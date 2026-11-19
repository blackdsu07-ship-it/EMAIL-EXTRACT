"""
streamlit_email_extractor.py  (extended)

Crawls a domain and extracts email addresses.

Discovery / crawling
  - sitemap.xml (+ robots.txt Sitemap:), seeded /contact /impressum /kontakt ... paths
  - contact-like links are crawled first (priority queue)
  - subdomains, http/www fallback, iframes, <base href>, meta/JS redirects
  - PDF / DOCX / vCard / TXT documents, other text-like files (security.txt, humans.txt)
  - URL normalisation (fragments / tracking params), charset detection, retries, robots.txt
  - optional JS rendering with Playwright (also captures XHR/JSON responses)

Extraction
  - plain text, mailto: (percent-encoded, multiple addresses)
  - [at]/(at)/{at}/[ at ]/[@]/ at + [dot]/(dot)/[.] text obfuscation, full-width @
  - HTML entities, \\xHH / \\uHHHH / %HH escapes
  - addresses split by tags/comments, hidden decoy spans
  - JS: string concatenation (incl. variables), array.join, reverse, String.fromCharCode,
        char-code arrays, hex strings, TYPO3 UnCryptMailto / data-mailto-token, ROT13
  - external .js and .css files (same site)
  - CSS: rtl / bidi-override (inline, <style>, external CSS), ::before/::after content
  - data-* attribute splits (data-user + data-domain)
  - reversed text, base64 (incl. URL-safe, short), hex
  - Cloudflare (data-cfemail and /cdn-cgi/l/email-protection#...)
  - images via OCR (contact-hinted or all, <img>, lazy attrs, CSS backgrounds, data: URIs),
    SVG text
  - optional external sources: DNS (DMARC rua/ruf, SOA), WHOIS, Wayback Machine

Run locally:
    pip install -r requirements.txt
    # OCR also needs the Tesseract binary (apt install tesseract-ocr / brew install tesseract)
    # JS rendering (optional, local only):
    #   pip install playwright && playwright install chromium
    streamlit run streamlit_email_extractor.py
"""

from __future__ import annotations

import csv
import base64
import gzip
import html
import io
import json
import re
import time
import zipfile
from collections import deque
from urllib.parse import parse_qsl, unquote, urldefrag, urlencode, urljoin, urlparse, urlunparse
from urllib.robotparser import RobotFileParser

import socket

# Hard global cap on every blocking network / DNS call. Without this, a black-holed
# host (firewall silently drops packets) or a broken resolver can make individual
# requests hang for minutes -- the crawler then appears to "load forever" and never
# crawls any page, even though `timeout=` is passed to requests (it does not cover
# DNS resolution done by other libraries).
socket.setdefaulttimeout(20)

import requests
from bs4 import BeautifulSoup, Comment, UnicodeDammit
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

try:
    import pytesseract
    from PIL import Image, ImageOps
    OCR_AVAILABLE = True
    _RESAMPLE = getattr(Image, "Resampling", Image).LANCZOS
except ImportError:
    OCR_AVAILABLE = False

try:
    from pypdf import PdfReader
    PDF_AVAILABLE = True
except ImportError:
    PDF_AVAILABLE = False

try:
    from playwright.sync_api import sync_playwright
    PLAYWRIGHT_AVAILABLE = True
except ImportError:
    PLAYWRIGHT_AVAILABLE = False

try:
    import dns.resolver
    DNS_AVAILABLE = True
except ImportError:
    DNS_AVAILABLE = False

try:
    import whois as _whois
    WHOIS_AVAILABLE = True
except ImportError:
    WHOIS_AVAILABLE = False

# Non-blocking socket for optional DNS lookups (dnspython honours this timeout).
_DNS_TIMEOUT = 5


# --------------------------------------------------------------------------- #
# Constants / regexes
# --------------------------------------------------------------------------- #

MAX_TEXT = 3_000_000          # max chars of a page / asset we run regexes on
MAX_ASSET_BYTES = 2_000_000
MAX_IMAGE_BYTES = 5_000_000

# Network timeouts. A *connect* timeout must be short: if the target host silently
# drops packets (firewall black-hole, dead CDN node), an unbounded connect makes the
# whole crawl hang "loading forever" without ever fetching a page. The read timeout
# stays generous so slow pages still get served.
CONNECT_TIMEOUT = 8
READ_TIMEOUT = 20
# Give up on a crawl after this many consecutive failed requests (timeouts, refused
# connections, ...). Prevents an endless "loading..." when the site is unreachable.
MAX_CONSECUTIVE_FAILURES = 15

# Local part / domain lengths are bounded to avoid quadratic regex backtracking on long tokens.
EMAIL_REGEX = re.compile(r"[A-Za-z0-9._%+\-]{1,64}@[A-Za-z0-9.\-]{1,253}\.[A-Za-z]{2,24}")

OBF_AT = r"(?:[\[\(\{<]\s*(?:at|@)\s*[\]\)\}>]|-at-|_at_|\s@\s)"
OBF_DOT = r"(?:[\[\(\{<]\s*(?:dot|\.)\s*[\]\)\}>]|-dot-|_dot_)"
OBF_A = re.compile(
    rf"([A-Za-z0-9._%+\-]{{1,64}})\s*{OBF_AT}\s*"
    rf"([A-Za-z0-9\-]{{1,63}}(?:\s*(?:{OBF_DOT}|\.)\s*[A-Za-z0-9\-]{{1,63}}){{1,6}})",
    re.I,
)
OBF_DOT_RE = re.compile(OBF_DOT, re.I)
# bare words: "name at domain dot com" (needs BOTH words to limit false positives)
OBF_B = re.compile(
    r"([A-Za-z0-9._%+\-]{1,64})\s+at\s+([A-Za-z0-9\-]{1,63}(?:\s+(?:dot|punkt)\s+[A-Za-z0-9\-]{1,63}){1,6})",
    re.I,
)
OBF_B_DOT = re.compile(r"\s+(?:dot|punkt)\s+", re.I)
OCR_SPACED = re.compile(r"([A-Za-z0-9._%+\-]{1,64})\s*@\s*([A-Za-z0-9\-]{1,63}(?:\s*\.\s*[A-Za-z0-9\-]{1,63}){1,6})")

JS_HEX_ESC = re.compile(r"\\x([0-9a-fA-F]{2})")
JS_UNI_ESC = re.compile(r"\\u([0-9a-fA-F]{4})")
ZERO_WIDTH = re.compile("[\u200b\u200c\u200d\u2060\ufeff\u00ad]")

CF_EMAIL_REGEX = re.compile(r"""data-cfemail=["']([a-fA-F0-9]+)["']""")
CF_HREF_REGEX = re.compile(r"/cdn-cgi/l/email-protection#([a-fA-F0-9]+)")
BASE64_CAND = re.compile(r"(?<![A-Za-z0-9+/=_\-])[A-Za-z0-9+/_\-]{8,}={0,2}(?![A-Za-z0-9+/=_\-])")
HEX_LIT = re.compile(r"""["']((?:[0-9a-fA-F]{2}){6,})["']""")

STR_LIT = r"""\"(?:[^\"\\\n]|\\.)*\"|'(?:[^'\\\n]|\\.)*'"""
IDENT = r"(?<![\w$])[A-Za-z_$][\w$]{0,40}(?![\w$])"   # bounded + anchored: no O(n^2) on long tokens
TOKEN = rf"(?:{STR_LIT}|{IDENT})"
VAR_RE = re.compile(rf"({IDENT})\s*=\s*({STR_LIT})")
CONCAT_RE = re.compile(rf"{TOKEN}(?:\s*\+\s*{TOKEN})+")
TOKEN_RE = re.compile(TOKEN)
JOIN_RE = re.compile(
    rf"\[\s*({TOKEN}(?:\s*,\s*{TOKEN})*)\s*\]\s*(\.\s*reverse\s*\(\s*\))?\s*\.\s*join\s*\(\s*({STR_LIT})\s*\)"
)
REV_STR_RE = re.compile(
    rf"({TOKEN})\s*\.\s*split\s*\(\s*(?:\"\"|'')\s*\)\s*\.\s*reverse\s*\(\s*\)\s*\.\s*join\s*\(\s*(?:\"\"|'')\s*\)"
)
CHARCODE_RE = re.compile(r"fromCharCode\s*\(\s*([^()]{1,2000}?)\s*\)")
CHARCODE_APPLY_RE = re.compile(r"fromCharCode\s*\.\s*apply\s*\(\s*\w+\s*,\s*\[([\d\s,xXa-fA-F]+)\]\s*\)")
INT_ARRAY_RE = re.compile(r"\[\s*((?:\d{2,3}\s*,\s*){5,}\d{2,3})\s*\]")
TYPO3_RE = re.compile(rf"""linkTo_UnCryptMailto\(\s*({STR_LIT})""")
TYPO3_TOKEN_RE = re.compile(r"""data-mailto-token=["']([^"']+)["']""")
ROT13_HINT = re.compile(r"rot13|str_rot13|replace\(\s*/\[a-zA-Z\]/g", re.I)

JUNK_TLDS = {
    "png", "jpg", "jpeg", "gif", "webp", "svg", "bmp", "ico", "css", "js", "mjs", "map", "woff", "woff2",
    "ttf", "otf", "eot", "mp4", "webm", "avif", "heic", "json", "php", "html", "htm", "xml", "txt", "pdf",
}
PLACEHOLDER_SUFFIXES = ("example.com", "example.org", "example.net", "domain.com", "yourdomain.com",
                        "email.com", "sentry.io", "wixpress.com")

CONTACT_KEYWORDS = ("contact", "kontakt", "impressum", "imprint", "about", "ueber", "uber", "team",
                    "privacy", "datenschutz", "legal", "support", "press", "presse", "media", "help",
                    "advert", "reklama", "mentions-legales", "aviso-legal", "nous-contacter")
SEED_PATHS = ["/contact", "/contact-us", "/contact.html", "/contacts", "/kontakt", "/impressum", "/imprint",
              "/about", "/about-us", "/ueber-uns", "/team", "/privacy", "/privacy-policy", "/datenschutz",
              "/legal", "/terms", "/support", "/help", "/advertise-with-us", "/press",
              "/.well-known/security.txt", "/security.txt", "/humans.txt"]
SKIP_EXT = (".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".ico", ".bmp", ".css", ".js", ".mjs", ".woff",
            ".woff2", ".ttf", ".eot", ".otf", ".mp3", ".mp4", ".avi", ".mov", ".webm", ".zip", ".gz", ".rar",
            ".7z", ".exe", ".dmg", ".apk", ".xml", ".rss", ".atom", ".json", ".xls", ".xlsx", ".ppt", ".pptx", ".doc")
DOC_EXT = (".pdf", ".docx", ".vcf", ".txt")
IMG_HINTS = ("mail", "contact", "kontakt", "e-mail", "impressum", "imprint", "address", "adresse")
HIDDEN_STYLE = re.compile(r"display\s*:\s*none|visibility\s*:\s*hidden|font-size\s*:\s*0(?:px|em|rem|%)?\s*(?:;|$)", re.I)
INLINE_TAGS = re.compile(r"</?(?:span|b|i|em|strong|font|u|small|big|wbr|bdi|bdo|code|sup|sub|mark|abbr|tt)\b[^>]*>", re.I)
RTL_STYLE = re.compile(r"direction\s*:\s*rtl|unicode-bidi\s*:\s*(?:bidi-override|isolate-override)", re.I)
CSS_RULE_RE = re.compile(r"([^{}@]+)\{([^{}]*)\}")
CSS_URL_RE = re.compile(r"""url\(\s*['"]?([^)'"\s]+)['"]?\s*\)""", re.I)

DEFAULT_HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9,de;q=0.8",
}

DEFAULT_OPTS = dict(
    max_pages=50,
    delay=0.5,
    include_subdomains=True,
    respect_robots=True,
    use_sitemap=True,
    seed_paths=True,
    fetch_assets=True,        # external .js / .css from the same site
    max_assets_per_page=10,
    fetch_docs=True,          # pdf / docx / vcf / txt
    max_docs=10,
    use_ocr=False,
    ocr_all=False,            # OCR every image, not only contact-hinted ones
    max_images=15,
    use_js_render=False,      # Playwright
    dns_whois=False,
    wayback=False,
    extra_domains=(),
)


# --------------------------------------------------------------------------- #
# Small helpers
# --------------------------------------------------------------------------- #

def normalize_domain(domain: str) -> str:
    domain = domain.strip().lower()
    domain = re.sub(r"^https?://", "", domain)
    domain = domain.split("/")[0].split(":")[0]
    if domain.startswith("www."):
        domain = domain[4:]
    return domain


def host_of(url: str) -> str:
    h = (urlparse(url).hostname or "").lower()
    return h[4:] if h.startswith("www.") else h


def clean_email(e: str) -> str:
    e = e.strip().strip("<>()[]{}'\"\u201c\u201d\u2018\u2019 ")
    e = re.sub(r"^mailto:", "", e, flags=re.I)
    e = e.rstrip(".,;:!?)>")
    return e.lower()


def is_valid_email(e: str) -> bool:
    if len(e) > 254 or e.count("@") != 1:
        return False
    local, dom = e.split("@")
    if not local or len(local) > 64 or ".." in e or local[0] == "." or local[-1] == ".":
        return False
    labels = dom.split(".")
    if len(labels) < 2 or any((not l) or len(l) > 63 or l[0] == "-" or l[-1] == "-" for l in labels):
        return False
    if labels[-1] in JUNK_TLDS or not labels[-1].isalpha():
        return False
    if re.match(r"^\d+(\.\d+)?x$", labels[0]):
        return False
    if dom.endswith(PLACEHOLDER_SUFFIXES):
        return False
    return True


def keep_valid(candidates) -> set:
    out = set()
    for c in candidates:
        c = clean_email(c)
        if EMAIL_REGEX.fullmatch(c) and is_valid_email(c):
            out.add(c)
    return out


def deep_text(s: str) -> str:
    """Undo HTML entities, JS \\x/\\u escapes, %XX escapes, full-width chars, zero-width chars."""
    s = html.unescape(html.unescape(s))
    if "\\x" in s:
        s = JS_HEX_ESC.sub(lambda m: chr(int(m.group(1), 16)), s)
    if "\\u" in s:
        s = JS_UNI_ESC.sub(lambda m: chr(int(m.group(1), 16)), s)
    s = s.replace("\uff20", "@").replace("\ufe6b", "@").replace("\uff0e", ".").replace("\u3002", ".")
    s = ZERO_WIDTH.sub("", s)
    if "%" in s:
        s = unquote(s)
    return s


def css_unescape(s: str) -> str:
    return re.sub(r"\\([0-9a-fA-F]{1,6})\s?", lambda m: chr(int(m.group(1), 16)), s)


def decode_cf_email(cfhex: str) -> str:
    try:
        r = int(cfhex[:2], 16)
        return "".join(chr(int(cfhex[i:i + 2], 16) ^ r) for i in range(2, len(cfhex), 2))
    except Exception:
        return ""


def typo3_decrypt(enc: str, offset: int) -> str:
    out = []
    for ch in enc:
        n = ord(ch)
        for start, end in ((0x2B, 0x3A), (0x40, 0x5A), (0x61, 0x7A)):
            if start <= n <= end:
                n += offset
                if offset > 0 and n > end:
                    n = start + (n - end - 1)
                elif offset < 0 and n < start:
                    n = end - (start - n - 1)
                break
        out.append(chr(n))
    return "".join(out)


def rot13(s: str) -> str:
    import codecs
    return codecs.encode(s, "rot_13")


def url_key(url: str) -> str:
    p = urlparse(url)
    return f"{p.scheme}://{(p.hostname or '').lower()}{p.path.rstrip('/') or '/'}?{p.query}"


def norm_url(url: str) -> str:
    url, _ = urldefrag(url)
    p = urlparse(url)
    q = [(k, v) for k, v in parse_qsl(p.query, keep_blank_values=True)
         if not k.lower().startswith("utm_") and k.lower() not in ("fbclid", "gclid", "mc_cid", "mc_eid")]
    return urlunparse((p.scheme.lower(), p.netloc.lower(), p.path or "/", p.params, urlencode(q), ""))


def has_ext(url: str, exts) -> bool:
    return urlparse(url).path.lower().endswith(exts)


def is_priority(*texts) -> bool:
    blob = " ".join(t for t in texts if t).lower()
    return any(k in blob for k in CONTACT_KEYWORDS)


def decode_response(resp: requests.Response) -> str:
    ctype = resp.headers.get("Content-Type", "").lower()
    if "charset" in ctype:
        return resp.text
    try:
        return UnicodeDammit(resp.content, is_html=True).unicode_markup or resp.text
    except Exception:
        return resp.text


# --------------------------------------------------------------------------- #
# Text-level extraction
# --------------------------------------------------------------------------- #

def extract_text_emails(text: str) -> dict:
    """Returns {"plain": set, "obfuscated": set}."""
    text = text[:MAX_TEXT]
    plain = keep_valid(EMAIL_REGEX.findall(text))
    obf = set()
    for m in OBF_A.finditer(text):
        dom = re.sub(r"\s+", "", OBF_DOT_RE.sub(".", m.group(2)))
        obf.add(f"{m.group(1)}@{dom}")
    for m in OBF_B.finditer(text):
        dom = re.sub(r"\s+", "", OBF_B_DOT.sub(".", m.group(2)))
        obf.add(f"{m.group(1)}@{dom}")
    return {"plain": plain, "obfuscated": keep_valid(obf) - plain}


def extract_reversed_text(text: str) -> set:
    """Emails stored backwards (used with CSS direction:rtl tricks or plain string reversal)."""
    return keep_valid(EMAIL_REGEX.findall(text[:MAX_TEXT][::-1]))


def flat_visible_text(raw_html: str) -> str:
    """Visible text where inline tags / comments / hidden decoys do not split the address."""
    try:
        s2 = BeautifulSoup(raw_html, "html.parser")
        for tag in s2(["script", "style", "noscript", "template"]):
            tag.decompose()
        for c in s2.find_all(string=lambda t: isinstance(t, Comment)):
            c.extract()
        hidden = []
        for el in s2.find_all(True):
            try:
                if el.has_attr("hidden") or HIDDEN_STYLE.search(el.get("style") or ""):
                    hidden.append(el)
            except Exception:
                continue
        for el in hidden:
            try:
                el.decompose()
            except Exception:
                pass
        s = str(s2)
        s = INLINE_TAGS.sub("", s)
        s = re.sub(r"<[^>]+>", " ", s)
        return deep_text(s)
    except Exception:
        return ""


def extract_cloudflare(text: str) -> set:
    found = set()
    for cfhex in CF_EMAIL_REGEX.findall(text) + CF_HREF_REGEX.findall(text):
        found.add(decode_cf_email(cfhex))
    return keep_valid(found)


def extract_base64_and_hex(text: str) -> dict:
    b64, hx = set(), set()
    seen = set()
    for cand in BASE64_CAND.findall(text[:MAX_TEXT]):
        if cand in seen:
            continue
        seen.add(cand)
        if len(seen) > 20000:
            break
        c = cand.replace("-", "+").replace("_", "/")
        c += "=" * (-len(c) % 4)
        try:
            decoded = base64.b64decode(c, validate=True).decode("utf-8", errors="ignore")
        except Exception:
            continue
        if "@" in decoded and sum(ch.isprintable() for ch in decoded) / len(decoded) > 0.85:
            b64.update(EMAIL_REGEX.findall(decoded))
    for h in HEX_LIT.findall(text[:MAX_TEXT]):
        try:
            decoded = bytes.fromhex(h).decode("latin-1")
        except Exception:
            continue
        if "@" in decoded:
            hx.update(EMAIL_REGEX.findall(decoded))
    return {"base64": keep_valid(b64), "hex": keep_valid(hx)}


def _lit(tok: str, vars_: dict):
    if tok[:1] in ("'", '"'):
        return re.sub(r"\\(['\"\\/])", r"\1", tok[1:-1])
    return vars_.get(tok)


def _to_int(x: str):
    x = x.strip()
    try:
        return int(x, 16) if x.lower().startswith("0x") else int(x)
    except ValueError:
        return None


def extract_js(text: str) -> dict:
    """Decode common JS email-hiding patterns. Returns {method: set(emails)}."""
    text = deep_text(text[:MAX_TEXT])
    out: dict = {}

    def add(method, strings):
        found = keep_valid(e for s in strings for e in EMAIL_REGEX.findall(s))
        if found:
            out.setdefault(method, set()).update(found)

    if "@" in text:
        vars_ = {m.group(1): _lit(m.group(2), {}) for m in VAR_RE.finditer(text)}
        # "user" + "@" + "domain.com", user + "@" + dom ...
        res = []
        for m in CONCAT_RE.finditer(text):
            parts = [_lit(t, vars_) for t in TOKEN_RE.findall(m.group(0))]
            if None not in parts:
                res.append("".join(parts))
        add("js-concat", res)
        # ["user","domain.com"].join("@")  (+ optional .reverse())
        res = []
        for m in JOIN_RE.finditer(text):
            items = [_lit(t, vars_) for t in TOKEN_RE.findall(m.group(1))]
            sep = _lit(m.group(3), vars_)
            if None in items or sep is None:
                continue
            if m.group(2):
                items = items[::-1]
            res.append(sep.join(items))
        add("js-join", res)
    # "moc.elpmaxe@resu".split("").reverse().join("")
    vars_ = {m.group(1): _lit(m.group(2), {}) for m in VAR_RE.finditer(text)}
    res = []
    for m in REV_STR_RE.finditer(text):
        s = _lit(m.group(1), vars_)
        if s:
            res.append(s[::-1])
    add("js-reverse", res)

    # String.fromCharCode(117,115,...) / apply / int arrays
    res = []
    for m in CHARCODE_RE.finditer(text):
        nums = [_to_int(x) for x in m.group(1).split(",")]
        if nums and None not in nums and all(0 < n < 0x110000 for n in nums):
            res.append("".join(chr(n) for n in nums))
    for m in CHARCODE_APPLY_RE.finditer(text):
        nums = [_to_int(x) for x in m.group(1).split(",") if x.strip()]
        if nums and None not in nums:
            res.append("".join(chr(n) for n in nums if 0 < n < 0x110000))
    for m in INT_ARRAY_RE.finditer(text):
        nums = [int(x) for x in m.group(1).split(",")]
        if all(32 <= n <= 126 for n in nums):
            res.append("".join(chr(n) for n in nums))
    add("js-charcode", res)

    # TYPO3 linkTo_UnCryptMailto('...') / data-mailto-token="..."
    encs = [_lit(m.group(1), {}) for m in TYPO3_RE.finditer(text)] + TYPO3_TOKEN_RE.findall(text)
    res = []
    for enc in encs:
        if not enc:
            continue
        for off in range(-26, 27):
            if off:
                dec = typo3_decrypt(enc, off)
                if "@" in dec and EMAIL_REGEX.search(dec):
                    res.append(dec)
    add("js-typo3-cloak", res)

    # ROT13 (only when the page ships a rot13 routine)
    if ROT13_HINT.search(text):
        res = []
        for m in re.finditer(STR_LIT, text):
            lit = m.group(0)[1:-1]
            if "@" in lit and len(lit) <= 120:
                res.append(rot13(lit))
        add("js-rot13", res)
    return out


# --------------------------------------------------------------------------- #
# DOM / CSS level extraction
# --------------------------------------------------------------------------- #

def extract_mailto(soup: BeautifulSoup) -> set:
    found = set()
    for a in soup.find_all(["a", "area"], href=True):
        href = a["href"].strip()
        if href.lower().startswith("mailto:"):
            body = unquote(href[7:].split("?")[0])
            body = deep_text(body)
            for part in re.split(r"[,;]", body):
                found.add(part)
    return keep_valid(found)


def extract_data_attr_splits(soup: BeautifulSoup) -> set:
    found = set()
    for el in soup.find_all(True):
        d = {k.lower(): v for k, v in el.attrs.items() if isinstance(v, str) and k.lower().startswith("data-")}
        if len(d) < 2:
            continue
        users = [v for k, v in d.items() if re.search(r"user|name|local|prefix|before|first", k)]
        doms = [v for k, v in d.items() if re.search(r"domain|host|site|suffix|after|second", k)]
        tlds = [v for k, v in d.items() if re.search(r"tld|ext|ending", k)]
        for u in users:
            for dm in doms:
                found.add(f"{u}@{dm}")
                for t in tlds:
                    found.add(f"{u}@{dm}.{t.lstrip('.')}")
    return keep_valid(found)


def _safe_select(soup, selector):
    try:
        return soup.select(selector)
    except Exception:
        return []


def extract_css_tricks(soup: BeautifulSoup, css_text: str) -> dict:
    """rtl / bidi-override reversal and ::before/::after generated content."""
    rtl_texts, pseudo_texts = [], []

    rtl_elems = list(soup.find_all(style=RTL_STYLE)) + list(soup.find_all("bdo", dir="rtl")) \
        + list(soup.find_all(attrs={"dir": "rtl"}))
    pseudo: dict = {}   # id(el) -> {"el": el, "before": str, "after": str}

    for sel, body in CSS_RULE_RE.findall(css_text):
        if RTL_STYLE.search(body):
            for part in sel.split(","):
                part = re.sub(r"::?(?:before|after)\s*$", "", part.strip())
                if part:
                    rtl_elems.extend(_safe_select(soup, part))
        m = re.search(r"content\s*:\s*([^;}]+)", body, re.I)
        if not m:
            continue
        for part in sel.split(","):
            pm = re.match(r"^(.*?)::?(before|after)\s*$", part.strip())
            if not pm or not pm.group(1).strip():
                continue
            for el in _safe_select(soup, pm.group(1).strip()):
                text = ""
                for tm in re.finditer(r"\"([^\"]*)\"|'([^']*)'|attr\(\s*([\w-]+)\s*\)", m.group(1)):
                    if tm.group(3):
                        text += str(el.get(tm.group(3), ""))
                    else:
                        text += css_unescape(tm.group(1) if tm.group(1) is not None else tm.group(2))
                slot = pseudo.setdefault(id(el), {"el": el, "before": "", "after": ""})
                slot[pm.group(2)] += text

    for el in rtl_elems:
        t = el.get_text("")
        rtl_texts.extend([t[::-1], t])
    for slot in pseudo.values():
        inner = slot["el"].get_text("")
        pseudo_texts.extend([slot["before"] + inner + slot["after"], slot["before"] + slot["after"]])

    return {
        "css-reversed": keep_valid(e for t in rtl_texts for e in EMAIL_REGEX.findall(t)),
        "css-pseudo": keep_valid(e for t in pseudo_texts for e in EMAIL_REGEX.findall(t)),
    }


# --------------------------------------------------------------------------- #
# Images (OCR / SVG)
# --------------------------------------------------------------------------- #

def ocr_image_bytes(content: bytes) -> set:
    if not OCR_AVAILABLE or len(content) > MAX_IMAGE_BYTES:
        return set()
    img = Image.open(io.BytesIO(content))
    img.load()
    if img.width * img.height > 25_000_000:
        return set()
    if img.mode in ("RGBA", "LA", "P"):
        img = img.convert("RGBA")
        bg = Image.new("RGBA", img.size, (255, 255, 255, 255))
        bg.alpha_composite(img)
        img = bg
    img = img.convert("L")
    if max(img.size) < 600:
        img = img.resize((img.width * 3, img.height * 3), _RESAMPLE)
    for variant in (img, ImageOps.invert(img)):
        for psm in (6, 7):
            try:
                text = pytesseract.image_to_string(variant, config=f"--psm {psm}")
            except Exception:
                return set()
            squeezed = " ".join(
                f"{m.group(1)}@{re.sub(chr(32), '', m.group(2))}" for m in OCR_SPACED.finditer(text)
            )
            found = keep_valid(EMAIL_REGEX.findall(text + " " + squeezed))
            if found:
                return found
    return set()


def image_candidates(soup: BeautifulSoup, base_url: str, css_text: str):
    """Yield (absolute_url_or_data_uri, hint_text)."""
    for img in soup.find_all("img"):
        hint = f"{img.get('alt', '')} {img.get('title', '')} {' '.join(img.get('class', []) or [])} {img.get('id', '')}"
        srcs = [img.get(a) for a in ("src", "data-src", "data-lazy-src", "data-original")]
        if img.get("srcset"):
            srcs.append(img["srcset"].split(",")[0].strip().split(" ")[0])
        for s in srcs:
            if s:
                yield (s if s.startswith("data:") else urljoin(base_url, s)), f"{s} {hint}"
    for inp in soup.find_all("input", type="image"):
        if inp.get("src"):
            yield urljoin(base_url, inp["src"]), f"{inp['src']} {inp.get('alt', '')}"
    for el in soup.find_all(style=re.compile(r"url\(", re.I)):
        for u in CSS_URL_RE.findall(el.get("style", "")):
            yield (u if u.startswith("data:") else urljoin(base_url, u)), f"{u} {' '.join(el.get('class', []) or [])}"
    for sel, body in CSS_RULE_RE.findall(css_text):
        if "background" in body:
            for u in CSS_URL_RE.findall(body):
                yield (u if u.startswith("data:") else urljoin(base_url, u)), f"{u} {sel}"


# --------------------------------------------------------------------------- #
# Documents
# --------------------------------------------------------------------------- #

def document_text(content: bytes, url: str, ctype: str) -> str:
    path = urlparse(url).path.lower()
    try:
        if path.endswith(".pdf") or "pdf" in ctype:
            if not PDF_AVAILABLE:
                return ""
            reader = PdfReader(io.BytesIO(content))
            chunks = []
            for page in reader.pages[:60]:
                chunks.append(page.extract_text() or "")
                for annot in page.get("/Annots") or []:
                    try:
                        a = annot.get_object().get("/A")
                        if a and a.get("/URI"):
                            chunks.append(str(a["/URI"]))
                    except Exception:
                        pass
            return "\n".join(chunks)
        if path.endswith(".docx") or "wordprocessingml" in ctype:
            with zipfile.ZipFile(io.BytesIO(content)) as z:
                parts = []
                for name in ("word/document.xml", "word/_rels/document.xml.rels", "word/footer1.xml",
                             "word/header1.xml", "word/footnotes.xml"):
                    if name in z.namelist():
                        parts.append(re.sub(r"<[^>]+>", " ", z.read(name).decode("utf-8", "ignore")))
                return "\n".join(parts)
    except Exception:
        return ""
    return UnicodeDammit(content).unicode_markup or ""


# --------------------------------------------------------------------------- #
# Crawl context
# --------------------------------------------------------------------------- #

def make_session() -> requests.Session:
    s = requests.Session()
    s.headers.update(DEFAULT_HEADERS)
    retry = Retry(total=1, backoff_factor=0.5, status_forcelist=[429, 500, 502, 503, 504],
                  allowed_methods=["GET", "HEAD"], respect_retry_after_header=False)
    # pool_connections small; keep-alive lets a session reuse connections to the same host
    s.mount("http://", HTTPAdapter(max_retries=retry, pool_connections=4, pool_maxsize=8))
    s.mount("https://", HTTPAdapter(max_retries=retry, pool_connections=4, pool_maxsize=8))
    return s


class Robots:
    def __init__(self, session):
        self.session = session
        self.cache: dict = {}

    def _load(self, base: str):
        if base in self.cache:
            return self.cache[base]
        rp = RobotFileParser()
        text = ""
        try:
            r = self.session.get(base + "/robots.txt", timeout=10)
            if r.status_code == 200 and "html" not in r.headers.get("Content-Type", "").lower():
                text = r.text
        except requests.RequestException:
            pass
        rp.parse(text.splitlines())
        rp.modified()
        self.cache[base] = (rp, text)
        return self.cache[base]

    def allowed(self, url: str) -> bool:
        p = urlparse(url)
        rp, _ = self._load(f"{p.scheme}://{p.netloc}")
        return rp.can_fetch("*", url)

    def sitemaps(self, base: str) -> list:
        rp, text = self._load(base)
        found = rp.site_maps() or []
        if not found:
            found = re.findall(r"(?im)^\s*sitemap:\s*(\S+)", text)
        return found

    def crawl_delay(self, base: str):
        rp, _ = self._load(base)
        try:
            return rp.crawl_delay("*")
        except Exception:
            return None


class Renderer:
    """Optional headless-browser renderer (Playwright)."""

    def __init__(self, timeout_ms: int = 20000):
        self.timeout = timeout_ms
        self.pw = sync_playwright().start()
        self.browser = self.pw.chromium.launch(headless=True)
        self.context = self.browser.new_context(user_agent=DEFAULT_HEADERS["User-Agent"])

    def render(self, url: str):
        page = self.context.new_page()
        extra: list = []

        def on_response(resp):
            try:
                ct = resp.headers.get("content-type", "").lower()
                if any(t in ct for t in ("json", "xml", "text/plain")) and resp.status == 200:
                    extra.append(resp.text()[:500_000])
            except Exception:
                pass

        page.on("response", on_response)
        try:
            try:
                page.goto(url, wait_until="networkidle", timeout=self.timeout)
            except Exception:
                pass
            try:
                page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
                page.wait_for_timeout(600)
            except Exception:
                pass
            return page.content(), extra
        finally:
            page.close()

    def close(self):
        for obj, fn in ((self.browser, "close"), (self.pw, "stop")):
            try:
                getattr(obj, fn)()
            except Exception:
                pass


class Ctx:
    def __init__(self, domain: str, opts: dict, log=None, on_found=None, on_removed=None):
        self.on_found = on_found
        self.on_removed = on_removed
        self.domain = domain
        self.o = opts
        self.scope = {domain}
        self.session = make_session()
        self.robots = Robots(self.session)
        self.assets: dict = {}
        self.ocr_seen: set = set()
        self.results: dict = {}
        self.log = log or (lambda m: None)

    # scope -----------------------------------------------------------------
    def in_scope(self, url: str) -> bool:
        h = host_of(url)
        if not h:
            return False
        for d in self.scope:
            if h == d or (self.o["include_subdomains"] and h.endswith("." + d)):
                return True
        return False

    # results ---------------------------------------------------------------
    def email_in_scope(self, email: str) -> bool:
        return self.in_scope("http://" + email.split("@")[1])

    def add(self, emails, method: str, url: str):
        for e in emails:
            r = rot13(e)
            if e not in self.results and r != e:
                # the ROT13-encoded form of an address we already have is junk, never report it
                if r in self.results and self.email_in_scope(r) and not self.email_in_scope(e):
                    continue
                # an in-scope address arrived after its encoded junk form was reported: retract the junk
                if r in self.results and self.email_in_scope(e) and not self.email_in_scope(r):
                    del self.results[r]
                    if self.on_removed:
                        try:
                            self.on_removed(r)
                        except Exception:
                            pass
            is_new = e not in self.results
            rec = self.results.setdefault(e, {"methods": set(), "url": url})
            rec["methods"].add(method)
            if is_new and self.on_found:
                try:
                    self.on_found(e, method, url)
                except Exception:
                    pass

    # network ---------------------------------------------------------------
    def get(self, url: str, check_robots: bool = True, **kw):
        if check_robots and self.o["respect_robots"] and not self.robots.allowed(url):
            self.log(f"[robots] blocked {url}")
            return None
        kw.setdefault("timeout", (CONNECT_TIMEOUT, READ_TIMEOUT))
        try:
            return self.session.get(url, allow_redirects=True, **kw)
        except requests.RequestException as e:
            self.log(f"[err] {url} -- {e.__class__.__name__}: {e}")
            return None

    def fetch_asset(self, url: str, kind: str):
        """Fetch a same-site .js/.css/.svg file once, return text ('' if unavailable)."""
        if url in self.assets:
            return self.assets[url]
        text = ""
        if self.in_scope(url):
            r = self.get(url)
            if r is not None and r.status_code == 200 and len(r.content) <= MAX_ASSET_BYTES:
                text = decode_response(r)
        self.assets[url] = text
        return text


# --------------------------------------------------------------------------- #
# Page processing
# --------------------------------------------------------------------------- #

def collect_css(soup: BeautifulSoup, base_url: str, ctx: Ctx) -> str:
    chunks = [s.get_text() for s in soup.find_all("style")]
    if ctx.o["fetch_assets"]:
        n = 0
        for link in soup.find_all("link", href=True):
            if "stylesheet" in " ".join(link.get("rel") or []).lower() and n < ctx.o["max_assets_per_page"]:
                chunks.append(ctx.fetch_asset(urljoin(base_url, link["href"]), "css"))
                n += 1
    return "\n".join(chunks)[:MAX_TEXT]


def collect_scripts(soup: BeautifulSoup, base_url: str, ctx: Ctx) -> list:
    texts = []
    if ctx.o["fetch_assets"]:
        n = 0
        for sc in soup.find_all("script", src=True):
            if n >= ctx.o["max_assets_per_page"]:
                break
            u = urljoin(base_url, sc["src"])
            if ctx.in_scope(u):
                texts.append(ctx.fetch_asset(u, "js"))
                n += 1
    return texts


def process_images(soup, base_url, css_text, ctx: Ctx, url: str):
    found = []  # (emails, method)
    if not ctx.o["use_ocr"] and not ctx.o["fetch_assets"]:
        return found
    cands = list(image_candidates(soup, base_url, css_text))
    cands.sort(key=lambda c: 0 if any(k in c[1].lower() for k in IMG_HINTS) else 1)
    checked = 0
    for src, hint in cands:
        if src in ctx.ocr_seen:
            continue
        hinted = any(k in hint.lower() for k in IMG_HINTS)
        path = urlparse(src).path.lower() if not src.startswith("data:") else ""
        is_svg = path.endswith(".svg") or src.startswith("data:image/svg")
        if checked >= ctx.o["max_images"]:
            break
        if not is_svg and not (ctx.o["use_ocr"] and (hinted or ctx.o["ocr_all"])):
            continue
        ctx.ocr_seen.add(src)
        checked += 1
        try:
            if src.startswith("data:"):
                head, _, payload = src.partition(",")
                data = base64.b64decode(payload) if ";base64" in head else unquote(payload).encode()
            else:
                if not ctx.in_scope(src) and not hinted:
                    continue
                r = ctx.get(src)
                if r is None or r.status_code != 200:
                    continue
                data = r.content
            if is_svg:
                txt = deep_text(data[:MAX_ASSET_BYTES].decode("utf-8", "ignore"))
                txt = re.sub(r"<[^>]+>", "", txt)
                found.append((keep_valid(EMAIL_REGEX.findall(txt)), "svg-text"))
            else:
                found.append((ocr_image_bytes(data), "ocr-image"))
        except Exception:
            continue
    return found


def extract_all_emails(raw_html: str, soup: BeautifulSoup, base_url: str, ctx: Ctx) -> list:
    """Return [(email, method)] for one HTML document."""
    out: list = []

    def add(method, emails):
        for e in emails:
            out.append((e, method))

    raw = raw_html[:MAX_TEXT]
    deep = deep_text(raw)
    css_text = collect_css(soup, base_url, ctx)
    js_texts = [raw] + collect_scripts(soup, base_url, ctx)

    # text level ------------------------------------------------------------
    t = extract_text_emails(deep)
    add("plain", t["plain"])
    add("text-obfuscation", t["obfuscated"])

    flat = flat_visible_text(raw)
    ft = extract_text_emails(flat)
    plain_all = t["plain"]
    for e in (ft["plain"] | ft["obfuscated"]) - plain_all - t["obfuscated"]:
        if not any(e != p and e.endswith(p) for p in plain_all):   # drop glued prefixes
            out.append((e, "split-tags/hidden-decoy"))
    st = extract_text_emails(soup.get_text(" "))
    add("text-obfuscation", st["obfuscated"])

    add("reversed-text", extract_reversed_text(deep) | extract_reversed_text(flat))

    # DOM level -------------------------------------------------------------
    add("mailto", extract_mailto(soup))
    add("data-attr-split", extract_data_attr_splits(soup))
    for method, emails in extract_css_tricks(soup, css_text).items():
        add(method, emails)
    for a in soup.find_all(True, attrs={"data-cfemail": True}):
        add("cloudflare", keep_valid([decode_cf_email(a["data-cfemail"])]))
    add("cloudflare", extract_cloudflare(raw))

    # JS / encodings --------------------------------------------------------
    for jt in js_texts:
        for method, emails in extract_js(jt).items():
            if method == "js-rot13":
                # rot13-ing ordinary addresses yields valid-looking junk, so keep in-scope domains only
                emails = {e for e in emails if ctx.in_scope("http://" + e.split("@")[1])}
            add(method, emails)
        enc = extract_base64_and_hex(jt)
        add("base64", enc["base64"])
        add("hex", enc["hex"])

    # images ----------------------------------------------------------------
    for emails, method in process_images(soup, base_url, css_text, ctx, base_url):
        add(method, emails)
    return out


def discover_links(soup: BeautifulSoup, base_url: str, raw_html: str, ctx: Ctx):
    """Return [(url, priority)] of in-scope links to crawl."""
    base_tag = soup.find("base", href=True)
    base = urljoin(base_url, base_tag["href"]) if base_tag else base_url
    found = []

    def consider(href, text="", force_pri=False):
        href = (href or "").strip()
        low = href.lower()
        if not href or low.startswith(("mailto:", "tel:", "javascript:", "data:", "#", "sms:")):
            return
        u = urljoin(base, href)
        if urlparse(u).scheme not in ("http", "https") or not ctx.in_scope(u):
            return
        if has_ext(u, SKIP_EXT) or "/cdn-cgi/" in u:
            return
        found.append((norm_url(u), force_pri or is_priority(u, text)))

    for a in soup.find_all(["a", "area"], href=True):
        consider(a["href"], a.get_text(" ", strip=True))
    for fr in soup.find_all(["iframe", "frame"], src=True):
        consider(fr["src"], force_pri=True)
    for meta in soup.find_all("meta", attrs={"http-equiv": re.compile("refresh", re.I)}):
        m = re.search(r"url\s*=\s*['\"]?([^'\";]+)", meta.get("content", ""), re.I)
        if m:
            consider(m.group(1), force_pri=True)
    for m in re.finditer(r"""(?:window\.|document\.)?location(?:\.href)?\s*=\s*["']([^"']+)["']""", raw_html[:MAX_TEXT]):
        consider(m.group(1), force_pri=True)
    return found


# --------------------------------------------------------------------------- #
# Sitemaps, external sources
# --------------------------------------------------------------------------- #

def read_sitemaps(base: str, ctx: Ctx, max_files: int = 10, max_urls: int = 3000) -> list:
    todo = list(ctx.robots.sitemaps(base)) or []
    for guess in ("/sitemap.xml", "/sitemap_index.xml", "/sitemap-index.xml"):
        if base + guess not in todo:
            todo.append(base + guess)
    urls, seen_files = [], 0
    while todo and seen_files < max_files and len(urls) < max_urls:
        sm = todo.pop(0)
        r = ctx.get(sm)
        if r is None or r.status_code != 200:
            continue
        seen_files += 1
        data = r.content
        try:
            if sm.endswith(".gz") or data[:2] == b"\x1f\x8b":
                data = gzip.decompress(data)
        except Exception:
            continue
        text = data.decode("utf-8", "ignore")
        for loc in re.findall(r"<loc>\s*(.*?)\s*</loc>", text, re.S | re.I):
            loc = html.unescape(loc.replace("<![CDATA[", "").replace("]]>", "")).strip()
            if re.search(r"\.xml(\.gz)?$", urlparse(loc).path, re.I) and "sitemap" in loc.lower():
                todo.append(loc)
            else:
                urls.append(loc)
    return urls[:max_urls]


def dns_whois_emails(domain: str, ctx: Ctx):
    if DNS_AVAILABLE:
        # Bound resolver time: a broken / firewalled DNS setup must never hang the crawl.
        try:
            dns.resolver.default_resolver = dns.resolver.Resolver(configure=True)
            dns.resolver.default_resolver.lifetime = _DNS_TIMEOUT
            dns.resolver.default_resolver.timeout = _DNS_TIMEOUT
        except Exception:
            pass
        try:
            for r in dns.resolver.resolve("_dmarc." + domain, "TXT"):
                txt = b"".join(r.strings).decode("utf-8", "ignore")
                for tag in ("rua", "ruf"):
                    for m in re.finditer(rf"{tag}\s*=\s*([^;]+)", txt):
                        for part in m.group(1).split(","):
                            part = part.strip()
                            if part.lower().startswith("mailto:"):
                                ctx.add(keep_valid([part[7:].split("!")[0]]), "dns-dmarc", "DNS")
        except Exception:
            pass
        try:
            for r in dns.resolver.resolve(domain, "SOA"):
                labels = re.split(r"(?<!\\)\.", str(r.rname).rstrip("."))
                if len(labels) >= 3:
                    mail = labels[0].replace("\\.", ".") + "@" + ".".join(labels[1:])
                    ctx.add(keep_valid([mail]), "dns-soa", "DNS")
        except Exception:
            pass
    if WHOIS_AVAILABLE:
        try:
            w = _whois.whois(domain)
            emails = w.emails if isinstance(w.emails, (list, tuple, set)) else [w.emails]
            ctx.add(keep_valid([e for e in emails if e]), "whois", "WHOIS")
        except Exception:
            pass


def wayback_pages(domain: str, ctx: Ctx, limit: int = 10) -> list:
    api = (f"https://web.archive.org/cdx/search/cdx?url={domain}/*&output=json&fl=timestamp,original"
           f"&filter=statuscode:200&filter=mimetype:text/html&collapse=urlkey&limit=800")
    r = ctx.get(api, check_robots=False)
    if r is None or r.status_code != 200:
        return []
    try:
        rows = json.loads(r.text)[1:]
    except Exception:
        return []
    picked = [(ts, orig) for ts, orig in rows if is_priority(orig)][:limit]
    root = [(ts, orig) for ts, orig in rows if urlparse(orig).path in ("", "/")][:2]
    return [f"https://web.archive.org/web/{ts}id_/{orig}" for ts, orig in picked + root]


# --------------------------------------------------------------------------- #
# Main crawl
# --------------------------------------------------------------------------- #

def process_html(html_text: str, url: str, ctx: Ctx):
    try:
        soup = BeautifulSoup(html_text, "html.parser")
    except Exception:
        return [], []
    base_tag = soup.find("base", href=True)
    base = urljoin(url, base_tag["href"]) if base_tag else url
    found = extract_all_emails(html_text, soup, base, ctx)
    links = discover_links(soup, url, html_text, ctx)
    return found, links


def crawl(start_domain: str, opts: dict | None = None, progress_callback=None, log=None,
          on_found=None, on_removed=None):
    o = {**DEFAULT_OPTS, **(opts or {})}
    domain = normalize_domain(start_domain)
    ctx = Ctx(domain, o, log=log, on_found=on_found, on_removed=on_removed)
    for extra in o.get("extra_domains") or ():
        ctx.scope.add(normalize_domain(extra))

    renderer = None
    if o["use_js_render"] and PLAYWRIGHT_AVAILABLE:
        try:
            renderer = Renderer()
        except Exception as e:
            ctx.log(f"[js] Playwright unavailable: {e}")

    q_pri: deque = deque()
    q_norm: deque = deque()
    seen: set = set()
    visited: list = []
    counters = {"pages": 0, "docs": 0}

    def enqueue(url: str, pri: bool = False):
        url = norm_url(url)
        k = url_key(url)
        if k in seen:
            return
        seen.add(k)
        (q_pri if pri else q_norm).append(url)

    # start URL: https -> https://www -> http -> http://www
    start = None
    first_resp = None
    for cand in (f"https://{domain}/", f"https://www.{domain}/", f"http://{domain}/", f"http://www.{domain}/"):
        r = ctx.get(cand)
        if r is not None:
            start, first_resp = cand, r
            break
    if start is None:
        ctx.log("[err] could not reach the domain over https/http")
        if renderer:
            renderer.close()
        return ctx.results, visited, ctx
    final = first_resp.url
    ctx.scope.add(host_of(final))
    base = f"{urlparse(final).scheme}://{urlparse(final).netloc}"
    seen.add(url_key(norm_url(start)))
    q_pri.append(norm_url(start))

    robots_delay = ctx.robots.crawl_delay(base) if o["respect_robots"] else None
    delay = max(o["delay"], float(robots_delay or 0))

    if o["seed_paths"]:
        for p in SEED_PATHS:
            enqueue(base + p, pri=True)
    if o["use_sitemap"]:
        for u in read_sitemaps(base, ctx):
            if ctx.in_scope(u) and not has_ext(u, SKIP_EXT):
                enqueue(u, pri=is_priority(u))

    cached_first = {norm_url(start): first_resp}
    attempts = 0
    consecutive_failures = 0
    max_attempts = o["max_pages"] * 3 + len(SEED_PATHS) + 20
    while (q_pri or q_norm) and attempts < max_attempts:
        url = q_pri.popleft() if q_pri else q_norm.popleft()
        is_doc = has_ext(url, DOC_EXT)
        if is_doc:
            if not o["fetch_docs"] or counters["docs"] >= o["max_docs"]:
                continue
        elif counters["pages"] >= o["max_pages"]:
            if q_pri or any(has_ext(u, DOC_EXT) for u in q_norm):
                continue          # keep draining priority items / documents only
            break
        if o["respect_robots"] and url not in cached_first and not ctx.robots.allowed(url):
            ctx.log(f"[robots] skipped {url}")
            continue
        attempts += 1
        visited.append(url)

        resp = cached_first.pop(url, None) or ctx.get(url)
        skipped, err = False, None
        htmls: list = []

        if resp is None:
            skipped, err = True, "request failed"
        else:
            ctype = resp.headers.get("Content-Type", "").lower()
            if resp.status_code == 200:
                counters["docs" if is_doc else "pages"] += 1
                if is_doc or any(t in ctype for t in ("pdf", "wordprocessingml", "vcard")):
                    text = document_text(resp.content, url, ctype)
                    t = extract_text_emails(deep_text(text))
                    ctx.add(t["plain"] | t["obfuscated"], "document(pdf/docx/vcf/txt)", url)
                elif "html" in ctype or not ctype:
                    htmls.append(decode_response(resp))
                elif any(t in ctype for t in ("text/", "json", "xml")):
                    text = deep_text(decode_response(resp))
                    t = extract_text_emails(text)
                    ctx.add(t["plain"] | t["obfuscated"], "text-file", url)
                    for m, em in extract_js(text).items():
                        ctx.add(em, m, url)
            else:
                skipped, err = True, f"HTTP {resp.status_code}"

        if renderer and not is_doc and (htmls or (resp is not None and resp.status_code in (403, 429, 503))):
            try:
                rendered, extra = renderer.render(url)
                htmls.append(rendered)
                for blob in extra:
                    t = extract_text_emails(deep_text(blob))
                    ctx.add(t["plain"] | t["obfuscated"], "rendered-xhr", url)
                if skipped:
                    counters["pages"] += 1
                skipped, err = False, None
            except Exception as e:
                ctx.log(f"[js] render failed for {url}: {e}")

        for h in htmls:
            found, links = process_html(h, url, ctx)
            for email, method in found:
                ctx.add([email], method, url)
            for lu, pri in links:
                enqueue(lu, pri)

        if progress_callback:
            progress_callback(counters["pages"] + counters["docs"], o["max_pages"] + o["max_docs"], url,
                              skipped=skipped, error=err)

        # If the site keeps failing (timeouts / connection errors), stop instead of
        # grinding through thousands of doomed requests -- otherwise the UI looks like
        # it is "loading forever" and never finishes.
        consecutive_failures = 0 if not skipped else consecutive_failures + 1
        if consecutive_failures >= MAX_CONSECUTIVE_FAILURES:
            ctx.log(f"[warn] {consecutive_failures} consecutive failed requests -- stopping early "
                    f"(the site seems unreachable or is blocking us)")
            break

        time.sleep(delay)

    if renderer:
        renderer.close()

    if o["dns_whois"]:
        dns_whois_emails(domain, ctx)
    if o["wayback"]:
        for wb in wayback_pages(domain, ctx):
            r = ctx.get(wb, check_robots=False)
            if r is not None and r.status_code == 200:
                saved = ctx.o["fetch_assets"]
                ctx.o["fetch_assets"] = False
                found, _ = process_html(decode_response(r), wb, ctx)
                ctx.o["fetch_assets"] = saved
                for email, method in found:
                    ctx.add([email], "wayback/" + method, wb)
            time.sleep(delay)

    drop_rot13_lookalikes(ctx)
    return ctx.results, visited, ctx


def drop_rot13_lookalikes(ctx: Ctx):
    """If rot13(x) is an in-scope address we found, the raw string x was only the encoded form."""
    for e in list(ctx.results):
        r = rot13(e)
        if r != e and r in ctx.results and ctx.email_in_scope(r) and not ctx.email_in_scope(e):
            del ctx.results[e]
            if ctx.on_removed:
                ctx.on_removed(e)


def split_results(results: dict, domain: str, extra_domains=()):
    scope = {normalize_domain(domain)} | {normalize_domain(d) for d in extra_domains if d.strip()}
    own, other = {}, {}
    for email, rec in results.items():
        d = email.split("@")[1]
        (own if any(d == s or d.endswith("." + s) for s in scope) else other)[email] = rec
    return own, other


# --------------------------------------------------------------------------- #
# Streamlit UI
# --------------------------------------------------------------------------- #

def run_ui():
    import streamlit as st

    st.set_page_config(page_title="Domain Email Extractor", page_icon="📧", layout="wide")
    st.title("📧 Domain Email Extractor")
    st.write("Crawls a domain and extracts email addresses, including most common obfuscation tricks.")

    domain_input = st.text_input("Domain", placeholder="example.com")
    c1, c2 = st.columns(2)
    max_pages = c1.number_input("Max pages to crawl", min_value=1, max_value=2000, value=50)
    delay = c2.number_input("Delay between requests (sec)", min_value=0.0, max_value=5.0, value=0.5, step=0.1)

    include_other = st.checkbox("Also show emails found from other domains on the site", value=False)
    extra_domains_txt = st.text_input(
        "Related domains to treat as the same organisation (comma-separated)",
        placeholder="e.g. newindianexpress.com, edexlive.com",
    )

    with st.expander("Discovery options", expanded=False):
        include_subdomains = st.checkbox("Include subdomains", value=True)
        respect_robots = st.checkbox("Respect robots.txt (+ Crawl-delay)", value=True)
        use_sitemap = st.checkbox("Read sitemap.xml / robots.txt sitemaps", value=True)
        seed_paths = st.checkbox("Try common pages (/contact, /impressum, /kontakt, /about, security.txt ...)", value=True)
        fetch_assets = st.checkbox("Scan external .js / .css files of the site", value=True)
        fetch_docs = st.checkbox(
            "Scan PDF / DOCX / vCard / TXT files", value=True, disabled=not PDF_AVAILABLE,
            help="PDF needs pypdf (DOCX, vCard and TXT work without it).",
        )
        max_docs = st.number_input("Max documents", min_value=0, max_value=200, value=10)
        use_js_render = st.checkbox(
            "Render JavaScript with a headless browser (slow, also reads XHR/JSON)",
            value=False, disabled=not PLAYWRIGHT_AVAILABLE,
            help="pip install playwright && playwright install chromium (local use).",
        )
        if not PLAYWRIGHT_AVAILABLE:
            st.caption("⚠️ JS rendering unavailable — Playwright is not installed.")

    with st.expander("Image / OCR options", expanded=False):
        use_ocr = st.checkbox("Enable OCR for image-based emails (slower)", value=False, disabled=not OCR_AVAILABLE)
        ocr_all = st.checkbox("OCR every image, not only contact-hinted ones", value=False, disabled=not OCR_AVAILABLE)
        max_images = st.number_input("Max images per page", min_value=1, max_value=100, value=15)
        if not OCR_AVAILABLE:
            st.caption("⚠️ OCR unavailable — install pytesseract + pillow and the Tesseract binary.")

    with st.expander("External sources (outside the website)", expanded=False):
        dns_whois = st.checkbox(
            "DNS (DMARC rua/ruf, SOA) and WHOIS", value=False,
            help="Often privacy-proxied, but DMARC/SOA addresses are frequently real mailboxes.",
        )
        wayback = st.checkbox("Wayback Machine (older versions of contact pages)", value=False)

    start = st.button("Start crawling", type="primary", disabled=not domain_input)

    if start and domain_input:
        status_box = st.empty()
        progress_bar = st.progress(0)
        log_box = st.expander("Crawl log", expanded=False)
        log_lines: list = []

        def push_log(msg):
            log_lines.append(msg)
            log_box.text("\n".join(log_lines[-300:]))

        def progress_callback(count, total, url, skipped, error=None):
            progress_bar.progress(min(count / max(total, 1), 1.0))
            status_box.text(f"Crawled {count} item(s)... currently: {url}")
            push_log(f"{'[skip]' if skipped else '[ok]  '} {url}{' -- ' + error if error else ''}")

        extra_domains = [d.strip() for d in extra_domains_txt.split(",") if d.strip()]
        scope_now = {normalize_domain(domain_input)} | {normalize_domain(d) for d in extra_domains}
        live_header = st.empty()
        live_box = st.empty()
        live_rows: list = []          # newest first
        live_other = {"n": 0}

        def on_removed(email):
            live_other["n"] = max(0, live_other["n"] - 1)
            live_header.markdown(f"**Found so far: {len(live_rows)}**"
                                 + (f" · {live_other['n']} from other domains" if live_other["n"] else ""))

        def on_found(email, method, url):
            d = email.split("@")[1]
            if any(d == sc or d.endswith("." + sc) for sc in scope_now):
                live_rows.insert(0, f"{email}    ({method})")
                live_header.markdown(f"**Found so far: {len(live_rows)}**"
                                     + (f" · {live_other['n']} from other domains" if live_other["n"] else ""))
                live_box.code("\n".join(live_rows), language=None)
            else:
                live_other["n"] += 1
                live_header.markdown(f"**Found so far: {len(live_rows)}** · {live_other['n']} from other domains")
        opts = dict(
            max_pages=int(max_pages), delay=float(delay), include_subdomains=include_subdomains,
            respect_robots=respect_robots, use_sitemap=use_sitemap, seed_paths=seed_paths,
            fetch_assets=fetch_assets, fetch_docs=fetch_docs, max_docs=int(max_docs),
            use_ocr=use_ocr, ocr_all=ocr_all, max_images=int(max_images),
            use_js_render=use_js_render, dns_whois=dns_whois, wayback=wayback,
            extra_domains=extra_domains,
        )

        with st.spinner("Crawling..."):
            results, visited, _ctx = crawl(domain_input, opts, progress_callback, push_log, on_found, on_removed)

        progress_bar.progress(1.0)
        status_box.text(f"Done. Crawled {len(visited)} item(s).")
        live_header.empty()
        live_box.empty()

        clean_domain = normalize_domain(domain_input)
        own, other = split_results(results, clean_domain, extra_domains)

        st.subheader(f"Emails @{clean_domain}{' + related' if extra_domains else ''} ({len(own)})")
        if own:
            emails = sorted(own)
            tab1, tab2, tab3 = st.tabs(["One per line", "Comma-separated", "With source"])
            with tab1:
                st.caption("Hover the box and click the copy icon (top-right) to copy all emails")
                st.code("\n".join(emails), language=None)
            with tab2:
                st.caption("Hover the box and click the copy icon (top-right) to copy all emails")
                st.code(", ".join(emails), language=None)
            with tab3:
                st.dataframe(
                    [{"email": e, "found via": ", ".join(sorted(own[e]["methods"])), "first seen on": own[e]["url"]}
                     for e in emails],
                    use_container_width=True,
                )
            buf = io.StringIO()
            writer = csv.writer(buf)
            writer.writerow(["email", "found_via", "first_seen_on"])
            for e in emails:
                writer.writerow([e, "|".join(sorted(own[e]["methods"])), own[e]["url"]])
            st.download_button("Download as CSV", data=buf.getvalue(), file_name=f"{clean_domain}_emails.csv", mime="text/csv")
        else:
            st.info("No emails found on that domain.")

        if include_other and other:
            st.subheader(f"Other emails found on the site ({len(other)})")
            st.caption("Hover the box and click the copy icon (top-right) to copy all emails")
            st.code("\n".join(sorted(other)), language=None)


if __name__ == "__main__":
    run_ui()
