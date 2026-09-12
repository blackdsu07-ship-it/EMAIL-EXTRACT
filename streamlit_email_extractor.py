"""
streamlit_email_extractor.py

Streamlit UI for crawling a domain and extracting email addresses,
including common obfuscation techniques:
  - Plain text
  - mailto: links
  - [at]/[dot] style text obfuscation
  - HTML entities (&#64; etc.)
  - JavaScript concatenation ("user" + "@" + "domain", .join("@"), etc.)
  - CSS direction:rtl / unicode-bidi reversal tricks
  - Cloudflare email protection (data-cfemail)
  - Base64-encoded emails
  - Image-based emails via OCR (optional, requires pytesseract + Tesseract)

Run locally:
    pip install streamlit requests beautifulsoup4 pillow
    # optional, for image OCR:
    pip install pytesseract
    # and install the Tesseract binary itself (not just the pip package):
    #   Windows: https://github.com/UB-Mannheim/tesseract/wiki
    #   Mac:     brew install tesseract
    #   Linux:   sudo apt install tesseract-ocr

    streamlit run streamlit_email_extractor.py
"""

import re
import time
import io
import csv
import html
import base64
from collections import deque
from urllib.parse import urljoin, urlparse

import requests
import streamlit as st
from bs4 import BeautifulSoup

try:
    import pytesseract
    from PIL import Image
    OCR_AVAILABLE = True
except ImportError:
    OCR_AVAILABLE = False

EMAIL_REGEX = re.compile(
    r"[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}"
)

OBFUSCATED_REGEX = re.compile(
    r"[a-zA-Z0-9._%+\-]+\s*(?:\[at\]|\(at\)|\{at\}|-at-|\sat\s)\s*"
    r"[a-zA-Z0-9\-]+"
    r"(?:\s*(?:\[dot\]|\(dot\)|\{dot\}|-dot-|\sdot\s|\.)\s*[a-zA-Z0-9\-]+)+",
    re.IGNORECASE,
)

# JS concatenation like: "user" + "@" + "example.com"
JS_CONCAT_REGEX = re.compile(
    r"""["']([a-zA-Z0-9._%+\-]+)["']\s*(?:\+|,)\s*["']@["']\s*(?:\+|,)\s*["']([a-zA-Z0-9.\-]+\.[a-zA-Z]{2,})["']""",
)

BASE64_CANDIDATE_REGEX = re.compile(r"[A-Za-z0-9+/]{16,}={0,2}")

CF_EMAIL_REGEX = re.compile(r'data-cfemail="([a-f0-9]+)"')

DEFAULT_HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; EmailExtractor/1.0)"
}


def normalize_domain(domain: str) -> str:
    domain = domain.strip().lower()
    domain = re.sub(r"^https?://", "", domain)
    domain = domain.split("/")[0]
    if domain.startswith("www."):
        domain = domain[4:]
    return domain


def clean_email(e: str) -> str:
    return e.strip().rstrip(".,;:)").lower()


def decode_cf_email(cfhex: str) -> str:
    """Decode Cloudflare's data-cfemail obfuscation."""
    try:
        r = int(cfhex[:2], 16)
        email = "".join(
            chr(int(cfhex[i:i + 2], 16) ^ r)
            for i in range(2, len(cfhex), 2)
        )
        return email
    except Exception:
        return ""


def extract_plain_and_obfuscated(text: str) -> set:
    found = set()

    def repl(m):
        s = m.group(0)
        s = re.sub(r"\[at\]|\(at\)|\{at\}|-at-|\sat\s", "@", s, flags=re.IGNORECASE)
        s = re.sub(r"\[dot\]|\(dot\)|\{dot\}|-dot-|\sdot\s", ".", s, flags=re.IGNORECASE)
        s = re.sub(r"\s+", "", s)
        return s
    deob = OBFUSCATED_REGEX.sub(repl, text)

    found.update(EMAIL_REGEX.findall(deob))
    return {clean_email(e) for e in found}


def extract_html_entities(raw_html: str) -> set:
    decoded = html.unescape(raw_html)
    return {clean_email(e) for e in EMAIL_REGEX.findall(decoded)}


def extract_js_concat(raw_html: str) -> set:
    found = set()
    for user, domain in JS_CONCAT_REGEX.findall(raw_html):
        candidate = f"{user}@{domain}"
        if EMAIL_REGEX.fullmatch(candidate):
            found.add(clean_email(candidate))

    join_pattern = re.compile(
        r"""\[\s*["']([a-zA-Z0-9._%+\-]+)["']\s*,\s*["']([a-zA-Z0-9.\-]+\.[a-zA-Z]{2,})["']\s*\]\s*\.join\(\s*["']@["']\s*\)"""
    )
    for user, domain in join_pattern.findall(raw_html):
        candidate = f"{user}@{domain}"
        if EMAIL_REGEX.fullmatch(candidate):
            found.add(clean_email(candidate))

    return found


def extract_css_reversed(soup: BeautifulSoup) -> set:
    found = set()
    candidates = soup.find_all(style=re.compile(r"direction\s*:\s*rtl|unicode-bidi\s*:\s*bidi-override", re.I))
    for el in candidates:
        text = el.get_text()
        reversed_text = text[::-1]
        found.update(EMAIL_REGEX.findall(reversed_text))
        found.update(EMAIL_REGEX.findall(text))
    return {clean_email(e) for e in found}


def extract_cloudflare(raw_html: str) -> set:
    found = set()
    for cfhex in CF_EMAIL_REGEX.findall(raw_html):
        decoded = decode_cf_email(cfhex)
        if EMAIL_REGEX.fullmatch(decoded):
            found.add(clean_email(decoded))
    return found


def extract_base64(raw_html: str) -> set:
    found = set()
    for candidate in BASE64_CANDIDATE_REGEX.findall(raw_html):
        try:
            padded = candidate + "=" * (-len(candidate) % 4)
            decoded_bytes = base64.b64decode(padded, validate=True)
            decoded_str = decoded_bytes.decode("utf-8", errors="ignore")
        except Exception:
            continue
        if "@" in decoded_str:
            for m in EMAIL_REGEX.findall(decoded_str):
                found.add(clean_email(m))
    return found


def extract_from_images(soup: BeautifulSoup, base_url: str, session: requests.Session, max_images: int = 15) -> set:
    found = set()
    if not OCR_AVAILABLE:
        return found

    imgs = soup.find_all("img", src=True)
    checked = 0
    for img in imgs:
        if checked >= max_images:
            break
        src = img["src"]
        hint = f"{src} {img.get('alt', '')} {img.get('class', '')}".lower()
        if not any(k in hint for k in ["mail", "contact", "kontakt", "email", "e-mail"]):
            continue
        img_url = urljoin(base_url, src)
        try:
            resp = session.get(img_url, timeout=10)
            image = Image.open(io.BytesIO(resp.content))
            text = pytesseract.image_to_string(image)
            found.update(EMAIL_REGEX.findall(text))
            checked += 1
        except Exception:
            continue
    return {clean_email(e) for e in found}


def extract_all_emails(raw_html: str, soup: BeautifulSoup, base_url: str,
                        session: requests.Session, use_ocr: bool) -> set:
    found = set()
    found |= extract_plain_and_obfuscated(raw_html)
    found |= extract_html_entities(raw_html)
    found |= extract_js_concat(raw_html)
    found |= extract_css_reversed(soup)
    found |= extract_cloudflare(raw_html)
    found |= extract_base64(raw_html)
    if use_ocr:
        found |= extract_from_images(soup, base_url, session)

    for a in soup.find_all("a", href=True):
        href = a["href"].strip()
        if href.startswith("mailto:"):
            addr = href[len("mailto:"):].split("?")[0]
            if addr:
                found.add(clean_email(addr))
        cf = a.get("data-cfemail")
        if cf:
            decoded = decode_cf_email(cf)
            if EMAIL_REGEX.fullmatch(decoded):
                found.add(clean_email(decoded))

    return found


def crawl(start_domain, max_pages, delay, use_ocr, progress_callback=None):
    start_domain = normalize_domain(start_domain)
    start_url = f"https://{start_domain}/"

    visited = set()
    queue = deque([start_url])
    all_emails = set()
    session = requests.Session()
    session.headers.update(DEFAULT_HEADERS)

    while queue and len(visited) < max_pages:
        url = queue.popleft()
        if url in visited:
            continue
        visited.add(url)

        try:
            resp = session.get(url, timeout=10)
        except requests.RequestException:
            if progress_callback:
                progress_callback(len(visited), max_pages, url, skipped=True)
            continue

        if resp.status_code == 200 and "text/html" in resp.headers.get("Content-Type", ""):
            try:
                soup = BeautifulSoup(resp.text, "html.parser")
            except Exception:
                soup = None

            if soup is not None:
                page_emails = extract_all_emails(resp.text, soup, url, session, use_ocr)
                all_emails.update(page_emails)

                for a in soup.find_all("a", href=True):
                    href = a["href"].strip()
                    if href.startswith("mailto:"):
                        continue
                    next_url = urljoin(url, href)
                    parsed = urlparse(next_url)
                    if parsed.scheme not in ("http", "https"):
                        continue
                    if normalize_domain(parsed.netloc) != start_domain:
                        continue
                    if next_url not in visited:
                        queue.append(next_url)

        if progress_callback:
            progress_callback(len(visited), max_pages, url, skipped=False)

        time.sleep(delay)

    domain_emails = {e for e in all_emails if e.endswith("@" + start_domain)}
    other_emails = all_emails - domain_emails
    return domain_emails, other_emails, visited


# ---------------- Streamlit UI ----------------

st.set_page_config(page_title="Domain Email Extractor", page_icon="📧")
st.title("📧 Domain Email Extractor")
st.write("Crawls a domain's own website and extracts email addresses, including common obfuscation tricks.")

domain_input = st.text_input("Domain", placeholder="example.com")

col1, col2 = st.columns(2)
with col1:
    max_pages = st.number_input("Max pages to crawl", min_value=1, max_value=1000, value=50)
with col2:
    delay = st.number_input("Delay between requests (sec)", min_value=0.0, max_value=5.0, value=0.5, step=0.1)

include_other = st.checkbox("Also show emails found from other domains on the site", value=False)

use_ocr = st.checkbox(
    "Enable OCR for image-based emails (slower)",
    value=False,
    disabled=not OCR_AVAILABLE,
    help="Requires pytesseract + Tesseract installed. Only checks images whose src/alt hints at contact/email."
)
if not OCR_AVAILABLE:
    st.caption("⚠️ OCR unavailable — install with `pip install pytesseract pillow` and install the Tesseract binary to enable.")

start = st.button("Start crawling", type="primary", disabled=not domain_input)

if start and domain_input:
    status_box = st.empty()
    progress_bar = st.progress(0)
    log_box = st.expander("Crawl log", expanded=False)
    log_lines = []

    def progress_callback(count, total, url, skipped):
        progress_bar.progress(min(count / total, 1.0))
        status_box.text(f"Crawled {count}/{total} pages... currently: {url}")
        log_lines.append(f"{'[skip]' if skipped else '[ok]  '} {url}")
        log_box.text("\n".join(log_lines[-200:]))

    with st.spinner("Crawling..."):
        domain_emails, other_emails, visited = crawl(
            domain_input, int(max_pages), float(delay), use_ocr, progress_callback
        )

    progress_bar.progress(1.0)
    status_box.text(f"Done. Crawled {len(visited)} page(s).")

    clean_domain = normalize_domain(domain_input)
    st.subheader(f"Emails @{clean_domain} ({len(domain_emails)})")
    if domain_emails:
        sorted_emails = sorted(domain_emails)

        tab1, tab2 = st.tabs(["One per line", "Comma-separated"])
        with tab1:
            st.caption("Hover the box and click the copy icon (top-right) to copy all emails")
            st.code("\n".join(sorted_emails), language=None)
        with tab2:
            st.caption("Hover the box and click the copy icon (top-right) to copy all emails")
            st.code(", ".join(sorted_emails), language=None)

        buf = io.StringIO()
        writer = csv.writer(buf)
        writer.writerow(["email"])
        for e in sorted_emails:
            writer.writerow([e])
        st.download_button(
            "Download as CSV",
            data=buf.getvalue(),
            file_name=f"{clean_domain}_emails.csv",
            mime="text/csv",
        )
    else:
        st.info("No emails found on that domain.")

    if include_other and other_emails:
        sorted_other = sorted(other_emails)
        st.subheader(f"Other emails found on the site ({len(other_emails)})")
        st.caption("Hover the box and click the copy icon (top-right) to copy all emails")
        st.code("\n".join(sorted_other), language=None)
