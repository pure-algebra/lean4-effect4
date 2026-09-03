"""Check downloaded bytes, bibliography identity, page parsing, and text copies."""
import hashlib
import io
import json
import logging
import re
import subprocess
import unicodedata
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path

from pypdf import PdfReader

ROOT = Path(__file__).resolve().parent


def normal(text):
    text = unicodedata.normalize("NFKD", text.replace("&", "and"))
    return re.sub("[^a-z0-9]", "", text.encode("ascii", "ignore").decode().lower())


class HTMLText(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.skip = 0
        self.ids = set()

    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self.skip += 1
        for name, value in attrs:
            if name == "id":
                self.ids.add(value)
        if tag in ("p", "div", "li", "section", "h1", "h2", "h3", "h4", "dt", "dd", "pre", "tr", "br"):
            self.parts.append("\n")

    def handle_endtag(self, tag):
        if tag in ("script", "style"):
            self.skip -= 1

    def handle_data(self, data):
        if not self.skip:
            self.parts.append(data)


def main():
    manifest = json.loads((ROOT / "manifest.json").read_text())
    rows = manifest["sources"]
    assert len(rows) == 22 and len({r["id"] for r in rows}) == 22
    assert all(r["status"] == "downloaded" for r in rows)
    assert len({r["sha256"] for r in rows}) == 22, "Duplicate source documents"
    input_row = manifest["request_document"]
    assert hashlib.sha256((ROOT / input_row["file"]).read_bytes()).hexdigest() == input_row["sha256"]
    (ROOT / "text").mkdir(exist_ok=True)
    checks = []
    for row in rows:
        path = ROOT / row["file"]
        data = path.read_bytes()
        assert len(data) == row["bytes"], path
        assert hashlib.sha256(data).hexdigest() == row["sha256"], path
        result = dict(id=row["id"], file=row["file"], bytes_match=True, sha256_match=True)
        if path.suffix == ".pdf":
            warnings = io.StringIO()
            handler = logging.StreamHandler(warnings)
            logger = logging.getLogger("pypdf")
            logger.addHandler(handler)
            try:
                reader = PdfReader(path)
                pages = [page.extract_text() or "" for page in reader.pages]
            finally:
                logger.removeHandler(handler)
            assert pages and sum(map(len, pages)) > 1000, path
            opening = "\n".join(pages[:3])
            assert normal(row["title"]) in normal(opening), (row["id"], "title mismatch")
            # Use independent Poppler parsing to confirm the page count.
            info = subprocess.run(["pdfinfo", str(path)], capture_output=True, text=True)
            assert info.returncode == 0, (path, info.stderr)
            count = int(re.search(r"^Pages:\s+(\d+)", info.stdout, re.M).group(1))
            assert count == len(pages), path
            text = "\n\n".join(f"--- PDF page {i+1} ---\n{p}" for i, p in enumerate(pages))
            versions = sorted(set(re.findall(r"arXiv:\s*(\d{4}\.\d{4,5}v\d+)", text)))
            if row["id"] == "03":
                assert "2211.06863v1" in versions
            if row["id"] == "15":
                assert "2302.01415v1" in versions
            result.update(pages=len(pages), all_pages_extracted=True,
                          title_match=True, pdfinfo_page_count_match=True,
                          arxiv_versions=versions,
                          pypdf_warnings=warnings.getvalue().splitlines())
            if info.stderr:
                result["pdfinfo_warnings"] = info.stderr.strip().splitlines()
        else:
            html = data.decode("utf-8")
            parser = HTMLText()
            parser.feed(html)
            assert "idl-exceptions" in parser.ids
            assert re.search(r"<title>Web IDL Standard</title>", html)
            text = re.sub(r"\n[ \t]*\n+", "\n\n", "".join(parser.parts)).strip() + "\n"
            assert len(text) > 100000 and "throw" in text and "reject" in text
            result.update(title_match=True, exceptions_anchor_present=True)
        text_path = ROOT / "text" / (path.stem + ".txt")
        text_path.write_text(text)
        result.update(text_file=str(text_path.relative_to(ROOT)),
                      extracted_characters=len(text),
                      text_sha256=hashlib.sha256(text_path.read_bytes()).hexdigest())
        checks.append(result)
        print(f"PASS {row['id']}: {row['title']}", flush=True)
    expected = {r["file"] for r in rows}
    actual = {str(p.relative_to(ROOT)) for folder in ("papers", "standards")
              for p in (ROOT / folder).iterdir() if p.is_file()}
    assert expected == actual, "Missing or unrecorded downloaded files"
    assert not list(ROOT.rglob("*.part")), "Incomplete download file remains"
    summary = dict(verified_at=datetime.now(timezone.utc).isoformat(),
                   sources_checked=len(checks), pdfs_checked=21,
                   pdf_pages_checked=sum(c.get("pages", 0) for c in checks),
                   original_bytes=sum(r["bytes"] for r in rows),
                   unrecorded_files=0, missing_sources=0,
                   all_checks_passed=True, checks=checks)
    (ROOT / "verification.json").write_text(json.dumps(summary, indent=2) + "\n")
    sums = [f"{r['sha256']}  {r['file']}" for r in rows]
    sums.append(f"{input_row['sha256']}  {input_row['file']}")
    (ROOT / "SHA256SUMS").write_text("\n".join(sums) + "\n")
    print(f"Verified {len(checks)} sources, {summary['pdf_pages_checked']} PDF pages, {summary['original_bytes']} bytes.")


if __name__ == "__main__":
    main()
