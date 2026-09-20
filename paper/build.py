#!/usr/bin/env python3
"""Render the mathematical manuscript with Pandoc/Tectonic; preserve source provenance."""
import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
OUT = ROOT / "output" / "pdf"


def run(args, **kwargs):
    return subprocess.run(args, cwd=ROOT, check=True, text=True, **kwargs)


def main():
    for executable in ("pandoc", "tectonic"):
        if not shutil.which(executable):
            raise SystemExit(f"Missing {executable}; see paper/README.md")
    run(["python3", "paper/check.py"])
    revision = run(["git", "rev-parse", "HEAD"], capture_output=True).stdout.strip()
    source = (PAPER / "manuscript.md").read_text()
    title, body = source.split("\n", 1)
    title = title.removeprefix("# ")
    body = body.replace("Authors and affiliations: **[placeholders]**.\n", "", 1)
    # Promote section levels after extracting the title; numbers are authored.
    body = re.sub(r"^##", "#", body, flags=re.M)
    # Keep the proof-end symbol with the preceding sentence.
    body = body.replace(r" $\square$", r"\nobreak\hspace{.5em}$\square$")
    # Paper-relative source links become immutable repository links in the PDF.
    def absolute_link(match):
        label, target = match.groups()
        if "://" in target or target.startswith("#"):
            return match.group(0)
        file_part, sep, fragment = target.partition("#")
        local = (PAPER / file_part).resolve()
        rel = local.relative_to(ROOT).as_posix()
        if not local.is_file():
            raise ValueError(f"Missing manuscript link: {target}")
        suffix = sep + fragment if sep else ""
        return f"[{label}](https://github.com/mhenglein/subtail/blob/{revision}/{rel}{suffix})"
    body = re.sub(r"\[([^\]]+)\]\(([^)]+)\)", absolute_link, body)
    # Force a separate contents page after the abstract and before Section 1.
    body = body.replace("# 1. Introduction", "\\newpage\n\\begingroup\\small\n\\tableofcontents\n\\endgroup\n\\newpage\n\n# 1. Introduction", 1)
    # Give the bibliography a clean page instead of splitting its final entries.
    body = body.replace("# References\n", "\\newpage\n\n# References\n", 1)
    OUT.mkdir(parents=True, exist_ok=True)
    scratch = ROOT / "tmp" / "pdfs" / "paper-rewrite"
    scratch.mkdir(parents=True, exist_ok=True)
    md = scratch / "paper.md"
    md.write_text(body)
    tex = OUT / "subtail-paper.tex"
    run(["pandoc", str(md), "--from=markdown+tex_math_dollars+raw_tex", "--standalone",
         "--to=latex", "--metadata", f"title={title}", "--metadata", "author=Author and affiliation placeholders",
         "--metadata", "date=20 September 2026",
         "--citeproc", "--bibliography", str(PAPER / "references.bib"),
         "--csl", str(PAPER / "references.csl"), "--metadata", "link-citations=true",
         "--variable", "documentclass=article", "--variable", "fontsize=11pt", "--variable", "papersize=a4",
         "--variable", "geometry=margin=25mm", "--variable", "colorlinks=true",
         "--variable", "urlcolor=blue", "--variable", "linkcolor=black",
         "--variable", "citecolor=blue", "--variable", "toc-depth=2",
         "--include-in-header", str(PAPER / "header.tex"), "--output", str(tex)])
    run(["tectonic", str(tex), "--outdir", str(OUT), "--keep-logs"])
    pdf = OUT / "subtail-paper.pdf"
    source_paths = (PAPER / "manuscript.md", PAPER / "header.tex", PAPER / "build.py", PAPER / "lean-map.json",
                    PAPER / "references.bib", PAPER / "references.csl")
    def committed_source_matches(path):
        result = subprocess.run(
            ["git", "show", f"{revision}:{path.relative_to(ROOT).as_posix()}"],
            cwd=ROOT, text=True, capture_output=True)
        return result.returncode == 0 and result.stdout == path.read_text()
    source_matches = all(committed_source_matches(p) for p in source_paths)
    mapping = json.loads((PAPER / "lean-map.json").read_text())
    manifest = {
        "status": "research draft; licensing pending; author placeholders",
        "repository_revision_at_render": revision,
        "source_files_match_render_revision": source_matches,
        "mathematical_source_revisions": sorted({
            row.get("source_revision", mapping["source_revision"])
            for row in mapping["entries"]}),
        "tools": {name: run([name, "--version"], capture_output=True).stdout.splitlines()[0] for name in ("pandoc", "tectonic")},
        "sources": {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in source_paths},
        "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest(),
        "validation": "Rendering only; visual and mathematical reviews recorded separately."
    }
    (OUT / "subtail-paper-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(pdf)


if __name__ == "__main__":
    main()
