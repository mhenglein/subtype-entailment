#!/usr/bin/env python3
"""Render the C081 manuscript with Pandoc/Tectonic; preserve source provenance."""
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
    # Promote section levels after extracting the title; numbers are authored.
    body = re.sub(r"^##", "#", body, flags=re.M)
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
    body = body.replace("# 1. The theorem", "\\newpage\n\\begingroup\\small\n\\tableofcontents\n\\endgroup\n\\newpage\n\n# 1. The theorem", 1)
    OUT.mkdir(parents=True, exist_ok=True)
    scratch = ROOT / "tmp" / "pdfs" / "c081"
    scratch.mkdir(parents=True, exist_ok=True)
    md = scratch / "paper.md"
    md.write_text(body)
    tex = OUT / "subtail-paper.tex"
    run(["pandoc", str(md), "--from=markdown+tex_math_dollars+raw_tex", "--standalone",
         "--to=latex", "--metadata", f"title={title}", "--metadata", "author=Author and affiliation placeholders",
         "--metadata", "date=Research draft, 20 September 2026",
         "--variable", "documentclass=article", "--variable", "fontsize=11pt",
         "--variable", "geometry=margin=25mm", "--variable", "colorlinks=true",
         "--variable", "urlcolor=blue", "--variable", "toc-depth=2",
         "--include-in-header", str(PAPER / "header.tex"), "--output", str(tex)])
    run(["tectonic", str(tex), "--outdir", str(OUT), "--keep-logs"])
    pdf = OUT / "subtail-paper.pdf"
    source_paths = (PAPER / "manuscript.md", PAPER / "header.tex", PAPER / "build.py", PAPER / "lean-map.json")
    source_matches = all(
        run(["git", "show", f"{revision}:{p.relative_to(ROOT).as_posix()}"], capture_output=True).stdout
        == p.read_text() for p in source_paths
    )
    manifest = {
        "status": "research draft; licensing pending; author placeholders",
        "repository_revision_at_render": revision,
        "source_files_match_render_revision": source_matches,
        "mathematical_source_revision": json.loads((PAPER / "lean-map.json").read_text())["source_revision"],
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
