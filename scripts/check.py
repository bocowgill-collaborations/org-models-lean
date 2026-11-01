#!/usr/bin/env python3
"""Check public source structure, mathematical names, proof guards and source links.

This is a static supplement to `lake build`, not a replacement for kernel checking.
"""
import argparse
import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit
if sys.version_info < (3, 11):
    raise SystemExit("Source checks require Python 3.11 or newer.")
import tomllib
ROOT = Path(__file__).resolve().parents[1]
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide|unsafe|axiom|sorryAx)\b")
AUTHOR_IDENTIFIER = re.compile(r"(?i)\b[\w.']*(?:csaszar|ganz|orgsci|institutionaldesign|adaptiverationality|chapter|paper_)[\w.']*\b")
IMPORT = re.compile(r"^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)$", re.MULTILINE)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
def require(condition, message):
    if not condition:
        raise ValueError(message)

def strip_lean_comments_strings(text):
    """Preserve token boundaries while handling nested block comments."""
    output, i, nesting = [], 0, 0
    while i < len(text):
        if nesting:
            if text.startswith("/-", i):
                nesting += 1
                i += 2
            elif text.startswith("-/", i):
                nesting -= 1
                i += 2
            else:
                output.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            nesting = 1
            i += 2
            output.append(" ")
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            output.append(" ")
        elif text[i] == '"':
            output.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    output.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            output.append(text[i])
            i += 1
    require(nesting == 0, "Unclosed Lean block comment")
    return "".join(output)


def expected_roots(root):
    config = tomllib.loads((root / "lakefile.toml").read_text())
    executable_roots = {entry.get("root", entry["name"]) for entry in config.get("lean_exe", [])}
    result = {}
    for entry in config.get("lean_lib", []):
        name = entry["name"]
        modules = sorted(
            ".".join(path.relative_to(root).with_suffix("").parts)
            for path in (root / name).rglob("*.lean")
        )
        result[f"{name}.lean"] = "".join(f"import {module}\n" for module in modules
                                         if module not in executable_roots)
    return result


def check(root=ROOT, write_imports=False):
    config = tomllib.loads((root / "lakefile.toml").read_text())
    manifest = json.loads((root / "lake-manifest.json").read_text())
    require((root / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean pin changed")
    require(config["name"] == manifest["name"], "Lake package identity mismatch")
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    require(mathlib["rev"] == "8f9d9cff6bd728b17a24e163c9402775d9e6a365", "Mathlib pin changed")
    require(next(p for p in config["require"] if p["name"] == "mathlib")["rev"] == mathlib["rev"], "Lake pin mismatch")
    for package in manifest["packages"]:
        require(package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"]), "Unpinned dependency")
    roots = expected_roots(root)
    for name, expected in roots.items():
        if write_imports:
            (root / name).write_text(expected)
        require((root / name).read_text() == expected, f"Stale aggregate {name}; use --write-imports")
    files = sorted({*root.glob("*.lean"), *(root / "OrgLib").rglob("*.lean"),
                    *(root / "OrgLibExamples").rglob("*.lean"), *(root / "OrgLibTest").rglob("*.lean"),
                    *(root / "examples/external-client").glob("*.lean")})
    audits = []
    for path in files:
        text = path.read_text()
        code = strip_lean_comments_strings(text)
        relative = path.relative_to(root).as_posix()
        require(not FORBIDDEN.search(code), f"Forbidden proof token: {relative}")
        require(not AUTHOR_IDENTIFIER.search(code), f"Source-specific Lean identifier: {relative}")
        require(not AUTHOR_IDENTIFIER.search(path.stem), f"Source-specific module name: {relative}")
        require(max(map(len, text.splitlines()), default=0) <= 100, f"Lean line exceeds 100 columns: {relative}")
        if path.is_relative_to(root / "OrgLib") or path.name == "OrgLib.lean":
            imports = [word for line in IMPORT.findall(code) for word in line.split() if word != "all"]
            require(all(not word.startswith(("OrgLibExamples", "OrgLibTest", "Client")) for word in imports),
                    f"Example/test dependency crossed core boundary: {relative}")
        if path.name.endswith("Axioms.lean"):
            require("Lean.collectAxioms" in text and all(a in text for a in ALLOWED_AXIOMS), f"Missing axiom guard: {relative}")
            audits.append(relative)
    require(audits, "Missing build-time axiom guards")
    prose, fenced = [], False
    for line in (root / "README.md").read_text().splitlines():
        if line.lstrip().startswith("```"):
            fenced = not fenced
        elif not fenced:
            line = re.sub(r"`[^`]*`", "", line)
            prose.append(re.sub(r"\]\([^)]*\)", "]", line))
    require(not re.search(r"\borglib\b", "\n".join(prose), re.I), "README uses technical namespace as branding")
    ledger = json.loads((root / "docs/SOURCE_CORRESPONDENCE.json").read_text())
    references = 0
    for row in ledger["entries"]:
        path = root / row["lean_file"]
        require(path.is_file(), f"Missing source correspondence file: {row['lean_file']}")
        code = strip_lean_comments_strings(path.read_text())
        for declaration in row["lean_declarations"]:
            leaf = declaration.rsplit(".", 1)[-1]
            require(re.search(r"\b" + re.escape(leaf) + r"\b", code), f"Missing source declaration: {declaration}")
            references += 1
    claims = json.loads((root / "docs/CLAIMS.json").read_text())["declarations"]
    for row in claims:
        lines = (root / row["file"]).read_text().splitlines()
        require(1 <= row["line"] <= len(lines) and row["local_name"] in lines[row["line"] - 1], f"Stale claim pointer: {row['name']}")
        require(re.match(r"(?:def|theorem|structure|abbrev)\s+" + re.escape(row["local_name"]) + r"\b",
                         lines[row["line"] - 1]), f"Claim pointer is not a declaration: {row['name']}")
        expected_link = f'[{row["readme_label"]}]({row["file"]}#L{row["line"]})'
        require(expected_link in (root / "README.md").read_text(),
                f"README claim link does not identify its declaration: {row['name']}")
    link_count = 0
    documents = [root / "README.md", root / "DESIGN.md", root / "CONTRIBUTING.md",
                 *sorted((root / "docs").glob("*.md")), root / "supplements/README.md",
                 root / "examples/external-client/README.md"]
    for path in documents:
        if not path.exists():
            continue
        for raw in re.findall(r"\[[^\]]*\]\(([^)]+)\)", path.read_text()):
            target = urlsplit(raw.strip("<>"))
            if target.scheme or not target.path:
                continue
            destination = (path.parent / unquote(target.path)).resolve()
            require(destination.is_file(), f"Broken local link in {path.relative_to(root)}: {raw}")
            if re.fullmatch(r"L\d+", target.fragment):
                require(int(target.fragment[1:]) <= len(destination.read_text().splitlines()), f"Broken line anchor: {raw}")
            link_count += 1
    return {"status": "passed", "lean_files": len(files), "axiom_guard_modules": len(audits),
            "source_correspondence_rows": len(ledger["entries"]), "declaration_references": references,
            "claim_pointers": len(claims), "local_links": link_count, "pinned_dependencies": len(manifest["packages"]),
            "scope": "Static structure; run lake build for proof checking; human review is separate"}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-imports", action="store_true")
    args = parser.parse_args()
    try:
        print(json.dumps(check(ROOT, args.write_imports), indent=2))
    except (ValueError, OSError, KeyError, StopIteration) as error:
        print(f"Source check failed: {error}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
