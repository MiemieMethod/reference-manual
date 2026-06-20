from __future__ import annotations

import argparse
import ast
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANUAL = ROOT / "Manual"
MANUAL_ZH = ROOT / "ManualZh"

DOC_RE = re.compile(r'^\s*#doc\s+\(Manual\)\s+"((?:[^"\\]|\\.)*)"\s*=>\s*$')
HEADING_RE = re.compile(r"^\s{0,3}(#{1,6})\s+(.+?)\s*$")
FENCE_RE = re.compile(r"^\s*(`{3,}|~{3,})")
MARKDOWN_BLOCK_RE = re.compile(r"^\s*(`{3,}|~{3,})markdown\b")
FILE_RE = re.compile(r'^(\s*)file\s*:=\s*(?:some\s+)?"([^"]*)"\s*$')

VALID_SLUG_CHARS = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-_")
MANGLE = {
    "<": "_LT_",
    ">": "_GT_",
    ";": "_SEMI_",
    "‹": "_FLQ_",
    "›": "_FRQ_",
    "«": "_FLQQ_",
    "»": "_FLQQ_",
    "⟨": "_LANGLE_",
    "⟩": "_RANGLE_",
    "(": "_LPAR_",
    ")": "_RPAR_",
    "[": "_LSQ_",
    "]": "_RSQ_",
    "→": "_ARR_",
    "↦": "_MAPSTO_",
    "⊢": "_VDASH_",
}


@dataclass(frozen=True)
class Node:
    line: int
    kind: str
    level: int
    title: str
    metadata_span: tuple[int, int] | None
    file: str | None


def decode_lean_string(text: str) -> str:
    # The titles used here are simple string literals. Handle the common escapes
    # without trying to be a full Lean string parser.
    try:
        value = ast.literal_eval(f'"{text}"')
    except (SyntaxError, ValueError):
        return text
    return value if isinstance(value, str) else text


def slugify(text: str) -> str:
    out: list[str] = []
    for char in text:
        if char in VALID_SLUG_CHARS:
            out.append(char)
        elif char.isspace():
            out.append("-")
        else:
            out.append(MANGLE.get(char, "___"))
    return "".join(out)


def metadata_span(lines: list[str], start: int) -> tuple[int, int] | None:
    i = start
    while i < len(lines) and not lines[i].strip():
        i += 1
    if i >= len(lines) or lines[i].strip() != "%%%":
        return None
    j = i + 1
    while j < len(lines) and lines[j].strip() != "%%%":
        j += 1
    if j >= len(lines):
        return None
    return i, j


def metadata_file(lines: list[str], span: tuple[int, int] | None) -> str | None:
    if span is None:
        return None
    start, end = span
    for line in lines[start + 1 : end]:
        match = FILE_RE.match(line.rstrip("\n"))
        if match:
            return match.group(2)
    return None


def strip_heading_markup(text: str) -> str:
    text = text.strip()
    if text.endswith("#"):
        text = re.sub(r"\s+#+\s*$", "", text)
    return text.strip()


def nodes(lines: list[str]) -> list[Node]:
    out: list[Node] = []
    in_fence = False
    in_metadata = False
    in_markdown_block = False
    markdown_outer_fence: str | None = None

    for i, line in enumerate(lines):
        stripped = line.strip()

        if in_markdown_block:
            if stripped == markdown_outer_fence:
                in_markdown_block = False
                markdown_outer_fence = None
            continue

        markdown = MARKDOWN_BLOCK_RE.match(line)
        if markdown:
            in_markdown_block = True
            markdown_outer_fence = markdown.group(1)
            continue

        if stripped == "%%%":
            in_metadata = not in_metadata
            continue

        if in_metadata:
            continue

        if FENCE_RE.match(line):
            in_fence = not in_fence
            continue

        if in_fence:
            continue

        if match := DOC_RE.match(line):
            span = metadata_span(lines, i + 1)
            out.append(Node(i, "doc", 0, decode_lean_string(match.group(1)), span, metadata_file(lines, span)))
            continue

        if match := HEADING_RE.match(line):
            span = metadata_span(lines, i + 1)
            out.append(
                Node(
                    i,
                    "heading",
                    len(match.group(1)),
                    strip_heading_markup(match.group(2)),
                    span,
                    metadata_file(lines, span),
                )
            )

    return out


def route_for(node: Node) -> str:
    return node.file if node.file is not None else slugify(node.title)


def sync_file(src_path: Path, zh_path: Path, *, check: bool) -> tuple[bool, list[str], int]:
    src_lines = src_path.read_text(encoding="utf-8").splitlines(keepends=True)
    zh_lines = zh_path.read_text(encoding="utf-8").splitlines(keepends=True)
    src_nodes = nodes(src_lines)
    zh_nodes = nodes(zh_lines)

    diagnostics: list[str] = []
    if len(src_nodes) != len(zh_nodes):
        diagnostics.append(
            f"{zh_path.relative_to(ROOT)}: node count mismatch: "
            f"{len(src_nodes)} English, {len(zh_nodes)} Chinese"
        )
        return False, diagnostics, 0

    replacements: list[tuple[int, int, list[str]]] = []
    changed = 0
    for index, (src_node, zh_node) in enumerate(zip(src_nodes, zh_nodes), start=1):
        if (src_node.kind, src_node.level) != (zh_node.kind, zh_node.level):
            diagnostics.append(
                f"{zh_path.relative_to(ROOT)}:{zh_node.line + 1}: node {index} shape mismatch: "
                f"{src_node.kind} level {src_node.level}, Chinese has {zh_node.kind} level {zh_node.level}"
            )
            continue

        route = route_for(src_node)
        if zh_node.file == route:
            continue

        changed += 1
        file_line = f'file := "{route}"\n'
        if zh_node.metadata_span is None:
            replacements.append((zh_node.line + 1, zh_node.line + 1, ["%%%\n", file_line, "%%%\n"]))
            continue

        start, end = zh_node.metadata_span
        replaced = False
        block = zh_lines[start : end + 1].copy()
        new_block: list[str] = []
        for offset in range(1, len(block) - 1):
            match = FILE_RE.match(block[offset].rstrip("\n"))
            if match:
                if not replaced:
                    new_block.append(f'{match.group(1)}file := "{route}"\n')
                    replaced = True
                continue
            new_block.append(block[offset])
        block = [block[0], *new_block, block[-1]]
        if not replaced:
            block.insert(1, file_line)
        replacements.append((start, end + 1, block))

    if diagnostics:
        return False, diagnostics, changed

    if replacements and not check:
        for start, end, replacement in reversed(replacements):
            zh_lines[start:end] = replacement
        zh_path.write_text("".join(zh_lines), encoding="utf-8", newline="")

    return bool(replacements), diagnostics, changed


def paired_files() -> list[tuple[Path, Path]]:
    pairs = [(ROOT / "Manual.lean", ROOT / "ManualZh.lean")]
    for zh_path in sorted(MANUAL_ZH.rglob("*.lean")):
        src_path = MANUAL / zh_path.relative_to(MANUAL_ZH)
        if src_path.exists():
            pairs.append((src_path, zh_path))
    return pairs


def main() -> None:
    parser = argparse.ArgumentParser(description="Sync Chinese manual route file metadata from English sources.")
    parser.add_argument("--check", action="store_true", help="Report pending changes without writing files.")
    args = parser.parse_args()

    changed_files = 0
    changed_nodes = 0
    diagnostics: list[str] = []
    for src_path, zh_path in paired_files():
        changed, file_diagnostics, count = sync_file(src_path, zh_path, check=args.check)
        diagnostics.extend(file_diagnostics)
        if changed:
            changed_files += 1
            changed_nodes += count
            print(f"{zh_path.relative_to(ROOT)}: {'would update' if args.check else 'updated'} {count}")

    for diagnostic in diagnostics:
        print(diagnostic)
    if diagnostics:
        raise SystemExit(1)

    print(f"changed files: {changed_files}")
    print(f"changed route metadata entries: {changed_nodes}")


if __name__ == "__main__":
    main()
