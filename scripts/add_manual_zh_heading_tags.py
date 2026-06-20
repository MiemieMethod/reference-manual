from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANUAL = ROOT / "ManualZh"

HEADING_RE = re.compile(r"^\s{0,3}(#{1,6})\s+.+$")
DOC_RE = re.compile(r'^\s*#doc\s+\(Manual\)\s+".*"\s*=>\s*$')
FENCE_RE = re.compile(r"^\s*(`{3,}|~{3,})")
MARKDOWN_BLOCK_RE = re.compile(r"^\s*(`{3,}|~{3,})markdown\b")
GENERATED_TAG_RE = re.compile(r'^tag := "zh-[^"]+"$')
ANY_TAG_RE = re.compile(r"^tag\s*:=")


def slugify_path(path: Path) -> str:
    rel = path.relative_to(MANUAL).with_suffix("").as_posix().lower()
    slug = re.sub(r"[^a-z0-9]+", "-", rel).strip("-")
    return slug or "root"


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


def metadata_has_tag(lines: list[str], span: tuple[int, int]) -> bool:
    start, end = span
    return any(ANY_TAG_RE.match(line.strip()) for line in lines[start + 1 : end])


def remove_generated_tags(lines: list[str]) -> tuple[list[str], int]:
    out: list[str] = []
    removed = 0
    i = 0
    while i < len(lines):
        if lines[i].strip() == "%%%":
            block = [lines[i]]
            j = i + 1
            kept_nonblank = False
            while j < len(lines) and lines[j].strip() != "%%%":
                if GENERATED_TAG_RE.match(lines[j].strip()):
                    removed += 1
                else:
                    block.append(lines[j])
                    kept_nonblank = kept_nonblank or bool(lines[j].strip())
                j += 1
            if j < len(lines):
                block.append(lines[j])
                j += 1
            if kept_nonblank:
                out.extend(block)
            i = j
            continue
        out.append(lines[i])
        i += 1
    return out, removed


def add_tags(path: Path) -> int:
    original = path.read_text(encoding="utf-8").splitlines(keepends=True)
    lines, removed = remove_generated_tags(original)
    out: list[str] = []
    in_fence = False
    in_metadata = False
    in_markdown_block = False
    markdown_outer_fence: str | None = None
    heading_index = 0
    doc_index = 0
    added = 0
    file_slug = slugify_path(path)
    insert_after: dict[int, str] = {}

    for i, line in enumerate(lines):
        stripped = line.strip()

        if in_markdown_block:
            if stripped == markdown_outer_fence:
                in_markdown_block = False
                markdown_outer_fence = None
                out.append(line)
                continue
            out.append(line)
            continue

        md = MARKDOWN_BLOCK_RE.match(line)
        if md:
            in_markdown_block = True
            markdown_outer_fence = md.group(1)
            out.append(line)
            continue

        if stripped == "%%%":
            in_metadata = not in_metadata
            out.append(line)
            if i in insert_after:
                out.append(f'tag := "{insert_after[i]}"\n')
                added += 1
            continue

        if not in_metadata and FENCE_RE.match(line):
            in_fence = not in_fence
            out.append(line)
            continue

        if not in_fence and not in_metadata and DOC_RE.match(line):
            doc_index += 1
            out.append(line)
            root_suffix = "root" if doc_index == 1 else f"root-{doc_index:03d}"
            tag = f"zh-{file_slug}-{root_suffix}"
            span = metadata_span(lines, i + 1)
            if span is None:
                out.append("%%%\n")
                out.append(f'tag := "{tag}"\n')
                out.append("%%%\n")
                added += 1
            elif not metadata_has_tag(lines, span):
                insert_after[span[0]] = tag
            continue

        if not in_fence and not in_metadata and HEADING_RE.match(line):
            heading_index += 1
            out.append(line)
            tag = f"zh-{file_slug}-h{heading_index:03d}"
            span = metadata_span(lines, i + 1)
            if span is None:
                out.append("%%%\n")
                out.append(f'tag := "{tag}"\n')
                out.append("%%%\n")
                added += 1
            elif not metadata_has_tag(lines, span):
                insert_after[span[0]] = tag
            continue

        out.append(line)

    new_text = "".join(out)
    if new_text != "".join(original):
        path.write_text(new_text, encoding="utf-8", newline="")
        return added
    return 0


def main() -> None:
    total = 0
    changed = 0
    for path in sorted(MANUAL.rglob("*.lean")):
        added = add_tags(path)
        if added:
            changed += 1
            total += added
            print(f"{path.relative_to(ROOT)}: added {added}")
    print(f"changed files: {changed}")
    print(f"added tags: {total}")


if __name__ == "__main__":
    main()
