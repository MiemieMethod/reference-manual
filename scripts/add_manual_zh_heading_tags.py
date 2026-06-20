from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MANUAL = ROOT / "ManualZh"

HEADING_RE = re.compile(r"^\s{0,3}(#{1,6})\s+.+$")
FENCE_RE = re.compile(r"^\s*(`{3,}|~{3,})")
MARKDOWN_BLOCK_RE = re.compile(r"^\s*(`{3,}|~{3,})markdown\b")
GENERATED_TAG_RE = re.compile(r'^tag := "zh-[^"]+"$')


def slugify_path(path: Path) -> str:
    rel = path.relative_to(MANUAL).with_suffix("").as_posix().lower()
    slug = re.sub(r"[^a-z0-9]+", "-", rel).strip("-")
    return slug or "root"


def next_nonblank(lines: list[str], start: int) -> str | None:
    for line in lines[start:]:
        if line.strip():
            return line.strip()
    return None


def remove_generated_tags(lines: list[str]) -> tuple[list[str], int]:
    out: list[str] = []
    removed = 0
    i = 0
    while i < len(lines):
        if (
            i + 2 < len(lines)
            and lines[i].strip() == "%%%"
            and GENERATED_TAG_RE.match(lines[i + 1].strip())
            and lines[i + 2].strip() == "%%%"
        ):
            removed += 1
            i += 3
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
    added = 0
    file_slug = slugify_path(path)

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
            continue

        if not in_metadata and FENCE_RE.match(line):
            in_fence = not in_fence
            out.append(line)
            continue

        if not in_fence and not in_metadata and HEADING_RE.match(line):
            heading_index += 1
            out.append(line)
            if next_nonblank(lines, i + 1) != "%%%":
                tag = f"zh-{file_slug}-h{heading_index:03d}"
                out.append("%%%\n")
                out.append(f'tag := "{tag}"\n')
                out.append("%%%\n")
                added += 1
            continue

        out.append(line)

    if added or removed:
        path.write_text("".join(out), encoding="utf-8", newline="")
    return added


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
