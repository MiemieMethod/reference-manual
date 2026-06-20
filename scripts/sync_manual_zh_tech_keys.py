#!/usr/bin/env python3
"""Copy stable technical-term keys from the English manual to ManualZh.

The Chinese translation keeps the visible term text translated, but Verso's
term lookup still needs to use the same semantic keys as the source manual.
This script aligns `{tech}` and `{deftech}` occurrences with the corresponding
English file and inserts `key := "..."` where the translated occurrence does
not already have an explicit key.
"""

from __future__ import annotations

import argparse
import bisect
import difflib
import re
from dataclasses import dataclass
from pathlib import Path


TERM_RE = re.compile(
    r"\{(?P<kind>deftech|tech)(?P<opts>(?:[^{}\"]|\"(?:\\.|[^\"\\])*\")*)\}"
    r"(?P<body>\[[^\]\n]*\]|_[^_\n]+_|`[^`\n]+`)"
)
KEY_RE = re.compile(r'key\s*:=\s*"((?:\\.|[^"\\])*)"')


@dataclass(frozen=True)
class Occurrence:
    kind: str
    opts: str
    body: str
    start: int
    insert_at: int
    implicit_key: str
    explicit_key: str | None
    explicit_key_span: tuple[int, int] | None


def fenced_code_spans(text: str) -> list[tuple[int, int]]:
    spans: list[tuple[int, int]] = []
    in_fence = False
    fence_start = 0
    pos = 0
    for line in text.splitlines(True):
        if line.lstrip().startswith("```"):
            if in_fence:
                spans.append((fence_start, pos + len(line)))
                in_fence = False
            else:
                fence_start = pos
                in_fence = True
        pos += len(line)
    if in_fence:
        spans.append((fence_start, len(text)))
    return spans


def in_spans(spans: list[tuple[int, int]], pos: int) -> bool:
    idx = bisect.bisect_right(spans, (pos, float("inf"))) - 1
    return idx >= 0 and spans[idx][0] <= pos < spans[idx][1]


def body_text(body: str) -> str:
    if body[0] == "[":
        text = body[1:-1]
    elif body[0] == "_":
        text = body[1:-1]
    elif body[0] == "`":
        text = body[1:-1]
    else:
        text = body

    # Approximate VersoManual.Glossary.Norm.techString for the inline syntax
    # forms that occur inside glossary terms.
    text = re.sub(r"\{[^{}\n]*\}`([^`\n]*)`", r"\1", text)
    text = re.sub(r"\{[^{}\n]*\}", "", text)
    text = re.sub(r"`([^`\n]*)`", r"\1", text)
    text = re.sub(r"_([^_\n]*)_", r"\1", text)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def unescape_lean_string(text: str) -> str:
    return re.sub(r'\\([\\"])', r"\1", text)


def lean_string(text: str) -> str:
    return text.replace("\\", "\\\\").replace('"', '\\"')


def occurrences(text: str) -> list[Occurrence]:
    spans = fenced_code_spans(text)
    found: list[Occurrence] = []
    for match in TERM_RE.finditer(text):
        if in_spans(spans, match.start()):
            continue
        opts = match.group("opts")
        explicit = KEY_RE.search(opts)
        explicit_span = None
        if explicit:
            explicit_span = (match.start("opts") + explicit.start(1), match.start("opts") + explicit.end(1))
        found.append(
            Occurrence(
                kind=match.group("kind"),
                opts=opts,
                body=match.group("body"),
                start=match.start(),
                insert_at=match.start("opts"),
                implicit_key=body_text(match.group("body")),
                explicit_key=unescape_lean_string(explicit.group(1)) if explicit else None,
                explicit_key_span=explicit_span,
            )
        )
    return found


def line_col(text: str, pos: int) -> tuple[int, int]:
    line = text.count("\n", 0, pos) + 1
    prev = text.rfind("\n", 0, pos)
    col = pos + 1 if prev < 0 else pos - prev
    return line, col


def aligned_occurrences(
    src_occ: list[Occurrence], zh_occ: list[Occurrence], *, allow_gaps: bool
) -> tuple[list[tuple[Occurrence, Occurrence]], list[tuple[int, Occurrence]], list[tuple[int, Occurrence]]]:
    if len(src_occ) == len(zh_occ) and all(src.kind == zh.kind for src, zh in zip(src_occ, zh_occ)):
        return list(zip(src_occ, zh_occ)), [], []

    if not allow_gaps:
        return [], list(enumerate(src_occ, start=1)), list(enumerate(zh_occ, start=1))

    src_kinds = [occ.kind for occ in src_occ]
    zh_kinds = [occ.kind for occ in zh_occ]
    matcher = difflib.SequenceMatcher(None, src_kinds, zh_kinds, autojunk=False)
    pairs: list[tuple[Occurrence, Occurrence]] = []
    matched_src: set[int] = set()
    matched_zh: set[int] = set()
    for block in matcher.get_matching_blocks():
        for offset in range(block.size):
            src_index = block.a + offset
            zh_index = block.b + offset
            pairs.append((src_occ[src_index], zh_occ[zh_index]))
            matched_src.add(src_index)
            matched_zh.add(zh_index)

    missing_src = [(index + 1, occ) for index, occ in enumerate(src_occ) if index not in matched_src]
    extra_zh = [(index + 1, occ) for index, occ in enumerate(zh_occ) if index not in matched_zh]
    return pairs, missing_src, extra_zh


def sync_file(src_path: Path, zh_path: Path, *, dry_run: bool, allow_gaps: bool) -> tuple[int, list[str]]:
    src_text = src_path.read_text(encoding="utf-8")
    zh_text = zh_path.read_text(encoding="utf-8")
    src_occ = occurrences(src_text)
    zh_occ = occurrences(zh_text)
    diagnostics: list[str] = []

    pairs, missing_src, extra_zh = aligned_occurrences(src_occ, zh_occ, allow_gaps=allow_gaps)
    if not pairs and (missing_src or extra_zh):
        diagnostics.append(f"{zh_path}: occurrence count mismatch: {len(src_occ)} English, {len(zh_occ)} Chinese")
        return 0, diagnostics
    if missing_src or extra_zh:
        diagnostics.append(
            f"{zh_path}: aligned with gaps: {len(missing_src)} unmatched English, {len(extra_zh)} unmatched Chinese"
        )

    edits: list[tuple[int, int, str]] = []
    for index, (src, zh) in enumerate(pairs, start=1):
        if src.kind != zh.kind:
            line, col = line_col(zh_text, zh.start)
            diagnostics.append(
                f"{zh_path}:{line}:{col}: occurrence {index} kind mismatch: {src.kind} vs {zh.kind}"
            )
            return 0, diagnostics

        src_key = src.explicit_key or src.implicit_key
        if zh.explicit_key is not None:
            if zh.explicit_key != src_key and zh.explicit_key_span is not None:
                start, end = zh.explicit_key_span
                edits.append((start, end, lean_string(src_key)))
            continue
        if zh.implicit_key == src_key:
            continue
        edits.append((zh.insert_at, zh.insert_at, f' (key := "{lean_string(src_key)}")'))

    if edits and not dry_run:
        updated = zh_text
        for start, end, replacement in sorted(edits, reverse=True):
            updated = updated[:start] + replacement + updated[end:]
        zh_path.write_text(updated, encoding="utf-8", newline="")

    return len(edits), diagnostics


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--allow-gaps", action="store_true")
    parser.add_argument("--manual", default="Manual")
    parser.add_argument("--manual-zh", default="ManualZh")
    args = parser.parse_args()

    manual = Path(args.manual)
    manual_zh = Path(args.manual_zh)
    total = 0
    changed_files = 0
    diagnostics: list[str] = []

    for zh_path in sorted(manual_zh.rglob("*.lean")):
        src_path = manual / zh_path.relative_to(manual_zh)
        if not src_path.exists():
            continue
        count, file_diagnostics = sync_file(src_path, zh_path, dry_run=args.dry_run, allow_gaps=args.allow_gaps)
        diagnostics.extend(file_diagnostics)
        if count:
            changed_files += 1
            total += count

    for diagnostic in diagnostics:
        print(diagnostic)
    print(f"changed files: {changed_files}")
    print(f"inserted keys: {total}")
    print(f"skipped files: {len(diagnostics)}")
    return 1 if diagnostics else 0


if __name__ == "__main__":
    raise SystemExit(main())
