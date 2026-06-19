#!/usr/bin/env python3
"""
Translate the Verso source of the Lean reference manual to Chinese.

The script is conservative: it skips Lean code, fenced code blocks, metadata
blocks, imports, and structural Verso directives. Inline markup and Lean
identifiers are protected with placeholders before text is sent to the
translation backend, then restored afterwards.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Callable


LINE_SEP = "XQZLINESEP00000XQ"
CACHE_VERSION = 2

PROTECT_WORDS = [
    "Lean",
    "Lake",
    "Verso",
    "SubVerso",
    "Mathlib",
    "Reservoir",
    "GitHub",
    "GMP",
    "SMT",
    "TOML",
    "JSON",
    "YAML",
    "XML",
    "HTML",
    "CSS",
    "JavaScript",
    "Lua",
    "Python",
    "Rust",
    "Type",
    "Prop",
    "Sort",
    "IO",
    "FFI",
    "API",
    "ABI",
    "CLI",
    "REPL",
    "LSP",
    "ASCII",
    "Unicode",
    "UTF-8",
    "Windows",
    "Linux",
    "macOS",
]

GLOSSARY_PHRASES = {
    "dependent type theory": "依值类型论",
    "interactive theorem prover": "交互式定理证明器",
    "theorem prover": "定理证明器",
    "proof assistant": "证明助理",
    "definitional equality": "定义等价",
    "propositional equality": "命题等价",
    "inductive type": "归纳类型",
    "inductive types": "归纳类型",
    "dependent type": "依值类型",
    "dependent types": "依值类型",
    "type theory": "类型论",
    "universe level": "宇宙层级",
    "universe levels": "宇宙层级",
    "natural number": "自然数",
    "natural numbers": "自然数",
    "fixed-width integer": "固定位宽整数",
    "fixed-width integers": "固定位宽整数",
    "reference counting": "引用计数",
    "standard output": "标准输出",
    "standard error": "标准错误",
    "standard input": "标准输入",
    "well-founded recursion": "良基递归",
    "structural recursion": "结构递归",
    "pattern matching": "模式匹配",
    "syntax extension": "语法扩展",
    "macro expansion": "宏展开",
    "elaboration": "精化",
    "elaborator": "精化器",
    "kernel": "内核",
    "tactic": "策略",
    "tactics": "策略",
}

POST_REPLACEMENTS = [
    ("精益", "Lean"),
    ("湖泊", "Lake"),
    ("定理证明者", "定理证明器"),
    ("依赖类型理论", "依值类型论"),
    ("依赖类型", "依值类型"),
    ("命题平等", "命题等价"),
    ("命题相等", "命题等价"),
    ("定义平等", "定义等价"),
    ("定义相等", "定义等价"),
    ("普遍量化", "全称量化"),
    ("通用量化", "全称量化"),
    ("基本案例", "基例"),
    ("基本情况", "基例"),
    ("链接列表", "链表"),
    ("原始递归", "原始递归"),
    ("任意精度整数", "任意精度整数"),
    ("自然数 ", "自然数"),
    (" 内核", "内核"),
    ("阐述者", "精化器"),
    ("阐述", "精化"),
]

COMPACT_TERMS = [
    "自然数",
    "内核",
    "归纳类型",
    "策略",
    "精化器",
    "精化",
    "引用计数",
    "良基递归",
    "结构递归",
    "模式匹配",
    "语法扩展",
    "宏展开",
]


def has_cjk(text: str) -> bool:
    return any("\u4e00" <= ch <= "\u9fff" for ch in text)


def polish(text: str) -> str:
    for term in COMPACT_TERMS:
        text = text.replace(term + " ", term)
        text = text.replace(" " + term, term)
    text = re.sub(r"([\u4e00-\u9fff])\s+([，。；：！？、）])", r"\1\2", text)
    text = re.sub(r"([（])\s+([\u4e00-\u9fff])", r"\1\2", text)
    return text


def make_protector() -> tuple[Callable[[str], str], Callable[[str], str]]:
    placeholders: list[str] = []

    def add(value: str) -> str:
        token = f"XQZPH{len(placeholders):05d}XQ"
        placeholders.append(value)
        return token

    def protect(text: str) -> str:
        patterns = [
            r"\{[^{}\n]*\}`[^`\n]*`",
            r"\$`[^`\n]*`",
            r"`[^`\n]*`",
            r"\$[^$\n]+\$",
            r"https?://[^\s)\]]+",
            r"</?[^>\n]+>",
            r"&[A-Za-z][A-Za-z0-9]+;",
            r"\{[^{}\n]*\}",
        ]
        for pattern in patterns:
            text = re.sub(pattern, lambda match: add(match.group(0)), text)

        for phrase, zh in sorted(GLOSSARY_PHRASES.items(), key=lambda item: -len(item[0])):
            text = re.sub(rf"\b{re.escape(phrase)}\b", lambda _m, zh=zh: add(zh), text, flags=re.I)

        word_pattern = r"\b(?:" + "|".join(re.escape(word) for word in PROTECT_WORDS) + r")\b"
        text = re.sub(word_pattern, lambda match: add(match.group(0)), text)
        return text

    def restore(text: str) -> str:
        for _ in range(3):
            prior = text
            for index in range(len(placeholders) - 1, -1, -1):
                full = f"XQZPH{index:05d}XQ"
                split = f"XQZPH{index:05d}"
                text = text.replace(full, placeholders[index])
                text = text.replace(split, placeholders[index])
                text = re.sub(rf"XQZPH0*{index}(?:XQ)?", lambda _match, value=placeholders[index]: value, text)
            text = text.replace(" XQ", "")
            if text == prior:
                break
        for old, new in POST_REPLACEMENTS:
            text = text.replace(old, new)
        return polish(text)

    return protect, restore


def load_cache(path: Path) -> dict[str, str]:
    if not path.exists():
        return {}
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("version") != CACHE_VERSION:
        return {}
    return dict(data.get("translations", {}))


def save_cache(path: Path, cache: dict[str, str]) -> None:
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(
        json.dumps({"version": CACHE_VERSION, "translations": cache}, ensure_ascii=False, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    tmp.replace(path)


def google_translate_raw(items: list[str], pause: float, retries: int) -> list[str]:
    joined = f"\n{LINE_SEP}\n".join(items)
    query = urllib.parse.urlencode(
        {
            "client": "gtx",
            "sl": "en",
            "tl": "zh-CN",
            "dt": "t",
            "q": joined,
        }
    )
    url = "https://translate.googleapis.com/translate_a/single?" + query
    for attempt in range(retries + 1):
        try:
            with urllib.request.urlopen(url, timeout=90) as response:
                payload = json.loads(response.read().decode("utf-8"))
            translated = "".join(part[0] for part in payload[0] if part and part[0])
            pieces = [piece.strip() for piece in translated.split(LINE_SEP)]
            if len(pieces) != len(items):
                if len(items) == 1:
                    pieces = [translated.strip()]
                else:
                    raise RuntimeError(f"translation split mismatch: expected {len(items)}, got {len(pieces)}")
            if pause:
                time.sleep(pause)
            return pieces
        except Exception:
            if attempt == retries:
                raise
            time.sleep(2.0 * (attempt + 1))
    raise RuntimeError("unreachable translation retry state")


def translate_batch(items: list[str], cache: dict[str, str], pause: float, retries: int) -> list[str]:
    missing = [item for item in items if item not in cache]
    if missing:
        protect, restore = make_protector()
        protected = [protect(item) for item in missing]
        translated = google_translate_raw(protected, pause=pause, retries=retries)
        for source, target in zip(missing, translated, strict=True):
            cache[source] = restore(target)
    return [cache[item] for item in items]


def should_copy_line(stripped: str, before_doc: bool) -> bool:
    if before_doc or not stripped:
        return True
    if stripped.startswith(("{include", "{docstring", "{spliceContents", "{TODO}", "{TODO")):
        return True
    if stripped.startswith(":::") and '"' not in stripped:
        return True
    if stripped.startswith("%%%") or stripped in {":::", "::::", ":::::", "::::::"}:
        return True
    lean_starts = (
        "import ",
        "open ",
        "set_option ",
        "variable ",
        "namespace ",
        "section",
        "end",
        "#eval",
        "#check",
        "#guard",
        "#print",
        "def ",
        "theorem ",
        "example ",
        "inductive ",
        "structure ",
        "class ",
        "instance ",
        "abbrev ",
        "syntax ",
        "macro",
        "elab ",
        "attribute ",
        "@[",
    )
    return stripped.startswith(lean_starts)


def split_prefix(line: str) -> tuple[str, str]:
    match = re.match(r"^(\s*(?:[*+-]|\d+\.)\s+)(.*)$", line)
    if match:
        return match.group(1), match.group(2)
    match = re.match(r"^(\s*:\s+)(.*)$", line)
    if match:
        return match.group(1), match.group(2)
    match = re.match(r"^(\s*#+\s+)(.*)$", line)
    if match:
        return match.group(1), match.group(2)
    return "", line


def replace_quoted_title(line: str, translate_one: Callable[[str], str]) -> str | None:
    doc = re.match(r'^(\s*#doc\s+\(Manual\)\s+")([^"]+)(".*)$', line)
    if doc:
        return doc.group(1) + translate_one(doc.group(2)) + doc.group(3)

    directive = re.match(r'^(\s*:{3,}\s*(?:example|leanSection|paragraph|syntax|tomlFieldCategory)\b[^"]*")([^"]+)(".*)$', line)
    if directive:
        return directive.group(1) + translate_one(directive.group(2)) + directive.group(3)

    return None


def translate_file(path: Path, cache: dict[str, str], batch_size: int, pause: float, retries: int, force: bool) -> bool:
    original = path.read_text(encoding="utf-8")
    lines = original.splitlines(keepends=True)
    output: list[str] = []
    pending: list[tuple[int, str, str, str]] = []
    before_doc = True
    fence_mode: str | None = None
    in_metadata = False
    changed = False

    def flush() -> None:
        nonlocal changed
        if not pending:
            return
        texts = [text for _index, _prefix, text, _newline in pending]
        translated = translate_batch(texts, cache, pause=pause, retries=retries)
        for (index, prefix, _text, newline), target in zip(pending, translated, strict=True):
            rendered = prefix + target + newline
            output[index] = rendered
            if rendered != lines[index]:
                changed = True
        pending.clear()

    def translate_one(text: str) -> str:
        return translate_batch([text], cache, pause=pause, retries=retries)[0]

    for raw_index, raw in enumerate(lines):
        newline = "\n" if raw.endswith("\n") else ""
        line = raw[:-1] if newline else raw
        stripped = line.strip()

        if stripped.startswith("#doc (Manual)"):
            before_doc = False

        if stripped.startswith("```"):
            flush()
            if fence_mode is None:
                info = stripped[3:].strip().split()
                fence_mode = "markdown" if info and info[0] == "markdown" else "code"
            else:
                fence_mode = None
            output.append(raw)
            continue

        if stripped == "%%%":
            flush()
            in_metadata = not in_metadata
            output.append(raw)
            continue

        if fence_mode == "code" or in_metadata:
            output.append(raw)
            continue

        quoted = replace_quoted_title(line, translate_one)
        if quoted is not None:
            flush()
            rendered = quoted + newline
            output.append(rendered)
            if rendered != raw:
                changed = True
            continue

        if should_copy_line(stripped, before_doc):
            flush()
            output.append(raw)
            continue

        prefix, body = split_prefix(line)
        if not body.strip() or (has_cjk(body) and not force):
            flush()
            output.append(raw)
            continue

        output.append(raw)
        pending.append((len(output) - 1, prefix, body, newline))
        if len(pending) >= batch_size:
            flush()

    flush()
    rendered_file = "".join(output)
    if rendered_file != original:
        path.write_text(rendered_file, encoding="utf-8", newline="")
        changed = True
    return changed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="ManualZh", help="directory containing translated Lean modules")
    parser.add_argument("--cache", default="translation-cache-zh.json")
    parser.add_argument("--file", action="append", default=[], help="relative file under --root to translate")
    parser.add_argument("--limit", type=int, default=0, help="maximum number of files to process")
    parser.add_argument("--batch-size", type=int, default=32)
    parser.add_argument("--pause", type=float, default=0.15)
    parser.add_argument("--retries", type=int, default=3)
    parser.add_argument("--force", action="store_true", help="translate lines even if they already contain CJK")
    args = parser.parse_args()

    root = Path(args.root)
    cache_path = Path(args.cache)
    cache = load_cache(cache_path)

    if args.file:
        files = [root / item for item in args.file]
    else:
        files = sorted(root.rglob("*.lean"))

    if args.limit:
        files = files[: args.limit]

    changed = 0
    for number, path in enumerate(files, start=1):
        if not path.exists():
            raise FileNotFoundError(path)
        if translate_file(path, cache, batch_size=args.batch_size, pause=args.pause, retries=args.retries, force=args.force):
            changed += 1
        save_cache(cache_path, cache)
        print(f"[{number}/{len(files)}] {path} ({changed} changed)")

    save_cache(cache_path, cache)
    print(f"Translated {len(files)} file(s); changed {changed}. Cache entries: {len(cache)}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
