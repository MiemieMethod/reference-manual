/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "句法" =>
%%%
file := "Syntax"
tag := "string-syntax"
%%%

Lean 具有三种字符串文字：普通字符串文字、插值字符串文字和原始字符串文字。

# 字符串文字
%%%
file := "String-Literals"
tag := "string-literals"
%%%

字符串文字以双引号字符 `"` 开头和结尾。 {index (subterm := "string")}[文字]
在这些字符之间，它们可以包含任何其他字符，包括换行符，这些字符按字面意思包含（需要注意的是，Lean 源文件中的所有换行符都被解释为 `'\n'`，无论文件编码和平台如何）。
无法以其他方式写入字符串文字的特殊字符可以使用反斜杠进行转义，因此 `"\"Quotes\""` 是一个以双引号开头和结尾的字符串文字。
接受以下形式的转义序列：

: `\r`、`\n`、`\t`、`\\`、`\"`、`\'`

  这些转义序列具有通常的含义，分别映射到 `CR`、`LF`、制表符、反斜杠、双引号和单引号。

: `\xNN`

  当 `NN` 是两个十六进制数字的序列时，此转义表示其 Unicode 代码点由两位十六进制代码指示的字符。

: `\uNNNN`

  当 `NN` 是两个十六进制数字的序列时，此转义表示其 Unicode 代码点由四位十六进制代码指示的字符。


字符串文字可能包含 {deftech}[_gaps_]。
间隙由转义换行符表示，转义反斜杠和换行符之间没有中间字符。
在这种情况下，文字表示的字符串缺少换行符和下一行的所有前导空格。
字符串间隙不能位于仅包含空格的行之前。

这里，`str1` 和 `str2` 是相同的字符串：
```lean
def str1 := "String with \
             a gap"
def str2 := "String with a gap"

example : str1 = str2 := rfl
```

如果间隙后面的行为空，则该字符串将被拒绝：

```syntaxError foo
def str3 := "String with \

             a gap"
```
解析器错误是：
```leanOutput foo
<example>:2:0-3:0: unexpected additional newline in string gap
```

# 内插字符串
%%%
file := "Interpolated-Strings"
tag := "string-interpolation"
%%%

在字符串文字前面加上 `s!` 会导致其被处理为 {deftech}[_interpolated string_]，其中由 `{` 和 `}` 字符包围的字符串区域被解析并解释为 Lean 表达式。
通过附加插值之前的字符串、表达式（在其周围添加对 {name ToString.toString}`toString` 的调用）以及插值之后的字符串来解释插值字符串。

例如：
```lean
example :
    s!"1 + 1 = {1 + 1}\n" =
    "1 + 1 = " ++ toString (1 + 1) ++ "\n" :=
  rfl
```

在文字前面加上 `m!` 会导致插值生成 {name Lean.MessageData}`MessageData` 的实例，这是编译器用于向用户显示消息的内部数据结构。

# 原始字符串文字
%%%
file := "Raw-String-Literals"
tag := "raw-string-literals"
%%%

在 {deftech (key := "raw string literals")}[原始字符串文字]、{index (subterm := "raw string")}[文字] 中，没有转义序列或间隙，每个字符都准确地表示自身。
原始字符串文字前面是 `r`，后跟零个或多个哈希字符 (`#`) 和双引号 `"`。
字符串文字由双引号完成，后跟“相同数量”的哈希字符。
例如，它们可用于避免对某些字符进行双重转义：
```lean (name := evalStr)
example : r"\t" = "\\t" := rfl
#eval r"Write backslash in a string using '\\\\'"
```
`#eval` 产生：
```leanOutput evalStr
"Write backslash in a string using '\\\\\\\\'"
```

包含哈希标记允许字符串包含未转义的引号：

```lean
example :
    r#"This is "literally" quoted"# =
    "This is \"literally\" quoted" :=
  rfl
```

添加足够多的散列标记允许按字面意思写入任何原始文字：

```lean
example :
    r##"This is r#"literally"# quoted"## =
    "This is r#\"literally\"# quoted" :=
  rfl
```
