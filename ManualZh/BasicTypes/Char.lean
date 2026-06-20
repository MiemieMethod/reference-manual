/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.BasicTypes.Array.Subarray
import ManualZh.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "人物" =>
%%%
tag := "Char"
%%%

字符由类型 {name}`Char` 表示，它可以是任何 Unicode [标量值](http://www.unicode.org/glossary/#unicode_scalar_value)。
虽然 {ref "String"}[strings] 是 UTF-8 编码的字节数组，但字符由完整的 32 位值表示。
Lean 为字符文字提供特殊的 {ref "char-syntax"}[语法]。

# 逻辑模型
%%%
tag := "char-model"
%%%

从 Lean 逻辑的角度来看，字符由一个 32 位无符号整数和一个证明它是有效 Unicode 标量值的证明组成。

{docstring Char}

# 运行时表示
%%%
tag := "char-runtime"
%%%

作为 {ref "inductive-types-trivial-wrappers"}[普通包装器]，字符的表示方式与 {lean}`UInt32` 相同。
特别是，字符在单态上下文中表示为 32 位立即值。
换句话说，{lean}`Char` 类型的构造函数或结构体的字段不需要间接访问。
在多态上下文中，字符为 {tech}[boxed]。


# 句法
%%%
tag := "char-syntax"
%%%

字符文字由单个字符或用单引号括起来的转义序列组成（`'`、Unicode `'APOSTROPHE' (U+0027)`）。
在这些单引号之间，字符文字可能包含 `'` 以外的字符，包括换行符，这些换行符按字面意思包含（需要注意的是，Lean 源文件中的所有换行符都被解释为 `'\n'`，无论文件编码和平台如何）。
特殊字符可以使用反斜杠转义，因此 `'\''` 是包含单引号的字符文字。
接受以下形式的转义序列：

: `\r`、`\n`、`\t`、`\\`、`\"`、`\'`

  这些转义序列具有通常的含义，分别映射到 `CR`、`LF`、制表符、反斜杠、双引号和单引号。

: `\xNN`

  当 `NN` 是两个十六进制数字的序列时，此转义表示其 Unicode 代码点由两位十六进制代码指示的字符。

: `\uNNNN`

  当 `NN` 是两个十六进制数字的序列时，此转义表示其 Unicode 代码点由四位十六进制代码指示的字符。


# API 参考
%%%
tag := "char-api"
%%%

## 转换
%%%
tag := "zh-basictypes-char-h005"
%%%

{docstring Char.ofNat}

{docstring Char.toNat}

{docstring Char.isValidCharNat}

{docstring Char.ofUInt8}

{docstring Char.toUInt8}


将字符转换为字符串有两种方法。
{name}`Char.toString` 将字符转换为仅包含该字符的单例字符串，而 {name}`Char.quote` 将字符转换为相应字符文字的字符串表示形式。

{docstring Char.toString}

{docstring Char.quote}

:::example "From Characters to Strings"

{name}`Char.toString` 生成一个仅包含相关字符的字符串：

```lean (name := e)
#eval 'e'.toString
```
```leanOutput e
"e"
```

```lean (name := e')
#eval '\x65'.toString
```
```leanOutput e'
"e"
```

```lean (name := n')
#eval '"'.toString
```
```leanOutput n'
"\""
```

{name}`Char.quote` 生成一个包含经过适当转义的字符文字的字符串：
```lean (name := eq)
#eval 'e'.quote
```
```leanOutput eq
"'e'"
```

```lean (name := eq')
#eval '\x65'.quote
```
```leanOutput eq'
"'e'"
```

```lean (name := nq')
#eval '"'.quote
```
```leanOutput nq'
"'\\\"'"
```


:::




## 字符类
%%%
tag := "char-api-classes"
%%%

{docstring Char.isAlpha}

{docstring Char.isAlphanum}

{docstring Char.isDigit}

{docstring Char.isLower}

{docstring Char.isUpper}

{docstring Char.isWhitespace}

## 大小写转换
%%%
tag := "zh-basictypes-char-h007"
%%%

{docstring Char.toUpper}

{docstring Char.toLower}

## 比较
%%%
tag := "zh-basictypes-char-h008"
%%%

{docstring Char.le}

{docstring Char.lt}

## Unicode
%%%
tag := "zh-basictypes-char-h009"
%%%

{docstring Char.utf8Size}

{docstring Char.utf16Size}
