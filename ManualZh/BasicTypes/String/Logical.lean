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


#doc (Manual) "逻辑模型" =>
%%%
file := "Logical-Model"
tag := "zh-basictypes-string-logical-root"
%%%

{docstring String}

:::paragraph
Lean 中字符串的逻辑模型是一个包含两个字段的结构体：

 * {name}`String.toByteArray` 是 {name}`ByteArray`，其中包含字符串的 UTF-8 编码。

 * {name}`String.isValidUTF8` 证明字节实际上是字符串的有效 UTF-8 编码。

该模型允许使用字节数组上的操作来指定和证明低级别的字符串操作的属性，同时仍然建立在字节数组理论的基础上。
同时，它足够接近真实的运行时表示，以避免逻辑模型与运行时表示中有意义的操作之间的阻抗不匹配。
:::

# 向后兼容性
%%%
file := "Backwards-Compatibility"
tag := "zh-basictypes-string-logical-h001"
%%%

在 Lean 的早期版本中，字符串的逻辑模型是包含字符列表的结构。
这个模型还是很有用的。
仍然可以使用 {name}`String.ofList`（将字符列表转换为 {name}`String`）和 {name}`String.toList`（将 {name}`String` 转换为字符列表）来访问它。

{docstring String.ofList}

{docstring String.toList}
