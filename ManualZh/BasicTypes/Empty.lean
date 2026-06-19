/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "空的Type" =>
%%%
tag := "empty"
%%%

空类型 {name}`Empty` 表示不可能的值。
它是一个没有任何构造函数的归纳类型。

虽然普通类型 {name}`Unit`（具有不带参数的单个构造函数）可用于对结果不想要或无趣的计算进行建模，但 {name}`Empty` 可用于根本不可能进行计算的情况。
使用 {name}`Empty` 实例化多态类型可以将其某些构造函数（具有相应类型的参数的构造函数）标记为不可能； this can rule out certain code paths that are not desired.

类型为 {name}`Empty` 的术语的存在表示已到达不可能的代码路径。
由于缺乏构造函数，这种类型永远不会有值。
在不可能的代码路径上，没有理由编写更多代码；函数 {name}`Empty.elim` 可用于逃离不可能的路径。

{name}`Empty` 的宇宙多态等价物是 {name}`PEmpty`。

{docstring Empty}

{docstring PEmpty}


:::example "Impossible Code Paths"

函数 {lean}`f` 的类型签名表明它可能会抛出异常，但允许异常类型为任何类型：
```lean
def f (n : Nat) : Except ε Nat := pure n
```

使用 {lean}`Empty` 实例化 {lean}`f` 的异常类型利用了 {lean}`f` 实际上从未抛出异常的事实，将其转换为类型指示不会抛出异常的函数。
特别是，它允许使用 {lean}`Empty.elim` 来避免处理不可能的异常值。

```lean
def g (n : Nat) : Nat :=
  match f (ε := Empty) n with
  | .error e =>
    Empty.elim e
  | .ok v => v
```
:::

# API 参考

{docstring Empty.elim}

{docstring PEmpty.elim}
