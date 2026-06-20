/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "身份" =>
%%%
tag := "zh-monads-zoo-id-root"
%%%

身份单子 {name}`Id` 没有任何效果。
{name}`Id`和{name}`pure`的相应实现都是恒等函数，{name}`bind`是逆函数应用。
身份单子有两个主要用例：
 1. 它可以是实现具有局部效果的纯函数的 {keywordOf Lean.Parser.Term.do}`do` 块的类型。
 2. 它可以放置在一堆 monad 变压器的底部。

```lean -show
-- Verify claims
example : Id = id := rfl
example : Id.run (α := α) = id := rfl
example : (pure (f := Id)) = (id : α → α) := rfl
example : (bind (m := Id)) = (fun (x : α) (f : α → Id β) => f x) := rfl
```

{docstring Id}

{docstring Id.run}

:::example "Local Effects with the Identity Monad"
此代码块通过使用身份单子中的模拟本地可变性来实现倒计时过程。
```lean (name := idDo)
#eval Id.run do
  let mut xs := []
  for x in [0:10] do
    xs := x :: xs
  pure xs
```
```leanOutput idDo
[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
```
:::
