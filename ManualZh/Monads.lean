/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import ManualZh.Monads.Syntax
import ManualZh.Monads.Zoo
import ManualZh.Monads.Lift
import ManualZh.Monads.API
import ManualZh.Monads.Laws

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
set_option maxRecDepth 1024

#doc (Manual) "函子、Monad 和 `do` 表示法" =>

%%%
file := "Functors___-Monads-and-___do___-Notation"
tag := "monads-and-do"
%%%

类型类 {name}`Functor`、{name}`Applicative` 和 {name}`Monad` 提供了函数式编程的基本工具。{margin}[[_Lean函数式编程_](https://lean-lang.org/functional_programming_in_lean/functor-applicative-monad.html) 中提供了使用这些抽象进行编程的介绍。]
虽然它们受到范畴论中函子和单子概念的启发，但用于编程的版本更加有限。
Lean 标准库中的类型类表示用于编程的概念，而不是一般的数学定义。

{deftech}[{name}`Functor`] 的实例允许在整个多态上下文中一致地应用操作。
示例包括通过应用函数来转换列表的每个元素，以及通过安排将纯函数应用于现有 {lean}`IO` 操作的结果来创建新的 {lean}`IO` 操作。
{deftech}[{name}`Monad`]的实例允许对具有数据依赖性的副作用进行编码；示例包括使用元组来模拟可变状态、使用求和类型来模拟异常以及使用 {lean}`IO` 表示实际副作用。
{deftech (key := "Applicative functors")}[{name}`Applicative` 函子] 占据中间立场：与 monad 一样，它们允许将使用效果计算的函数应用于使用效果计算的参数，但它们不允许顺序数据依赖关系，其中效果的输出形成另一个有效操作的输入。

附加类型类 {name}`Pure`、{name}`Bind`、{name}`SeqLeft`、{name}`SeqRight` 和 {name}`Seq` 捕获来自 {name}`Applicative` 和 {name}`Monad` 的各个操作，允许它们重载并与不一定是 {name}`Applicative` 的类型一起使用函子或 {name}`Monad`。
{name}`Alternative` 类型类描述了另外具有一些失败和恢复概念的应用函子。


{docstring Functor}

{docstring Pure}

{docstring Seq}

{docstring SeqLeft}

{docstring SeqRight}

{docstring Applicative}


:::::keepEnv

```lean -show
section
variable {α : Type u} {β : Type u}
```

::::example "Lists with Lengths as Applicative Functors"

结构 {name}`LenList` 将列表与具有所需长度的证明配对。
因此，如果输入长度不同，其 `zipWith` 运算符不需要回退。

```lean
structure LenList (length : Nat) (α : Type u) where
  list : List α
  lengthOk : list.length = length

def LenList.head (xs : LenList (n + 1) α) : α :=
  xs.list.head <| by
    intro h
    cases xs
    simp_all
    subst_eqs

def LenList.tail (xs : LenList (n + 1) α) : LenList n α :=
  match xs with
  | ⟨_ :: xs', _⟩ => ⟨xs', by simp_all⟩

def LenList.map (f : α → β) (xs : LenList n α) : LenList n β where
  list := xs.list.map f
  lengthOk := by
    cases xs
    simp [List.length_map, *]

def LenList.zipWith (f : α → β → γ)
    (xs : LenList n α) (ys : LenList n β) :
    LenList n γ where
  list := xs.list.zipWith f ys.list
  lengthOk := by
    cases xs; cases ys
    simp [List.length_zipWith, *]
```

行为良好的 {name}`Applicative` 实例将函数按元素应用于参数。
由于 {name}`Applicative` 扩展了 {name}`Functor`，因此不需要单独的 {name}`Functor` 实例，并且 {name Functor.map}`map` 可以定义为 {name}`Applicative` 实例的一部分。

```lean
instance : Applicative (LenList n) where
  map := LenList.map
  pure x := {
    list := List.replicate n x
    lengthOk := List.length_replicate
  }
  seq {α β} fs xs := fs.zipWith (· ·) (xs ())
```

表现良好的 {name}`Monad` 实例采用应用函数结果的对角线：

```lean
@[simp]
theorem LenList.list_length_eq (xs : LenList n α) :
    xs.list.length = n := by
  cases xs
  simp [*]

def LenList.diagonal (square : LenList n (LenList n α)) : LenList n α :=
  match n with
  | 0 => ⟨[], rfl⟩
  | n' + 1 => {
    list :=
      square.head.head :: (square.tail.map (·.tail)).diagonal.list
    lengthOk := by simp
  }
```
::::

```lean -show
end
```
:::::


{docstring Alternative}

{docstring Bind}

{docstring Monad}

{include 0 ManualZh.Monads.Laws}

{include 0 ManualZh.Monads.Lift}

{include 0 ManualZh.Monads.Syntax}

{include 0 ManualZh.Monads.API}

{include 0 ManualZh.Monads.Zoo}
