/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`invalidDottedIdent`" =>
%%%
file := "About___-___invalidDottedIdent___"
tag := "zh-errorexplanations-invaliddottedident-root"
shortTitle := "invalidDottedIdent"
%%%

{errorExplanationHeader lean.invalidDottedIdent}

此错误表明在无效或不受支持的上下文中使用了点分标识符表示法。
点分标识符表示法允许省略标识符的名称空间，前提是它可以
由 Lean 根据类型信息推断。有关此符号的详细信息可以在手册中找到
section on {ref "identifiers-and-resolution"}[identifiers].

此表示法只能用在类型 Lean 能够推断的术语中。如果有不足的
类型信息 Lean 这样做，将引发此错误。推断的类型不能是类型
Universe（例如 {lean}`Prop` 或 {lean}`Type`），因为不支持点分标识符表示法
这些类型。

# 示例
%%%
file := "Examples"
tag := "zh-errorexplanations-invaliddottedident-h001"
%%%

:::errorExample "Insufficient Type Information"
```broken
def reverseDuplicate (xs : List α) :=
  .reverse (xs ++ xs)
```
```output
Invalid dotted identifier notation: The expected type of `.reverse` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `Array.reverse`
  [apply] `BitVec.reverse`
  [apply] `List.reverse`
  [apply] `Vector.reverse`
  [apply] `List.IsInfix.reverse`
  [apply] `List.IsPrefix.reverse`
  [apply] `List.IsSuffix.reverse`
  [apply] `List.Sublist.reverse`
  [apply] `Lean.Grind.AC.Seq.reverse`
  [apply] `Std.DTreeMap.Internal.Impl.reverse`
  [apply] `Std.Tactic.BVDecide.BVUnOp.reverse`
  [apply] `Std.DTreeMap.Internal.Impl.Ordered.reverse`
```
```fixed
def reverseDuplicate (xs : List α) : List α :=
  .reverse (xs ++ xs)
```

```lean -show
variable (α : Type) (xs : List α)
```

由于未指定 `reverseDuplicate` 的返回类型，因此 `.reverse` 的预期类型
无法确定。 Lean 将不会使用参数 {lean}`xs ++ xs` 的类型来推断
省略命名空间。添加返回类型 {lean}`List α` 允许 Lean 推断 `.reverse` 的类型
以及解析此标识符的适当命名空间 ({name}`List`)。

请注意，这意味着更改 `reverseDuplicate` 的返回类型会更改 `.reverse` 的方式
解析：如果返回类型为 `T`，则 Lean 将（尝试）将 `.reverse` 解析为函数
`T.reverse`，其返回类型为 `T` — 即使 `T.reverse` 不采用类型参数
`List α`。
:::

:::errorExample "Dotted Identifier Where Type Universe Expected"

```broken
example (n : Nat) :=
  match n > 42 with
  | .true  => n - 1
  | .false => n + 1
```
```output
Invalid dotted identifier notation: Not supported on type universe
  Prop
```
```fixed
example (n : Nat) :=
  match decide (n > 42) with
  | .true  => n - 1
  | .false => n + 1
```

```lean -show
variable (n : Nat)
```

命题 {lean}`n > 42` 具有类型 {lean}`Prop`，作为类型 Universe，不支持
点标识符符号。正如这个例子所演示的，尝试在这样的情况下使用这种表示法
上下文几乎总是一个错误。本示例的目的是让 `.true` 和 `.false`
布尔值，而不是命题；但是，{keywordOf Lean.Parser.Term.match}`match` 表达式不
自动对可判定的命题执行这种强制。显式添加 {name}`decide`
使判别式成为 {name}`Bool` 并允许点标识符解析成功。
:::
