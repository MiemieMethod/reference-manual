/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`dependsOnNoncomputable`" =>
%%%
shortTitle := "dependsOnNoncomputable"
%%%

{errorExplanationHeader lean.dependsOnNoncomputable}

此错误表明指定的定义依赖于一个或多个不依赖于该定义的定义。
包含可执行代码，因此需要标记为 {keyword}`noncomputable`。这样的
定义可以进行类型检查，但不包含可由 Lean 执行的代码。

如果您希望错误消息中指定的定义不可计算，请将其标记为
{keyword}`noncomputable` 将解决此错误。如果没有，请检查不可计算的
它所依赖的定义：它们可能是不可计算的，因为它们无法编译，是
{keyword}`axiom`，或本身标记为 {keyword}`noncomputable`。让你的一切
定义的不可计算依赖项可计算也将解决此错误。参见手册
section on {ref "declaration-modifiers"}[Modifiers] for more information about noncomputable
定义。

# 示例

:::errorExample "Necessarily Noncomputable Function Not Appropriately Marked"
```broken
axiom transform : Nat → Nat

def transformIfZero : Nat → Nat
  | 0 => transform 0
  | n => n
```
```output
`transform` not supported by code generator; consider marking definition as `noncomputable`
```
```fixed
axiom transform : Nat → Nat

noncomputable def transformIfZero : Nat → Nat
  | 0 => transform 0
  | n => n
```
在此示例中，`transformIfZero` 取决于公理 `transform`。因为 `transform` 是
axiom，它不包含任何可执行代码；尽管值 `transform 0` 的类型为 `Nat`，
没有办法计算它的价值。因此，`transformIfZero` 必须标记为 `noncomputable`，因为
它的执行将取决于这个公理。
:::

:::errorExample "Noncomputable Dependency Can Be Made Computable"
```broken
noncomputable def getOrDefault [Nonempty α] : Option α → α
  | some x => x
  | none => Classical.ofNonempty

def endsOrDefault (ns : List Nat) : Nat × Nat :=
  let head := getOrDefault ns.head?
  let tail := getOrDefault ns.getLast?
  (head, tail)
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'getOrDefault', which is 'noncomputable'
```
```fixed
def getOrDefault [Inhabited α] : Option α → α
  | some x => x
  | none => default

def endsOrDefault (ns : List Nat) : Nat × Nat :=
  let head := getOrDefault ns.head?
  let tail := getOrDefault ns.getLast?
  (head, tail)
```
由于使用了 `Classical.choice`，`getOrDefault` 的原始定义是不可计算的。
然而，与前面的示例不同的是，可以实现类似但可计算的
`getOrDefault` 的版本（使用 `Inhabited` 类型类），允许 `endsOrDefault`
可计算。 （`Inhabited` 和 `Nonempty` 之间的差异在文档中有描述
{ref "basic-classes"}[基本类]手册部分中的居住类型。）
:::

:::errorExample "Noncomputable Instance in Namespace"
```broken
open Classical in
/--
Returns `y` if it is in the image of `f`,
or an element of the image of `f` otherwise.
-/
def fromImage (f : Nat → Nat) (y : Nat) :=
  if ∃ x, f x = y then
    y
  else
    f 0
```
```output
failed to compile definition, consider marking it as 'noncomputable' because it depends on 'propDecidable', which is 'noncomputable'
```
```fixed
open Classical in
/--
Returns `y` if it is in the image of `f`,
or an element of the image of `f` otherwise.
-/
noncomputable def fromImage (f : Nat → Nat) (y : Nat) :=
  if ∃ x, f x = y then
    y
  else
    f 0
```
`Classical` 命名空间包含不可计算的 `Decidable` 实例。这些都是常见的
未明确出现在源代码中的不可计算依赖项的来源
定义。例如，在上面的示例中，命题的 `Decidable` 实例
`∃ x, f x = y` 是使用 `Classical` 可判定性实例合成的；因此，`fromImage` 必须
标记为 `noncomputable`。
:::
