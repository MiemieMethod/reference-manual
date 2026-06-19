/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "为 `grind` 注释库" =>
%%%
tag := "grind-annotation"
%%%

要在库中有效使用 {tactic}`grind`，必须通过将 {attr}`grind` 属性应用于合适的引理或声明 {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern` 来对其进行注释。
这些注释指导 {tactic}`grind` 对定理的选择，从而在隐喻白板上得出更多事实。
如果注释太少，{tactic}`grind` 将无法使用引理；如果太多，它可能会变得很慢或者由于耗尽资源限制而失败。
注释通常应该保守：仅当您期望 {tactic}`grind` 在模式匹配后_始终_实例化定理时才添加注释。

# 简单引理

通常，许多用 {attrs}`@[simp]` 注释的定理也应该用 {attrs}`@[grind =]` 注释。
一个重要的例外是，通常我们避免使用在右侧引入 {keywordOf Lean.Parser.Term.if}`if` 的 {attrs}`@[simp]` 定理，而是更喜欢以正条件和负条件作为假设的一对定理。
由于 {tactic}`grind` 设计用于执行案例分割，因此通常最好用 {attrs}`@[grind =]` 来注释引入 {keywordOf Lean.Parser.Term.if}`if` 的单个定理。

除了使用 {attrs}`@[grind =]` 鼓励 {tactic}`grind` 从左到右执行重写之外，您还可以使用 {attrs}`@[grind _=_]` 来“饱和”，无论何时遇到任何一方都允许双向重写。

# 向后和向前推理

:::paragraph
使用 {attrs}`@[grind ←]`（从定理的结论生成模式）进行向后推理定理，即当结论与目标匹配时应该尝试的定理。
标准库中用 {attr}`grind ←` 注释的定理的一些示例包括：
* ```signature
  Array.not_mem_empty (a : α) : ¬ a ∈ #[]
  ```
* ```signature
  Array.getElem_filter
    {xs : Array α} {p : α → Bool} {i : Nat}
    (h : i < (xs.filter p).size) :
    p (xs.filter p)[i]
  ```
* ```signature
  List.Pairwise.tail
    {l : List α} (h : Pairwise R l) :
    Pairwise R l.tail
  ```
In each case, the lemma is relevant when its conclusion matches a proof goal.
:::

:::paragraph
Use {attrs}`@[grind →]` (which generates patterns from the hypotheses) for forwards reasoning theorems,
i.e. where facts should be propagated from existing facts on the whiteboard.
Some examples of theorems in the standard library that are annotated with {attr}`grind →` are:
* ```signature
  List.getElem_of_getElem? {l : List α} :
    l[i]? = some a →
    ∃ h : i < l.length, l[i] = a
  ```
* ```signature
  Array.mem_of_mem_erase [BEq α] {a b : α} {xs : Array α}
    (h : a ∈ xs.erase b) :
    a ∈ xs
  ```
* ```signature
  List.forall_none_of_filterMap_eq_nil
    (h : filterMap f xs = []) :
    ∀ x ∈ xs, f x = none
  ```
在这些情况下，定理的假设决定它们何时相关。
:::

使用 {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern` 命令创建的自定义模式有很多用途。
一种常见的用途是引入有关术语或成员资格主张的不平等。

:::keepEnv
```lean -show
section
def count := @Array.count
theorem countP_le_size [BEq α] {a : α} {xs : Array α} : count a xs ≤ xs.size := Array.countP_le_size
notation "..." => countP_le_size
```

我们可能有
```lean
variable [BEq α]

theorem count_le_size {a : α} {xs : Array α} : count a xs ≤ xs.size :=
  ...

grind_pattern count_le_size => count a xs
```
```lean -show
variable {a : α} {xs : Array α}
```
一旦遇到 {lean}`count a xs` 项，它就会记录这个不等式（即使问题之前没有涉及不等式）。

```lean -show
end
```
:::

我们还可以使用多种模式来更具限制性，例如如果白板已经包含有关尺寸的事实，则仅引入有关尺寸的不等式：
```lean
theorem size_pos_of_mem {xs : Array α} (h : a ∈ xs) : 0 < xs.size :=
  sorry

grind_pattern size_pos_of_mem => a ∈ xs, xs.size
```
:::leanSection
```lean -show
variable {a : α} {xs : Array α}
```
与 {attrs}`@[grind →]` 属性不同，每当遇到 {lean}`a ∈ xs` 时都会实例化此定理，只有当 {lean}`xs.size` 已位于白板上时才会使用此模式。
（请注意，这种磨削模式也可以使用 {attrs}`@[grind <=]` 属性生成，该属性首先查看结论，然后向后通过假设来选择模式。
另一方面，{attrs}`@[grind →]` 将仅选择 {lean}`a ∈ xs`。）
:::


::::keepEnv
:::leanSection
```lean -show
axiom R : Type
axiom sin : R → R
axiom cos : R → R
@[instance] axiom instAdd : Add R
@[instance] axiom instOfNatR : OfNat R n
@[instance] axiom instHPowR : HPow R Nat R
variable {x : R}
axiom sin_sq_add_cos_sq' : sin x ^ 2 + cos x ^ 2 = 1
notation "..." => sin_sq_add_cos_sq'
```
在 Mathlib 中，我们可能希望启用关于正弦和余弦函数的多项式推理，
添加自定义研磨图案
```lean
theorem sin_sq_add_cos_sq : sin x ^ 2 + cos x ^ 2 = 1 := ...

grind_pattern sin_sq_add_cos_sq => sin x, cos x
```
一旦遇到*两个* {lean}`sin x` 和 {lean}`cos x`（具有相同的 {lean}`x`），它将实例化该定理。
然后，该定理将自动进入 Gröbner 基础模块，并用于推理涉及 {lean}`sin x` 和 {lean}`cos x` 的多项式表达式。
或者，更积极地编写两个单独的研磨模式，以便在遇到 {lean}`sin x` 或 {lean}`cos x` 时实例化该定理。
:::
::::
