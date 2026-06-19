/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta

/-!
This is extracted into its own file because line numbers show up in the error message, and we don't
want to update it over and over again as we edit the large file.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

#doc (Manual) "良基递归预处理示例（包含在其他地方）" =>

::::example "Preprocessing for a custom data type"

此示例演示了为自定义容器类型启用自动良基递归所需的条件。
结构类型 {name}`Pair` 是同构对：它恰好包含两个元素，这两个元素都具有相同的类型。
它可以被认为类似于始终包含两个元素的列表或数组。

作为容器，{name}`Pair` 可以支持 {name Pair.map}`map` 操作。
为了支持良基递归（其中递归调用发生在映射到 {name}`Pair` 的函数体内），需要一些附加定义，包括成员资格谓词、将成员大小与包含对的大小相关联的定理、引入和消除有关成员资格的假设的帮助程序、插入这些帮助程序的 {attr}`wf_preprocess` 规则以及对{tactic}`decreasing_trivial`策略。
这些步骤中的每一个都使得使用 {name}`Pair` 变得更加容易，但没有一个步骤是绝对必要的；无需立即实施每种类型的所有步骤。

```lean
/-- A homogeneous pair -/
structure Pair (α : Type u) where
  fst : α
  snd : α

/-- Mapping a function over the elements of a pair -/
def Pair.map (f : α → β) (p : Pair α) : Pair β where
  fst := f p.fst
  snd := f p.snd
```

定义使用 {name}`Pair` 的二叉树的嵌套归纳数据类型并尝试定义其 {name Tree.map}`map` 函数表明需要预处理规则。

```lean
/-- A binary tree defined using `Pair` -/
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | node : Pair (Tree α) → Tree α
```

{name Tree.map}`map` 函数的简单定义失败：

```lean +error -keep (name := badwf)
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
```

```leanOutput badwf (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
p : Pair (Tree α)
t' : Tree α
⊢ sizeOf t' < 1 + sizeOf p
```

:::paragraph
```lean -show
section
variable (t' : Tree α) (p : Pair (Tree α))
```
显然，证明义务是不可解决的，因为没有任何东西将 {lean}`t'` 与 {lean}`p` 连接起来。
```lean -show
end
```
:::

实现这种函数定义的标准习惯用法是拥有一个函数，通过证明它们实际上是集合的元素来丰富集合的每个元素。
陈述这个属性需要一个成员谓词。

```lean
inductive Pair.Mem (p : Pair α) : α → Prop where
  | fst : Mem p p.fst
  | snd : Mem p p.snd

instance : Membership α (Pair α) where
  mem := Pair.Mem
```

每个归纳类型自动具有一个 {name}`SizeOf` 实例。
集合的元素应该小于集合，但必须先证明这一事实，然后才能使用它来构造终止证明：

```lean
theorem Pair.sizeOf_lt_of_mem {α} [SizeOf α]
    {p : Pair α} {x : α} (h : x ∈ p) :
    sizeOf x < sizeOf p := by
  cases h <;> cases p <;> (simp; omega)
```

下一步是定义 {name Pair.attach}`attach` 和 {name Pair.unattach}`unattach` 函数，通过证明它们是该对的元素来丰富该对的元素，或者删除所述证明。
这里，{name}`Pair.unattach` 的类型更加通用，可以与任何 {ref "Subtype"}[subtype] 一起使用；这是一个典型的模式。

```lean
def Pair.attach (p : Pair α) : Pair {x : α // x ∈ p} where
  fst := ⟨p.fst, .fst⟩
  snd := ⟨p.snd, .snd⟩

def Pair.unattach {P : α → Prop} :
    Pair {x : α // P x} → Pair α :=
  Pair.map Subtype.val
```

现在可以通过使用 {name}`Pair.attach` 和 {name}`Pair.sizeOf_lt_of_mem` 显式定义 {name Tree.map}`Tree.map`：

```lean -keep
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.attach.map (fun ⟨t', _⟩ => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all +arith
  omega
```

这种转变可以完全自动化。
良基递归的预处理功能可用于自动引入 {lean}`Pair.attach` 函数。
这是分两个阶段完成的。
首先，当 {name}`Pair.map` 应用于函数参数之一时，它将被重写为 {name Pair.attach}`attach`/{name Pair.unattach}`unattach` 组合。
然后，当函数映射到 {name}`Pair.unattach` 的结果时，函数将被重写以接受成员资格证明并将其纳入范围。
```lean
@[wf_preprocess]
theorem Pair.map_wfParam (f : α → β) (p : Pair α) :
    (wfParam p).map f = p.attach.unattach.map f := by
  cases p
  simp [wfParam, Pair.attach, Pair.unattach, Pair.map]

@[wf_preprocess]
theorem Pair.map_unattach {P : α → Prop}
    (p : Pair (Subtype P)) (f : α → β) :
    p.unattach.map f =
    p.map fun ⟨x, h⟩ =>
      binderNameHint x f <|
      f (wfParam x) := by
  cases p; simp [wfParam, Pair.unattach, Pair.map]
```

现在可以在无需额外考虑的情况下编写函数体，并且成员资格假设仍然可用于终止证明。

```lean -keep
def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
decreasing_by
  have := Pair.sizeOf_lt_of_mem ‹_›
  simp_all
  omega
```

通过将 {name Pair.sizeOf_lt_of_mem}`sizeOf_lt_of_mem` 添加到 {tactic}`decreasing_trivial`策略可以全自动进行证明，就像对类似的内置定理所做的那样。

```lean
macro "sizeOf_pair_dec" : tactic =>
  `(tactic| with_reducible
    have := Pair.sizeOf_lt_of_mem ‹_›
    omega
    done)

macro_rules
  | `(tactic| decreasing_trivial) =>
    `(tactic| sizeOf_pair_dec)

def Tree.map (f : α → β) : Tree α → Tree β
  | leaf x => leaf (f x)
  | node p => node (p.map (fun t' => t'.map f))
termination_by t => t
```

为了使示例简短，{tactic}`sizeOf_pair_dec`策略是针对这种特定的递归模式量身定制的，对于通用容器库来说还不够通用。
然而，它确实证明了库在实践中可以像标准库中的容器类型一样方便。

::::
