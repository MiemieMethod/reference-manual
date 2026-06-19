/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Meta.Monotonicity

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order


#doc (Manual) "理论与构建" =>
%%%
tag := "partial-fixpoint-theory"
%%%

该构造建立在克纳斯特-塔斯基定理的变体之上：在链完备偏序中，每个单调函数都有一个最小不动点。

必要的理论可以在 `Lean.Order` 命名空间中找到。
这并不是一个通用的阶次理论结果库。
相反，`Lean.Order` 中的定义和定理仅用作 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 功能的实现细节，并且它们应被视为私有 API，可能会更改，恕不另行通知。

偏序的概念和链完全偏序的概念分别由类型类 {name}`Lean.Order.PartialOrder` 和 {name}`Lean.Order.CCPO` 表示。

{docstring Lean.Order.PartialOrder +allowMissing}

{docstring Lean.Order.CCPO +allowMissing}

```lean -show
section
open Lean.Order
variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β] (f : α → β) (x y : α)
```

如果函数保留偏序，则该函数是单调的。
也就是说，如果 {lean}`x ⊑ y`，则 {lean}`f x ⊑ f y`。
运算符 `⊑` 代表 {name}`Lean.Order.PartialOrder.rel`。

{docstring Lean.Order.monotone}

单调函数的不动点可以使用 {name}`fix` 来获取，它确实构造了一个不动点，如 {name}`fix_eq` 所示，

{docstring Lean.Order.fix}

{docstring Lean.Order.fix_eq}

:::paragraph

为了构造部分固定点，Lean 首先合成合适的 {name}`CCPO` 实例。

```lean -show
section
universe u v
variable (α : Type u)
variable (β : α → Sort v) [∀ x, CCPO (β x)]
variable (w : α)
```

* 如果函数的结果类型具有专用实例（如 {name}`Option` 和 {name}`instCCPOOption`），则该实例与函数类型 {name}`instCCPOPi` 的实例一起使用，以构造整个函数类型的实例。

* 否则，如果可以显示该函数的类型由见证者 {lean}`w` 占据，则使用包装器类型 {lean}`FlatOrder w` 的实例 {name}`FlatOrder.instCCPO`。在这个顺序中，{lean}`w` 是最小元素，所有其他元素都无法比较。

```lean -show
end
```

:::

接下来，对函数定义右侧的递归调用进行抽象；这变成了 {name}`fix` 的参数 `f`。单调性要求由 {tactic}`monotonicity`策略解决，它以语法驱动的方式应用组合单调性引理。

```lean -show
section
set_option linter.unusedVariables false
variable {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β] (more : (x : α) → β) (x : α)

local macro "…" x:term:arg "…" : term => `(more $x)
```

策略使用以下步骤解决 {lean}`monotone (fun x => … x …)` 形式的目标：

* 当不存在对 {lean}`x` 的依赖时应用 {name}`monotone_const`。
* 根据 {keywordOf Lean.Parser.Term.match}`match` 表达式进行拆分。
* 根据 {keywordOf termIfThenElse}`if` 表达式进行拆分。
* 如果值和类型不依赖于 {lean}`x`，则将 {keywordOf Lean.Parser.Term.let}`let` 表达式移至上下文。
* 当值和类型确实依赖于 {lean}`x` 时，对 {keywordOf Lean.Parser.Term.let}`let` 表达式进行 Zeta 缩减。
* 应用用 {attr}`partial_fixpoint_monotone` 注释的引理

```lean -show
end
```

以下单调性引理已注册，并且应允许在 `·` 指示的参数中的给定高阶函数下进行递归调用（但不允许其他参数，如 `_` 所示）。


{monotonicityLemmas}

这里描述的顺序理论框架也支持 {ref "coinductive-predicates"}[共归纳和归纳谓词]。
对于 {lean}`Prop` 值函数，{name}`Lean.Order.CompleteLattice` 实例提供最小和最大固定点，从而支持使用 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 和 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 子句进行定义。
