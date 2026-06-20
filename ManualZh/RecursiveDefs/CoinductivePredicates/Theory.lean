/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order


#doc (Manual) "理论与构建" =>
%%%
tag := "coinductive-theory"
%%%

共归纳和归纳谓词的构造建立在完全格的 Knaster-Tarski 不动点定理的基础上。
虽然 {ref "partial-fixpoint-theory"}[部分固定点递归] 依赖于链完整偏序 ({name}`Lean.Order.CCPO`)，但共归纳和归纳谓词使用更强的 {deftech (key := "complete lattice")}_完整格_ 概念。

关键思想是 {lean}`Prop` 带有按蕴涵排序的 {ref "complete-lattices"}[完整格] 结构（`P ⊑ Q` 当 `P → Q` 时），并且完整格上的任何单调内函数都具有根据 Knaster-Tarski 定理的最小和最大不动点。
共导谓词使用 {ref "lattice-prop"}[反向蕴涵顺序]（当 `Q → P` 时为 `P ⊑ Q`），因此此反向顺序中的最小固定点是标准顺序中的最大固定点。
对于 `α → Prop` 形式的谓词，此点阵结构到函数类型的逐点提升提供了必要的设置。
对于互块，完全格的乘积又是完全格。
该结构与 {ref "partial-fixpoint"}[部分固定点] 机械共享其内部结构。


# 完全格子
%%%
tag := "complete-lattices"
%%%

{tech (key := "complete lattice")}[完整格] 是一个偏序，其中每个子集都有一个最小上界，而不仅仅是每个链。

{docstring Lean.Order.CompleteLattice}

每个完整的格子都会产生一个 CCPO，因为每个链都是特定的子集，但反之通常不成立。
例如，居住类型上的平面顺序（由 {ref "partial-fixpoint"}[部分固定点] 用于尾递归函数）是 CCPO，但不是完整的格。

在完全格中，单调函数的最小不动点可以直接构造为所有预不动点的下确点，遵循 Knaster-Tarski 定理：

{docstring Lean.Order.lfp +allowMissing}

{docstring Lean.Order.lfp_fix +allowMissing}

相应的归纳原理是 Park 归纳：为了证明某个属性对于最小固定点的所有元素都成立，只需证明该属性通过定义函数的一次应用而得以保留。

{docstring Lean.Order.lfp_le_of_le_monotone}

# 命题的格结构
%%%
tag := "lattice-prop"
%%%

{lean}`Prop` 类型允许两个自然完整的晶格结构，每个结构都会产生一种不同类型的固定点：

:::paragraph

 * {name}`Lean.Order.ImplicationOrder` 通过暗示对命题进行排序：`P ⊑ Q` 表示 `P → Q`。
   此顺序中的最小固定点产生在定义规则下闭合的最小谓词，对应于 {tech (key := "lattice-theoretic inductive predicate")}_inducing predicate_。
   这是 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 使用的顺序。

 * {name}`Lean.Order.ReverseImplicationOrder` 通过反向蕴涵对命题进行排序：`P ⊑ Q` 表示 `Q → P`。
   此_反转_顺序中的最小固定点是标准顺序中的_最大_固定点，产生与定义规则一致的最大谓词。
   这对应于 {tech (key := "lattice-theoretic coinductive predicate")}_coininduced predicate_。
   这是 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 使用的顺序。

:::

完整格子中的箭头类型继承了完整格子结构，完整格子的乘积也是完整格子。
这些闭包属性允许将构造扩展到任意数量的谓词和相互块。

# 单调性
%%%
tag := "coinductive-monotonicity"
%%%

将谓词定义为不动点要求定义方程相对于适当的阶数是单调的。
对于 {keywordOf Lean.Parser.Command.declaration}`coinductive` 命令以及 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 和 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 终止子句，单调性要求是语义而不是语法。
{tactic}`monotonicity`策略通过组合用 {attr}`partial_fixpoint_monotone` 属性注册的引理来证明单调性。
这种方法比严格的积极性更为宽容。
例如，通过翻转 {name}`Lean.Order.ImplicationOrder` 和 {name}`Lean.Order.ReverseImplicationOrder` 之间的顺序可以正确处理否定和蕴涵。
这就是允许在同一个 {tech (key := "mutual block")}[互块]中混合感应和共感应固定点的原因。

{tactic}`monotonicity`策略处理的构造集是可扩展的：注册额外的 {attr}`partial_fixpoint_monotone` 引理可教导策略处理新的逻辑连接词或高阶函数。
或者，当通过 {keyword}`monotonicity` 子句使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 时，可以提供显式单调性证明项。

有关已注册单调性引理的完整列表以及有关单调性策略的更多详细信息，请参阅 {ref "partial-fixpoint-theory"}[部分不动点的理论部分]。
