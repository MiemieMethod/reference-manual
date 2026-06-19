/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Różowski
-/

import VersoManual

import Manual.Meta
import ManualZh.RecursiveDefs.CoinductivePredicates.CoinductiveSyntax
import ManualZh.RecursiveDefs.CoinductivePredicates.Theory

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600


#doc (Manual) "共归纳谓词和归纳谓词" =>
%%%
tag := "coinductive-predicates"
%%%

:::paragraph
Lean 的 类型论 不直接支持共感类型。
然而，{deftech (key := "lattice-theoretic coinductive predicate")}[共归纳谓词]，即{lean}`Prop`中的递归定义，可以使用命题上的完整格结构来定义。
这些谓词提供了共归纳推理原则，其中可以通过表明某事物满足一些本身与共归纳谓词的定义一致的较小谓词来证明它满足谓词。
这是归纳推理的对偶，其中可以通过潜在的递归案例分析来分解已知事实。
共归纳谓词允许指定和推理无限的域。
计算机科学的一些例子包括：

 * 允许循环的状态转换系统的相似性
 * 小步操作语义的分歧
 * 活性特性

同时，{deftech (key := "lattice-theoretic inductive predicate")}[归纳谓词]也可以使用相同的机制通过最少的固定点来定义。
由于它使用相同的底层机制，因此普通 {tech}[归纳类型] 的替代方案与混合感应-共感应互块兼容。
:::

::::::example "Infinite Sequences" (open := true)

::::leanSection
```lean -show
variable {R : α → α → Prop} (x y : α) {pred : α → Prop}
```
:::paragraph
给定 {lean}`α` 上的关系 {lean}`R`（即，类型为 {lean}`α → α → Prop`），则 {lean}`α` 中存在从 {lean}`x` 开始的无限序列值，如果：

 * 存在一些 {lean}`y` 使得 {lean}`R x y`，并且
 * 存在来自 {lean}`y` 的无限序列。

这是一个典型的共归纳谓词：它描述了一种潜在的无限行为，可以表示为没有基例的单个推理规则。
:::
::::

这个递归规范是明确定义的，但是它不能被定义为普通的递归函数，因为定义的递归部分并没有减少。
然而，这是一个完全合理的共归纳定义：
```lean
coinductive InfSeq (R : α → α → Prop) : α → Prop where
  | step (y : α) : R x y →  InfSeq R y → InfSeq R x
```

:::leanSection
```lean -show
variable {R : α → α → Prop} (a : α) {pred : α → Prop}
```

共归纳推理原理采用谓词 {lean}`pred`。
为了证明 {lean}`a` 是无限 {lean}`R` 序列的开始，只需证明 {lean}`R` 将满足 {lean}`pred` 的每个元素与其他此类元素相关即可。
换句话说，无限序列的存在可以通过提供一个来证明：
```signature
InfSeq.coinduct (R : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ y, R a y ∧ pred y) →
  ∀ (a : α), pred a → InfSeq R a
```
:::
::::::




在 Lean 中有两种定义共归纳谓词的方法：

 1. 对 {lean}`Prop` 中的递归 {keywordOf Lean.Parser.Command.declaration}`def` 使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 终止子句，该子句采用最大的固定点。同样，{keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句将归纳谓词定义为最小固定点。

 2. 使用 {keywordOf Lean.Parser.Command.coinductive}`coinductive` 命令，该命令提供镜像 {keywordOf Lean.Parser.Command.inductive}`inductive` 声明的声明性语法。


# 定点终止条款
%%%
tag := "fixpoint-clauses"
%%%

递归 {lean}`Prop` 值函数可以定义为不动点，方法是使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 进行共归纳定义（最大不动点）或 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 进行归纳定义（最小不动点）进行注释。
这些终止子句的作用与 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 相同，但使用 {ref "lattice-prop"}[`Prop` 上的完整晶格结构]来计算适当的固定点。

## 共导固定点
%%%
tag := "coinductive-fixpoint-clause"
%%%

:::leanSection
```lean -show
variable {P Q : ReverseImplicationOrder}
```
{keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 子句将谓词定义为其定义方程的最大不动点。
该函数相对于 {name}`Lean.Order.ReverseImplicationOrder` 必须是单调的，其中 {lean}`P ⊑ Q` 表示 {lean}`Q → P`。
:::

:::leanSection
```lean -show
variable {P Q : α → ReverseImplicationOrder}
example : (P ⊑ Q) = (∀ x, P x ⊑ Q x) := rfl
example : (∀ x, P x ⊑ Q x) = (∀ x, Q x → P x) := rfl
```
此排序在谓词域上逐点扩展。
给定谓词 {lean}`P` 和 {lean}`Q` over {lean}`α`，{lean}`P ⊑ Q` 表示 {lean}`∀ x : α, P x ⊑ Q x`（即 {lean}`∀ x, Q x → P x`）。
:::

::::example "Monotonicity of Infinite Sequences"
```lean -show
variable (R : α → α → Prop) {a : α}
```
当存在从 {lean}`a` 开始的 {lean}`R` 相关元素的无限链时，命题 {lean}`InfSeq R a` 为真。
可以使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 编写：

```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

在精化期间，第一步是通过递归调用抽象此递归定义，产生与 {lean}`F` 等效的定义：
```lean
def F (R : α → α → Prop) (a : α) (P : α → Prop) : Prop :=
  ∃ b, R a b ∧ P b
```

:::leanSection
```lean -show
variable (P Q : α → Prop) (R : α → α → Prop)
```
为了使该函数在反向蕴涵方面是单调的，它必须保留 {lean}`P` 和 {lean}`Q` 之间的反向蕴涵排序。
也就是说，{lean}`∀ (x : α), Q x → P x` 必须隐含 {lean}`∀ (x : α), F R x Q → F R x P`：
:::
```lean
theorem F_monotone
    (h : ∀ (x : α), Q x → P x) :
    ∀ (x : α), F R x Q → F R x P := by
  grind [F]
```
::::

:::example "Failure of Monotonicity"

如果不存在通向该元素的无限链，则该元素在关系中是可访问的。
该属性在标准库中归纳定义为 {name}`Acc`。
这种共推定义它的尝试失败了：
```lean +error (name := nonmono)
def NoInfChain (R : α → α → Prop) (x : α) : Prop :=
  ∀ y, R x y → ¬NoInfChain R y
coinductive_fixpoint
```

```leanOutput nonmono
Could not prove 'NoInfChain' to be monotone in its recursive calls:
  Cannot eliminate recursive call in
    NoInfChain R y✝
```

对应的函数是：
```lean
def F (R : α → α → Prop) (x : α) (P : α → Prop) : Prop :=
  ∀ y, R x y → ¬P y
```

Lean 未能证明这个函数是单调的，因为事实上它并不是单调的：
```lean
theorem F_nonmonotone :
    ¬(∀ α R P Q,
      (∀ (x : α), Q x → P x) →
      (∀ (x : α), F R x Q → F R x P)) := by
  suffices ∃ α R P Q,
      ¬((∀ (x : α), Q x → P x) →
        (∀ (x : α), F R x Q → F R x P)) by
    simpa
  -- α = PUnit, R always true
  refine ⟨PUnit, fun _ _ => True, ?_⟩
  -- P is trivially true, Q is always false
  refine ⟨fun _ => True, fun _ => False, ?_⟩
  simp [F]
```
:::

:::example "Non-Predicates"

某个命题的无限合取可以定义为共归纳不动点：
```lean
def InfConj (p : Prop) : Prop := p ∧ InfConj p
coinductive_fixpoint
```

然而，这不能用于定义无限乘积：
```lean +error (name := nonprop)
def InfProd (α : Type) : Prop := α × InfProd α
coinductive_fixpoint
```
错误消息表明需要一个提议：
```leanOutput nonprop
Application type mismatch: The argument
  InfProd α
has type
  Prop
of sort `Type` but is expected to have type
  Type ?u.6
of sort `Type (?u.6 + 1)` in the application
  α × InfProd α
```

:::

正如通过部分不动点的定义一样，共归纳谓词的定义方程在定义上并不成立。
然而，精化器证明了等式引理，允许将谓词重写为展开式。

:::example "Definitional Equality and Coinductive Predicates"
{lean}`InfSeq` 是关系开始无限链的共归纳语句：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

因为它是使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 定义的，所以它在定义上并不等于其展开：
```lean +error (name := nondefeq)
example (R : α → α → Prop) (a : α) :
    InfSeq R a = ∃ b, R a b ∧ InfSeq R b := by
  rfl
```
```leanOutput nondefeq
Tactic `rfl` failed: The left-hand side
  InfSeq R a
is not definitionally equal to the right-hand side
  ∃ b, R a b ∧ InfSeq R b

α : Sort u_1
R : α → α → Prop
a : α
⊢ InfSeq R a = ∃ b, R a b ∧ InfSeq R b
```

然而，它配备了等式引理，可以将其重写为展开式：
```lean
example (R : α → α → Prop) (a : α) :
    InfSeq R a = ∃ b, R a b ∧ InfSeq R b := by
  rw [InfSeq]
```

:::

除了方程引理之外，Lean 还生成 {deftech}[共归纳原理]。
共归纳原理指出，共归纳谓词可以通过展示一些其他谓词来证明，这些谓词是单调函数的后固定点。

::::example "Coinduction Principles for Infinite Sequences"
{lean}`InfSeq` 是关系开始无限链的共归纳语句：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

对应的单调函数为：
```lean
def F (R : α → α → Prop) (a : α) (P : α → Prop) : Prop :=
  ∃ b, R a b ∧ P b
```

:::leanSection
```lean -show
variable {R : α → α → Prop} {a : α} {P : α → Prop}
```
由于 {lean}`InfSeq` 是 {lean}`F` 的最大不动点，因此存在小于 {lean}`F` 中其图像的任何谓词，足以表明满足该谓词的每个元素也满足 {lean}`InfSeq`。
换句话说，为了证明{lean}`InfSeq R a`，只需证明谓词{lean}`P`使得{lean}`∀ (a : α), P a → F R a P`或{lean}`∀ (a : α), P a → ∃ b, R a b ∧ P b`，然后显示{lean}`P a`就足够了。
:::
该共归纳原理被命名为 {lean}`InfSeq.coinduct`：
```signature
InfSeq.coinduct {α} (R : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ b, R a b ∧ pred b) →
  ∀ (a : α), pred a → InfSeq R a
```
::::

::::example "Simple Proof by Coinduction"
{lean}`InfSeq` 指出关系中有无限的元素序列，具有给定的起点：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

:::leanSection
```lean -show
variable {R : α → α → Prop} {a : α}
```
如果 {lean}`R a a` 成立，则存在一个在 {lean}`a` 处循环的平凡无限链：

```lean
theorem cycle_InfSeq {R : α → α → Prop} (a : α) :
    R a a → InfSeq R a := by
  apply InfSeq.coinduct (pred := fun m => R m m)
  intro x h
  exact ⟨x, h, h⟩
```
:::
::::

:::example "Infinite Chains of Less-Than"
{lean}`InfSeq` 指出关系中有无限的元素序列，具有给定的起点：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

存在与 {lean (type := "Nat → Nat → Prop")}`(· < ·)` 相关的自然数的无限链。
所有自然数都启动这样的链，因此谓词可以很简单：
```lean
theorem lt_InfSeq {n : Nat} : InfSeq (· < ·) n := by
  apply InfSeq.coinduct (pred := fun x => True)
  . intro k _
    refine ⟨k + 1, ?_⟩
    simp
  . trivial
```
:::

::::example "DFA Language Equivalence"
同归纳谓词自然地捕获了类似互模拟的概念。

:::leanSection
```lean -show
variable {Q : Type} {A : Type} {q : Q}
```
确定性有限自动机由一组状态 {lean}`Q`、字母表 {lean}`A`、{lean}`Q` 中的起始状态 {lean}`q`、定义接受状态的 {lean}`Q` 的子集以及将状态和字母表的元素带到新状态的转换函数给出：
:::
```lean
structure DFA (Q : Type) (A : Type) : Type where
  q₀ : Q
  δ : Q → A → Q
  accepting : Q → Bool
```

同一字母表上的两个自动机在就给定状态对是否接受达成一致时，具有来自给定状态对的等效语言，并且根据其转换函数，它们还具有来自所有后继状态的等效语言：
```lean
def languageEquivalent (M : DFA Q A) (M' : DFA Q' A)
    (q : Q) (q' : Q') : Prop :=
  M.accepting q = M'.accepting q' ∧
    ∀ (a : A), languageEquivalent M M' (M.δ q a) (M'.δ q' a)
coinductive_fixpoint
```

共归纳原理捕捉了确定性自动机互模拟的标准概念：
```signature
languageEquivalent.coinduct {Q A Q' : Type}
  (M : DFA Q A) (M' : DFA Q' A) (pred : Q → Q' → Prop) :
  (∀ (q : Q) (q' : Q'), pred q q' →
    M.accepting q = M'.accepting q' ∧
    ∀ (a : A), pred (M.δ q a) (M'.δ q' a)) →
  ∀ (q : Q) (q' : Q'), pred q q' →
    languageEquivalent M M' q q'
```

可以用来证明这两个 DFA 具有等效的语言：
:::row (align := "top")
```diagram (cssScale := "0.1") +inline
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "ok") |>.atop
(cfg.state 1 "fail") |>.atop
(cfg.loop 0 "a") |>.atop
(cfg.loop 1 "a, b") |>.atop
(cfg.edge 0 1 "b")
```

```diagram (cssScale := "0.1") +inline
open Illuminate in
let cfg : StateDiagramConfig := {}
cfg.start 0 |>.atop
(cfg.accept 0 "start") |>.atop
(cfg.accept 1 "ok") |>.atop
(cfg.state 2 "fail") |>.atop
(cfg.arc 0 1 "a" 30) |>.atop
(cfg.arc 1 0 "a" (-30)) |>.atop
(cfg.edge 1 2 "b") |>.atop
(cfg.arc 0 2 "b" (-140)) |>.atop
(cfg.loop 2 "a, b")
```
:::

这些 DFA 可以使用以下定义来表示：
```lean
inductive Alphabet where | a | b

inductive Q1 where | ok | fail

def loop : DFA Q1 Alphabet where
  q₀ := .ok
  δ
    | .ok, .a => .ok
    | _, _ => .fail
  accepting
    | .ok => True
    | _ => False

inductive Q2 where | start | ok | fail

def cycle : DFA Q2 Alphabet where
  q₀ := .start
  δ
    | .start, .a => .ok
    | .ok, .a => .start
    | _, _ => .fail
  accepting
    | .start | .ok => True
    | .fail => False
```

为了证明它们是等价的，第一步是定义一个捕获它们等价状态的关系。
然后，共归纳证明了它们在语言等价性方面实际上是等价的：
```lean
theorem loop_equiv_cycle :
    languageEquivalent loop cycle loop.q₀ cycle.q₀ := by
  let r : Q1 → Q2 → Prop
  | .ok, .start
  | .ok, .ok
  | .fail, .fail => True
  | _, _ => False
  apply languageEquivalent.coinduct (pred := r)
  . simp only [loop, cycle] <;>
    grind
  . simp [r, loop, cycle]
```
::::

## 感应固定点
%%%
tag := "inductive-fixpoint-clause"
%%%

{keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句将谓词定义为其定义方程的最小不动点。
该函数相对于 {name}`Lean.Order.ImplicationOrder`（{lean}`Prop` 上的顺序）必须是单调的，其中 `P ⊑ Q` 表示 `P → Q`。
这为谓词提供了普通 {keywordOf Lean.Parser.Command.declaration}`inductive` 类型声明的替代方案，并且是 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 的对偶。

在大多数情况下，普通的归纳类型声明更为方便。
但是，与普通归纳类型声明相比，归纳固定点定义有两个关键优势，使它们更适合某些特殊用例：
 * 普通归纳类型声明具有_语法_正性条件，其中归纳类型的递归出现不能出现在负位置。相反，归纳固定点需要单调性，这是一个语义条件。
 * 归纳固定点可以与共归纳固定点相互定义，从而允许混合归纳-共归纳谓词。

对于每个归纳固定点定义，都会自动证明归纳原理。
该归纳原理与为归纳类型声明生成的相应归纳原理具有相同的逻辑强度，但其表述方式略有不同，必须明确应用。

正如共归纳固定点一样，归纳固定点定义在定义上不会减少。
它们可以使用生成的等式引理展开，并且它们的归纳原理允许它们用于证明。

:::example "Reflexive Transitive Closures as Inductive Fixpoints"
关系的自反传递闭包可以定义为归纳谓词：
```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```

相同的谓词可以定义为最小不动点。
```lean
def StarInd (tr : α → α → Prop) (q₁ q₂ : α) : Prop :=
  q₁ = q₂ ∨ ∃ (z : α), (tr q₁ z ∧ StarInd tr z q₂)
inductive_fixpoint
```

产生归纳原理：
```signature
StarInd.induct (tr : α → α → Prop) (q₂ : α) (pred : α → Prop)
  (hyp : ∀ (q₁ : α), (q₁ = q₂ ∨ ∃ z, tr q₁ z ∧ pred z) → pred q₁)
  (q₁ : α) :
  StarInd tr q₁ q₂ → pred q₁
```

可以利用归纳原理证明这两个公式是等价的：
```lean -keep
theorem star_implies_starInd (R : α → α → Prop) :
    ∀ a b : α, Star R a b = StarInd R a b := by
  intro a b
  ext
  constructor
  . intro h
    induction h <;> grind [StarInd]
  . apply StarInd.induct R b (Star R · b) ?_ a
    grind [Star]
```
:::

## 相互块中的混合归纳-共归纳谓词
%%%
tag := "mixed-mutual-fixpoint"
%%%

{tech}[mutual block] 可以混合 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 和 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句。
块中的每个定义都必须使用这两个子句之一。
该结构使用两个 {ref "lattice-prop"}[`Prop` 上的晶格结构]：{name Lean.Order.ImplicationOrder}`ImplicationOrder` 用于归纳定义，{name Lean.Order.ReverseImplicationOrder}`ReverseImplicationOrder` 用于共归纳定义。
在这两种情况下，都会计算相应晶格的最小不动点；使用反向蕴含顺序，最小不动点与标准顺序中的最大不动点重合。
这是可能的，因为当遇到否定或蕴涵时，{ref "coinductive-monotonicity"}[单调性]引理会在两个顺序之间翻转。

:::example "Mixed Inductive-Coinductive Mutual Block"
该相互块包含相互递归的共归纳和归纳谓词：
```lean
mutual
  def tick : Prop :=
    ¬tock
  coinductive_fixpoint

  def tock : Prop :=
    ¬tick
  inductive_fixpoint
end
```

为互块中的第一个定义生成互感应原理：
```signature
tick.mutual_induct (pred_1 pred_2 : Prop) :
  (pred_1 → pred_2 → False) → ((pred_1 → False) → pred_2) →
  (pred_1 → tick) ∧ (tock → pred_2)
```
:::


# 更多例子
%%%
tag := "coinductive-predicate-examples"
%%%

:::example "Infinite Chains from Universal Reachability" (open := true)
```lean -show
variable {a : α}
```
关系的自反传递闭包通过归纳指定：
```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```
无限序列通过共归纳法指定：
```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

如果从起始状态 {lean}`a` 通过自反传递闭包可到达的每个状态都有后继，则存在从 {lean}`a` 开始的无限链。
谓词 {lean}`AllSeqInf` 声明每个可达状态都有一个后继：
```lean
def AllSeqInf (R : α → α → Prop) (x : α) : Prop :=
  ∀ y : α, Star R x y → ∃ z, R y z
```
通过共归纳证明这意味着存在无限链：
```lean
theorem infSeq_of_allSeqInf (R : α → α → Prop) :
    ∀ x, AllSeqInf R x → InfSeq R x := by
  apply InfSeq.coinduct
  intro x H
  unfold AllSeqInf at H
  have H' := H x (.refl x)
  obtain ⟨y, Rxy⟩ := H'
  exact ⟨y, Rxy,
    fun y' Ryy' =>
      H y' (.step x y y' Rxy Ryy')⟩
```
:::


:::example "Coinduction Up-To Transitive Closure" (open := true)
强化的共归纳原理允许共归纳假设应用于传递闭包。
给定一个谓词 {lean}`X`，使得每个 {lean}`X` 状态通过一个或多个 {lean}`R` 步引导至另一个 {lean}`X` 状态，则每个 {lean}`X` 状态满足 {lean}`InfSeq R`：

```lean
inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : ∀ x : α, Star R x x
  | step : ∀ x y z, R x y → Star R y z → Star R x z
```

```lean
def InfSeq (R : α → α → Prop) (a : α) : Prop :=
  ∃ b, R a b ∧ InfSeq R b
coinductive_fixpoint
```

```lean
variable {α : Sort _} {R : α → α → Prop}

inductive Plus (R : α → α → Prop) :
    α → α → Prop where
  | left : ∀ a b c,
      R a b → Star R b c → Plus R a c

theorem plusStar (a b : α) :
    Plus R a b → Star R a b := by
  intro h; cases h
  case left _ h₂ h₃ =>
    exact Star.step _ _ _ h₂ h₃

theorem plusStarTrans (a b c : α) :
    Star R a b → Plus R b c →
    Plus R a c := by
  intro s p; induction s
  case refl => exact p
  case step d e _ rel _ ih =>
    exact Plus.left _ _ _ rel
      (plusStar _ _ (ih p))

variable (X : α → Prop)

theorem infSeqCoinductionUpTo :
    (∀ (a : α), X a →
      ∃ b, Plus R a b ∧ X b) →
    ∀ (a : α), X a → InfSeq R a := by
  intro h₁ a rel
  apply @InfSeq.coinduct _ _
    (fun a => ∃ b, Star R a b ∧ X b)
  case x =>
    obtain ⟨a', h₁, h₂⟩ := h₁ a rel
    exact ⟨a', plusStar _ _ h₁, h₂⟩
  case hyp =>
    intro a0 ⟨a1, h₃, h₄⟩
    obtain ⟨mid, h₅, h₆⟩ := h₁ a1 h₄
    have t := plusStarTrans a0 a1 mid h₃ h₅
    cases t
    case left mid2 rel2 s =>
      exact ⟨mid2, rel2, mid, s, h₆⟩
```
:::



{include 0 ManualZh.RecursiveDefs.CoinductivePredicates.CoinductiveSyntax}

{include 0 ManualZh.RecursiveDefs.CoinductivePredicates.Theory}
