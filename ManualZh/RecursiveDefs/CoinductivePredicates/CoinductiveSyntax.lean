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

set_option maxRecDepth 600


#doc (Manual) "`coinductive` 命令" =>
%%%
file := "The-___coinductive___-Command"
tag := "coinductive-command"
%%%

{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令提供用于定义 {tech (key := "lattice-theoretic coinductive predicate")}[共归纳谓词] 的语法，该语法镜像 {keywordOf Lean.Parser.Command.declaration}`inductive` 声明的语法。
该声明不是使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 编写递归函数，而是使用构造函数编写，就像归纳类型一样。

:::syntax command (title := "Coinductive Predicates")
```grammar
coinductive $_ $_* : $_ where
  $_*
```
{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令通过指定其构造函数来定义共归纳谓词。
它只能用于定义谓词，即在 {lean}`Prop` 中赋值的类型。
:::

{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令定义与相应的 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 定义相同的谓词。
它还生成构造函数和案例分析原理，就像普通的 {keywordOf Lean.Parser.Command.declaration}`inductive` 声明一样。

:::example "Coinductive Predicate via `coinductive`"
前面示例中的谓词 {lean}`InfSeq` 可以等效地使用 {keywordOf Lean.Parser.Command.coinductive}`coinductive` 命令定义：

```lean
variable (α : Type)

coinductive InfSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeq r b → InfSeq r a
```

这会生成一个构造函数和一个 {tech (key := "coinduction principle")}[代归纳原理]：

```signature
InfSeq.step (α : Type) (r : α → α → Prop) {a b : α} :
  r a b → InfSeq α r b → InfSeq α r a
```

```signature
InfSeq.coinduct (α : Type) (r : α → α → Prop) (pred : α → Prop) :
  (∀ (a : α), pred a → ∃ b, r a b ∧ pred b) →
  ∀ (a : α), pred a → InfSeq α r a
```

还生成了案例分析原理：
```signature
InfSeq.casesOn (α : Type) (r : α → α → Prop)
    {motive : (a : α) → InfSeq α r a → Prop} {a : α} (t : InfSeq α r a) :
  (∀ {a b} (a_1 : r a b) (a_2 : InfSeq α r b),
    motive a (InfSeq.step α r a_1 a_2)) →
  motive a t
```

案例分析可通过 {tactic}`cases`策略用于证明：

```lean
theorem InfSeq.casesOnTest (r : α → α → Prop)
    (a : α) : InfSeq α r a → ∃ b, r a b := by
  intro h
  cases h
  case step b _ hr => exists b
```
:::


# 精化
%%%
file := "Elaboration"
tag := "coinductive-elaboration"
%%%

在底层，{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令分几个步骤详细说明。
首先，它被当作普通的 {keywordOf Lean.Parser.Command.declaration}`inductive` 声明来处理。
然而，在使用内核注册类型之前，会创建 {deftech (key := "flat inductive")}_flat inductor_（也称为 _functor_）：构造函数前提中共归纳谓词的每个递归出现都被显式参数替换。


:::example "Flat Inductive"
此示例使用无限序列的共归纳规范：
```lean -show
variable (α : Type)
```
```lean
coinductive InfSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeq r b → InfSeq r a
```
对于 {lean}`InfSeq`，生成的平坦电感为：

```signature
InfSeq._functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
```

它的构造函数使用谓词参数来代替递归调用：

```lean (name := printFunctor) -keep
set_option pp.proofs true in
#print InfSeq._functor
```

```leanOutput printFunctor
inductive InfSeq._functor : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop
number of parameters: 3
constructors:
InfSeq._functor.step : ∀ (α : Type) (r : α → α → Prop) (InfSeq._functor.call : α → Prop) {a b : α},
  r a b → InfSeq._functor.call b → InfSeq._functor α r InfSeq._functor.call a
```
:::

然后构造等效的 {deftech (key := "existential form")}_存在形式_，将每个构造函数表示为从属乘积（即存在量词和连词）的析取。
这种形式用于单调性检查和生成可读的共归纳原理。

:::example "Existential Form"
```lean -show
variable (α : Type)
```
```lean
coinductive InfSeq (r : α → α → Prop) : α → Prop where
  | step : r a b → InfSeq r b → InfSeq r a
```

```lean (name := printExist)
set_option pp.proofs true in
#print InfSeq._functor.existential
```

```leanOutput printExist
def InfSeq._functor.existential : (α : Type) → (α → α → Prop) → (α → Prop) → α → Prop :=
fun α r InfSeq._functor.call a => ∃ b, r a b ∧ InfSeq._functor.call b
```

这两种形式通过等价定理联系起来：

```lean (name := checkExistEquiv) -keep
#check @InfSeq._functor.existential_equiv
```
```leanOutput checkExistEquiv
InfSeq._functor.existential_equiv : ∀ (α : Type) (r : α → α → Prop) (InfSeq._functor.call : α → Prop) (a : α),
  InfSeq._functor α r InfSeq._functor.call a ↔ ∃ b, r a b ∧ InfSeq._functor.call b
```
:::

然后使用 {ref "partial-fixpoint"}[部分固定点] 机制和 {name}`Lean.Order.ReverseImplicationOrder` 完整格实例将存在形式注册为共归纳谓词。
利用平面归纳和存在形式之间的对应关系，生成构造函数和案例分析消除器，就像常规的归纳类型一样。

:::paragraph
为名为 `P` 的共归纳谓词生成以下声明：

 * `P._functor`：{tech (key := "flat inductive")}[扁平电感]
 * `P._functor.existential`：{tech (key := "existential form")}[存在形式]
 * `P._functor.existential_equiv`：两种形式之间的等效性
 * `P.functor_unfold`：将共归纳谓词连接到其平面归纳的定理
 * 构造函数（例如，`P.step`）：对应于声明中的每个构造函数
 * `P.casesOn`：案例分析原理
  * `P.coinduct`: {tech (key := "coinduction principle")}[共归纳原理]
:::

# 互感和感性块
%%%
file := "Mutual-Coinductive-and-Inductive-Blocks"
tag := "mutual-coinductive-syntax"
%%%

在包含 {keywordOf Lean.Parser.Command.coinductive}`coinductive` 定义的 {tech (key := "mutual block")}[相互块] 中，{keywordOf Lean.Parser.Command.inductive}`inductive` 关键字被重新解释：它不是注册为普通的内核归纳类型，而是通过晶格理论 {tech (key := "lattice-theoretic inductive predicate")}[感应固定点] 机制进行详细说明。
这允许在同一个共同块中混合共归纳谓词和归纳谓词。

:::example "Mutual Coinductive-Inductive Block"
谓词 {lean}`Tick` 和 {lean}`Tock` 相互定义，其中 {lean}`Tick` 作为共归纳谓词，{lean}`Tock` 作为归纳谓词：

```lean
mutual
  coinductive Tick : Prop where
  | mk : ¬Tock → Tick

  inductive Tock : Prop where
  | mk : ¬Tick → Tock
end
```

两个构造函数都可用：
```lean (name := checkTickMk)
#check @Tick.mk
```
```leanOutput checkTickMk
Tick.mk : ¬Tock → Tick
```
```lean (name := checkTockMk)
#check @Tock.mk
```
```leanOutput checkTockMk
Tock.mk : ¬Tick → Tock
```

产生互感原理：
```lean (name := checkMutualInduct)
#check @Tick.mutual_induct
```
```leanOutput checkMutualInduct
Tick.mutual_induct : ∀ (pred_1 pred_2 : Prop),
  (pred_1 → pred_2 → False) → ((pred_1 → False) → pred_2) → (pred_1 → Tick) ∧ (Tock → pred_2)
```
:::

# 限制
%%%
file := "Restrictions"
tag := "coinductive-restrictions"
%%%

:::paragraph
{keywordOf Lean.Parser.Command.declaration}`coinductive` 命令具有以下限制：

 * 它只能定义谓词，即 {lean}`Prop` 中赋值的类型。
   尝试在 {lean}`Type` 或更高的宇宙中定义共归纳类型会导致错误。

 * 定义的谓词可能没有 {tech (key := "macro scopes")}[宏范围]。

 * 尚不支持通过 {keywordOf Lean.Parser.Term.match}`match` 的模式匹配；请改用 {tactic}`cases`策略。

:::

:::example "Restriction to Predicates"
尝试定义不是谓词的共归纳类型会导致错误：

```lean +error (name := notPredErr)
coinductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat
```
```leanOutput notPredErr
`coinductive` keyword can only be used to define predicates
```
:::
