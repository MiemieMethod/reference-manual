/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Meta.Monotonicity
import ManualZh.RecursiveDefs.PartialFixpoint.Theory

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order

set_option maxRecDepth 600

#doc (Manual) "部分不动点递归" =>
%%%
tag := "partial-fixpoint"
%%%

所有定义从根本上来说都是方程：定义的新常数等于定义的右侧。
对于 {ref "structural-recursion"}[结构递归] 定义的函数，该等式保持 {tech (key := "definitional equality")}[定义]，并且该函数的应用返回一个唯一的值。
对于 {ref "well-founded-recursion"}[良基递归] 定义的函数，方程可能仅适用于 {tech (key := "proposition")}[命题]，但函数对参数的所有类型正确应用都等于定义规定的相应值。
在这两种情况下，函数对所有输入都终止的事实意味着通过应用函数计算的值始终是唯一确定的。


在某些情况下，如果函数并非针对所有参数都终止，则方程可能无法唯一地确定每个输入的函数返回值，但仍然存在定义方程成立的函数。
在这些情况下，定义为 {deftech}_partial fixpoint_ 仍然是可能的。
任何满足定义方程的函数都可以用来证明该方程不会产生逻辑矛盾，然后该方程可以被证明为关于该函数的定理。
与定义递归函数的其他策略一样，编译后的代码按最初编写的方式使用该函数；与消除器或可访问性证明的递归方面的定义类似，用于定义部分不动点的函数仅用于证明 Lean 逻辑中函数方程的合理性，以达到数学推理的目的。

术语 {tech}_partial fixpoint_ 特定于 Lean。
声明为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数不需要终止证明，只要其返回值的类型是固定的即可，但从 Lean 的逻辑角度来看，它们是完全不透明的。
另一方面，部分不动点可以在编写证明时使用其定义方程进行重写。
从逻辑上讲，部分不动点是应用时不会减少 {tech (key := "definitional equality")}[定义] 的总函数，但为其提供了等式重写规则。
它们是_部分的_，因为定义方程不一定为所有可能的参数指定一个值。


虽然部分固定点确实允许定义无法使用结构或良基递归表达的函数，但该技术在其他情况下也很有用。
即使在定义方程完全描述了函数的行为并且可以使用 {ref "well-founded-recursion"}[良基递归] 进行终止证明的情况下，将函数定义为部分固定点以避免编写终止证明可能会更方便。

仅当通过使用 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 注释定义明确请求时，才会将递归函数定义为部分固定点。

:::paragraph
有两类函数可以定义为部分不动点：

 * 返回类型为居住类型的尾递归函数

 * 以合适的 monad 形式返回值的函数，例如 {name}`Option` monad

这两类都由相同的理论和构造支持：链完备偏序中单调方程的最小不动点。

:::

正如结构函数和良基递归一样，Lean 允许将 {tech}[相互递归] 函数定义为部分固定点。
要使用此功能，{tech}[mutual block] 中的每个函数定义都必须使用 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 修饰符进行注释。

```lean -show
section
variable (p : Nat → Bool)
```

:::example "Definition by Partial Fixpoint"

以下函数查找谓词 {lean}`p` 成立的最小自然数。
如果 `p` 永远不成立，则此方程不指定行为：函数 {lean}`find` 可以返回 {lean  (type := "Nat")}`42` 或任何其他 {lean}`Nat` 在这种情况下，并且仍然满足方程。

```lean
def find (p : Nat → Bool) (i : Nat := 0) : Nat :=
  if p i then
    i
  else
    find p (i + 1)
partial_fixpoint
```

精化器可以证明满足方程的函数存在。
在 Lean 的逻辑中，{lean}`find` 被定义为任意此类函数。
:::

```lean -show
end
```

# 尾递归函数
%%%
tag := "partial-fixpoint-tailrec"
%%%

:::paragraph

如果满足以下两个条件，则递归函数可以定义为部分不动点：

 1. 该函数的返回类型是固定的（与 {ref "partial-unsafe"}[标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数]一样）— {name}`Nonempty` 或 {name}`Inhabited` 实例都可以工作。
 2. 所有递归调用都在函数的 {tech}[尾部位置] 中。

如果表达式是：

 * 函数体本身，
 * 位于尾部位置的 {keywordOf Lean.Parser.Term.match}`match` 表达式的分支，
 * 位于尾部位置的 {keywordOf termIfThenElse}`if` 表达式的分支，以及
 * 位于尾部位置的 {keywordOf Lean.Parser.Term.let}`let` 表达式的主体。

特别是，{keywordOf Lean.Parser.Term.match}`match` 表达式的 {tech (key := "match discriminant")}[判别式]、{keywordOf termIfThenElse}`if` 表达式的条件和函数的参数不是尾部位置。

:::

```lean -show
-- Test that nonempty is enough
inductive A : Type where
  | mkA
  | mkA'

instance : Nonempty A := ⟨.mkA⟩

def getA (n : Nat) : A :=
  getA (n + 1)
partial_fixpoint

example (n : Nat) : getA n = getA (n + 3) := by
  conv => lhs; rw [getA, getA, getA]
```

:::example "Loops are Tail Recursive Functions"

因为函数体本身是一个{tech}[尾部位置]，所以无限循环函数{lean}`loop`是尾递归的。
它可以被定义为部分固定点。

```lean
def loop (x : Nat) : Nat := loop (x + 1)
partial_fixpoint
```

:::

:::example "Tail Recursion with Branching"

{lean}`Array.find` 也可以使用具有终止证明的良基递归进行构造，但使用 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 进行定义可能更方便，无需终止证明。

```lean
def Array.find (xs : Array α) (p : α → Bool)
    (i : Nat := 0) : Option α :=
  if h : i < xs.size then
    if p xs[i] then
      some xs[i]
    else
      Array.find xs p (i + 1)
  else
    none
partial_fixpoint
```

如果递归调用的结果不只是返回，而是传递给另一个函数，则它不在尾部位置，并且此定义失败。

```lean -keep +error (name := nonTailPos)
def List.findIndex (xs : List α) (p : α → Bool) : Int :=
  match xs with
  | [] => -1
  | x::ys =>
    if p x then
      0
    else
      have r := List.findIndex ys p
      if r = -1 then -1 else r + 1
partial_fixpoint
```
递归调用的错误消息是：
```leanOutput nonTailPos
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    if ys✝.findIndex p = -1 then -1 else ys✝.findIndex p + 1
  Tried to apply 'monotone_ite', but failed.
  Possible cause: A missing `MonoBind` instance.
  Use `set_option trace.Elab.Tactic.monotonicity true` to debug.
```

:::

# 一元函数
%%%
tag := "partial-fixpoint-monadic"
%%%


如果函数的返回类型是作为 {name}`Lean.Order.MonoBind` 实例的 monad（例如 {name}`Option`），则将函数定义为部分固定点会更强大。
在这种情况下，递归调用不仅限于尾部位置，还可能发生在高阶一元函数内部，例如 {name}`bind` 和 {name}`List.mapM`。

其适用的高阶函数集是 {ref "partial-fixpoint-theory"}[extensible]，因此这里没有给出详尽的列表。
我们的愿望是接受使用 {name}`bind` 等抽象单子操作构建的单子递归函数定义，但不会打开单子的抽象（例如，通过匹配 {name}`Option` 值）。
特别是，使用 {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation] 应该可以。

:::example "Monadic functions"

以下函数在 {name}`Option` monad 中实现 Ackermann 函数，并且无需（显式或隐式）终止证明即可接受：

```lean -keep
def ack : (n m : Nat) → Option Nat
  | 0,   y   => some (y+1)
  | x+1, 0   => ack x 1
  | x+1, y+1 => do ack x (← ack (x+1) y)
partial_fixpoint
```

递归调用也可能发生在高阶函数中，例如 {name}`List.mapM`（如果设置正确）和 {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation]：

```lean -keep
structure Tree where cs : List Tree

def Tree.rev (t : Tree) : Option Tree := do
  Tree.mk (← t.cs.reverse.mapM (Tree.rev ·))
partial_fixpoint

def Tree.rev' (t : Tree) : Option Tree := do
  let mut cs := []
  for c in t.cs do
    cs := (← c.rev') :: cs
  return Tree.mk cs
partial_fixpoint
```

递归调用结果上的模式匹配将阻止部分固定点的定义通过：

```lean -keep +error (name := monoMatch)
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      match List.findIndex ys p with
      | none => none
      | some r => some (r + 1)
partial_fixpoint
```
```leanOutput monoMatch
Could not prove 'List.findIndex' to be monotone in its recursive calls:
  Cannot eliminate recursive call `List.findIndex ys p` enclosed in
    match ys✝.findIndex p with
    | none => none
    | some r => some (r + 1)
```

在这种特殊情况下，使用 {name}`Functor.map` 而不是显式模式匹配有助于：

```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```
:::

# 部分正确性定理
%%%
tag := "partial-correctness-theorem"
%%%


对于定义为部分不动点的每个函数，Lean 证明满足定义方程。
这使得可以通过重写来证明。
然而，这些方程定理不足以推理函数在函数规范未终止的参数上的行为。
在运行时导致无限递归的代码路径最终将成为潜在证明中的无限重写链。

另一方面，合适的单子中的部分固定点提供了额外的定理，将未定义的值从非终止映射到单子中的合适的值。
在 {name}`Option` 单子中，对于定义方程指定非终止的所有函数输入，部分固定点等于 {name}`Option.none`。
根据这一事实，Lean 证明了函数的 {deftech}_部分正确性定理_，该定理允许当函数结果为 {name}`Option.some` 时得出事实。


::::example "Partial Correctness Theorem"

回想一下之前示例中的 {lean}`List.findIndex`：

```lean
def List.findIndex (xs : List α) (p : α → Bool) : Option Nat :=
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      some 0
    else
      (· + 1) <$> List.findIndex ys p
partial_fixpoint
```

通过此函数定义，Lean 自动证明以下部分正确性定理：

```signature
List.findIndex.partial_correctness.{u_1} {α : Type u_1}
  (p : α → Bool)
  (motive : List α → Nat → Prop)
  (h :
    ∀ (findIndex : List α → Option Nat),
      (∀ (xs : List α) (r : Nat), findIndex xs = some r → motive xs r) →
        ∀ (xs : List α) (r : Nat),
          (match xs with
              | [] => none
              | x :: ys =>
                if p x = true then some 0
                else (fun x => x + 1) <$> findIndex ys) = some r →
            motive xs r)
  (xs : List α) (r : Nat) :
  xs.findIndex p = some r →
    motive xs r
```

:::paragraph
这里，动机是 {lean}`List.findIndex` 的参数和返回类型之间的关系，其中 {name}`Option` 从返回类型中删除。
如果给定具有与 {lean}`List.findIndex` 兼容的签名的任意部分函数，则以下内容成立：

 * 对于任意函数返回值（而不是 {name}`none`）的所有输入，动机都得到满足，

 * 使用定义方程进行一次重写，其中递归调用被任意函数替换，也意味着动机的满足

那么对于 {lean}`List.findIndex` 返回 {name}`some` 的所有输入，动机都得到满足。

:::

部分正确性定理是一个推理原理。
它可用于证明结果数字是列表中的有效索引，并且谓词适用于该索引：

```lean
theorem List.findIndex_implies_pred
    (xs : List α) (p : α → Bool) :
    xs.findIndex p = some i →
    ∃x, xs[i]? = some x ∧ p x := by
  apply List.findIndex.partial_correctness
          (motive := fun xs i => ∃ x, xs[i]? = some x ∧ p x)
  intro findIndex ih xs r hsome
  split at hsome
  next => contradiction
  next x ys =>
    split at hsome
    next =>
      have : r = 0 := by simp_all
      simp_all
    next =>
      simp only [Option.map_eq_map, Option.map_eq_some_iff] at hsome
      obtain ⟨r', hr, rfl⟩ := hsome
      specialize ih _ _ hr
      simpa
```

::::

# 具有部分不动点的互递归
%%%
tag := "mutual-partial-fixpoint"
%%%

Lean 支持使用 {tech}[部分固定点] 定义 {tech}[相互递归] 函数。
可以使用 {tech}[mutual block] 引入相互递归，但它也可以由 {keywordOf Lean.Parser.Term.letrec}`let rec` 表达式和 {keywordOf Lean.Parser.Command.declaration}`where` 块产生。
相互良基递归的规则应用于一组实际相互递归、提升的定义，这些定义由相互组的 {ref "mutual-syntax"}[精化步骤] 产生。

如果交互组中的所有函数都有 {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` 子句，则使用此策略。

{include 1 ManualZh.RecursiveDefs.PartialFixpoint.Theory}
