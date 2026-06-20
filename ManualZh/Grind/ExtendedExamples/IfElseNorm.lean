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


open Lean.Grind

#doc (Manual) "`if`-`then`-`else` 归一化" =>
%%%
tag := "grind-if-then-else-norm"
%%%

```lean -show
open Std
```

此示例展示了 {tactic}`grind` 的“开箱即用”功能。
后面的示例将探索添加 {attrs}`@[grind]` 注释作为开发过程的一部分，以使 {tactic}`grind` 在新领域中更加有效。
此示例不依赖于 {tactic}`grind` 的任何代数扩展，我们只是使用：
* 从库中实例化带注释的定理，
* {tech (key := "congruence closure")}[同余闭包]，以及
* 案件分割。

这里的解决方案建立在 Chris Hughes 早期的形式化基础上，但有一些显着的改进：
* 验证与代码分开，
* 现在证明是 {tactic}`fun_induction` 和 {tactic}`grind` 的单行组合，
* 该证明对于代码的更改（例如，将 {name}`HashMap` 替换为 {name}`TreeMap`）以及精确验证条件的更改具有鲁棒性。


# 问题
%%%
tag := "zh-grind-extendedexamples-ifelsenorm-h001"
%%%

以下是 Rustan Leino 对问题的原始描述，如 [Leonardo de Moura 发布](https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Rustan's.20challenge) 在 Lean Zulip 上的描述：

> 数据结构是一个带有布尔文字、变量和 if-then-else 表达式的表达式。

  目标是将此类表达式规范化为以下形式：
  a) 没有嵌套的 if：if 表达式的条件部分本身不是 if 表达式
  b) 无常量测试：if 表达式的条件部分不是常量
  c) 没有多余的 if：if 的 then 和 else 分支不同
  d) 每个变量最多计算一次：条件的自由变量与 then 分支中的自由变量不相交，也与 else 分支中的自由变量不相交。

  人们应该证明标准化函数产生满足这四个条件的表达式，并且还应该证明标准化函数保留了给定表达式的含义。

# 正式声明
%%%
tag := "zh-grind-extendedexamples-ifelsenorm-h002"
%%%

:::leanFirst
为了形式化 Lean 中的语句，我们使用归纳类型{name}`IfExpr`：

```lean
/--
An if-expression is either boolean literal, a
numbered variable, or an if-then-else expression
where each subexpression is an if-expression.
-/
inductive IfExpr
  | lit : Bool → IfExpr
  | var : Nat → IfExpr
  | ite : IfExpr → IfExpr → IfExpr → IfExpr
deriving DecidableEq
```
:::

:::leanFirst
并定义一些归纳谓词和 {name IfExpr.eval}`eval` 函数，因此我们可以声明四个所需的属性：

```lean
namespace IfExpr

/--
An if-expression has a "nested if" if it contains
an if-then-else where the "if" is itself an if-then-else.
-/
def hasNestedIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (ite _ _ _) _ _ => true
  | ite _ t e => t.hasNestedIf || e.hasNestedIf

/--
An if-expression has a "constant if" if it contains
an if-then-else where the "if" is itself a literal.
-/
def hasConstantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite (lit _) _ _ => true
  | ite i t e =>
    i.hasConstantIf || t.hasConstantIf || e.hasConstantIf

/--
An if-expression has a "redundant if" if
it contains an if-then-else where
the "then" and "else" clauses are identical.
-/
def hasRedundantIf : IfExpr → Bool
  | lit _ => false
  | var _ => false
  | ite i t e => t == e || i.hasRedundantIf ||
      t.hasRedundantIf || e.hasRedundantIf

/--
All the variables appearing in an if-expressions,
read left to right, without removing duplicates.
-/
def vars : IfExpr → List Nat
  | lit _ => []
  | var i => [i]
  | ite i t e => i.vars ++ t.vars ++ e.vars

/--
A helper function to specify that two lists are disjoint.
-/
def _root_.List.disjoint {α} [DecidableEq α] :
    List α → List α → Bool
  | [], _ => true
  | x::xs, ys => x ∉ ys && xs.disjoint ys

/--
An if expression evaluates each variable at most once if
for each if-then-else the variables in the "if" clause
are disjoint from the variables in the "then" clause
and the variables in the "if" clause
are disjoint from the variables in the "else" clause.
-/
def disjoint : IfExpr → Bool
  | lit _ => true
  | var _ => true
  | ite i t e =>
      i.vars.disjoint t.vars && i.vars.disjoint e.vars &&
        i.disjoint && t.disjoint && e.disjoint

/--
An if expression is "normalized" if it has
no nested, constant, or redundant ifs,
and it evaluates each variable at most once.
-/
def normalized (e : IfExpr) : Bool :=
  !e.hasNestedIf && !e.hasConstantIf &&
    !e.hasRedundantIf && e.disjoint

/--
The evaluation of an if expression
at some assignment of variables.
-/
def eval (f : Nat → Bool) : IfExpr → Bool
  | lit b => b
  | var i => f i
  | ite i t e => bif i.eval f then t.eval f else e.eval f

end IfExpr
```
:::

使用这些我们可以陈述问题。面临的挑战是适应以下类型（并且做得很好！）：

```lean
def IfNormalization : Type :=
  { Z : IfExpr → IfExpr // ∀ e, (Z e).normalized ∧ (Z e).eval = e.eval }
```

# 其他解决方案
%%%
tag := "zh-grind-extendedexamples-ifelsenorm-h003"
%%%

此时，值得暂停并至少执行以下操作之一：

:::comment
TODO (@david-christiansen)：我们在此处包含一个指向 live-lean 和外部托管代码块的链接。没有办法保持同步。 :-(
:::

* 尝试自己证明这一点！对于初学者来说是相当有挑战性的！
  你可以[试试](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fgist.githubusercontent.com%2Fkim-em%2Ff416b31fe29de8a3f1b2b3a84e0f1793%2Fraw%2F75ca61230b50c126f8658bacd933ecf7bfcaa4b8%2Fgrind_ite.lean)
  在 Live Lean 编辑器中，无需任何安装。
* 阅读 Chris Hughes 的[解决方案](https://github.com/leanprover-community/mathlib4/blob/master/Archive/Examples/IfNormalization/Result.lean)，
  它包含在 Mathlib 存档中。
  该解决方案很好地利用了 Aesop，但并不理想，因为
  1. 它使用子类型定义解决方案，同时给出其构造并证明其属性。
     我们认为在风格上最好将它们分开。
  2. 即使使用 Aesop 自动化，在我们将其交给 Aesop 之前，仍然需要大约 15 行手动打样工作。
* 阅读 Wojciech Nawrocki 的[解决方案](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Rustan's.20challenge/near/398824748)。
  这一过程使用的自动化程度较低，校样工作量约为 300 行。

# 使用{tactic}`grind`的解决方案
%%%
tag := "zh-grind-extendedexamples-ifelsenorm-h004"
%%%

其实解决这个问题并不难：
我们只需要一个递归函数来携带“已分配的变量”的记录，
然后，每当对变量执行分支时，在每个分支中添加新的赋值。
它还需要展平嵌套的 if-then-else 表达式，这些表达式在“条件”位置有另一个 if-then-else。
（这是从 Chris Hughes 的解决方案中提取的，但没有子类型。）

让我们在 `IfExpr` 命名空间内工作。
```lean
namespace IfExpr
```

:::keepEnv

```lean +error (name := failed_to_show_termination)
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)

```

这非常简单，但它立即遇到了一个问题：

```leanOutput failed_to_show_termination (stopAt := "Could not find a decreasing measure.")
fail to show termination for
  IfExpr.normalize
with errors
failed to infer structural recursion:
Cannot use parameter assign:
  the type HashMap Nat Bool does not have a `.brecOn` recursor
Cannot use parameter #2:
  failed to eliminate recursive application
    normalize assign (a.ite (b.ite t e) (c.ite t e))


Could not find a decreasing measure.
```


Lean 这里告诉我们它看不到该函数正在终止。
通常，Lean 非常擅长自行解决此问题，但对于足够复杂的函数
我们需要介入并给予提示。

在这种情况下我们可以看到这是递归调用
`ite (ite a b c) t e` 正在 `(ite a (ite b t e) (ite c t e))` 上调用 {lean}`normalize`
Lean 遇到困难。 Lean 已对合理的终止措施进行了猜测，
基于使用自动生成的 {name}`sizeOf` 函数，但无法证明最终的目标，
本质上是因为 `t` 和 `e` 在递归调用中多次出现。
:::

为了解决这样的问题，我们几乎总是想停止使用自动生成的 `sizeOf` 函数，
并构建我们自己的终止措施。我们将使用

```lean
@[simp] def normSize : IfExpr → Nat
  | lit _ => 0
  | var _ => 1
  | .ite i t e => 2 * normSize i + max (normSize t) (normSize e) + 1
```


许多不同的功能都可以在这里工作。基本思想是增加“condition”分支的“权重”
（这是 `2 * normSize i` 中的乘法因子），
因此，只要“condition”部分收缩一点，即使“then”和“else”分支增长，整个表达式也会被视为收缩。
我们用 {attrs}`@[simp]` 注释了该定义，因此允许 Lean 的自动终止检查器展开该定义。

完成此操作后，将使用 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句进行定义：

:::keepEnv
```lean
def normalize (assign : Std.HashMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize
```

现在是时候证明这个函数的一些属性了。
我们只需将我们想要的所有属性打包在一起：

```lean -keep
theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign :=
  sorry
```

即：
* {lean}`normalize` 的结果实际上是根据初始定义进行归一化的，
* 如果我们使用一些赋值规范化“if-then-else”表达式，然后评估剩余的变量，
  我们得到与使用两个赋值的组合评估原始“if-then-else”相同的结果，
* 并且赋值中出现的任何变量都不再出现在规范化表达式中。

您可能认为我们应该将这三个属性表述为单独的引理，
但事实证明一次证明它们真的很方便，因为我们可以使用 {tactic}`fun_induction`
策略假设所有这些属性在递归调用中适用于 {lean}`normalize`，然后
{tactic}`grind` 会将所有事实放在一起得出结果：

```lean
-- We tell `grind` to unfold our definitions above.
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint

theorem normalize_spec
    (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```

{tactic}`fun_induction` 和 {tactic}`grind` 组合在这里工作的事实有点令人惊讶。
我们对此感到非常兴奋，我们希望看到更多这种风格的证明！

高度自动化证明的一个可爱的结果是，您通常可以灵活地更改语句，
根本不改变证明！作为例子，我们上面断言的特定方式
“赋值中出现的任何变量不再出现在规范化表达式中”
可以用许多不同的方式来表述（尽管没有省略！）。变化其实并不重要，
和 {tactic}`grind` 都可以证明和使用其中的任何一个：

这里我们使用`assign.contains v = false`：
```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat), v ∈ vars (normalize assign e) →
          assign.contains v = false := by
  fun_induction normalize with grind
```

这里我们使用 `assign[v]? = none`：

```lean
example (assign : Std.HashMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → assign[v]? = none := by
  fun_induction normalize with grind
```

事实上，我们是否使用 `grind` 也没有什么影响
{name}`HashMap` 或 {name}`TreeMap` 用于存储分配，
我们可以简单地切换该实现细节，而无需触及证明：

:::


```lean -show
-- We have to repeat these annotations because we've rolled back the environment to before we defined `normalize`.
attribute [local grind]
  normalized hasNestedIf hasConstantIf hasRedundantIf
  disjoint vars eval List.disjoint
```
```lean
def normalize (assign : Std.TreeMap Nat Bool) :
    IfExpr → IfExpr
  | lit b => lit b
  | var v =>
    match assign[v]? with
    | none => var v
    | some b => lit b
  | ite (lit true)  t _ => normalize assign t
  | ite (lit false) _ e => normalize assign e
  | ite (ite a b c) t e =>
    normalize assign (ite a (ite b t e) (ite c t e))
  | ite (var v)     t e =>
    match assign[v]? with
    | none =>
      let t' := normalize (assign.insert v true) t
      let e' := normalize (assign.insert v false) e
      if t' = e' then t' else ite (var v) t' e'
    | some b => normalize assign (ite (lit b) t e)
termination_by e => e.normSize

theorem normalize_spec
    (assign : Std.TreeMap Nat Bool) (e : IfExpr) :
    (normalize assign e).normalized
      ∧ (∀ f, (normalize assign e).eval f =
          e.eval fun w => assign[w]?.getD (f w))
      ∧ ∀ (v : Nat),
          v ∈ vars (normalize assign e) → ¬ v ∈ assign := by
  fun_induction normalize with grind
```

（我们能够做到这一点的事实依赖于这样一个事实：{tactic}`grind` 所需的 {name}`HashMap` 和 {name}`TreeMap` 的所有引理都已在标准库中进行了注释。）

如果您想尝试一下这段代码，
您可以在[此处](https://github.com/leanprover/lean4/blob/master/tests/lean/run/grind_ite.lean)找到整个文件，
或者事实上[无需安装即可使用](https://live.lean-lang.org/#project=lean-nightly&url=https%3A%2F%2Fraw.githubusercontent.com%2Fleanprover%2Flean4%2Frefs%2Fheads%2Fmaster%2Ftests%2Flean%2Frun%2Fgrind_ite.lean)
在实时 Lean 编辑器中。

```lean -show
end IfExpr
```
