/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "使用 {tactic}`conv` 进行有针对性的重写" =>
%%%
tag := "conv"
%%%

{tactic}`conv` 或转换策略允许在目标内进行有针对性的重写。
{tactic}`conv` 的参数是用与主要策略语言互操作的单独语言编写的；它具有导航到目标内特定子项的命令以及允许重写这些子项的命令。
当重写仅应用于目标的一部分（例如仅应用于等式的一侧）而不是全面应用时，或者当重写应用于阻止策略（如 {tactic}`rw`）访问该术语的活页夹下方时，{tactic}`conv` 非常有用。

转换策略语言与主要策略语言非常相似：它使用相同的证明状态，策略主要针对主要目标工作，并且可能会失败或成功执行一系列新目标，并且宏展开与策略交错执行。
与主要的策略语言（其中策略旨在最终解决目标）不同，{tactic}`conv`策略用于_更改_目标，以便它能够在主要的策略语言中进行进一步处理。
打算用 {tactic}`conv` 重写的目标用垂直条而不是十字转门显示。

:::tactic "conv"
:::

::::example "Navigation and Rewriting with {tactic}`conv`"

在此示例中，有多个加法实例，{tactic}`rw` 默认情况下会重写它遇到的第一个实例。
在重写之前使用 {tactic}`conv` 导航到特定子术语使 {tactic}`rw` 别无选择，只能重写正确的术语。

```lean
example (x y z : Nat) : x + (y + z) = (x + z) + y := by
  conv =>
    lhs
    arg 2
    rw [Nat.add_comm]
  rw [Nat.add_assoc]
```

::::

::::example "Rewriting Under Binders with {tactic}`conv`"

在此示例中，加法发生在活页夹下，因此无法使用 {tactic}`rw`。
然而，使用{tactic}`conv`导航到函数体后，就成功了。
{tactic}`conv` 的嵌套使用会导致在对其子项之一执行进一步转换后控制返回到项中的当前位置。
由于目标是重写后的自反方程，因此 {tactic}`conv` 自动将其关闭。

```lean
example :
    (fun (x y z : Nat) =>
      x + (y + z))
    =
    (fun x y z =>
      (z + x) + y)
  := by
  conv =>
    lhs
    intro x y z
    conv =>
      arg 2
      rw [Nat.add_comm]
    rw [← Nat.add_assoc]
    arg 1
    rw [Nat.add_comm]
```

::::

# 控制结构
%%%
tag := "conv-control"
%%%


:::conv first (show := "first")
:::

:::conv convTry_ (show := "try")
:::

:::conv «conv_<;>_» (show:="<;>") +allowMissing
:::

:::conv convRepeat_ (show := "repeat")
:::

:::conv skip (show := "skip")
:::

:::conv nestedConv (show := "{ ... }")
:::

:::conv paren (show := "( ... )")
:::

:::conv convDone (show := "done")
:::

# 目标选择
%%%
tag := "conv-goals"
%%%


:::conv allGoals (show := "all_goals")
:::

:::conv anyGoals (show := "any_goals")
:::

:::conv case (show := "case ... => ...")
:::

:::conv case' (show := "case' ... => ...")
:::

:::conv «convNext__=>_» (show := "next ... => ...")
:::

:::conv focus (show := "focus")
:::

:::conv «conv·_» (show := "· ...")
:::


:::conv failIfSuccess (show := "fail_if_success")
:::


# 导航
%%%
tag := "conv-nav"
%%%


:::conv lhs (show := "lhs")
:::

:::conv rhs (show := "rhs")
:::

:::conv fun (show := "fun")
:::

:::conv congr (show := "congr")
:::

:::conv arg (show := "arg [@]i")
:::

:::syntax Lean.Parser.Tactic.Conv.enterArg (title := "Arguments to {keyword}`enter`")
```grammar
$i:num
```
```grammar
@$i:num
```
```grammar
$x:ident
```
:::

:::conv enter (show := "enter")
:::


:::conv pattern (show := "pattern")
:::

:::conv ext (show := "ext")
:::

:::conv convArgs (show := "args")
:::

:::conv convLeft (show := "left")
:::

:::conv convRight (show := "right")
:::

:::conv convIntro___ (show := "intro")
:::

# 改变目标
%%%
tag := "conv-change"
%%%

## 减少
%%%
tag := "conv-reduction"
%%%

:::conv cbv (show := "cbv")
:::

:::example "The `cbv` Tactic"
{conv}`cbv`策略可用于约简函数，包括通过 {ref "well-founded-recursion"}[良基递归] 定义的函数，否则这些函数是不可约的。
通常，{name}`f` 仅在命题上等于其展开，因此 {tactic}`rfl` 无法证明等式 {lean}`f 5 = 5`：
```lean
def f (n : Nat) :=
  match n with
  | 0 => 0
  | n + 1 => f n + 1
termination_by (n,0)
```
```lean +error (name := nonEq)
example : f 5 = 5 := by rfl
```
```leanOutput nonEq
Tactic `rfl` failed: The left-hand side
  f 5
is not definitionally equal to the right-hand side
  5

⊢ f 5 = 5
```
在等式左侧使用 {conv}`cbv`，可以使该语句成立：
```lean -show
-- The `cbv` tactic is presently experimental, and a warning is issued when it is used.
-- This option disables the warning:
set_option cbv.warning false
```
```lean
example : f 5 = 5 := by
  conv =>
    lhs
    cbv
```
:::

:::conv whnf (show := "whnf")
:::

:::conv reduce (show := "reduce")
:::

:::conv zeta (show := "zeta")
:::

:::conv delta (show := "delta")
:::

:::conv unfold (show := "unfold")
:::

## 简化
%%%
tag := "conv-simp"
%%%

:::conv simp (show := "simp")
:::

:::conv dsimp (show := "dsimp")
:::

:::conv simpMatch (show := "simp_match")
:::

## 重写
%%%
tag := "conv-rw"
%%%

:::conv change (show := "change")
:::

:::conv rewrite (show := "rewrite")
:::

:::conv convRw__ (show := "rw")
:::

:::conv convErw__ (show := "erw")
:::

:::conv convApply_ (show := "apply")
:::

# 嵌套策略
%%%
tag := "conv-nested"
%%%


:::tactic Lean.Parser.Tactic.Conv.convTactic
:::

:::conv nestedTactic (show := "tactic")
:::

:::conv nestedTacticCore (show := "tactic'")
:::

:::tactic Lean.Parser.Tactic.Conv.convTactic (show := "conv'")
:::

:::conv convConvSeq (show := "conv => ...")
:::


# 调试实用程序
%%%
tag := "conv-debug"
%%%

:::conv convTrace_state (show := "trace_state")
:::


# 其他
%%%
tag := "conv-other"
%%%

:::conv convRfl (show := "rfl")
:::

:::conv normCast (show := "norm_cast")
:::
