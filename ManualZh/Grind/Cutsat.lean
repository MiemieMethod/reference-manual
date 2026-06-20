/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)
open Verso.Code.External (lit)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "线性整数算术" =>
%%%
tag := "cutsat"
%%%

:::paragraph
线性整数算术求解器实现了基于模型的线性整数算术决策过程。
求解器可以处理四类线性多项式约束（其中 `p` 是 [线性多项式](https://en.wikipedia.org/wiki/Degree_of_a_polynomial)）：

: 平等

 `p = 0`

: 整除性

 `d ∣ p`

: 不等式

  `p ≤ 0`

: 不平等

  `p ≠ 0`

它对于线性整数运算来说是完整的，并且通过使用{name}`Int.ofNat`将它们转换为整数来支持自然数。
可以通过 {name}`Lean.Grind.ToInt` 的实例添加对可嵌入到 {lean}`Int` 中的其他类型的支持。
允许使用非线性项（例如 `x * x`），并表示为变量。
该求解器还能够将信息传播回隐喻的 {tactic}`grind` 白板，这可以触发其他子系统的进一步进展。
默认情况下是启用的；可以使用标志 {lit}`-lia` 禁用它
:::



::::example "Examples of Linear Integer Arithmetic" (open := true)

所有这些陈述都可以使用线性整数算术求解器来证明。
在第一个示例中，左侧必须是 2 的倍数，因此不能是 5：
```lean
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  grind
```

求解器支持混合等式和不等式：
```lean
example {x y : Int} :
    2 * x + 3 * y = 0 →
    1 ≤ x →
    y < 1 := by
  grind
```

它还支持线性整除约束：
```lean
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind
```


如果没有 `lia`，{tactic}`grind` 无法证明以下陈述：

```lean +error (name := noLia)
example (a b : Int) :
    2 ∣ a + 1 →
    2 ∣ b + a →
    ¬ 2 ∣ b + 2 * a := by
  grind -lia
```
```leanOutput noLia
`grind` failed
case grind
a b : Int
h : 2 ∣ a + 1
h_1 : 2 ∣ a + b
h_2 : 2 ∣ 2 * a + b
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [ematch] E-matching patterns
  [linarith] Linarith assignment for `Int`
```
::::

# 理性解决方案
%%%
tag := "cutsat-qlia"
%%%

该求解器对于线性整数运算来说是完整的。
然而，搜索可能会在约束很少的情况下变得巨大，但求解器并不是为执行大规模案例分析而设计的。
{tactic}`grind` 的 `qlia` 选项通过指示求解器接受有理解来减少搜索空间。
使用此选项，求解器可能会更快，但它并不完整。

:::example "Rational Solutions"
以下示例有有理解，但没有整数解：
```lean
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind
```

因为它使用有理解，所以当指定 `+qlia` 时，{tactic}`grind` 无法反驳目标的否定：
```lean +error (name := withqlia)
example {x y : Int} :
    27 ≤ 13 * x + 11 * y →
    13 * x + 11 * y ≤ 30 →
    -10 ≤ 9 * x - 7 * y →
    9 * x - 7 * y > 4 := by
  grind +qlia
```
```leanOutput withqlia (expandTrace := cutsat)
`grind` failed
case grind
x y : Int
h : -13 * x + -11 * y + 27 ≤ 0
h_1 : 13 * x + 11 * y + -30 ≤ 0
h_2 : -9 * x + 7 * y + -10 ≤ 0
h_3 : 9 * x + -7 * y + -4 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 62/117
    [assign] y := 2
```

求解器构建的有理模型位于目标诊断中的 `Assignment satisfying linear constraints` 部分。
:::

# 非线性约束
%%%
tag := "zh-grind-cutsat-h002"
%%%

该求解器目前支持非线性约束，并将诸如 `x * x` 之类的非线性项视为变量。

::::example "Nonlinear Terms" (open := true)
线性整数算术求解器无法证明这个定理：

```lean +error (name := nonlinear)
example (x : Int) : x * x ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
```

从线性整数算术求解器的角度来看，它相当于：

```lean +error (name := nonlinear2)
example {y : Int} (x : Int) : y ≥ 0 := by
  grind
```
```leanOutput nonlinear
`grind` failed
case grind
x : Int
h : x * x + 1 ≤ 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
```

:::paragraph
这可以通过将选项 {option}`trace.grind.lia.assert` 设置为 {lean}`true` 来看到，该选项跟踪求解器处理的所有约束。

```lean +error (name := liaDiag)
example (x : Int) : x*x ≥ 0 := by
  set_option trace.grind.lia.assert true in
  grind
```
```leanOutput liaDiag
[grind.lia.assert] -1*「x ^ 2 + 1」 + 「x ^ 2」 + 1 = 0
[grind.lia.assert] 「x ^ 2」 + 1 ≤ 0
```
术语 `x ^ 2` 在 `「x ^ 2」 + 1 ≤ 0` 中被“引用”，以指示 `x ^ 2` 被视为变量。
:::
::::

# 除法和模数
%%%
tag := "zh-grind-cutsat-h003"
%%%

该求解器支持线性除法和模运算。

:::example "Linear Division and Modulo"
```lean
example (x y : Int) :
    x = y / 2 →
    y % 2 = 0 →
    y - 2 * x = 0 := by
  grind
```
:::

# 代数处理
%%%
tag := "zh-grind-cutsat-h004"
%%%

求解器规范交换（半）环表达式。

:::example "Commutative (Semi)ring Normalization"
交换环归一化可以解决这个目标：
```lean
example (a b : Nat)
    (h₁ : a + 1 ≠ a * b * a)
    (h₂ : a * a * b ≤ a + 1) :
    b * a ^ 2 < a + 1 := by
  grind
```
:::

# 传播信息
%%%
tag := "cutsat-mbtc"
%%%

该求解器还实现了 {deftech (key := "model-based theory combination")}_基于模型的理论组合_，这是一种将等式传播回隐喻共享白板的机制。
这些额外的等式反过来可能会引发新的同余。
基于模型的理论组合增加了搜索空间的大小；可以使用选项 `grind -mbtc` 禁用它。

::::example "Propagating Equalities"
在上面的例子中，线性不等式和不等式意味着 `y = 0`：
```lean
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind
```
因此 `x = x + y`，因此 `f x = f (x + y)` 由 {tech (key := "congruence closure")}[同余]。
如果没有基于模型的理论组合，证明就会陷入困境：
```lean +error (name := noMbtc)
example (f : Int → Int) (x y : Int) :
    f x = 0 →
    0 ≤ y → y ≤ 1 → y ≠ 1 →
    f (x + y) = 0 := by
  grind -mbtc
```
```leanOutput noMbtc
`grind` failed
case grind
f : Int → Int
x y : Int
h : f x = 0
h_1 : -1 * y ≤ 0
h_2 : y + -1 ≤ 0
h_3 : ¬y = 1
h_4 : ¬f (x + y) = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Int`
```
::::

# 其他类型
%%%
tag := "cutsat-ToInt"
%%%

LIA 求解器还可以处理包含自然数的线性约束。
它使用 `Int.ofNat` 将它们转换为整数约束。

:::example "Natural Numbers as Linear Integer Arithmetic"
```lean
example (x y z : Nat) :
    x < y + z →
    y + 1 < z →
    z + x < 3 * z := by
  grind
```
:::

有一个可扩展的机制，通过 {lean}`Lean.Grind.ToInt` 类型类来告诉求解器，类型嵌入在整数中。
使用它，我们可以解决诸如以下的目标：

```lean
example (a b c : Fin 11) : a ≤ 2 → b ≤ 3 → c = a + b → c ≤ 5 := by
  grind

example (a : Fin 2) : a ≠ 0 → a ≠ 1 → False := by
  grind

example (a b c : UInt64) : a ≤ 2 → b ≤ 3 → c - a - b = 0 → c ≤ 5 := by
  grind
```

{docstring Lean.Grind.ToInt}

{docstring Lean.Grind.IntInterval}

# 实施说明
%%%
tag := "zh-grind-cutsat-h007"
%%%

::::leanSection
```lean -show
variable {x y : Int}
```

:::paragraph
线性整数算术求解器的实现受到 {citet cuttingToTheChase}[] 第 4 节的启发。
与论文相比，它包括一些增强和修改，例如：

* 扩展约束支持（平等和不平等），

* 使用“大”析取而不是新变量对 `Cooper-Left` 规则进行优化编码，以及

* 用于案例分割的决策变量跟踪（不等式、`Cooper-Left`、`Cooper-Right`）。
:::

:::paragraph
求解器过程逐步构建模型（即项中变量的分配），通过约束生成解决冲突。
例如，给定部分模型 `{x := 1}` and constraint {lean}`3 ∣ 3 * y + x + 1`：

- 求解器无法将模型扩展到 {lean}`y`，因为 {lean}`3 ∣ 3 * y + 2` 不可满足。

- 因此，它通过生成隐含约束 {lean}`3 ∣ x + 1` 来解决冲突。

- 新约束迫使求解器为 {lean}`x` 找到新的分配。
:::


:::paragraph
当分配变量 `y` 时，求解器考虑：

- 最佳上限和下限（不等式）。

- 可分性约束。

- 所有不等式约束，其中 `y` 是最大变量。
:::
::::

`Cooper-Left` 和 `Cooper-Right` 规则处理不等式和整除性的组合。
对于不可满足的不等式 `p ≠ 0`，求解器生成案例分割：`p + 1 ≤ 0 ∨ -p + 1 ≤ 0`。


:::comment
计划的未来功能：改进约束传播。
:::
