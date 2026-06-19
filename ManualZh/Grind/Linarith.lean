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

-- Due to Lean.Grind.Semiring.nsmul_eq_natCast_mul
set_option verso.docstring.allowMissing true

open Lean.Grind

#doc (Manual) "线性算术工作站" =>
%%%
tag := "grind-linarith"
%%%

{tactic}`grind`策略包括一个用于任意类型的线性算术求解器，称为 `linarith`，用于 {ref "cutsat"}`cutsat` 不支持的类型。
与 {ref "grind-ring"}`ring` 求解器一样，它可用于具有某些类型类实例的任何类型。
它根据这些类型类的可用性进行自我配置，因此无需提供所有类型类即可使用求解器；然而，它的功能随着更多实例的可用性而增强。
该求解器对于推理实数、有序向量空间以及无法嵌入到 {name}`Int` 中的其他类型非常有用。


`linarith` 的核心功能是基于模型的整数系数线性不等式求解器。
可以使用选项 `grind -linarith` 禁用它。


:::example "Goals Decided by `linarith`" (open := true)
```imports -show
import Std
```
```lean -show
open Lean.Grind
```
所有这些示例都依赖于以下排序符号和 `linarith` 类的实例：
```lean
variable [LE α] [LT α] [Std.LawfulOrderLT α]  [Std.IsLinearOrder α]
variable [IntModule α] [OrderedAdd α]
```

整数模块 ({name}`IntModule`) 是具有零、加法、求反、减法和整数标量乘法的类型，满足这些运算的预期属性。
线性阶 ({name}`Std.IsLinearOrder`) 是任何元素对都有序的阶，{name}`OrderedAdd` 指出向两侧添加常数可以保留排序。

```lean
example {a b : α} : 2 • a + b ≥ b + a + a := by grind

example {a b : α} (h : a ≤ b) : 3 • a + b ≤ 4 • b := by grind

example {a b c : α} :
    a = b + c →
    2 • b ≤ c →
    2 • a ≤ 3 • c := by
  grind

example {a b c d e : α} :
    2 • a + b ≥ 0 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0 →
    a ≥ 3 • c → c ≥ 6 • e → d - 5 • e ≥ 0 →
    a + b + 3 • c + d + 2 • e < 0 →
    False := by
  grind
```
:::

:::example "Commutative Ring Goals Decided by `linarith`" (open := true)
```imports -show
import Std
```
```lean -show
open Lean.Grind
```
对于具有 {name}`CommRing` 实例的交换环类型（即乘法运算符可交换的类型），`linarith` 具有更多功能。

```lean
variable [LE R] [LT R] [Std.IsLinearOrder R] [Std.LawfulOrderLT R]
variable [CommRing R] [OrderedRing R]
```

{inst}`CommRing R` 实例允许 `linarith` 执行基本归一化，例如识别线性原子 `a * b` 和 `b * a`，并考虑两侧的标量乘法。
{inst}`OrderedRing R` 实例允许求解器支持常量，因为它可以访问 {lean}`(0 : R) < 1`.

```lean
example (a b : R) (h : a * b ≤ 1) : b * 3 • a + 1 ≤ 4 := by grind

example (a b c d e f : R) :
    2 • a + b ≥ 1 →
    b ≥ 0 → c ≥ 0 → d ≥ 0 → e • f ≥ 0 →
    a ≥ 3 • c →
    c ≥ 6 • e • f → d - f * e * 5 ≥ 0 →
    a + b + 3 • c + d + 2 • e • f < 0 →
    False := by
  grind
```
:::

:::TODO
计划的未来功能
* 支持 `NatModule`（通过嵌入 Grothendieck 包络线，就像我们已经对半环所做的那样），
* `ring` 和 `linarith` 求解器之间更好的通信。
  目前这两个求解器之间的通信很少。
* 有序环上的非线性算术。
:::

# 支持`linarith`
%%%
tag := "grind-linarith-classes"
%%%

要向 `linarith` 添加对新类型的支持，第一步是在可能的情况下实现 {name}`IntModule`，否则实现 {name}`NatModule`。
每个 {name}`Ring` 都已经是 {name}`IntModule`，并且每个 {name}`Semiring` 都已经是 {name}`NatModule`，因此实现这些实例之一也足够了。
接下来，应实现订单类之一（{name}`Std.IsPreorder`、{name}`Std.IsPartialOrder` 或 {name}`Std.IsLinearOrder`）。
通常，当上下文已包含矛盾时，{name Std.IsPreorder}`IsPreorder` 实例就足够了，但需要 {name Std.IsLinearOrder}`IsLinearOrder` 实例才能证明线性不等式目标。
通过实现 {name}`OrderedAdd` 和 {name}`OrderedRing` 来启用其他功能，{name}`OrderedAdd` 表示模块中的加法结构与阶数兼容，{name}`OrderedRing` 改进了对常量的支持。


{docstring Lean.Grind.NatModule}

{docstring Lean.Grind.IntModule}

{docstring Lean.Grind.OrderedAdd}

{docstring Lean.Grind.OrderedRing}
