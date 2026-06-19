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
set_option maxHeartbeats 300000

#doc (Manual) "代数工作室（交换环、域）" =>
%%%
tag := "grind-ring"
%%%

{tactic}`grind` 中的 `ring` 求解器受到 Gröbner 基础计算过程和术语重写完成的启发。
它将多元多项式视为重写规则。
例如，多项式等式`x * y + x - 2 = 0`被视为重写规则`x * y ↦ -x + 2`。
它使用叠加来确保重写系统是汇合的。

以下示例演示了可由 `ring` 求解器决定的目标。
在这些示例中，`Lean` 和 `Lean.Grind` 命名空间处于打开状态：
```lean
open Lean Grind
```

:::example "Commutative Rings" (open := true)
```lean -show
open Lean.Grind
```
```lean
example [CommRing α] (x : α) : (x + 1) * (x - 1) = x ^ 2 - 1 := by
  grind
```
:::
:::example "Ring Characteristics" (open := true)
求解器“知道”`16*16 = 0`，因为[环特征](https://en.wikipedia.org/wiki/Characteristic_%28algebra%29)（即，乘法恒等式与加法恒等式之和的最小副本数）是 `256`，它由 {name}`IsCharP` 实例提供。

```lean -show
open Lean.Grind
```
```lean
example [CommRing α] [IsCharP α 256] (x : α) :
    (x + 16)*(x - 16) = x^2 := by
  grind
```
:::

:::example "Standard Library Types" (open := true)
```lean -show
open Lean.Grind
```
解算器开箱即用地支持标准库中的类型。
`UInt8` 是具有特征 `256` 的交换环，因此具有 {inst}`CommRing UInt8` 和 {inst}`IsCharP UInt8 256` 的实例。
```lean
example (x : UInt8) : (x + 16) * (x - 16) = x ^ 2 := by
  grind
```
:::

:::example "More Commutative Ring Proofs" (open := true)
```lean -show
open Lean.Grind
```
交换环的公理足以证明这些陈述。

```lean
example [CommRing α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```

```lean
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
:::

:::example "Characteristic Zero" (open := true)
```lean -show
open Lean.Grind
```
`ring` 证明 `a + 1 = 2 + a` 不可满足，因为已知特性为 0。

```lean
example [CommRing α] [IsCharP α 0] (a : α) :
    a + 1 = 2 + a → False := by
  grind
```
:::

:::example "Inferred Characteristic" (open := true)
```lean -show
open Lean.Grind
```
即使最初不知道该特征，当 `grind` 发现 `n = 0` 对于某些数字 `n` 时，它也会对该特征做出推断：
```lean
example [CommRing α] (a b c : α)
    (h₁ : a + 6 = a) (h₂ : c = c + 9) (h : b + 3*c = 0) :
    27*a + b = 0 := by
  grind
```
:::

# 解算器 Type 类
%%%
tag := "grind-ring-classes"
%%%

:::paragraph
用户可以通过提供以下 {tech (key := "type class")}[类型类] 的实例（全部位于 `Lean.Grind` 命名空间中）来为自己的类型启用 `ring` 求解器：

* {name Lean.Grind.Semiring}`Semiring`

* {name Lean.Grind.Ring}`Ring`

* {name Lean.Grind.CommSemiring}`CommSemiring`

* {name Lean.Grind.CommRing}`CommRing`

* {name Lean.Grind.IsCharP}`IsCharP`

* {name Lean.Grind.AddRightCancel}`AddRightCancel`

* {name Lean.Grind.NoNatZeroDivisors}`NoNatZeroDivisors`

* {name Lean.Grind.Field}`Field`


代数求解器将根据这些实例的可用性进行自我配置，因此不需要提供所有实例。
当然，当某些代数求解器不可用时，代数求解器的功能将会降低。
:::

Lean 标准库包含标准库中定义的类型的适用实例。
通过提供这些实例，其他库也可以启用 {tactic}`grind` 的 `ring` 求解器。
例如，Mathlib `CommRing` 类型类实现 `Lean.Grind.CommRing` 以确保 `ring` 解算器开箱即用。

## 代数结构

为了启用代数求解器，类型应该具有求解器支持的最具体的可能代数结构的实例。
按照特异性递增的顺序，即 {name Lean.Grind.Semiring}`Semiring`、{name Lean.Grind.Ring}`Ring`、{name Lean.Grind.CommSemiring}`CommSemiring`、{name Lean.Grind.CommRing}`CommRing` 和 {name Lean.Grind.Field}`Field`。

{docstring Lean.Grind.Semiring}

{docstring Lean.Grind.CommSemiring}

{docstring Lean.Grind.Ring}

{docstring Lean.Grind.CommRing}

### 领域
%%%
tag := "grind-ring-field"
%%%

:::leanSection
```lean -show
variable {a b p : α} [Field α]
```
`ring` 解算器还支持 {name}`Field`。
如果 {name}`Field` 实例可用，则求解器会将项 `a / b` 预处理为 `a * b⁻¹`。
它还将每个不等式 `p ≠ 0` 重写为等式 `p * p⁻¹ = 1`。
:::

::::example "Fields and `grind`"
```lean -show
open Lean.Grind
```
此示例需要其 {name}`Field` 实例：

```lean
example [Field α] (a : α) :
    a ^ 2 = 0 →
    a = 0 := by
  grind
```
::::

{docstring Lean.Grind.Field}

## 环特性

:::TODO

写

:::

{docstring Lean.Grind.IsCharP}


## 自然数零因数
%%%
tag := "NoNatZeroDivisors"
%%%


`NoNatZeroDivisors` 类用于控制系数增长。
例如，多项式 `2 * x * y + 4 * z = 0` 被简化为 `x * y + 2 * z = 0`。
在处理不平等时也使用它。

:::example "Using `NoNatZeroDivisors`"
```lean -show
open Lean.Grind
```
在此示例中，{tactic}`grind` 依赖 {name}`NoNatZeroDivisors` 实例来简化目标：
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
没有它，证明就会失败：
```lean (name := NoNatZero) +error
example [CommRing α] (a b : α) :
    2 * a + 2 * b = 0 →
    b ≠ -a → False := by
  grind
```
```leanOutput NoNatZero
`grind` failed
case grind
α : Type u_1
inst : CommRing α
a b : α
h : 2 * a + 2 * b = 0
h_1 : ¬b = -a
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [ring] Ring `α`
```
:::

{docstring Lean.Grind.NoNatZeroDivisors}

{docstring Lean.Grind.NoNatZeroDivisors.mk'}

`ring` 模块还针对 `a` 是否为零执行项 `a⁻¹` 的案例分析。
在以下示例中，如果 `2*a` 为零，则 `a` 也为零，因为
我们有 `NoNatZeroDivisors α`，所有项都为零并且等式成立。否则，
`ring` 将等式 `a*a⁻¹ = 1` 和 `2*a*(2*a)⁻¹ = 1` 相加，并关闭目标。

```lean
example [Field α] [NoNatZeroDivisors α] (a : α) :
    1 / a + 1 / (2 * a) = 3 / (2 * a) := by
  grind
```

如果没有 `NoNatZeroDivisors`，`grind` 将根据需要对为零的数字执行大小写分割：
```lean
example [Field α] (a : α) : (2 * a)⁻¹ = a⁻¹ / 2 := by grind
```

在以下示例中，`ring` 不需要执行任何大小写拆分，因为
目标包含不等式 `y ≠ 0` 和 `w ≠ 0`。

```lean
example [Field α] {x y z w : α} :
    x / y = z / w →
    y ≠ 0 → w ≠ 0 →
    x * w = z * y := by
  grind (splits := 0)
```

您可以使用选项 `grind -ring` 禁用 `ring` 解算器。

```lean +error (name := noRing)
example [CommRing α] (x y : α) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind -ring
```
```leanOutput noRing
`grind` failed
case grind
α : Type u_1
inst : CommRing α
x y : α
h : x ^ 2 * y = 1
h_1 : x * y ^ 2 = y
h_2 : ¬y * x = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [linarith] Linarith assignment for `α`
```

### 右抵消加法
%%%
tag := "AddRightCancel"
%%%

`ring` 解算器自动将 `CommSemiring` 嵌入到 `CommRing` 包络中（使用构造 `Lean.Grind.Ring.OfSemiring.Q`）。
但是，仅当 `CommSemiring` 实现类型类 `AddRightCancel` 时，嵌入才是单射的。
`Nat` 是实现 `AddRightCancel` 的交换半环的示例。

```lean
example (x y : Nat) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```

{docstring Lean.Grind.AddRightCancel}

# 资源限制

Gröbner 基础计算可能非常昂贵。您可以使用选项 `grind (ringSteps := <num>)` 限制 `ring` 求解器执行的步数

:::example "Limiting `ring` Steps"
```lean -show
open Lean.Grind
```
此示例无法通过最多执行 100 个步骤来解决：
```lean +error (name := ring100)
example [CommRing α] [IsCharP α 0] (d t c : α) (d_inv PSO3_inv : α) :
    d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0 →
    -d ^ 4 * (d + t - d * t - 2) *
      (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t^4 +
      2 * d^2 * t^4 - c * (d + t + d * t)) = 0 →
    d * d_inv = 1 →
    (d + t - d * t - 2) * PSO3_inv = 1 →
    t^2 = t + 1 := by
  grind (ringSteps := 100)
```
```leanOutput ring100
`grind` failed
case grind
α : Type u_1
inst : CommRing α
inst_1 : IsCharP α 0
d t c d_inv PSO3_inv : α
h : d ^ 2 * (d + t - d * t - 2) * (d + t + d * t) = 0
h_1 : -d ^ 4 * (d + t - d * t - 2) *
    (2 * d + 2 * d * t - 4 * d * t ^ 2 + 2 * d * t ^ 4 + 2 * d ^ 2 * t ^ 4 - c * (d + t + d * t)) =
  0
h_2 : d * d_inv = 1
h_3 : (d + t - d * t - 2) * PSO3_inv = 1
h_4 : ¬t ^ 2 = t + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [ring] Ring `α`
  [limits] Thresholds reached
```
:::

`ring` 求解器通过使用计算的 Gröbner 基对项进行归一化，将等式传播回 `grind`内核。
在以下示例中，方程 `x ^ 2 * y = 1` 和 `x * y ^ 2 = y` 意味着等式 `x = 1` 和 `y = 1`。
因此，术语 `x * y` 和 `1` 相等，因此 `some (x * y) = some 1` 同余。

```lean
example (x y : Int) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    some (y * x) = some 1 := by
  grind
```

:::comment
计划的未来功能：支持非交换环和半环。
:::
