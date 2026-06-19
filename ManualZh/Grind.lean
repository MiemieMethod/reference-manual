/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers

import ManualZh.Grind.ConstraintPropagation
import ManualZh.Grind.CongrClosure
import ManualZh.Grind.CaseAnalysis
import ManualZh.Grind.EMatching
import ManualZh.Grind.Cutsat
import ManualZh.Grind.Algebra
import ManualZh.Grind.Linarith
import ManualZh.Grind.Annotation
import ManualZh.Grind.ExtendedExamples

-- Needed for the if-then-else normalization example.
import Std.Data.TreeMap
import Std.Data.HashMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true

-- TODO (@kim-em): `Lean.Grind.AddCommMonoid` and `Lean.Grind.AddCommGroup` are not yet documented.
set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

-- The verso default max line length is 60, which is very restrictive.
-- TODO: discuss with David.
set_option verso.code.warnLineLength 72

open Manual (comment)

#doc (Manual) "`grind`策略" =>
%%%
tag := "grind-tactic"
%%%

:::tutorials
 * {ref "grind-index-map" (remote := "tutorials")}[使用 `grind` 进行订购地图]
:::

```lean -show
-- Open some namespaces for the examples.
open Lean Lean.Grind Lean.Meta.Grind
```

{tactic}`grind`策略使用受现代 SMT 求解器启发的技术来自动构建证明。
它通过增量收集事实集、使用一组合作技术从现有事实中推导出新事实来生成证据。
在幕后，所有的证明都是通过反证法，所以预期的结论和前提之间不存在操作上的区别； {tactic}`grind` 总是试图推导出矛盾。

想象一个虚拟白板。
每当 {tactic}`grind` 发现新的等式、不等式或布尔文字时，它都会将该事实写入黑板上，将等效项合并到存储桶中，并邀请每个引擎从共享白板中读取并添加回共享白板。
特别是，由于所有真命题都等于 {lean}`True`，所有假命题都等于 {lean}`False`，因此 {tactic}`grind` 跟踪一组已知事实作为跟踪等价类的一部分。

:::paragraph
合作的引擎有：

* {tech}[同余闭包],
* {tech}[约束传播],
* {tech}[E 匹配],
* 指导{ref "grind-split"}[案例分析]，以及
* 一套卫星理论求解器，包括 {ref "cutsat"}[线性整数算术] 和 {ref "grind-ring"}[交换环]。

与其他策略一样，{tactic}`grind` 为其添加的每个事实生成普通的 Lean 证明条款。
Lean 的标准库已经用 `@[grind]` 属性进行了注释，因此会自动发现常见的引理。
:::

{tactic}`grind` *不是*为搜索空间组合爆炸的目标而设计 - 想想大型 `n` 鸽子实例、图形着色减少、高阶 N 皇后板或编码为布尔约束的 200 变量数独。
此类编码需要数千（或数百万）次大小写分割，这会压垮 {tactic}`grind` 的分支搜索。
对于位级或纯布尔组合问题，请使用 {tactic}`bv_decide`。  {tactic}`bv_decide`策略调用最先进的 SAT 求解器（例如 CaDiCaL 或 Kissat），然后返回紧凑的机器可检查证书。
所有大量搜索都发生在 Lean 之外；证书在 Lean 内重放和验证，因此保留了信任（验证时间随证书大小而变化）。

:::TODO
当可用时将其包括在内：
* *需要跨多个理论进行大量案例分析的完整 SMT 问题*（数组、位向量、丰富的算术、量词等）→ 使用即将推出的 *`lean‑smt`*策略- 用于 CVC5 的紧凑 Lean 前端，可重放 Lean 内的 unsat 核心或模型。
:::


:::example "Congruence Closure" (open := true)

使用 {tech}[同余闭包]，该证明立即成功，它发现了相等项的集合。

```lean
example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) :
    a = c := by
  grind
```

:::

:::example "Algebraic Reasoning" (open := true)

该证明使用 {tactic}`grind` 的交换环求解器。

```lean -show
open Lean.Grind
```
```lean
example [CommRing α] [NoNatZeroDivisors α] (a b c : α) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  grind
```
:::

:::example "Finite-Field Reasoning" (open := true)
{name}`Fin` 上的算术运算溢出，当结果超出界限时返回到 {lean  (type := "Fin 11")}`0`。
{tactic}`grind` 可以使用这个事实来证明如下定理：

```lean
example (x y : Fin 11) :
    x ^ 2 * y = 1 →
    x * y ^ 2 = y →
    y * x = 1 := by
  grind
```
:::

:::example "Linear Integer Arithmetic with Case Analysis" (open := true)

```lean
example (x y : Int) :
    27 ≤ 11 * x + 13 * y →
    11 * x + 13 * y ≤ 45 →
    -10 ≤ 7 * x - 9 * y →
    7 * x - 9 * y ≤ 4 →
    False := by
  grind
```

:::

# 错误信息
%%%
tag := "grind-errors"
%%%

当 {tactic}`grind` 失败时，它会打印剩余的子目标，然后打印其子系统返回的所有信息 - “共享白板”的内容。
特别是，它提供了已确定为相等的术语的等价类。
最大的两个类显示为 `True propositions` 和 `False propositions`，列出了当前已知的可证明或可反驳的每个文字。
检查这些列表以发现缺失的事实或矛盾的假设。

# 最小化 `grind` 调用

`grind only [...]`策略使用一组有限的定理调用 {tactic}`grind`，这可以提高性能。
可以使用 {tactic}`grind?` 方便地构造对 `grind only` 的调用，它会自动记录 {tactic}`grind` 使用的定理并建议合适的 `grind only`。

这些定理通常包含符号前缀，例如 `=`、`←` 或 `→`，表示
触发实例化的模式。详细信息请参见 {ref "e-matching"}[电子匹配部分]。
某些定理可能标有 `usr` 前缀，这表示使用了自定义模式。

{include 1 ManualZh.Grind.CongrClosure}

{include 1 ManualZh.Grind.ConstraintPropagation}

{include 1 ManualZh.Grind.CaseAnalysis}

{include 1 ManualZh.Grind.EMatching}

{include 1 ManualZh.Grind.Cutsat}

{include 1 ManualZh.Grind.Algebra}

{include 1 ManualZh.Grind.Linarith}

{include 1 ManualZh.Grind.Annotation}

# 还原性

{tech}[可简化]术语定义由{tactic}`grind` 热切地展开。
这可以实现更高效的 定义等价 比较和索引。

:::example "Reducibility and Congruence Closure"
{name}`one` 的定义不是 {tech}[可约化]：
```lean
def one := 1
```
这意味着 {tactic}`grind` 不会展开它：
```lean +error (name := noUnfold)
example : one = 1 := by grind
```
```leanOutput noUnfold
`grind` failed
case grind
h : ¬one = 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [cutsat] Assignment satisfying linear constraints
```

另一方面，{name}`two` 是缩写，因此可以简化：
```lean
abbrev two := 2
```

{tactic}`grind` 将 {name}`two` 展开，然后将其添加到“白板”中，从而可以立即完成证明：
```lean
example : two = 2 := by grind
```
:::

电子匹配模式还展现了可简化的定义。
为有关缩写的定理生成的模式以展开的缩写表示。
缩写一般不应是递归的；特别是，当使用 {tactic}`grind` 时，递归缩写可能会导致索引性能较差和不可预测的模式。

:::example "E-matching and Unfolding Abbreviations"
当向定理添加 {attr}`grind` 注释时，将根据定理语句生成 E 匹配模式。
这些模式决定了定理何时被实例化。
定理 {name}`one_eq_1` 提到了 {tech}[半可约] 定义 {name}`one`，结果模式也是 {name}`one`：
```lean (name := one_eq_1)
def one := 1

@[grind? =]
theorem one_eq_1 : one = 1 := by rfl
```
```leanOutput one_eq_1
one_eq_1: [one]
```

将相同的注释应用于有关 {tech}`reducible` 缩写 {name}`two` 的定理会产生 {name}`two` 展开的模式：
```lean (name := two_eq_2)
abbrev two := 2

@[grind? =]
theorem two_eq_2: two = 2 := by grind
```
```leanOutput two_eq_2
two_eq_2: [@OfNat.ofNat `[Nat] `[2] `[instOfNatNat 2]]
```

:::

:::example "Recursive Abbreviations and `grind`"
使用 {attr}`grind` 属性为递归缩写的 {tech}[等式引理] 添加电子匹配模式不会产生递归缩写的有用模式。
斐波那契函数定义中的 {attrs}`@[grind?]` 属性会产生三种模式，每种模式对应于三种可能性之一：
```lean (name := fib1) -keep
@[grind?]
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```
```leanOutput fib1
fib.eq_1: [fib `[0]]
```
```leanOutput fib1
fib.eq_2: [fib `[1]]
```
```leanOutput fib1
fib.eq_3: [fib (#0 + 2)]
```
用缩写替换定义会产生函数出现展开的模式。
这些模式并不是特别有用：
```lean (name := fib2) -keep
@[grind?]
abbrev fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```
```leanOutput fib2
fib.eq_1: [@OfNat.ofNat `[Nat] `[0] `[instOfNatNat 0]]
```
```leanOutput fib2
fib.eq_2: [@OfNat.ofNat `[Nat] `[1] `[instOfNatNat 1]]
```
```leanOutput fib2
fib.eq_3: [@HAdd.hAdd `[Nat] `[Nat] `[Nat] `[instHAdd] (fib #0) (fib (#0 + 1))]
```
:::



```comment
# Diagnostics
TBD
Threshold notices, learned equivalence classes, integer assignments, algebraic basis, performed splits, instance statistics.

# Troubleshooting & FAQ
TBD
```

{include 1 ManualZh.Grind.ExtendedExamples}
