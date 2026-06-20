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

#doc (Manual) "集成`grind`的功能" =>
%%%
tag := "zh-grind-extendedexamples-integration-root"
%%%

:::paragraph
该示例演示了{tactic}`grind`的各个子模块如何无缝集成。
特别是我们可以：
* 使用自定义模式实例化库中的定理，
* 执行案例分割，
* 进行线性整数算术推理，包括模块化条件，以及
* 进行 Gröbner 基础推理
所有这些都没有提供明确的指令来驱动这些推理模式之间的相互作用。
:::

对于此示例，我们将从实数的“模拟”版本以及 `sin` 和 `cos` 函数开始。
当然，这个示例可以使用 Mathlib 的版本[无需任何更改](https://github.com/leanprover-community/mathlib4/blob/master/MathlibTest/grind/trig.lean)！


:::TODO
`instCommRingR` 的 `sorry` 会导致运行时崩溃。目前还不清楚为什么。
:::

```lean
axiom R : Type


@[instance] axiom instCommRingR : Lean.Grind.CommRing R


axiom sin : R → R
axiom cos : R → R
axiom trig_identity : ∀ x, (cos x)^2 + (sin x)^2 = 1
```

:::paragraph
我们的第一步是告诉grind在看到涉及{name}`sin`或{name}`cos`的目标时“将三角恒等式放在白板上”：

```lean
grind_pattern trig_identity => cos x
grind_pattern trig_identity => sin x
```

请注意，这里我们对同一定理使用“两种”不同模式，因此即使 {tactic}`grind` 仅看到这些函数之一，该定理也会被实例化。
如果我们希望仅当 {name}`sin` 和 {name}`cos` 都存在时更保守地实例化定理，我们可以使用多重模式：

```lean -keep
grind_pattern trig_identity => cos x, sin x
```

对于本示例，两种方法都可以。
:::

::::leanSection
```lean -show
variable {x : R}
```

:::paragraph
因为 `grind` 立即注意到三角恒等式，所以我们可以证明这样的目标：
```lean
example : (cos x + sin x)^2 = 2 * cos x * sin x + 1 := by
  grind
```
这里 {tactic}`grind` 执行以下操作：

1. 它注意到 {lean}`cos x` 和 {lean}`sin x`，因此实例化三角恒等式。

2. 它注意到这是 {inst}`CommRing R` 中的多项式，并将其发送到 Gröbner 基础模块。
   此时不进行任何计算：它是该环中的第一个多项式关系，因此 Gröbner 基更新为 {lean}`[(cos x)^2 + (sin x)^2 - 1]`。

3. 它注意到球门的左侧和右侧是 {inst}`CommRing R` 中的多项式，并将它们发送到 Gröbner 基础模块进行归一化。

由于它们模 {lean}`(cos x)^2 + (sin x)^2 = 1` 的范式相等，因此它们的等价类被合并，并且目标得到解决。

:::


:::paragraph
当需要 {tech (key := "congruence closure")}[同余闭包] 时，我们也可以进行此类论证：
```lean
example (f : R → Nat) :
    f ((cos x + sin x)^2) = f (2 * cos x * sin x + 1) := by
  grind
```

```lean -show
variable (f : R → Nat) (n : Nat)
```

与之前一样，{tactic}`grind` 实例化三角恒等式，注意到 {lean}`(cos x + sin x)^2` 和 {lean}`2 * cos x * sin x + 1` 等于模 {lean}`(cos x)^2 + (sin x)^2 = 1`，
将这些代数表达式放在同一个等价类中，然后将函数应用程序 {lean}`f ((cos x + sin x)^2)` 和 {lean}`f (2 * cos x * sin x + 1)` 放在同一个等价类中，
并关闭目标。
:::

请注意，我们在这里使用了任意函数​​ {typed}`f : R → Nat`；让我们检查一下 `grind` 在 Gröbner 基步骤之后是否可以使用一些线性整数算术推理：
```lean
example (f : R → Nat) :
    4 * f ((cos x + sin x)^2) ≠ 2 + f (2 * cos x * sin x + 1) := by
  grind
```


这里，{tactic}`grind` 首先计算出对于某些 {typed}`n : Nat`，这个目标简化为 {lean}`4 * n ≠ 2 + n`（即通过如上所述识别两个函数应用），然后使用模块化来导出矛盾。



最后，我们还可以在某些情况下混合拆分：
```lean
example (f : R → Nat) :
    max 3 (4 * f ((cos x + sin x)^2)) ≠
      2 + f (2 * cos x * sin x + 1) := by
  grind
```
和以前一样，{tactic}`grind` 首先进行识别两个函数应用程序所需的实例化和 Gröbner 基础计算。
但是，`cutsat` 算法本身无法对 {lean}`max 3 (4 * n) ≠ 2 + n` 执行任何操作。
接下来，在实例化声明 {lean}`∀ {n m : Nat}, max n m = if n ≤ m then m else n` 的 {lean}`Nat.max_def`（自动，因为标准库中的注释）之后，{tactic}`grind` 可以根据不等式进行大小写拆分。
在分支{lean}`3 ≤ 4 * n`中，`cutsat`再次使用模块化来证明`4 * n ≠ 2 + n`。
在分支{lean}`4 * n < 3`中，`cutsat`快速确定{lean}`n = 0`，然后注意到{lean}`4 * 0 ≠ 2 + 0`。

当然，这是一个非常人为的例子！
在实践中，这种不同推理模式的自动集成非常强大：跟踪实例化定理和等价类的中央“白板”可以将相关术语和等式交给适当的模块（此处为 `cutsat` 和 Gröbner 库），然后模块可以将新事实返回到白板。

::::
