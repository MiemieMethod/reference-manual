/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inductionWithNoAlts`" =>
%%%
shortTitle := "inductionWithNoAlts"
%%%

{errorExplanationHeader lean.inductionWithNoAlts}

在 Lean 中使用归纳的基于策略的证明需要使用类似模式匹配的符号来描述
个别情况的证明。但是，Mathlib 中的 `induction'`策略和专用
`induction`策略用于自然数游戏中的自然数遵循不同的模式。

# 示例

:::errorExample "Adding Explicit Cases to an Induction Proof"
```broken
theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with n n_ih
  rw [Nat.mul_zero]
  rw [Nat.mul_succ]
  rw [Nat.add_zero]
  rw [n_ih]
```
```output
Invalid syntax for induction tactic: The `with` keyword must be followed by a tactic or by an alternative (e.g. `| zero =>`), but here it is followed by the identifier `n`.
```
```fixed
theorem zero_mul (m : Nat) : 0 * m = 0 := by
  induction m with
  | zero =>
    rw [Nat.mul_zero]
  | succ n n_ih =>
    rw [Nat.mul_succ]
    rw [Nat.add_zero]
    rw [n_ih]
```
被破坏的例子具有自然数游戏中正确证明的结构，并且这个
如果您使用 `import Mathlib` 并将 `induction` 替换为 `induction'`，则证明将起作用。感应策略
在基本 Lean 中，期望 {keyword}`with` 关键字后面跟着一系列情况，并且名称
对于电感外壳，在 {name Nat.succ}`succ` 外壳中提供，而不是在 {name Nat.succ}`succ` 外壳中提供
预先。
:::
