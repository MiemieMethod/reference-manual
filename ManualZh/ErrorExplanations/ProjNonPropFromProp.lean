/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`projNonPropFromProp`" =>
%%%
tag := "zh-errorexplanations-projnonpropfromprop-root"
shortTitle := "projNonPropFromProp"
%%%

{errorExplanationHeader lean.projNonPropFromProp}
当尝试使用命题证明投影一段数据时，会发生此错误
指数投影。例如，如果 `h` 是存在命题的证明，则尝试
提取见证 `h.1` 是此错误的一个示例。此类预测是不允许的，因为它们
可能违反 Lean 对 {lean}`Prop` 进行大消除的禁止（请参阅
{ref "propositions"}[Propositions] 手册部分了解更多详细信息）。

考虑使用模式匹配而不是索引投影
{keywordOf Lean.Parser.Term.let}`let`、{keywordOf Lean.Parser.Term.match}`match` 表达式或
像 {tactic}`cases` 一样解构策略以从一种命题类型消除到另一种命题类型。注意事项
仅当结果值也在 {lean}`Prop` 中时，这种消除才有效；如果不是，
错误 {ref "lean.propRecLargeElim" (domain := Manual.errorExplanation)}[`lean.propRecLargeElim`]
将被提高。

# 示例
%%%
tag := "zh-errorexplanations-projnonpropfromprop-h001"
%%%

:::errorExample "Attempting to Use Index Projection on Existential Proof"

```broken
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > 0 :=
  ⟨h.1, Nat.lt_of_succ_lt h.2⟩
```
```output
Invalid projection: Cannot project a value of non-propositional type
  Nat
from the expression
  h
which has propositional type
  ∃ x, x > a + 1
```
```fixed "let"
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > a :=
  let ⟨w, hw⟩ := h
  ⟨w, Nat.lt_of_succ_lt hw⟩
```
```fixed "cases"
example (a : Nat) (h : ∃ x : Nat, x > a + 1) : ∃ x : Nat, x > a := by
  cases h with
  | intro w hw =>
    exists w
    omega
```

与存在命题的证明相关的证人不能使用以下方法提取：
指数投影。相反，有必要使用模式匹配：或者像 a 这样的术语
{keywordOf Lean.Parser.Term.let}`let` 绑定或策略（如 {tactic}`cases`）。
:::
