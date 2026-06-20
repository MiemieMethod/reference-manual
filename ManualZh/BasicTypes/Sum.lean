/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "总和类型" =>
%%%
file := "Sum-Types"
tag := "sum-types"
%%%


{deftech}_Sum types_ 表示两种类型之间的选择：和的元素是其他类型之一的元素，并与它来自哪种类型的指示配对。
求和也称为不相交联合、可区分联合或标记联合。
sum 的构造函数也称为 {deftech}_injections_；从数学上讲，它们可以被视为从每个被加数到总和的单射函数。

::::leanSection
```lean -show
universe u v
```

:::paragraph
sum 类型有两种类型：

 * {lean}`Sum` 是所有 {lean}`Type` {tech (key := "universe polymorphism")}[宇宙] 上的 {tech (key := "universes")}[多态]，并且绝不是 {tech (key := "proposition")}[命题]。

 * {lean}`PSum` 允许加数是命题或类型。与 {name}`Or` 不同，两个命题的 {name}`PSum` 仍然是一个类型，非命题代码可以检查使用哪个注入来构造给定值。

手动编写的 Lean 代码几乎总是仅使用 {lean}`Sum`，而 {lean}`PSum` 则用作证明自动化实现的一部分。
这是因为它施加了 宇宙层级 统一无法解决的有问题的约束。
特别是，该类型位于宇宙 {lean}`Sort (max 1 u v)` 中，这可能会导致 宇宙层级 统一出现问题，因为方程 `max 1 u v = ?u + 1` 在级别算术中无解。
`PSum` 通常仅用于构造任意类型之和的自动化。
:::
::::

{docstring Sum}

{docstring PSum}



# 句法
%%%
file := "Syntax"
tag := "sum-syntax"
%%%

名称 {name}`Sum` 和 {name}`PSum` 很少明确写入。
大多数代码使用相应的中缀运算符。

```lean -show
section
variable {α : Type u} {β : Type v}
```

:::syntax term (title := "Sum Types")
```grammar
$_ ⊕ $_
```

{lean}`α ⊕ β` 是 {lean}`Sum α β` 的表示法。

:::

```lean -show
end
```

```lean -show
section
variable {α : Sort u} {β : Sort v}
```

:::syntax term (title := "Potentially-Propositional Sum Types")
```grammar
$_ ⊕' $_
```

{lean}`α ⊕' β` 是 {lean}`PSum α β` 的表示法。

:::

```lean -show
end
```

# API 参考
%%%
file := "API-Reference"
tag := "sum-api"
%%%

Sum 类型主要用于 {tech (key := "pattern matching")}[模式匹配]，而不是来自 API 的显式函数调用。
因此，它们的主要 API 是构造函数 {name Sum.inl}`inl` 和 {name Sum.inr}`inr`。

## 案例区分
%%%
file := "Case-Distinction"
tag := "zh-basictypes-sum-h003"
%%%

{docstring Sum.isLeft}

{docstring Sum.isRight}

## 提取值
%%%
file := "Extracting-Values"
tag := "zh-basictypes-sum-h004"
%%%

{docstring Sum.elim}

{docstring Sum.getLeft}

{docstring Sum.getLeft?}

{docstring Sum.getRight}

{docstring Sum.getRight?}

## 转换
%%%
file := "Transformations"
tag := "zh-basictypes-sum-h005"
%%%

{docstring Sum.map}

{docstring Sum.swap}

## 有人居住
%%%
file := "Inhabited"
tag := "zh-basictypes-sum-h006"
%%%

{name}`Sum` 和 {name}`PSum` 的 {name}`Inhabited` 定义未注册为实例。
这是因为有两种不同的方法来构造默认值（通过 {name Sum.inl}`inl` 或 {name Sum.inr}`inr`），并且实例综合可能会导致任一选择。
结果可能是两个相同书写的术语的精化不同并且不 {tech (key := "definitional equality")}[定义等价]。

两种类型都有 {name}`Nonempty` 实例，对于 {tech (key := "proof irrelevance")}[证明无关性]，选择 {name Sum.inl}`inl` 或 {name Sum.inr}`inr` 并不重要。
这足以启用 {keyword}`partial` 功能。
对于需要 {name}`Inhabited` 实例的情况（例如使用 {keyword}`panic!` 的程序），可以通过使用 {keywordOf Lean.Parser.Term.have}`have` 或 {keywordOf Lean.Parser.Term.let}`let` 将实例添加到本地上下文来显式使用该实例。

:::example "Inhabited Sum Types"

在 Lean 的逻辑中，{keywordOf Lean.Parser.Term.panic}`panic!` 相当于其类型的 {name}`Inhabited` 实例中指定的默认值。
这意味着该类型必须具有这样的实例 - {name}`Nonempty` 实例与选择公理相结合将使程序不可计算。

产品有正确的实例：
```lean
example : Nat × String := panic! "Can't find it"
```

默认情况下，总和不会：
```lean +error (name := panic)
example : Nat ⊕ String := panic! "Can't find it"
```
```leanOutput panic
failed to synthesize instance of type class
  Inhabited (Nat ⊕ String)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

可以使用 {keywordOf Lean.Parser.Term.have}`have` 使所需实例可用于实例合成：
```lean
example : Nat ⊕ String :=
  have : Inhabited (Nat ⊕ String) := Sum.inhabitedLeft
  panic! "Can't find it"
```
:::

{docstring Sum.inhabitedLeft}

{docstring Sum.inhabitedRight}

{docstring PSum.inhabitedLeft}

{docstring PSum.inhabitedRight}
