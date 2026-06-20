/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inferDefTypeFailed`" =>
%%%
tag := "zh-errorexplanations-inferdeftypefailed-root"
shortTitle := "inferDefTypeFailed"
%%%

{errorExplanationHeader lean.inferDefTypeFailed}

当未完全指定定义的类型且 Lean 无法推断时，会出现此错误
从可用信息中可以看出其类型。如果定义有参数，这个错误仅指
冒号后的结果类型（错误
{ref "lean.inferBinderTypeFailed" (domain := Manual.errorExplanation)}[`lean.inferBinderTypeFailed`]
表示无法推断参数类型）。

要解决此错误，请在定义中提供附加类型信息。这可以做到
直接通过在定义中的冒号后提供显式结果类型来实现
标头。或者，如果未提供显式结果类型，则添加更多类型
定义主体的信息——例如通过指定隐式类型参数或给出
`let` 绑定器的显式类型 — 可以允许 Lean 推断定义的类型。寻找类型
与此一起出现的推理或隐式论证综合错误，以识别
可能导致此错误的歧义。

请注意，当提供显式结果类型时（即使该类型包含孔），Lean 也不会
使用定义主体中的信息来帮助推断定义或其参数的类型。
因此，添加显式结果类型可能还需要向参数添加类型注释
其类型以前是可以推断的。此外，始终需要提供明确的
输入 `theorem` 声明：`theorem` 语法需要类型注释，而精化器
永远不会尝试使用定理体来推断被证明的命题。

# 示例
%%%
tag := "zh-errorexplanations-inferdeftypefailed-h001"
%%%

:::errorExample "Implicit Argument Cannot be Inferred"
```broken
def emptyNats :=
  []
```
```output
Failed to infer type of definition `emptyNats`
```
```fixed "type annotation"
def emptyNats : List Nat :=
  []
```
```fixed "implicit argument"
def emptyNats :=
  List.nil (α := Nat)
```

这里，Lean 无法推断出 `List` 类型构造函数的参数 `α` 的值，即
反过来又阻止它推断定义的类型。可能有两种修复方法：指定
定义的预期类型允许 Lean 推断适当的隐式参数
`List.nil` 构造函数；或者，使这个隐式参数在函数体中显式显示
为 Lean 提供足够的信息来推断定义的类型。
:::

:::errorExample "Definition Type Uninferrable Due to Unknown Parameter Type"
```broken
def identity x :=
  x
```
```output
Failed to infer type of definition `identity`
```
```fixed
def identity (x : α) :=
  x
```

在此示例中，`identity` 的类型由 `x` 的类型确定，无法推断。
指示的错误和
{ref "lean.inferBinderTypeFailed" (domain := Manual.errorExplanation)}[`lean.inferBinderTypeFailed`]
因此出现（请参阅该示例的其他讨论的解释）。解决
后者通过显式指定 `x` 的类型为 Lean 提供足够的信息来推断
定义类型。
:::
