/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inferBinderTypeFailed`" =>
%%%
shortTitle := "inferBinderTypeFailed"
%%%

{errorExplanationHeader lean.inferBinderTypeFailed}

当声明头或本地绑定中的绑定器类型不完全时，会发生此错误
指定且无法由 Lean 推断。一般来说，可以通过提供更多
通过显式注释其类型来帮助 Lean 确定绑定器类型的信息
或者通过在使用它的站点提供附加类型信息。当有问题的活页夹
发生在声明的标头中，此错误通常伴随有
{ref "lean.inferDefTypeFailed" (domain := Manual.errorExplanation)}[`lean.inferDefTypeFailed`]。

请注意，如果声明使用显式结果类型进行注释，即使该声明包含
漏洞 - Lean 将不会使用定义主体中的信息来推断参数类型。它可能
因此有必要显式指定参数的类型，否则其类型将是
无需结果类型注释即可推断；请参阅“由于结果类型而无法推断的绑定程序”
下面以“注释”为例进行演示。在 {keyword}`theorem` 声明中，主体永远不会
用于推断活页夹的类型，因此任何无法从其余活页夹推断其类型的活页夹
定理类型必须包含类型注释。

当原本用作声明名称的标识符被更改时，也可能会出现此错误。
无意中写在了活页夹位置。在这些情况下，错误的标识符是
被视为具有未指定类型的绑定器，导致类型推断失败。这经常
尝试使用语法同时定义多个相同类型的常量时会发生
不支持这一点。此类情况包括：
* 尝试通过在 {keyword}`example` 关键字后写入标识符来举个例子；
* 尝试通过列出来定义具有相同类型和（如果适用）值的多个常量
  它们按顺序位于 {keyword}`def`、{keyword}`opaque` 或其他声明关键字之后；
* 尝试通过按顺序列出它们来定义同一类型结构的多个字段
  结构声明的同一行上的名称；和
* 省略归纳构造函数名称之间的竖线。

下面的示例演示了前三种情况。

# 示例

:::errorExample "Binder Type Requires New Type Variable"
```broken
def identity x :=
  x
```
```output
Failed to infer type of binder `x`
```
```fixed
def identity (x : α) :=
  x
```
在上面的代码中，`x`的类型是不受约束的；如本示例所示，Lean 不
自动为此类绑定器生成新的类型变量。相反，`x` 的类型 `α` 必须是
明确指定。请注意，如果启用自动隐式参数插入（因为它是通过
默认），`α`本身的binder不需要提供； Lean 将为此插入隐式绑定器
自动参数。
:::

:::errorExample "Uninferred Binder Type Due to Resulting Type Annotation"
```broken
def plusTwo x : Nat :=
  x + 2
```
```output
Failed to infer type of binder `x`

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
```
```fixed
def plusTwo (x : Nat) : Nat :=
  x + 2
```
尽管 `x` 被推断为 `plusTwo` 主体中的类型为 `Nat`，但此信息不是
在详细说明定义的类型时可用，因为其结果类型 (`Nat`) 已
明确指定。仅考虑标头中的信息，无法确定 `x` 的类型
确定，导致显示的错误。因此，有必要将 `x` 的类型包含在
它的活页夹。
:::

:::errorExample "Attempting to Name an Example Declaration"
```broken
example trivial_proof : True :=
  trivial
```
```output
Failed to infer type of binder `trivial_proof`

Note: Examples do not have names. The identifier `trivial_proof` is being interpreted as a parameter `(trivial_proof : _)`.
```
```fixed
example : True :=
  trivial
```
此代码无效，因为它尝试为 `example` 声明指定名称。例子不能
被命名，并且在其他声明形式中出现名称的地方写入标识符
被详细精化为粘合剂，其类型无法推断。如果必须命名声明，则应该是
使用支持命名的声明形式定义，例如 `def` 或 `theorem`。
:::

:::errorExample "Attempting to Define Multiple Opaque Constants at Once"
```broken
opaque m n : Nat
```
```output
Failed to infer type of binder `n`

Note: Multiple constants cannot be declared in a single declaration. The identifier `n` is being interpreted as a parameter `(n : _)`.
```
```fixed
opaque m : Nat
opaque n : Nat
```
此示例错误地尝试使用单个 `opaque` 声明定义多个常量。
这样的声明只能定义一个常量：不可能列出多个标识符
在 `opaque` 或 `def` 之后将它们定义为具有相同的类型（或值）。这样的声明是
相反，详细说明为使用由给出的参数定义单个常量（例如上面的 `m`）
后续标识符 (`n`)，其类型未指定且无法推断。定义多个
全局常量，需要单独声明。
:::

:::errorExample "Attempting to Define Multiple Structure Fields on the Same Line"
```broken
structure Person where
  givenName familyName : String
  age : Nat
```
```output
Failed to infer type of binder `familyName`
```
```fixed "Fixed (separate lines)"
structure Person where
  givenName : String
  familyName : String
  age : Nat
```
```fixed "Fixed (parenthesized)"
structure Person where
  (givenName familyName : String)
  age : Nat
```
此示例错误地尝试定义多个结构字段（`givenName` 和 `familyName`）
通过在同一行连续列出它们来表示同一类型。 Lean 相反将其解释为
定义单个字段 `givenName`，由没有指定类型的绑定器 `familyName` 参数化。
可以通过在单独的行上列出每个字段或将每个字段括起来来实现预期的行为
在括号中指定多个字段名称的行（请参阅手册部分
{ref "inductive-types"}[归纳类型] 了解有关结构的更多详细信息
声明）。
:::
