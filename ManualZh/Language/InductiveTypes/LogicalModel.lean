/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta
import Manual.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

#doc (Manual) "逻辑模型" =>
%%%
tag := "inductive-types-logical-model"
%%%


# 递归器
%%%
tag := "recursors"
%%%

每个归纳类型都配备有 {tech}[recursor]。
递归器完全由类型构造函数和构造函数的签名确定。
递归器具有函数类型，但它们是原始类型，无法使用 `fun` 进行定义。

## 递归器类型
%%%
tag := "recursor-types"
%%%

:::paragraph
递归器采用以下参数：
: 归纳类型的{tech (key := "parameters")}[参数]

  由于参数是一致的，因此可以在整个递归器上抽象它们。

: {deftech}_motive_

  动机决定了递归器的应用类型。动机是一个函数，其参数是类型的索引和实例化这些索引的类型的实例。动机确定的类型的特定 Universe 取决于归纳类型的 Universe 和特定构造函数 - 有关详细信息，请参阅有关 {ref "subsingleton-elimination"}[{tech}[subsingleton] 消除] 的部分。

: 每个构造函数都有一个 {deftech (key := "minor premise")}_小前提_

  对于每个构造函数，递归器期望一个函数满足构造函数的任意应用的动机。
  每个小前提都抽象了构造函数的所有参数。
  如果构造函数的参数类型是归纳类型本身，则小前提另外接受一个参数，该参数的类型是应用于该参数值的动机 - 这将收到递归处理递归参数的结果。

: {deftech (key := "major premise")}_大前提_，或目标

  最后，递归器将类型的实例以及任何索引值作为参数。

递归器的结果类型是应用于这些索引的动机和大前提。
:::

:::example "The recursor for {lean}`Bool`"
{lean}`Bool`的递归器{name}`Bool.rec`具有以下参数：

 * 动机计算任何宇宙中的类型，给定 {lean}`Bool`。
 * 两个构造函数都有一些小前提，其中 {lean}`false` 和 {lean}`true` 的动机都得到满足。
 * 大前提是一些{lean}`Bool`。

返回类型是应用于大前提的动机。

```signature
Bool.rec.{u} {motive : Bool → Sort u}
  (false : motive false)
  (true : motive true)
  (t : Bool) : motive t
```
:::

::::example "The recursor for {lean}`List`"
{lean}`List`的递归器{name}`List.rec`具有以下参数：

:::keepEnv
```lean -show
axiom α.{u} : Type u
```

 * 参数{lean}`α`排在第一位，因为动机、小前提、大前提都需要引用它。
 * 动机计算任何宇宙中的类型，给定 {lean}`List α`。 宇宙层级 `u` 和 `v` 之间没有连接。
 * 两个构造函数都有一些小前提：
    - {name}`List.nil` 的动机得到满足
    - 动机应该可以满足 {name}`List.cons` 的任何应用，因为它可以满足尾部。额外的参数`motive tail`是因为`tail`的类型是{name}`List`的递归出现。
 * 大前提是一些{lean}`List α`。
:::

再次强调，返回类型是应用于大前提的动机。

```signature
List.rec.{u, v} {α : Type v} {motive : List α → Sort u}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail →
    motive (head :: tail))
  (t : List α) : motive t
```
::::

:::::keepEnv
::::example "Recursor with parameters and indices"
给出 {name}`EvenOddList` 的定义：
```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```


递归器 {name}`EvenOddList.rec` 与 `List` 非常相似。
差异来自于索引的存在：
 * 现在的动机抽象了任何任意选择的指数。
 * {name EvenOddList.nil}`nil` 的小前提将动机应用于 {name EvenOddList.nil}`nil` 的索引值 `true`。
 * 小前提{name EvenOddList.cons}`cons`对其递归发生中使用的索引值进行抽象，并用其否定实例化动机。
 * 大前提还抽象了任意选择的索引。

```signature
EvenOddList.rec.{u, v} {α : Type v}
  {motive : (isEven : Bool) → EvenOddList α isEven → Sort u}
  (nil : motive true EvenOddList.nil)
  (cons : {isEven : Bool} →
    (head : α) →
    (tail : EvenOddList α isEven) → motive isEven tail →
    motive (!isEven) (EvenOddList.cons head tail)) :
  {isEven : Bool} → (t : EvenOddList α isEven) → motive isEven t
```
::::
:::::

当使用谓词（即返回 {lean}`Prop` 的函数）作为动机时，递归表示归纳。
非递归构造函数的小前提是基例，为具有递归参数的构造函数的小前提提供的附加参数是归纳假设。

### 亚单例消除
%%%
tag := "subsingleton-elimination"
%%%

Lean 中的证明与计算无关。
换句话说，在提供了某个命题的“某些”证明后，程序应该不可能检查它收到了“哪个”证明。
这反映在归纳定义的命题或谓词的递归器类型中。
对于这些类型，如果该定理有多个潜在证明，则动机可能只会返回另一个 {lean}`Prop`。
如果类型的结构使得最多只有一个证明，那么动机可能会返回任何宇宙中的类型。
最多有一个居民的命题称为 {deftech}_subsingleton_。
不是强迫用户_证明_只有一种可能的证明，而是使用保守的语法近似来检查命题是否是子单例。
满足以下两个要求的提案被视为子单例：
 * 最多有一个构造函数。
 * 每个构造函数的参数类型都是 {lean}`Prop`、参数或索引。

:::example "{lean}`True` is a subsingleton"
{lean}`True` 是一个子单例，因为它有一个构造函数，并且该构造函数没有参数。
其递归器具有以下签名：
```signature
True.rec.{u} {motive : True → Sort u}
  (intro : motive True.intro)
  (t : True) : motive t
```
:::

:::example "{lean}`False` is a subsingleton"
{lean}`False` 是一个子单例，因为它没有构造函数。
其递归器具有以下签名：
```signature
False.rec.{u} (motive : False → Sort u) (t : False) : motive t
```
请注意，动机是一个显式参数。
这是因为在任何进一步的参数类型中都没有提到它，因此无法通过统一来解决。
:::


:::example "{name}`And` is a subsingleton"
{lean}`And` 是一个子单例，因为它有一个构造函数，并且构造函数的两个参数类型都是命题。
其递归器具有以下签名：
```signature
And.rec.{u} {a b : Prop} {motive : a ∧ b → Sort u}
  (intro : (left : a) → (right : b) → motive (And.intro left right))
  (t : a ∧ b) : motive t
```
:::

:::example "{name}`Or` is not a subsingleton"
{lean}`Or` 不是子单例，因为它有多个构造函数。
其递归器具有以下签名：
```signature
Or.rec {a b : Prop} {motive : a ∨ b → Prop}
  (inl : ∀ (h : a), motive (.inl h))
  (inr : ∀ (h : b), motive (.inr h))
  (t : a ∨ b) : motive t
```
动机的类型表明{name}`Or.rec`只能用于产生证明。
析取的证明可以用来证明其他东西，但是程序无法检查两个析取中哪一个为真并用于证明。
:::

:::example "{name}`Eq` is a subsingleton"
{lean}`Eq` 是一个子单例，因为它只有一个构造函数 {name}`Eq.refl`。
此构造函数使用参数值实例化 {lean}`Eq` 的索引，因此所有参数都是参数：
```signature
Eq.refl.{u} {α : Sort u} (x : α) : Eq x x
```

其递归器具有以下签名：
```signature
Eq.rec.{u, v} {α : Sort v} {x : α}
  {motive : (y : α) → x = y → Sort u}
  (refl : motive x (.refl x))
  {y : α} (t : x = y) : motive y t
```
这意味着等式证明可以用来重写非命题的类型。
:::

## 减少
%%%
tag := "iota-reduction"
%%%


除了向逻辑添加新常量之外，归纳类型声明还添加新的归约规则。
这些规则控制着递归器和构造函数之间的交互；特别是以构造函数作为主要前提的递归器。
这种形式的还原称为 {deftech (key := "ι-reduction")}_ι-还原_（iota 还原）{index}[ι-还原]{index (subterm:="ι (iota)")}[还原]。

当递归器的大前提是不带递归参数的构造函数时，递归应用程序会简化为构造函数的小前提对构造函数的参数的应用。
如果存在递归参数，则通过将递归应用于递归事件来找到小前提的这些参数。

# 格式良好的要求
%%%
tag := "well-formed-inductives"
%%%

归纳类型声明须遵守许多格式良好的要求。
这些要求确保 Lean 在使用归纳类型的新规则进行扩展时保持逻辑一致。
他们是保守的：存在潜在的归纳类型不会破坏一致性，但这些要求仍然拒绝。

## 宇宙层级
%%%
tag := "inductive-type-universe-levels"
%%%

归纳类型的 Type 构造函数必须位于 {tech}[universe] 或其返回类型为 Universe 的函数类型中。
每个构造函数必须位于返回归纳类型的饱和应用程序的函数类型中。
如果归纳类型的 Universe 是 {lean}`Prop`，则对 Universe 没有进一步的限制，因为 {lean}`Prop` 是 {tech (key := "impredicative")}[必然]。
如果 Universe 不是 {lean}`Prop`，则构造函数的每个参数必须满足以下条件：
 * 如果构造函数的参数是归纳类型的参数（在参数与索引的意义上），则此参数的类型可能不大于类型构造函数的范围。
 * 所有其他构造函数参数必须小于类型构造函数的范围。

:::::keepEnv
::::example "Universes, constructors, and parameters"
{lean}`Either` 位于其参数的较大宇宙中，因为两者都是归纳类型的参数：
```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Either α β
  | inr : β → Either α β
```

{lean}`CanRepr` 位于比构造函数参数 `α` 更大的宇宙中，因为 `α` 不是归纳类型的参数之一：
```lean
inductive CanRepr : Type (u + 1) where
  | mk : (α : Type u) → [Repr α] → CanRepr
```

无构造函数归纳类型可能位于比其参数更小的宇宙中：
```lean
inductive Spurious (α : Type 5) : Type 0 where
```
但是，在不更改其级别的情况下向 {name}`Spurious` 添加构造函数是不可能的。
::::
:::::

## 严格的积极性
%%%
tag := "strict-positivity"
%%%


在构造函数的参数类型中定义的类型的所有出现都必须位于 {deftech (key := "strictly positive")}_严格正_位置。
如果某个位置不在函数的参数类型中（无论其周围嵌套了多少个函数类型），并且它不是除归纳类型的类型构造函数之外的任何表达式的参数，则该位置严格为正。
此限制排除了不健全的归纳类型定义，但代价是也排除了一些没有问题的定义。

:::::example "Non-strictly-positive inductive types"
::::keepEnv
:::keepEnv
如果不拒绝，类型 `Bad` 将使 Lean 不一致：
```lean (name := Bad) +error
inductive Bad where
  | bad : (Bad → Bad) → Bad
```
```leanOutput Bad
(kernel) arg #1 of 'Bad.bad' has a non positive occurrence of the datatypes being declared
```
:::

:::keepEnv
```lean -show
axiom Bad : Type
axiom Bad.bad : (Bad → Bad) → Bad
```
这是因为可以编写一个循环论证，在假设 {lean}`Bad` 下证明 {lean}`False`。
{lean}`Bad.bad` 被拒绝，因为构造函数的参数的类型为 {lean}`Bad → Bad`，该类型是 {lean}`Bad` 作为参数类型出现的函数类型。
:::

:::keepEnv
定点运算符的此声明被拒绝，因为 `Fix` 作为 `f` 的参数出现：
```lean (name := Fix) +error
inductive Fix (f : Type u → Type u) where
  | fix : f (Fix f) → Fix f
```
```leanOutput Fix
(kernel) arg #2 of 'Fix.fix' contains a non valid occurrence of the datatypes being declared
```
:::

`Fix.fix` 被拒绝，因为 `f` 不是归纳类型的类型构造函数，但 `Fix` 本身作为它的参数出现。
在这种情况下，`Fix` 也足以构造与 `Bad` 等效的类型：
```lean -show
axiom Fix : (Type → Type) → Type
```
```lean
def Bad : Type := Fix fun t => t → t
```
::::
:::::


## Prop 与 Type 对比
%%%
tag := "prop-vs-type"
%%%

Lean 拒绝实际上无法多态使用的全域多态类型。
如果 Universe 参数的某些实例化导致类型本身成为 {lean}`Prop`，则可能会出现这种情况。
如果此类型不是 {tech}[subsingleton]，则其递归器只能定位命题（即 {tech}[motive] 必须返回 {lean}`Prop`）。
这些类型只有作为 {lean}`Prop` 本身才有意义，因此宇宙多态性可能是一个错误。
由于它们基本上无用，因此 Lean 的归纳类型精化器并未设计为支持这些类型。

当这样的宇宙多态归纳类型确实是子单子时，定义它们是有意义的。
Lean 的标准库定义了 {name}`PUnit` 和 {name}`PEmpty`。
要定义可以驻留在 {lean}`Prop` 或 {lean}`Type` 中的子单例，请将选项 {option}`bootstrap.inductiveCheckResultingUniverse` 设置为 {lean}`false`。

{optionDocs bootstrap.inductiveCheckResultingUniverse}

::::keepEnv
:::example "Overly-universe-polymorphic {lean}`Bool`"
不允许定义可以在任何 Universe 中的 {lean}`Bool` 版本：
```lean +error (name := PBool)
inductive PBool : Sort u where
  | true
  | false
```


```leanOutput PBool
Invalid universe polymorphic resulting type: The resulting universe is not `Prop`, but it may be `Prop` for some parameter values:
  Sort u

Hint: A possible solution is to use levels of the form `max 1 _` or `_ + 1` to ensure the universe is of the form `Type _`
```
:::
::::



# 终止检查的结构
%%%
tag := "recursor-elaboration-helpers"
%%%

除了 Lean 的核心 类型论 为归纳类型规定的类型构造函数、构造函数和递归器之外，Lean 还构造了许多有用的帮助程序。
首先，方程编译器（将模式匹配的递归函数转换为递归器的应用程序）使用这些附加构造：
 * `recOn` 是递归器的一个版本，其中每个构造函数的大前提先于小前提。
 * `casesOn` 是递归器的一个版本，其中每个构造函数的大前提先于小前提，并且递归参数不会产生归纳假设。它表达的是案例分析而不是原始递归。
 * `below` 计算一个类型，出于某种动机，表示归纳类型的_所有_居民（大前提的子树）满足该动机。它将归纳或原始递归的动机转变为强递归或强归纳的动机。
 * `brecOn` 是递归器的一个版本，其中 `below` 用于提供对所有子树的访问，而不仅仅是直接递归参数。它代表强感应。
 * `noConfusion` 是一个通用的陈述，从中可以导出构造函数的单射性和不相交性。
 * `noConfusionType` 是 `noConfusion` 的动机，它决定两个构造函数相等的结果。对于单独的构造函数，这是 {lean}`False`；如果两个构造函数相同，则结果是它们各自的参数相等。

这些结构遵循 {citet constructionsOnConstructors}[] 中的描述。

对于 {tech (key := "well-founded recursion")}[良基递归]，拥有可用的通用大小概念通常很有用。
这是在 {name}`SizeOf` 类中捕获的。

{docstring SizeOf}
