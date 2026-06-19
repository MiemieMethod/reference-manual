/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option linter.constructorNameAsVariable false

set_option guard_msgs.diff true

#doc (Manual) "条款" =>
%%%
tag := "terms"
%%%


{deftech}_Terms_ 是在 Lean 中编写数学和程序的主要手段。
{deftech (key := "Lean elaborator")}[精化器] 将它们转换为 Lean 的最小核心语言，然后由内核检查并编译执行。
术语语法为{ref "syntax-ext"}[任意扩展]；本章记录了 Lean 提供的开箱即用的术语语法。

# 标识符
%%%
tag := "identifiers-and-resolution"
%%%

:::syntax term (title := "Identifiers")
```
$x:ident
```
:::

标识符术语是对名称的引用。{margin}[标识符的具体词法语法在 {ref "keywords-and-identifiers"}[有关 Lean 的具体语法的部分]中进行了描述。]
标识符也出现在绑定名称的上下文中，例如 {keywordOf Lean.Parser.Term.let}`let` 和 {keywordOf Lean.Parser.Term.fun}`fun`；然而，这些具有约束力的事件本身并不是完整的术语。
从标识符到名称的映射并不简单：在 {tech}[模块] 中的任何点，一定数量的 {tech}[命名空间] 将打开，可能存在 {tech}[节变量]，并且可能存在本地绑定。
此外，标识符可以包含多个点分隔的原子标识符；点既将命名空间与其内容分隔开，又将变量与使用 {tech}[字段表示法] 的字段或函数分隔开。
这会产生歧义，因为标识符 `A.B.C.D.e.f` 可以指以下任何内容：

 * 命名空间 `A.B.C.D.e` 中的名称 `f`（例如，在 `e` 的 {keywordOf Lean.Parser.Command.declaration}`where` 块中定义的函数）。
 * 如果 `A.B.C.D.e` 的类型为 `T`，则 `T.f` 到 `A.B.C.D.e` 的应用
 * 字段 `f` 从名为 `A.B.C.D.e` 的结构的投影
 * 根据结构值 `A` 进行一系列字段投影 `B.C.D.e`，然后使用字段表示法应用 `f`
 * 如果命名空间 `Q` 已打开，则它可能是对以上任何带有 `Q` 前缀的引用，例如命名空间 `Q.A.B.C.D.e` 中的名称 `f`

此列表并不详尽。
给定标识符，精化器必须发现标识符引用的是哪个名称或哪些名称，以及任何尾随组件是否是通过字段表示法应用的字段或函数。
这个名字叫做{deftech (key := "resolve")}_resolving_。

全局环境中的一些声明是在第一次引用时延迟创建的。
以创建这些声明之一并导致对其引用的方式解析标识符称为 {deftech}_realizing_ 名称。
解析和实现名称的规则是相同的，因此即使本节仅涉及解析名称，它也适用于两者。

名称解析受以下因素影响：
 * {tech (key := "pre-resolved identifier")}[预解析名称] 附加到标识符
 * 附加到标识符的 {tech}[宏范围]
 * 范围内的本地绑定，包括作为 {keywordOf Lean.Parser.Term.letrec}`let rec` 的精化的一部分创建的辅助定义。
 * 在当前模块传递导入的模块中使用 {keywordOf Lean.Parser.Command.export}`export` 创建的别名
 * 当前的 {tech}[节范围]，特别是 {tech}[当前命名空间]、打开的命名空间和节变量


标识符的任何前缀都可以解析为一组名称。
然后，未包含在解析过程中的后缀将被视为场投影或场符号。
较长前缀的解析优先于较短前缀的解析；换句话说，尽可能少的标识符组成部分被视为字段符号。
标识符前缀可以指以下任何一项，较早的项目优先于后面的项目：
 1. 名称与标识符前缀相同的本地绑定变量，包括宏作用域，更接近的本地绑定优先于外部本地绑定。
 2. 名称与标识符前缀相同的本地辅助定义
 3. 名称与标识符前缀相同的 {tech}[节变量]
 3. 与附加到标识符前缀的 {tech}[当前命名空间] 前缀相同的全局名称，或者当前命名空间的前缀中存在别名，当前命名空间的较长前缀优先于较短前缀
 4. 已通过 {keywordOf Lean.Parser.Command.open}`open` 命令纳入范围的全局名称，与标识符前缀相同


如果标识符解析为多个名称，则精化器尝试使用所有这些名称。
如果其中一个成功，则将其用作标识符的含义。
如果多个成功或全部失败，则为错误。

::::keepEnv
:::example "Local Names Take Precedence"
本地绑定优先于全局绑定：
```lean (name := localOverGlobal)
def x := "global"

#eval
  let x := "local"
  x
```
```leanOutput localOverGlobal
"local"
```
名称的最内层本地绑定优先于其他名称：
```lean (name := innermostLocal)
#eval
  let x := "outer"
  let x := "inner"
  x
```
```leanOutput innermostLocal
"inner"
```
:::
::::

::::keepEnv
:::example "Longer Prefixes of Current Namespace Take Precedence"
命名空间 `A`、`B` 和 `C` 是嵌套的。
`A` 和 `C` 都包含 `x` 的定义。
```lean (name := NS)
namespace A
def x := "A.x"
namespace B
namespace C
def x := "A.B.C.x"
```

当当前命名空间为 `A.B.C` 时，{lean}`x` 解析为 {lean}`A.B.C.x`。
```lean (name := NSC)
#eval x
```
```leanOutput NSC
"A.B.C.x"
```
当当前命名空间为 `A.B` 时，{lean}`x` 解析为 {lean}`A.x`。
```lean (name := NSB)
end C
#eval x
```
```leanOutput NSB
"A.x"
```
:::
::::

::::keepEnv
:::example "Longer Identifier Prefixes Take Precedence"
当标识符可以引用名称的不同投影时，名称最长的优先：
```lean
structure A where
  y : String
deriving Repr

structure B where
  y : A
deriving Repr

def y : B := ⟨⟨"shorter"⟩⟩
def y.y : A := ⟨"longer"⟩
```
根据上述声明，{lean}`y.y.y` 原则上可以引用 {name}`y` 的 {name B.y}`y` 字段的 {name A.y}`y` 字段，或者引用 {name}`y.y` 的 {name A.y}`y` 字段。
它引用 {name}`y.y` 的 {name A.y}`y` 字段，因为名称 {name}`y.y` 是比名称 {name}`y` 更长的 `y.y.y` 前缀：
```lean (name := yyy)
#eval y.y.y
```
```leanOutput yyy
"longer"
```
:::
::::

::::keepEnv
:::example "Current Namespace Contents Take Precedence Over Opened Namespaces"
当标识符可以引用当前名称空间前缀中定义的名称或打开的名称空间时，前者优先。
```lean
namespace A
def x := "A.x"
end A

namespace B
def x := "B.x"
namespace C
open A
#eval x
```
尽管 `A` 的打开时间比 {name}`B.x` 的声明更新，但标识符 `x` 解析为 {name}`B.x` 而不是 {name}`A.x`，因为 `B` 是当前命名空间 `B.C` 的前缀。
```lean (name := nestedVsOpen)
#eval x
```
```leanOutput nestedVsOpen
"B.x"
```
:::
::::


:::example "Ambiguous Identifiers"
在此示例中，`x` 可以引用 {name}`A.x` 或 {name}`B.x`，并且两者都不优先。
因为两者具有相同的类型，所以这是一个错误。
```lean (name := ambi) +error
def A.x := "A.x"
def B.x := "B.x"
open A
open B
#eval x
```
```leanOutput ambi (whitespace := lax)
Ambiguous term
  x
Possible interpretations:
  B.x : String

  A.x : String
```
:::


:::example "Disambiguation via Typing"
当其他不明确的名称具有不同的类型时，这些类型用于消除歧义：
```lean (name := ambiNo)
def C.x := "C.x"
def D.x := 3
open C
open D
#eval (x : String)
```
```leanOutput ambiNo
"C.x"
```
:::



## 领先 `.`

当标识符以点 (`.`) 开头时，将使用精化器期望的表达式类型来解析它，而不是使用当前命名空间和开放命名空间集。
{tech}[通用字段表示法] 是相关的：此 {deftech}_前导点表示法_使用标识符的预期类型将其解析为名称，而字段表示法使用紧邻点之前的术语的推断类型。

具有前导 `.` 的标识符将在 {deftech}_expected 类型的命名空间_ 中查找。
如果术语的预期类型是应用于零个或多个参数的常量，则其命名空间就是该常量的名称。
如果该类型不是常量（例如函数、元变量或 Universe）的应用，则它没有命名空间。

如果在预期类型的​​命名空间中找不到该名称，但可以展开该常量以生成另一个常量，则将查阅其命名空间。
重复此过程，直到遇到常量应用以外的情况，或者直到无法展开常量。

::::keepEnv
:::example "Leading `.`"
{name List.replicate}`.replicate` 的预期类型为 `List Unit`。
该类型的命名空间为 `List`，因此 {name List.replicate}`.replicate` 解析为 {name List.replicate}`List.replicate`。
```lean (name := dotRep)
#eval show List Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
:::

:::example "Leading `.` and Unfolding Definitions"
{name List.replicate}`.replicate` 的预期类型为 `MyList Unit`。
该类型的命名空间为 `MyList`，但没有定义 `MyList.replicate`。
展开 {lean}`MyList Unit` 会生成 {lean}`List Unit`，因此 {name List.replicate}`.replicate` 解析为 {name List.replicate}`List.replicate`。
```lean (name := dotRep)
def MyList α := List α
#eval show MyList Unit from .replicate 3 ()
```
```leanOutput dotRep
[(), (), ()]
```
:::
::::

# 功能类型
%%%
tag := "function-types"
%%%

Lean 的函数类型不仅仅描述函数的域和共域。
它们还提供了详细说明应用程序站点的说明，指示某些参数将通过统一或 {ref "instance-synth"}[类型类合成] 自动发现，其他参数是可选的，具有默认值，而其他参数应使用自定义策略脚本进行合成。
此外，它们的语法包含对缩写 {tech (key := "currying")}[curried] 函数的支持。

:::syntax term (title := "Function types")
依赖函数类型包括显式名称：
```grammar
($x:ident : $t) → $t2
```

非依赖函数类型不会：
```grammar
$t1:term → $t2
```
:::

:::syntax term (title := "Curried Function Types")
依赖函数类型可以包含在一组括号中具有相同类型的多个参数：
```grammar
($x:ident* : $t) → $t
```
这相当于为嵌套函数类型中的每个参数名称重复类型注释。
:::

:::syntax term (title := "Implicit, Optional, and Auto Parameters")
函数类型可以描述采用隐式参数、实例隐式参数、可选参数和自动参数的函数。
除实例隐式参数外，所有参数都需要一个或多个名称。
```grammar
($x:ident* : $t := $e) → $t
```
```grammar
($x:ident* : $t := by $tacs) → $t
```
```grammar
{$x:ident* : $t} → $t
```
```grammar
[$t] → $t
```
```grammar
[$x:ident : $t] → $t
```
```grammar
⦃$x:ident* : $t⦄ → $t
```

:::

:::example "Multiple Parameters, Same Type"
{name}`Nat.add`的类型可以这样写：

 * {lean}`Nat → Nat → Nat`

 * {lean}`(a : Nat) → (b : Nat) → Nat`

 * {lean}`(a b : Nat) → Nat`

最后两种类型允许函数与 {tech}[命名参数] 一起使用；除此之外，这三个都是等效的。
:::

# 功能

%%%
tag := "function-terms"
%%%


具有函数类型的术语可以通过抽象创建，通过 {keywordOf Lean.Parser.Term.fun}`fun` 关键字引入。{margin}[在各个社区中，函数抽象也称为 _lambdas_，因为 Alonzo Church 对它们的表示法，或者称为_匿名函数_，因为它们不需要在全局环境中使用名称进行定义。]
虽然核心 类型论 中的抽象仅允许绑定单个变量，但函数术语在高级 Lean 语法中非常灵活。

:::syntax term (title := "Function Abstraction")
最基本的函数抽象引入一个变量来代表函数的参数：

```grammar
fun $x:ident => $t
```

在精化时间，Lean 必须能够确定函数的域。
类型归属是提供此信息的一种方式：

```grammar
fun $x:ident : term => $t
```
:::

使用 {keywordOf Lean.Parser.Command.declaration (parser := Lean.Parser.Command.definition)}`def` desugar 到 {keywordOf Lean.Parser.Term.fun}`fun` 等关键字定义的函数定义。
另一方面，归纳类型声明引入了具有函数类型（构造函数和类型构造函数）的新值，这些值本身不能仅使用 {keywordOf Lean.Parser.Term.fun}`fun` 来实现。

:::syntax term (title := "Curried Functions")


{keywordOf Lean.Parser.Term.fun}`fun` 之后接受多个参数名称：
```grammar
fun $x:ident $x:ident* => $t
```

```grammar
fun $x:ident $x:ident* : $t:term => $t
```

多个参数的不同类型注释需要括号：

```grammar
free{"fun " "(" (ident)* ": " term")" " =>" term}
```

这些相当于编写嵌套的 {keywordOf Lean.Parser.Term.fun}`fun` 项。
:::

在本节中描述的所有语法中，{keywordOf Lean.Parser.Term.fun}`=>` 可以替换为 {keywordOf Lean.Parser.Term.fun}`↦`。

函数抽象还可以使用模式匹配语法作为其参数规范的一部分，从而避免需要引入立即解构的局部变量。
{ref "pattern-fun"}[有关模式匹配的部分]中描述了此语法。

## 隐式参数
%%%
tag := "implicit-functions"
%%%


Lean 支持函数的隐式参数。
这意味着 Lean 本身可以为函数提供参数，而不是要求用户提供所有需要的参数。
隐式参数分为三种：

  : 普通隐式参数

    普通 {deftech}[隐式] 参数是 Lean 应通过统一确定其值的函数参数。
    换句话说，每个调用站点应该恰好有一个潜在的参数值，该值将导致函数调用作为一个整体是正确类型的。
    Lean精化器尝试在函数每次出现时查找所有隐式参数的值。
    普通隐式参数写在花括号中（`{` 和 `}`）。

  : 严格的隐式参数

    {deftech}_Strictimplicit_ 参数与普通隐式参数相同，但 Lean 仅在调用站点提供后续显式参数时才尝试查找参数值。
    严格隐式参数写在双花括号中（`⦃` 和 `⦄`，或 `{{` 和 `}}`）。

  : 实例隐式参数

    {tech}_instance隐式_参数的实参可通过 {ref "instance-synth"}[类型类综合]找到。
    实例隐式参数写在方括号中（`[` 和 `]`）。
    与其他类型的隐式参数不同，不使用 `:` 编写的实例隐式参数指定参数的类型，而不是提供名称。
    此外，只允许使用单个名称。
    大多数实例隐式参数都会省略参数名称，因为作为函数参数合成的实例在函数体内已经可用，即使没有显式命名。

::::keepEnv
:::example "Ordinary vs Strict Implicit Parameters"
函数 {lean}`f` 和 {lean}`g` 之间的区别在于 `α` 严格隐含在 {lean}`f` 中：
```lean
def f ⦃α : Type⦄ : α → α := fun x => x
def g {α : Type} : α → α := fun x => x
```

当应用于具体参数时，这些函数的精化是相同的：
```lean
example : f 2 = g 2 := rfl
```

但是，当未提供显式参数时，使用 {lean}`f` 不需要求解隐式 `α`：
```lean
example := f
```
但`g`的使用确实需要解决，如果信息不足，无法详细说明：
```lean +error (name := noAlpha)
example := g
```
```leanOutput noAlpha
don't know how to synthesize implicit argument `α`
  @g ?m.3
context:
⊢ Type
```
:::
::::


:::syntax term (title := "Functions with Varying Binders")
{keywordOf Lean.Parser.Term.fun}`fun` 最通用的语法接受绑定序列：
```grammar
fun $p:funBinder $p:funBinder* => $t
```
:::


:::syntax Lean.Parser.Term.funBinder (title := "Function Binders")
函数绑定器可以是标识符：
```grammar
$x:ident
```
带括号的标识符序列：
```grammar
($x:ident $y:ident*)
```
具有类型归属的标识符序列：
```grammar
($x:ident $y:ident* : $t)
```
隐式参数，带或不带类型描述：
```grammar
{$x:ident $x:ident*}
```
```grammar
{$x:ident $x:ident* : $t}
```
instance implicits, anonymous or named:
```grammar
[$t:term]
```
```grammar
[$x:ident : $t]
```
或严格的隐式参数，带或不带类型归属：
```grammar
⦃$x:ident $x:ident*⦄
```
```grammar
⦃$x:ident* : $t⦄
```

通常，可以使用 `_` 代替标识符来创建匿名参数，并且可以分别使用 `{{` 和 `}}` 来编写 `⦃` 和 `⦄`。
:::



Lean的核心语言不区分隐式参数、实例参数和显式参数：各种函数和函数类型在定义上是相等的。
仅在精化期间才能观察到差异。

```lean -show
-- Evidence of claims in prior paragraph
example : ({x : Nat} → Nat) = (Nat → Nat) := rfl
example : (fun {x} => 2 : {x : Nat} → Nat) = (fun x => 2 : Nat → Nat) := rfl
example : ([x : Repr Nat] → Nat) = (Repr Nat → Nat) := rfl
example : (⦃x : Nat⦄ → Nat) = (Nat → Nat) := rfl
```


如果函数的预期类型包含隐式参数，但其绑定器不包含，则生成的函数最终可能会比代码中指示的绑定器具有更多参数。
这是因为隐式参数是自动添加的。

:::example "Implicit Parameters from Types"
恒等函数可以用单个显式参数编写。
只要其类型已知，就会自动添加隐式类型参数。
```lean (name := funImplAdd)
#check (fun x => x : {α : Type} → α → α)
```
```leanOutput funImplAdd
fun {α} x => x : {α : Type} → α → α
```

以下都是等效的：
```lean (name := funImplThere)
#check (fun {α} x => x : {α : Type} → α → α)
```
```leanOutput funImplThere
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn)
#check (fun {α} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn
fun {α} x => x : {α : Type} → α → α
```

```lean (name := funImplAnn2)
#check (fun {α : Type} (x : α) => x : {α : Type} → α → α)
```
```leanOutput funImplAnn2
fun {α} x => x : {α : Type} → α → α
```

:::

# 功能应用
%%%
tag := "function-application"
%%%

通常，函数应用程序是使用并置方式编写的：参数放在函数后面，它们之间至少有一个空格。
在 Lean 的 类型论 中，所有函数都只接受一个参数并产生一个值。
所有函数应用程序都将单个函数与单个参数结合起来。
多个参数通过柯里化来表示。

高级术语语言将函数与一个或多个参数一起视为一个单元，并支持其他功能，例如隐式参数、可选参数、按名称参数以及普通位置参数。
精化器将这些转换为核心 类型论 的更简单模型。

:::freeSyntax term (title := "Function Application")
函数应用程序由一项、后跟一个或多个参数、或零个或多个参数以及最后的 {deftech}[省略号] 组成。
```grammar
$e:term $e:argument+
***************
$e:term $e:argument* ".."
```
:::

{TODO}[Annotate with syntax kinds for incoming hyperlinks during traversal pass]
:::freeSyntax Lean.Parser.Term.argument (title := "Arguments")
函数参数可以是术语或 {deftech}[命名参数]。
```grammar
$e:term
***********
"("$x:ident ":=" $e:term")"
```
:::

函数的核心语言类型决定了参数在最终表达式中的位置。
函数类型包括其预期参数的名称。
在Lean的核心语言中，非依赖函数类型被编码为依赖函数类型，其中参数名称不出现在主体中。
此外，它们是内部选择的，因此它们不能写为命名参数的名称；这对于防止意外捕获很重要。

函数期望的每个参数都有一个名称。
重复函数的参数类型，从参数序列中选择参数，如下所示：
 * 如果参数的名称与为命名参数提供的名称匹配，则选择该参数。
 * 如果参数为 {tech}[隐式]，则会使用该参数的类型创建一个新的元变量并选择该元变量。
 * 如果参数是 {tech}[实例隐式]，则使用参数的类型创建一个新的实例元变量并插入。实例元变量安排在稍后综合。
 * 如果参数是 {tech}[严格隐式] 参数，并且存在尚未选择的任何命名或位置参数，则会使用该参数的类型创建一个新的元变量并选择该元变量。
 * 如果参数是显式的，则选择并详细说明下一个位置参数。如果没有位置参数：
   * 如果参数声明为 {tech}[可选参数]，则选择其默认值作为参数。
   * 如果参数是 {tech}[自动参数]，则执行其关联的策略脚本来构造参数。
   * 如果参数既不是可选的也不是自动的，并且不存在省略号，则选择一个新变量作为参数。如果存在省略号，则选择新的元变量，就好像参数是隐式的一样。

作为一种特殊情况，当函数应用程序出现在 {ref "pattern-matching"}[pattern] 中并且存在省略号时，可选参数和自动参数将变为通用模式 (`_`) 而不是被插入。

如果类型不是函数类型并且保留参数，则这是一个错误。
插入所有参数并有省略号后，缺失的参数将全部设置为新的元变量，就像它们是隐式参数一样。
如果为缺少显式位置参数创建了任何新变量，则整个应用程序将包装在绑定它们的 {keywordOf Lean.Parser.Term.fun}`fun` 术语中。
最后，调用实例综合并求解尽可能多的元变量：
 1. 为整个函数应用程序推断类型。这可能会导致一些元变量由于类型推断期间发生的统一而被解决。
 2. 实例元变量被合成。仅当推断类型是作为实例之一的输出参数的元变量时，才使用 {tech}[默认实例]。
 3. 如果有预期类型，则与推断类型统一；然而，由于这种统一而产生的错误将被丢弃。如果预期类型和推断类型可以相等，则统一可以解决剩余的隐式参数元变量。如果它们不相等，则不会引发错误，因为周围的精化器可能能够插入 {tech}[coercions] 或 {tech (key := "lift")}[monad lifts]。


::::keepEnv
:::example "Named Arguments"
```lean -show
set_option linter.unusedVariables false
```
{keywordOf Lean.Parser.Command.check}`#check` 命令可用于检查为函数调用插入的参数。

函数 {name}`sum3` 采用三个显式 {lean}`Nat` 参数，名为 `x`、`y` 和 `z`。
```lean
def sum3 (x y z : Nat) : Nat := x + y + z
```

所有三个参数都可以按位置提供。
```lean (name := sum31)
#check sum3 1 3 8
```
```leanOutput sum31
sum3 1 3 8 : Nat
```

也可以按名称提供它们。
```lean (name := sum32)
#check sum3 (x := 1) (y := 3) (z := 8)
```
```leanOutput sum32
sum3 1 3 8 : Nat
```

当按名称提供参数时，可以按任何顺序。
```lean (name := sum33)
#check sum3 (y := 3) (z := 8) (x := 1)
```
```leanOutput sum33
sum3 1 3 8 : Nat
```

命名参数和位置参数可以自由混合。
```lean (name := sum34)
#check sum3 1 (z := 8) (y := 3)
```
```leanOutput sum34
sum3 1 3 8 : Nat
```

命名参数和位置参数可以自由混合。
如果参数是按名称提供的，则将使用该参数，即使它出现在可能已使用的位置参数之后。
```lean (name := sum342)
#check sum3 1 (x := 8) (y := 3)
```
```leanOutput sum342
sum3 8 3 1 : Nat
```

如果要在未提供的参数之后插入命名参数，则会创建一个函数，在其中填写所提供的参数。
```lean (name := sum35)
#check sum3 (z := 8)
```
```leanOutput sum35
fun x y => sum3 x y 8 : Nat → Nat → Nat
```

在幕后，参数的名称保存在函数类型中。
这意味着剩余的参数可以再次按名称传递。
```lean (name := sum36)
#check (sum3 (z := 8)) (y := 1)
```
```leanOutput sum36
fun x => (fun x y => sum3 x y 8) x 1 : Nat → Nat
```

参数名称取自函数的_type_，并且函数参数使用的名称不需要与类型中使用的名称匹配。
这意味着与参数名称冲突的本地绑定不会阻止使用命名参数，因为 Lean 通过重命名函数的参数同时在类型中保持名称不变来避免这种冲突。
```lean (name := sum15)
#check let x := 15; sum3 (z := x)
```
这里，命名 {name}`sum3` 第一个参数的 `x` 已被替换，以免与周围的 {keywordOf Parser.Term.let}`let` 冲突：
```leanOutput sum15
let x := 15;
fun x_1 y => sum3 x_1 y x : Nat → Nat → Nat
```
即使`x`被重命名，它仍然可以通过名称传递：
```lean (name := xNoCapture)
#check (let x := 15; sum3 (z := x)) (x := 4)
```
```leanOutput xNoCapture
(let x := 15;
  fun x_1 y => sum3 x_1 y x)
  4 : Nat → Nat
```
这是因为该类型中仍使用名称 `x`。
启用选项 {option}`pp.piBinderNames` 显示类型中的参数名称：
```lean (name := xRenamed)
set_option pp.piBinderNames true in
#check let x := 15; sum3 (z := x)
```
```leanOutput xRenamed
let x := 15;
fun x_1 y => sum3 x_1 y x : (x y : Nat) → Nat
```
:::
::::


可选参数和自动参数不是 Lean 核心 类型论 的一部分。
它们使用 {name}`optParam` 和 {name}`autoParam` {tech}[gadgets] 进行编码。

{docstring optParam}

{docstring autoParam}

## 广义字段表示法
%%%
tag := "generalized-field-notation"
%%%

{ref "structure-fields"}[关于结构字段的部分]描述了从类型为结构的术语投影字段的表示法。
通用字段表示法由一个术语后跟一个点 (`.`) 和一个标识符组成，不以空格分隔。

:::syntax term (title := "Field Notation")
```grammar
$e:term.$f:ident
```
:::

如果术语的类型是应用于零个或多个参数的常量，则 {deftech}[field notation] 可用于向其应用函数，无论该术语是具有字段的结构还是类型类实例。
使用字段表示法来应用其他函数称为 {deftech}_广义字段表示法_。

在术语类型的命名空间中查找点后面的标识符，这是常量的名称。
如果该类型不是常量的应用（例如元变量或 Universe），则它没有命名空间，并且不能使用通用字段表示法。
作为一种特殊情况，如果表达式是函数，则通用字段表示法将在 `Function` 命名空间中查找。因此，{lean}`Nat.add.uncurry` 是等效于 {lean}`Function.uncurry Nat.add` 的广义字段表示法的使用。

如果未找到该字段，但可以展开常量以产生另一种类型，即常量或常量的应用，则使用新常量重复该过程。

当找到一个函数时，点之前的项将成为该函数的参数。
具体来说，它成为第一个不会出现类型错误的显式参数。
除此之外，该应用程序像往常一样详细说明。

:::example "Generalized Field Notation"
类型 {lean}`Username` 是常量，因此 {name}`Username` 命名空间中的函数可以应用于具有通用字段表示法的 {lean}`Username` 类型的项。
```lean
def Username := String
```

其中一个函数是 {name}`Username.validate`，它检查用户名是否不包含前导空格，并且仅使用一小组可接受的字符。
在其定义中，通用字段表示法用于调用函数 {lean}`String.isPrefixOf`、{name}`String.any`、{lean}`Char.isAlpha` 和 {lean}`Char.isDigit`。
对于 {lean}`String.isPrefixOf`，它采用两个 {lean}`String` 参数，{lean}`" "` 用作第一个参数，因为它是点之前的项。
即使 {name}`String.any` 的类型为 {lean}`Username`，也可以使用通用字段表示法在 {lean}`name` 上调用 {name}`String.any`，因为未定义 `Username.any` 并且 {lean}`Username` 展开为 {lean}`String`。

```lean
def Username.validate (name : Username) : Except String Unit := do
  if " ".isPrefixOf name then
    throw "Unexpected leading whitespace"
  if name.any notOk then
    throw "Unexpected character"
  return ()
where
  notOk (c : Char) : Bool :=
    !c.isAlpha &&
    !c.isDigit &&
    !c ∈ ['_', ' ']

def adminUser : Username := "admin"
```

但是，无法使用字段表示法在 {lean}`"root"` 上调用 {lean}`Username.validate`，因为 {lean}`String` 不会展开为 {lean}`Username`。
```lean +error (name := notString)
#eval "admin".validate
```
```leanOutput notString
Invalid field `validate`: The environment does not contain `String.validate`, so it is not possible to project the field `validate` from an expression
  "admin"
of type `String`
```

另一方面，{lean}`adminUser` 的类型为 {lean}`Username`，因此可以使用通用字段表示法调用 {lean}`Username.validate` 函数：
```lean (name := isUsername)
#eval adminUser.validate
```
```leanOutput isUsername
Except.ok ()
```

从另一个方向来看，{name}`String.any` *可以*使用广义字段表示法对 {lean}`Username` 值 {lean}`adminUser` 进行调用，因为类型 {lean}`Username` 展开为 {lean}`String`。
```lean (name := isString1)
#eval adminUser.any (· == 'm')
```
```leanOutput isString1
true
```
:::

{optionDocs pp.fieldNotation}

:::syntax attr (title := "Controlling Field Notation")
{attr}`pp_nodot` 属性导致 Lean 的漂亮打印机在打印函数时不使用字段表示法。
```grammar
pp_nodot
```
:::

::::keepEnv
:::example "Turning Off Field Notation"
默认情况下，{lean}`Nat.half` 使用字段符号打印。
```lean
def Nat.half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => n.half + 1
```
```lean (name := succ1)
#check Nat.half Nat.zero
```
```leanOutput succ1
Nat.zero.half : Nat
```
将 {attr}`pp_nodot` 添加到 {name}`Nat.half` 会导致在显示术语时改用普通函数应用程序语法。
```lean (name := succ2)
attribute [pp_nodot] Nat.half

#check Nat.half Nat.zero
```
```leanOutput succ2
Nat.half Nat.zero : Nat
```
:::
::::

## 管道语法

管道语法提供了编写函数应用程序的替代方法。
重复管道使用解析优先级而不是嵌套括号来将函数应用程序嵌套到位置参数。

:::syntax term (title := "Pipelines")
右管道符号将管道右侧的术语应用于其左侧的术语。
```grammar
$e |> $e
```
左管道符号将管道左侧的术语应用于其右侧的术语。
```grammar
$e <| $e
```
:::

右侧管道符号背后的直觉是，左侧的值被馈送到第一个函数，其结果被馈送到第二个函数，依此类推。
在左管道表示法中，右侧的值向左馈送。

:::example "Right pipeline notation"
正确的管道可用于调用一个术语上的一系列函数。
对于读者来说，他们倾向于强调正在转换的数据。
```lean (name := rightPipe)
#eval "Hello!" |> String.toList |> List.reverse |> List.head!
```
```leanOutput rightPipe
'!'
```
:::

:::example "Left pipeline notation"
左管道可用于调用某个术语的一系列函数。
他们倾向于强调功能而不是数据。
```lean (name := lPipe)
#eval List.head! <| List.reverse <| String.toList <| "Hello!"
```
```leanOutput lPipe
'!'
```
:::

:::syntax term (title := "Pipeline Fields")
有一个版本的管道表示法用于 {tech}[通用字段表示法]。
```grammar
$e |>.$_:ident
```
```grammar
$e |>.$_:fieldIdx
```
:::

::::keepEnv
```lean -show
section
universe u
axiom T : Nat → Type u
variable {e : T 3} {arg : Char}
axiom T.f : {n : Nat} → Char → T n → String
```

{lean}`e |>.f arg` 是 {lean}`(e).f arg` 的替代语法。


:::example "Pipeline Fields"

有些函数不方便与管道一起使用，因为它们的参数顺序不利。
例如，{name}`Array.push` 采用数组作为其第一个参数，而不是 {lean}`Nat`，从而导致此错误：
```lean (name := arrPush) +error
#eval #[1, 2, 3] |> Array.push 4
```
```leanOutput arrPush
failed to synthesize instance of type class
  OfNat (Array ?m.2) 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  Array ?m.2
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

使用管道字段表示法会导致数组被插入到第一个类型正确的位置：
```lean (name := arrPush2)
#eval #[1, 2, 3] |>.push 4
```
```leanOutput arrPush2
#[1, 2, 3, 4]
```

这个过程可以迭代：
```lean (name := arrPush3)
#eval #[1, 2, 3] |>.push 4 |>.reverse |>.push 0 |>.reverse
```
```leanOutput arrPush3
#[0, 1, 2, 3, 4]
```
:::


```lean -show
end
```
::::

# 数字文字

有两种数字文字：自然数文字和 {deftech}[科学文字]。
两者均通过 {tech (key := "type class")}[类型类] 重载。

## 自然数
%%%
tag := "nat-literals"
%%%

```lean -show
section
variable {n : Nat}
```

自然数可以多种形式指定：

 - 0 到 9 的数字序列是十进制文字
 - `0b` 或 `0B` 后跟一个或多个 0 和 1 的序列是二进制文字
 - `0o` 或 `0O` 后跟一个或多个数字 0 到 7 的序列是八进制文字
 - `0x` 或 `0X` 后跟一系列一个或多个十六进制数字（0 到 9 以及 A 到 F，不区分大小写）是十六进制文字

所有数字文字也可以包含内部下划线，二进制、八进制或十六进制文字中的前两个字符之间除外。
这些旨在以自然的方式帮助数字组，例如 {lean}`1_000_000` 或 {lean}`0x_c0de_cafe`。
（虽然可以将数字 123 写为 {lean}`1_2__3`，但不建议这样做。）

当 Lean 遇到自然数文字 {lean}`n` 时，它通过重载方法 {lean}`OfNat.ofNat n` 对其进行解释。
{lean}`OfNat Nat n` 的 {tech}[默认实例] 确保在不存在其他类型信息时可以推断类型 {lean}`Nat`。

{docstring OfNat}

```lean -show
end
```

:::example "Custom Natural Number Literals"
结构体{lean}`NatInterval`表示自然数的区间。
```lean
structure NatInterval where
  low : Nat
  high : Nat
  low_le_high : low ≤ high

instance : Add NatInterval where
  add
    | ⟨lo1, hi1, le1⟩, ⟨lo2, hi2, le2⟩ =>
      ⟨lo1 + lo2, hi1 + hi2, by grind⟩
```

{name}`OfNat` 实例允许使用自然数文字来表示间隔：
```lean
instance : OfNat NatInterval n where
  ofNat := ⟨n, n, by omega⟩
```
```lean (name := eval8Interval)
#eval (8 : NatInterval)
```
```leanOutput eval8Interval
{ low := 8, high := 8, low_le_high := _ }
```
```lean (name := eval7Interval)
#eval (0b111 : NatInterval)
```
```leanOutput eval7Interval
{ low := 7, high := 7, low_le_high := _ }
```
:::

没有单独的整数文字。
诸如 {lean}`-5` 之类的术语由应用于自然数文字的前缀否定（可以通过 {name}`Neg` 类型类重载）组成。

## 科学数字

科学数字文字由一系列十进制数字组成，后跟（不插入空格）可选的小数部分（句号后跟零个或多个十进制数字）和可选的指数部分（字母 `e` 后跟可选的 `+` 或 `-`，然后后跟一个或多个十进制数字）。
科学数字通过 {name}`OfScientific` 类型类重载。

{docstring OfScientific}

{name}`Float` 和 {name}`Float32` 有一个 {lean}`OfScientific` 实例，但没有单独的浮点文字。

## 弦乐

字符串文字在 {ref "string-syntax"}[字符串章节]中进行了描述。

## 列表和数组

列表和数组文字包含括号内以逗号分隔的元素序列，数组以哈希标记 (`#`) 为前缀。
数组文字被解释为包含在转换调用中的列表文字。
出于性能原因，非常大的列表和数组文字会转换为局部定义序列，而不仅仅是列表构造函数的迭代应用程序。

:::syntax term (title := "List Literals")
```grammar
[$_,*]
```
:::

:::syntax term (title := "Array Literals")
```grammar
#[$_,*]
```
:::

:::example "Long List Literals"
该列表包含 32 个元素。
生成的代码是{name}`List.cons`的迭代应用：
```lean (name := almostLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1]
```
```leanOutput almostLong
[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List Nat
```

具有 33 个元素的列表文字成为局部定义的序列：
```lean (name := indeedLong)
#check
  [1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1,1,1,1,1,1,1,1,
   1]
```
```leanOutput indeedLong
let y :=
  let y :=
    let y := [1, 1, 1, 1, 1];
    1 :: 1 :: 1 :: 1 :: y;
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y :=
  let y := 1 :: 1 :: 1 :: 1 :: y;
  1 :: 1 :: 1 :: 1 :: y;
let y := 1 :: 1 :: 1 :: 1 :: y;
1 :: 1 :: 1 :: 1 :: y : List Nat
```

:::

# 结构和构造函数

{ref "anonymous-constructor-syntax"}[匿名构造函数] 和 {ref "structure-constructors"}[结构实例语法] 在各自的部分中进行了描述。

# 条件句
%%%
tag := "if-then-else"
%%%

条件表达式用于检查命题是真还是假。{margin}[尽管语法相似，但 {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` 使用 {ref "tactic-language-branching"}[在策略语言中]，而 {keywordOf Lean.Parser.Term.doIf}`if` 使用 {ref "tactic-language-branching"}[在`do`-notation] 是单独的语法形式，记录在它们自己的部分中。]
这要求该命题具有 {name}`Decidable` 实例，因为无法检查_任意_命题是真还是假。
还有一个从 {name}`Bool` 到 {lean}`Prop` 的 {tech}[强制]，它会产生可判定的命题（即，所讨论的 {name}`Bool` 等于 {name}`true`），如 {ref "decidable-propositions"}[关于可判定性的部分]中所述。

条件表达式有两种版本：一种仅执行大小写区分，而另一种则另外在本地上下文中添加有关命题真假的假设。
这允许运行时检查生成可用于静态排除错误的编译时证据。

:::syntax term (title := "Conditionals")
如果没有名称注释，条件表达式仅表达控制流。
```grammar
if $e then
  $e
else
  $e
```

通过名称注释，{keywordOf termDepIfThenElse}`if` 的分支可以访问命题分别为真或假的局部假设。
```grammar
if $h : $e then
  $e
else
  $e
```
:::


::::keepEnv
:::example "Checking Array Bounds"

数组索引需要证据证明相关索引在数组范围内，因此 {name}`getThird` 没有详细说明。

```lean +error -keep (name := getThird1)
def getThird (xs : Array α) : α := xs[2]
```
```leanOutput getThird1
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

将返回类型放宽为 {name}`Option` 并添加边界检查会导致相同的错误。
这是因为索引在边界内的证明没有添加到本地上下文中。
```lean +error -keep (name := getThird2)
def getThird (xs : Array α) : Option α :=
  if xs.size ≤ 2 then none
  else xs[2]
```
```leanOutput getThird2
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.7
xs : Array α
⊢ 2 < xs.size
```

将证明命名为 `h` 足以使执行边界检查的策略成功，即使它没有在程序文本中明确出现。
```lean
def getThird (xs : Array α) : Option α :=
  if h : xs.size ≤ 2 then none
  else xs[2]
```

:::
::::

还有 {keywordOf termIfLet}`if` 的模式匹配版本。
如果模式匹配，则它采用第一个分支，绑定模式变量。
如果模式不匹配，则采用第二个分支。

:::syntax term (title := "Pattern-Matching Conditionals")
```grammar
if let $p := $e then
  $e
else
  $e
```
:::


如果需要仅 {name}`Bool` 的条件语句，则可以使用 {keywordOf boolIfThenElse}`bif` 变体。
:::syntax term (title := "Boolean-Only Conditional")
```grammar
bif $e then
  $e
else
  $e
```
:::


# 模式匹配
%%%
tag := "pattern-matching"
%%%


{deftech}_Patternmatching_ 是一种使用 {deftech}_patterns_ 语法来识别和解构值的方法，{deftech}_patterns_ 是术语的子集。
识别和解构值的模式类似于用于构造值的语法。
一个或多个 {deftech}_match 判别式_同时与一系列 {deftech}_match 替代方案_进行比较。
判别式可以被命名。
每个替代项都包含一个或多个以逗号分隔的模式序列；所有模式序列必须包含与判别式相同数量的模式。
当模式序列与所有判别式匹配时，在用每个 {tech}[模式变量] 的值以及每个命名判别式的等式假设扩展的环境中评估相应 {keywordOf Lean.Parser.Term.match}`=>` 后面的项。
该术语称为匹配替代项的 {deftech}_right-hand side_。

:::syntax term (title := "Pattern Matching")
```grammar
match
    $[(generalizing := $e)]?
    $[(motive := $e)]?
    $[$d:matchDiscr],*
  with
$[| $[$e,*]|* => $e]*
```
:::

:::syntax matchDiscr (title := "Match Discriminants") -open
```grammar
$e:term
```
```grammar
$h:ident : $e:term
```
:::

模式匹配表达式也可以使用 {tech}[quasiquotations] 作为模式，匹配相应的 {name}`Lean.Syntax` 值并将 {tech}[antiquotations] 的内容视为普通模式。
引用模式的编译方式与其他模式不同，因此如果 {keywordOf Lean.Parser.Term.match}`match` 中的一种模式是语法，那么所有模式都必须是语法。
报价模式在 {ref "quote-patterns"}[报价部分]中描述。

模式是术语的子集。
它们由以下部分组成：

: 包罗万象的模式

  空洞语法 {lean}`_` 是一种匹配任何值且不绑定任何模式变量的模式。
  包罗万象的模式并不完全等同于未使用的模式变量。
  它们可以用在模式输入需要更具体的 {tech}[无法访问的模式]的位置，而变量不能在这些位置使用。

: 标识符

  如果标识符未绑定在当前范围内且未应用于参数，则它表示模式变量。
  {deftech}_Pattern 变量_ 匹配任何值，并且如此匹配的值将绑定到计算 {tech}[右侧] 的本地环境中的模式变量。
  如果标识符已绑定，则如果它绑定到 {tech}[归纳类型] 的 {tech}[构造函数]，或者其定义具有 {attr}`match_pattern` 属性，则它是一个模式。

: 应用领域

  如果所应用的函数是绑定到构造函数的标识符或具有 {attr}`match_pattern` 属性并且所有参数也是模式，则函数应用程序是模式。
  如果标识符是构造函数，则当参数模式与构造函数的参数匹配时，模式将匹配使用该构造函数构建的值。
  如果它是具有 {attr}`match_pattern` 属性的函数，则展开函数应用程序，并将结果项的 {tech}[正规形式] 用作模式。
  默认参数照常插入，并且它们的正常形式用作模式。
  然而，{tech (key := "ellipsis")}[省略号] 会导致所有其他参数被视为通用模式，即使是那些具有关联默认值或策略的参数。

: 文字

  {ref "char-syntax"}[字符文字] 和 {ref "string-syntax"}[字符串文字] 是与相应字符或字符串匹配的模式。
  {ref "raw-string-literals"}[原始字符串文字] 允许作为模式，但 {ref "string-interpolation"}[插值字符串] 不允许作为模式。
  模式中的 {ref "nat-syntax"}[自然数文字] 通过合成相应的 {name}`OfNat` 实例并将结果项减少为 {tech}[正常形式]（它必须是模式）来解释。
  同样，{tech}[科学文字] 通过相应的 {name}`OfScientific` 实例进行解释。
  虽然 {lean}`Float` 有这样的实例，但 {lean}`Float` 不能用作模式，因为该实例依赖于无法简化为有效模式的不透明函数。

: 结构实例

  {tech}[结构实例]可以用作模式。
  它们被解释为相应的结构构造函数。

: 引用的名字

  Quoted names, such as {lean}`` `x `` and {lean}``` ``none ```, match the corresponding {name}`Lean.Name` value.

: 宏

  模式中的宏被扩展。
  如果产生的扩展是模式，那么它们就是模式。

: 无法访问的模式

  {deftech}[不可访问的模式] 是通过稍后键入约束而强制具有特定值的模式。
  任何术语都可以用作不可访问的术语。
  无法访问的术语用括号括起来，前面带有句点 (`.`)。

:::syntax term (title := "Inaccessible Patterns")
```grammar
.($e)
```
:::

:::example "Inaccessible Patterns"
数字的_奇偶性_是它是偶数还是奇数：
```lean
inductive Parity : Nat → Type where
  | even (h : Nat) : Parity (h + h)
  | odd (h : Nat) : Parity ((h + h) + 1)

def Nat.parity (n : Nat) : Parity n :=
  match n with
  | 0 => .even 0
  | n' + 1 =>
    match n'.parity with
    | .even h => .odd h
    | .odd h =>
      have eq : (h + 1) + (h + 1) = (h + h + 1 + 1) :=
        by omega
      eq ▸ .even (h + 1)
```

由于 {lean}`Parity` 类型的值包含数字的一半（向下舍入）作为其偶数或奇数表示的一部分，因此可以通过查找奇偶校验然后提取数字来实现除以二（以非常规方式）。
```lean
def half (n : Nat) : Nat :=
  match n, n.parity with
  | .(h + h),     .even h => h
  | .(h + h + 1), .odd h  => h
```
由于 {name}`Parity.even` 和 {name}`Parity.odd` 的索引结构强制数字具有某种形式，否则该形式不是有效模式，因此与其匹配的模式必须对被除数使用不可访问的模式。
:::

还可以对模式进行命名。
{deftech}[命名模式]将名称与模式关联起来；在后续模式中以及匹配替代项的右侧，名称指的是与给定模式匹配的值的部分。
命名模式在名称和模式之间写入 `@`。
就像判别式一样，命名模式也可以提供用于相等假设的名称。

:::syntax term (title := "Named Patterns")
```grammar
$x:ident@$e
```
```grammar
$x:ident@$h:ident:$e
```
:::


```lean -show -keep
-- Check claims about patterns

-- Literals
/-- error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]` -/
#guard_msgs in
def foo (x : String) : String :=
  match x with
  | "abc" => ""
  | r#"hey"# => ""
  | s!"a{x}y" => _
  | _ => default

structure Blah where
  n : Nat
deriving Inhabited

instance : OfNat Blah n where
  ofNat := ⟨n + 1⟩

/--
error: Missing cases:
(Blah.mk Nat.zero)
(Blah.mk (Nat.succ (Nat.succ _)))
-/
#check_msgs in
def abc (n : Blah) : Bool :=
  match n with
  | 0 => true

partial instance : OfNat Blah n where
  ofNat :=
    let rec f (x : Nat) : Blah :=
      match x with
      | 0 => f 99
      | n + 1 => f n
    f n

-- This shows that the partial instance was not unfolded
/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive (instOfNatBlah_1.f 0)
but is expected to have type
  motive n✝
-/
#check_msgs in
def defg (n : Blah) : Bool :=
  match n with
  | 0 => true

/--
error: Dependent elimination failed: Type mismatch when solving this alternative: it has type
  motive (Float.ofScientific 25 true 1)
but is expected to have type
  motive x✝
-/
#check_msgs in
def twoPointFive? : Float → Option Float
  | 2.5 => some 2.5
  | _ => none

/--
info: @Neg.neg.{0} Float instNegFloat
  (@OfScientific.ofScientific.{0} Float instOfScientificFloat (nat_lit 320) Bool.true (nat_lit 1)) : Float
-/
#check_msgs in
set_option pp.all true in
#check -32.0

structure OnlyThreeOrFive where
  val : Nat
  val2 := false
  ok : val = 3 ∨ val = 5 := by rfl


-- Default args are not synthesized in patterns
/--
error: Fields missing: `val2`, `ok`
-/
#check_msgs in
def ggg : OnlyThreeOrFive → Nat
  | {val := n} => n

/--
error: Fields missing: `val2`
-/
#check_msgs in
def hhh : OnlyThreeOrFive → Nat
  | {val := n, ok := p} => n

-- Ellipses don't synth default args in patterns
def ggg' : OnlyThreeOrFive → Nat
  | .mk n .. => n

-- Ellipses do synth default args via tactics, but not exprs, otherwise
/--
error: could not synthesize default value for parameter 'ok' using tactics
---
error: Tactic `rfl` failed: The left-hand side
  3 = 3
is not definitionally equal to the right-hand side
  3 = 5

⊢ 3 = 3 ∨ 3 = 5
---
info: { val := 3, val2 := ?m.2647, ok := ⋯ } : OnlyThreeOrFive
-/
#check_msgs in
#check OnlyThreeOrFive.mk 3 ..

/-- info: { val := 3, val2 := ?_, ok := ⋯ } : OnlyThreeOrFive -/
#check_msgs in
set_option pp.mvars.anonymous false in
#check OnlyThreeOrFive.mk 3 (ok := .inl rfl) ..

/--
info: fun y =>
  match
    have this := ⟨y * 3, ⋯⟩;
    this with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), ⋯ => () : Nat → Unit
-/
#check_msgs in
#check fun (y : Nat) => match show {n : Nat// n = y * 3} from ⟨y*3, rfl⟩ with
  | ⟨x, z⟩ =>
    match x, z with
    | .(y * 3), rfl => ()

```

## 类型

每个判别式都必须有良好的类型。
由于模式是术语的子集，因此也可以检查它们的类型。
与给定判别式匹配的每个模式必须与相应的判别式具有相同的类型。

每个匹配替代项的 {tech}[右侧] 应具有与整体 {keywordOf Lean.Parser.Term.match}`match` 术语相同的类型。
为了支持 依值类型，将判别式与模式匹配可以细化模式范围内预期的类型。
在同一匹配替代项和右侧类型中的两个后续模式中，判别式的出现将被替换为它所匹配的模式。


::::keepEnv
```lean -show
variable {α : Type u}
```

:::example "Type Refinement"
这个 {tech}[索引族] 描述了大部分平衡的树，深度编码在类型中。
```lean
inductive BalancedTree (α : Type u) : Nat → Type u where
  | empty : BalancedTree α 0
  | branch
    (left : BalancedTree α n)
    (val : α)
    (right : BalancedTree α n) :
    BalancedTree α (n + 1)
  | lbranch
    (left : BalancedTree α (n + 1))
    (val : α)
    (right : BalancedTree α n) :
    BalancedTree α (n + 2)
  | rbranch
    (left : BalancedTree α n)
    (val : α)
    (right : BalancedTree α (n + 1)) :
    BalancedTree α (n + 2)
```

要开始实现函数来构造具有某些初始元素和给定深度的完美平衡树，可以使用 {tech}[hole] 进行定义。
```lean -keep (name := fill1) +error
def BalancedTree.filledWith
    (x : α) (depth : Nat) :
    BalancedTree α depth :=
  _
```
错误消息表明树应该具有指示的深度。
```leanOutput fill1
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α depth
```

匹配预期深度并插入孔会导致每个孔出现错误消息。
这些消息表明预期类型已被细化，`depth` 被匹配的值替换。
```lean +error (name := fill2)
def BalancedTree.filledWith
    (x : α) (depth : Nat) :
    BalancedTree α depth :=
  match depth with
  | 0 => _
  | n + 1 => _
```
第一个洞产生以下消息：
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth : Nat
⊢ BalancedTree α 0
```
第二个洞产生以下消息：
```leanOutput fill2
don't know how to synthesize placeholder
context:
α : Type u
x : α
depth n : Nat
⊢ BalancedTree α (n + 1)
```

树的深度和树本身的匹配会根据深度的模式对树的类型进行细化。
这意味着某些组合的类型不正确，例如 {lean}`0` 和 {name BalancedTree.branch}`branch`，因为细化第二个判别式的类型会生成与构造函数的类型不匹配的 {lean}`BalancedTree α 0`。
```lean (name := patfail) +error
def BalancedTree.isPerfectlyBalanced
    (n : Nat) (t : BalancedTree α n) : Bool :=
  match n, t with
  | 0, .empty => true
  | 0, .branch left val right =>
    isPerfectlyBalanced left &&
    isPerfectlyBalanced right
  | _, _ => false
```
```leanOutput patfail
Type mismatch
  left.branch val right
has type
  BalancedTree ?m.54 (?m.51 + 1)
but is expected to have type
  BalancedTree α 0
```
:::
::::

### 模式相等性证明

当命名判别式时，{keywordOf Lean.Parser.Term.match}`match` 会生成模式和判别式相等的证明，并将其绑定到 {tech}[右侧] 中提供的名称。
这对于弥合索引系列上的依赖模式匹配与需要显式命题参数的 API 之间的差距非常有用，并且可以帮助利用假设的策略取得成功。

:::example "Pattern Equality Proofs"
函数 {lean}`last?` 使用标准库函数 {lean}`List.getLast`，它要么引发异常，要么返回其参数的最后一个元素。
此函数需要证明所讨论的列表非空。
将比赛命名为 `xs` 可确保范围内存在一个假设，即 `xs` 等于 `_ :: _`，{tactic}`simp_all` 使用该假设来实现目标。
```lean
def last? (xs : List α) : Except String α :=
  match h : xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```

没有名字，{tactic}`simp_all`就无法找到矛盾。
```lean +error (name := namedHyp)
def last?' (xs : List α) : Except String α :=
  match xs with
  | [] =>
    .error "Can't take first element of empty list"
  | _ :: _ =>
    .ok <| xs.getLast (show xs ≠ [] by intro h'; simp_all)
```
```leanOutput namedHyp
simp_all made no progress
```
:::

### 明确的动机

模式匹配不是 Lean 的内置原语。
相反，它通过 {tech}[辅助匹配函数] 转换为 {tech}[递归器] 的应用程序。
两者都需要 {tech}_motive_ 来解释判别式和结果类型之间的关系。
一般来说，{keywordOf Lean.Parser.Term.match}`match`精化器能够合成适当的动机，并且模式匹配期间发生的类型细化是所选动机的结果。
在某些特殊情况下，可能需要不同的动机，并且可以使用 {keywordOf Lean.Parser.Term.match}`match` 的 `(motive := …)` 语法显式提供。
这个动机应该是一个函数类型，它期望至少与判别式一样多的参数。
将具有此类型的函数按顺序应用于判别式所产生的类型是整个 {keywordOf Lean.Parser.Term.match}`match` 项的类型，而将具有此类型的函数应用于每个替代中的所有模式所产生的类型是该替代的 {tech}[右侧] 的类型。

:::example "Matching with an Explicit Motive"
显式动机可用于提供从周围上下文中无法获得的类型信息。
尝试匹配数字和证明它实际上是 {lean}`5` 是一个错误，因为没有理由将数字连接到证明：
```lean +error (name := noMotive)
#eval
  match 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput noMotive
Invalid match expression: This pattern contains metavariables:
  Eq.refl ?m.76
```
一个明确的动机解释了判别式之间的关系：
```lean (name := withMotive)
#eval
  match (motive := (n : Nat) → n = 5 → String) 5, rfl with
  | 5, rfl => "ok"
```
```leanOutput withMotive
"ok"
```
:::

### 判别式细化

当匹配索引族时，索引也必须是判别式。
否则，该模式的类型不会很好：如果索引只是一个变量但构造函数的类型需要更具体的值，则这是一个类型错误。
然而，一个名为 {deftech}[判别细化] 的过程会自动添加索引作为附加判别式。

::::keepEnv
:::example "Discriminant Refinement"
在 {lean}`f` 的定义中，等式证明是唯一的判别式。
然而，相等是一个索引族，并且仅当 `n` 是附加判别式时匹配才有效。
```lean
def f (n : Nat) (p : n = 3) : String :=
  match p with
  | rfl => "ok"
```
使用 {keywordOf Lean.Parser.Command.print}`#print` 表明附加判别式是自动添加的。
```lean (name := fDef)
#print f
```
```leanOutput fDef
def f : (n : Nat) → n = 3 → String :=
fun n p =>
  match 3, p with
  | .(n), ⋯ => "ok"
```
:::
::::

### 概括
%%%
tag := "match-generalization"
%%%

模式匹配精化器通过查找预期类型中判别式的出现来自动确定动机，将它们概括为后续判别式的类型，以便可以替换适当的模式。
此外，默认情况下，上下文中变量类型中判别式的出现将被概括和替换。
可以通过将 `(generalizing := false)` 标志传递给 {keywordOf Lean.Parser.Term.match}`match` 来关闭后一种行为。

:::::keepEnv
::::example "Matching, With and Without Generalization"
```lean -show
variable {α : Type u} (b : Bool) (ifTrue : b = true → α) (ifFalse : b = false → α)
```
在 {lean}`boolCases` 的定义中，假设 {lean}`b` 被概括为 `h` 的类型，然后替换为实际模式。
这意味着 {lean}`ifTrue` 和 {lean}`ifFalse` 在各自的情况下具有类型 {lean}`true = true → α` 和 {lean}`false = false → α`，但 `h` 的类型提到了原始判别式。

```lean +error (name := boolCases1) -keep
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
第一种情况的错误是两种情况的典型错误：
```leanOutput boolCases1
Application type mismatch: The argument
  h
has type
  b = true
but is expected to have type
  true = true
in the application
  ifTrue h
```
关闭泛化可以使类型检查成功，因为 {lean}`b` 仍保留在 {lean}`ifTrue` 和 {lean}`ifFalse` 的类型中。
```lean
def boolCases (b : Bool)
    (ifTrue : b = true → α)
    (ifFalse : b = false → α) :
    α :=
  match (generalizing := false) h : b with
  | true  => ifTrue h
  | false => ifFalse h
```
在通用版本中，{name}`rfl` 可以用作证明参数作为替代方案。
::::
:::::

## 自定义模式功能
%%%
tag := "match_pattern-functions"
%%%

```lean -show
section
variable {n : Nat}
```

在模式中，使用 {attr}`match_pattern` 属性定义的常量将展开并规范化，而不是拒绝。
这允许对许多模式使用更方便的语法。
在标准库中，{name}`Nat.add`、{name}`HAdd.hAdd`、{name}`Add.add` 和 {name}`Neg.neg` 都具有此属性，该属性允许像 {lean}`n + 1` 这样的模式而不是 {lean}`Nat.succ n`。
类似地，{name}`Unit`和{name}`Unit.unit`是将{name}`PUnit`和{name}`PUnit.unit`各自的{tech}[宇宙参数]设置为0的定义； {name}`Unit.unit` 上的 {attr}`match_pattern` 属性允许其在模式中使用，并扩展为 {lean}`PUnit.unit.{0}`。

:::syntax attr (title := "Attribute for Match Patterns")
{attr}`match_pattern` 属性指示应在模式中展开而不是拒绝定义。
```grammar
match_pattern
```
:::

::::keepEnv
```lean -show
section
variable {k : Nat}
```
:::example "Match Patterns Follow Reduction"
以下函数无法编译：
```lean +error (name := nonPat)
def nonzero (n : Nat) : Bool :=
  match n with
  | 0 => false
  | 1 + k => true
```
模式 `1 + _` 上的错误消息是：
```leanOutput nonPat
Invalid pattern(s): `k` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 1 k)
```

这是因为 {name}`Nat.add` 是通过其第二个参数的递归定义的，相当于：
```lean
def add : Nat → Nat → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
```

{tech}[ι-reduction] 是不可能的，因为匹配的值是变量，而不是构造函数。
{lean}`1 + k` 被卡为 {lean}`Nat.add 1 k`，这不是有效的模式。

对于 {lean}`k + 1`（即 {lean}`Nat.add k (.succ .zero)`），第二个模式匹配，因此它减少为 {lean}`Nat.succ (Nat.add k .zero)`。
现在第二个模式匹配，生成 {lean}`Nat.succ k`，这是一个有效的模式。
:::
```lean -show
end
```

::::


```lean -show
end
```


## 模式匹配功能
%%%
tag := "pattern-fun"
%%%

:::syntax term (title := "Pattern-Matching Functions")
可以通过模式匹配指定功能，方法是在 {keywordOf Lean.Parser.Term.fun}`fun` 之后编写一系列模式，每个模式前面都有一个竖线 (`|`)。
```grammar
fun
  $[| $pat,* => $term]*
```
这将脱糖为一个立即对其参数进行模式匹配的函数。
:::

::::keepEnv
:::example "Pattern-Matching Functions"
{lean}`isZero` 使用模式匹配函数抽象定义，而 {lean}`isZero'` 使用模式匹配表达式定义：
```lean
def isZero : Nat → Bool :=
  fun
    | 0 => true
    | _ => false

def isZero' : Nat → Bool :=
  fun n =>
    match n with
    | 0 => true
    | _ => false
```
因为前者是后者的语法糖，所以它们在定义上是相等的：
```lean
example : isZero = isZero' := rfl
```
脱糖在 {keywordOf Lean.Parser.Command.print}`#print` 的输出中可见：
```lean (name := isZero)
#print isZero
```
输出
```leanOutput isZero
def isZero : Nat → Bool :=
fun x =>
  match x with
  | 0 => true
  | x => false
```
尽管
```lean (name := isZero')
#print isZero'
```
输出
```leanOutput isZero'
def isZero' : Nat → Bool :=
fun n =>
  match n with
  | 0 => true
  | x => false
```
:::
::::

## 其他模式匹配运营商

除了 {keywordOf Lean.Parser.Term.match}`match` 和 {keywordOf termIfLet}`if let` 之外，还有一些其他运算符执行模式匹配。

:::syntax term (title := "The {keyword}`matches` Operator")
如果左侧的项与右侧的模式匹配，则 {keywordOf Lean.«term_Matches_|»}`matches` 运算符将返回 {lean}`true`。
```grammar
$e matches $e
```
:::

当对 {keywordOf Lean.«term_Matches_|»}`matches` 的结果进行分支时，通常最好使用 {keywordOf termIfLet}`if let`，它除了检查模式是否匹配之外还可以绑定模式变量。

```lean -show
/--
info: match 4 with
| n.succ => true
| x => false : Bool
-/
#check_msgs in
#check 4 matches (n + 1)
```

如果没有可以匹配判别式或判别式序列的构造函数模式，则相关代码将无法访问，因为本地上下文中必定存在错误假设。
{keywordOf Lean.Parser.Term.nomatch}`nomatch` 表达式是零个案例的匹配，可以具有任何类型，只要没有可能的案例可以匹配判别式即可。

:::syntax term (title := "Caseless Pattern Matches")
```grammar
nomatch $e,*
```
:::

::::keepEnv
:::example "Inconsistent Indices"
没有构造函数模式可以匹配此示例中的两个证明：
```lean
example (p1 : x = "Hello") (p2 : x = "world") : False :=
  nomatch p1, p2
```

这是因为它们分别将 `x` 的值细化为不相等的字符串。
因此，{keywordOf Lean.Parser.Term.nomatch}`nomatch` 运算符允许示例的主体证明 {lean}`False`（或任何其他命题或类型）。
:::
::::

当预期类型是函数类型时，{keywordOf Lean.Parser.Term.nofun}`nofun` 是函数的简写，该函数采用与类型指示的参数一样多的参数，其中主体是应用于所有参数的 {keywordOf Lean.Parser.Term.nomatch}`nomatch`。
:::syntax term (title := "Caseless Functions")
```grammar
nofun
```
:::

::::keepEnv
:::example "Impossible Functions"
可以使用 {keywordOf Lean.Parser.Term.nofun}`nofun`，而不是为两个相等证明引入参数，然后在 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 中使用两者。
```lean
example : x = "Hello" → x = "world" → False := nofun
```
:::
::::

## 精化模式匹配
%%%
tag := "pattern-match-elaboration"
draft := true
%%%

:::planned 209
将模式匹配的精化指定为 {deftech}[辅助匹配函数]。
:::

# 洞

{deftech}_hole_ 或 {deftech}_placeholder term_ 是指示缺少精化器.{index}[占位符术语]{index (subterm := "placeholder")}[术语]的指令的术语
就术语而言，当周围上下文仅允许在漏洞所在的位置写入一个类型正确的术语时，可以自动填充漏洞。
否则，一个洞就是一个错误。
在模式中，孔代表可以匹配任何东西的通用模式。


:::syntax term (title := "Holes")
孔用下划线书写。
```grammar
_
```
:::

::::keepEnv
:::example "Filling Holes with Unification"
函数 {lean}`the` 的使用方式与 {keywordOf Lean.Parser.Term.show}`show` 或 {tech}[类型归属] 类似。
```lean
def the (α : Sort u) (x : α) : α := x
```
如果可以推断出第二个参数的类型，则第一个参数可以是一个洞。
这两个命令是等效的：
```lean
#check the String "Hello!"

#check the _ "Hello"
```
:::
::::


在编写证明时，显式引入未知值会很方便。
这是通过 {deftech}_合成孔_ 完成的，这些孔永远无法通过统一解决，并且可能出现在多个位置。
它们主要在策略证明中有用，并在 {ref "metavariables-in-proofs"}[证明中的元变量部分]中进行了描述。

:::syntax term (title := "Synthetic Holes")
```grammar
?$x:ident
```
```grammar
?_
```
:::

# Type 归属

{deftech}_Type ascriptions_ 用术语的类型显式注释它们。
它们是为 Lean 提供术语的预期类型的一种方法。
此类型在定义上必须等于基于术语上下文所期望的类型。
Type 归属不仅仅用于记录程序：
 * 程序文本中可能没有足够的信息来派生术语的类型。归属是提供类型的一种方式。
 * 推断的类型可能不是某个术语所需的类型。
 * 术语的预期类型用于驱动 {tech}[强制转换] 的插入，而归属是控制强制插入位置的一种方法。

:::syntax term (title := "Postfix Type Ascriptions")
Type 归属必须用括号括起来。
它们表明第一项的类型是第二项。
```grammar
($_ : $_)
```
:::


如果需要类型归属的术语很长，例如策略证明或 {keywordOf Lean.Parser.Term.do}`do` 块，则带有强制括号的后缀类型归属可能难以阅读。
此外，对于证明和 {keywordOf Lean.Parser.Term.do}`do` 块，术语的类型对其解释至关重要。
在这些情况下，前缀版本可以更容易阅读。
:::syntax term (title := "Prefix Type Ascriptions")
```grammar
show $_ from $_
```
当{keywordOf Lean.Parser.Term.show}`show`主体中的术语是策略证明时，可以省略关键字{keywordOf Lean.Parser.Term.show}`from`。
```grammar
show $_ by $_
```
:::

:::example "Ascribing Statements to Proofs"
此示例无法执行策略证明，因为所需的命题未知。
作为运行早期策略的一部分，该命题会自动细化为策略可以证明的命题。
然而，他们的默认情况填写不正确，导致证明失败。
```lean (name := byBusted) +error
example (n : Nat) := by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
```leanOutput byBusted
Invalid rewrite argument: Expected an equality or iff proof or definition name, but `ih` is a proof of
  0 ≍ n'
```

具有 {keywordOf Lean.Parser.Term.show}`show` 的前缀类型归属可用于提供正在证明的命题。
这在语法上下文中很有用，因为将其添加为本地定义会很不方便。
```lean
example (n : Nat) := show 0 + n = n by
  induction n
  next => rfl
  next n' ih =>
    simp only [HAdd.hAdd, Add.add, Nat.add] at *
    rewrite [ih]
    rfl
```
:::

:::example "Ascribing Types to {keywordOf Lean.Parser.Term.do}`do` Blocks"
此示例缺乏足够的类型信息来合成 {name}`Pure` 实例。
```lean (name := doBusted) +error
example := do
  return 5
```
```leanOutput doBusted
typeclass instance problem is stuck
  Pure ?m.12

Note: Lean will not try to resolve this typeclass instance problem because the type argument to `Pure` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```

具有 {keywordOf Lean.Parser.Term.show}`show` 的前缀类型归属与 {tech}[hole] 一起可用于指示 monad。
{tech (key := "default instance")}[默认] {lean}`OfNat _ 5` 实例提供了足够的类型信息来填充 {lean}`Nat` 的漏洞。
```lean
example := show StateM String _ from do
  return 5
```
:::

后缀类型归属和 {keywordOf Lean.Parser.Term.show}`show` 之间存在重要区别。
普通后缀类型归属会更改该术语的预期类型，这可能会改变该术语的详细说明方式。
然而，在精化之后，Lean 推断结果项的类型，并使用该推断类型执行进一步的精化任务。
另一方面，{keywordOf Lean.Parser.Term.show}`show` 详细精化了推断类型为归属类型的术语。
使用 {tech}[通用字段表示法] 时可以观察到差异，其中仅保证在使用 {keywordOf Lean.Parser.Term.show}`show` 时使用归属类型来解析字段。

::::example "Postfix Ascription vs `show`"

:::paragraph
此定义为 {lean}`List String` 建立了替代名称：
```lean
def Colors := List String
```
:::

:::paragraph
后缀类型归属提供了确定隐式参数 {name}`String` 到 {name}`List.nil` 所需的类型信息，但结果类型仍然是 {lean}`List String`：
```lean (name := nil)
#check ([] : Colors)
```
```leanOutput nil
[] : List String
```
:::

:::paragraph
另一方面，当使用 {keywordOf Lean.Parser.Term.show}`show` 时，详细术语的构造方式使得推断类型为 {lean}`Colors`：
```lean (name := nil2)
#check (show Colors from [])
```
```leanOutput nil2
have this := [];
this : Colors
```
:::

:::paragraph
该函数设计为使用 {tech}[通用字段表示法] 调用：
```lean
def Colors.hasYellow (cs : Colors) : Bool :=
  cs.any (·.toLower == "yellow")
```
:::

:::paragraph
由于它们推断类型的差异，它可以与 {keywordOf Lean.Parser.Term.show}`show` 一起使用，但不能与后缀类型归属一起使用：
```lean (name := nil3) +error
#eval ([] : Colors).hasYellow
```
```leanOutput nil3
Invalid field `hasYellow`: The environment does not contain `List.hasYellow`, so it is not possible to project the field `hasYellow` from an expression
  []
of type `List String`
```
```lean (name := nil4)
#eval (show Colors from []).hasYellow
```
```leanOutput nil4
false
```
:::
::::


# 引用和反引用

报价条款在 {ref "quotation"}[报价部分]中进行了描述。

# `do`-符号

{keywordOf Lean.Parser.Term.do}`do`-符号在 {ref "do-notation"}[在单子章节中]进行了描述。

# 证明

调用策略({keywordOf Lean.Parser.Term.byTactic}`by`) 的语法在 {ref "by"}[证明部分]中描述。
