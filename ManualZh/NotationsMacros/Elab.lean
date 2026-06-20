/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual hiding seeAlso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "精化器" =>

%%%
tag := "elaborators"
%%%

:::seeAlso
* 精化器处理 {ref "syntax-ext"}[新语法扩展]。

* {ref "quote-patterns"}[引用模式]是最典型的解构语法的方式。
:::

虽然宏允许通过将新语法转换为现有语法来扩展 Lean，但 {deftech}_elaborators_ 允许直接处理新语法。
精化器可以访问 Lean 本身用于实现该语言的每个功能的所有内容。
定义新的精化器允许语言扩展与 Lean 的任何内置功能一样强大。

:::paragraph
精化器有两种类型：

 * {deftech}_Command elaborators_ 用于向 Lean 添加新命令。
   命令作为副作用实现：它们可以向全局环境添加新常量，扩展编译时表（例如跟踪 {tech (key := "instances")}[实例] 的表），它们可以以信息、警告或错误的形式提供反馈，并且它们可以完全访问 {name}`IO` monad。
   命令精化器与它们可以处理的 {tech (key := "kind")}[语法类型] 相关联。

 * {deftech}_Term elaborators_ 用于通过将语法转换为 Lean 的核心 类型论 来实现新术语。
   他们可以做命令精化器可以做的一切，而且他们还可以访问正在精化该术语的本地上下文。
   术语精化器可以查找绑定变量、绑定新变量、统一两个术语等等。
   术语精化器必须返回 {name}`Lean.Expr` 类型的值，它是核心 类型论 的 AST。
:::

本节提供了概述和一些精化器的示例。
由于 Lean 自己的精化器使用相同的工具，因此精化器的源代码是进一步示例的良好来源。
就像宏一样，多个精化器可以与一种语法类型相关联；它们按顺序进行尝试，并且精化器可以通过抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常来委托给表中的下一个精化器。

:::syntax command (title := "Elaboration Rules")

{keywordOf Lean.Parser.Command.elab_rules}`elab_rules` 命令采用一系列精化规则（指定为语法模式匹配），并将每个规则添加为精化器。
在先前定义的精化器之前按顺序尝试规则，并且稍后的精化器可以添加更多选项。

```grammar
$[$d:docComment]?
$[@[$attrs,*]]?
$_:attrKind elab_rules $[(kind := $k)]? $[: $_]? $[<= $_]?
  $[| `(free{(p:ident"|")?/-- Suitable syntax for {p} -/}) => $e]*
```

:::

命令、术语和策略各自维护一个将语法类型映射到精化器的表。
应使用精化器的语法类别在冒号后指定，并且必须是 `term`、`command` 或 `tactic`。
{keywordOf Lean.Parser.Command.elab_rules}`<=` 将提供的标识符绑定到正在精化术语的上下文中的当前预期类型；它只能用于术语精化器，如果存在，则 `term` 隐含为语法类别。


:::syntax attr (title := "Elaborator Attribute")
通过应用适当的属性，精化器可以直接与语法类型相关联。
每个都采用语法类型的名称并将定义与该类型相关联。

```grammar
term_elab $_
```
```grammar
command_elab $_
```
```grammar
tactic $_
```
:::

# 命令精化器
%%%
tag := "zh-notationsmacros-elab-h001"
%%%

:::::leanSection
```lean -show
open Lean Elab Command
```
命令精化器的类型为 {name}`CommandElab`，它是 {lean}`Syntax → CommandElabM Unit` 的缩写。
命令精化器可以使用 {keywordOf Lean.Parser.Command.elab_rules}`elab_rules` 隐式定义，或者通过定义函数并应用 {attr}`command_elab` 属性显式定义。

:::example "Querying the Environment"
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```

命令精化器可用于查询环境以发现有多少个常量具有给定名称。
此示例使用 {name}`MonadEnv` 类中的 {name}`getEnv` 来获取当前环境。
{name}`Environment.constants` 生成从名称到有关它们的信息的映射（例如它们的类型以及它们是否是定义、{tech (key := "inductive type")}[归纳类型] 声明等）。
{name}`logInfoAt` 允许信息输出与原始程序的语法关联，并且 {tech (key := "token antiquotation")}[令牌反引号] 用于实现 Lean 约定，即交互式命令的输出与其关键字关联。

```lean
syntax "#count_constants " ident : command

elab_rules : command
  | `(#count_constants%$tok $x) => do
    let pattern := x.getId
    let env ← getEnv
    let mut count := 0
    for (y, _) in env.constants do
      if pattern.isSuffixOf y then
        count := count + 1
    logInfoAt tok m!"Found {count} instances of '{pattern}'"
```

```lean (name := run)
def interestingName := 55
def NS.interestingName := "Another one"

#count_constants interestingName
```

```leanOutput run
Found 2 instances of 'interestingName'
```

:::

:::::

# 术语精化器
%%%
tag := "zh-notationsmacros-elab-h002"
%%%

:::::leanSection
```lean -show
open Lean Elab Term
```
术语精化器的类型为 {name}`TermElab`，它是 {lean}`Syntax → Option Expr → TermElabM Expr` 的缩写。
可选的 {lean}`Expr` 参数是正在精化的术语的预期类型，如果尚不知道类型，则为 `none`。
与命令精化器一样，术语精化器可以使用 {keywordOf Lean.Parser.Command.elab_rules}`elab_rules` 隐式定义，或者通过定义函数并应用 {attr}`term_elab` 属性显式定义。

:::example "Avoiding a Type"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term
```

此示例演示了与类型归属相反的语法精化器。
提供的项可以具有除指定类型之外的任何类型，并且元变量是悲观地解决的。
在此示例中，{name}`elabType` 调用术语精化器，然后确保生成的术语是一种类型。
{name}`Meta.inferType` 推断一项的类型，{name}`Meta.isDefEq` 尝试通过统一使两项 {tech (key := "definitional equality")}[定义等价]，如果成功则返回 {lean}`true`。

```lean
syntax (name := notType) "(" term  " !: " term ")" : term

@[term_elab notType]
def elabNotType : TermElab := fun stx _ => do
  let `(($tm:term !: $ty:term)) := stx
    | throwUnsupportedSyntax
  let unexpected ← elabType ty
  let e ← elabTerm tm none
  let eTy ← Meta.inferType e
  if (← Meta.isDefEq eTy unexpected) then
    throwErrorAt tm m!"Got unwanted type {eTy}"
  else pure e
```

如果类型位置不包含类型，则 `elabType` 会引发错误：
```lean (name := notType) +error
#eval ([1, 2, 3] !: "not a type")
```
```leanOutput notType
type expected, got
  ("not a type" : String)
```

如果术语的类型绝对不等于提供的类型，则精化成功：
```lean (name := ok)
#eval ([1, 2, 3] !: String)
```
```leanOutput ok
[1, 2, 3]
```

如果类型匹配，则会抛出错误：
```lean (name := nope) +error
#eval (5 !: Nat)
```
```leanOutput nope
Got unwanted type Nat
```

类型相等性检查可能会填充缺失的信息，因此 {lean  (type := "String")}`sorry`（可能有任何类型）也会被拒绝：
```lean (name := unif) +error
#eval (sorry !: String)
```
```leanOutput unif
Got unwanted type String
```
:::

:::example "Using Any Local Variable"
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```

术语精化器可以访问预期类型和本地上下文。
这可用于创建 {tactic}`assumption`策略的类似术语。

第一步是使用 {name}`getLocalHyps` 访问本地上下文。
它返回最外层绑定位于左侧的上下文，因此以相反的顺序遍历。
对于每个局部假设，都会使用 {name}`Meta.inferType` 推断类型。
如果可以等于预期类型，则返回假设；如果没有合适的假设，就会产生错误。

```lean
syntax "anything!" : term

elab_rules <= expected
  | `(anything!) => do
    let hyps ← getLocalHyps
    for h in hyps.reverse do
      let t ← Meta.inferType h
      if (← Meta.isDefEq t expected) then return h

    throwError m!"No assumption in {hyps} has type {expected}"
```

新语法查找函数的绑定变量：
```lean (name := app)
#eval (fun (n : Nat) => 2 + anything!) 5
```
```leanOutput app
7
```

它根据需要选择最新的合适变量：
```lean (name := lets)
#eval
  let x := "x"
  let y := "y"
  "It was " ++ y
```
```leanOutput lets
"It was y"
```

当没有合适的假设时，它会返回描述尝试的错误：
```lean (name := noFun) +error
#eval
  let x := Nat.zero
  let y := "hello"
  fun (f : Nat → Nat) =>
    (anything! : Int → Int)
```
```leanOutput noFun
No assumption in [x, y, f] has type Int → Int
```

由于它使用统一，因此此处选择自然数文字，因为数字文字可以具有带有 {name}`OfNat` 实例的任何类型。
不幸的是，没有函数的 {name}`OfNat` 实例，因此稍后实例合成失败。
```lean (name := poly) +error
#eval
  let x := 5
  let y := "hello"
  (anything! : Int → Int)
```
```leanOutput poly
failed to synthesize instance of type class
  OfNat (Int → Int) 5
numerals are polymorphic in Lean, but the numeral `5` cannot be used in a context where the expected type is
  Int → Int
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::::

# 定制策略
%%%
tag := "zh-notationsmacros-elab-h003"
%%%

自定义策略在 {ref "custom-tactics"}[有关策略的部分]中进行了描述。
