/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.Language.Namespaces
import ManualZh.Coercions


import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

#doc (Manual) "命名空间和部分" =>
%%%
file := "Namespaces-and-Sections"
tag := "namespaces-sections"
htmlSplit := .never
%%%

名称被组织成分层的 {deftech}_namespaces_，它们是名称的集合。
命名空间是 Lean 中组织 API 的主要方式：它们提供操作本体，对相关项进行分组。
此外，虽然这不是通过在命名空间中给它们命名来完成的，但 {ref "language-extension"}[语法扩展]、{tech (key := "instances")}[实例] 和 {tech (key := "attributes")}[属性] 等功能的效果可以附加到命名空间。

将操作排序到名称空间中可以从全局角度从概念上组织库。
然而，任何给定的 Lean 文件通常不会同等地使用所有名称。
{tech}[Sections] 提供了一种对全局可用名称集合的本地视图进行排序的方法，以及精确控制编译器选项以及语言扩展、实例和属性的范围的方法。
它们还允许使用 {keywordOf Lean.Parser.Command.variable}`variable` 命令集中声明并根据需要传播许多声明共享的参数。


{include 1 ManualZh.Language.Namespaces}

# 章节范围
%%%
file := "Section-Scopes"
tag := "scopes"
%%%

许多命令对当前 {deftech (key := "section scope")}[_sectionscope_] 产生影响（有时在清除时简称为“scope”）。
每个 Lean 模块都有一个部分范围。
嵌套作用域是通过 {keywordOf Lean.Parser.Command.namespace}`namespace` 和 {keywordOf Lean.Parser.Command.section}`section` 命令以及 {keywordOf Lean.Parser.Command.in}`in` 命令组合器创建的。

在部分范围内跟踪以下数据：

: 当前命名空间

  {deftech (key := "current namespace")}_当前命名空间_ 是将在其中定义新声明的命名空间。
  此外，{tech (key:="resolve")}[名称解析] 包括全局名称范围内当前命名空间的所有前缀。

: 开放的命名空间

  当命名空间为 {deftech}_opened_ 时，其名称在当前作用域中无需显式前缀即可使用。
  此外，已打开的命名空间中的作用域属性和 {ref "syntax-rules"}[作用域语法扩展] 在当前节作用域中处于活动状态。

: 选项

  编译器选项在修改范围结束时将恢复为其原始值。

: 节变量

  {tech (key := "Section variables")}[节变量] 是作为参数自动添加到定义中的名称（或 {tech (key := "instance implicit")}[实例隐式] 参数）。
  当它们出现在定理的陈述中时，它们也会作为全称量化的假设添加到定理中。


## 控制部分范围
%%%
file := "Controlling-Section-Scopes"
tag := "scope-commands"
%%%

{keywordOf Lean.Parser.Command.section}`section` 命令创建新的 {deftech}[section] 范围，但不会修改当前命名空间、打开的命名空间或节变量。
当节结束时，对节范围所做的更改将被恢复。
此外，节可能会导致默认情况下将一组修饰符应用于该节中的所有声明。
可以选择对节进行命名；关闭命名节的 {keywordOf Lean.Parser.Command.end}`end` 命令必须使用相同的名称。
如果节名称具有多个组成部分（即，如果它们包含 `.` 分隔的名称），则会引入多个嵌套节。
节名称没有其他作用，并且有助于提高可读性。

:::syntax command (title := "Sections")
{keywordOf Lean.Parser.Command.section}`section` 命令创建一个节范围，该范围持续到 `end` 命令或文件末尾。
节标题（如果存在）会修改节中的声明。
```grammar
$hdr:sectionHeader section $[$id:ident]?
```
:::

:::syntax Lean.Parser.Command.sectionHeader (title := "Section Headers")
节标题（如果存在）会修改节中的声明。
```grammar
$[@[expose]]?
$[public]? $[noncomputable]? $[meta]?
```
如果标头包含 {keyword}`noncomputable`，则该节中的定义都被认为是不可计算的，并且不会为它们生成编译代码。
这对于依赖非计算推理原则（例如选择公理）的定义是必需的。

其余修饰符仅在 {tech (key := "modules")}[模块] 中有用。
如果标头包含 {attrs}`@[expose]`，则该节中的所有定义都是 {tech}[exposed]。
如果它包含 {keyword}`public`，则默认情况下，此类 {deftech (key := "public section")}[publicsection] 中的声明是公共的，而不是私有的。
如果它包含{keyword}`meta`，则该节的声明全部放在{tech (key := "meta phase")}[元阶段]中。
:::

:::example "Named Section"

名称 {name Greetings.english}`english` 在 `Greetings` 命名空间中定义。

```lean
def Greetings.english := "Hello"
```

在其名称空间之外，无法对其进行求值。

```lean +error (name := english1)
#eval english
```
```leanOutput english1
Unknown identifier `english`
```

打开一个节可以包含对全局范围的修改。
此部分名为 `Greetings`。
```lean
section Greetings
```

即使节名称与定义的名称空间匹配，该名称也不在范围内，因为节名称纯粹是为了可读性和易于重构。

```lean +error  (name := english2)
#eval english
```
```leanOutput english2
Unknown identifier `english`
```

打开命名空间 `Greetings` 会将 {name}`Greetings.english` 变为 {name Greetings.english}`english`：


```lean  (name := english3)
open Greetings

#eval english
```
```leanOutput english3
"Hello"
```

必须使用该部分的名称来关闭它。

```lean +error (name := english4) -keep
end
```
```leanOutput english4
Missing name after `end`: Expected the current scope name `Greetings`

Hint: To end the current scope `Greetings`, specify its name:
  end ̲G̲r̲e̲e̲t̲i̲n̲g̲s̲
```

```lean
end Greetings
```

当该部分关闭时，{keywordOf Lean.Parser.Command.open}`open` 命令的效果将恢复。
```lean +error  (name := english5)
#eval english
```
```leanOutput english5
Unknown identifier `english`
```
:::

{keywordOf Lean.Parser.Command.namespace}`namespace` 命令创建新的节范围。
在此节范围内，当前命名空间是命令中提供的名称，相对于周围节范围中的当前命名空间进行解释。
与节一样，当命名空间的范围结束时，对节范围所做的更改将被恢复。

要关闭命名空间，{keywordOf Lean.Parser.Command.end}`end` 命令需要当前命名空间的后缀，该后缀已被删除。
由引入该后缀部分的 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令引入的所有节范围均已关闭。

:::syntax command (title := "Namespace Declarations")
`namespace` 命令通过附加提供的标识符来修改当前命名空间。
它创建一个持续到 {keywordOf Lean.Parser.Command.end}`end` 命令或文件末尾的节范围。
```grammar
namespace $id:ident
```
:::


:::syntax command (title := "Section and Namespace Terminators")
如果没有标识符，{keywordOf Lean.Parser.Command.end}`end` 会关闭最近打开的部分，该部分必须是匿名的。
```grammar
end
```

使用标识符，它关闭最近打开的部分或名称空间。
如果它是一个节，则标识符必须是自最近的 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令以来打开的节的串联名称的后缀。
如果它是命名空间，则标识符必须是自最新仍打开的 {keywordOf Lean.Parser.Command.section}`section` 以来的当前命名空间扩展的后缀；之后，当前命名空间将删除此后缀。
```grammar
end $id:ident
```
:::

关闭 {keywordOf Lean.Parser.Command.mutual}`mutual` 块的 {keywordOf Lean.Parser.Command.mutual}`end` 是 {keywordOf Lean.Parser.Command.mutual}`mutual` 语法的一部分，而不是 {keywordOf Lean.Parser.Command.end}`end` 命令。

:::example "Nesting Namespaces and Sections"
命名空间和节可以嵌套。
单个 {keywordOf Lean.Parser.Command.end}`end` 命令可以关闭一个或多个命名空间或一个或多个部分，但不能关闭两者的混合。

使用两个单独的命令将当前命名空间设置为 `A.B.C` 后，可以使用单个 {keywordOf Lean.Parser.Command.end}`end` 删除 `B.C`：
```lean
namespace A.B
namespace C
end B.C
```
此时，当前命名空间为`A`。

接下来，打开一个匿名部分和命名空间 `D.E`：
```lean
section
namespace D.E
```
此时，当前命名空间为`A.D.E`。
由于中间部分，{keywordOf Lean.Parser.Command.end}`end` 命令无法关闭所有三个命令：
```lean +error (name := endADE) -keep
end A.D.E
```
```leanOutput endADE
Invalid name after `end`: Expected `D.E`, but found `A.D.E`
```
相反，命名空间和节必须单独结束。
```lean
end D.E
end
end A
```
:::

{keywordOf Lean.Parser.Command.in}`in` 组合器可用于创建单命令节范围，而不是为单个命令打开节。
{keywordOf Lean.Parser.Command.in}`in` 组合器是右关联的，允许堆叠多个范围修改。

:::syntax command (title := "Local Section Scopes")
`in` 命令组合器引入了单个命令的节范围。
```grammar
$c:command in
$c:command
```
:::

:::example "Using {keywordOf Lean.Parser.Command.in}`in` for Local Scopes"
使用 {keywordOf Lean.Parser.Command.in}`in` 可以使命名空间的内容可供单个命令使用。
```lean
def Dessert.cupcake := "delicious"

open Dessert in
#eval cupcake
```

单个命令后，{keywordOf Lean.Parser.Command.open}`open` 的效果恢复。

```lean +error (name := noCake)
#eval cupcake
```
```leanOutput noCake
Unknown identifier `cupcake`
```
:::

## 节变量
%%%
file := "Section-Variables"
tag := "section-variables"
%%%

{deftech (key := "Section variables")}_Section Variables_ 是自动添加到提及它们的声明中的参数。
无论选项 {option}`autoImplicit` 是否为 {lean}`true`，都会发生这种情况。
节变量可以是隐式的、严格隐式的或显式的；实例隐式节变量经过特殊处理。

当在非定理声明中遇到节变量的名称时，会将其添加为参数。
还会添加提及该变量的任何实例隐式节变量。
如果添加的任何变量依赖于其他变量，那么这些变量也会被添加；迭代此过程，直到不再有依赖关系为止。
所有节变量都按照声明顺序添加到所有其他参数之前。
仅当节变量出现在定理的_陈述_中时才会添加节变量。
否则，如果证明项使用了节变量，则修改定理的证明可能会更改其陈述。

使用 {keywordOf Lean.Parser.Command.variable}`variable` 命令声明变量。


:::syntax command (title := "Variable Declarations")
```grammar
variable $b:bracketedBinder $b:bracketedBinder*
```
:::

`variable` 后允许的括号内的绑定符与 {ref "bracketed-parameter-syntax"}[定义标头中使用的语法]匹配。

::::example "Section Variables"
在本节中，自动隐式参数被禁用，但定义了许多节变量。

```lean
section
set_option autoImplicit false
universe u
variable {α : Type u} (xs : List α) [Zero α] [Add α]
```


由于自动隐式参数已禁用，并且 `β` 既不是节变量也不是绑定为函数的参数，因此以下定义失败：
```lean +error (name := secvars) -keep
def addAll (lst : List β) : β :=
  lst.foldr (init := 0) (· + ·)
```
```leanOutput secvars
Unknown identifier `β`

Note: It is not possible to treat `β` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```


:::paragraph
另一方面，当使用节变量时，甚至 {lean}`xs` 也不需要直接写入定义中：

```lean
def addAll :=
  xs.foldr (init := 0) (· + ·)
```
:::
::::

要向定理添加节变量（即使语句中未明确提及），请使用 {keywordOf Lean.Parser.Command.include}`include` 命令标记该变量。
所有标记为包含的变量都将添加到所有定理中。
{keywordOf Lean.Parser.Command.omit}`omit` 命令从变量中删除包含标记；将其与 {keywordOf Lean.Parser.Command.in}`in` 一起使用通常是个好主意。


```lean -show
section
variable {p : Nat → Prop}
variable (pFifteen : p 15)
```
:::::example "Included and Omitted Section Variables"

本节的变量包括一个谓词以及证明它普遍成立所需的一切，以及一个无用的额外假设。

```lean
section
variable {p : Nat → Prop}
variable (pZero : p 0) (pStep : ∀ n, p n → p (n + 1))
variable (pFifteen : p 15)
```

然而，该定理的假设中仅添加了{lean}`p`，因此无法证明。
```lean +error -keep
theorem p_all : ∀ n, p n := by
  intro n
  induction n
```

{keywordOf Lean.Parser.Command.include}`include` 命令导致无条件添加附加假设：
```lean -keep (name := lint)
include pZero pStep pFifteen

theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```
由于插入了虚假假设 {lean}`pFifteen`，Lean 发出警告：
```leanOutput lint
automatically included section variable(s) unused in theorem `p_all`:
  pFifteen
consider restructuring your `variable` declarations so that the variables are not in scope or explicitly omit them:
  omit pFifteen in theorem ...

Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
```

通过使用 {keywordOf Lean.Parser.Command.omit}`omit` 删除 {lean}`pFifteen` 可以避免这种情况：
```lean -keep
include pZero pStep pFifteen

omit pFifteen in
theorem p_all : ∀ n, p n := by
  intro n
  induction n <;> simp [*]
```

```lean
end
```

:::::
```lean -show
end
```
