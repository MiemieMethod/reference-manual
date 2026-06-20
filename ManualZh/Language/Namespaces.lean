/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "命名空间" =>
%%%
file := "Namespaces"
tag := "namespaces"
%%%


包含句点的名称（不在 {tech}[guillemets] 内）是分层名称；句点分隔名称的_组成部分_。
名称中除了最后一个组成部分之外的所有组成部分都是名称空间，而最后一个组成部分是名称本身。

命名空间用于对相关定义、定理、类型和其他声明进行分组。
当命名空间对应于类型的名称时，可以使用 {tech (key := "generalized field notation")}[通用字段表示法] 来访问其内容。
除了组织名称之外，命名空间还对 {ref "language-extension"}[语法扩展]、{ref "attributes"}[属性] 和 {ref "type-classes"}[实例] 进行分组。

命名空间与 {tech}[modules] 正交：模块是一起详细说明、编译和加载的代码单元，但模块名称与其提供的名称之间没有必然联系。
模块可以包含任何名称空间中的名称，并且分层模块的嵌套结构与分层名称空间的嵌套结构无关。

有一个根命名空间，通常通过简单地省略命名空间来表示。
可以通过以 `_root_` 开头的名称来明确指示。
在名称将相对于环境命名空间（例如来自 {tech (key := "section scope")}[节范围]）或本地范围进行解释的上下文中，这可能是必要的。

:::example "Explicit Root Namespace"
当前命名空间中的名称优先于根命名空间中的名称。
在此示例中，{name}`Forest.statement` 定义中的 {name Forest.color}`color` 引用 {name}`Forest.color`：
```lean
def color := "yellow"
namespace Forest
def color := "green"
def statement := s!"Lemons are {color}"
end Forest
```
```lean (name := green)
#eval Forest.statement
```
```leanOutput green
"Lemons are green"
```

在 `Forest` 命名空间内，对根命名空间中的 {name _root_.color}`color` 的引用必须使用 `_root_` 进行限定：
```lean
namespace Forest
def nextStatement :=
  s!"Ripe lemons are {_root_.color}, not {color}"
end Forest
```
```lean (name := ygreen)
#eval Forest.nextStatement
```
```leanOutput ygreen
"Ripe lemons are yellow, not green"
```
:::

# 命名空间和节范围
%%%
file := "Namespaces-and-Section-Scopes"
tag := "zh-language-namespaces-h001"
%%%

每个 {tech (key := "section scope")}[节范围] 都有一个 {tech (key := "current namespace")}[当前命名空间]，它由 {keywordOf Lean.Parser.Command.namespace}`namespace` 命令确定。{margin}[{keywordOf Lean.Parser.Command.namespace}`namespace` 命令在 {ref "scope-commands"}[有关引入节范围的命令的部分]中进行了描述。]
在节范围内声明的名称将添加到当前命名空间。
如果声明的名称有多个组件，则其命名空间嵌套在当前命名空间内；声明的当前命名空间的主体是嵌套命名空间。
节范围还包括一组 {deftech (key := "opened namespaces")}_opened 命名空间_，这些命名空间的内容在没有附加限定的范围内。
{tech (key := "resolve")}[解析] 特定名称的标识符会考虑当前命名空间和打开的命名空间。
但是，{deftech}[protected] 声明（即具有 {keyword}`protected` {ref "declaration-modifiers"}[modifier] 的声明）在打开其命名空间时不会进入作用域。
{ref "identifiers-and-resolution"}[关于标识符作为术语的部分]中描述了将标识符解析为考虑当前命名空间和打开的命名空间的名称的规则。

:::example "Current Namespace"
定义归纳类型会导致该类型的构造函数被放置在其命名空间中，在本例中为 {name}`HotDrink.coffee`、{name}`HotDrink.tea` 和 {name}`HotDrink.cocoa`。
```lean
inductive HotDrink where
  | coffee
  | tea
  | cocoa
```
在命名空间之外，除非打开命名空间，否则必须限定这些名称：
```lean (name := okTea)
#check HotDrink.tea
```
```leanOutput okTea
HotDrink.tea : HotDrink
```
```lean (name := notOkTea) +error
#check tea
```
```leanOutput notOkTea
Unknown identifier `tea`
```
```lean (name := okTea2)
section
open HotDrink
#check tea
end
```
```leanOutput okTea2
HotDrink.tea : HotDrink
```

如果直接在 `HotDrink` 命名空间内定义函数，则将使用设置为 `HotDrink` 的当前命名空间来详细说明函数的主体。
构造函数的范围是：
```lean
def HotDrink.ofString? : String → Option HotDrink
  | "coffee" => some coffee
  | "tea" => some tea
  | "cocoa" => some cocoa
  | _ => none
```
定义另一个归纳类型会创建一个新的命名空间：
```lean
inductive ColdDrink where
  | water
  | juice
```

在 `HotDrink` 命名空间内，可以在没有显式前缀的情况下定义 {name}`HotDrink.toString`。
在 `ColdDrink` 命名空间中定义函数需要显式 `_root_` 限定符以避免定义 `HotDrink.ColdDrink.toString`：
```lean
namespace HotDrink

def toString : HotDrink → String
  | coffee => "coffee"
  | tea => "tea"
  | cocoa => "cocoa"

def _root_.ColdDrink.toString : ColdDrink → String
  | .water => "water"
  | .juice => "juice"

end HotDrink
```

:::

{keywordOf Lean.Parser.Command.open}`open` 命令打开一个命名空间，使其内容在当前节范围内可用。
打开命名空间有很多变体，为管理本地范围提供了灵活性。

:::syntax command (title := "Opening Namespaces")
{keywordOf Lean.Parser.Command.open}`open` 命令用于打开命名空间：
```grammar
open $_:openDecl
```
:::

:::syntax Lean.Parser.Command.openDecl (title := "Opening Entire Namespaces") (label := "open declaration")
一个或多个标识符的序列导致序列中的每个名称空间被打开：
```grammar
$_:ident $_:ident*
```
序列中的每个命名空间都被视为相对于所有当前打开的命名空间，从而产生一组命名空间。
该集合中的每个命名空间都会在处理序列中的下一个命名空间之前打开。
:::

:::example "Opening Nested Namespaces"
要打开的命名空间被视为相对于当前打开的命名空间。
如果相同的组件出现在不同的命名空间路径中，则可以使用单个 {keywordOf Lean.Parser.Command.open}`open` 命令通过迭代地将每个组件纳入范围来打开所有组件。
此示例定义了各种命名空间中的名称：
```lean
namespace A -- _root_.A
def a1 := 0
namespace B -- _root_.A.B
def a2 := 0
namespace C -- _root_.A.B.C
def a3 := 0
end C
end B
end A
namespace B -- _root_.B
def a4 := 0
namespace C -- _root_.B.C
def a5 := 0
end C
end B
namespace C -- _root_.C
def a6 := 0
end C
```
名字是：
 * {name}`A.a1`
 * {name}`A.B.a2`
 * {name}`A.B.C.a3`
 * {name}`B.a4`
 * {name}`B.C.a5`
 * {name}`C.a6`

可以使用单个迭代 {keywordOf Lean.Parser.Command.open}`open` 命令将所有六个名称纳入范围：
```lean
section
open A B C
example := [a1, a2, a3, a4, a5, a6]
end
```

如果命令中的初始命名空间为 `A.B`，则 `_root_.A`、`_root_.B` 和 `_root_.B.C` 都不会打开：
```lean +error (name := dotted)
section
open A.B C
example := [a1, a2, a3, a4, a5, a6]
end
```
```leanOutput dotted
Unknown identifier `a1`
```
```leanOutput dotted
Unknown identifier `a4`
```
```leanOutput dotted
Unknown identifier `a5`
```
打开 `A.B` 会使 `A.B.C` 与 `_root_.C` 一起显示为 `C`，因此后续的 `C` 将打开两者。
:::


:::syntax Lean.Parser.Command.openDecl (title := "Hiding Names") (label := "open declaration")
{keyword}`hiding` 声明指定一组不应纳入范围的名称。
与打开整个命名空间相反，提供的标识符必须唯一指定要打开的命名空间。
```grammar
$_:ident hiding $x:ident $x:ident*
```
:::

```lean -show -keep
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B hiding x
```

:::syntax Lean.Parser.Command.openDecl (title := "Renaming") (label := "open declaration")
{keyword}`renaming` 声明允许重命名打开的命名空间中的某些名称；它们可以在当前节范围内以新名称进行访问。
提供的标识符必须唯一指定要打开的命名空间。
```grammar
$_:ident renaming $[$x:ident → $x:ident],*
```

可以使用ASCII箭头(`->`)代替Unicode箭头(`→`)。
:::

```lean -show -keep
namespace A
namespace B
def x := 5
end B
end A
namespace B
end B
open A
-- test claim in preceding box
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B renaming x → y
/-- error: ambiguous namespace `B`, possible interpretations: `[B, A.B]` -/
#check_msgs in
open B renaming x -> y
```


:::syntax Lean.Parser.Command.openDecl (title := "Restricted Opening") (label := "open declaration")
括号表示_仅_括号中列出的名称应纳入范围。
```grammar
$_:ident ($x:ident $x*)
```
指示的命名空间将添加到每个当前打开的命名空间，并且每个名称都会在每个结果命名空间中考虑。
所有列出的名称必须明确；也就是说，它们必须恰好存在于所考虑的命名空间之一中。
:::

```lean -show -keep
namespace A
namespace B
def y := ""
end B
end A
namespace B
end B
open A
-- test claim in preceding box
-- TODO the reality is a bit more subtle - the name should be accessible by only one path. This should be clarified.
/-- error: ambiguous identifier `y`, possible interpretations: [B.y, B.y] -/
#check_msgs in
open B (y)
```

:::syntax Lean.Parser.Command.openDecl (title := "Scoped Declarations Only") (label := "open declaration")
{keyword}`scoped` 关键字指示应打开所提供命名空间中的所有作用域属性、实例和语法，同时不使任何名称可用。
```grammar
scoped $x:ident $x*
```
:::

::::example "Opening Scoped Declarations"
在此示例中，在命名空间 `NS` 中创建作用域 {tech}[notation] 和定义：
```lean
namespace NS
scoped notation "{!{" e "}!}" => (e, e)
def three := 3
end NS
```

在命名空间之外，该表示法不可用：

```syntaxError closed
def x := {!{ "pear" }!}
```
```leanOutput closed
<example>:1:21-1:22: unexpected token '!'; expected '}'
```

{keyword}`open scoped` 命令使符号可用：
:::keepEnv
```lean
open scoped NS
def x := {!{ "pear" }!}
```

但是，名称 {name}`NS.three` 不在范围内：
```lean +error (name := nothree)
def y := three
```
```leanOutput nothree
Unknown identifier `three`
```
:::
::::

# 导出名称
%%%
file := "Exporting-Names"
tag := "zh-language-namespaces-h002"
%%%

{deftech}_Exporting_ 名称使其在当前命名空间中可用。
与定义不同，此别名是完全透明的：使用直接解析为原始名称。
将名称导出到根命名空间使其无需限定即可使用； Lean 标准库对 {name}`Option` 的构造函数等名称和 {name}`get` 等键类型类方法执行此操作。

:::syntax command (title := "Exporting Names")
{keyword}`export` 命令将其他名称空间中的名称添加到当前名称空间中，就像它们已在其中声明一样。
当当前命名空间打开时，这些导出的名称也会进入作用域。

```grammar
export $_ ($_*)
```

在内部，导出的名称被注册为其目标的别名。
从内核的角度来看，只存在原来的名称；精化器将别名解析为 {tech (key := "resolve")}[解析] 标识符的一部分。
:::

:::example "Exported Names"
{tech (key := "inductive type")}[归纳类型] {name}`Veg.Leafy` 的声明建立了构造函数 {name}`Veg.Leafy.spinach` 和 {name}`Veg.Leafy.cabbage`：
```lean
namespace Veg
inductive Leafy where
  | spinach
  | cabbage
export Leafy (spinach)
end Veg
export Veg.Leafy (cabbage)
```
第一个 {keyword}`export` 命令使 {name}`Veg.Leafy.spinach` 可作为 {name}`Veg.spinach` 进行访问，因为 {tech (key := "current namespace")}[当前命名空间] 是 `Veg`。
第二个使 {name}`Veg.Leafy.cabbage` 可作为 {name}`cabbage` 进行访问，因为当前命名空间是根命名空间。
:::
