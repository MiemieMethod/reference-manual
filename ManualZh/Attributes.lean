/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option pp.rawOnError true
set_option maxRecDepth 3000

set_option linter.unusedVariables false

#doc (Manual) "属性" =>
%%%
file := "Attributes"
tag := "attributes"
htmlSplit := .never
%%%

{deftech}_Attributes_ 是声明上的一组可扩展的编译时注释。
它们可以作为 {ref "declaration-modifiers"}[声明修饰符] 或使用 {keywordOf Lean.Parser.Command.attribute}`attribute` 命令添加。

属性可以将信息与编译时表（包括 {tech (key := "custom simp sets")}[自定义 simp 集]、{tech (key := "macros")}[宏] 和 {tech (key := "instances")}[实例]）中的声明相关联，对定义施加附加要求（例如，如果其类型不是类型类，则拒绝它们），或生成附加代码。
与术语、命令的 {tech (key := "macros")}[宏] 和自定义 {tech}[elaborators] 以及策略一样，属性的 {tech (key := "syntax category")}[语法类别] `attr` 被设计为可扩展，并且有一个表将每个扩展映射到解释它的编译时程序。

属性应用为 {deftech (key := "attribute instances")}_attribute 实例_，将范围指示符与属性配对。
这些可能出现在作为声明修饰符的属性中，也可能出现在独立的 {keywordOf Lean.Parser.Command.attribute}`attribute` 命令中。

:::syntax Lean.Parser.Term.attrInstance (title := "Attribute Instances")
```grammar
$_:attrKind $_:attr
```

`attrKind` 是可选的 {ref "scoped-attributes"}[属性范围] 关键字 {keyword}`local` 或 {keyword}`scoped`。
这些控制属性效果的可见性。
属性本身是可扩展 {tech (key := "syntax category")}[语法类别] `attr` 中的任何内容。
:::

属性系统非常强大：属性可以将任意信息与声明相关联并生成任意数量的帮助程序。
这会带来一些设计权衡：存储这些信息需要空间，而检索它需要时间。
因此，某些属性只能应用于定义该声明的模块中的声明。
这使得大型项目中的查找速度更快，因为它们不需要检查所有模块的数据。
每个属性决定如何存储自己的元数据，以及对于给定用例，灵活性和性能之间的适当权衡是什么。

# 属性作为修饰符
%%%
file := "Attributes-as-Modifiers"
tag := "zh-attributes-h001"
%%%

属性可以作为 {ref "declaration-modifiers"}[声明修饰符] 添加到声明中。
它们放置在文档注释和可见性修饰符之间。

:::syntax Lean.Parser.Term.attributes -open (title := "Attributes")
```grammar
@[$_:attrInstance,*]
```
:::

# {keyword}`attribute` 命令
%%%
file := "The-___keyword______attribute___-Command"
tag := "zh-attributes-h002"
%%%

{keywordOf Lean.Parser.Command.attribute}`attribute` 命令可用于修改声明的属性。
一些示例用途包括：
 * 通过添加 {attr}`instance` 将预先存在的声明注册为本地范围中的 {tech (key := "instance")}[实例]，
 * 使用 {attr}`simp` 或 {attr}`ext` 将预先存在的定理标记为简单引理或外延引理，并且
 * 暂时从默认的 {tech}[simp set] 中删除 simp 引理。

:::syntax command (title := "Attribute Modification")
{keywordOf Lean.Parser.Command.attribute}`attribute` 命令在现有声明中添加或删除属性。
标识符是其属性被修改的名称。
```grammar
attribute [$_,*] $_
```
:::

除了向现有声明添加属性的属性实例之外，还可以删除某些属性；这称为 {deftech}_erasing_ 属性。
可以通过在属性名称前添加 `-` 来删除属性。
然而，并非所有属性都支持擦除。

:::syntax Lean.Parser.Command.eraseAttr (title := "Erasing Attributes")
通过在属性名称前添加 `-` 来擦除属性。

```grammar
-$_:ident
```
:::


# 范围属性
%%%
file := "Scoped-Attributes"
tag := "scoped-attributes"
%%%

许多属性可以应用于特定范围。
这决定了属性的效果是否仅在当前节范围、打开当前命名空间的命名空间中或在任何地方可见。
这些范围指示还用于控制 {ref "syntax-rules"}[语法扩展] 和 {ref "instance-attribute"}[类型类实例]。
每个属性负责精确定义这些术语对其特定效果的含义。

:::syntax attrKind -open (title := "Attribute Scopes") (alias := Lean.Parser.Term.attrKind)
每当建立全局范围的声明（默认）的 {tech}[module] 被传递导入时，全局范围的声明（默认）就会生效。
它们通过缺少另一个范围修饰符来指示。
```grammar
```

本地范围的声明仅在建立它们的 {tech (key := "section scope")}[节范围] 范围内有效。
```grammar
local
```

只要打开建立作用域声明的 {tech (key := "current namespace")}[namespace]，作用域声明就会生效。
```grammar
scoped
```
:::
