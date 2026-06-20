/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "源文件和模块" =>
%%%
tag := "files"
htmlSplit := .never
%%%

Lean 中的最小编译单元是单个 {tech}[源文件]。
源文件可以根据文件名导入其他源文件。
换句话说，文件的名称和文件夹结构在 Lean 代码中很重要。

每个源文件都有一个 {deftech}_导入名称_，该名称源自其文件名和调用 Lean 的方式的组合：Lean 有一组_根目录_，它希望在其中查找代码，源文件的导入名称是从根目录到文件名的目录名称，带点 (`.`)散布并删除 `.lean`。
例如，如果以 `Projects/MyLib/src` 作为根调用 Lean，则文件 `Projects/MyLib/src/Literature/Novel/SciFi.lean` 可以作为 `Literature.Novel.SciFi` 导入。

::: TODO
在此描述文件名的区分大小写/保留
:::

# 编码和表示
%%%
tag := "module-encoding"
%%%

Lean {deftech}[源文件] 是以 UTF-8 编码的 Unicode 文本文件。 {TODO}[弄清楚BOM和Lean的状态]
行可以以换行符结束（`"\n"`、Unicode `'LINE FEED (LF)' (U+000A)`），也可以以换页符和换行符序列结束（`"\r\n"`、Unicode `'CARRIAGE RETURN (CR)' (U+000D)` 后跟 `'LINE FEED (LF)' (U+000A)`）。
但是，Lean 在解析或比较文件时会标准化行结尾，因此所有文件都会被比较，就好像它们的所有行结尾都是 `"\n"` 一样。
::: TODO
旁注：这是为了使缓存文件和 `#guard_msgs` 等文件即使在 git 更改行结尾时也能工作。还保持存储在解析的语法对象中的偏移量一致。
:::

# 具体语法
%%%
tag := "module-syntax"
%%%


Lean的具体语法是{ref "language-extension"}[extensible]。
在像 Lean 这样的语言中，不可能一劳永逸地完全描述语法，因为除了新常量或 {tech}[归纳类型] 之外，库还可能定义语法。
这里不是完整地描述语言，而是描述整体框架，而每种语言构造的语法都记录在其所属的部分中。

## 空白
%%%
tag := "whitespace"
%%%

Lean 中的标记可以由任意数量的 {deftech}[_whitespace_] 字符序列分隔。
空白可以是空格（`" "`、Unicode `'SPACE (SP)' (U+0020)`）、有效的换行序列或注释。 {TODO}[外部参考]
制表符和后面不跟换行符的回车符都不是有效的空白序列。

## 评论
%%%
tag := "comments"
%%%


注释是文件的一部分，尽管不是空白，但也被视为空白。
Lean 有两种注释语法：

: 线路评论

  不作为标记的一部分出现的 `--` 开始_行注释_。从初始 `-` 到换行符的所有字符都被视为空格。{index (subterm := "line")}[comment]

: 阻止评论

  `/-` 不作为令牌的一部分出现且后面没有紧跟 `-` 字符，则开始 _block comment_.{index (subterm := "block")}[comment]
  块注释将继续，直到找到终止 `-/`。
  块注释可以嵌套；如果之前的嵌套块注释开启符 `/-` 已被匹​​配的 `-/` 终止，则 `-/` 仅终止注释。

`/--` 和 `/-!` 开始 {deftech}_documentation_ {TODO}[xref] 而不是注释，它们也以 `-/` 终止，并且可能包含嵌套块注释。
尽管文档类似于注释，但它们有自己的语法类别；它们的有效位置由 Lean 的语法确定。



## 关键字和标识符
%%%
tag := "keywords-and-identifiers"
%%%


{tech}[标识符] 由一个或多个标识符组件组成，这些组件之间用 `'.'`.{index}[标识符] 分隔

{deftech}[标识符组件] 由字母或类似字母的字符或下划线 (`'_'`) 组成，后跟零个或多个标识符连续字符。
字母为大写或小写的英文字母，类字母字符包括一系列非英语字母文字，包括在 Lean 中广泛使用的希腊字母、科普特文字、Unicode 类字母符号块的成员，其中包含许多双线字符（包括 `ℕ` 和 `ℤ`）和缩写、Latin-1 补充字母（`×` 和 `÷` 除外）和 Latin Extended-A 块。
标识符连续字符由字母、类似字母的字符、下划线（`'_'`）、感叹号（`!`）、问号（`?`）、下标和单引号（`'`）组成。
作为例外，下划线本身并不是有效的标识符。

```lean -show
def validIdentifier (str : String) : IO String :=
  Lean.Parser.identFn.test str

/-- info: "Success! Final stack:\n  `ℕ\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"?\"" -/
#check_msgs in
#eval validIdentifier "?"

/-- info: "Success! Final stack:\n  `ℕ?\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "ℕ?"

/-- info: "Failure @0 (⟨1, 0⟩): expected identifier\nFinal stack:\n  <missing>\nRemaining: \"_\"" -/
#check_msgs in
#eval validIdentifier "_"

/-- info: "Success! Final stack:\n  `_3\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_3"

/-- info: "Success! Final stack:\n  `_.a\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "_.a"

/-- info: "Success! Final stack:\n  `αποδεικνύοντας\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "αποδεικνύοντας"

/-- info: "Success! Final stack:\n  `κύκ\nRemaining:\n\"λος\"" -/
#check_msgs in
#eval validIdentifier "κύκλος"

/-- info: "Success! Final stack:\n  `øvelse\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "øvelse"

/-- info: "Success! Final stack:\n  `Übersetzung\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "Übersetzung"

/- Here's some things that probably should be identifiers but aren't at the time of writing -/

/--
info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"переклад\""
-/
#check_msgs in
#eval validIdentifier "переклад"

/-- info: "Failure @0 (⟨1, 0⟩): expected token\nFinal stack:\n  <missing>\nRemaining: \"汉语\"" -/
#check_msgs in
#eval validIdentifier "汉语"


```

标识符组件也可能被双 {deftech}[guillemets]（`'«'` 和 `'»'`）包围。
此类标识符组件可以包含除 `'»'` 之外的任何字符，甚至 `'«'`、`'.'` 和换行符。
这些海角不是生成的标识符组件的一部分，因此 `«x»` 和 `x` 表示相同的标识符。
另一方面，`«Nat.add»` 是具有单个组件的标识符，而 `Nat.add` 有两个组件。




```lean -show
/-- info: "Success! Final stack:\n  `«\n  »\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«\n»"

/-- info: "Success! Final stack:\n  `««one line\n  and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "««one line\nand another»"

/-- info: "Success! Final stack:\n  `«one line\x00and another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x00and another»"

/-- info: "Success! Final stack:\n  `«one line\x0band another»\nAll input consumed." -/
#check_msgs in
#eval validIdentifier "«one line\x0Band another»"
```

一些潜在的标识符组件可以是保留关键字。
保留关键字的具体集合取决于活动语法扩展集合，这可能取决于导入文件集合和当前打开的 {TODO}[xref/deftech for namespace] 命名空间； Lean 无法作为整体进行枚举。
这些关键字还必须用 guillemets 引用，才能在大多数语法上下文中用作标识符组件。
关键字可以用作没有 guillemets 的标识符的上下文（例如归纳类型中的构造函数名称）为 {deftech}_rawidentifier_contexts.{index (subterm:="raw")}[identifier]

包含一个或多个 `'.'` 字符并因此由多个标识符组件组成的标识符称为 {deftech}[分层标识符]。
分层标识符用于表示导入名称和命名空间中的名称。

# 结构
%%%
tag := "module-structure"
%%%


:::syntax Lean.Parser.Module.module -open (title := "Modules")
```grammar
$hdr:header $cmd:command*
```

源文件由 {deftech}_file header_ 后跟 {deftech}_commands_ 序列组成。
:::

如果源文件的标头以 {keywordOf Lean.Parser.Module.header}`module` 开头，则它被称为 {tech}_module_。
模块可以更好地控制向客户端公开哪些信息。

## 标头
%%%
tag := "module-headers"
%%%


模块标题列出了应在当前模块之前详细说明的模块。
它们的声明在当前模块中可见。

:::syntax Lean.Parser.Module.header -open (title := "Module Headers")
模块头由可选的 {keywordOf Lean.Parser.Module.header}`module` 关键字组成，后跟一系列 {deftech}[`import` 语句]：
```grammar
$[module]?
$i:import*
```

可选的 {keyword}`prelude` 关键字只能在 Lean 的源代码中使用：
```grammar
$[module]?
prelude
$i:import*
```
:::

如果存在，{keyword}`prelude` 关键字表示该文件是 Lean {deftech}_prelude_ 实现的一部分，该代码无需任何显式导入即可使用 — 不应在 Lean 实现之外使用。

:::syntax Lean.Parser.Module.prelude -open (title := "Prelude Modules")
```grammar
prelude
```

:::

::::syntax Lean.Parser.Module.import (title := "Imports")
所有 {tech}[源文件] 都可以使用普通导入：
```grammar
import $mod:ident
```

在不是模块的源文件中，这会导入指定的 Lean 文件。
导入文件使其内容在当前源文件以及通过其导入传递导入的源文件中可用。

源文件名不一定对应于命名空间。
源文件可以将名称添加到任何命名空间，并且导入源文件对当前打开的命名空间集没有影响。

通过将名称中的点 (`'.'`) 替换为目录分隔符并附加 `.lean` 或 `.olean`，{tech}[导入名称] 将转换为文件名。
Lean 在其包含路径中搜索相应的中间构建产品或可导入模块文件。

{tech}[Modules] 可以使用以下导入语法：
```grammar
$[public]? $[meta]? import $[all]? $mod:ident
```

:::paragraph
模块的所有导入本身都必须是模块。
如果没有修饰符，导入模块的公共作用域将添加到当前模块的私有作用域中。导入的模块不可用于导入当前模块的模块。
修饰符的含义如下：

: {keyword}`public`

  导入模块的公共作用域将添加到当前模块的公共作用域中，并可供当前模块的导入者使用。

: {keyword}`meta`

  导入模块的内容在当前模块的 {tech}[元阶段] 中可用。

: {keyword}`all`

  导入模块的私有作用域被添加到当前模块的 {tech}[私有作用域]。
:::
::::

## 命令
%%%
tag := "commands"
%%%


{tech}[Commands] 是 Lean 中的顶级语句。
一些示例包括归纳类型声明、定理、函数定义、命名空间修饰符（如 `open` 或 `variable`）以及交互式查询（如 `#check`）。
命令的语法是用户可扩展的，命令甚至可以 {ref "language-extension"}[添加用于解析后续命令的新语法]。
具体的 Lean 命令记录在本手册的相应章节中，而不是在此列出。

::: TODO
使索引包含所有命令的链接，然后从此处进行外部引用
:::

# 模块和可见性
%%%
tag := "module-scopes"
%%%

:::paragraph
{deftech}[模块] 是一个选择区分公共信息和私人信息的源文件。
Lean 确保私人信息可以更改，而不会影响仅导入其公共信息的客户端。
该学科带来了许多好处：

: 平均构建时间大大缩短

  对仅影响非导出信息（例如校样、注释和文档字符串）的文件的更改不会触发这些文件外部的重建。
  即使必须重建相关文件，也可以跳过那些不受影响的文件（由其 {keywordOf Lean.Parser.Module.import}`import` 注释确定）。

: 控制 API 演化

  图书馆作者可以相信，对非导出信息的更改不会影响其图书馆的下游用户。
  如果仅公开函数的签名，那么下游用户就不能依赖涉及其展开的定义等式；这意味着该库的作者可以自由地采用更有效的算法，而不会无意中破坏客户端代码。

: 避免意外展开

  限制定义可以展开的范围可以避免应通过应用更具体的定理来取代的归约，以及实际上不必要的无效归约。
  这提高了证明精化的速度。

: 较小的可执行文件

  分离编译时和运行时代码可以更积极地消除死代码，保证策略等元程序不会进入最终的二进制文件。

: 减少内存使用

  从导入中排除诸如校样之类的私人信息可以改善 Lean 在构建和编辑项目时的内存使用情况。
  即使在进一步最小化导入之前，将 mathlib4 移植到模块系统也能节省近 50%。{TODO}[mathlib 名称的链接和格式与手册的其余部分一致]
:::

:::paragraph
模块包含两个单独的范围：{deftech}_public 范围_ 包含在导入模块的模块中可见的信息，而 {deftech}_private 范围_ 包含通常仅在模块内可见的信息。
私人或公开信息的一些示例包括：

: 名称

  常量（例如定义、归纳类型或构造函数）可以是私有的或公共的。
  公共常量的类型只能引用公共名称。

: 定义

  公共定义可能是 {deftech}[exposeed]，也可能不是。
  如果未公开公共定义，则无法在只能访问公共范围的上下文中展开它。
  相反，客户必须依赖公共范围内提供的有关定义的定理。
:::

每个声明都有默认的可见性规则。
一般来说，默认情况下所有名称都是私有的，除非在 {tech}[public 部分] 中定义。
即使是公共名称通常也将定义主体放在私有范围内，甚至公开定义中的证明也保持私有。
每个声明命令的具体可见性规则与声明本身一起记录。

::::example "Private and Public Definitions"
:::leanModules +error
模块 {module}`Greet.Create` 定义函数 {name}`greeting`。
由于没有可见性修饰符，因此该函数默认为 {tech}[私有范围]：
```leanModule (moduleName := Greet.Create)
module
def greeting (name : String) : String :=
  s!"Hello, {name}"
```
{name}`greeting` 的定义在模块 {module}`Greet` 中不可见，即使它导入了 {module}`Greet.Create`：
```leanModule (moduleName := Greet) (name := noRef)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2
```
```leanOutput noRef
Unknown identifier `greeting`
```
:::

:::leanModules
如果{name}`greeting`公开，则{name}`greetTwice`可以参考它：
```leanModule (moduleName := Greet.Create)
module
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
```leanModule (moduleName := Greet)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2
```
:::
::::

::::example "Exposed and Unexposed Definitions"
:::leanModules +error
模块 {module}`Greet.Create` 定义公共函数 {name}`greeting`。
```leanModule (moduleName := Greet.Create)
module
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
尽管 {name}`greeting` 的定义在模块 {module}`Greet` 中可见，但它无法在证明中展开，因为定义的主体位于 {module}`Greet` 的 {tech}[私有范围] 中：
```leanModule (moduleName := Greet) (name := nonExp)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2

theorem greetTwice_is_greet_twice {name1 name2 : String} :
    greetTwice name1 name2 = "Hello, " ++ name1 ++ "\n" ++ "Hello, " ++ name2 := by
  simp [greetTwice, greeting]
```
```leanOutput nonExp
Invalid simp theorem `greeting`: Expected a definition with an exposed body
```
:::

:::leanModules
添加 {attrs}`@[expose]` 属性会公开定义，以便下游模块可以展开 {name}`greeting`：
```leanModule (moduleName := Greet.Create)
module
@[expose]
public def greeting (name : String) : String :=
  s!"Hello, {name}"
```
现在，证明可以继续进行：
```leanModule (moduleName := Greet)
module
import Greet.Create
def greetTwice (name1 name2 : String) : String :=
  greeting name1 ++ "\n" ++ greeting name2

theorem greetTwice_is_greet_twice {name1 name2 : String} :
    greetTwice name1 name2 = "Hello, " ++ name1 ++ "\n" ++ "Hello, " ++ name2 := by
  simp [greetTwice, greeting, toString]
  grind [String.append_assoc]
```
:::
::::

:::::example "Proofs are Private"
::::leanModules
:::paragraph
在此模块中，函数 {name}`incr` 是公开的，但其实现并未公开：
```leanModule (moduleName := Main)
module

public def incr : Nat → Nat
  | 0 => 1
  | n + 1 => incr n + 1

public theorem incr_eq_plus1 : incr = (· + 1) := by
  funext n
  induction n <;> simp [incr, *]
```
:::

尽管如此，定理 {name}`incr_eq_plus1` 的证明可以揭示其定义。
这是因为定理的证明属于私有范围。
公共定理和私有定理都是如此。
::::
:::::

从普通源文件转换到模块时可以使用选项 {option}`backward.privateInPublic`。
当它设置为 {lean}`true` 时，将导出私有定义，但在导入模块中无法访问它们的名称。
但是，允许在其定义模块的公共部分中引用它们。
除非将选项 {option}`backward.privateInPublic.warn` 设置为 {lean}`false`，否则此类引用会导致警告。
这些警告可用于定位并最终消除这些引用，从而允许禁用 {option}`backward.privateInPublic`。
类似地，{option}`backward.proofsInPublic` 导致使用 {keywordOf Lean.Parser.Term.by}`by` 创建的证明是公开的，而不是私有的；这可以使 {keywordOf Lean.Parser.Term.by}`by` 以其预期类型填充元变量。
{option}`backward.proofsInPublic` 的大多数用例还要求启用 {option}`backward.privateInPublic`。

{optionDocs backward.privateInPublic}

{optionDocs backward.privateInPublic.warn}

{optionDocs backward.proofsInPublic}

::::example "Exporting Private Definitions"
:::leanModules
在模块{module}`L.Defs`中，{name}`f`的公共定义引用其签名中的私有定义{name}`drop2`。
由于 {option}`backward.privateInPublic` 是 {lean}`true`，因此允许这样做，从而导致警告：
```leanModule (moduleName := L.Defs) (name := warnPub)
module

set_option backward.privateInPublic true

def drop2 (xs : List α) : List α := xs.drop 2

public def f (xs : List α) (transform : List α → List α:= drop2) : List α :=
  transform xs
```
```leanOutput warnPub
Private declaration `drop2` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled.

Disable `backward.privateInPublic.warn` to silence this warning.
```
导入模块时，对 {name}`f` 的引用使用 {name}`drop2` 作为默认参数值；但是，在模块 {module}`L` 中无法访问其名称：
```leanModule (moduleName :=  L) (name := withPrivateInTerm)
module
import L.Defs

def xs := [1, 2, 3]

set_option pp.explicit true in
#check f xs
```
```leanOutput withPrivateInTerm
@f Nat xs (@drop2✝ Nat) : List Nat
```
:::
::::

::::example "Proofs in Public"
:::leanModules
在纯源文件 {module}`NotMod` 中，{name}`two` 的定义通过求解 {tech}`metavariable` 使用证明的内容来填写定义中的数值：
```leanModule (moduleName := NotMod)
structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
:::
:::leanModules +error
将此文件转换为模块会导致错误，因为定义的主体在公共部分中公开，但证明是私有的，因此无法更改公共类型：
```leanModule (moduleName := Mod) (name := proofMeta)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
```leanOutput proofMeta
tactic execution is stuck, goal contains metavariables
  ?m.3 + ?m.3 = ?m.5
```
:::
:::leanModules
设置选项 {option}`backward.proofsInPublic` 会导致证明位于模块的公共部分，因此它可以解决元变量：
```leanModule (moduleName := Mod)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

set_option backward.proofsInPublic true in
abbrev two := Half.mk _ <| by
  show 2 + 2 = 4
  rfl
```
:::

:::leanModules
然而，重新表述定义通常是更好的风格，以便证明有一个完整的目标：
```leanModule (moduleName := Mod)
module
public section

structure Half (n : Nat) where
  val : Nat
  ok : val + val = n

abbrev two : Half 4 := Half.mk 2 <| by
  rfl
```
:::
::::


可以使用 {keywordOf Lean.Parser.Module.import}`all` 修饰符将模块的私有范围导入到另一个模块中。
默认情况下，仅当导入的模块和当前模块来自相同的 Lake {tech}[package] 时才允许这样做，因为其主要目的是允许将定义和证明分离到单独的模块中以进行库的内部组织。
Lake 包或库选项 {ref "Lake.PackageConfig allowImportAll" (domain := Manual.lakeTomlField)}`allowImportAll` 可以设置为允许其他包通过 {keywordOf Lean.Parser.Module.import}`import all` 访问当前包的私有作用域。
导入的私有范围包括导入模块的私有导入，包括嵌套的 {keywordOf Lean.Parser.Module.import}`import all`。
因此，当前模块可访问的私有作用域集合是 {keywordOf Lean.Parser.Module.import}`import all` 声明的传递闭包。

带模块系统的{keywordOf Lean.Parser.Module.import}`import all`比不带模块系统的{keywordOf Lean.Parser.Module.import}`import`更强大。
它使导入的私有定义可以通过名称直接访问，就像它们是在当前模块中定义的一样。
{keywordOf Lean.Parser.Module.import}`import all` 的第二个用例是访问库内多个模块中的代码，但这些代码不应提供给下游消费者，以及允许测试访问不属于公共 API 的信息。

::::example "Importing Private Information"
:::leanModules (moduleRoot := Tree) +error
该库将定义模块与引理模块分开。
这是 Lean 代码中的常见模式。
```leanModule (moduleName := Tree.Basic)
module

public inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

public def Tree.count : Tree α → Nat
  | .leaf => 0
  | .branch left _ right => left.count + 1 + right.count
```
然而，由于 {name}`Tree.count` 没有暴露，所以引理文件中的证明无法展开它：
```leanModule (moduleName := Tree.Lemmas) (name := lemmasNoAll)
module
public import Tree.Basic
theorem Tree.count_leaf_eq_zero : count (.leaf : Tree α) = 0 := by
  simp [count]
```
```leanOutput lemmasNoAll
Invalid simp theorem `count`: Expected a definition with an exposed body
```
:::

:::leanModules (moduleRoot := Tree)
将私有范围从 {module}`Tree.Basic` 导入引理模块允许在证明中展开定义。
```leanModule (moduleName := Tree.Basic)
module

public inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

public def Tree.count : Tree α → Nat
  | .leaf => 0
  | .branch left _ right => left.count + 1 + right.count
```
```leanModule (moduleName := Tree.Lemmas)
module
import all Tree.Basic
public import Tree.Basic
theorem Tree.count_leaf_eq_zero : count (.leaf : Tree α) = 0 := by
  simp [count]
```
:::
::::


## 元阶段
%%%
tag := "meta-phase"
%%%

Lean 中的定义会产生 类型论 中专为形式推理而设计的表示形式以及专为执行而设计的编译表示形式。
这种编译表示用于生成机器代码，但也可以使用解释器直接执行。
在 {tech -normalize}[精化] 期间运行的代码（例如 {ref "tactics"}[策略] 或 {ref "macros"}[macros]）是定义的编译形式。
如果此编译表示发生更改，则由它创建的任何代码可能不再是最新的，并且必须重新运行。
由于编译器执行重要的优化，因此对函数的传递依赖链中的任何定义进行更改原则上可能会使其编译表示无效。
这意味着模块导出的元程序比普通定义产生更强的耦合。
此外，元程序在普通术语的构造期间运行；因此，它们在使用前必须被完全定义和编译。
毕竟，没有函数体的函数定义无法运行。
元程序运行的时间称为 {deftech}_元编程阶段_，通常简称为 {deftech}_元阶段_。

正如它们区分公共信息和私有信息一样，模块还区分元阶段可用的代码和普通代码。
任何用作编译时执行入口点的声明都必须使用 {keywordOf Lean.Parser.Module.import}`meta` 修饰符进行标记，这表明该声明可用作元程序。
这是在内置元编程语法（例如 {keywordOf Lean.Parser.Command.syntax}`syntax`、{keywordOf Lean.Parser.Command.macro}`macro` 和 {keywordOf Lean.Parser.Command.elab}`elab`）中自动完成的，但在手动应用元编程属性（例如 {keyword}`app_delab`）或定义帮助器声明时可能需要显式完成。
{keywordOf Parser.Command.declModifiers}`meta` 定义只能访问（并因此调用）执行相关位置中的其他 {keywordOf Parser.Command.declModifiers}`meta` 定义；非 {keywordOf Parser.Command.declModifiers}`meta` 定义同样只能访问其他非 {keywordOf Parser.Command.declModifiers}`meta` 定义。

::::example "Meta Definitions"
:::leanModules +error
在此模块中，辅助函数 {name}`revArrays` 反转术语中每个数组文字中元素的顺序。
这由宏 {keyword}`rev!` 调用。
```leanModule (moduleName := Main) (name := nonMeta)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

partial def revArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$((xs : Array Term).reverse),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM revArrays)⟩
    | _ => pure ⟨other⟩

macro "rev!" e:term : term => do
  revArrays e
```
该错误消息表明 {name}`revArrays` 无法从宏中使用，因为它未在模块的 {tech}[元编程阶段] 中定义：
```leanOutput nonMeta
Invalid `meta` definition `_aux___macroRules_termRev!__1`, `revArrays` not marked `meta`
```
:::
:::leanModules
使用 {keywordOf Lean.Parser.Command.declModifiers}`meta` 修饰符标记 {name}`revArrays` 允许宏定义调用它：
```leanModule (moduleName := Main) (name := withMeta)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta partial def revArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$((xs : Array Term).reverse),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM revArrays)⟩
    | _ => pure ⟨other⟩

macro "rev!" e:term : term => do
  revArrays e

#eval rev! #[1, 2, 3]
```
```leanOutput withMeta
#[3, 2, 1]
```
:::
::::

最初不属于元阶段的库可以通过使用 {keywordOf Parser.Module.import}`meta import` 导入模块来引入。
当模块在元阶段导入时，其所有定义都在该阶段可用，无论它们是否标记为 {keywordOf Parser.Command.declModifiers}`meta`。
不存在元元阶段。
除了使导入模块的公共内容在元阶段可用之外，{keywordOf Parser.Module.import}`meta import` 还指示如果导入模块的编译表示发生更改，则应重建当前模块，以确保重新运行修改后的元程序。
如果一个定义应该在两个阶段都可用，那么它必须在单独的模块中定义并在两个阶段导入。

::::example "Cross-Phase Code Reuse"
:::leanModules +error
在此模块中，函数 {name}`toPalindrome` 是在元阶段定义的，这允许它在宏中使用，但不能在普通定义中使用：
```leanModule (moduleName := Phases) (name := bothPhases)
module

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta def toPalindrome (xs : Array α) : Array α := xs ++ xs.reverse

meta partial def palArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$(toPalindrome (xs : Array Term)),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM palArrays)⟩
    | _ => pure ⟨other⟩

macro "pal!" e:term : term => do
  palArrays e

#check pal! (#[1, 2, 3] ++ [6, 7, 8])

public def colors := toPalindrome #["red", "green", "blue"]
```
```leanOutput bothPhases
Invalid definition `colors`, may not access declaration `toPalindrome` marked as `meta`
```
:::
:::leanModules
将 {name}`toPalindrome` 移至其自己的模块 {module}`Phases.Pal` 允许在两个阶段导入该模块：
```leanModule (moduleName := Phases.Pal)
module

public def toPalindrome (xs : Array α) : Array α := xs ++ xs.reverse
```
```leanModule (moduleName := Phases) (name := bothPhases)
module

meta import Phases.Pal
import Phases.Pal

open Lean

variable [Monad m] [MonadRef m] [MonadQuotation m]

meta partial def palArrays : Syntax → m Term
  | `(#[$xs,*]) => `(#[$(toPalindrome (xs : Array Term)),*])
  | other => do
    match other with
    | .node k i args =>
      pure ⟨.node k i (← args.mapM palArrays)⟩
    | _ => pure ⟨other⟩

local macro "pal!" e:term : term => do
  palArrays e

#check pal! (#[1, 2, 3] ++ [6, 7, 8])

public def colors := toPalindrome #["red", "green", "blue"]
```
如果宏 {keyword}`pal!` 是公共的（即，如果未使用 {keyword}`local` 修饰符声明它），则 {module}`Phases.Pal` 的 {keywordOf Lean.Parser.Module.import}`meta import` 也需要声明为 {keywordOf Lean.Parser.Module.import}`public`。
:::
::::

此外，如果导入的定义可以在当前模块外部的编译时执行，即如果可以从当前模块中的某些公共 {keywordOf Parser.Command.declModifiers}`meta` 定义访问它，则导入必须是公共的。
使用 {keywordOf Parser.Module.import}`public meta import`。
如果该声明已声明为 {keywordOf Parser.Command.declModifiers}`meta`，则 {keywordOf Parser.Module.import}`public import` 就足够了。

与定义不同，大多数元程序默认是公共的。
因此，大多数 {keywordOf Lean.Parser.Module.import}`meta import` 实际上也是 {keywordOf Parser.Module.import}`public`。
例外情况是导入定义仅用于本地元程序时，例如使用 {keywordOf Parser.Command.syntax}`local syntax`、{keywordOf Parser.Command.macro}`local macro` 或 {keywordOf Parser.Command.elab}`local elab` 声明的定义。

作为指导原则，通常最好保持 {keywordOf Lean.Parser.Command.declModifiers}`meta` 注释的数量尽可能小。
这可以避免将可重用的声明锁定到 {tech}[元阶段] 中，并有助于构建系统避免更多的重建。
因此，当元程序依赖于本身不需要标记为 {keywordOf Lean.Parser.Command.declModifiers}`meta` 的其他代码时，该其他代码应放置在单独的模块中并且不标记为 {keywordOf Lean.Parser.Command.declModifiers}`meta`。
只有实际注册元程序的最终模块才需要帮助程序处于元阶段。
该模块应使用 {keywordOf Lean.Parser.Module.import}`public meta import` 导入这些帮助程序，然后使用内置语法（如 {keywordOf Parser.Command.elab}`elab`、使用 {keywordOf Lean.Parser.Command.declaration}`meta def` 或使用 {keywordOf Lean.Parser.Command.section}`meta section`）定义其元程序。


# 精心设计的模块
%%%
tag := "module-contents"
%%%

当 Lean 详细说明源文件时，结果是 {tech}[环境]。
该环境包括常量 {tech}[归纳类型]、{tech}[定理]、{tech (key := "type class")}[类型类]、{tech}[实例]以及文件中声明的所有其他内容，以及跟踪 {tech}[simp 集]等各种数据的边表，命名空间别名和 {tech}[文档注释]。
如果文件包含模块，那么环境还会跟踪哪些信息是公共的和私有的，以及定义可用的阶段。

当源文件由 Lean 处理时，命令将内容添加到环境中。
在精化之后，环境被序列化为 {deftech (key:="olean")}[`.olean` 文件]，其中包含环境和压缩堆区域，其中包含环境所需的运行时对象。
这意味着可以加载导入的源文件，而无需重新执行其所有命令。
精心设计模块产生的环境被序列化为三个 {tech (key:="olean")}[`.olean` 文件]，其中包含环境中的私有、公共和服务器信息。
服务器信息由 API 文档和定义源位置等数据组成，仅在使用 Lean 语言服务器时需要，不需要与其他上下文中的公共信息一起加载。

# 模块系统错误和模式
%%%
tag := "zh-sourcefiles-h012"
%%%

:::paragraph
以下列表包含在使用模块系统，特别是将现有文件移植到模块系统时可能遇到的常见错误：

: 未知的常量错误

  检查是否正在 {tech}[公共范围] 中访问私有定义。
  如果是这样，也可以通过将当前声明设为私有，或者使用字段上的 {keywordOf Lean.Parser.Term.structInstFieldDef}`private` 修饰符或 {keywordOf Lean.Parser.Term.by}`by` 作为证明将引用放入私有范围来解决问题。

: 定义等价 错误，尤其是在移植之后

  预期定义等价性失败通常是由于定义中缺少 {attr}`expose` 属性，或者如果导入，则缺少 {keywordOf Lean.Parser.Module.import}`import all`。
  如果您图书馆之外的任何人可能需要相同的访问权限，请首选前者。
  错误消息应列出无法展开的非公开定义。
  当策略直接发出引用特定声明的证明术语而不经过精化器（例如通过反射证明）时，这也可能显示为内核错误。
  在这种情况下，没有现成的跟踪可用于调试；考虑在相关模块的关闭上慷慨地使用{attrs}`@[expose]`‍` `{keywordOf Parser.Command.section}`section`s。

:::

## 移植现有文件的秘诀
%%%
tag := "zh-sourcefiles-h013"
%%%

:::paragraph
为了获得模块系统的好处，必须将源文件制成模块。
首先在所有文件中启用模块系统，并进行最小的重大更改：
1. 所有文件都带有 {keywordOf Lean.Parser.Module.header}`module` 前缀。
2. 使所有现有导入 {keywordOf Lean.Parser.Command.declModifiers}`public` 除非它们仅用于校样。
 * 当发生提及引用私有数据的错误时添加 {keywordOf Lean.Parser.Module.import}`import all`。
 * 当出现“必须是 {keywordOf Lean.Parser.Module.import}`meta`”的错误时添加 {keywordOf Lean.Parser.Module.import}`public meta import`。
   定义仅限本地的元程序时，可以省略 {keywordOf Lean.Parser.Module.import}`public`。
3. 在文件的其余部分添加前缀 `@[expose] public section`，或者对于以编程为重点的文件，添加 {keywordOf Lean.Parser.Command.section}`public section`。
   后者应该用于将运行但不会推理的程序。
:::

在模块系统下的初始构建成功后，可以迭代地最小化模块之间的依赖关系。
特别是，删除 {keywordOf Lean.Parser.Command.declModifiers}`public` 和 {attrs}`@[expose]` 的使用将有助于避免不必要的重建。

# 包、库和目标
%%%
tag := "code-distribution"
%%%


Lean 模块被组织成 {tech}_packages_，它们是代码分发的单元。
{tech}[package] 可能包含多个库或可执行文件。

包中供其他 Lean 包使用的代码被组织到 {deftech (key:="library")}[库] 中。
旨在作为独立程序编译和运行的代码被组织到 {deftech (key:="executable")}[可执行文件] 中。
有关 {ref "lake"}[Lake，标准 Lean 构建工具] 的部分详细介绍了包、库和可执行文件。
