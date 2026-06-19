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

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "定义新语法" =>
%%%
tag := "syntax-ext"
%%%

Lean 的语法统一表示非常通用且灵活。
这意味着对 Lean 解析器的扩展不需要对解析语法的表示进行扩展。

# 语法模型
%%%
tag := "syntax-data"
%%%

Lean 的解析器生成 {name}`Lean.Syntax` 类型的具体语法树。
{name}`Lean.Syntax` 是归纳类型，表示 Lean 的所有语法，包括命令、术语、策略和任何自定义扩展。
所有这些都由一些基本构建块表示：

: {deftech}[原子]

  原子是语法的基本终端，包括文字（例如字符和数字）、括号、运算符和关键字。

: {deftech}[标识符]

  :::keepEnv
  ```lean -show
  variable {α : Type u}
  variable {x : α}
  ```
  标识符代表名称，例如 {lean}`x`、{lean}`Nat` 或 {lean}`Nat.add`。
  标识符语法包括标识符可能引用的预解析名称列表。
  :::

: {deftech}[节点]

  节点代表非终结符的解析。
  节点包含 {deftech}_syntax kind_，它标识生成节点的语法规则，以及子 {name Lean.Syntax}`Syntax` 值的数组。

: 缺少语法

  当解析器遇到错误时，它会返回部分结果，因此 Lean 可以提供有关部分编写的程序或包含错误的程序的一些反馈。
  部分结果包含一个或多个缺失语法的实例。

原子和标识符统称为 {deftech}_tokens_。

{docstring Lean.Syntax}

{docstring Lean.Syntax.Preresolved}

# 语法节点类型

语法节点类型通常标识生成该节点的解析器。
这是为运算符或符号（或其自动生成的内部名称）指定的名称出现的地方。
虽然只有节点包含标识其类型的字段，但标识符按照约定具有 {name Lean.identKind}`identKind` 类型，而原子按照约定具有其内部字符串作为其类型。
Lean 的解析器将每个关键字原子 `KW` 包装在一个单例节点中，其类型为 `` `token.KW ``。
可以使用 {name Lean.Syntax.getKind}`Syntax.getKind` 提取语法值的类型。

{docstring Lean.SyntaxNodeKind}

{docstring Lean.Syntax.isOfKind}

{docstring Lean.Syntax.getKind}

{docstring Lean.Syntax.setKind}

# 令牌和文字类型

许多命名类型与解析器生成的基本标记相关联。
通常，单令牌语法产生式由包含单个 {name Lean.Syntax.atom}`atom` 的 {name Lean.Syntax.node}`node` 组成；节点中保存的种类允许识别该值。
解析器不会解释文字的原子：字符串原子包括其前导和尾随双引号字符以及其中包含的任何转义序列，并且十六进制数字保存为以 {lean}`"0x"` 开头的字符串。
提供 {ref "typed-syntax-helpers"}[Helpers]（例如 {name}`Lean.TSyntax.getString`）来按需执行此解码。

```lean -show -keep
-- Verify claims about atoms and nodes
open Lean in
partial def noInfo : Syntax → Syntax
  | .node _ k children => .node .none k (children.map noInfo)
  | .ident _ s x pre => .ident .none s x pre
  | .atom _ s => .atom .none s
  | .missing => .missing
/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "0xabc123"]
-/
#check_msgs in
#eval noInfo <$> `(term|0xabc123)

/--
info: Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"ab\\tc\""]
-/
#check_msgs in
#eval noInfo <$> `(term|"ab\tc")
```

{docstring Lean.identKind}

{docstring Lean.strLitKind}

{docstring Lean.interpolatedStrKind}

{docstring Lean.interpolatedStrLitKind}

{docstring Lean.charLitKind}

{docstring Lean.numLitKind}

{docstring Lean.scientificLitKind}

{docstring Lean.nameLitKind}

{docstring Lean.fieldIdxKind}

# 内部种类

{docstring Lean.groupKind}

{docstring Lean.nullKind}

{docstring Lean.choiceKind}

{docstring Lean.hygieneInfoKind}

# 来源职位
%%%
tag := "source-info"
%%%

原子、标识符和节点可选地包含 {deftech}[源信息]，用于跟踪它们与原始文件的对应关系。
解析器保存所有标记的源信息，但不保存节点的源信息；已解析节点的位置信息是根据其第一个和最后一个标记重建的。
并非所有 {name Lean.Syntax}`Syntax` 数据都来自解析器：它可能是 {tech}[宏展开] 的结果，在这种情况下，它通常包含生成和解析的语法的混合，或者它可能是 {tech (key := "delaborator")}[delaborating] 内部术语的结果以将其显示给用户。
在这些用例中，节点本身可能包含源信息。

源信息有两种：

: {deftech}[原件]

  原始源信息来自解析器。
  除了原始源位置之外，它还包含解析器跳过的前导和尾随空格，这允许重建原始字符串。
  该空白被保存为原始源代码的字符串表示形式的偏移量（即，{name}`Substring`），以避免分配子字符串的副本。

: {deftech}[合成]

  综合源信息来自元程序（包括宏）或来自 Lean 的内部。
  因为没有要重建的原始字符串，所以它不保存前导和尾随空格。
  即使术语已自动转换，合成源位置也可用于提供准确的反馈，并跟踪详细表达式与其在 Lean 输出中的表示之间的对应关系。
  合成位置可能被标记为 {deftech}_canonical_，在这种情况下，一些通常会忽略合成位置的操作会将其视为不存在。

{docstring Lean.SourceInfo}

# 检查语法

```lean -show
section Inspecting
open Lean
```

检查 {lean}`Syntax` 值的主要方法有以下三种：

 : {lean}`Repr` 实例

  {lean}`Repr Syntax` 实例根据 {lean}`Syntax` 类型的构造函数生成非常详细的语法表示。

 : {lean}`ToString` 实例

  {lean}`ToString Syntax` 实例生成一个紧凑的视图，表示具有特定约定的某些语法类型，可以使其更易于一目了然。
  此实例抑制源位置信息。

 : 漂亮的打印机

  Lean 的漂亮打印机尝试呈现语法，就像在源文件中一样，但如果语法的嵌套结构与预期形状不匹配，则会失败。

::::keepEnv
:::example "Representing Syntax as Constructors"
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```

{name}`Repr` 实例的语法表示可以通过在 {keywordOf Lean.Parser.Command.eval}`#eval` 上下文中引用它来检查，它可以在命令精化monad {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中运行操作。
为了减小示例输出的大小，使用帮助器 {lean}`removeSourceInfo` 在显示之前删除源信息。
```lean
partial def removeSourceInfo : Syntax → Syntax
  | .atom _ str => .atom .none str
  | .ident _ str x pre => .ident .none str x pre
  | .node _ k children => .node .none k (children.map removeSourceInfo)
  | .missing => .missing
```

```lean (name := reprStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (repr (removeSourceInfo stx.raw))
```
```leanOutput reprStx1
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `«term_+_»
  #[Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "2"],
    Lean.Syntax.atom (Lean.SourceInfo.none) "+", Lean.Syntax.missing]
```

在第二个示例中，通过引用插入的 {tech}[宏范围] 在调用 {name}`List.length` 时可见。
```lean (name := reprStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (repr (removeSourceInfo stx.raw))
```
{tech}[预解析标识符] {name}`List.length` 的内容在此处可见：
```leanOutput reprStx2 (allowDiff := 2)
Lean.Syntax.node
  (Lean.SourceInfo.none)
  `Lean.Parser.Term.app
  #[Lean.Syntax.ident
      (Lean.SourceInfo.none)
      "List.length".toRawSubstring
      (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `List.length.«_@».Manual.NotationsMacros.SyntaxDef 1704743902) "_hygCtx") "_hyg") 2)
      [Lean.Syntax.Preresolved.decl `List.length []],
    Lean.Syntax.node
      (Lean.SourceInfo.none)
      `null
      #[Lean.Syntax.node
          (Lean.SourceInfo.none)
          `«term[_]»
          #[Lean.Syntax.atom (Lean.SourceInfo.none) "[",
            Lean.Syntax.node
              (Lean.SourceInfo.none)
              `null
              #[Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Rose\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Daffodil\""],
                Lean.Syntax.atom (Lean.SourceInfo.none) ",",
                Lean.Syntax.node (Lean.SourceInfo.none) `str #[Lean.Syntax.atom (Lean.SourceInfo.none) "\"Lily\""]],
            Lean.Syntax.atom (Lean.SourceInfo.none) "]"]]]
```
:::
::::

{name}`ToString` 实例表示 {name}`Syntax` 的构造函数，如下所示：

 * {name Syntax.ident}`ident` 构造函数表示为基础名称。未显示源信息和预先解析的名称。
 * {name Syntax.atom}`atom` 构造函数表示为字符串。
 * {name Syntax.missing}`missing` 构造函数由 `<missing>` 表示。
 * {name Syntax.node}`node` 构造函数的表示取决于类型。
   如果类型为 {lean}`` `null ``，则该节点由方括号中的子节点顺序表示。
   否则，节点由其类型后跟其子节点表示，两者都用括号括起来。

:::example "Syntax as Strings"
```imports -show
import Lean.Elab
```
```lean -show
open Lean
```
语法的字符串表示形式可以通过在 {keywordOf Lean.Parser.Command.eval}`#eval` 的上下文中引用它来检查，它可以在命令精化monad {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中运行操作。

```lean (name := toStringStx1)
#eval do
  let stx ← `(2 + $(⟨.missing⟩))
  logInfo (toString stx)
```
```leanOutput toStringStx1
(«term_+_» (num "2") "+" <missing>)
```

在第二个示例中，通过引用插入的 {tech}[宏范围] 在调用 {name}`List.length` 时可见。
```lean (name := toStringStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  logInfo (toString stx)
```
```leanOutput toStringStx2 (allowDiff := 2)
(Term.app
 `List.length._@.Manual.NotationsMacros.SyntaxDef.3168789510._hygCtx._hyg.2
 [(«term[_]» "[" [(str "\"Rose\"") "," (str "\"Daffodil\"") "," (str "\"Lily\"")] "]")])
```
:::

漂亮的打印语法通常在将其包含在给用户的消息中时最有用。
通常，Lean 在需要时会自动调用漂亮打印机。
但是，如果需要，可以显式调用 {name}`ppTerm`。

::::keepEnv
:::example "Pretty-Printed Syntax"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Command
```

语法的字符串表示形式可以通过在 {keywordOf Lean.Parser.Command.eval}`#eval` 的上下文中引用它来检查，它可以在命令精化monad {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中运行操作。
因为新的语法声明还为漂亮打印机配备了显示它们的指令，所以漂亮打印机需要一个配置对象。
这个上下文可以用一个助手来构建：
```lean
def getPPContext : CommandElabM PPContext := do
  return {
    env := (← getEnv),
    opts := (← getOptions),
    currNamespace := (← getCurrNamespace),
    openDecls := (← getOpenDecls)
  }
```

```lean (name := ppStx1)
#eval show CommandElabM Unit from do
  let stx ← `(2 + 5)
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx1
2 + 5
```

在第二个示例中，通过引用插入到 {name}`List.length` 上的 {tech}[宏范围] 导致它显示为带有匕首 (`✝`)。
```lean (name := ppStx2)
#eval do
  let stx ← `(List.length ["Rose", "Daffodil", "Lily"])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo fmt
```
```leanOutput ppStx2
List.length✝ ["Rose", "Daffodil", "Lily"]
```

漂亮的打印会自动换行并插入缩进。
{tech}[强制] 通常使用默认布局宽度将漂亮打印机的输出转换为 {name}`logInfo` 所需的类型。
可以通过使用命名参数显式调用 {name Std.Format.pretty}`pretty` 来控制宽度。
```lean (name := ppStx3)
#eval do
  let flowers := #["Rose", "Daffodil", "Lily"]
  let manyFlowers := flowers ++ flowers ++ flowers
  let stx ← `(List.length [$(manyFlowers.map (quote (k := `term))),*])
  let fmt ← ppTerm (← getPPContext) stx
  logInfo (fmt.pretty (width := 40))
```
```leanOutput ppStx3
List.length✝
  ["Rose", "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily", "Rose",
    "Daffodil", "Lily"]
```
:::


::::

```lean -show
end Inspecting
```

# 类型化语法
%%%
tag := "typed-syntax"
%%%

语法还可以用指定其属于哪个 {tech}[语法类别] 的类型进行注释。
{TODO}[Describe the problem here—complicated invisible internal invariants leading to weird error msgs]
{name Lean.TSyntax}`TSyntax` 结构包含语法类别的类型级列表以及语法树。
语法类别列表通常只包含一个元素，在这种情况下，不会显示列表结构本身。

{docstring Lean.TSyntax}

{docstring Lean.SyntaxNodeKinds}

{tech}[Quasiquotations] 防止替换不来自正确语法类别的类型化语法。
对于许多 Lean 的内置语法类别，有一组 {tech}[强制转换] 适当地包装另一种类别的语法，例如从字符串文字语法到术语语法的强制转换。
此外，许多仅对某些语法类别有效的辅助函数仅针对适当的类型化语法定义。

```lean -show
/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
open Lean in
#synth CoeHTCT (TSyntax `str) (TSyntax `term)
```

{name Lean.TSyntax}`TSyntax` 的构造函数是公共的，没有什么可以阻止用户构造破坏内部不变量的值。
{name Lean.TSyntax}`TSyntax` 的使用应被视为减少常见错误的一种方法，而不是完全排除它们。


:::leanSection
```lean -show
open Lean Syntax
variable {ks : SyntaxNodeKinds} {sep : String}
```
除了 {name Lean.TSyntax}`TSyntax` 之外，还有一些表示带或不带分隔符的语法数组的类型。
这些对应于语法声明或反引号中的 {TODO}[xref] 重复元素。
{lean}`TSyntaxArray ks`是{lean}`Array (TSyntax ks)`的{tech}[缩写]，而{lean}`TSepArray ks sep`是一个结构体；这意味着 {tech}[广义字段表示法] 可用于将数组函数应用于 {name}`TSyntaxArray`，但不能应用于 {name}`TSepArray`。
{lean}`TSepArray ks` 和 {lean}`TSyntaxArray ks` 之间存在 {tech}[强制]，以及显式转换函数。
此转换会从基础数组中插入或删除分隔符元素，所需时间与元素数量成线性关系。
:::

{docstring Lean.TSyntaxArray}

{docstring Lean.TSyntaxArray.raw}

{docstring Lean.Syntax.TSepArray}

{docstring Lean.Syntax.TSepArray.getElems +allowMissing}

{docstring Lean.Syntax.TSepArray.elemsAndSeps}

{docstring Lean.Syntax.TSepArray.ofElems}

{docstring Lean.Syntax.TSepArray.push +allowMissing}


# 别名

为常用的类型化语法变体提供了许多别名。
这些别名允许在更高的抽象级别编写代码。

{docstring Lean.Term}

{docstring Lean.Command}

{docstring Lean.Syntax.Level}

{docstring Lean.Syntax.Tactic}

{docstring Lean.Prec}

{docstring Lean.Prio}

{docstring Lean.Ident}

{docstring Lean.StrLit}

{docstring Lean.CharLit}

{docstring Lean.NameLit}

{docstring Lean.NumLit}

{docstring Lean.ScientificLit}

{docstring Lean.HygieneInfo}

# 构造语法的助手
%%%
tag := "syntax-construction-helpers"
%%%

{docstring Lean.mkIdent +allowMissing}

{docstring Lean.mkIdentFrom}

{docstring Lean.mkIdentFromRef +allowMissing}

{docstring Lean.mkCIdent +allowMissing}

{docstring Lean.mkCIdentFrom}

{docstring Lean.mkCIdentFromRef +allowMissing}

{docstring Lean.Syntax.mkApp}

{docstring Lean.Syntax.mkCApp +allowMissing}

{docstring Lean.Syntax.mkLit +allowMissing}

{docstring Lean.Syntax.mkCharLit +allowMissing}

{docstring Lean.Syntax.mkStrLit +allowMissing}

{docstring Lean.Syntax.mkNumLit +allowMissing}

{docstring Lean.Syntax.mkNatLit +allowMissing}

{docstring Lean.Syntax.mkScientificLit +allowMissing}

{docstring Lean.Syntax.mkNameLit +allowMissing}

{docstring Lean.mkOptionalNode +allowMissing}

{docstring Lean.mkGroupNode +allowMissing}

{docstring Lean.mkHole +allowMissing}

## 引用数据
%%%
tag := "quote-class"
%%%

:::leanSection
```lean -show
open Lean
```
{name Lean.Quote}`Quote` 类允许将值转换为表示它们的类型化语法。
例如，{lean (type:="Term")}`quote 5` 表示 {lean (type := "Term")}``⟨.node .none `num #[.atom .none "5"]⟩``。
该类通过语法类型进行参数化；这允许相同的值以不同的种类适当地表示。
{name}`Quote` 的实例解析考虑类型化语法 {tech}[强制转换]。
语法类型的默认值为 {lean}`` `term ``。
```lean -show
/--
info: { raw := Lean.Syntax.node (Lean.SourceInfo.none) `num #[Lean.Syntax.atom (Lean.SourceInfo.none) "5"] }
-/
#guard_msgs in
#eval (quote 5 : Term)
```
:::

:::paragraph
无法保证 {name Lean.Quote.quote}`Quote.quote` 的结果能够成功精化。
一般来说，生成的语法包含所有显式参数的带引号版本，并省略隐式参数。

{docstring Lean.Quote +allowMissing}

定义 {name Lean.Quote}`Quote` 的实例时，请使用 {name Lean.mkCIdent}`mkCIdent` 和 {name Lean.Syntax.mkCApp}`mkCApp` 以避免在生成的语法中捕获变量。
:::

:::example "Defining `Quote` Instances"
```lean -show
open Lean Syntax
```

引用 {name}`Tree` 类型的树，{name}`mkCIdent` 和 {name}`mkCApp` 用于确保具有相似名称的本地绑定不会干扰。
使用双反引号可确保构造函数名称不包含拼写错误并得到正确解析。
```lean
inductive Tree (α : Type u) : Type u where
  | leaf
  | branch (left : Tree α) (val : α) (right : Tree α)

instance [Quote α] : Quote (Tree α) where
  quote := quoteTree
where
  quoteTree
    | .leaf =>
      mkCIdent ``Tree.leaf
    | .branch l v r =>
      mkCApp ``Tree.branch #[quoteTree l, quote v, quoteTree r]
```

:::

# 解码类型化语法
%%%
tag := "typed-syntax-helpers"
%%%

对于文字，Lean 的解析器生成包含 {name Lean.Syntax.atom}`atom` 的单例节点。
内部原子包含一个带有源信息的字符串，而节点的种类指定如何解释该原子。
这可能涉及解码字符串转义序列或解释 16 进制数字文字。
本节中的帮助程序执行正确的解释。

{docstring Lean.TSyntax.getId}

{docstring Lean.TSyntax.getName}

{docstring Lean.TSyntax.getNat}

{docstring Lean.TSyntax.getScientific}

{docstring Lean.TSyntax.getString}

{docstring Lean.TSyntax.getChar}

{docstring Lean.TSyntax.getHygieneInfo}

# 语法类别
%%%
tag := "syntax-categories"
%%%

Lean 的解析器包含一个 {deftech}_syntaxcategories_ 表，它对应于上下文无关语法中的非终结符。
一些最重要的类别是术语、命令、宇宙层级、优先级、优先级以及表示标记（例如文字）的类别。
通常，每个 {tech}[语法种类] 对应于一个类别。
可以使用 {keywordOf Lean.Parser.Command.syntaxCat}`declare_syntax_cat` 声明新类别。

:::syntax command (title := "Declaring Syntactic Categories")
声明一个新的语法类别。

```grammar
$[$_:docComment]?
declare_syntax_cat $_ $[(behavior := $_)]?
```
:::

前导标识符行为是一项高级功能，通常不需要修改。
它控制解析器在遇到标识符时的行为，有时可能会导致标识符被视为非保留关键字。
这用于避免将每个 {ref "tactics"}[策略] 的名称转换为保留关键字。

{docstring Lean.Parser.LeadingIdentBehavior}

# 语法规则
%%%
tag := "syntax-rules"
%%%

每个 {tech}[语法类别] 与一组 {deftech}_syntax Rules_ 相关联，这些规则对应于上下文无关语法中的产生式。
可以使用 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令定义语法规则。

:::syntax command (title := "Syntax Rules")
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind
syntax$[:$p]? $[(name := $x)]? $[(priority := $p)]? $_* : $c
```
:::

与运算符和符号声明一样，文档注释的内容在用户与新语法交互时向用户显示。
可以添加属性以在结果定义上调用编译时元程序。

语法规则与 {tech}[节范围] 的交互方式与属性、运算符和符号相同。
默认情况下，任何模块中的解析器都可以使用语法规则，该模块可传递地导入在其中建立语法规则的语法规则，但可以将它们声明为 `scoped` 或 `local`，以分别将其可用性限制为当前名称空间已打开的上下文或当前 {tech}[节范围]。

当类别的多个语法规则可以匹配当前输入时，{tech}[本地最长匹配规则]用于选择其中之一。
与符号和运算符一样，如果最长匹配存在平局，则使用声明的优先级来确定应用哪个解析结果。
如果这仍然不能解决歧义，则保存所有并列的结果。
精化器预计将尝试所有这些方法，并在能够详细精化其中一个时成功。

语法规则的优先级紧跟在 {keywordOf Lean.Parser.Command.syntax}`syntax` 关键字之后，限制解析器仅当优先级上下文至少为提供的值时才使用此新语法。
{TODO}[Default precedence]
就像运算符和符号一样，语法规则可以手动提供名称；如果不是，则会生成一个未使用的名称。
无论是提供还是生成，此名称都用作生成的 {name Lean.Syntax.node}`node` 中的语法类型。

语法声明的主体比符号的主体更加灵活。
字符串文字指定要匹配的原子。
子术语可以从任何语法类别中提取，而不仅仅是术语，并且它们可以是可选的或重复的，有或没有交错的逗号分隔符。
语法规则中的标识符指示语法类别，而不是像在符号中那样命名子术语。


最后，语法规则指定了它扩展的语法类别。
在不存在的类别中声明语法规则是错误的。

```lean -show
-- verify preceding para
/-- error: unknown category `nuhUh` -/
#check_msgs in
syntax "blah" : nuhUh
```


:::syntax stx -open (title := "Syntax Specifiers")
语法类别 `stx` 是可能出现在 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令主体中的说明符的语法。

字符串文字被解析为 {tech}[atoms]（包括 `if`、`#eval` 或 `where` 等关键字）：
```grammar
$s:str
```
字符串中的前导空格和尾随空格不会影响解析，但会导致 Lean 在显示 {tech}[proof states] 中的语法和错误消息时在相应位置插入空格。
通常，在语法规则中作为原子出现的有效标识符成为保留关键字。
在字符串文字前面加上 & 符号 (`&`) 可抑制此行为：
```grammar
&$s:str
```

标识符指定给定位置预期的语法类别，并且可以选择提供优先级：{TODO}[这里默认 prec？]
```grammar
$x:ident$[:$p]?
```

`*` 修饰符是 Kleene 星号，匹配前面语法的零次或多次重复。
也可以使用 `many` 写入。
```grammar
$s:stx *
```
`+` 修饰符匹配前述语法的一次或多次重复。
也可以使用 `many1` 写入。
```grammar
$s:stx +
```
`?` 修饰符使子项成为可选，并匹配前面语法的零次或一次（但不能多次）重复。
也可写为`optional`。
```grammar
$s:stx ?
```
```grammar
optional($s:stx)
```

`,*` 修饰符与前面带有交错逗号的语法的零次或多次重复相匹配。
也可以使用 `sepBy` 写入。
```grammar
$_:stx ,*
```

`,+` 修饰符与前面带有交错逗号的语法的一次或多次重复相匹配。
也可以使用 `sepBy1` 写入。
```grammar
$_:stx ,+
```

`,*,?` 修饰符将前面语法的零次或多次重复与交错逗号匹配，从而允许在最终重复之后使用可选的尾随逗号。
也可以使用 `sepBy` 和 `allowTrailingSep` 修饰符来编写。
```grammar
$_:stx ,*,?
```

`,+,?` 修饰符将前面语法的一次或多次重复与交错逗号相匹配，从而允许在最后一次重复之后使用可选的尾随逗号。
也可以使用 `sepBy1` 和 `allowTrailingSep` 修饰符来编写。
```grammar
$_:stx ,+,?
```

`<|>` 运算符（可写为 `orelse`）与任一语法匹配。
然而，如果第一个分支消耗了任何令牌，那么它就会被提交，并且失败将不会被回溯：
```grammar
$_:stx <|> $_:stx
```
```grammar
orelse($_:stx, $_:stx)
```

`!` 运算符与其参数的补集匹配。
如果它的参数失败，那么它会成功，重置解析状态。
```grammar
! $_:stx
```

语法说明符可以使用括号进行分组。
```grammar
($_:stx)
```

可以使用 `many` 和 `many1` 定义重复。
后者需要至少一个重复语法实例。
```grammar
many($_:stx)
```
```grammar
many1($_:stx)
```

带有分隔符的重复可以使用 `sepBy` 和 `sepBy1` 来定义，它们分别匹配零个或多个出现以及一个或多个出现，由某种其他语法分隔。
它们分为三个品种：
 * 双参数版本使用字符串文字中提供的原子来解析分隔符，并且不允许尾随分隔符。
 * 三参数版本使用第三个参数来解析分隔符，使用原子进行漂亮的打印。
 * 四参数版本可选择允许分隔符在序列结束时出现额外的时间。
    第四个参数必须始终是关键字 `allowTrailingSep`。

```grammar
sepBy($_:stx, $_:str)
```
```grammar
sepBy($_:stx, $_:str, $_:stx)
```
```grammar
sepBy($_:stx, $_:str, $_:stx, allowTrailingSep)
```
```grammar
sepBy1($_:stx, $_:str)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx)
```
```grammar
sepBy1($_:stx, $_:str, $_:stx, allowTrailingSep)
```
:::

::::keepEnv
:::example "Parsing Matched Parentheses and Brackets"

可以使用语法规则定义由匹配的圆括号和方括号组成的语言。
第一步是声明一个新的 {tech}[语法类别]：
```lean
declare_syntax_cat balanced
```
接下来，可以为圆括号和方括号添加规则。
为了排除空字符串，基例由空对组成。
```lean
syntax "(" ")" : balanced
syntax "[" "]" : balanced
syntax "(" balanced ")" : balanced
syntax "[" balanced "]" : balanced
syntax balanced balanced : balanced
```

为了根据这些规则调用 Lean 的解析器，还必须将新语法类别嵌入到可能已解析的语法类别中：
```lean
syntax (name := termBalanced) "balanced " balanced : term
```

这些术语无法详细说明，但出现精化错误表明解析成功：
```lean
/--
error: elaboration function for `termBalanced` has not been implemented
  balanced ()
-/
#guard_msgs in
example := balanced ()

/--
error: elaboration function for `termBalanced` has not been implemented
  balanced []
-/
#guard_msgs in
example := balanced []

/--
error: elaboration function for `termBalanced` has not been implemented
  balanced [[]()([])]
-/
#guard_msgs in
example := balanced [[] () ([])]
```

同样，当它们不匹配时解析会失败：
```syntaxError mismatch
example := balanced [() (]]
```
```leanOutput mismatch
<example>:1:25-1:26: unexpected token ']'; expected ')' or balanced
```
:::
::::

::::keepEnv
:::example "Parsing Comma-Separated Repetitions"
可以使用以下语法添加需要双方括号并允许尾随逗号的列表文字变体：
```lean
syntax "[[" term,*,? "]]" : term
```

添加 {tech}[宏] 来描述如何将其转换为普通列表文字，使其可以在测试中使用。
```lean
macro_rules
  | `(term|[[$e:term,*]]) => `([$e,*])
```

```lean (name := evFunnyList)
#eval [["Dandelion", "Thistle",]]
```
```leanOutput evFunnyList
["Dandelion", "Thistle"]
```

:::
::::

# 缩进
%%%
tag := "syntax-indentation"
%%%

在内部，解析器维护保存的源位置。
语法规则可能包括与这些保存的位置交互的指令，导致在不满足条件时解析失败。
缩进敏感构造（例如 {keywordOf Lean.Parser.Term.do}`do`）保存源位置，在考虑此保存位置的同时解析其组成部分，然后恢复原始位置。

特别是，缩进敏感度是通过组合 {name Lean.Parser.withPosition}`withPosition` 或 {name Lean.Parser.withPositionAfterLinebreak}`withPositionAfterLinebreak`（在解析某些其他语法开始时保存源位置）与 {name Lean.Parser.checkColGt}`colGt`、{name Lean.Parser.checkColGe}`colGe` 和 {name Lean.Parser.checkColEq}`colEq`（将当前列与最近保存位置的列进行比较）来指定的。
{name Lean.Parser.checkLineEq}`lineEq` 还可用于确保两个位置位于源文件中的同一行。

:::parserAlias withPosition
:::

:::parserAlias withoutPosition
:::

:::parserAlias withPositionAfterLinebreak
:::

:::parserAlias colGt
:::

:::parserAlias colGe
:::

:::parserAlias colEq
:::

:::parserAlias lineEq
:::


::::keepEnv
:::example "Aligned Columns"
这种保存注释的语法采用项目符号列表，每个项目必须在同一列对齐。
```lean
syntax "note " ppLine withPosition((colEq "◦ " str ppLine)+) : term
```

没有与此语法关联的精化器或宏，但解析器接受以下示例：
```lean +error (name := noteEx1)
#check
  note
    ◦ "One"
    ◦ "Two"
```
```leanOutput noteEx1
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```

该语法不要求列表相对于起始标记缩进，这将需要额外的 `withPosition` 和 `colGt`。
```lean +error (name := noteEx15)
#check
  note
◦ "One"
◦ "Two"
```
```leanOutput noteEx15
elaboration function for `«termNote__◦__»` has not been implemented
  note
    ◦ "One"
    ◦ "Two"

```


以下示例在语法上无效，因为项目符号点的列不匹配。
```syntaxError noteEx2
#check
  note
    ◦ "One"
   ◦ "Two"
```
```leanOutput noteEx2
<example>:4:3-4:4: expected end of input
```

```syntaxError noteEx2
#check
  note
   ◦ "One"
     ◦ "Two"
```
```leanOutput noteEx2
<example>:4:5-4:6: expected end of input
```
:::
::::
