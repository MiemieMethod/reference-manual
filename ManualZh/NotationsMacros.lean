/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import ManualZh.NotationsMacros.Operators
import ManualZh.NotationsMacros.Precedence
import ManualZh.NotationsMacros.Notations
import ManualZh.NotationsMacros.SyntaxDef
import ManualZh.NotationsMacros.Elab
import ManualZh.NotationsMacros.DoElab
import ManualZh.NotationsMacros.Delab

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual hiding seeAlso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "符号和宏" =>
%%%
tag := "language-extension"
%%%

不同的数学领域有自己的符号约定，并且许多符号在不同领域中以不同的含义重复使用。
重要的是，形式化开发能够使用既定的符号：形式化数学已经很困难，并且语法之间翻译的心理开销可能很大。
同时，能够控制符号扩展的范围也很重要。
许多领域使用具有不同含义的相关符号，并且应该可以将这些单独领域的发展结合起来，使读者和系统都知道在文件的任何给定区域中哪个约定有效。

Lean 通过多种机制解决符号可扩展性问题，每种机制解决问题的不同方面。
它们可以灵活组合以达到必要的结果：

 * {ref "parser"}_extensible parser_ {index}[parser] 允许以声明方式实现多种符号约定，并灵活组合。
 * {ref "macro-and-elab"}[宏] 允许将新语法轻松映射到现有语法，这是为新构造提供含义的简单方法。
  由于 {tech}[卫生] 和源位置的自动传播，此过程不会干扰 Lean 的交互功能。
 * {ref "macro-and-elab"}[Elaborators] 提供新语法，在宏表达能力不足的情况下，可使用与 Lean 自己的语法相同的工具。
 * {ref "notations"}[符号] 允许同时定义解析器扩展、宏和漂亮的打印机。
   定义中缀、前缀或后缀运算符时，{ref "operators"}[自定义运算符] 自动处理优先级和关联性。
 * 低级解析器扩展允许解析器以修改其标记和空格规则的方式进行扩展，甚至完全替换 Lean 的语法。这是一个高级主题，需要熟悉 Lean 内部结构；尽管如此，在不修改编译器的情况下完成此操作的可能性很重要。本参考手册是使用语言扩展编写的，该语言扩展用类似 Markdown 的语言来替换 Lean 的具体语法来编写文档，但源文件仍然是 Lean 文件。

{include 0 ManualZh.NotationsMacros.Operators}

{include 0 ManualZh.NotationsMacros.Precedence}

{include 0 ManualZh.NotationsMacros.Notations}

{include 0 ManualZh.NotationsMacros.SyntaxDef}

# 宏
%%%
tag := "macros"
%%%

{deftech}_Macros_ 是在 {tech (key := "elaborator") -normalize}[精化] 和 {ref "tactic-macros"}[策略执行] 期间发生的从 {name Lean.Syntax}`Syntax` 到 {name Lean.Syntax}`Syntax` 的转换。
用宏转换的结果替换语法称为 {deftech}_宏扩展_。
多个宏可以与单个 {tech}[语法类型] 关联，并且按定义顺序尝试它们。
宏在 {tech}[monad] 中运行，该 {tech}[monad] 可以访问一些编译时元数据，并且能够发出错误消息或委托给后续宏，但宏 monad 的功能远不如精化monad 强大。

```lean -show
section
open Lean (Syntax MacroM)
```

宏与 {tech}[语法类型] 关联。
内部表将语法类型映射到 {lean}`Syntax → MacroM Syntax` 类型的宏。
宏通过抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常委托给表中的下一个条目。
当一个给定的 {name}`Syntax` 值_是一个宏_时，存在与其语法类型关联且不会抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 的宏。
如果宏引发任何其他异常，则会向用户报告错误。
{tech}[语法类别]与宏展开无关；然而，由于每种语法类型通常与单个语法类别相关联，因此它们在实践中不会产生干扰。

::::keepEnv
:::example "Macro Error Reporting"
当以下宏的参数为文字数字 5 时，将报告错误。
它扩展到所有其他情况下的论点。
```lean
syntax &"notFive" term:arg : term
open Lean in
macro_rules
  | `(term|notFive 5) =>
    Macro.throwError "'5' is not allowed here"
  | `(term|notFive $e) =>
    pure e
```

当应用于语法上不是数字 5 的术语时，精化成功：
```lean (name := notFiveAdd)
#eval notFive (2 + 3)
```
```leanOutput notFiveAdd
5
```

当错误情况被触发时，用户会收到一条错误消息：
```lean (name := notFiveFive) +error
#eval notFive 5
```
```leanOutput notFiveFive
'5' is not allowed here
```
:::
::::

在详细精化一段语法之前，精化器检查其 {tech}[语法类型] 是否具有与其关联的宏。
这些是按顺序尝试的。
如果宏成功，可能返回不同类型的语法，则重复检查并再次扩展宏，直到最外层语法不再是宏。
然后可以继续执行精化或策略。
仅扩展最外层语法（通常为 {name Lean.Syntax.node}`node`），并且宏展开的输出可能包含作为宏的嵌套语法。
当精化器到达这些嵌套宏时，它们将依次展开。

特别是，宏展开在 Lean 中出现在三种情况下：

 1. 在术语精化期间，要详细说明的语法最外层中的宏在调用 {ref "elaborators"}[语法术语精化器] 之前展开。

 2. 在命令精化期间，要详细说明的语法最外层的宏在调用 {ref "elaborators"}[语法的命令精化器] 之前展开。

 3. 在策略执行期间，要详细说明的语法最外层中的宏将扩展 {ref "tactic-macros"}[在将语法作为策略执行之前]。


```lean -keep -show
-- Test claim in preceding paragraph that it's OK for macros to give up prior to elab
syntax "doubled " term:arg : term

macro_rules
  | `(term|doubled $n:num) => `($n * 2)
  | `(term|doubled $_) => Lean.Macro.throwUnsupported

/-- info: 10 -/
#check_msgs in
#eval doubled 5

/--
error: elaboration function for `termDoubled_` has not been implemented
  doubled (5 + 2)
-/
#check_msgs in
#eval doubled (5 + 2)

elab_rules : term
  | `(term|doubled $e:term) => Lean.Elab.Term.elabTerm e none

/-- info: 7 -/
#check_msgs in
#eval doubled (5 + 2)
```

## 卫生
%%%
tag := "macro-hygiene"
%%%

如果宏的扩展无法导致标识符捕获，则该宏为 {deftech (key:="hygiene")}_hygienic_。
{deftech}[标识符捕获]是指标识符最终引用了源代码中该标识符出现的范围之外的绑定位点。
标识符捕获有两种类型：
 * 如果宏的扩展引入了绑定器，那么作为宏参数的标识符最终可能会引用引入的绑定器（如果它们的名称恰好匹配）。
 * 如果宏的扩展旨在引用一个名称，但该宏在本地绑定该名称或引入了新的全局名称的上下文中使用，则它最终可能会引用错误的名称。

第一种变量捕获可以通过确保宏引入的每个绑定都使用新生成的全局唯一名称来避免，而第二种变量捕获可以通过始终使用完全限定名称来引用常量来避免。
每次调用宏时都必须再次生成新名称，以避免递归宏中的变量捕获。
这些技术很容易出错。
变量捕获问题很难测试，因为它们依赖于名称选择的巧合，并且一致地应用这些技术会产生嘈杂的代码。

Lean 具有自动卫生功能：几乎在所有情况下，宏都会自动卫生。
通过使用 {deftech}_macroscopes_ 对宏引入的标识符进行注释，可以避免引入的绑定捕获，该标识符唯一标识宏展开的每次调用。
如果标识符的绑定和使用具有相同的宏范围，则它们是通过宏展开的同一步骤引入的，并且应该相互引用。
同样，宏生成的代码中全局名称的使用不会被扩展上下文中的本地绑定捕获，因为这些使用站点具有绑定出现中不存在的宏范围。
通过使用在宏主体中生成的代码中在引用时匹配的一组全局名称来注释潜在的全局名称引用，可以防止新引入的全局名称的捕获。
用潜在引用对象注释的标识符称为 {deftech}_预解析标识符_，并且 {name}`Syntax.ident` 构造函数上的 {lean}`Syntax.Preresolved` 字段用于存储潜在引用对象。
在精化期间，如果标识符具有与其关联的预解析全局名称，则其他全局名称不会被视为有效的引用目标。

宏作用域和预解析标识符的引入发生在 {tech}[quotation] 期间。
通过引用以外的其他方式构造语法的宏也应该通过其他方式确保卫生。
有关Lean卫生算法的更多详细信息，请查阅{citet beyondNotations ullrich23}[]。

## 宏观单子
%%%
tag := "macro-monad"
%%%

宏单子 {name Lean.MacroM}`MacroM` 足够强大，可以实现卫生和报告错误。
宏展开无法直接修改环境、执行统一、检查当前本地上下文或执行任何仅在特定上下文中有意义的其他操作。
这允许在整个 Lean 中使用相同的宏机制，并且它使宏的编写比 {tech}[elaborators] 容易得多。

{docstring Lean.MacroM}

{docstring Lean.Macro.expandMacro?}

{docstring Lean.Macro.trace}

### 异常和错误
%%%
tag := "macro-exceptions"
%%%

{name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常用于宏展开期间的控制流。
它表明当前宏无法扩展接收到的语法，但尚未发生错误。
{name Lean.Macro.throwError}`throwError` 和 {name Lean.Macro.throwErrorAt}`throwErrorAt` 引发的异常终止宏展开，并向用户报告错误。

{docstring Lean.Macro.throwUnsupported}

{docstring Lean.Macro.Exception.unsupportedSyntax}

{docstring Lean.Macro.throwError}

{docstring Lean.Macro.throwErrorAt}

### 卫生相关操作
%%%
tag := "macro-monad-hygiene"
%%%

{tech}[Hygiene] 是通过将 {tech}[宏范围] 添加到语法中出现的标识符来实现的。
通常，{tech}[quotation] 的过程会添加所有必要的作用域，但直接构造语法的宏必须将宏作用域添加到它们引入的标识符中。

{docstring Lean.Macro.withFreshMacroScope}

{docstring Lean.Macro.addMacroScope}

### 查询环境
%%%
tag := "macro-environment"
%%%

宏对查询环境的支持非常有限。
他们可以检查常量是否存在并解析名称，但无法进行进一步的内省。

{docstring Lean.Macro.hasDecl}

{docstring Lean.Macro.getCurrNamespace}

{docstring Lean.Macro.resolveNamespace}

{docstring Lean.Macro.resolveGlobalName}

## 引述
%%%
tag := "quotation"
%%%

{deftech}_Quotation_ 标记用于表示为 {name}`Syntax` 类型数据的代码。
引用的代码已被解析，但未详细说明 - 虽然它在语法上必须正确，但不一定有意义。
引用使得以编程方式生成代码变得更加容易：无需对 Lean 解析器将生成的 {name Lean.Syntax.node}`node` 值的特定嵌套进行逆向工程，而是可以直接调用解析器来创建它们。
这在面对可能改变解析树的内部结构而不影响用户可见的具体语法的语法重构时也更加稳健。
Lean 中的报价被 `` `( `` and `)` 包围。

被引用的语法类别或解析器可以通过将其名称放在左反引号和括号后面，后跟竖线（`|`）来指示。
作为特殊情况，名称 `tactic` 可用于解析策略或策略的序列。
如果未提供语法类别或解析器，Lean 会尝试将引用解析为术语和非空命令序列。
术语引用比命令引用具有更高的优先级，因此在有歧义的情况下，选择将解释为术语；这可以通过明确指示引用是命令序列来覆盖。

::::keepEnv
:::example "Term vs Command Quotation Syntax"
```lean -show
open Lean
```

在下面的示例中，引用的内容可以是函数应用程序，也可以是命令序列。
两者都匹配文件的同一区域，因此 {tech}[本地最长匹配规则] 不相关。
术语引用的优先级高于命令引用，因此引用被解释为术语。
条款期望其 {tech}[反引号] 具有类型 {lean}``TSyntax `term`` rather than {lean}``TSyntax `command``。
```lean +error (name := cmdQuot)
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) :=
  `($cmd1 $cmd2)
```
结果是两个类型错误，如下所示：
```leanOutput cmdQuot
Application type mismatch: The argument
  cmd1
has type
  TSyntax `command
but is expected to have type
  TSyntax `term
in the application
  cmd1.raw
```

引号的类型 ({lean}``MacroM (TSyntax `command)``) 不用于选择结果，因为语法优先级先于精化应用。
在这种情况下，指定反引号是命令可以解决歧义，因为函数应用程序需要在这些位置使用术语：
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) :=
  `($cmd1:command $cmd2:command)
```
同样，在引用中插入命令可以消除它可能是术语的可能性：
```lean
example (cmd1 cmd2 : TSyntax `command) : MacroM (TSyntax `command) :=
  `($cmd1 $cmd2 #eval "hello!")
```
:::
::::

```lean -show
-- There is no way to extract parser priorities (they're only saved in the Pratt tables next to
-- compiled Parser code), so this test of priorities checks the observable relative priorities of the
-- quote parsers.

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `term)
-/
#check_msgs in
#check (`($(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node2 info `Lean.Parser.Term.app { raw := Syntax.missing }.raw
            (Syntax.node1 info `null { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `term)
-/
#check_msgs in
#check (`($(⟨.missing⟩) $(⟨.missing⟩)) : MacroM _)
/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node2 info `null { raw := Syntax.missing }.raw
            { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `command)
-/
#check_msgs in
#check (`($(⟨.missing⟩):command $(⟨.missing⟩)) : MacroM _)

/--
info: do
  let _ ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure { raw := { raw := Syntax.missing }.raw } : MacroM (Lean.TSyntax `tactic)
-/
#check_msgs in
#check (`(tactic| $(⟨.missing⟩):tactic) : MacroM _)

/--
info: do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let _ ← Lean.getCurrMacroScope
  let _ ← Lean.MonadQuotation.getContext
  pure
      {
        raw :=
          Syntax.node1 info `Lean.Parser.Tactic.seq1
            (Syntax.node3 info `null { raw := Syntax.missing }.raw (Syntax.atom info ";")
              { raw := Syntax.missing }.raw) } : MacroM (Lean.TSyntax `tactic.seq)
-/
#check_msgs in
#check (`(tactic|
          $(⟨.missing⟩):tactic; $(⟨.missing⟩)) : MacroM _)
```

:::freeSyntax term -open (title := "Quotations")

Lean 的语法包括术语、命令、策略和策略序列的引用，以及允许引用 Lean 可以解析的任何输入的通用引用语法。
术语引用的优先级最高，其次是策略引用、一般引用，最后是命令引用。

```grammar
`(term|`($_:term))
*******
"`("$_:command+")"
*******
`(term|`(tactic| $_:tactic))
*******
`(term|`(tactic| $_:tactic;*))
*******
"`("p:ident"|"/-- Parse a {p} here -/")"
```
:::

```lean -show
section M
variable {m : Type → Type}
open Lean (MonadRef MonadQuotation)
open Lean.Elab.Term (TermElabM)
open Lean.Elab.Command (CommandElabM)
open Lean.Elab.Tactic (TacticM)
```

引用不是类型 {name}`Syntax`，而是类型为 {lean}`m Syntax` 的单子操作。
引用是一元的，因为它通过添加 {tech}[宏范围] 和预解析标识符来实现 {tech}[卫生]，如 {ref "macro-hygiene"}[卫生部分] 中所述。
要使用的特定 monad 是引用的隐式参数，任何具有 {name}`MonadQuotation` 类型类实例的 monad 都适用。
{name}`MonadQuotation` 扩展了 {name}`MonadRef`，这使引用能够访问宏扩展器或精化器当前正在处理的语法的源位置。 {name}`MonadQuotation` 还包括将 {tech}[宏范围] 添加到标识符并为子任务使用新的宏范围的功能。
支持报价的 Monad 包括 {name}`MacroM`、{name}`TermElabM`、{name}`CommandElabM` 和 {name}`TacticM`。

```lean -show
end M
```


```lean -show
-- Verify claim about monads above
open Lean in
example [Monad m] [MonadQuotation m] : m Syntax := `(term|2 + 2)
```

### 准报价
%%%
tag := "quasiquotation"
%%%

{deftech}_Quasiquotation_ 是一种可能包含 {deftech}_antiquotations_ 的引用形式，{deftech}_antiquotations_ 是未引用的引用区域，而是计算结果语法的表达式。
准引用本质上是一个模板；外部引用区域提供了一个固定的框架，始终产生相同的外部语法，而反引号产生最终语法中不同的部分。
Lean 中的所有引用都是准引用，因此不需要特殊语法来区分准引用和其他引用。
引用过程不会将宏作用域添加到通过反引号插入的标识符，因为这些标识符要么来自另一个引用（在这种情况下它们已经具有宏作用域），要么来自宏的输入（在这种情况下它们不应该具有宏作用域，因为它们不是由宏引入的）。

基本反引号由美元符号 (`$`) 和紧随其后的标识符组成。
这意味着相应变量的值（应该是语法树）将被替换到引用语法的这个位置。
通过将整个表达式括在括号中，可以将其用作反引号。

```lean -show
section
open Lean
example (e : Term) : MacroM Syntax := `(term| $e)

example (e : Term) : MacroM Syntax := `(term| $(e))

--example (e : Term) : MacroM Syntax := `(term| $ (e))

end
```



```lean -show
section
open Lean (TSyntax SyntaxNodeKinds)
variable {c : SyntaxNodeKinds}
```

Lean 的解析器根据解析器在给定位置的期望为每个反引号分配一个语法类别。
如果解析器需要语法类别 {lean}`c`，则反引号的类型为 {lean}`TSyntax c`。


某些语法类别可以与其他类别的元素相匹配。
例如，数字和字符串文字除了是它们自己的语法类别之外，也是有效的术语。
反引号可以通过在反引号后面加上冒号和类别名称来注释预期类别，这会导致解析器验证带注释的类别在给定位置是否可接受，并构造解析树中所需的任何中间层。

:::freeSyntax antiquot (title := "Antiquotations") -open
```grammar
"$"ident(":"ident)?
*******
"$("term")"(":"ident)?
```
启动反引号的美元符号（“$”）与后面的标识符或括号内的术语之间不允许有空格。
同样，注释反引号的语法类别的冒号周围不允许有空格。
:::

:::example "Quasiquotation"

本例中使用了两种形式的反引号。
由于自然数不是语法，因此 {name Lean.quote}`quote` 用于将数字转换为表示它的语法。

```lean
open Lean in
example [Monad m] [MonadQuotation m] (x : Term) (n : Nat) : m Syntax :=
  `($x + $(quote (n + 2)))
```
:::

:::::keepEnv
::::example "Antiquotation Annotations"
```lean -show
open Lean
```

此示例要求 {lean}`m` 是一个可以进行报价的 monad。
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

默认情况下，反引号 `$e` 应该是一个术语，因为这是立即预期作为加法的第二个参数的语法类别。
```lean (name := ex1)
def ex1 (e) := show m _ from `(2 + $e)
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `term) : m (TSyntax `term)
```

将 `$e` 注释为数字文字会成功，因为数字文字也是有效术语。
参数 `e` 的预期类型更改为 ``TSyntax `num``。
```lean (name := ex2)
def ex2 (e) := show m _ from `(2 + $e:num)
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (e : TSyntax `num) : m (TSyntax `term)
```

美元符号和标识符之间不允许有空格。
```syntaxError ex2err1
def ex2 (e) := show m _ from `(2 + $ e:num)
```
```leanOutput ex2err1
<example>:1:34-1:36: unexpected token '$'; expected '`(tactic|' or no space before spliced term
```

冒号之前也不允许有空格：
```syntaxError ex2err2
def ex2 (e) := show m _ from `(2 + $e :num)
```
```leanOutput ex2err2
<example>:1:37-1:39: unexpected token ':'; expected ')'
```
::::
:::::

```lean -show
end
```

:::::keepEnv
::::example "Expanding Quasiquotation"
打印 {name}`f` 的定义演示了准引用的扩展。
```lean (name := expansion)
open Lean in
def f [Monad m] [MonadQuotation m]
    (x : Term) (n : Nat) : m Syntax :=
  `(fun k => $x + $(quote (n + 2)) + k)
#print f
```
```leanOutput expansion
def f : {m : Type → Type} → [Monad m] → [Lean.MonadQuotation m] → Lean.Term → Nat → m Syntax :=
fun {m} [Monad m] [Lean.MonadQuotation m] x n => do
  let info ← Lean.MonadRef.mkInfoFromRefPos
  let scp ← Lean.getCurrMacroScope
  let quotCtx ← Lean.MonadQuotation.getContext
  pure
      {
          raw :=
            Syntax.node2 info `Lean.Parser.Term.fun (Syntax.atom info "fun")
              (Syntax.node4 info `Lean.Parser.Term.basicFun
                (Syntax.node1 info `null (Syntax.ident info "k".toRawSubstring' (Lean.addMacroScope quotCtx `k scp) []))
                (Syntax.node info `null #[]) (Syntax.atom info "=>")
                (Syntax.node3 info `«term_+_»
                  (Syntax.node3 info `«term_+_» x.raw (Syntax.atom info "+") (Lean.quote `term (n + 2)).raw)
                  (Syntax.atom info "+")
                  (Syntax.ident info "k".toRawSubstring' (Lean.addMacroScope quotCtx `k scp) []))) }.raw
```

:::paragraph
```lean -show
section
open Lean (Term)
open Lean.Quote
variable {x : Term} {n : Nat}
```

在此输出中，报价是 {keywordOf Lean.Parser.Term.do}`do` 块。
它首先构建结果语法的源信息，这些信息是通过向编译器查询当前正在处理的用户语法而获得的。
然后，它获取当前宏作用域和正在处理的模块的名称，因为宏作用域是相对于模块添加的，以实现独立编译并避免需要全局计数器。
然后，它使用 {name}`Syntax.node1` 和 {name}`Syntax.node2` 等帮助器构造一个节点，这些帮助器创建一个具有指定数量的子节点的 {name}`Syntax.node`。
宏作用域被添加到每个标识符，并且 {name Lean.TSyntax.raw}`TSyntax.raw` 用于提取类型化语法包装器的内容。
{lean}`x` 和 {lean  (type := "Term")}`quote (n + 2)` 的反引号直接出现在扩展中，作为 {name}`Syntax.node3` 的参数。

```lean -show
end
```
:::

::::
:::::


### 接头
%%%
tag := "splices"
%%%

除了通过反引号包括其他语法之外，准引号还可以包括 {deftech}_splices_。
拼接表示数组的元素按顺序插入。
重复的元素可以包括分隔符，例如列表或数组元素之间的逗号。
拼接可以由带有 {deftech}_splice 后缀_的普通反引号组成，或者它们可以是 {deftech}_扩展拼接_，提供额外的重复结构。

剪接后缀由星号或有效原子后跟星号 (`*`) 组成。
后缀可以跟在任何标识符或术语反引号后面。
带有拼接后缀 `*` 的反引号对应于 `many` 或 `many1` 的使用；语法规则中的 `*` 和 `+` 后缀均对应于 `*` 剪接后缀。
带有在星号之前包含原子的剪接后缀的反引号对应于 `sepBy` 或 `sepBy1` 的使用。
拼接后缀 `?` 对应于语法规则中 `optional` 或 `?` 后缀的使用。
由于 `?` 是有效的标识符字符，因此标识符必须加括号才能将其用作后缀。

虽然语法的重复说明符和反引号后缀之间存在重叠，但它们具有不同的语法。
定义语法时，后缀 `*`、`+`、`,*`、`,+`、`,*,?` 和 `,+,?` 内置于 Lean。
除了 `,` 之外，没有更短的方法来指定分隔符。
反引号后缀要么只是 `*`，要么是提供给 `sepBy` 或 `sepBy1` 的任何原子，后跟 `*`。
语法重复`+`和`*`对应于拼接后缀`*`；重复 `,*`、`,+`、`,*,?` 和 `,+,?` 对应于 `,*`。
语法和拼接中的可选后缀`?`相互对应。


:::table +header
 * - 语法重复
   - 拼接后缀
 * - `+` `*`
   - `*`
 * - `,*` `,+` `,*,?` `,+,?`
   - `,*`
 * - `sepBy(_, "S")` `sepBy1(_, "S")`
   - `S*`
 * - `?`
   - `?`
:::


::::keepEnv
:::example "Suffixed Splices"
```imports -show
import Lean.Elab
```
```lean -show
open Lean
open Lean.Elab.Command (CommandElabM)
```

此示例要求 {lean}`m` 是一个可以进行报价的 monad。
```lean
variable {m : Type → Type} [Monad m] [MonadQuotation m]
```

默认情况下，反引号 `$e` 应该是由逗号分隔的术语数组，正如列表正文中所期望的那样：
```lean (name := ex1)
def ex1 (xs) := show m _ from `(#[$xs,*])
#check ex1
```
```leanOutput ex1
ex1 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Syntax.TSepArray `term ",") : m (TSyntax `term)
```

但是，Lean 包含各种数组表示之间的强制转换集合，这些数组将自动插入或删除分隔符，因此普通的术语数组也是可以接受的：
```lean (name := ex2)
def ex2 (xs : Array (TSyntax `term)) :=
  show m _ from `(#[$xs,*])
#check ex2
```
```leanOutput ex2
ex2 {m : Type → Type} [Monad m] [MonadQuotation m] (xs : Array (TSyntax `term)) : m (TSyntax `term)
```

重复注释也可以与术语反引号和语法类别注释一起使用。
该示例位于 {name Lean.Elab.Command.CommandElabM}`CommandElabM` 中，因此可以方便地记录结果。
```lean (name := ex3)
def ex3 (size : Nat) := show CommandElabM _ from do
  let mut nums : Array Nat := #[]
  for i in [0:size] do
    nums := nums.push i
  let stx ← `(#[$(nums.map (Syntax.mkNumLit ∘ toString)):num,*])
  -- Using logInfo here causes the syntax to be rendered via
  -- the pretty printer.
  logInfo stx

#eval ex3 4
```
```leanOutput ex3
#[0, 1, 2, 3]
```
:::
::::

::::keepEnv
:::example "Non-Comma Separators"
以下列表的非常规语法通过长破折号或双星号而不是逗号分隔数字元素。
```lean
syntax "⟦" sepBy1(num, " — ") "⟧": term
syntax "⟦" sepBy1(num, " ** ") "⟧": term
```
这意味着 `—*` 和 `***` 是 `⟦` 和 `⟧` 原子之间的有效剪接后缀。
对于 `***`，前两个星号是语法规则中的原子，而第三个星号是重复后缀。
```lean
macro_rules
  | `(⟦$n:num—*⟧) => `(⟦$n***⟧)
  | `(⟦$n:num***⟧) => `([$n,*])
```
```lean (name := nonComma)
#eval ⟦1 — 2 — 3⟧
```
```leanOutput nonComma
[1, 2, 3]
```
:::
::::

::::keepEnv
:::example "Optional Splices"
```imports -show
import Lean.Elab
```
以下语法声明可以选择匹配两个标记之间的术语。
嵌套的 `term` 周围需要括号，因为 `term?` 是有效标识符。
```lean -show
open Lean
```
```lean
syntax "⟨| " (term)? " |⟩": term
```

术语的 `?` 拼接后缀需要 {lean}`Option Term`：
```lean
def mkStx [Monad m] [MonadQuotation m]
    (e : Option Term) : m Term :=
  `(⟨| $(e)? |⟩)
```
```lean (name := checkMkStx)
#check mkStx
```
```leanOutput checkMkStx
mkStx {m : Type → Type} [Monad m] [MonadQuotation m] (e : Option Term) : m Term
```

提供 {name}`some` 会导致可选术语出现。
```lean (name := someMkStx)
#eval do logInfo (← mkStx (some (quote 5)))
```
```leanOutput someMkStx
⟨| 5 |⟩
```

提供 {name}`none` 会导致可选术语不存在。
```lean (name := noneMkStx)
#eval do logInfo (← mkStx none)
```
```leanOutput noneMkStx
⟨| |⟩
```

:::
::::

```lean -show
section
open Lean Syntax
variable {k k' : SyntaxNodeKinds} {sep : String} [Coe (TSyntax k) (TSyntax k')]
-- Demonstrate the coercions between different kinds of repeated syntax

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSyntaxArray k) (TSepArray k' sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (Array (TSyntax k)) (TSepArray k sep)

/-- info: instCoeHTCTOfCoeHTC -/
#check_msgs in
#synth CoeHTCT (TSepArray k sep) (TSyntaxArray k)

end
```

### 令牌反引号
%%%
tag := "token-antiquotations"
%%%

除了完整语法的反引号之外，Lean 还具有 {deftech}_token antiquotations_ 功能，它允许原子的源信息替换为其他语法的源信息。
生成的合成源信息被标记为 {tech}[canonical]，以便它将用于错误消息、证明状态和其他反馈。
这主要用于控制 Lean 向用户报告的错误消息或其他信息的放置。
令牌反引号不允许通过求值插入任意原子。
标记反引号由一个原子（即关键字）组成

:::freeSyntax antiquot +open (title := "Token Antiquotations")
令牌反引号将令牌上的源信息（类型为 {name Lean.SourceInfo}`SourceInfo`）替换为其他语法中的源信息。

```grammar
atom"%$"ident
```
:::


::: TODO

带括号的更复杂拼接

:::

## 匹配语法
%%%
tag := "quote-patterns"
%%%

:::seeAlso
新语法是使用 {ref "syntax-rules"}[语法扩展] 定义的。
:::

准引号可用于模式匹配来识别与模板匹配的语法。
正如用作术语的引用中的反引号是被视为普通非引用表达式的区域一样，模式中的反引号也是被视为普通 Lean 模式的区域。
引号模式的编译方式与其他模式不同，因此它们不能与单个 {keywordOf Lean.Parser.Term.match}`match` 表达式中的非引号模式混合。
与普通引用一样，引用模式首先由 Lean 的解析器处理。
然后解析器的输出被编译成代码来确定是否存在匹配。
语法匹配假定匹配的语法是由 Lean 的解析器通过引用或直接在用户代码中生成的，并使用它来省略一些检查。
例如，如果在给定位置中只能出现特定关键字，则可以省略该检查。

在以下情况下，语法与引号模式匹配：


 : 原子

  关键字原子（例如 {keywordOf termIfThenElse}`if` 或 {keywordOf Lean.Parser.Term.match}`match`）会生成类型为 `token.` 后跟原子的单例节点。
  在许多情况下，没有必要检查特定的原子值，因为语法只允许单个关键字，并且不会执行任何检查。
  如果匹配的术语的语法需要检查，则比较节点类型。

  文字（例如字符串或数字文字）通过其底层字符串表示形式进行比较。
  模式 `` `(0x15) `` and the quotation `` `(21) `` 不匹配。

 : 节点

  如果匹配的模式和值都表示 {name}`Syntax.node`，则当两者具有相同的语法类型、相同的子项数并且每个子模式与相应的子值匹配时，存在匹配。

 : 标识符

  如果匹配的模式和值都是标识符，则比较它们的文字 {name Lean.Name}`Name` 值是否相等模宏范围。
  “看起来”相同的标识符匹配，并且它们是否引用相同的绑定并不重要。
  此设计选择允许在无法访问可通过引用比较名称的编译时环境的上下文中使用引用模式匹配。


由于引用模式匹配基于解析器发出的节点类型，因此如果来自不同语法类别，看起来相同的引用可能不匹配。
如果有疑问，在引用中包含语法类别会有所帮助。

:::leanSection
```lean -show
open Lean Syntax
variable {k : SyntaxNodeKinds} {sep : String}

```

由语法模式匹配绑定的变量的类型为 {lean}`TSyntax k`，其中 {lean}`k` 描述潜在的语法类型。
重复中的变量的类型为 {lean}`TSyntaxArray k`，如果重复使用字符串 {lean}`sep` 分隔，则为 {lean}`TSepArray k sep` 类型。
{name}`TSyntax` 在 {ref "typed-syntax"}[有关类型化语法的部分]中进行了更详细的描述。
:::

::::example "Syntax Pattern Matching"

```lean -show
open Lean Syntax
```

列表推导式是一种用于编写列表的表示法，其灵感来自于标准集生成器表示法。
列表推导式由方括号组成，方括号包含结果项，后跟一些_限定符_；每个限定符要么从其他列表中引入一个变量，要么强加一个必须满足的条件。
限定符是嵌套的：每个新变量的值都会针对每个先前的值进行评估。

```lean
syntax qbind := ident "←" term

syntax qpred := term

syntax qualifier := atomic(qbind) <|> qpred

syntax "[" term "|" qualifier,* "]" : term
```

列表推导式可以脱糖为对 {name}`List.flatMap` 的一系列调用。
变量引入将转换为变量值表达式上的 {name List.flatMap}`flatMap`，而谓词将转换为条件，如果谓词为 true 或 false，则返回 1 或 0 值。
最终 {name List.flatMap}`flatMap` 的主体是结果项。

这种脱糖可以作为使用准引用模式的宏来实现：
```lean
macro_rules
  | `(term|[$e | $qs,* ]) => do
    let init ← `([$e])
    qs.getElems.foldrM (β := Term) (init := init) fun
      | `(qualifier|$x ← $e'), r =>
        `(($e' : List _) |>.flatMap fun $x => $r)
      | `(qualifier|$e':term), r =>
        `((if $e' then [()] else []) |>.flatMap fun () => $r)
      | other, _ =>
        Macro.throwErrorAt other "Unknown qualifier"
```
最初，限定符序列的类型为 {lean}``TSepArray `qualifier ","``，表示它表示以逗号分隔的限定符序列。
{lean}`TSepArray.getElems` 将其转换为 {lean}``TSyntaxArray `qualifier``, which is an abbreviation for {lean}``Array (TSyntax `qualifier)``。
这允许使用 {tech}[通用字段表示法] 来调用 {name}`Array.foldrM`。
谓词分支中需要 `term` 注释，以防止匹配值具有语法类型 {lean}`` `qualifier ``；必须从该值中解开一个 {name Syntax.node}`node`。

列表推导式的行为符合预期：
```lean (name := evalComp)
#eval [ s!"{x}; {y}" |
  x ← (1...5).toList,
  x % 2 = 0,
  y ← [true, false]
]
```
```leanOutput evalComp
["2; true", "2; false", "4; true", "4; false"]
```
::::

## 定义宏
%%%
tag := "defining-macros"
%%%


定义宏有两种主要方法：{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令和 {keywordOf Lean.Parser.Command.macro}`macro` 命令。
{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令将宏与现有语法相关联，而 {keywordOf Lean.Parser.Command.macro}`macro` 命令同时定义新语法和将其转换为现有语法的宏。
{keywordOf Lean.Parser.Command.macro}`macro` 命令可以看作是 {keywordOf Lean.Parser.Command.notation}`notation` 的概括，它允许以编程方式生成扩展，而不是简单地通过替换来生成。

### `macro_rules` 命令
%%%
tag := "macro_rules"
%%%

:::syntax command (title := "Rule-Based Macros With {keyword}`macro_rules`")

{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令采用一系列重写规则（指定为语法模式匹配），并将每个规则添加为宏。
在先前定义的宏之前按顺序尝试规则，稍后的宏定义可能会添加更多宏规则。

```grammar
$[$d:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro_rules $[(kind := $k)]?
  $[| `(free{(p:ident"|")?/-- Suitable syntax for {p} -/}) => $e]*
```
:::

宏中的模式必须是引用模式。
它们可以匹配任何语法类别的语法，但给定的模式只能匹配单一语法类型。
如果没有为引用指定类别或解析器，则它可能匹配术语或命令（序列），但绝不会两者都匹配。
为了避免歧义，选择术语“解析器”。

在内部，宏在一个表中进行跟踪，该表将每个 {tech}[语法类型] 映射到其宏。
{keywordOf Lean.Parser.Command.macro_rules}`macro_rules`命令可以用语法类型明确地注释。

如果显式提供了语法类型，则宏定义会检查每个引用模式是否具有该类型。
如果引用的解析结果是 {tech}[选择节点]（即，如果解析不明确），则对于具有指定类型的每个替代项，模式都会重复一次。
如果没有一个替代方案具有指定的类型，则这是一个错误。

如果没有明确提供种类，则解析器确定的种类将用于每个模式。
这些模式不需要全部具有相同的语法类型；宏是为至少一种模式使用的每种语法类型定义的。
如果引用模式的解析结果是 {tech}[选择节点]（即，如果解析不明确），则这是一个错误。

如果语法本身没有文档注释，则会向用户显示与 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 关联的文档注释。
否则，将显示语法本身的文档注释。

与 {ref "notations"}[符号] 和 {ref "operators"}[运算符] 一样，宏规则可以声明为 `scoped` 或 `local`。
作用域宏仅在当前命名空间打开时才有效，本地宏规则仅在当前 {tech}[节范围] 中有效。

::::keepEnv
:::example "Idiom Brackets"
习语括号是使用应用函子的另一种语法。
如果习语括号包含函数应用程序，则该函数将包装在 {name}`pure` 中，并使用 `<*>` 应用于每个参数。 {TODO}[操作员超链接到文档]
Lean 默认不支持习语括号，但可以使用宏定义它们。
```lean
syntax (name := idiom) "⟦" (term:arg)+ "⟧" : term

macro_rules
  | `(⟦$f $args*⟧) => do
    let mut out ← `(pure $f)
    for arg in args do
      out ← `($out <*> $arg)
    return out
```

这个新语法可以立即使用。
```lean
def addFirstThird [Add α] (xs : List α) : Option α :=
  ⟦Add.add xs[0]? xs[2]?⟧
```
```lean (name := idiom1)
#eval addFirstThird (α := Nat) []
```
```leanOutput idiom1
none
```
```lean (name := idiom2)
#eval addFirstThird [1]
```
```leanOutput idiom2
none
```
```lean (name := idiom3)
#eval addFirstThird [1,2,3,4]
```
```leanOutput idiom3
some 4
```
:::
::::

::::keepEnv
:::example "Scoped Macros"
```lean -show
open Lean
```
作用域宏规则仅在其命名空间中有效。
当命名空间 `ConfusingNumbers` 打开时，数字文字将被分配错误的含义。
```lean
namespace ConfusingNumbers
```

以下宏识别奇数数字文字的术语，并将其替换为其值的两倍。
如果它无条件地将它们替换为两倍的值，则宏展开将成为无限循环，因为相同的规则始终与输出匹配。

```lean
scoped macro_rules
  | `($n:num) => do
    if n.getNat % 2 = 0 then Lean.Macro.throwUnsupported
    let n' := (n.getNat * 2)
    `($(Syntax.mkNumLit (info := n.raw.getHeadInfo) (toString n')))
```

一旦命名空间结束，宏就不再使用。
```lean
end ConfusingNumbers
```

在不打开命名空间的情况下，数字文字将以通常的方式运行。
```lean (name := nums1)
#eval (3, 4)
```
```leanOutput nums1
(3, 4)
```

当命名空间打开时，宏将 {lean}`3` 替换为 {lean}`6`。
```lean (name := nums2)
open ConfusingNumbers

#eval (3, 4)
```
```leanOutput nums2
(6, 4)
```

更改宏中数字或其他文字的解释通常没有用。
然而，当向可扩展策略添加新规则（例如 {tactic}`trivial`）时，范围宏非常有用，这些规则可以很好地处理命名空间的内容，但不应始终使用。
:::
::::

在幕后，{keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令为与其引号模式匹配的每种语法类型生成一个宏函数。
该函数有一个默认情况，会抛出 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常，因此可以尝试进一步的宏。


具有两个规则的单个 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令并不总是相当于两个单独的单匹配命令。
首先，从上到下尝试 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 中的规则，但首先尝试最近声明的宏，因此需要颠倒顺序。
此外，如果宏中较早的规则引发 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常，则不会尝试较晚的规则；如果它们位于单独的 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令中，则将尝试它们。

::::example "One vs. Two Sets of Macro Rules"
```lean -show
open Lean.Macro
```

`arbitrary!` 宏旨在扩展为给定类型的某个任意确定的值。

```lean
syntax (name := arbitrary!) "arbitrary! " term:arg : term
```

:::keepEnv
```lean
macro_rules
  | `(arbitrary! ()) => `(())
  | `(arbitrary! Nat) => `(42)
  | `(arbitrary! ($t1 × $t2)) => `((arbitrary! $t1, arbitrary! $t2))
  | `(arbitrary! Nat) => `(0)
```

用户可以通过定义更多的宏规则集来扩展它，例如失败的 {lean}`Empty` 规则：
```lean
macro_rules
  | `(arbitrary! Empty) => throwUnsupported
```

```lean (name := arb1)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb1
(42, 42)
```
:::

:::keepEnv
如果所有宏规则都被定义为单独的情况，则结果将改为使用 {lean}`Nat` 的后一种情况。
这是因为单个 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令中的规则是从上到下检查的，但最近定义的 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令优先于较早的命令。

```lean
macro_rules
  | `(arbitrary! ()) =>
    `(())
macro_rules
  | `(arbitrary! Nat) =>
    `(42)
macro_rules
  | `(arbitrary! ($t1 × $t2)) =>
    `((arbitrary! $t1, arbitrary! $t2))
macro_rules
  | `(arbitrary! Nat) =>
    `(0)
macro_rules
  | `(arbitrary! Empty) =>
    throwUnsupported
```

```lean (name := arb2)
#eval arbitrary! (Nat × Nat)
```
```leanOutput arb2
(0, 0)
```
:::

此外，如果任何规则引发 {name Lean.Macro.Exception.unsupportedSyntax}`unsupportedSyntax` 异常，则不会检查该命令中的其他规则。
```lean
macro_rules
  | `(arbitrary! (List Nat)) => throwUnsupported
  | `(arbitrary! (List $_)) => `([])

macro_rules
  | `(arbitrary! (Array Nat)) => `(#[42])
macro_rules
  | `(arbitrary! (Array $_)) => throwUnsupported
```

{lean}`List Nat` 的情况无法详细说明，因为宏展开未将 {keywordOf arbitrary!}`arbitrary!` 语法转换为精化器支持的语法。
```lean (name := arb3) +error
#eval arbitrary! (List Nat)
```
```leanOutput arb3
elaboration function for `arbitrary!` has not been implemented
  arbitrary! (List Nat)
```

{lean}`Array Nat` 的情况成功，因为在第二组宏规则引发异常后尝试第一组宏规则。
```lean (name := arb4)
#eval arbitrary! (Array Nat)
```
```leanOutput arb4
#[42]
```
::::


### `macro` 命令
%%%
tag := "macro-command"
%%%

```lean -show
section
open Lean
```

{keywordOf Lean.Parser.Command.macro}`macro` 命令同时定义新的 {tech}[语法规则]，并将其与 {tech}[宏] 关联。
与 {keywordOf Lean.Parser.Command.notation}`notation` 不同，{keywordOf Lean.Parser.Command.notation}`notation` 只能定义新术语语法，并且其中扩展是要替换参数的术语，{keywordOf Lean.Parser.Command.macro}`macro` 命令可以在任何 {tech}[语法类别] 中定义语法，并且可以使用 {name}`MacroM` monad 中的任意代码来生成扩展。
由于宏比符号灵活得多，Lean 无法自动生成解扩展器；这意味着通过 {keywordOf Lean.Parser.Command.macro}`macro` 命令实现的新语法可用于 Lean 的_输入_，但 Lean 的输出在没有进一步工作的情况下不会使用它。

:::syntax command (title := "Macro Declarations")
```grammar
$[$_:docComment]?
$[@[$attrs,*]]?
$_:attrKind macro$[:$p]? $[(name := $_)]? $[(priority := $_)]? $xs:macroArg* : $k:ident =>
  $tm
```
:::

:::syntax Lean.Parser.Command.macroArg -open (title := "Macro Arguments")
宏的参数可以是语法项（如 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令中使用的），也可以是带有附加名称的语法项。
```grammar
$s:stx
```
```grammar
$x:ident:$stx
```
:::

在扩展中，附加到语法项的名称是绑定的；对于适当的语法类型，它们的类型为 {name Lean.TSyntax}`TSyntax`。
如果解析器匹配的语法没有定义的类型（例如，因为名称应用于复杂规范），则类型为 {lean}`TSyntax Name.anonymous`。

```lean -show -keep
-- Check the typing rules
open Lean Elab Term Macro Meta

elab "dbg_type " e:term ";" body:term : term => do
  let e' ← elabTerm e none
  let t ← inferType e'
  logInfoAt e t
  elabTerm body none

/--
info: TSyntax `str
---
info: TSyntax Name.anonymous
---
info: Syntax.TSepArray `num ","
-/
#check_msgs in
macro "gah!" thing:str other:(str <|> num) arg:num,* : term => do
  dbg_type thing; pure ()
  dbg_type other; pure ()
  dbg_type arg; pure ()
  return quote s!"{thing.raw} ||| {other.raw} ||| {arg.getElems}"

/-- info: "(str \"\\\"one\\\"\") ||| (num \"44\") ||| #[(num \"2\"), (num \"3\")]" : String -/
#check_msgs in
#check gah! "one" 44 2,3

```

文档注释与新语法相关联，属性种类（无、`local` 或 `scoped`）控制宏的可见性，就像它对符号的可见性一样：`scoped` 宏在定义它们的命名空间中或在打开该命名空间的任何 {tech}[节范围] 中可用，而 `local`宏仅在本地部分范围内可用。

在幕后，{keywordOf Lean.Parser.Command.macro}`macro` 命令本身由宏实现，该宏将其扩展为 {keywordOf Lean.Parser.Command.syntax}`syntax` 命令和 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令。
应用于宏命令的任何属性都会应用于语法定义，但不会应用于 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 命令。

```lean -show
end
```

### 宏属性
%%%
tag := "macro-attribute"
%%%

可以使用 {keywordOf Lean.Parser.Attr.macro}`macro` 属性将 {tech}[宏] 手动添加到语法类型中。
这种指定宏的低级方法通常没有用处，除非宏本身生成宏定义的代码生成结果。

:::syntax attr (title := "The {keyword}`macro` Attribute")
{keywordOf Lean.Parser.Attr.macro}`macro` 属性指定将函数视为指定语法类型的 {tech}[宏]。
```grammar
macro $_:ident
```
:::

::::keepEnv
:::example "The Macro Attribute"
```lean -show
open Lean Macro
```
```lean
/-- Generate a list based on N syntactic copies of a term -/
syntax (name := rep) "[" num " !!! " term "]" : term

@[macro rep]
def expandRep : Macro
  | `([ $n:num !!! $e:term]) =>
    let e' := Array.replicate n.getNat e
    `([$e',*])
  | _ =>
    throwUnsupported
```

计算这个新表达式表明该宏存在。
```lean (name := attrEx1)
#eval [3 !!! "hello"]
```
```leanOutput attrEx1
["hello", "hello", "hello"]
```
:::
::::

{include 0 ManualZh.NotationsMacros.Elab}

{include 0 ManualZh.NotationsMacros.DoElab}

{include 0 ManualZh.NotationsMacros.Delab}
