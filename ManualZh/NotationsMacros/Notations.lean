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

#doc (Manual) "符号" =>
%%%
tag := "notations"
%%%

术语 {deftech}_notation_ 在 Lean 中有两种使用方式：它可以指以简洁的方式记录想法的一般概念，它是允许用很少的代码方便地实现符号的语言功能的名称。
与自定义运算符一样，Lean 符号允许使用新形式扩展术语语法。
然而，符号更加通用：新语法可以自由地将所需的关键字或运算符与子术语混合在一起，并且它们提供对优先级的更精确的控制。
符号还可以在结果子项中重新排列它们的参数，而中缀运算符以固定顺序将它们提供给函数项。
由于符号可以定义混合使用前缀、中缀和后缀组件的运算符，因此它们可以称为 {deftech}_mixfix_ 运算符。

:::syntax command (title := "Notation Declarations")
符号是使用 {keywordOf Lean.Parser.Command.notation}`notation` 命令定义的。

```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind notation$[:$_:prec]? $[(name := $_:ident)]? $[(priority := $_:prio)]? $[$_:notationItem]* => $_:term
```
:::

:::syntax Lean.Parser.Command.notationItem -open (title := "Notation Items")
符号定义的主体由 {deftech}_notation items_ 序列组成，它可以是字符串文字或具有可选优先级的标识符。
```grammar
$s:str
```
```grammar
$x:ident$[:$_:prec]?
```
:::

与运算符声明一样，当用户与新语法交互时，会向用户显示文档注释的内容。
添加 {attr}`inherit_doc` 属性会导致符号扩展到的术语开头的函数文档注释被复制到新语法。
可以添加其他属性以在结果定义上调用其他编译时元程序。

符号与 {tech}[节范围] 的交互方式与属性和运算符相同。
默认情况下，符号在任何可传递导入建立符号的模块中都可用，但它们可以声明为 `scoped` 或 `local`，以分别将其可用性限制在当前名称空间已打开的上下文或当前 {tech}[节范围] 中。

与运算符一样，解析符号时使用 {tech}[本地最长匹配规则]。
如果最长匹配有多个表示法，则使用声明的优先级来确定应用哪个解析结果。
如果这仍然不能解决歧义，则所有内容都会被保存，并且精化器预计会尝试所有这些内容，当恰好有一个可以详细说明时就会成功。

符号声明的主体不是由具有固定性和标记的单个运算符组成，而是由一系列 {deftech}_notation items_ 组成，它可以是新的 {tech}[atoms]（包括 `if`、`#eval` 或 `where` 等关键字和符号，例如`=>`、`+`、`↗`、`⟦` 或 `⋉`）或条款的位置。
正如它们在运算符中所做的那样，字符串文字标识原子的位置。
字符串中的前导空格和尾随空格不会影响解析，但会导致 Lean 在显示 {tech}[proof states] 中的语法和错误消息时在相应位置插入空格。
标识符指示需要术语的位置，并命名相应的术语，以便可以将其插入符号的扩展中。

虽然自定义运算符只有一个优先级概念，但符号中涉及很多内容。
符号本身具有优先级，每个要解析的术语也具有优先级。
符号的优先级决定了它可以在哪些上下文中进行解析：解析器仅尝试解析优先级至少与当前上下文一样高的产生式。
例如，由于乘法的优先级高于加法，因此解析器将在解析加法参数时尝试解析中缀乘法项，但反之则不然。
要解析的每个术语的优先级决定了其中可能出现哪些其他产生式。

如果没有为符号本身提供优先级，则默认值取决于符号的形式。
如果表示法均以原子开头和结尾（由字符串文字表示），则默认优先级为 `max`.{TODO}[keywordOf]
这既适用于仅由单个原子组成的符号，也适用于具有多个项目的符号，其中第一个和最后一个项目都是原子。
否则，整个表示法的默认优先级是 `lead`。
如果没有为作为术语的符号项目提供优先级，则它们默认为优先级 `min`。

```lean -keep -show

-- Test for default precedences for notations

/-- Parser max -/
notation "takesMax " e:max => e
/-- Parser lead -/
notation "takesLead " e:lead => e
/-- Parser min -/
notation "takesMin " e:min => e

/-- Take the first one -/
notation e1 " <# " e2 => e1

/-- Take the first one in brackets! -/
notation "<<<<<" e1 " <<# " e2 ">>>>>" => e1

elab "#parse_test " "[" e:term "]"  : command => do
  Lean.logInfoAt e (toString e)
  pure ()

-- Here, takesMax vs takesLead distinguishes the notations

/-- info: («term_<#_» (termTakesMax_ "takesMax" (num "1")) "<#" (num "2")) -/
#check_msgs in
#parse_test [ takesMax 1 <# 2 ]

/-- info: (termTakesLead_ "takesLead" («term_<#_» (num "1") "<#" (num "2"))) -/
#check_msgs in
#parse_test [ takesLead 1 <# 2 ]


-- Here, takesMax vs takesLead does not distinguish the notations because both have precedence `max`

/--
info: (termTakesMax_ "takesMax" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesMax <<<<< 1 <<# 2 >>>>> ]

/--
info: (termTakesLead_ "takesLead" («term<<<<<_<<#_>>>>>» "<<<<<" (num "1") "<<#" (num "2") ">>>>>"))
-/
#check_msgs in
#parse_test [ takesLead <<<<< 1 <<# 2 >>>>> ]
```

在所需的双箭头（{keywordOf Lean.Parser.Command.notation}`=>`）之后，提供了扩展符号。
虽然运算符总是通过按顺序将其函数应用于运算符的参数来扩展，但符号可以将其术语项放置在扩展中的任何位置。
这些术语通过名称来引用。
术语项可以在扩展中出现任意多次。
由于符号扩展是在精化或代码生成之前发生的纯粹语法过程，因此扩展中的重复项可能会导致在计算结果项时出现重复计算，甚至在 monad 中工作时出现重复的副作用。

::::keepEnv
:::example "Ignored Terms in Notation Expansion"
此表示法忽略其第一个参数：
```lean
notation (name := ignore) "ignore " _ign:arg e:arg => e
```

被忽略位置的术语被丢弃，并且 Lean 从不尝试详细说明它，因此可以在此处使用否则会导致错误的术语：
```lean (name := ignore)
#eval ignore (2 + "whatever") 5
```
```leanOutput ignore
5
```

但是，被忽略的术语在语法上仍然必须有效：
```syntaxError ignore' (category := command)
#eval ignore (2 +) 5
```
```leanOutput ignore'
<example>:1:17-1:18: unexpected token ')'; expected term
```
:::
::::

::::keepEnv
:::example "Duplicated Terms in Notation Expansion"

{keywordOf dup}`dup!` 符号重复其子项。

```lean
notation (name := dup) "dup!" t:arg => (t, t)
```

由于该术语是重复的，因此可以用不同的类型分别精化：
```lean
def e : Nat × Int := dup! (2 + 2)
```

打印结果定义表明加法运算将执行两次：
```lean (name := dup)
#print e
```
```leanOutput dup
def e : Nat × Int :=
(2 + 2, 2 + 2)
```
:::
::::


当扩展由全局环境中定义的函数的应用组成并且符号中的每个项恰好出现一次时，会生成 {tech}[unexpander]。
当匹配函数应用术语时，新符号将显示在 {tech}[证明状态]、错误消息和 Lean 的其他输出中，否则会显示。
与自定义运算符一样，Lean 不会跟踪原始术语中是否使用了该符号；它在 Lean 输出中的每个机会都使用。

:::example "Notations, Defined Functions, and Unexpanders"
当符号未扩展为已定义函数的应用时，不会生成解扩展器。
在这里，符号扩展为匿名函数：
```lean
notation "[" start " ⇒ " stop "]" => fun x => x > start && x < stop
```

由于展开中没有命名函数，因此无法生成解展开器：
```lean (name := noUnexp)
#check [5 ⇒ 8]
```
```leanOutput noUnexp
fun x => decide (x > 5) && decide (x < 8) : Nat → Bool
```

使用命名函数会产生一个解展开器，该解展开器用于由 {name}`between` 的应用程序组成的术语：
```lean
def between (start stop : Nat) : Nat → Prop :=
  fun x => x > start && x < stop

notation "[" start " ⇒' " stop "]" => between start stop
```
```lean (name := withUnexp)
#check [5 ⇒' 8]
```
```leanOutput withUnexp
[5 ⇒' 8] : Nat → Prop
```
:::

# 运算符和符号
%%%
tag := "operators-and-notations"
%%%

在内部，运算符声明被转换为符号声明。
术语符号项插入到运算符期望参数的位置以及扩展中的相应位置。
对于前缀和后缀运算符，符号的优先级及其术语项的优先级是运算符声明的优先级。
对于非关联中缀运算符，表示法的优先级是声明的优先级，但两个参数都以高一级的优先级进行解析，这会阻止连续使用不带括号的表示法。
关联中缀运算符对符号和一个参数使用该运算符的优先级，而对另一个参数则使用高一级的优先级；这可以防止仅在一个方向上连续应用。
左关联运算符对其右参数使用较高的优先级，而右关联运算符对其左参数使用较高的优先级。
