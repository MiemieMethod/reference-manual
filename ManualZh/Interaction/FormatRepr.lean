/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Std.Data.HashSet

import Manual.Meta
import Manual.Papers

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.code.warnLineLength 72
set_option verso.docstring.allowMissing true

#doc (Manual) "技术输出" =>
%%%
tag := "format-repr"
%%%

{name}`Repr` 类型类用于提供可解析和评估以获得等效值的数据的标准表示形式。
这不是一个严格的正确性标准：对于某些类型，尤其是那些带有嵌入命题的类型，这是不可能实现的。
但是，{name}`Repr` 实例生成的输出应尽可能接近可解析和评估的输出。

:::paragraph
除了机器可读之外，这种表示形式还应该方便人们理解，特别是行不应该太长，嵌套值应该缩进。
这是通过两步过程实现的：

 1. {name}`Repr` 实例生成 {name}`Std.Format` 类型的中间文档，它紧凑地表示一组在换行符和缩进位置方面有所不同的字符串。
 2. 渲染过程根据所需的最大线长度等标准从集合中选择“最佳”代表。

特别是，{name}`Std.Format` 可以组合构建，因此 {name}`Repr` 实例不需要考虑周围的缩进上下文。
:::


# 格式
%%%
tag := "Format"
%%%


::::leanSection
```lean -show
open Std (Format)
open Std.Format
variable {str : String} {indent : String} {n : Nat}
```
:::paragraph
{name}`Format`{margin}[此处描述的 API 是 Wadler 的 ({citehere wadler2003}[]) 的改编版，它已被修改为在严格的语言中高效，并支持元数据标签等附加功能。] 是一组字符串的紧凑表示。
最重要的 {name Std.Format}`Format` 操作是：

: 弦乐

  可以使用 {name}`text` 构造函数将 {name}`String` 制作为 {name}`Format`。
  此构造函数注册为从 {name}`String` 到 {name}`Format` 的 {ref "coercions"}[强制]，因此通常不需要显式调用它。
  {lean}`text str` 表示仅包含 {lean}`str` 的单例集。
  如果字符串包含换行符 ({lean}`'\n'`)，则它们将无条件作为换行符插入到结果输出中，无论组如何。
  但是，它们会根据当前的缩进级别进行缩进。

: 追加

  可以使用 {inst}`Append Format` 实例中的 `++` 运算符附加两个 {name}`Format`。

: 组和换行符

  构造函数 {name}`line` 表示同时包含 {lean}`"\n" ++ indent` 和 {lean}`" "` 的集​​合，其中 {lean}`indent` 是一个具有足够空格以正确缩进该行的字符串。
  无论如何，它可以被认为是一个换行符，如果当前行有足够的空间，它将被“展平”到一个空格。
  换行符出现在_groups_中：{name}`group` 运算符的最近封闭应用程序确定换行符属于哪个组。
  默认情况下，组中的所有 {name}`line` 代表 {lean}`"\n"`，或者全部代表 {lean}`" "`；组也可以配置为填充行，在这种情况下，组中最小数量的 {name}`line` 代表 {lean}`"\n"`。
  不属于组的 {name}`line` 的使用始终代表 {lean}`"\n"`。

: 缩进

  插入换行符时，输出也会缩进。
  {lean}`nest n` 将文档的缩进增加 {lean}`n` 空格。
  这不足以表示所有 Lean 语法，有时需要列精确对齐。
  {lean}`align` 是一个文档，可确保输出字符串处于当前缩进级别，如果可能的话仅插入空格，或者如果需要则插入换行符后跟空格。

: 标记

  Lean 的交互功能需要能够将输出与其所表示的基础值关联起来。
  例如，这允许 Lean 开发环境在将鼠标悬停在术语证明状态或错误消息上时呈现详细的术语。
  可以使用 {lean}`tag n` 使用 {name}`Nat` 值 {lean}`n` 对文档进行“标记”；这些 {name}`Nat` 应映射到侧表中的基础值。
:::
::::

:::example "Widths and Newlines"
```imports -show
import Std
```
```lean
open Std Format
```

帮助器 {name}`parenSeq` 创建一个带括号的序列，具有分组和缩进，以使其响应不同的输出宽度。
```lean
def parenSeq (xs : List Format) : Format :=
  group <|
    nest 2 (text "(" ++ line ++ joinSep xs line) ++
    line ++
    ")"
```

该文档表示带括号的数字序列：
```lean
def lst : Format := parenSeq nums
where nums := [1, 2, 3, 4, 5].map (text s!"{·}")
```

```lean -show -keep
-- check statement in next paragraph
/-- info: 120 -/
#check_msgs in
#eval defWidth
```

使用 120 个字符的默认行宽进行渲染会将整个序列放在一行上：
```lean (name := lstp)
#eval IO.println lst.pretty
```
```leanOutput lstp
( 1 2 3 4 5 )
```

由于所有 {name}`line` 都属于同一个 {name}`group`，因此它们要么全部呈现为空格，要么全部呈现为换行符。
如果只有 9 个字符可用，则 {name}`lst` 中的所有 {name}`line` 都将成为换行符：
```lean (name := lstp9)
#eval IO.println (lst.pretty (width := 9))
```
```leanOutput lstp9
(
  1
  2
  3
  4
  5
)
```


本文档包含 {name}`lst` 的三个副本，按进一步的括号顺序排列：
```lean
def lsts := parenSeq [lst, lst, lst]
```

在默认宽度下，它保持在一行上：
```lean (name := lstsp)
#eval IO.println lsts.pretty
```
```leanOutput lstsp
( ( 1 2 3 4 5 ) ( 1 2 3 4 5 ) ( 1 2 3 4 5 ) )
```

如果只有 20 个可用字符，则每次出现 {name}`lst` 时都会独占一行。
这是因为将外部 {name}`group` 转换为换行符足以将字符串保持在 20 列之内：
```lean (name := lstsp20)
#eval IO.println (lsts.pretty (width := 20))
```
```leanOutput lstsp20
(
  ( 1 2 3 4 5 )
  ( 1 2 3 4 5 )
  ( 1 2 3 4 5 )
)
```

如果只有 10 个字符，则每个数字必须独占一行：
```lean (name := lstsp10)
#eval IO.println (lsts.pretty (width := 10))
```
```leanOutput lstsp10
(
  (
    1
    2
    3
    4
    5
  )
  (
    1
    2
    3
    4
    5
  )
  (
    1
    2
    3
    4
    5
  )
)
```
:::


:::example "Grouping and Filling"
```lean
open Std Format
```

帮助器 {name}`parenSeq` 创建一个带括号的序列，每个元素放置在一个新行并缩进：
```lean
def parenSeq (xs : List Format) : Format :=
  nest 2 (text "(" ++ line ++ joinSep xs line) ++
  line ++
  ")"
```

{name}`nums` 包含数字 1 到 20，作为格式列表：
```lean
def nums : List Format :=
  Nat.fold 20 (init := []) fun i _ ys =>
    text s!"{20 - i}" :: ys
```

```lean (name := nums)
#eval nums
```

由于 {name}`parenSeq` 不引入任何组，因此生成的文档将呈现在一行上：
```lean
#eval IO.println (pretty (parenSeq nums))
```

这可以通过对它们进行分组来解决。
{name}`grouped` 使用 {name}`group` 执行此操作，而 {name}`filled` 使用 {name}`fill` 执行此操作。
```lean
def grouped := group (parenSeq nums)
def filled := fill (parenSeq nums)
```

两个分组运算符都会导致使用 {name}`line` 呈现为空格。
如果有足够的空间，两者都会呈现在一行上：
```lean (name := groupedp)
#eval IO.println (pretty grouped)
```
```leanOutput groupedp
( 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )
```

```lean (name := filledp)
#eval IO.println (pretty filled)
```
```leanOutput filledp
( 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )
```

然而，当单行上没有足够的空间时，差异就会变得明显。
除非 {name}`group` 中的所有换行符都可以是空格，否则都不能：
```lean (name := groupedp30)
#eval IO.println (pretty (width := 30) grouped)
```
```leanOutput groupedp30
(
  1
  2
  3
  4
  5
  6
  7
  8
  9
  10
  11
  12
  13
  14
  15
  16
  17
  18
  19
  20
)
```

另一方面，使用 {name}`fill` 仅根据需要插入换行符以避免出现两宽：
```lean (name := filledp30)
#eval IO.println (pretty (width := 30) filled)
```
```leanOutput filledp30
( 1 2 3 4 5 6 7 8 9 10 11 12
  13 14 15 16 17 18 19 20 )
```

使用较长的序列可以清楚地看到 {name}`fill` 的行为：
```lean (name := filledbigp30)
#eval IO.println <|
  pretty (width := 30) (fill (parenSeq (nums ++ nums ++ nums ++ nums)))
```
```leanOutput filledbigp30
( 1 2 3 4 5 6 7 8 9 10 11 12
  13 14 15 16 17 18 19 20 1 2
  3 4 5 6 7 8 9 10 11 12 13 14
  15 16 17 18 19 20 1 2 3 4 5
  6 7 8 9 10 11 12 13 14 15 16
  17 18 19 20 1 2 3 4 5 6 7 8
  9 10 11 12 13 14 15 16 17 18
  19 20 )
```
:::

::::example "Newline Characters in Strings"
在字符串中包含换行符会导致渲染过程无条件插入换行符。
然而，这些换行符确实尊重当前的缩进级别。

文档 {name}`str` 由带有两个换行符的嵌入字符串组成：
```lean
open Std Format

def str : Format := text "abc\nxyz\n123"
```

:::paragraph
打印带分组和不带分组的字符串都会导致使用换行符：
```lean (name := str1)
#eval IO.println str.pretty
```
```leanOutput str1
abc
xyz
123
```
```lean (name := str2)
#eval IO.println (group str).pretty
```
```leanOutput str2
abc
xyz
123
```
:::

:::paragraph
由于字符串不以换行符结尾，因此第一个字符串的最后一行与第二个字符串的第一行位于同一行：
```lean (name := str3)
#eval IO.println (str ++ str).pretty
```
```leanOutput str3
abc
xyz
123abc
xyz
123
```
:::

:::paragraph
但是，增加缩进级别会导致字符串的所有三行都从同一列开始：
```lean (name := str4)
#eval IO.println (text "It is:" ++ indentD str).pretty
```
```leanOutput str4
It is:
  abc
  xyz
  123
```

```lean (name := str5)
#eval IO.println (nest 8 <| text "It is:" ++ align true ++ str).pretty
```
```leanOutput str5
It is:  abc
        xyz
        123
```
:::

::::

## 文件
%%%
tag := "format-api"
%%%

{docstring Std.Format}

{docstring Std.Format.FlattenBehavior}

{docstring Std.Format.fill}

## 空文档
%%%
tag := "format-empty"
%%%


:::paragraph
空字符串在 {name}`Std.Format` 中没有唯一的代表。
以下所有内容都代表空字符串：

* {lean  (type := "Std.Format")}`.nil`
* {lean  (type := "Std.Format")}`.text ""`
* {lean  (type := "Std.Format")}`.text "" ++ .nil`
* {lean  (type := "Std.Format")}`.nil ++ .text ""`

使用 {name}`Std.Format.isEmpty` 检查文档是否包含零个字符，使用 {name}`Std.Format.isNil` 专门检查它是否是构造函数 {lean}`Std.Format.nil`。
:::

{docstring Std.Format.isEmpty}

{docstring Std.Format.isNil}



## 序列
%%%
tag := "format-join"
%%%

当存在某种重复内容（例如列表的元素）时，本节中的运算符非常有用。
这通常是通过使用 {ref "format-brackets"}[包围运算符] 在其分隔符参数中包含 {name Std.Format.line}`line` 来完成的

{docstring Std.Format.join}

{docstring Std.Format.joinSep}

{docstring Std.Format.prefixJoin}

{docstring Std.Format.joinSuffix}

## 缩进
%%%
tag := "format-indent"
%%%

这些运算符可以更轻松地在 {name}`Std.Format.nest` 之上实现一致的缩进样式。

{docstring Std.Format.nestD}

{docstring Std.Format.defIndent}

{docstring Std.Format.indentD}

## 方括号和圆括号
%%%
tag := "format-brackets"
%%%

这些运算符可以更轻松地实现一致的括号样式。

{docstring Std.Format.bracket}

{docstring Std.Format.sbracket}

{docstring Std.Format.paren}

{docstring Std.Format.bracketFill}

## 渲染
%%%
tag := "format-render"
%%%

{inst}`ToString Std.Format` 实例使用其默认参数调用 {name}`Std.Format.pretty`。

有两种方式呈现文档：
* 使用 {name Std.Format.pretty}`pretty` 构造 {name}`String`。
  必须先构建整个字符串，然后才能将任何字符串发送给用户。
* 使用 {name Std.Format.prettyM}`prettyM` 增量发射 {name}`String`，并使用某些 {name}`Monad` 中的效果。
  一旦每行被渲染，它就会被发射。
  这适合流式输出。

{docstring Std.Format.pretty}

{docstring Std.Format.defWidth}

{docstring Std.Format.prettyM}

{docstring Std.Format.MonadPrettyFormat}

## `ToFormat` 级

{name}`Std.ToFormat` 类用于提供格式化值的标准方法，但不期望此格式化是有效的 Lean 语法。
这些实例用于错误消息和某些 {ref "format-join"}[序列连接运算符]。

{docstring Std.ToFormat}

# `Repr`
%%%
tag := "repr"
%%%

{name}`Repr` 实例描述如何将值表示为 {name}`Std.Format`。
因为它们应该发出有效的 Lean 语法，所以这些实例需要考虑 {tech}[优先级]。
插入最大数量的括号是可行的，但它使人们更难以阅读结果输出。

{docstring Repr}

{docstring repr}

{docstring reprStr}

:::example "Maximal Parentheses"
{name}`NatOrInt` 类型可以包含 {name}`Nat` 或 {name}`Int`：
```lean
inductive NatOrInt where
  | nat : Nat → NatOrInt
  | int : Int → NatOrInt
```
此 {inst}`Repr NatOrInt` 实例通过插入许多括号来确保输出是有效的 Lean 语法：
```lean
instance : Repr NatOrInt where
  reprPrec x _ :=
    .nestD <| .group <|
      match x with
      | .nat n =>
          .text "(" ++ "NatOrInt.nat" ++ .line ++ "(" ++ repr n ++ "))"
      | .int i =>
          .text "(" ++ "NatOrInt.int" ++ .line ++ "(" ++ repr i ++ "))"
```
无论它包含 {name}`Nat`、非负 {name}`Int` 还是负 {name}`Int`，都可以解析结果：
```lean (name := parens)
open NatOrInt in
#eval do
  IO.println <| repr <| nat 3
  IO.println <| repr <| int 5
  IO.println <| repr <| int (-5)
```
```leanOutput parens
(NatOrInt.nat (3))
(NatOrInt.int (5))
(NatOrInt.int (-5))
```
但是，{lean}`(NatOrInt.nat (3))` 并不是特别惯用的 Lean，并且多余的括号可能会导致读取大型表达式变得困难。
:::


方法 {name}`Repr.reprPrec` 具有以下签名：
```signature
Repr.reprPrec.{u} {α : Type u} [Repr α] : α → Nat → Std.Format
```
第一个显式参数是要表示的值，而第二个参数是它出现的上下文的 {tech}[precedence]。
此优先级可用于决定是否插入括号：如果实例生成的语法的优先级大于其上下文的优先级，则需要括号。

## 如何编写 `Repr` 实例
%%%
tag := "repr-instance-howto"
%%%

Lean 可以使用 {ref "deriving-instances"}[实例派生]自动为大多数类型生成适当的 {name}`Repr` 实例。
然而，在某些情况下，有必要手动编写一个实例：

* 有些库提供函数作为类型的主要实例，而不是其构造函数；在这些情况下，{name}`Repr` 实例应表示对这些函数的调用。
  例如，{name}`Std.HashSet.ofList` 用于 {inst}`Repr (HashSet α)` 实例。

* 一些归纳类型包括格式良好的证明。
  由于程序无法检查校样，因此无法直接渲染它们。
  这是类型除了构造函数之外还有接口的常见原因。

* 具有特殊语法的类型（例如 {name}`List`）应在其 {name}`Repr` 实例中使用此语法。

* 结构的派生 {name}`Repr` 实例使用 {tech}[结构实例] 表示法。
  手写实例可以显式使用构造函数的名称或使用 {tech}[匿名构造函数语法]。

```lean -show -keep
/-- info: Std.HashSet.ofList [0, 3, 5] -/
#check_msgs in
#eval IO.println <| repr (({} : Std.HashSet Nat).insert 3 |>.insert 5 |>.insert 0)
```
```lean -show -keep
structure S where
  x : Nat
  y : Nat
deriving Repr
/-- info: { x := 2, y := 3 } -/
#check_msgs in
#eval IO.println <| repr <| S.mk 2 3
```

编写自定义 {name}`Repr` 实例时，请遵循以下约定：

: 优先级

  检查优先级，根据需要添加括号，并将正确的优先级传递给嵌入数据的 {name}`reprPrec` 实例。
  如果需要，每个实例都有责任将自己括在括号中；实例通常不应将对 {name}`reprPrec` 的递归调用括起来。

  函数应用程序具有最高优先级，{lean}`max_prec`。
  帮助程序 {name}`Repr.addAppParen` 和 {name}`reprArg` 分别在需要时在应用程序周围插入括号，并将适当的优先级传递给函数参数。

: 完全限定名称

  {name}`Repr` 实例确实有权访问给定位置的开放命名空间集。
  环境中常量的所有名称都应该完全限定以消除歧义。

: 默认嵌套

  嵌套数据应使用 {name Std.Format.nestD}`nestD` 缩进，以确保跨实例的缩进一致。

: 分组和换行

  每个包含换行符的 {name}`Repr` 实例的输出应包含在 {name Std.Format.group}`group` 中。
  此外，如果生成的代码包含嵌套的概念表达式，则应在每个嵌套级别周围插入 {name Std.Format.group}`group`。
  通常应在以下位置插入换行符：
    * 在构造函数及其每个参数之间
    * `:=`之后
    * `,`之后
    * 在 {tech}[结构实例] 表示法及其内容的左大括号和右大括号之间
    * 在中缀运算符之后，但不是之前

: 圆括号和方括号

  应使用 {name}`Std.Format.bracket` 或其特化 {name}`Std.Format.paren`（表示括号）和 {name}`Std.Format.sbracket`（表示方括号）插入圆括号和方括号。
  这些运算符以与 Lean 相同的方式对齐括号或方括号表达式的内容。
  尾随圆括号和方括号不应单独占一行，而应与其内容保持一致。

{docstring Repr.addAppParen}

{docstring reprArg}


:::example "Inductive Types with Constructors"
归纳类型{name}`N.NatOrInt` 可以包含 {name}`Nat` 或 {name}`Int`：
```lean
namespace N

inductive NatOrInt where
  | nat : Nat → NatOrInt
  | int : Int → NatOrInt

```
{inst}`Repr NatOrInt` 实例遵循以下约定：
 * 右侧是函数应用程序，因此它使用 {name}`Repr.addAppParen` 在必要时添加括号。
 * 括号包裹着整个主体，没有额外的 {name Std.Format.line}`line`。
 * 整个函数应用是分组的，并且嵌套了默认的数量。
 * 通过使用 {name Std.Format.line}`line` 将函数与其参数分开；该换行符通常是一个空格，因为 {inst}`Repr Nat` 和 {inst}`Repr Int` 实例不太可能产生长输出。
 * 对 {name}`reprPrec` 的递归调用会传递 {lean}`max_prec`，因为它们位于函数参数位置，并且函数应用程序具有最高优先级。

```lean
instance : Repr NatOrInt where
  reprPrec
    | .nat n =>
      Repr.addAppParen <|
        .group <| .nestD <|
          "N.NatOrInt.nat" ++ .line ++ reprPrec n max_prec
    | .int i =>
      Repr.addAppParen <|
        .group <| .nestD <|
          "N.NatOrInt.int" ++ .line ++ reprPrec i max_prec
```
```lean (name := nat5)
#eval IO.println (repr (NatOrInt.nat 5))
```
```leanOutput nat5
N.NatOrInt.nat 5
```
```lean (name := int5)
#eval IO.println (repr (NatOrInt.int 5))
```
```leanOutput int5
N.NatOrInt.int 5
```
```lean (name := intm5)
#eval IO.println (repr (NatOrInt.int (-5)))
```
```leanOutput intm5
N.NatOrInt.int (-5)
```
```lean (name := someintm5)
#eval IO.println (repr (some (NatOrInt.int (-5))))
```
```leanOutput someintm5
some (N.NatOrInt.int (-5))
```


```lean (name := lstnat)
#eval IO.println (repr <| (List.range 10).map (NatOrInt.nat))
```
```leanOutput lstnat
[N.NatOrInt.nat 0,
 N.NatOrInt.nat 1,
 N.NatOrInt.nat 2,
 N.NatOrInt.nat 3,
 N.NatOrInt.nat 4,
 N.NatOrInt.nat 5,
 N.NatOrInt.nat 6,
 N.NatOrInt.nat 7,
 N.NatOrInt.nat 8,
 N.NatOrInt.nat 9]
```

```lean (name := lstnat3)
#eval IO.println <|
  Std.Format.pretty (width := 3) <|
    repr <| (List.range 10).map NatOrInt.nat
```
```leanOutput lstnat3
[N.NatOrInt.nat
   0,
 N.NatOrInt.nat
   1,
 N.NatOrInt.nat
   2,
 N.NatOrInt.nat
   3,
 N.NatOrInt.nat
   4,
 N.NatOrInt.nat
   5,
 N.NatOrInt.nat
   6,
 N.NatOrInt.nat
   7,
 N.NatOrInt.nat
   8,
 N.NatOrInt.nat
   9]
```

:::

:::example "Infix Syntax"
此示例演示了如何使用优先级对左关联漂亮打印机进行编码。
{lean}`AddExpr` 类型表示具有常量和加法的表达式：
```lean
inductive AddExpr where
  | nat : Nat → AddExpr
  | add : AddExpr → AddExpr → AddExpr
```

{name}`OfNat` 和 {name}`Add` 实例为 {name}`AddExpr` 提供更方便的语法：
```lean
instance : OfNat AddExpr n where
  ofNat := .nat n

instance : Add AddExpr where
  add := .add
```

{inst}`Repr AddExpr` 实例应仅插入必要的括号。
Lean 的加法运算符是左关联的，优先级为 65，因此对左侧的递归调用使用优先级 64，并且如果当前上下文的优先级大于或等于 65，则运算符本身会被括号括起来：
```lean
protected def AddExpr.reprPrec : AddExpr → Nat → Std.Format
  | .nat n, p  =>
    Repr.reprPrec n p
  | .add e1 e2, p =>
    let out : Std.Format :=
      .nestD <| .group <|
        AddExpr.reprPrec e1 64 ++ " " ++ "+" ++ .line ++
        AddExpr.reprPrec e2 65
    if p ≥ 65 then out.paren else out

instance : Repr AddExpr := ⟨AddExpr.reprPrec⟩
```

```lean -show -keep
-- Test that the guidelines provided for infix operators match Lean's own pretty printer
/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 +
        8 +
      9 +
    10 +
  11 : Nat
-/
#check_msgs in
#check 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11

/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 +
        8 +
      9 +
    10 +
  11
-/
#check_msgs in
#eval (1 : AddExpr) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11

```

无论输入的括号如何，此实例仅插入必要的括号：
```lean (name := prec1)
#eval IO.println (repr (((2 + 3) + 4) : AddExpr))
```
```leanOutput prec1
2 + 3 + 4
```
```lean (name:=prec2)
#eval IO.println (repr ((2 + 3 + 4) : AddExpr))
```
```leanOutput prec2
2 + 3 + 4
```
```lean (name:=prec3)
#eval IO.println (repr ((2 + (3 + 4)) : AddExpr))
```
```leanOutput prec3
2 + (3 + 4)
```
```lean (name:=prec4)
#eval IO.println (repr ([2 + (3 + 4), (2 + 3) + 4] : List AddExpr))
```
```leanOutput prec4
[2 + (3 + 4), 2 + 3 + 4]
```
在实现中使用 {name Std.Format.group}`group`、{name Std.Format.nestD}`nestD` 和 {name Std.Format.line}`line` 会导致在狭窄的上下文中出现预期的换行符和缩进：
```lean (name:=prec5)
#eval ([2 + (3 + 4), (2 + 3) + 4] : List AddExpr)
  |> repr
  |>.pretty (width := 0)
  |> IO.println
```
```leanOutput prec5
[2 +
   (3 +
      4),
 2 +
     3 +
   4]
```
:::

## 原子类型
%%%
tag := "ReprAtom"
%%%

当列表的元素足够小时，用每行一个元素呈现列表可能既难以阅读又浪费空间。
为了提高可读性，{name}`List` 有两个 {name}`Repr` 实例：一个使用 {name}`Std.Format.bracket` 作为其内容，另一个使用 {name}`Std.Format.bracketFill`。
后者是在前者之后定义的，因此在可能的情况下选择后者；但是，它需要空类型类 {name}`ReprAtom` 的实例。

如果某个类型的 {name}`Repr` 实例从不生成空格或换行符，则它应该有一个 {name}`ReprAtom` 实例。
Lean 具有 {name}`String`、{name}`UInt8`、{name}`Nat`、{name}`Char` 和 {name}`Bool` 等类型的 {name}`ReprAtom` 实例。

```lean -show
open Lean Elab Command in
#eval show CommandElabM Unit from
  for x in [``String, ``UInt8, ``Nat, ``Char, ``Bool] do
    runTermElabM fun _ => do
      discard <| Meta.synthInstance (.app (.const ``ReprAtom [0]) (.const x []))
      Term.synthesizeSyntheticMVarsNoPostponing
```

{docstring ReprAtom}

::::example "Atomic Types and `Repr`"

归纳类型{name}`ABC` 的所有构造函数都不带参数：

```lean
inductive ABC where
  | a
  | b
  | c
deriving Repr
```

派生的 {inst}`Repr ABC` 实例用于显示列表：
```lean (name := abc1)
def abc : List ABC := [.a, .b, .c]

def abcs : List ABC := abc ++ abc ++ abc

#eval IO.println ((repr abcs).pretty (width := 14))
```

由于宽度较窄，因此插入换行符：
```leanOutput abc1
[ABC.a,
 ABC.b,
 ABC.c,
 ABC.a,
 ABC.b,
 ABC.c,
 ABC.a,
 ABC.b,
 ABC.c]
```

:::paragraph
但是，将列表转换为 {lean}`List Nat` 会导致格式不同的结果。
```lean (name := abc2)
def ABC.toNat : ABC → Nat
  | .a => 0
  | .b => 1
  | .c => 2

#eval IO.print ((repr (abcs.map ABC.toNat)).pretty (width := 14))
```
换行次数要少得多：
```leanOutput abc2
[0, 1, 2, 0,
 1, 2, 0, 1,
 2]
```
:::

这是因为 {inst}`ReprAtom Nat` 实例的存在。
为 {name}`ABC` 添加一个会导致类似的行为：
```lean (name := abc3)
instance : ReprAtom ABC := ⟨⟩

#eval IO.println ((repr abcs).pretty (width := 14))
```
```leanOutput abc3
[ABC.a, ABC.b,
 ABC.c, ABC.a,
 ABC.b, ABC.c,
 ABC.a, ABC.b,
 ABC.c]
```
::::
