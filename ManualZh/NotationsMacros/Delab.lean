/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.PrettyPrinter.Delaborator

import Manual.Meta


open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean (Syntax Expr)

#doc (Manual) "扩展Lean的输出" =>
%%%
file := "Extending-Lean___s-Output"
tag := "unexpand-and-delab"
%%%

用新语法扩展Lean，并通过宏和精化器实现新语法，使用户可以更方便地向Lean表达想法。
然而，Lean 是一个_交互式_ 定理证明器：它提供的反馈易于理解也很重要。
语法扩展应该在_output_ 和_input_ 中使用。

:::paragraph
有两种主要机制可用于指示 Lean 在其输出中使用语法扩展：

: 解扩展器

  解扩展器是 {tech (key := "macros")}[宏] 的逆。
  宏通过翻译根据旧语法实现新语法，将新功能扩展为预先存在的功能的编码。
  与宏一样，{deftech}_unexpanders_ 将 {lean}`Syntax` 翻译为 {lean}`Syntax`；与宏不同，它们将编码转换为新的扩展。

: 精化器

  Delaborators 是 {tech (key := "elaborators")}[elaborators] 的逆。
  虽然 {tech (key := "elaborators")}[elaborators] 将 {lean}`Syntax` 翻译为核心类型论的 {lean}`Expr`，但 {deftech}_delaborators_ 将 {lean}`Expr` 翻译为 {lean}`Syntax`。
:::

在显示 {name}`Expr` 之前，首先对其进行细化，然后取消展开。
精化器跟踪其输出源自的原始 {name}`Expr` 中的位置；该位置在生成的语法 {name Lean.SourceInfo}`SourceInfo` 中进行编码。
正如宏展开自动使用与原始语法位置相对应的合成源信息来注释生成的语法，解扩展机制保留生成的语法与基础 {name}`Expr` 的关联。
此关联启用 Lean 的交互功能，当结果语法显示在 {tech (key := "proof states")}[证明状态] 和诊断中时，该功能提供有关结果语法的信息。

# 解扩展器
%%%
file := "Unexpanders"
tag := "Unexpanders"
%%%

正如宏注册在将 {tech (key := "syntax kinds")}[语法种类] 映射到宏实现的表中一样，解扩展器也注册在将常量名称映射到解扩展器实现的表中。
Lean 在向用户显示语法之前，会尝试根据此表重写语法中常量的每个应用。
非应用程序的上下文出现被视为具有零参数的应用程序。

反膨胀是从内到外进行的。
在参数被解展开后，解展开器将传递应用程序的语法，并隐藏隐式参数。
如果选项 {option}`pp.explicit` 是 {lean}`true` 或 {option}`pp.notation` 是 {lean}`false`，则不使用解扩展器。

::::::::leanSection
```lean -show
open Lean.PrettyPrinter (Unexpander UnexpandM)
```

解扩展器的类型为 {lean}`Lean.PrettyPrinter.Unexpander`，它是 `Syntax → Lean.PrettyPrinter.UnexpandM Syntax` 的缩写。
在本节的其余部分中，名称 {lean}`Unexpander` 和 {lean}`UnexpandM` 不合格地使用。
{lean}`UnexpandM` 是一个通过其 {name Lean.MonadQuotation}`MonadQuotation` 和 {lean}`MonadExcept Unit` 实例支持报价和失败的 monad。

解展开器应该返回未展开的语法，或者使用 {lean  (type := "UnexpandM Syntax")}`throw ()` 失败。
如果解展开成功，则生成的语法将再次解展开；如果失败，则尝试下一个解扩展器。
当该语法没有成功的解展开器时，其子节点将被解展开，直到所有解展开的机会都用尽为止。

{docstring Lean.PrettyPrinter.Unexpander}

{docstring Lean.PrettyPrinter.UnexpandM}

通过应用 {attr}`app_unexpander` 属性来注册常量的解扩展器。
{ref "operators"}[自定义运算符] 和 {ref "notations"}[符号] 自动为其引入的语法创建解展开器。

:::syntax attr (title := "Unexpander Registration")
```grammar
app_unexpander $_:ident
```

为常量的应用注册类型为 {name}`Unexpander` 的解扩展器。
:::


:::::example "Custom Unit Type"
::::keepEnv
与 {lean}`Unit` 等效的类型，但具有自己的表示法，可以定义为零字段结构和宏：
```lean
structure Solo where
  mk ::

syntax "‹" "›" : term

macro_rules
  | `(term|‹›) => ``(Solo.mk)
```


虽然新的符号可用于编写定理陈述，但它不会出现在证明状态中。
例如，当证明{lean}`Solo`类型的所有值都等于{lean}`‹›`时，初始证明状态为：
```proofState
∀v, v = ‹› := by
intro v
/--
v : Solo
⊢ v = { }
-/

```
此证明状态显示使用 {tech (key := "structure instance")}[结构实例] 语法的构造函数。
解扩展器可用于覆盖此选择。
由于 {name}`Solo.mk` 不能应用于任何参数，因此解展开器可以忽略语法，该语法始终为 {lean (type := "UnexpandM Syntax")}`` `(Solo.mk) ``。

```lean
@[app_unexpander Solo.mk]
def unexpandSolo : Lean.PrettyPrinter.Unexpander
  | _ => `(‹›)
```

有了这个解展开器，证明的初始状态现在用正确的语法呈现：
```proofState
∀v, v = ‹› := by
intro v
/--
v : Solo
⊢ v = ‹›
-/

```

::::
:::::

:::::example "Unexpansion and Arguments"

{name}`ListCursor` 表示 {lean}`List` 中的位置。
{name}`ListCursor.before` 包含该位置之前的元素的反向列表，{name}`ListCursor.after` 包含该位置之后的元素。

```lean
structure ListCursor (α) where
  before : List α
  after : List α
deriving Repr
```

列表光标可以向左或向右移动：
```lean
def ListCursor.left : ListCursor α → Option (ListCursor α)
  | ⟨[], _⟩ => none
  | ⟨l :: ls, rs⟩ => some ⟨ls, l :: rs⟩

def ListCursor.right : ListCursor α → Option (ListCursor α)
  | ⟨_, []⟩ => none
  | ⟨ls, r :: rs⟩ => some ⟨r :: ls, rs⟩
```

它们也可以一直向左或一直向右移动：
```lean
def ListCursor.rewind : ListCursor α → ListCursor α
  | xs@⟨[], _⟩ => xs
  | ⟨l :: ls, rs⟩ => rewind ⟨ls, l :: rs⟩
termination_by xs => xs.before

def ListCursor.fastForward : ListCursor α → ListCursor α
  | xs@⟨_, []⟩ => xs
  | ⟨ls, r :: rs⟩ => fastForward ⟨r :: ls, rs⟩
termination_by xs => xs.after
```

```lean -show
def ListCursor.ofList (xs : List α) : ListCursor α where
  before := []
  after := xs

def ListCursor.toList : (xs : ListCursor α) → List α
  | ⟨[], rs⟩ => rs
  | ⟨l::ls, rs⟩ => toList ⟨ls, l :: rs⟩
termination_by xs => xs.before
```

但是，需要反转先前元素的列表可能会使列表游标难以理解。
可以为光标指定一个符号，其中标志 (`🚩`) 标记光标在列表中的位置：
```lean
syntax "[" term,* " 🚩 " term,* "]": term
macro_rules
  | `([$ls,* 🚩 $rs,*]) =>
    ``(ListCursor.mk [$[$((ls : Array Lean.Term).reverse)],*] [$rs,*])
```
在宏中，元素序列的类型为 {lean}``Syntax.TSepArray `term ","``。
{lean}`Array Lean.Term` 的类型注释会引发强制转换，以便可以应用 {name}`Array.reverse`，并且类似的强制转换会重新插入分隔逗号。
这些强制转换在 {ref "typed-syntax"}[类型化语法] 部分中进行了描述。

虽然该语法有效，但 Lean 的输出中未使用它：
```lean (name := flagNo)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagNo
{ before := [3, 2, 1], after := [4, 5] } : ListCursor Nat
```

解扩展器可以解决这个问题。
解展开器依赖于已重写两个列表的列表文字的内置解展开器：
```lean
@[app_unexpander ListCursor.mk]
def unexpandListCursor : Lean.PrettyPrinter.Unexpander
  | `($_ [$ls,*] [$rs,*]) =>
    `([$((ls : Array Lean.Term).reverse),* 🚩 $(rs),*])
  | _ => throw ()
```

```lean (name := flagYes)
#check [1, 2, 3 🚩 4, 5]
```
```leanOutput flagYes
[1, 2, 3 🚩 4, 5] : ListCursor Nat
```

```lean (name := flagYes2)
#reduce [1, 2, 3 🚩 4, 5].right
```
```leanOutput flagYes2
some [1, 2, 3, 4 🚩 5]
```

```lean (name := flagYes3)
#reduce [1, 2, 3 🚩 4, 5].left >>= (·.left)
```
```leanOutput flagYes3
some [1 🚩 2, 3, 4, 5]
```

:::::

::::::::


# 精化器
%%%
file := "Delaborators"
tag := "delaborators"
%%%
::::::::leanSection
```lean -show
open Lean.PrettyPrinter.Delaborator (DelabM Delab)
open Lean (Term)
```
解析器是 {lean}`Lean.PrettyPrinter.Delaborator.Delab` 类型的函数，它是 {lean}`Lean.PrettyPrinter.Delaborator.DelabM Term` 的缩写。
与解展开器不同，解展开器不是作为函数实现的。
这是为了更容易正确实现它们：monad {name}`DelabM` 跟踪正在详细说明的表达式中的当前位置，以便详细说明机制可以注释生成的语法。

解析器使用 {attr}`delab` 属性注册。
内部表将 {name}`Expr`（不带命名空间）的构造函数的名称映射到 delaborators。
此外，参考名称 `app.`﻿$`c` 来查找常量 $`c` 的应用程序的解释器，并参考名称 `mdata.`﻿$`k` 来查找 {name}`Expr.mdata` 构造函数的解释器，其元数据。

:::syntax attr (title := "Delaborator Registration")
{attr}`delab` 属性为 {lean}`Expr` 的指示构造函数或元数据键注册一个解析器。
```grammar
delab $_:ident
```

{keyword}`app_delab ` 属性在当前 {tech (key := "resolve")}[范围] 中的 {tech (key := "section scope")}[解析] 后为指示常量的应用程序注册一个解释器。
```grammar
app_delab $_:ident
```
:::

::::leanSection
```lean -show
open Lean.PrettyPrinter.Delaborator.SubExpr
```
:::paragraph
monad {name}`DelabM` 是一个 {tech}[reader monad]，其中包括对 {lean}`Expr` 中当前位置的访问。
递归精化是通过调整读取器单子的跟踪位置来执行的，而不是通过显式地将子表达式传递给另一个函数来执行。
在解析器中处理子表达式的最重要的函数位于命名空间 `Lean.PrettyPrinter.Delaborator.SubExp` 中：
 * {name}`getExpr` 检索当前表达式进行分析。
 * {name}`withAppFn` 将当前位置调整为应用程序中函数的位置。
 * {name}`withAppArg` 将当前位置调整为应用程序中参数的位置
 * {name}`withAppFnArgs` 将当前表达式分解为非应用程序函数及其参数，重点关注每个函数。
 * {name}`withBindingBody` 下降到函数或函数类型的主体。

可以使用更多函数深入 {name}`Expr` 的其余构造函数。
:::
::::


::::::::

::::draft
:::planned 122

 * 精化示例和组合器参考
 * 漂亮的印刷
 * 括号
:::
::::
