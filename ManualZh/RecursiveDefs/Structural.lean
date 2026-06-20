/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Joachim Breitner
-/

import VersoManual
import ManualZh.RecursiveDefs.Structural.RecursorExample
import ManualZh.RecursiveDefs.Structural.CourseOfValuesExample

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option guard_msgs.diff true

#doc (Manual) "结构递归" =>
%%%
file := "Structural-Recursion"
tag := "structural-recursion"
%%%

结构递归函数是指每次递归调用的结构项都小于参数的项。
相同的参数必须在所有递归调用中减少；该参数称为 {deftech (key := "decreasing parameter")}_递减参数_。
结构递归比递归器提供的原始递归更强，因为递归调用可以使用参数的更深层嵌套的子项，而不仅仅是直接子项。
然而，用于实现结构递归的结构是使用递归器实现的；这些辅助结构在 {ref "recursor-elaboration-helpers"}[关于归纳类型的部分]中进行了描述。

管理结构递归的规则本质上是_语法_的。
有许多递归定义表现出结构递归计算行为，但不被这些规则所接受；这是全自动分析的基本结果。
{tech (key := "Well-founded recursion")}[良基递归] 提供了一种语义方法来演示终止，该方法可用于递归函数不是结构递归的情况，但也可以在根据结构递归计算的函数不满足语法要求时使用。

```lean -show
section
variable (n n' : Nat)
```
:::example "Structural Recursion vs Subtraction"
函数 {lean}`countdown` 在结构上是递归的。
The parameter {lean}`n` was matched against the pattern {lean}`n' + 1`, which means that {lean}`n'` is a direct subterm of {lean}`n` in the second branch of the pattern match:
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown n'
```

将模式匹配替换为等效的布尔测试和减法会导致错误：
```lean +error (name := countdown') -keep
def countdown' (n : Nat) : List Nat :=
  if n == 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```
```leanOutput countdown'
fail to show termination for
  countdown'
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' n'


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n : Nat
h✝ : ¬(n == 0) = true
n' : Nat := n - 1
⊢ n - 1 < n
```
这是因为参数 {lean}`n` 上没有模式匹配。
虽然此函数确实终止，但它这样做的论点是基于 if、相等测试和减法的属性，而不是 {lean}`Nat` 是 {tech (key := "inductive type")}[归纳类型] 的通用特征。
这些参数使用 {tech (key := "well-founded recursion")}[良基递归] 表示，对函数定义的轻微更改允许 Lean 自动支持良基递归来构造替代终止证明。
此版本基于 {lean}`Nat` 的 {tech (key := "propositional equality")}[命题等价] 的可判定性进行分支，而不是布尔相等测试的结果：

```lean
def countdown' (n : Nat) : List Nat :=
  if n = 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
```

在这里，Lean 的自动化自动根据有关 命题等价 和减法的事实构建终止证明。
它在幕后使用良基递归而不是结构递归。
:::
```lean -show
end
```

结构递归可以显式或自动使用。
对于显式结构递归，函数定义声明哪个参数是 {tech (key := "decreasing parameter")}[递减参数]。
如果未显式声明终止策略，Lean 将搜索递减参数以及与 {tech (key := "well-founded recursion")}[良基递归] 一起使用的递减度量。
显式注释结构递归有以下好处：
 * 它可以加速精化，因为没有搜索发生。
 * 它为读者记录了终止论证。
 * 在明确需要结构递归的情况下，它可以防止意外使用良基递归。

# 显式结构递归
%%%
file := "Explicit-Structural-Recursion"
tag := "zh-recursivedefs-structural-h001"
%%%

要显式使用结构递归，可以使用指定 {tech (key := "decreasing parameter")}[递减参数] 的 {keywordOf Lean.Parser.Command.declaration}`termination_by structural` 子句来注释函数或定理定义。
递减的参数可以是对签名中命名的参数的引用。
当签名指定函数类型时，递减的参数还可以是签名中未命名的参数；在这种情况下，可以通过将其余参数的名称写在箭头之前来引入它们（{keywordOf Lean.Parser.Command.declaration}`=>`）。

:::example "Specifying Decreasing Parameters"

当递减参数是函数的命名参数时，可以通过引用其名称来指定。

```lean -keep
def half (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n
```

当签名中未命名递减参数时，可以在 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句中本地引入名称。

```lean -keep
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by structural n => n
```
:::

:::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Structural Recursion")

`termination_by structural` 子句引入了递减参数。

```grammar
termination_by structural $[$_:ident* =>]? $term
```

可选 `=>` 之前的标识符可以将函数参数带入非
已经绑定在声明头中，并且强制术语必须指示函数的参数之一，无论是在头中引入还是在子句中本地引入。
:::

递减参数必须满足以下条件：

* 其类型必须是 {tech (key := "inductive type")}[归纳类型]。

* 如果其类型是 {tech}[indexed family]，则所有索引都必须是函数的参数。

* 如果递减参数的归纳或索引族具有数据类型参数，则这些数据类型参数本身可能仅依赖于属于 {tech (key := "fixed prefix")}[固定前缀] 的函数参数。

{deftech (key := "fixed parameter")}_fixedparameter_ 是在所有递归调用中未经修改地传递的函数参数，并且不是递归参数类型的索引。
{deftech}_fixed prefix_ 是函数参数的最长前缀，其中所有参数都是固定的。

:::example "Ineligible decreasing parameters"

递减参数的类型必须是归纳类型。
在{lean}`notInductive`中，指定了一个函数作为递减参数：

```lean +error (name := badnoindct)
def notInductive (x : Nat → Nat) : Nat :=
  notInductive (fun n => x (n+1))
termination_by structural x
```
```leanOutput badnoindct
cannot use specified measure for structural recursion:
  its type is not an inductive
```

如果递减参数是索引族，则所有索引都必须是变量。
在 {lean}`constantIndex` 中，索引系列 {lean}`Fin'` 改为应用于常量值：

```lean +error (name := badidx)
inductive Fin' : Nat → Type where
  | zero : Fin' (n+1)
  | succ : Fin' n → Fin' (n+1)

def constantIndex (x : Fin' 100) : Nat := constantIndex .zero
termination_by structural x
```
```leanOutput badidx
cannot use specified measure for structural recursion:
  its type Fin' is an inductive family and indices are not variables
    Fin' 100
```

递减参数类型的参数不得依赖于变化参数或索引之后的函数参数。
在{lean}`afterVarying`中，{tech (key := "fixed prefix")}[固定前缀]为空，因为第一个参数`n`变化，所以`p`不是固定前缀的一部分：

```lean +error (name := badparam)
inductive WithParam' (p : Nat) : Nat → Type where
  | zero : WithParam' p (n+1)
  | succ : WithParam' p n → WithParam' p (n+1)

def afterVarying (n : Nat) (p : Nat) (x : WithParam' p n) : Nat :=
  afterVarying (n+1) p .zero
termination_by structural x
```
```leanOutput badparam
failed to infer structural recursion:
Cannot use parameter x:
  failed to eliminate recursive application
    afterVarying (n + 1) p WithParam'.zero
```
:::

此外，函数的每次递归调用都必须在递减的 {deftech (key := "strict sub-term")}_strict 子项_上
参数。

 * 递减参数本身是一个子项，但不是严格的子项。
 * 如果子项是 {keywordOf Lean.Parser.Term.match}`match` 表达式或其他模式匹配语法的 {tech (key := "match discriminant")}[判别式]，则与判别式匹配的模式是每个 {tech (key := "match alternative")}[匹配替代项] 的 {tech (key := "right-hand side")}[右侧] 中的子项。
   特别是，{ref "match-generalization"}[匹配泛化]的规则用于将判别式连接到右侧模式项的出现；因此，它尊重 {tech (key := "definitional equality")}[定义等价]。
   当且仅当判别式是严格子项时，该模式才是严格子项。
 * 如果子项是应用于参数的构造函数，则其递归参数是严格子项。

```lean -show
section
variable (n : Nat)
```
::::example "Nested Patterns and Sub-Terms"

在以下示例中，递减参数 {lean}`n` 与嵌套模式 {lean  (type := "Nat")}`.succ (.succ n)` 进行匹配。因此，{lean  (type := "Nat")}`.succ (.succ n)` 是 {lean  (type := "Nat")}`n` 的（非严格）子术语，因此 {lean  (type := "Nat")}`n` 和 {lean  (type := "Nat")}`.succ n` 都是严格子术语，并且定义被接受。

```lean
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) =>  fib n + fib (.succ n)
termination_by structural n => n
```

为清楚起见，本示例使用 {lean  (type := "Nat")}`.succ n` 和 {lean  (type := "Nat")}`.succ (.succ n)`，而不是等效的 {lean}`Nat` 特定的 {lean}`n+1` 和 {lean}`n+2`。

:::TODO
链接到记录此特殊语法的位置。
:::

::::
```lean -show
end
```

```lean -show
section
variable {α : Type u} (n n' : Nat) (xs : List α)
```
:::example "Matching on Complex Expressions Can Prevent Elaboration"

在以下示例中，递减参数 {lean}`n` 并不直接是 {keywordOf Lean.Parser.Term.match}`match` 表达式的 {tech (key := "match discriminant")}[判别式]。
因此，{lean}`n'` 不被视为 {lean}`n` 的子术语。

```lean +error -keep (name := badtarget)
def half (n : Nat) : Nat :=
  match Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by structural n
```
```leanOutput badtarget
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    half n'
```

使用 {tech (key := "well-founded recursion")}[良基递归]，并将判别式显式连接到匹配模式，可以接受此定义。

```lean
def half (n : Nat) : Nat :=
  match h : Option.some n with
  | .some (n' + 2) => half n' + 1
  | _ => 0
termination_by n
decreasing_by simp_all; omega
```

同样，以下示例失败：尽管 {lean}`xs.tail` 会简化为 {lean}`xs` 的严格子项，但根据上述规则，这对 Lean 不可见。
特别是，{lean}`xs.tail` 不 {tech (key := "definitional equality")}[定义等于] {lean}`xs` 的严格子项。

```lean +error -keep
def listLen : List α → Nat
  | [] => 0
  | xs => listLen xs.tail + 1
termination_by structural xs => xs
```

:::
```lean -show
end
```


:::example "Simultaneous Matching vs Matching Pairs for Structural Recursion"

用于证明终止的策略的一个重要结果是*两个 {tech (key := "match discriminant")}[判别式]的同时匹配并不等于匹配一对*。
同时匹配保持判别式和模式之间的联系，允许模式匹配细化本地上下文中的假设类型以及 {keywordOf Lean.Parser.Term.match}`match` 的预期类型。
本质上，{keywordOf Lean.Parser.Term.match}`match` 的精化规则会特殊对待判别式，并且以保留程序运行时含义的方式更改判别式不一定会保留编译时含义。

此函数查找两个自然数中的最小值，由结构递归在其第一个参数上定义：
```lean -keep
def min' (n k : Nat) : Nat :=
  match n, k with
  | 0, _ => 0
  | _, 0 => 0
  | n' + 1, k' + 1 => min' n' k' + 1
termination_by structural n
```

将两个参数上的同时模式匹配替换为一对上的匹配会导致终止分析失败：
```lean +error (name := noMin)
def min' (n k : Nat) : Nat :=
  match (n, k) with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' n' k' + 1
termination_by structural n
```
```leanOutput noMin
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    min' n' k'
```

这是因为当将递归调用与严格较小的参数值匹配时，分析仅考虑参数上的直接模式匹配。
将判别式包装成一对会破坏连接。
:::

:::example "Structural Recursion Under Pairs"

无法通过结构递归详细说明此函数，该函数用于查找一对的两个分量中的最小值。
```lean +error (name := minpair) -keep
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by structural nk
```
```leanOutput minpair
failed to infer structural recursion:
Cannot use parameter nk:
  the type Nat × Nat does not have a `.brecOn` recursor
```

这是因为参数的类型 {name}`Prod` 不是递归的。
因此，其构造函数没有可由模式匹配公开的递归参数。

使用 {tech (key := "well-founded recursion")}[良基递归] 可以接受此定义，但是：
```lean
def min' (nk : Nat × Nat) : Nat :=
  match nk with
  | (0, _) => 0
  | (_, 0) => 0
  | (n' + 1, k' + 1) => min' (n', k') + 1
termination_by nk
```
:::

```lean -show
section
variable (n n' : Nat)
```
:::example "Structural Recursion and Definitional Equality"

即使 {lean}`countdown` 的递归出现应用于不是递减参数的严格子项的项，也接受以下定义：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown (n' + 0)
termination_by structural n
```

这是因为 {lean}`n' + 0` 是 {tech (key := "definitional equality")}[定义等于] {lean}`n'`，这是 {lean}`n` 的严格子术语。
从模式匹配生成的 {tech (key := "strict sub-term")}[子项] 使用 {ref "match-generalization"}[匹配泛化] 的规则连接到 {tech (key := "match discriminant")}[判别]，该规则尊重 定义等价。

在 {lean}`countdown'` 中，递归出现应用于 {lean}`0 + n'`，它在定义上并不等于 `n'`，因为自然数上的加法在其第二个参数中是结构递归的：
```lean +error (name := countdownNonDefEq)
def countdown' (n : Nat) : List Nat :=
  match n with
  | 0 => []
  | n' + 1 => n' :: countdown' (0 + n')
termination_by structural n
```
```leanOutput countdownNonDefEq
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    countdown' (0 + n')
```

:::
```lean -show
end
```

# 相互结构递归
%%%
file := "Mutual-Structural-Recursion"
tag := "mutual-structural-recursion"
%%%

Lean 支持使用结构递归定义 {tech (key := "mutually recursive")}[相互递归]函数。
可以使用 {tech}[mutual block] 引入相互递归，但它也可以由 {keywordOf Lean.Parser.Term.letrec}`let rec` 表达式和 {keywordOf Lean.Parser.Command.declaration}`where` 块产生。
相互结构递归的规则应用于一组实际相互递归、提升的定义，这些定义由相互组的 {ref "mutual-syntax"}[精化步骤] 产生。
如果共同组中的每个函数都有一个 {keyword}`termination_by structural` 注释来指示该函数的递减参数，则使用结构递归来转换定义。

对上述递减参数的要求进行扩展：

 * 所有递减参数的所有类型必须来自同一归纳类型，或者更一般地来自同一 {ref "mutual-inductive-types"}[归纳类型的共同组]。

 * 对于所有函数，递减参数类型的参数必须相同，并且可能仅取决于函数参数的 _common_ 固定前缀。

这些功能不必与相互的归纳类型一对一对应。
多个函数可以具有相同类型的递减参数，并且并非所有与递减参数相互递归的类型都需要具有相应的函数。

:::example "Mutual Structural Recursion Over Non-Mutual Types"

以下示例演示了非互归纳数据类型上的相互递归：

```lean
mutual
  def even : Nat → Prop
    | 0 => True
    | n+1 => odd n
  termination_by structural n => n

  def odd : Nat → Prop
    | 0 => False
    | n+1 => even n
  termination_by structural n => n
end
```
:::

:::example "Mutual Structural Recursion Over Mutual Types"

以下示例演示了相互归纳类型上的递归。
函数 {lean}`Exp.size` 和 {lean}`App.size` 是相互递归的。

```lean
mutual
  inductive Exp where
    | var : String → Exp
    | app : App → Exp

  inductive App where
    | fn : String → App
    | app : App → Exp → App
end

mutual
  def Exp.size : Exp → Nat
    | .var _ => 1
    | .app a => a.size
  termination_by structural e => e

  def App.size : App → Nat
    | .fn _ => 1
    | .app a e => a.size + e.size + 1
  termination_by structural a => a
end
```

{lean}`App.numArgs` 的定义在类型 {lean}`App` 上进行结构递归。
说明并非交互组中的所有归纳类型都需要处理。

```lean
def App.numArgs : App → Nat
  | .fn _ => 0
  | .app a _ => a.numArgs + 1
termination_by structural a => a
```

:::

::::draft
:::planned 235

描述 {ref "nested-inductive-types"}[嵌套归纳类型] 上的相互结构递归。

:::
::::

# 推断结构递归
%%%
file := "Inferring-Structural-Recursion"
tag := "inferring-structural-recursion"
%%%


如果递归或互递归函数定义中不存在 {keyword}`termination_by` 子句，则 Lean 尝试通过按顺序尝试所有合适的参数来有效地推断合适的结构递减参数。
如果此搜索失败，Lean 将尝试推断 {tech (key := "well-founded recursion")}[良基递归]。

对于相互递归函数，会尝试所有参数组合，直至达到极限以避免组合爆炸。
如果只有部分相互递归函数具有 {keyword}`termination_by structural` 子句，则仅考虑这些参数，而对于其他函数，则考虑结构递归的所有参数。

{keyword}`termination_by?` 子句导致显示推断的终止注释。
可以使用提供的建议或代码操作将其自动添加到源文件中。

:::example "Inferred Termination Annotations"
Lean 自动推断函数 {lean}`half` 在结构上是递归的。
{keyword}`termination_by?` 子句会导致显示推断的终止注释，并且只需单击一下即可将其自动添加到源文件中。

```lean (name := inferStruct)
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
termination_by?
```
```leanOutput inferStruct
Try this:
  [apply] termination_by structural x => x
```
:::

# 精化使用值过程递归
%%%
file := "Elaboration-Using-Course-of-Values-Recursion"
tag := "elab-as-course-of-values"
%%%

在本节中，将更详细地解释用于精化结构递归函数的构造。
此精化使用从归纳类型递归器自动生成的 {ref "recursor-elaboration-helpers"}[`below` 和 `brecOn` 结构]。

{spliceContents ManualZh.RecursiveDefs.Structural.RecursorExample}

结构递归分析尝试将递归 {tech (key := "pre-definition")}[预定义] 转换为适当的结构递归结构的使用。
到这一步，模式匹配已经被翻译成匹配器函数的使用；这些由终止检查器进行特殊处理。
接下来，对于每组参数，尝试使用 `brecOn` 进行转换。

{spliceContents ManualZh.RecursiveDefs.Structural.CourseOfValuesExample}

`below` 构造是从类型的每个值到对所有较小值进行某些函数调用的结果的映射；它可以理解为一个记忆表，其中已经包含了所有较小值的结果。
`below` 结构中表达的“较小值”的概念直接对应于 {tech (key := "strict sub-terms")}[严格子术语]的定义。

递归器需要归纳类型的每个构造函数都有一个参数；在 {tech}[ι-reduction] 期间，使用构造函数的参数（以及递归参数的递归结果）调用这些参数。
另一方面，值过程递归运算符 `brecOn` 只需要一个一次性覆盖所有构造函数的情况。
这种情况提供了一个值和一个 `below` 表，该表包含所有小于给定值的值的递归结果；它应该使用表的内容来满足提供值的动机。
如果函数在给定参数（或参数组）上进行结构递归，则所有递归调用的结果都将出现在该表中。

当递归函数的主体转换为对函数参数之一的 `brecOn` 的调用时，该参数及其值过程表位于范围内。
分析遍历函数体，寻找递归调用。
如果参数匹配，则其在本地上下文中的出现次数为 {ref "match-generalization"}[generalized]，然后使用模式实例化；对于值过程表的类型也是如此。
通常，此模式匹配会导致值过程表的类型变得更加具体，从而可以访问较小值的递归结果。
该泛化过程实现了模式是匹配判别式的 {tech (key := "strict sub-term")}[子项] 的规则。
当检测到函数的递归出现时，将查阅值过程表以查看它是否包含正在检查的参数的结果。
如果是这样，则可以用表中的投影来替换递归调用。
如果不是，则相关参数不支持结构递归。

```lean -show
section
```

:::example "Elaboration Walkthrough"
遍历 {name}`half` 的精化的第一步是将其手动脱糖为更简单的形式。
这与 Lean 的工作方式不匹配，但当存在的 {name}`OfNat` 实例较少时，其输出更容易阅读。
这个可读的定义：
```lean -keep
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
可以重写为这个较低级别的版本：
```lean -keep
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```

精化器首先精化了一个预定义，其中递归仍然存在，但定义在 Lean 的核心 类型论 中。
打开编译器对预定义的跟踪，并使漂亮的打印机更加明确，使生成的预定义可见：
```lean -keep -show
-- Test of next block - visually check correspondence when updating!
set_option trace.Elab.definition.body true in
set_option pp.all true in

/--
trace: [Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x (fun (_ : Unit) => Nat.zero) (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
-/
#guard_msgs in
def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
```lean (name := tracedHalf)
set_option trace.Elab.definition.body true in
set_option pp.all true in

def half : Nat → Nat
  | .zero | .succ .zero => .zero
  | .succ (.succ n) => half n |>.succ
```
返回的跟踪消息是：{TODO}[跟踪未显示在序列化信息中 - 找出原因，以便此测试可以更好地工作，或者更好的是，向 Verso 添加适当的跟踪渲染]
```
[Elab.definition.body] half : Nat → Nat :=
    fun (x : Nat) =>
      half.match_1.{1} (fun (x : Nat) => Nat) x
        (fun (_ : Unit) => Nat.zero)
        (fun (_ : Unit) => Nat.zero)
        fun (n : Nat) => Nat.succ (half n)
```
辅助匹配函数的定义为：
```lean (name := halfmatch)
#print half.match_1
```
```leanOutput halfmatch (whitespace := lax)
@[implicit_reducible] def half.match_1.{u_1} :
    (motive : Nat → Sort u_1) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
格式更易读，这个定义是：
```lean
def half.match_1'.{u} :
    (motive : Nat → Sort u) → (x : Nat) →
    (Unit → motive Nat.zero) → (Unit → motive 1) →
    ((n : Nat) → motive n.succ.succ) →
    motive x :=
  fun motive x h_1 h_2 h_3 =>
    Nat.casesOn x (h_1 ()) fun n =>
      Nat.casesOn n (h_2 ()) fun n =>
        h_3 n
```
换句话说，{name}`half` 中使用的模式的具体配置在 {name}`half.match_1` 中捕获。

该定义是 {name}`half` 预定义的更具可读性的版本：
```lean
def half' : Nat → Nat :=
  fun (x : Nat) =>
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
```

要将其精化为结构递归函数，第一步是建立 `bRecOn` 调用。
该定义必须标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable`，因为 Lean 不支持递归器（例如 {name}`Nat.brecOn`）的代码生成。
```lean +error -keep
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      _
/- To translate:
    half.match_1 (motive := fun _ => Nat) x
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

下一步是将原始函数体中出现的 `x` 替换为 {name Nat.brecOn}`brecOn` 提供的 `n`。
由于 `table` 的类型取决于 `x`，因此在使用 {name}`half.match_1` 拆分案例时也必须对其进行泛化，从而导致带有额外参数的动机。

```lean +error -keep (name := threeCases)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        _
        _
        _)
      table
/- To translate:
      (fun _ => 0) -- Case for 0
      (fun _ => 0) -- Case for 1
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```
这三种情况的占位符需要以下类型：
```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_1`
context:
x n : Nat
table : Nat.below n
⊢ Unit → Nat.below Nat.zero → Nat
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_2`
context:
x n : Nat
table : Nat.below n
⊢ Unit → Nat.below 1 → Nat
```

```leanOutput threeCases
don't know how to synthesize placeholder for argument `h_3`
context:
x n : Nat
table : Nat.below n
⊢ (n : Nat) → Nat.below n.succ.succ → Nat
```

预定义中的前两种情况是常量函数，无需检查递归：

```lean +error -keep (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        _)
      table
/- To translate:
      (fun n => Nat.succ (half' n)) -- Case for n + 2
-/
```

最后一种情况包含递归调用。
它应该转换为对值过程表的查找。
最后一个孔类型的更易读的表示是：
```leanTerm
(n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat
```
这相当于
```leanTerm
(n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat
```

```lean -show
example : ((n : Nat) →
Nat.below (motive := fun _ => Nat) n.succ.succ →
Nat) = ((n : Nat) →
Nat ×' (Nat ×' Nat.below (motive := fun _ => Nat) n) →
Nat) := rfl
```

```lean -show

variable {n : Nat}
```

值过程表中的第一个 {lean}`Nat` 是 {lean}`n + 1` 的递归结果，第二个是 {lean}`n` 的递归结果。
因此，递归调用可以替换为查找，并且精化成功：

```lean +error -keep (name := oneMore)
noncomputable
def half'' : Nat → Nat :=
  fun (x : Nat) =>
    x.brecOn fun n table =>
      (half.match_1
        (motive :=
          fun k =>
            k.below (motive := fun _ => Nat) →
            Nat)
        n
        (fun () _ => .zero)
        (fun () _ => .zero)
        (fun _ table => Nat.succ table.2.1)
      table
```

实际的精化器通过将具有新名称的哨兵类型插入到动机中来跟踪为结构递归检查的参数与值过程表中的位置之间的关系。
:::

```lean -show
end
```

::::draft
::: planned 56
相互递归函数精化的描述
:::
::::
