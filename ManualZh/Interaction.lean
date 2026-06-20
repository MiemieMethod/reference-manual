/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import ManualZh.Interaction.FormatRepr

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "与 Lean 交互" =>
%%%
htmlSplit := .never
tag := "interaction"
%%%

Lean 专为交互式使用而设计，而不是作为批处理模式系统，在批处理模式系统中将整个文件输入然后转换为目标代码或错误消息。
许多设计用于交互式使用的编程语言都提供 {deftech}[REPL]、{margin}[{noVale "Vale can't handle partly-bolded words"}[“*R*ead-*E*val-*P*rint *L*oop”] 的缩写；代码会被解析（“read”）、求值并显示结果，此过程可按需重复。]可在其中输入和测试代码，并使用加载源文件、类型检查术语或查询环境的命令。
Lean 的交互功能基于不同的范例。
Lean 提供了 {tech (key := "commands")}[命令]，用于在源文件上下文中完成相同的任务，而不是在程序外部提供单独的命令提示符。
按照惯例，用于交互使用而不是作为持久代码工件的一部分的命令以 {keyword}`#` 为前缀。

Lean 命令的信息可在 {deftech}_message log_ 中获取，它累积来自 {tech (key := "Lean elaborator")}[精化器] 的输出。
消息日志中的每个条目都与特定的源范围相关联，并具有 {deftech}_severity_。
共有三种严重性：{lean  (type := "Lean.MessageSeverity")}`information` 用于不指示问题的消息，{lean  (type := "Lean.MessageSeverity")}`warning` 指示潜在问题，{lean  (type := "Lean.MessageSeverity")}`error` 指示明确问题。
对于交互式命令，结果通常作为与命令的前导关键字关联的信息性消息返回。

# 评估条款
%%%
tag := "hash-eval"
%%%

{keywordOf Lean.Parser.Command.eval}`#eval` 命令用于将代码作为程序运行。
特别是，它能够执行 {lean}`IO` 操作，它使用按值调用评估策略{ref "partial-unsafe"}[执行 {keyword}`partial` 函数]，并且类型和证明都被删除。
使用 {keywordOf Lean.reduceCmd}`#reduce` 来使用 {tech (key := "definitional equality")}[定义等价] 中的归约规则来归约项。

:::syntax command (title := "Evaluating Terms")

```grammar
#eval $t
```

```grammar
#eval! $t
```

{includeDocstring Lean.Parser.Command.eval}

:::

{keywordOf Lean.Parser.Command.eval}`#eval` 始终 {tech (key := "Lean elaborator")}[详细说明] 并编译提供的术语。
然后，它检查该术语是否传递依赖于 {lean}`sorry` 的任何使用，在这种情况下，评估将终止，除非该命令作为 {keywordOf Lean.Parser.Command.eval}`#eval!` 调用。
这是因为编译的代码可能依赖于由适当语句的证明确保的编译时不变量（例如数组查找在范围内），并且运行包含不完整证明的代码（或使用 {lean}`sorry`“证明”不正确的语句）可能会导致 Lean 本身崩溃。

```lean -show
section
variable (m : Type → Type)
open Lean.Elab.Command (CommandElabM)
```

:::paragraph

代码的运行方式取决于其类型：

 * 如果该类型位于 {lean}`IO` 单子中，则它在捕获 {tech (key := "standard output")}[标准输出] 和 {tech (key := "standard error")}[标准错误] 的上下文中执行，并将其重定向到 Lean {tech (key := "message log")}[消息日志]。
   如果返回值的类型不是 {lean}`Unit`，则它会显示为非一元表达式的结果。
 * 如果该类型位于内部 Lean 元编程 monad（{name Lean.Elab.Command.CommandElabM}`CommandElabM`、{name Lean.Elab.Term.TermElabM}`TermElabM`、{name Lean.MetaM}`MetaM` 或 {name Lean.CoreM}`CoreM`）之一中，则它在当前上下文中运行。
    例如，环境将包含调用 {keywordOf Lean.Parser.Command.eval}`#eval` 的范围内的定义。
    与 {name}`IO` 一样，结果值显示为非一元表达式的结果。
    当 Lean 在 {ref "lake"}[Lake] 下运行时，其工作目录（以及 {name}`IO` 操作的工作目录）是当前的 {tech}`workspace`。
 * 如果该类型位于其他某个单子 {lean}`m` 中，并且存在 {lean}`MonadLiftT m CommandElabM` 或 {lean}`MonadEvalT m CommandElabM` 实例，则使用 {name}`MonadLiftT.monadLift` 或 {name}`MonadEvalT.monadEval` 将单子转换为可以与 {keywordOf Lean.Parser.Command.eval}`#eval` 一起运行的单子，然后照常运行。
 * 如果该术语的类型不在任何受支持的 monad 中，则将其视为纯值。
  运行编译后的代码，并显示结果。

由于详细精化{keywordOf Lean.Parser.Command.eval}`#eval` 中的术语而产生的辅助定义或其他环境修改将被丢弃。
如果该术语是元编程单子中的操作，则通过运行单子操作对环境所做的更改将被保留。
:::

```lean -show
end
```


在 {tech}`module` 中使用时，{keywordOf Lean.Parser.Command.eval}`#eval` 显示了 Lean 语言服务器和 Lean 编译器处理文件的方式之间的差异。
由于它在编译时运行代码，因此 {keywordOf Lean.Parser.Command.eval}`#eval` 要求其代码在 {tech (key := "meta phase")}[元阶段] 中可用。
为了更容易地试验模块，语言服务器使所有导入的模块在元阶段可用，而编译器严格遵守 {keywordOf Lean.Parser.Module.import}`meta` 声明。
因此，使用 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 与 {keywordOf Lean.Parser.Command.eval}`#eval` 一起嵌入轻量级测试的模块可能会在语言服务器中成功详细说明，但在构建过程中会失败。
要解决此问题，可以使用包含测试的模块中的 {keywordOf Lean.Parser.Module.import}`meta import` 导入定义：

::::example "Evaluation and Meta"
:::leanModules -server +error
```leanModule (moduleName := Eval.Even)
module
public section
def isEven (n : Nat) : Bool :=
  n % 2 = 0

```
```leanModule (moduleName := Eval) (name := noMetaEval)
module
import Eval.Even

/-- info: [true, false] -/
#guard_msgs in
#eval [isEven 4, isEven 5]
```
```leanOutput noMetaEval
❌️ Docstring on `#guard_msgs` does not match generated message:

- info: [true, false]
+ error: Invalid `meta` definition `_eval`, `isEven` is not accessible here; consider adding `public meta import Eval.Even`
```
:::
:::leanModules
将 {name}`isEven` 导入元阶段修复了问题：
```leanModule (moduleName := Eval.Even)
module
public section
def isEven (n : Nat) : Bool :=
  n % 2 = 0
```
```leanModule (moduleName := Eval) (name := metaEval)
module
meta import Eval.Even

/-- info: [true, false] -/
#guard_msgs in
#eval [isEven 4, isEven 5]
```
:::
::::


使用 {name Lean.ToExpr}`ToExpr`、{name}`ToString` 或 {name}`Repr` 实例（如果存在）显示结果。
如果不是，并且 {option}`eval.derive.repr` 是 {lean}`true`，则 Lean 尝试派生合适的 {name}`Repr` 实例。
如果找不到或派生出合适的实例，则这是一个错误。
将 {option}`eval.pp` 设置为 {lean}`false` 将禁止 {keywordOf Lean.Parser.Command.eval}`#eval` 使用 {name Lean.ToExpr}`ToExpr` 实例。

:::example "Displaying Output"

{keywordOf Lean.Parser.Command.eval}`#eval`无法显示功能：
```lean (name := funEval) +error
#eval fun x => x + 1
```
```leanOutput funEval
Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Nat → Nat
```

它能够派生实例来显示没有 {name}`ToString` 或 {name}`Repr` 实例的输出：

```lean (name := quadEval)
inductive Quadrant where
  | nw | sw | se | ne

#eval Quadrant.nw
```
```leanOutput quadEval
Quadrant.nw
```

不保存派生实例。
禁用 {option}`eval.derive.repr` 会导致 {keywordOf Lean.Parser.Command.eval}`#eval` 失败：

```lean (name := quadEval2) +error
set_option eval.derive.repr false
#eval Quadrant.nw
```
```leanOutput quadEval2
Could not synthesize a `ToExpr`, `Repr`, or `ToString` instance for type
  Quadrant
```

:::

{optionDocs eval.pp}

{optionDocs eval.type}

{optionDocs eval.derive.repr}

通过定义合适的 {lean}`MonadLift`{margin}[{lean}`MonadLift` 在 {ref "lifting-monads"}[有关提升 monad 的部分]] 或 {lean}`MonadEval` 实例中描述，可以赋予 Monad 在 {keywordOf Lean.Parser.Command.eval}`#eval` 中执行的能力。
正如 {name}`MonadLiftT` 是 {name}`MonadLift` 实例的传递闭包一样，{name}`MonadEvalT` 是 {name}`MonadEval` 实例的传递闭包。
与 {name}`MonadLiftT` 一样，用户不应直接定义 {name}`MonadEvalT` 的其他实例。

{docstring MonadEval}

{docstring MonadEvalT}

# 减少条款
%%%
tag := "hash-reduce"
%%%

{keywordOf Lean.reduceCmd}`#reduce` 命令重复对一项进行缩减，直到无法进一步缩减为止。
缩减是在活页夹下执行的，但为了避免意外的速度减慢，除非启用了 {keywordOf Lean.reduceCmd}`#reduce` 的相应选项，否则将跳过证明和类型。
与 {keywordOf Lean.Parser.Command.eval}`#eval` 命令不同，归约不会产生副作用，并且结果显示为术语，而不是通过 {name}`ToString` 或 {name}`Repr` 实例显示。

一般来说，{keywordOf Lean.reduceCmd}`#reduce` 主要用于诊断 定义等价 和证明项的问题，而 {keywordOf Lean.Parser.Command.eval}`#eval` 更适合计算项的值。
特别是，使用 {tech (key := "well-founded recursion")}[良基递归] 或 {tech (key := "partial fixpoints")}[部分固定点] 定义的函数要么使用归约引擎计算非常慢，要么根本不会归约。

:::syntax command (title := "Reducing Terms")
```grammar
#reduce $[($ident := $tm)]* $t
```

{includeDocstring Lean.reduceCmd}

:::

:::example "Reducing Functions"

减少一项会导致 Lean 逻辑中的正常形式。
由于基础术语会先减少然后显示，所以不需要 {name}`ToString` 或 {name}`Repr` 实例。
函数可以像任何其他术语一样显示。

在某些情况下，这种范式很短，类似于人们可能写的术语：
```lean (name := plusOne)
#reduce (fun x => x + 1)
```
```leanOutput plusOne
fun x => x.succ
```

在其他情况下，{ref "elab-as-course-of-values"}[函数的精化] 的详细信息（例如 Lean 的核心逻辑的添加）会被暴露：
```lean (name := onePlus)
#reduce (fun x => 1 + x)
```
```leanOutput onePlus
fun x => (Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) x).1 1
```

:::

# 检查类型
%%%
tag := "hash-check"
%%%

:::syntax command (title := "Checking Types")

{keyword}`#check` 可用于详细说明术语并检查其类型。

```grammar
#check $t
```

如果提供的术语是全局常量名称的标识符，则 {keyword}`#check` 打印其签名。
否则，该术语将被详细说明为 Lean 术语并打印其类型。
:::

{keywordOf Lean.Parser.Command.check}`#check` 中的术语精化不要求对该术语进行充分精化；它可能包含元变量。
如果所写的项_可能_具有类型，则精化成功。
如果永远无法合成所需的实例，则精化失败；由元变量引起的综合问题不会阻止精化。


:::example "{keyword}`#check` and Underdetermined Types"
在此示例中，列表元素的类型未确定，因此该类型包含一个元变量：
```lean (name := singletonList)
#check fun x => [x]
```
```leanOutput singletonList
fun x => [x] : ?m.9 → List ?m.9
```

在此示例中，所添加的项的类型和加法的结果类型都是未知的，因为{name}`HAdd`允许添加不同类型的项。
在幕后，元变量代表未知的 {name}`HAdd` 实例。
```lean (name := polyPlus)
#check fun x => x + x
```
```leanOutput polyPlus
fun x => x + x : (x : ?m.12) → ?m.19 x
```

:::

:::syntax command (title := "Testing Type Errors")
```grammar
#check_failure $t
```
{keywordOf Lean.Parser.Command.check}`#check` 的此变体使用与 {keywordOf Lean.Parser.Command.check}`#check` 相同的过程来详细精化该术语。
如果精化成功，则为错误；如果失败，则没有错误。
部分精化的术语和发现的任何类型信息都将添加到 {tech (key := "message log")}[消息日志]。
:::


:::example "Checking for Type Errors"

正如预期的那样，尝试将字符串添加到自然数失败：
```lean (name := oneOne)
#check_failure "one" + 1
```
```leanOutput oneOne
failed to synthesize instance of type class
  HAdd String Nat ?m.5

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
尽管如此，还是有一个部分精化的术语：
```leanOutput oneOne
"one" + 1 : ?m.32
```

:::

# 综合实例
%%%
tag := "hash-synth"
%%%

:::syntax command (title := "Synthesizing Instances")
```grammar
#synth $t
```
:::

{keywordOf Lean.Parser.Command.synth}`#synth` 命令调用 Lean 的 {tech (key := "type class")}[类型类] 解析机制，并尝试执行 {ref "instance-synth"}[实例合成] 来查找给定类型类的实例。
如果成功，则输出结果实例项。

::::example "Synthesizing a Type Class Instance"

:::paragraph
Lean 使用类型类来重载加法等操作。
`+` 运算符是调用 {name}`HAdd.hAdd` 的符号，它是 {name}`HAdd` 类型类中的单个方法。
此示例显示 Lean 让我们将两个整数相加，结果将是一个整数：
```lean (name := synthInstHAddNat)
#synth HAdd Int Int Int
```
```leanOutput synthInstHAddNat
instHAdd
```
:::

:::paragraph
默认情况下，Lean 不显示输出项中的隐式参数。
然而，实例参数是隐式的，这降低了此输出对于理解实例综合的有用性。
将选项 {option}`pp.explicit` 设置为 {name}`true` 会导致 Lean 显示隐式参数，包括实例：
```lean (name := synthInstHAddNat2)
set_option pp.explicit true in
#synth HAdd Int Int Int
```
```leanOutput synthInstHAddNat2
@instHAdd Int Int.instAdd
```
:::

:::paragraph
Lean 不允许添加整数和字符串，如类型类实例合成失败所示：
```lean (name := synthInstHAddNatInt) +error
#synth HAdd Int String String
```
```leanOutput synthInstHAddNatInt
failed to synthesize
  HAdd Int String String

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::


::::

# 查询上下文
%%%
tag := "hash-print"
%%%

{keyword}`#print` 系列命令用于查询 Lean 以获取有关定义的信息。

:::syntax command (title := "Printing Definitions")
```grammar
#print $t:ident
```

打印常量的定义。
:::

使用 {keywordOf Lean.Parser.Command.print}`#print` 打印定义会将定义打印为术语。
使用 {ref "tactics"}[策略] 证明的定理在打印为项时可能会非常大。

:::syntax command (title := "Printing Strings")
```grammar
#print $s:str
```

将字符串文字添加到 Lean 的 {tech (key := "message log")}[消息日志]。
:::


:::syntax command (title := "Printing Axioms")
```grammar
#print axioms $t
```

列出常量传递依赖的所有公理。有关更多信息，请参阅 {ref "print-axioms"}[公理文档]。
:::

:::example "Printing Axioms"
```imports -show
import Std.Tactic.BVDecide
```

这两个函数各自交换一对位向量中的元素：

```lean
def swap (x y : BitVec 32) : BitVec 32 × BitVec 32 :=
  (y, x)

def swap' (x y : BitVec 32) : BitVec 32 × BitVec 32 :=
  let x := x ^^^ y
  let y := x ^^^ y
  let x := x ^^^ y
  (x, y)
```

使用 {ref "function-extensionality"}[函数扩展性]、{ref "the-simplifier"}[简化器] 和 {tactic}`bv_decide` 可以证明它们是相等的：
```lean
theorem swap_eq_swap' : swap = swap' := by
  funext x y
  simp only [swap, swap', Prod.mk.injEq]
  bv_decide
```

由此产生的证明使用了许多公理：
```lean (name := axioms)
#print axioms swap_eq_swap'
```
```leanOutput axioms
'swap_eq_swap'' depends on axioms: [propext, Classical.choice, Quot.sound, swap_eq_swap'._native.bv_decide.ax_3]
```

公理 {name}`swap_eq_swap'._native.bv_decide.ax_3` 由 {tactic}`bv_decide` 生成，表明本机代码用于将外部证明证书转换为 Lean 证明项。
:::

:::syntax command (title := "Printing Equations")
命令 {keywordOf Lean.Parser.Command.printEqns}`#print equations`（可缩写为 {keywordOf Lean.Parser.Command.printEqns}`#print eqns`）显示函数的 {tech (key := "equational lemmas")}[方程引理]。
```grammar
#print equations $t
```
```grammar
#print eqns $t
```
:::

:::example "Printing Equations"

```lean (name := intersperse_eqns)
def intersperse (x : α) : List α → List α
  | y :: z :: zs => y :: x :: intersperse x (z :: zs)
  | xs => xs

#print equations intersperse
```
```leanOutput intersperse_eqns
equations:
@[backward_defeq] theorem intersperse.eq_1.{u_1} : ∀ {α : Type u_1} (x y z : α) (zs : List α),
  intersperse x (y :: z :: zs) = y :: x :: intersperse x (z :: zs)
theorem intersperse.eq_2.{u_1} : ∀ {α : Type u_1} (x : α) (x_1 : List α),
  (∀ (y z : α) (zs : List α), x_1 = y :: z :: zs → False) → intersperse x x_1 = x_1
```

它不打印定义方程，也不打印展开方程：
```lean (name := intersperse_eq_def)
#check intersperse.eq_def
```
```leanOutput intersperse_eq_def
intersperse.eq_def.{u_1} {α : Type u_1} (x : α) (x✝ : List α) :
  intersperse x x✝ =
    match x✝ with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```

```lean (name := intersperse_eq_unfold)
#check intersperse.eq_unfold
```
```leanOutput intersperse_eq_unfold
intersperse.eq_unfold.{u_1} :
  @intersperse = fun {α} x x_1 =>
    match x_1 with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```

:::

:::syntax command (title := "Scope Information")

{includeDocstring Lean.Parser.Command.where}

```grammar
#where
```
:::

:::example "Scope Information"
{keywordOf Lean.Parser.Command.where}`#where` 命令显示对当前 {tech (key := "section scope")}[节范围] 所做的所有修改，无论是在当前范围还是在其嵌套的范围中。

```lean +fresh (name := scopeInfo)
section
open Nat

namespace A
variable (n : Nat)
namespace B

open List
set_option pp.funBinderTypes true

#where

end A.B
end
```
```leanOutput scopeInfo (allowDiff := 1)
namespace A.B

open Nat List

variable (n : Nat)

set_option pp.funBinderTypes true
```

:::

:::syntax command (title := "Checking the Lean Version")

{includeDocstring Lean.Parser.Command.version}

```grammar
#version
```
:::


# 使用 {keyword}`#guard_msgs` 测试输出
%%%
tag := "hash-guard_msgs"
%%%

{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令可用于确保命令输出的消息符合预期。
与本节中的交互命令一起，它可用于构造一个文件，该文件仅在输出符合预期时才会详细说明；这样的文件可以用作 {ref "lake"}[Lake] 中的 {tech (key := "test driver")}[测试驱动程序]。

:::syntax command (title := "Documenting Expected Output")
```grammar
$[$_:docComment]?
#guard_msgs $[($_,*)]? in
$c:command
```

{includeDocstring Lean.guardMsgsCmd}

:::

:::example "Testing Return Values"

{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令可以确保一组测试用例通过：

```lean
def reverse : List α → List α := helper []
where
  helper acc
    | [] => acc
    | x :: xs => helper (x :: acc) xs

/-- info: [] -/
#guard_msgs in
#eval reverse ([] : List Nat)

/-- info: ['c', 'b', 'a'] -/
#guard_msgs in
#eval reverse "abc".toList
```

:::


:::paragraph
可以通过三种方式指定 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令的行为：

 1. 提供一个过滤器来选择要检查的消息子集

 2. 指定空白比较策略

 3. 决定按消息内容或消息生成顺序对消息进行排序

这些配置选项在括号中提供，并用逗号分隔。
:::

::::syntax Lean.guardMsgsSpecElt (title := "Specifying {keyword}`#guard_msgs` Behavior") -open

```grammar
$_:guardMsgsFilter
```
```grammar
whitespace := $_
```
```grammar
ordering := $_
```

{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 共有三种选项：过滤器、空白比较策略和排序。
::::

:::syntax Lean.guardMsgsFilter (title := "Output Filters for {keyword}`#guard_msgs`") -open
```grammar
$[drop]? all
```
```grammar
$[drop]? info
```
```grammar
$[drop]? warning
```
```grammar
$[drop]? error
```

{includeDocstring Lean.guardMsgsFilter}

:::


:::syntax Lean.guardMsgsWhitespaceArg (title := "Whitespace Comparison for `#guard_msgs`") -open
```grammar
exact
```
```grammar
lax
```
```grammar
normalized
```


比较消息时，始终忽略前导和尾随空格。除此之外，还可以使用以下设置：

 * `whitespace := exact` 需要精确的空格匹配。

 * `whitespace := normalized` 在匹配之前将所有换行符转换为空格（默认）。这允许打破长线。

 * `whitespace := lax` 在匹配之前将空格折叠为单个空格。

:::

选项 {option}`guard_msgs.diff` 控制当预期消息与生成的消息不匹配时 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 生成的错误消息的内容。
默认情况下，{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 显示逐行差异，前导 `+` 用于指示生成消息中的行，前导 `-` 用于指示预期消息中的行。
当消息很大且差异很小时，这可以更容易地注意到它们的差异。
将 {option}`guard_msgs.diff` 设置为 `false` 会导致 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 仅显示生成的消息，该消息可以与源文件中的预期消息进行比较。
如果消息之间的差异令人困惑或难以承受，这会很方便。

{optionDocs guard_msgs.diff}

:::example "Displaying Differences"
{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令可用于测试玫瑰树 {lean}`Tree` 的定义以及创建它们的函数 {lean}`Tree.big`：

```lean
inductive Tree (α : Type u) : Type u where
  | val : α → Tree α
  | branches : List (Tree α) → Tree α

def Tree.big (n : Nat) : Tree Nat :=
  if n < 5 then .branches [.val n, .val (n - 1), .val n, .val (n - 2)]
  else .branches [.big (n / 2),  .big (n / 3)]
```

然而，当输出很大时，很难发现测试失败的根源：
```lean +error (name := bigMsg)
set_option guard_msgs.diff false
/--
info: Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0],
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
-/
#guard_msgs in
#eval Tree.big 20
```
评估产生：
```leanOutput bigMsg (severity := information)
Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0]],
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
```

如果没有 {option}`guard_msgs.diff`，{keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令会报告以下错误：
```leanOutput bigMsg (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

info: Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0]],
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
```

相反，启用 {option}`guard_msgs.diff` 会突出显示差异，使错误更加明显：
```lean +error (name := bigMsg')
set_option guard_msgs.diff true in
/--
info: Tree.branches
  [Tree.branches
     [Tree.branches
        [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
         Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0,
      Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
   Tree.branches
     [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
      Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
-/
#guard_msgs in
#eval Tree.big 20
```
```leanOutput bigMsg'  (severity := error)
❌️ Docstring on `#guard_msgs` does not match generated message:

  info: Tree.branches
    [Tree.branches
       [Tree.branches
          [Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0],
-          Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0,
+          Tree.branches [Tree.val 1, Tree.val 0, Tree.val 1, Tree.val 0]],
        Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1]],
     Tree.branches
       [Tree.branches [Tree.val 3, Tree.val 2, Tree.val 3, Tree.val 1],
        Tree.branches [Tree.val 2, Tree.val 1, Tree.val 2, Tree.val 0]]]
```
:::

{include 1 ManualZh.Interaction.FormatRepr}
