/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Meta
import Manual.Papers

import ManualZh.ValidatingProofs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option guard_msgs.diff true

open Lean (Syntax SourceInfo)

open Illuminate in
def pipelineDiagram : Diagram SVG :=
  let resultStyle : TextStyle := { fontSize := 20, bold := true }
  let result :=
    Diagram.hsep (align := .bottom) 8
      [.text "✔" { resultStyle with color := Color.green }, .text "/" resultStyle, .text "✖" resultStyle]
      |>.pad 8
      |>.namedWithAnchors `result
  let codeLabel :=
    Diagram.text "Code.lean"
      (style := { fontFamily := "monospace", fontSize := 12 })
      |>.pad 12
  let code :=
    Diagram.paper
      (name := `source)
      (label := some codeLabel)
      (width := some 80)
      (height := some 100)
      (fill := Color.white)
  Diagram.grid (hSpacing := 70) (vSpacing := 50) #[
    #[some code,                            none],
    #[some (box `stx "Syntax\nTree"),        none],
    #[some (box `core "Core Type\nTheory"), some (box `kernel "Core Type\nTheory\n(no recursion)")],
    #[some (box `exe "Executable"),         some result]
  ]
  -- Arrows with stealth arrowheads and upright labels
    |>.connect `source.south `stx.north
      (label := lbl "Parsing") (arrowhead := ah)
    |>.connect `stx.south `core.north
      (label := lbl "Elaboration") (arrowhead := ah)
    |>.connect `core.south `exe.north
      (label := lbl "Compilation") (arrowhead := ah)
    |>.connect `core.east `kernel.west
      (label := lbl "Recursion\nElimination") (arrowhead := ah)
  -- Self-loop on Syntax Tree for macro expansion (left side)
    |>.connect
      { point := `stx.west, shift := ⟨0, -10⟩, angle := some (pi + pi / 7), pull := 3.5 }
      { point := `stx.west, shift := ⟨0, 10⟩, angle := some (0 - pi / 7), pull := 3.5 }
      (label := lbl "Macro\nExpansion") (arrowhead := ah)
  -- Kernel check arrow
    |>.connect `kernel.south `result.north
      (label := lbl "Kernel\nCheck") (arrowhead := ah)
where
  ah : Arrowhead := { type := .stealth }
  lbl (s : String) : Option (Label SVG) :=
    some { label := .text s { fontSize := 10 }, upright := true }
  box (name : Lean.Name) (label : String) (fontFamily := "sans-serif") : Diagram SVG :=
    Diagram.text label { fontSize := 12, fontFamily }
      |>.pad 12
      |>.filledFrame
        (fill := Color.white)
        (stroke := { color := Color.black, width := 1 })
        (cornerRadius := 6)
      |>.namedWithAnchors name


#doc (Manual) "精化和编译" =>
%%%
htmlSplit := .never
%%%

粗略地说，Lean对一个源文件的处理可以分为以下几个阶段：

: 解析

  解析器将字符序列转换为 {lean}`Syntax` 类型的语法树。
  Lean 的解析器是可扩展的，因此 {lean}`Syntax` 类型非常通用。

: 宏展开

  宏是用更基本的语法代替语法糖的转换。
  宏展开的输入和输出的类型均为 {lean}`Syntax`。

: 精化

  {deftech (key := "Lean elaborator") -normalize}[精化] 是将 Lean 面向用户的语法转换为其核心 类型论 的过程。
  这个核心理论要简单得多，使得可信的内核变得非常小。
  精化还生成用于 Lean 交互功能的元数据，例如证明状态或表达式类型，并将它们存储在侧表中。

: 内核正在检查

  Lean 的可信内核检查精化器的输出，以确保其遵循 类型论 的规则。

: 汇编

  编译器将详细的 Lean 代码转换为可以运行的可执行文件。


:::figure "The Lean Pipeline" (tag := "pipeline-overview")
```diagram
pipelineDiagram
```
:::


实际上，上述阶段并不严格地依次发生。
Lean 解析单个 {tech}[command]（顶级声明），对其进行详细说明，并执行任何必要的内核检查。
宏展开是精化的一部分；在翻译一段语法之前，精化器首先扩展最外层存在的任何宏。
宏语法可能保留在更深的层，但当精化器到达这些层时，它将扩展。
精化有多种：命令精化实现每个顶级命令的效果（例如声明 {tech}[归纳类型]、保存定义、求值表达式），而术语精化负责构造在许多命令中出现的术语（例如签名中的类型、定义的右侧或要计算的表达式）。
策略执行是术语精化的专业化。

详细说明命令时，Lean 的状态会发生变化。
新的定义或类型可能已保存以供将来使用，语法可能会扩展，或者无需明确限定即可引用的名称集可能已更改。
下一个命令在此更新的状态下被解析和详细说明，并且它本身更新后续命令的状态。

# 解析
%%%
tag := "parser"
%%%

Lean 的解析器是一个递归下降解析器，它使用基于 Pratt 解析 {citep pratt73}[] 的动态表来解析运算符优先级和关联性。
当语法明确时，解析器不需要回溯；在语法不明确的情况下，类似于 Packrat 解析中使用的记忆表可以避免指数爆炸。
解析器具有高度可扩展性：用户可以在任何命令中定义新语法，并且该语法在下一个命令中可用。
当前 {tech}[节范围] 中的开放命名空间也会影响使用哪些解析规则，因为仅当给定命名空间打开时，解析器扩展才可以设置为活动状态。

当遇到歧义时，选择最长的匹配解析。
如果没有唯一的最长匹配，则两个匹配解析都保存在语法树中的 {deftech}[选择节点] 中，稍后由精化器解析。
当解析器失败时，它返回一个 {lean}`Syntax.missing` 节点，允许错误恢复。

成功后，解析器会保存足够的信息来重建原始源文件。
不成功的解析可能会丢失无法解析的文件区域的一些信息。
{lean}`SourceInfo` 记录类型记录有关一段语法起源的信息，包括其源位置和周围的空白。
根据 {lean}`SourceInfo` 字段，{lean}`Syntax` 与源文件可以具有三种关系：
 * {lean}`SourceInfo.original` 表示语法值是由解析器直接生成的。
 * {lean}`SourceInfo.synthetic` 表示语法值是通过编程生成的，例如通过宏扩展器。尽管如此，合成语法仍可能被标记为_canonical_，在这种情况下，Lean 用户界面会将其视为用户编写的。合成语法用原始文件中的位置进行注释，但不包括前导或尾随空格。
 * {lean}`SourceInfo.none` 表示与文件没有关系。

解析器维护一个标记表，用于跟踪当前属于该语言的保留字。
定义新语法或打开命名空间可能会导致以前有效的标识符成为关键字。

Lean 语法中的每个产生式均已命名。
产品的名称称为 {deftech}_kind_。
这些语法类型很重要，因为它们是用于在精化器表中查找语法解释的关键。

{ref "language-extension"}[专门章节]中更详细地描述了语法扩展。

# 宏展开和精化
%%%
tag := "macro-and-elab"
%%%

解析完命令后，下一步就是详细说明它。
{deftech -normalize}_elaboration_ 的精确含义取决于所精化的内容：精化命令会影响 Lean 状态的变化，而精化术语会导致 Lean 的核心 类型论 中出现术语。
命令和术语的精化都可以是递归的，这既是因为诸如 {keywordOf Lean.Parser.Command.in}`in` 之类的命令组合器，也是因为术语可能包含其他术语。

命令和术语精化具有不同的功能。
命令精化可能会对环境产生副作用，并且它有权在 {lean}`IO` 中运行任意计算。
Lean {deftech}[环境] 包含从名称到定义的常见映射以及 {deftech}[环境扩展] 中定义的附加数据，这些数据是与环境关联的附加表；环境扩展用于跟踪有关 Lean 代码的大多数其他信息，包括 {tactic}`simp` 引理、自定义漂亮打印机以及编译器的中间表示等内部结构。
命令精化还维护一个消息日志，其中包含编译器的信息输出、警告和错误的内容、一组将元数据与原始语法关联起来的 {tech}[信息树]（用于交互功能，如显示证明状态、标识符完成和显示文档）、累积的调试跟踪、打开的 {tech}[节范围] 以及与宏展开。
术语精化可以修改除开放范围之外的所有这些字段。
此外，它还可以通过 Lean 简洁、友好的语法访问在核心语言中创建完全显式术语所需的所有机制，包括统一、类型类实例综合和类型检查。

术语和命令精化中的第一步都是宏展开。
有一个表将语法类型映射到宏实现；宏实现是将宏语法转换为新语法的一元函数。
宏保存在同一个表中，并在术语、命令、策略以及 Lean 的任何其他宏可扩展部分的同一个 monad 中执行。
如果宏返回的语法本身就是宏，则该语法将再次扩展 - 重复此过程，直到生成类型不是宏的语法，或者达到最大迭代次数，此时 Lean 会产生错误。
典型的宏处理其语法的一些外层，而保留一些子术语不变。
这意味着即使宏展开已完成，顶层以下的语法中仍可能残留有宏调用。
新的宏可以添加到宏表中。
{ref "macros"}[宏部分]中详细描述了定义新宏。

在宏展开之后，术语和命令精化器都会查阅将语法类型映射到精化过程的表。
术语精化器使用上面提到的非常强大的 monad 将语法和可选的预期类型映射到核心语言表达式。
命令精化器接受语法并且不返回任何值，但可能会对全局命令状态产生一元副作用。
虽然术语和命令精化器都可以访问 {lean}`IO`，但它们执行副作用的情况并不常见；例外情况包括与外部工具或求解器的交互。

可以扩展精化器表，以通过扩展表来启用术语和命令的新语法。
有关如何向 Lean 添加其他精化器的说明，请参阅 {ref "elaborators"}[有关精化器的部分]。
当命令或术语包含更多命令或术语时，它们会在嵌套语法上递归调用适当的精化器。
然后，该精化器将在从表中调用精化器之前扩展宏。
对于语法的给定“层”，虽然宏展开出现在精化之前，但宏展开和精化通常是交错的。

## 信息树
%%%
tag := "zh-elaboration-h003"
%%%

与 Lean 代码交互时，比简单地将其作为依赖项导入时需要更多信息。
例如，Lean 的交互式环境可用于查看所选表达式的类型、逐步完成证明的所有中间状态、查看文档以及突出显示绑定变量的所有出现。
在精化期间，交互使用 Lean 所需的信息存储在名为 {deftech}_info trees_ 的边表中。

```lean -show
open Lean.Elab (Info)
```


信息树将元数据与用户的原始语法相关联。
它们的树结构与语法的树结构紧密对应，尽管语法树中的给定节点可能有许多相应的信息树节点来记录其不同方面。
此元数据包括精化器以 Lean 核心语言表示的输出、给定点的活动证明状态、交互式标识符完成的建议等等。
元数据还可以任意扩展；构造函数 {lean}`Info.ofCustomInfo` 接受 {lean}`Dynamic` 类型。
这可用于添加自定义代码操作或其他用户界面扩展使用的信息。

# 内核
%%%
tag := "zh-elaboration-h004"
%%%

Lean 的可信 {deftech}_kernel_ 是核心 类型论 类型检查器的小型、强大的实现。
它不包括语法终止检查器，也不执行统一；通过将所有递归函数细化为原语 {tech}[recursors] 的使用来保证终止，并且预计精化器已经执行了统一。
在命令或术语精化器将新的归纳类型或定义添加到环境中之前，必须由内核检查它们，以防止精化中潜在的错误。

Lean 的内核是用 C++ 编写的。
[Rust](https://github.com/ammkrn/nanoda_lib) 和 [Lean](https://github.com/digama0/lean4lean) 中有独立的重新实现，并且 Lean 项目希望拥有尽可能多的实现，以便可以相互交叉检查。

内核实现的语言是构造微积分的一个版本，依值类型论 具有以下功能：
 * 全依值类型
 * 归纳定义的类型可以相互归纳或包括嵌套在其他归纳类型下的递归
 * {tech}[必然]，定义上证明无关，{tech}[命题]的扩展 {tech}[宇宙]
 * {tech}[谓词]，数据域的非累积层次结构
 * {ref "quotients"}[商类型] 具有定义的计算规则
 * 命题函数外延性{margin}[函数外延性是一个可以使用商类型证明的定理，但它是一个非常重要的推论，值得单独列出。]
 * 函数和乘积的定义 {tech (key := "η-equivalence")}[η-equality]
 * 宇宙多态定义
 * 一致性：不存在 {lean}`False` 类型的无公理封闭项

```lean -show -keep
-- Test definitional eta for structures
structure A where
  x : Nat
  y : Int
example (a : A) : ⟨a.x, a.y⟩ = a := rfl
set_option linter.unusedVariables false in
inductive B where
  | mk (x : Nat) (y : Int) : B
example (b : B) : ⟨b.1, b.2⟩ = b := rfl
/--
error: Type mismatch
  rfl
has type
  ?m.836 = ?m.836
but is expected to have type
  e1 = e2
-/
#check_msgs in
example (e1 e2 : Empty) : e1 = e2 := rfl
```

该理论足够丰富，可以表达前沿的研究数学，但又足够简单，可以进行小型、高效的实现。
明确证明条款的存在使得实施独立的证明检查器变得可行，从而增强了我们的信心。
由{citet carneiro19}[]和{citet ullrich23}[]详细描述。

Lean 的 类型论 不具有主题还原功能，定义等价 不一定具有传递性，并且有可能使类型检查器无法终止。
这些元理论属性都不会在实践中引起问题——传递性失败极其罕见，而且据我们所知，除非专门编写代码来执行它，否则不会发生非终止。
最重要的是，逻辑健全性不受影响。
在实践中，明显的不终止与足够慢的程序是无法区分的。后者是在野外观察到的原因。
这些元理论性质是具有非谓性、计算商类型、定义证明无关性和命题外延性的结果；这些功能对于支持普通数学实践和实现自动化都非常有价值。

# 精化结果
%%%
tag := "elaboration-results"
%%%

Lean 的核心 类型论 不包括模式匹配或递归定义。
相反，它提供了低级 {tech}[recursors]，可用于实现大小写区分和原始递归。
因此，精化器必须将使用模式匹配和递归的定义转换为使用递归的定义。{margin}[有关递归定义的精化的更多详细信息，请参阅该主题的 {ref "recursive-definitions"}[专用部分]。]
此转换还证明了该函数对于所有潜在参数都终止，因为所有可以转换为递归器的函数也会终止。

到递归器的转换分两个阶段进行：在精化期间，模式匹配的使用被对 {deftech}_辅助匹配函数_（也称为 {deftech}_matcher 函数_）的调用所取代，这些函数实现了代码中出现的特定大小写区分。
这些辅助函数本身是使用递归器定义的，尽管它们没有利用递归器实际实现递归行为的能力。{margin}[它们使用 {ref "recursor-elaboration-helpers"}[关于递归器和精化的部分]中描述的 `casesOn` 构造的变体，专门用于减少代码大小。]
因此，术语精化器返回核心语言术语，其中模式匹配已替换为使用实现大小写区分的特殊函数，但这些术语仍可能包含所定义函数的递归出现。
仍包含递归但已详细精化为核心语言的定义称为 {deftech}[预定义]。
要查看 Lean 输出中的辅助模式匹配功能，请将选项 {option}`pp.match` 设置为 {lean}`false`。

{optionDocs pp.match}


```lean -show -keep
def third_of_five : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
set_option pp.match false

/--
info: @[reducible] def third_of_five._sparseCasesOn_1.{u_1, u} : {α : Type u} →
  {motive : List α → Sort u_1} →
    (t : List α) →
      ((head : α) → (tail : List α) → motive (head :: tail)) → (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t :=
fun {α} {motive} t cons =>
  List.rec (motive := fun t => (Nat.hasNotBit 2 t.ctorIdx → motive t) → motive t) (fun «else» => «else» ⋯)
    (fun head tail tail_ih «else» => cons head tail) t
-/
#check_msgs in
#print third_of_five._sparseCasesOn_1

/--
info: third_of_five.eq_def.{u_1} {α : Type u_1} (x✝ : List α) :
  third_of_five x✝ =
    third_of_five.match_1 (fun x => Option α) x✝ (fun head head_1 x head_2 head_3 => some x) fun x => none
-/
#check_msgs in
#check third_of_five.eq_def

/--
info: @[implicit_reducible] def third_of_five.match_1.{u_1, u_2} : {α : Type u_1} →
  (motive : List α → Sort u_2) →
    (x : List α) →
      ((head head_1 x head_2 head_3 : α) → motive [head, head_1, x, head_2, head_3]) →
        ((x : List α) → motive x) → motive x :=
fun {α} motive x h_1 h_2 =>
  third_of_five._sparseCasesOn_1 x
    (fun head tail =>
      third_of_five._sparseCasesOn_1 tail
        (fun head_1 tail =>
          third_of_five._sparseCasesOn_1 tail
            (fun head_2 tail =>
              third_of_five._sparseCasesOn_1 tail
                (fun head_3 tail =>
                  third_of_five._sparseCasesOn_1 tail
                    (fun head_4 tail =>
                      third_of_five._sparseCasesOn_2 tail (h_1 head head_1 head_2 head_3 head_4) fun h =>
                        h_2 (head :: head_1 :: head_2 :: head_3 :: head_4 :: tail))
                    fun h => h_2 (head :: head_1 :: head_2 :: head_3 :: tail))
                fun h => h_2 (head :: head_1 :: head_2 :: tail))
            fun h => h_2 (head :: head_1 :: tail))
        fun h => h_2 (head :: tail))
    fun h => h_2 x
-/
#check_msgs in
#print third_of_five.match_1
```

:::paragraph
然后预定义被发送到编译器和内核。
编译器按原样接收预定义，递归完好无损。
另一方面，发送到内核的版本会经历第二次转换，用 {ref "structural-recursion"}[递归器的使用]、{ref "well-founded-recursion"}[良基递归] 或 {ref "partial-fixpoint"}[部分定点递归] 替换显式递归。
这种分裂有以下三个原因：
 * 编译器可以编译 {ref "partial-unsafe"}[`partial` 函数]，内核将其视为不透明常量以进行推理。
 * 编译器还可以编译完全绕过内核的 {ref "partial-unsafe"}[`unsafe` 函数]。
 * 转换为递归器不一定保留程序员期望的成本模型，特别是惰性与严格性，但编译后的代码必须具有可预测的性能。
   用于证明递归定义合理性的其他策略会导致内部术语与编写的程序相差甚远。

编译器将中间表示存储在环境扩展中。
:::

对于直接结构递归函数，翻译将使用类型的递归器。
这些函数在内核中运行时往往相对有效，它们的定义方程定义明确，并且易于理解。
使用类型的递归器无法捕获的其他递归模式的函数使用 {tech}[良基递归] 进行转换，这是结构递归，证明某些 {tech}[measure] 在每次递归调用时都会减少，或者使用 {ref "partial-fixpoint"}[partial fixpoints]，逻辑上捕获通过诉诸领域理论构造来至少部分地描述函数的规范。
Lean 可以自动导出许多终止证明，但有些需要手动证明。
良基递归更灵活，但由于证明项表明测度减少，并且它们的定义方程可能仅在命题上成立，因此生成的函数在内核中执行速度通常较慢。
为了向通过结构和良基递归定义的函数提供统一的接口并检查其自身的正确性，精化器证明了将函数与其原始定义相关联的 {deftech}[方程引理]。
在函数的命名空间中，`eq_unfold` 将函数直接与其定义相关联，`eq_def` 将其与实例化隐式参数后的定义相关联，$`N` 引理 `eq_N` 将其模式匹配的每种情况与相应的右侧相关联，包括表明未采用较早分支的充分假设。

::::keepEnv
:::example "Equational Lemmas"
给出 {lean}`thirdOfFive` 的定义：
```lean
def thirdOfFive : List α → Option α
  | [_, _, x, _, _] => some x
  | _ => none
```
生成将 {lean}`thirdOfFive` 与其定义相关的等式引理。

{lean}`thirdOfFive.eq_unfold` 指出，当不提供参数时，它可以展开为其原始定义：
```signature
thirdOfFive.eq_unfold.{u_1} :
  @thirdOfFive.{u_1} = fun {α : Type u_1} x =>
    match x with
    | [head, head_1, x, head_2, head_3] => some x
    | x => none
```

{lean}`thirdOfFive.eq_def` 声明它在应用于参数时与其定义匹配：
```signature
thirdOfFive.eq_def.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    thirdOfFive x =
      match x with
      | [head, head_1, x, head_2, head_3] => some x
      | x => none
```

{lean}`thirdOfFive.eq_1` 表明其第一个定义方程成立：
```signature
thirdOfFive.eq_1.{u} {α : Type u}
    (head head_1 x head_2 head_3 : α) :
  thirdOfFive [head, head_1, x, head_2, head_3] = some x
```

{lean}`thirdOfFive.eq_2` 表明其第二个定义方程成立：
```signature
thirdOfFive.eq_2.{u_1} {α : Type u_1} :
  ∀ (x : List α),
    (∀ (head head_1 x_1 head_2 head_3 : α),
      x = [head, head_1, x_1, head_2, head_3] → False) →
    thirdOfFive x = none
```
最后的引理 {lean}`thirdOfFive.eq_2` 包括第一个分支无法匹配的前提（即列表不正好有五个元素）。
:::
::::

::::keepEnv
:::example "Recursive Equational Lemmas"
给出 {lean}`everyOther` 的定义：
```lean
def everyOther : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: everyOther xs
```

生成的方程引理将 {lean}`everyOther` 的基于递归的实现与其原始递归定义联系起来。

{lean}`everyOther.eq_unfold` 声明不带参数的 `everyOther` 等于其展开：
```signature
everyOther.eq_unfold.{u} :
  @everyOther.{u} = fun {α} x =>
    match x with
    | [] => []
    | [x] => [x]
    | x :: _ :: xs => x :: everyOther xs
```

{lean}`everyOther.eq_def` 声明 `everyOther` 应用于参数时等于其定义：
```signature
everyOther.eq_def.{u} {α : Type u} :
  ∀ (x : List α),
    everyOther x =
      match x with
      | [] => []
      | [x] => [x]
      | x :: _ :: xs => x :: everyOther xs
```

{lean}`everyOther.eq_1` 演示其第一个模式：
```signature
everyOther.eq_1.{u} {α : Type u} : everyOther [] = ([] : List α)
```

{lean}`everyOther.eq_2` 演示了其第二种模式：
```signature
everyOther.eq_2.{u} {α : Type u} (x : α) : everyOther [x] = [x]
```

{lean}`everyOther.eq_3` 展示了其最终模式：
```signature
everyOther.eq_3.{u} {α : Type u} (x y : α) (xs : List α) :
  everyOther (x :: y :: xs) = x :: everyOther xs
```

因为模式不重叠，所以对于等式引理，不需要关于先前模式不匹配的假设。
:::
::::

详细说明模块后，使用内核检查对环境的每个添加，模块对全局环境（包括扩展）所做的更改将序列化到 {deftech}[`.olean` 文件]。
在这些文件中，Lean 项和值的表示方式与内存中的一样；因此该文件可以直接进行内存映射。
导致 Lean 添加到环境的所有代码路径都涉及首先由内核检查的新类型或定义。
然而，Lean 是一个非常开放、灵活的系统。
为了防止编写不当的元程序跳过障碍向环境添加未经检查的值的可能性，可以使用单独的工具 `lean4checker` 来验证 `.olean` 文件中的整个环境是否满足内核。

除了 `.olean` 文件之外，精化器还会生成 `.ilean` 文件，该文件是语言服务器使用的索引。
该文件包含与模块交互工作而无需完全加载模块所需的信息，例如定义的源位置。
`.ilean` 文件的内容是实现细节，可能会在任何版本中更改。

最后，调用编译器将存储在其环境扩展中的函数的中间表示转换为 C 代码。
为每个 Lean 模块生成一个 C 文件；然后使用捆绑的 C 编译器将它们编译为本机代码。
如果在构建配置中设置了 `precompileModules` 选项，则该本机代码可以由 Lean 动态加载和调用；否则，将使用口译员。
对于大多数工作负载，编译的开销大于通过避免解释器节省的时间，但某些工作负载可以通过预编译策略、语言扩展或 Lean 的其他扩展来显着加快速度。


# 初始化
%%%
tag := "initialization"
%%%

启动之前，精化器必须正确初始化。
Lean 本身包含 {deftech}[初始化] 代码，必须运行该代码才能正确构造编译器的初始状态；此代码在加载任何模块之前以及调用精化器之前运行。
此外，每个依赖项本身都可以贡献初始化代码，例如用于设置环境扩展。
在内部，每个环境扩展都被分配到一个数组中的唯一索引，并且该数组的大小等于注册的环境扩展的数量，因此必须知道扩展的数量才能正确分配环境。

运行 Lean 自己的内置初始化程序后，将解析模块的标头并将依赖项的 `.olean` 文件加载到内存中。
构建了一个“预环境”，其中包含依赖项环境的联合。
接下来，在解释器中执行依赖项指定的所有初始化代码。
此时，环境扩展的数量已知，因此可以将预环境重新分配到具有正确大小的扩展数组的环境结构中。


:::syntax command (title := "Initialization Blocks")
{keywordOf Lean.Parser.Command.initialize}`initialize` 块将代码添加到模块的初始化程序中。
{keywordOf Lean.Parser.Command.initialize}`initialize` 块的内容被视为 {lean}`IO` monad 中 {keywordOf Lean.Parser.Term.do}`do` 块的内容。

有时，初始化只需要通过副作用来扩展内部数据结构。
在这种情况下，内容的类型预计为 {lean}`IO Unit`：
```grammar
initialize
  $cmd*
```

初始化还可用于构造包含对内部状态的引用的值，例如由环境扩展支持的属性。
在这种形式的 {keywordOf Lean.Parser.Command.initialize}`initialize` 中，初始化应返回 {lean}`IO` monad 中指定的类型。
```grammar
initialize $x:ident : $t:term ←
  $cmd*
```
:::


:::syntax command (title := "Compiler-Internal Initializers")
Lean 的内部结构还定义了初始化期间必须运行的代码。
但是，由于 Lean 是引导编译器，因此必须特别注意定义为 Lean 本身一部分的初始化程序，并且 Lean 自己的初始化程序必须在导入或加载 _any_ 模块之前运行。
这些初始值设定项是使用 {keywordOf Lean.Parser.Command.initialize}`builtin_initialize` 指定的，不应在编译器实现之外使用。

```grammar
builtin_initialize
  $cmd*
```
```grammar
builtin_initialize $x:ident : $t:term ←
  $cmd*
```
:::
