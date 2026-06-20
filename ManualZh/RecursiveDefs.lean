/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.RecursiveDefs.Structural
import ManualZh.RecursiveDefs.WF
import ManualZh.RecursiveDefs.PartialFixpoint
import ManualZh.RecursiveDefs.CoinductivePredicates

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode



#doc (Manual) "递归定义" =>
%%%
file := "Recursive-Definitions"
tag := "recursive-definitions"
%%%

允许任意递归函数定义会使 Lean 的逻辑不一致。
一般递归使得编写循环证明成为可能：“{tech (key := "proposition")}[命题] $`P` 为真，因为命题 $`P` 为真”。
在证明之外，可以将无限循环分配为类型 {name}`Empty`，它可以与 {keywordOf Lean.Parser.Term.nomatch}`nomatch` 或 {name Empty.rec}`Empty.rec` 一起使用来证明任何定理。

完全禁止递归函数定义将使 Lean 的用处大大降低：{tech (key := "inductive types")}[归纳类型] 是定义谓词和数据的关键，并且它们具有递归结构。
此外，大多数有用的递归函数不会威胁到健全性，并且无限循环通常表明定义中的错误而不是有意的行为。
Lean 要求安全地定义每个递归函数，而不是禁止递归函数。
在详细精化递归定义时，Lean精化器还提供了所定义的函数是安全的理由。{margin}[精化概述中有关 {ref "elaboration-results"}[精化器的输出]的部分将上下文背景化精化的精化器整体上下文中的递归定义。]

可以定义六种主要的递归函数：

: 结构递归函数

  结构递归函数采用一个参数，以便该函数仅对所述参数的严格子组件进行递归调用。{margin}[严格来说，类型为 {tech (key := "indexed families")}[索引族] 的参数与其索引分组在一起，整个集合被视为一个单元。]
  精化器将递归转换为参数的 {tech}[recursor] 的使用。
  因为递归器的每次类型正确使用都保证避免无限回归，所以这个翻译是函数终止的证据。
  通过递归器定义的函数的应用程序在定义上等于递归的结果，并且通常在内核内相对有效。

: 对有根据的关系进行递归

  很多函数也很难转换为结构递归；例如，函数可能会终止，因为数组索引和数组大小之间的差异随着索引的增加而减小，但 {name}`Nat.rec` 不适用，因为增加的索引是函数的参数。
  此处，终止的 {tech}[measure] 在每次递归调用时都会减少，但该度量本身并不是函数的参数。
  在这些情况下，{tech (key := "well-founded recursion")}[良基递归] 可用于定义函数。
  良基递归是一种将具有递减测度的递归函数系统地转换为递归函数的技术，并证明每个测度递减序列最终都会以最小值终止。
  通过良基递归定义的函数的应用程序不一定在定义上等于它们的返回值，但这种等式可以作为命题来证明。
  即使存在定义等式，这些函数的计算速度通常也很慢，因为它们需要减少通常非常大的证明项。

: 作为部分不动点的递归函数

  函数的定义可以理解为指定其行为的方程。
  在某些情况下，即使递归函数不一定对所有输入都终止，也可以证明满足此规范的函数的存在。
  该策略甚至适用于函数定义不一定针对所有输入终止的某些情况。
  这些偏函数作为这些方程的固定点出现，称为 {tech (key := "partial fixpoints")}_部分固定点_。

  特别是，任何返回类型位于某些 monad 中的函数（例如 {name}`Option`）都可以使用此策略来定义。
  Lean 为这些一元函数生成附加的部分正确性定理。
  与良基递归一样，定义为部分不动点的函数的应用在定义上并不等于其返回值，但 Lean 生成的定理在命题上将函数等同于其展开以及其定义中指定的归约行为。

: 作为固定点的共归纳和归纳谓词

  递归 {lean}`Prop` 值函数可以定义为完整格上单调算子的最大或最小不动点。
  使用 {keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 或 {keywordOf Lean.Parser.Command.declaration}`coinductive` 命令定义的共归纳谓词描述潜在的无限行为，例如无限序列或互模拟。
  使用 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 定义的归纳谓词提供了标准归纳类型的替代方案，该替代方案与混合归纳-共归纳互块兼容。

: 具有非空余域的偏函数

  对于许多应用程序来说，推理某些功能的实现并不重要。
  递归函数可能仅用作证明自动化步骤实现的一部分，或者它可能是一个永远不会被正式证明正确的普通程序。
  在这些情况下，Lean内核不需要定义或命题等式来维持定义；保持健全性就足够了。
  标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数被内核视为不透明常量，既不展开也不还原。
  健全性所需要的只是它们的返回类型是可居住的。
  偏函数仍然可以像往常一样在编译代码中使用，并且它们可以出现在命题和证明中；他们的方程理论在Lean的逻辑中简直是非常薄弱。

: 不安全的递归定义

  不安全定义没有部分定义的任何限制。
  他们可以自由地使用一般递归，并且可以使用 Lean 的功能来打破有关其方程理论的假设，例如用于转换的原语 ({name}`unsafeCast`)、检查指针相等性 ({name}`ptrAddrUnsafe`) 以及观察 {tech (key := "reference counts")}[引用计数] ({name}`isExclusiveUnsafe`)。
  但是，任何引用不安全定义的声明本身都必须标记为 {keywordOf Lean.Parser.Command.declaration}`unsafe`，以明确何时无法保证逻辑健全性。
  不安全操作可用于将其他函数的实现替换为编译代码中更有效的变体，而内核仍使用原始定义。
  被替换的函数可能是不透明的，这导致函数名称在逻辑中具有琐碎的方程理论，或者它可能是普通函数，在这种情况下该函数在逻辑中使用。
  请谨慎使用此功能：逻辑健全性不会受到威胁，但如果不安全的实现不正确，则用 Lean 编写的程序的行为可能会偏离其经过验证的逻辑模型。

:::TODO

提供所有策略及其属性概述的表格

:::

如 {ref "elaboration-results"}[精化器输出概述]中所述，递归函数的精化分两个阶段进行：
 1. 该定义的详细说明就像 Lean 的核心 类型论 具有递归定义一样。
    除了使用递归之外，这个临时定义还得到了充分的精化。
    编译器根据这些临时定义生成代码。

 2. 终止分析尝试使用五种技术来验证 Lean 的内核的功能。
    如果定义标记为 {keywordOf Lean.Parser.Command.declaration}`unsafe` 或 {keywordOf Lean.Parser.Command.declaration}`partial`，则使用该技术。
    如果存在显式 {keywordOf Lean.Parser.Command.declaration}`termination_by`、{keywordOf Lean.Parser.Command.declaration}`partial_fixpoint`、{keywordOf Lean.Parser.Command.declaration}`coinductive_fixpoint` 或 {keywordOf Lean.Parser.Command.declaration}`inductive_fixpoint` 子句，则所指示的技术是唯一尝试的一种技术。
    如果不存在此类子句，则精化器执行搜索，测试函数的每个参数作为结构递归的候选者，并尝试查找具有在每次递归调用时减少的有充分依据的关系的度量。

本节描述管理递归函数的规则。
在描述了相互递归之后，指定了五种递归定义中的每一种，以及每种递归定义的推理能力和灵活性之间的权衡。

# 相互递归
%%%
file := "Mutual-Recursion"
tag := "mutual-syntax"
%%%

正如递归定义是在定义主体中提及所定义的名称一样，{deftech}_mutually recursive_ 定义是可以递归或互相提及的定义。
要在多个声明之间使用相互递归，必须将它们放置在 {deftech (key := "mutual block")}[相互块] 中。

:::syntax command (title := "Mutual Declaration Blocks")
相互递归的一般语法是：

```grammar
mutual
  $[$declaration:declaration]*
end
```
其中声明必须是定义或定理。
:::

相互块中的声明不在彼此签名的范围内，但在彼此主体的范围内。
即使名称不在签名范围内，它们也不会作为自动绑定隐式参数插入。

:::example "Mutual Block Scope"
相互块中定义的名称不在彼此签名的范围内。

```lean +error (name := mutScope) -keep
mutual
  abbrev NaturalNum : Type := Nat
  def n : NaturalNum := 5
end
```
```leanOutput mutScope
Unknown identifier `NaturalNum`
```

没有相互块，定义成功：
```lean
abbrev NaturalNum : Type := Nat
def n : NaturalNum := 5
```
:::

:::example "Mutual Block Scope and Automatic Implicit Parameters"
相互块中定义的名称不在彼此签名的范围内。
尽管如此，它们不能用作自动隐式参数：

```lean +error (name := mutScopeTwo) -keep
mutual
  abbrev α : Type := Nat
  def identity (x : α) : α := x
end
```
```leanOutput mutScopeTwo
Unknown identifier `α`
```

使用不同的名称，会自动添加隐式参数：
```lean
mutual
  abbrev α : Type := Nat
  def identity (x : β) : β := x
end
```
:::

详细说明递归定义总是以交互块的粒度进行，就好像每个声明周围都有一个单例交互块，而该声明本身不是该块的一部分。
通过 {keywordOf Lean.Parser.Term.letrec}`let rec` 引入的本地定义和
 {keywordOf Lean.Parser.Command.declaration}`where` 脱离其上下文，根据需要引入捕获的自由变量的参数，并将它们视为 {keywordOf Lean.Parser.Command.mutual}`mutual` 块内的单独定义。 {TODO}[在此处或术语部分更详细地解释此机制。]
因此，{keywordOf Lean.Parser.Command.declaration}`where` 块中定义的帮助器可以相互使用相互递归，也可以与它们所在的定义使用相互递归，但它们可能不会在类型签名中相互提及。

在精化的第一步之后（其中定义仍然是递归的），并且在使用上述技术转换递归之前，Lean 在相互块中的定义中识别实际（相互）递归派 {TODO}[定义这个术语，它很有用]，并按依赖顺序单独处理它们。

{include 0 ManualZh.RecursiveDefs.Structural}

{include 0 ManualZh.RecursiveDefs.WF}

{include 0 ManualZh.RecursiveDefs.PartialFixpoint}

{include 0 ManualZh.RecursiveDefs.CoinductivePredicates}

# 不完整和不安全的定义
%%%
file := "Partial-and-Unsafe-Definitions"
tag := "partial-unsafe"
%%%


While most Lean functions can be reasoned about in Lean's 类型论 as well as compiled and run, definitions marked {keyword}`partial` or {keyword}`unsafe` cannot be meaningfully reasoned about.
From the perspective of the logic, {keyword}`partial` functions are opaque constants, and theorems that refer to {keyword}`unsafe` definitions are summarily rejected.
作为无法使用这些函数进行推理的代价，对它们的要求要少得多； this can make it possible to write programs that would be impractical or cost-prohibitive to prove anything about, while not giving up formal reasoning for the rest.
In essence, the {keyword}`partial` subset of Lean is a traditional functional programming language that is nonetheless deeply integrated with the theorem proving features, and the {keyword}`unsafe` subset features the ability to break Lean's runtime invariants in certain rare situations, at the cost of less integration with Lean's theorem-proving特点。
类似地，{keyword}`noncomputable` 定义可能使用在程序中没有意义但在逻辑中有意义的功能。

## 部分功能
%%%
file := "Partial-Functions"
tag := "partial-functions"
%%%

{keyword}`partial` 修饰符只能应用于函数定义。
不需要部分函数来证明终止，并且 Lean 不会尝试这样做。
这些函数是“部分”的，因为它们不一定指定从域的每个元素到共域元素的映射，因为它们可能无法终止域的某些或所有元素。
它们被详细精化为包含显式递归的 {tech (key := "pre-definitions")}[预定义]，并使用内核进行类型检查；然而，它们随后被逻辑视为不透明常量。

函数的返回类型必须是可居住的；这确保了稳健性。
否则，部分函数可能具有 {lean}`Unit → Empty` 等类型。
与{name}`Empty.elim`一起，这样的函数的存在可以用来证明{lean}`False`，即使它不减少。

对于部分定义，内核负责以下内容：
* 它确保预定义的类型确实是格式良好的类型。
* 它检查预定义的类型是否为函数类型。
* 它确保函数的共域被要求的 {lean}`Nonempty` 或 {lean}`Inhabited` 实例占据。
* 如果 Lean 具有递归定义，它会检查生成的术语类型是否正确。

即使递归定义不是内核的 类型论 的一部分，内核仍可用于检查定义主体是否具有正确的类型。
这与其他函数式语言的工作方式相同：通过在定义已与其类型关联的环境中检查主体来对递归的使用进行类型检查。
确保进行类型检查后，主体将被丢弃，内核仅保留不透明常量。
与所有 Lean 函数一样，编译器从详细的 {tech (key := "pre-definition")}[预定义] 生成代码。

即使内核未展开部分函数，​​仍然可以推理调用它们的其他函数，只要该推理不依赖于部分函数本身的实现即可。

:::example "Partial Functions in Proofs"
递归函数 {name}`nextPrime` 通过反复测试候选数来低效地计算给定数之后的下一个素数。
因为素数有无穷多个，所以它总是终止；然而，提出这个证明并非易事。
因此它被标记为 {keyword}`partial`。

```lean
def isPrime (n : Nat) : Bool := Id.run do
  for i in [2:n] do
    if i * i > n then return true
    if n % i = 0 then return false
  return true

partial def nextPrime (n : Nat) : Nat :=
  let n := n + 1
  if isPrime n then n else nextPrime n
```

尽管如此，还是可以证明以下两个函数是相等的：
```lean
def answerUser (n : Nat) : String :=
  s!"The next prime is {nextPrime n}"

def answerOtherUser (n : Nat) : String :=
  " ".intercalate [
    "The",
    "next",
    "prime",
    "is",
    toString (nextPrime n)
  ]
```
事实上，证明是由 {tactic}`rfl` 提供的：
```lean
theorem answer_eq_other : answerUser = answerOtherUser := by
  rfl
```
:::

## 不安全的定义
%%%
file := "Unsafe-Definitions"
tag := "unsafe"
%%%

不安全定义的保障措施比部分函数还要少。
它们的共域不需要被占用，它们不限于函数定义，并且它们可以访问 Lean 的特征，这些特征可能违反内部不变量或破坏抽象。
因此，它们根本不能用作数学推理的一部分。

虽然部分函数被 类型论 视为不透明常量，但不安全定义只能从其他不安全定义引用。
因此，任何调用不安全函数的函数本身必定是不安全的。
不允许将定理宣布为不安全。

除了不受限制地使用递归之外，不安全函数还可以从一种类型转换为另一种类型、检查两个值是否是内存中的同一对象、检索指针值以及从其他纯代码运行 {lean}`IO` 操作。
使用这些运算符需要彻底了解 Lean 实现。

{docstring unsafeCast}

{docstring ptrEq +allowMissing}

{docstring ptrEqList +allowMissing}

{docstring ptrAddrUnsafe +allowMissing}

{docstring isExclusiveUnsafe}

{docstring unsafeIO}

{docstring unsafeEIO}

{docstring unsafeBaseIO}


通常，不安全运算符用于编写利用低级细节的快速代码。
正如 Lean 代码可以在运行时通过 FFI 替换为 C 代码一样，{TODO}[xref] 安全 Lean 代码可以替换为运行时程序的不安全 Lean 代码。
这是通过将 {attr}`implemented_by` 属性添加到要替换的函数（通常是 {keyword}`opaque` 定义）来完成的。
虽然这不会威胁到 Lean 作为逻辑的健全性，因为要替换的常量已经由内核检查过，并且不安全的替换仅在运行时代码中使用，但它仍然存在风险。
C 代码和不安全代码都可能执行任意副作用。

:::syntax attr (title := "Replacing Run-Time Implementations")
{attr}`implemented_by` 属性指示编译器在编译代码中将一个常量替换为另一个常量。
替换常数可能不安全。
```grammar
implemented_by $_:ident
```
:::

:::example "Checking Equality with Pointers"

通常，{lean}`BEq` 实例的相等谓词必须完全遍历其两个参数以确定它们是否相等。
如果它们实际上是内存中的同一个对象，那么这确实是浪费。
可以在遍历之前使用指针相等测试来捕获这种情况。

所比较的类型是 {name}`Tree`，一种二叉树类型。
```lean
inductive Tree α where
  | empty
  | branch (left : Tree α) (val : α) (right : Tree α)
```

不安全函数可以使用指针相等来更快地终止结构相等测试，当指针相等失败时回退到结构检查。
```lean
unsafe def Tree.fastBEq [BEq α] (t1 t2 : Tree α) : Bool :=
  if ptrEq t1 t2 then
    true
  else
    match t1, t2 with
    | .empty, .empty => true
    | .branch l1 x r1, .branch l2 y r2 =>
      if ptrEq x y || x == y then
        l1.fastBEq l2 && r1.fastBEq r2
      else false
    | _, _ => false
```

不透明定义上的 {attr}`implemented_by` 属性连接了安全和不安全代码的世界。
```lean
@[implemented_by Tree.fastBEq]
opaque Tree.beq [BEq α] (t1 t2 : Tree α) : Bool

instance [BEq α] : BEq (Tree α) where
  beq := Tree.beq
```
:::

::::example "Taking Advantage of Run-Time Representations"

由于 {name}`Fin` 与其基础 {name}`Nat` 的表示方式相同，因此可以用 {name}`unsafeCast` 替换 {lean}`List.map Fin.val`，以避免实际上不执行任何操作的线性时间遍历：
```lean
unsafe def unFinImpl (xs : List (Fin n)) : List Nat :=
  unsafeCast xs

@[implemented_by unFinImpl]
def unFin (xs : List (Fin n)) : List Nat :=
  xs.map Fin.val
```

:::paragraph
从 Lean内核的角度来看，{lean}`unFin` 是使用 {name}`List.map` 定义的：
```lean
theorem unFin_length_eq_length {xs : List (Fin n)} :
    (unFin xs).length = xs.length := by
  simp [unFin]
```
在编译后的代码中，没有对列表的遍历。
:::

这种替换是有风险的：证明和编译代码之间的对应关系完全取决于两个实现的等价性，而这在 Lean 中无法证明。
该对应关系依赖于 Lean 的实现细节。
这些“逃生舱口”应该非常小心地使用。
::::

# 控制减少
%%%
file := "Controlling-Reduction"
tag := "reducibility"
htmlSplit := .never
%%%

在检查校样和程序时，Lean 会考虑 {deftech}_reducibility_（也称为_transparency_）。
定义的可归约性控制在精化和证明执行期间展开它的上下文。

可还原性有四个级别：

: {deftech (key := "Irreducible")}[不可约]

  不可约定义在精化期间根本没有展开。
  通过应用 {attr}`irreducible` 属性可以使定义变得不可约。

: {deftech (key := "Semireducible")}[半还原]

  半简化定义不会通过潜在昂贵的自动化（例如类型类实例合成或 {tactic}`simp`）展开，但它们会在检查 定义等价 和解析 {tech (key := "generalized field notation")}[广义字段表示法] 时展开。
  {keywordOf Lean.Parser.Command.declaration}`def` 命令通常创建半可简化定义，除非使用属性指定了不同的可简化级别；但是，默认情况下，使用 {tech (key := "well-founded recursion")}[良基递归] 的定义是不可约的。

: {deftech (key := "Implicit reducible")}[隐式可约]

  隐式可约定义在类型类 {tech (key := "synthesis")}[实例综​​合] 期间以及检查函数隐式参数的 {tech (key := "definitional equality")}[定义等价] 期间展开。
  这包括普通 {tech (key := "implicit")}[隐式] 参数、{tech (key := "instance implicit")}[实例隐式] 参数和 {tech (key := "strict implicit")}[严格隐式] 参数。
  所有类型类实例都应该是实例可约简的或可约简的，就像出现在隐式参数类型中并且旨在约简的定义一样。

: {deftech (key := "Reducible")}[可还原]

  可简化的定义基本上随需随处展开。
  Type 类实例综合、定义等价 检查以及语言的其余部分将定义本质上视为缩写。
  这是 {keywordOf Lean.Parser.Command.declaration}`abbrev` 命令应用的设置。

:::example "Reducibility and Instance Synthesis"
{lean}`String` 的这三个别名分别是可约、半约和不可约。
```lean
abbrev Phrase := String

def Clause := String

@[irreducible]
def Utterance := String
```

可约化和半约化别名在精化器的 定义等价 检查期间展开，导致它们被视为等同于 {lean}`String`：
```lean
def hello : Phrase := "Hello"

def goodMorning : Clause := "Good morning"
```
另一方面，不可约别名被拒绝作为字符串类型，因为精化器的 定义等价 测试不会展开它：
```lean +error (name := irred)
def goodEvening : Utterance := "Good evening"
```
```leanOutput irred
Type mismatch
  "Good evening"
has type
  String
but is expected to have type
  Utterance
```

由于 {lean}`Phrase` 是可约化的，因此 {inst}`ToString String` 实例可以用作 {inst}`ToString Phrase` 实例：
```lean
#synth ToString Phrase
```

但是，{lean}`Clause` 是半可约的，因此不能使用 {inst}`ToString String` 实例：
```lean +error (name := toStringClause)
#synth ToString Clause
```
```leanOutput toStringClause
failed to synthesize
  ToString Clause

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

可以通过创建减少为 {lean}`ToString String` 实例的 {lean}`ToString Clause` 实例来显式启用该实例。
此示例之所以有效，是因为在检查 定义等价 时展开了半简化定义：
```lean
instance : ToString Clause := inferInstanceAs (ToString String)
```
:::


:::example "Reducibility and Generalized Field Notation"
{tech (key := "Generalized field notation")}[通用字段表示法] 在搜索匹配名称时展开可简化和半可简化声明。
给定 {name}`List` 的半简化别名 {name}`Sequence`：
```lean
def Sequence := List

def Sequence.ofList (xs : List α) : Sequence α := xs
```
通用字段表示法允许从 {lean}`Sequence Nat` 类型的术语访问 {name}`List.reverse`。
```lean
#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```

然而，声明 {name}`Sequence` 不可约会阻止展开：
```lean +error (name := irredSeq)
attribute [irreducible] Sequence

#check let xs : Sequence Nat := .ofList [1,2,3]; xs.reverse
```
```leanOutput irredSeq
Invalid field `reverse`: The environment does not contain `Sequence.reverse`, so it is not possible to project the field `reverse` from an expression
  xs
of type `Sequence Nat`
```
:::

:::syntax attr (title := "Reducibility Annotations")
可以使用四个可归约属性之一来设置定义的可归约性：

```grammar
reducible
```
```grammar
implicit_reducible
```
```grammar
semireducible
```
```grammar
irreducible
```
这些属性只能在与正在修改的定义相同的文件中全局应用，但它们可以 {keywordOf attrInst (parser := Lean.Parser.Term.attrKind)}`local`ly 应用到任何地方。
:::

## 还原性和策略
%%%
file := "Reducibility-and-Tactics"
tag := "zh-recursivedefs-h006"
%%%

策略{tactic}`with_reducible`、{tactic}`with_reducible_and_instances` 和 {tactic}`with_unfolding_all` 控制大多数策略展开的定义。

:::example "Reducibility and Tactics"
函数 {lean}`plus`、{lean}`sum` 和 {lean}`tally` 都是 {lean}`Nat.add` 的同义词，分别是可约、半约和不可约：
```lean
abbrev plus := Nat.add

def sum := Nat.add

@[irreducible]
def tally := Nat.add
```

可约同义词由 {tactic}`simp` 展开：
```lean
theorem plus_eq_add : plus x y = x + y := by simp
```

然而，半约同义词并未由 {tactic}`simp` 展开：
```lean -keep +error (name := simpSemi)
theorem sum_eq_add : sum x y = x + y := by simp
```
尽管如此，由 {tactic}`rfl` 引发的 定义等价 检查会展开 {lean}`sum`：
```lean
theorem sum_eq_add : sum x y = x + y := by rfl
```
然而，不可约的 {lean}`tally` 不会被 定义等价 约简。
```lean  -keep +error (name := reflIr)
theorem tally_eq_add : tally x y = x + y := by rfl
```
当显式提供时，{tactic}`simp`策略可以展开任何定义，甚至是不可约的定义：
```lean  -keep (name := simpName)
theorem tally_eq_add : tally x y = x + y := by simp [tally]
```
类似地，可以通过将证明的一部分放在 {tactic}`with_unfolding_all` 块中来指示忽略不可约性：
```lean
theorem tally_eq_add : tally x y = x + y := by with_unfolding_all rfl
```
:::

:::example "Reducibility and Implicit Arguments"
函数 {lean}`plus`、{lean}`sum` 和 {lean}`tally` 是 {lean}`Nat.add` 的同义词，分别是可约化、隐式可约化和不可约化：
```lean
abbrev plus := Nat.add

@[implicit_reducible]
def sum := Nat.add

def tally := Nat.add
```

{name}`Nonzero` 的实例包含给定数字不等于零的证明。
函数 {name}`notZero` 从合成实例中提取此证明：
```lean
class Nonzero (n : Nat) where
  non_zero : n ≠ 0

instance Nonzero.instSucc : Nonzero (n + 1) where
  non_zero := by grind

def notZero (n : Nat) [Nonzero n] : n ≠ 0 := Nonzero.non_zero
```

找到可简化定义 {name}`plus` 的实例：
```lean
#check notZero (plus 2 2)
```
还可以找到隐式可约定义 {name}`sum`。
这是因为类型 {lean}`Nonzero (sum 2 2)` 是 {name}`notZero` 的 {tech (key := "instance implicit")}[实例隐式] 参数的类型。
特别是，{name}`sum` 被简化为 {name}`Nat.add`，它本身是隐式可约的，因此类型被简化为 {lean}`Nonzero 4`：
```lean
#check notZero (sum 2 2)
```

{name}`tally` 的实例合成失败，因为它没有减少：
```lean +error (name := notZeroTally)
#check notZero (tally 2 2)
```
```leanOutput notZeroTally
failed to synthesize instance of type class
  Nonzero (tally 2 2)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

在其他上下文中，例如调用 {tactic}`simp`，{name}`plus` 会展开：
```lean
theorem plus_eq_add : plus x y = x + y := by simp
```

然而，隐式可约同义词并未由 {tactic}`simp` 展开：
```lean -keep +error (name := simpInst)
theorem sum_eq_add : sum x y = x + y := by simp
```
```leanOutput simpInst
`simp` made no progress
```

:::


## 修改还原性
%%%
file := "Modifying-Reducibility"
tag := "zh-recursivedefs-h007"
%%%

通过使用 {keywordOf Lean.Parser.Command.attribute}`attribute` 命令应用适当的属性，可以在定义定义的模块中全局修改定义的可约性。
在其他模块中，可以通过使用 {keyword}`local` 修饰符应用属性来修改导入定义的可简化性。
{keywordOf Lean.Parser.commandSeal__}`seal` 和 {keywordOf Lean.Parser.commandUnseal__}`unseal` 命令是此过程的简写。

:::syntax command (title := "Local Irreducibility")

{includeDocstring Lean.Parser.commandSeal__}

```grammar
seal $_:ident $_*
```
:::

:::syntax command (title := "Local Reducibility")
{includeDocstring Lean.Parser.commandUnseal__}

```grammar
unseal $_:ident $_*
```

:::

## 选项
%%%
file := "Options"
tag := "zh-recursivedefs-h008"
%%%

为了提高性能，精化器和许多策略构建了索引和缓存。
其中许多都考虑了可还原性，如果可还原性发生全局变化，则无法使它们失效并重新生成。
默认情况下，不允许对还原性设置进行不安全的更改，这可能会产生不可预测的结果，但可以通过使用 {option}`allowUnsafeReducibility` 选项来启用它们。

{optionDocs allowUnsafeReducibility}
