/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers
import ManualZh.Classes.InstanceDecls
import ManualZh.Classes.InstanceSynth
import ManualZh.Classes.DerivingHandlers
import ManualZh.Classes.BasicClasses

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command (declModifiers)

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxRecDepth 100000
#doc (Manual) "Type 类别" =>
%%%
tag := "type-classes"
%%%

如果一个操作可以与多种类型一起使用，那么它就是_多态_。
在 Lean 中，多态性分为三种：

 1. {tech (key := "universe polymorphism")}[宇宙多态性]，其中定义中的排序可以通过各种方式实例化，
 2. 将类型作为（可能是隐式的）参数的函数，允许单个代码体处理任何类型，以及
 3. {deftech (key := "ad-hoc polymorphism")}_ad-hoc多态性_，用类型类实现，其中要重载的操作对于不同类型可能有不同的实现。

由于 Lean 不允许对类型进行大小写分析，因此多态函数实现的操作对于任何类型参数的选择都是统一的；例如，{name}`List.map` 不会根据输入列表是否包含 {name}`String` 或 {name}`Nat` 突然进行不同的计算。
当没有“统一”的方法来实现操作时，临时多态操作非常有用；规范用例是重载算术运算符，以便它们与 {name}`Nat`、{name}`Int`、{name}`Float` 以及具有合理加法概念的任何其他类型一起使用。
Ad-hoc多态性也可能涉及多种类型；在集合中查找给定索引处的值涉及集合类型、索引类型以及要提取的成员元素的类型。
{deftech (key := "type class")}_type class_{margin}[Type 类首先在 {citehere wadlerBlott89}[]] 中描述，描述了重载操作的集合（称为 {deftech (key := "methods")}_methods_）以及所涉及的类型。

Type 类非常灵活。
重载可能涉及多种类型；对于数据结构、索引类型、元素类型甚至断言结构中键存在的谓词的特定选择，可以重载诸如对数据结构进行索引之类的操作。
由于Lean的表达类型系统，重载操作不仅限于类型；类型类可以通过普通值、类型族、甚至谓词或命题来参数化。
所有这些可能性都在实践中使用：

: 自然数文字

  {name}`OfNat` 类型类用于解释自然数文字。
  实例可能不仅取决于被实例化的类型，还取决于数字文字本身。

: 计算效果

  Type类，例如{name}`Monad`，其参数是从一种类型到另一种类型的函数，用于提供{ref "monads-and-do"}[具有副作用的程序的特殊语法]。
  重载操作的“类型”实际上是类型级函数，例如 {name}`Option`、{name}`IO` 或 {name}`Except`。

: 谓词和命题

  {name}`Decidable` 类型类允许 Lean 自动找到命题的决策过程。
  这用作 {keywordOf termIfThenElse}`if` 表达式的基础，该表达式可以在任何可判定的命题上分支。

虽然普通的多态定义只是期望使用任意参数进行实例化，但使用类型类重载的运算符将使用 {deftech (key := "instances")}_instances_ 进行实例化，{deftech}_instances_ 定义某些特定参数集的重载操作。
这些 {deftech}[instance-implicit] 参数在方括号中指示。
在调用站点，Lean 或者 {deftech (key := "synthesis")}_synthesizes_ {index}[实例合成] {index (subterm := "of type class instances")}[合成]来自可用候选的合适实例，或者发出错误信号。
因为实例本身可能具有实例参数，所以该搜索过程可以是递归的并且产生组合来自各种实例的代码的最终复合实例值。
因此，类型类实例合成也是以类型导向的方式构造程序的一种手段。

以下是类型类的一些典型用例：
 * Type 类可以表示重载运算符，例如可与各种类型的数字一起使用的算术或可用于各种数据结构的成员谓词。对于给定类型，通常有一个规范的运算符选择——毕竟，{lean}`Nat` 没有合理的加法替代定义——但这不是一个基本属性，如果需要，库可以提供替代实例。
 * Type 类可以表示代数结构，提供额外的结构和结构所需的公理。例如，表示阿贝尔群的类型类可能包含二元运算符、一元逆运算符、单位元素的方法，以及证明二元运算符是结合性和交换性的、单位是单位以及逆运算符在运算符两侧产生单位元素的证明。这里，可能没有规范的结构选择，并且库可以提供多种方法来实例化给定的一组公理；整数上有两个同样规范的幺半群结构。
 * 类型类可以表示两种类型之间的关系，允许库以某种新颖的方式一起使用它们。
   {lean}`Coe` 类表示自动插入从一种类型到另一种类型的强制转换，{lean}`MonadLift` 表示一种在需要另一种效果的上下文中运行具有一种效果的操作的方法。
 * Type 类可以表示类型驱动代码生成的框架，其中多态类型的实例各自贡献最终程序的一部分。
    {name}`Repr` 类定义了类型的规范漂亮打印机，多态类型最终得到多态 {name}`Repr` 实例。
    当最终在具有已知具体类型的表达式（例如 {lean}`List (Nat × (String ⊕ Int))`）上调用漂亮打印时，生成的漂亮打印机包含从 {name}`List`、{name}`Prod`、{name}`Nat`、{name}`Sum`、{name}`String` 的 {name}`Repr` 实例组装的代码，以及{name}`Int`。

# 类声明
%%%
tag := "class"
%%%

Type 类使用 {keywordOf Lean.Parser.Command.declaration}`class` 关键字声明。

:::syntax command (title := "Type Class Declarations")
```grammar
$_:declModifiers
class $d:declId $_:bracketedBinder* $[: $_]?
  $[extends $[$[$_ : ]?$_],*]?
  where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$x:ident],*]?
```

声明一个新类型类。
:::

:::keepEnv
```lean -show
-- Just make sure that the `deriving` clause is legit
class A (n : Nat) where
  k : Nat
  eq : n = k
deriving DecidableEq
```
:::


{keywordOf Lean.Parser.Command.declaration}`class` 声明创建一个新的单构造函数归纳类型，就像使用了 {keywordOf Lean.Parser.Command.declaration}`structure` 命令一样。
事实上，{keywordOf Lean.Parser.Command.declaration}`class` 和 {keywordOf Lean.Parser.Command.declaration}`structure` 命令的结果几乎相同，并且两者中可以以相同的方式使用默认值等功能。
有关结构体的默认值、继承和其他功能的更多信息，请参阅 {ref "structures"}[结构体文档]。
结构声明和类声明之间的区别是：

: 方法而不是字段

  创建 {tech}[methods]，而不是创建将结构类型的值作为显式参数的字段投影。每个方法都将相应的实例作为实例隐式参数。

: 实例隐式父类

  扩展其他类的类的构造函数将其父类的实例作为实例隐式参数，而不是显式参数。
  当定义此类的实例时，实例综合用于查找继承字段的值。
  不是类的父级仍然是底层构造函数的显式参数。

: 通过实例合成进行父投影

  结构字段投影利用 {ref "structure-inheritance"}[继承信息] 从子结构值投影父结构字段。
  相反，类使用实例合成：给定一个子类实例，合成将构造父类；因此，方法不会以与将投影添加到子结构相同的方式添加到子类中。

: 注册为班级

  生成的归纳类型被注册为类型类，可以为其定义实例，并且可以用作实例隐式参数的类型。

: 考虑 Out 和 semi-out 参数

  {name}`outParam` 和 {name}`semiOutParam` {tech}[gadgets] 在结构定义中没有任何意义，但它们在类定义中用于控制实例搜索。

虽然类定义允许使用 {keywordOf Lean.Parser.Command.declaration}`deriving` 子句来维护类和结构精化之间的并行性，但它们并不经常使用，应被视为高级功能。

:::example "No Instances of Non-Classes"

Lean 拒绝非类类型的实例隐式参数：
```lean +error (name := notClass)
def f [n : Nat] : n = n := rfl
```

```leanOutput notClass
invalid binder annotation, type is not a class instance
  Nat

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
```

:::

::::example "Class vs Structure Constructors"
非常小的代数层次结构可以表示为结构（下面的 {name}`S.Magma`、{name}`S.Semigroup` 和 {name}`S.Monoid`）、结构和类的混合 ({name}`C1.Monoid`)，或仅使用类（{name}`C2.Magma`、{name}`C2.Semigroup` 和 {name}`C2.Monoid`）：
```lean
namespace S
structure Magma (α : Type u) where
  op : α → α → α

structure Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

structure Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end S

namespace C1
class Monoid (α : Type u) extends S.Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C1

namespace C2
class Magma (α : Type u) where
  op : α → α → α

class Semigroup (α : Type u) extends Magma α where
  op_assoc : ∀ x y z, op (op x y) z = op x (op y z)

class Monoid (α : Type u) extends Semigroup α where
  ident : α
  ident_left : ∀ x, op ident x = x
  ident_right : ∀ x, op x ident = x
end C2
```


{name}`S.Monoid.mk` 和 {name}`C1.Monoid.mk` 具有相同的签名，因为类 {name}`C1.Monoid` 的父类本身不是一个类：
```signature
S.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  S.Monoid α
```
```signature
C1.Monoid.mk.{u} {α : Type u}
  (toSemigroup : S.Semigroup α)
  (ident : α)
  (ident_left : ∀ (x : α), toSemigroup.op ident x = x)
  (ident_right : ∀ (x : α), toSemigroup.op x ident = x) :
  C1.Monoid α
```

同样，由于 `S.Magma` 和 `C2.Magma` 都不是从另一个结构或类继承的，因此它们的构造函数是相同的：
```signature
S.Magma.mk.{u} {α : Type u} (op : α → α → α) : S.Magma α
```
```signature
C2.Magma.mk.{u} {α : Type u} (op : α → α → α) : C2.Magma α
```

然而，{name}`S.Semigroup.mk` 将其父级作为普通参数，而 {name}`C2.Semigroup.mk` 将其父级作为实例隐式参数：
```signature
S.Semigroup.mk.{u} {α : Type u}
  (toMagma : S.Magma α)
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  S.Semigroup α
```
```signature
C2.Semigroup.mk.{u} {α : Type u} [toMagma : C2.Magma α]
  (op_assoc : ∀ (x y z : α),
    toMagma.op (toMagma.op x y) z = toMagma.op x (toMagma.op y z)) :
  C2.Semigroup α
```

最后，{name}`C2.Monoid.mk` 将其半群父代作为实例隐式参数。
对 `op` 的引用成为对方法 {name}`C2.Magma.op` 的引用，依靠实例综合通过其父投影从 {name}`C2.Semigroup` 实例隐式参数恢复实现：
```signature
C2.Monoid.mk.{u} {α : Type u}
  [toSemigroup : C2.Semigroup α]
  (ident : α)
  (ident_left : ∀ (x : α), C2.Magma.op ident x = x)
  (ident_right : ∀ (x : α), C2.Magma.op x ident = x) :
  C2.Monoid α
```
::::

类型类的参数可以用 {deftech}_gadgets_ 标记，它们是恒等函数的特殊版本，导致精化器以不同方式处理值。
小工具永远不会改变术语的_含义_，但它们可能会导致在精化时间搜索过程中以不同方式对待该术语。
小工具 {name}`outParam` 和 {name}`semiOutParam` 影响 {ref "instance-synth"}[实例综合]，因此它们记录在该部分中。

类型是否是类对 定义等价 没有影响。
具有相同参数的同一类的两个实例不一定相同，实际上可能非常不同。

::::example "Instances are Not Unique"

这种二进制堆插入的实现是有缺陷的：
```lean
structure Heap (α : Type u) where
  contents : Array α
deriving Repr

def Heap.bubbleUp [Ord α] (i : Nat) (xs : Heap α) : Heap α :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if Ord.compare xs.contents[i] xs.contents[j] == .lt then
      Heap.bubbleUp j { xs with contents := xs.contents.swap i j }
    else xs

def Heap.insert [Ord α] (x : α) (xs : Heap α) : Heap α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
```

问题在于，使用一个 {name}`Ord` 实例构造的堆稍后可能会与另一个实例一起使用，从而导致堆不变量的破坏。

纠正此问题的一种方法是使堆类型取决于所选的 `Ord` 实例：
```lean
structure Heap' (α : Type u) [Ord α] where
  contents : Array α

def Heap'.bubbleUp [inst : Ord α]
    (i : Nat) (xs : @Heap' α inst) :
    @Heap' α inst :=
  if h : i = 0 then xs
  else if h : i ≥ xs.contents.size then xs
  else
    let j := i / 2
    if inst.compare xs.contents[i] xs.contents[j] == .lt then
      Heap'.bubbleUp j {xs with contents := xs.contents.swap i j}
    else xs

def Heap'.insert [Ord α] (x : α) (xs : Heap' α) : Heap' α :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.bubbleUp i
```

在改进的定义中，{name}`Heap'.bubbleUp` 是不必要的明确；该实例不需要在此处显式命名，因为 Lean 仍然会选择指定的实例，但它确实为读者带来了正确性不变的前沿和中心。
::::

## 将类型求和为类
%%%
tag := "class inductive"
%%%

大多数类型类遵循一组重载方法的范例，客户端可以从中自由选择。
这自然是通过产品类型建模的，重载方法是该产品类型的投影。
然而，有些类是求和类型：它们要求合成实例的接收者首先检查提供了可用实例构造函数。
为了说明这些类，类声明可以包含任意 {tech (key := "inductive type")}[归纳类型]，而不仅仅是结构声明的扩展形式。

:::syntax Lean.Parser.Command.declaration (title := "Class Inductive Type Declarations")
```grammar
$_:declModifiers
class inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```
:::

归纳类型类与其他归纳类型类一样，只是它们可以参与实例合成。
类归纳的典型示例是 {name}`Decidable`：在具有自由变量的上下文中合成实例相当于合成决策过程，但如果没有自由变量，则可以仅通过实例合成来确定命题的真实性（如 {tactic (show:="decide")}`Lean.Parser.Tactic.decide`策略所做的那样）。

## 类别缩写
%%%
tag := "class-abbrev"
%%%

在某些情况下，许多相关的类型类可能在整个代码库中同时出现。
不必重复编写所有名称，而是可以定义一个扩展所有相关类的类，而本身不提供新方法。
然而，这个新类有一个缺点：它的实例必须显式声明。

{keywordOf Lean.Parser.Command.classAbbrev}`class abbrev` 命令允许创建 {deftech}_class abbreviations_，其中一个名称是许多其他类参数的缩写。
在幕后，类缩写由扩展所有其他类的类来表示。
它的构造函数还被声明为一个实例，因此可以仅通过实例合成来构造新类。

::::keepEnv

:::example "Class Abbreviations"
{name}`plusTimes1` 和 {name}`plusTimes2` 都要求其参数类型具有 {name}`Add` 和 {name}`Mul` 实例：

```lean
class abbrev AddMul (α : Type u) := Add α, Mul α

def plusTimes1 [AddMul α] (x y z : α) := x + y * z

class AddMul' (α : Type u) extends Add α, Mul α

def plusTimes2 [AddMul' α] (x y z : α) := x + y * z
```

由于 {name}`AddMul` 是 {keywordOf Lean.Parser.Command.classAbbrev}`class abbrev`，因此无需附加声明即可将 {name}`plusTimes1` 与 {lean}`Nat` 一起使用：

```lean (name := plusTimes1)
#eval plusTimes1 2 5 7
```
```leanOutput plusTimes1
37
```

但是，{name}`plusTimes2` 失败，因为没有 {lean}`AddMul' Nat` 实例 — 尚未声明任何实例：
```lean (name := plusTimes2a) +error
#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2a
failed to synthesize instance of type class
  AddMul' ?m.8

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
声明一个非常通用的实例可以解决 {lean}`Nat` 和所有其他类型的问题：
```lean (name := plusTimes2b)
instance [Add α] [Mul α] : AddMul' α where

#eval plusTimes2 2 5 7
```
```leanOutput plusTimes2b
37
```
:::
::::

{include 0 ManualZh.Classes.InstanceDecls}

{include 0 ManualZh.Classes.InstanceSynth}

# 派生实例
%%%
tag := "deriving-instances"
%%%

Lean 可以自动生成许多类的实例，该过程称为 {deftech}_deriving_instances。
实例派生可以在定义类型时调用，也可以作为独立命令调用。

:::syntax Lean.Parser.Command.optDeriving -open (title := "Instance Deriving (Optional)")
作为创建新归纳类型的命令的一部分，{keywordOf Lean.Parser.Command.declaration}`deriving` 子句指定应为其生成实例的以逗号分隔的类名列表：
```grammar
$[deriving $[$_],*]?
```
:::

:::syntax Lean.Parser.Command.deriving (title := "Stand-Alone Deriving of Instances")
独立的 {keywordOf Lean.Parser.Command.deriving}`deriving` 命令指定多个类名称和主题名称。
每个指定的类别都是针对每个指定的科目派生的。
```grammar
deriving instance $[$_],* for $_,*
```
:::

::::keepEnv
:::example "Deriving Multiple Classes"
指定多个类来派生多种类型后，如以下代码所示：
```lean
structure A where
structure B where

deriving instance BEq, Repr for A, B
```
所有类型都存在所有实例，因此所有四个 {keywordOf Lean.Parser.Command.synth}`#synth` 命令都会成功：
```lean
#synth BEq A
#synth BEq B
#synth Repr A
#synth Repr B
```
:::
::::

{include 2 ManualZh.Classes.DerivingHandlers}

{include 0 ManualZh.Classes.BasicClasses}
