/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Std.Data.Iterators
import Std.Data.TreeMap

import Manual.Meta
import ManualZh.Interaction.FormatRepr

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Std.Iterators Types
open Std (TreeMap Iter IterM IterStep Iterator PlausibleIterStep IteratorLoop IteratorAccess LawfulIteratorLoop)

#doc (Manual) "迭代器" =>
%%%
tag := "iterators"
%%%

{deftech}_iterator_ 提供对某些数据源的每个元素的顺序访问。
典型的迭代器允许对集合（例如列表、数组或 {name Std.TreeMap}`TreeMap`）中的元素进行一一访问，但它们也可以通过执行某些 {tech (key := "monad")}[monadic] 效果（例如读取文件）来提供对数据的访问。
迭代器为所有这些操作提供了一个通用接口。
写入迭代器 API 的代码可以不知道数据源。

每个迭代器都维护一个内部状态，使其能够确定下一个值。
由于 Lean 是纯函数式语言，因此使用迭代器不会使其无效，而是使用更新后的状态复制它。
与往常一样，{tech (key := "reference count")}[引用计数]用于将仅使用一次值的程序优化为破坏性修改值的程序。

要使用迭代器，请导入 {module}`Std.Data.Iterators`。

:::example "Mixing Collections"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
使用 {name}`List.zip` 或 {name}`Array.zip` 组合列表和数组通常需要将其中一个集合转换为另一个集合。
使用迭代器，无需转换即可处理它们：
```lean (name := zip)
def colors : Array String := #["purple", "gray", "blue"]
def codes : List String := ["aa27d1", "a0a0a0", "0000c5"]

#eval colors.iter.zip codes.iter |>.toArray
```
```leanOutput zip
#[("purple", "aa27d1"), ("gray", "a0a0a0"), ("blue", "0000c5")]
```
:::

::::example "Avoiding Intermediate Structures"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
:::paragraph
在此示例中，组合了颜色数组和颜色代码列表。
该计划分为三个中间阶段：
1. 名称和代码成对组合。
2. 这些对被转换成可读的字符串。
3. 字符串与换行符组合在一起。
```lean (name := intermediate)
def colors : Array String := #["purple", "gray", "blue"]

def codes : List String := ["aa27d1", "a0a0a0", "0000c5"]

def go : IO Unit := do
  let colorCodes := colors.iter.zip codes.iter
  let colorCodes := colorCodes.map fun (name, code) =>
    s!"{name} ↦ #{code}"
  let colorCodes := colorCodes.fold (init := "") fun x y =>
    if x.isEmpty then y else x ++ "\n" ++ y
  IO.println colorCodes

#eval go
```
```leanOutput intermediate
purple ↦ #aa27d1
gray ↦ #a0a0a0
blue ↦ #0000c5
```
:::

计算的中间阶段不分配新的数据结构。
相反，转换的所有步骤都融合到一个循环中，{name}`Iter.fold` 一次执行一个步骤。
在每个步骤中，单个颜色和颜色代码被组合成一对，重写为字符串，并添加到结果字符串中。
::::

Lean 标准库提供了三种迭代器操作。
{deftech}_Producers_ 从某些数据源创建一个新的迭代器。
它们确定迭代器要返回哪些数据，以及如何计算这些数据，但它们无法控制计算发生的时间。
{deftech}_Consumers_ 将迭代器中的数据用于某种目的。
消费者请求迭代器的数据，迭代器仅计算足够的数据来满足消费者的请求。
{deftech (key := "iterator combinator")}_Combinators_ 既是消费者又是生产者：它们从现有迭代器创建新迭代器。
示例包括 {name}`Iter.map` 和 {name}`Iter.filter`。
生成的迭代器通过消耗其底层迭代器来生成数据，并且在它们本身被消耗之前实际上不会迭代底层集合。


:::keepEnv
```lean -show
/-- A collection type. -/
structure Coll : Type u where
/-- The elements of the collection `Coll`. -/
structure Elem : Type u where
/-- Returns an iterator for `c`. -/
def Coll.iter (c : Coll) := (#[].iter : Iter Elem)
```
每个有意义的内置集合都可以进行迭代。
换句话说，集合库包括迭代器 {tech}[生产者]。
按照约定，集合类型 {name}`Coll` 提供函数 {name}`Coll.iter`，该函数返回集合元素上的迭代器。
示例包括 {name}`List.iter`、{name}`Array.iter` 和 {name}`TreeMap.iter`。
此外，其他内置类型（例如范围）支持使用相同约定的迭代。
:::

# 运行时注意事项
%%%
tag := "zh-iterators-h001"
%%%

对于许多用例，使用迭代器可以通过避免分配中间数据结构来提高性能。
如果没有迭代器，则使用数组压缩列表需要首先将其中一个类型转换为另一种类型，分配中间结构，然后使用适当的 {name List.zip}`zip` 函数。
使用迭代器，可以避免中间结构。

当使用迭代器时，生成的计算应该被视为单个循环，即使迭代器本身是使用来自多个底层迭代器的组合器构建的。
循环的一个步骤可能会执行底层迭代器的多个步骤。
在许多情况下，Lean 编译器可以优化迭代器计算，消除中间开销，但这并不能保证。
当分析显示涉及多个数据源的紧密循环花费大量时间时，可能有必要检查编译器的 IR 以查看迭代器的操作是否被融合。
特别是，如果 IR 在步骤中包含许多模式匹配，则可能是内联或专门化失败的标志。
如果是这种情况，可能需要手动编写尾递归函数，而不是使用更高级别的 API。

# 迭代器定义
%%%
tag := "zh-iterators-h002"
%%%

迭代器可以是单子迭代器或纯迭代器，并且它们可以是有限的、高效的或潜在无限的。
{deftech (key:="monadic iterator")}_Monadic_ 迭代器在某些 {tech}[monad] 中使用副作用来发出每个值，因此必须在 monad 中使用，而 {deftech (key:="pure iterator")}_pure_ 迭代器不需要副作用。
例如，迭代目录中的所有文件需要 {name}`IO` monad。
纯迭代器的类型为 {name}`Iter`，而一元迭代器的类型为 {name}`IterM`。

{docstring Iter}

{docstring IterM}

{name}`Iter` 和 {name}`IterM` 类型仅仅是内部状态的包装。
该内部状态类型是迭代器类型的隐式参数。
对于基本的生产者迭代器（例如从 {name}`List.iter` 生成的迭代器），这种类型相当简单；但是，由 {tech (key := "iterator combinator")}[combinators] 生成的迭代器使用可能会变大的多态状态类型。
由于 Lean 在详细说明函数体之前详细说明了函数的指定返回类型，因此可能无法自动确定函数返回的迭代器类型的内部状态类型。
在这些情况下，从签名中省略返回类型并在定义主体上放置类型注释可能会有所帮助，这允许从主体调用的特定迭代器组合器用于确定状态类型。

:::example "Iterator State Types"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators.Types (ListIterator ArrayIterator Map)
```

为列表和数组迭代器显式编写内部状态类型是可行的：
```lean
def reds := ["red", "crimson"]

example : @Iter (ListIterator String) String := reds.iter

example : @Iter (ArrayIterator String) String := reds.toArray.iter
```
然而，使用 {name}`Iter.map` 组合器的内部状态类型相当复杂：
```lean
example :
    @Iter
      (Map (ListIterator String) Id Id @id fun x : String =>
        pure x.length)
      Nat :=
  reds.iter.map String.length
```
省略状态类型会导致错误：
```lean +error (name := noStateType)
example : Iter Nat := reds.iter.map String.length
```
```leanOutput noStateType
don't know how to synthesize implicit argument `α`
  @Iter ?m.1 Nat
context:
⊢ Type

Note: Because this declaration's type has been explicitly provided, all parameter types and holes (e.g., `_`) in its header are resolved before its body is processed; information from the declaration body cannot be used to infer what these values should be
```
与其手动编写状态类型，不如省略返回类型并在该术语周围提供注释：
```lean
example := (reds.iter.map String.length : Iter Nat)

example :=
  show Iter Nat from
  reds.iter.map String.length
```
:::

迭代的实际过程包括根据请求生成一系列迭代步骤。
每个步骤都会返回一个更新后的迭代器，其中包含新的内部状态以及数据值（以 {name}`IterStep.yield` 形式）、调用方应再次请求数据值的指示符 ({name}`IterStep.skip`) 或迭代完成的指示 ({name}`IterStep.done`)。
如果没有 {name IterStep.skip}`skip` 的能力，那么使用迭代器组合器（例如 {name}`Iter.filter`）将更加困难，因为这些迭代器组合器不会为底层迭代器生成的所有值生成值。
使用 {name IterStep.skip}`skip`，{name Iter.filter}`filter` 的实现不需要担心底层迭代器是否是 {tech (key:="finite iterator")}[finite] 来成为定义明确的函数，并且可以在单独的证明中进行其有限性的推理。
此外，{name Iter.filter}`filter` 需要一个内部循环，这对于编译器来说内联要困难得多。

{docstring IterStep}

{name}`Iter` 和 {name}`IterM` 采取的步骤分别由类型 {name}`Iter.Step` 和 {name}`IterM.Step` 表示。
两种类型的步骤都是 {name}`IterStep` 的包装器，其中包括用于跟踪终止行为的 {ref "iterator-plausibility"}[附加证明]。

{docstring Iter.Step}

{docstring IterM.Step}

步骤是使用 {name}`Iterator.step`（{name}`Iterator` 类型类的方法）的迭代器生成的。
{name}`Iterator` 用于纯迭代器和一元迭代器；纯迭代器在 monad 的选择上可以是完全多态的，这允许调用者使用 {name}`Id` 实例化它。

{docstring Iterator +allowMissing}

## 合理性
%%%
tag := "iterator-plausibility"
%%%

除了阶跃函数之外，{name}`Iterator` 的实例还包括关系 {name}`Iterator.IsPlausibleStep`。
这种关系的存在是因为大多数迭代器都保持其内部状态的不变性并以可预测的方式产生值。
例如，数组迭代器跟踪数组和数组中的当前索引。
步进数组迭代器会导致迭代器遍历相同的底层数组；当索引足够小时，它会产生一个值，否则会产生一个值。
迭代器状态中的 {deftech}_plausible Steps_ 是通过 {name Iterator.IsPlausibleStep}`IsPlausibleStep` 的迭代器实现与其相关的那些步骤。
在逻辑级别跟踪合理性使得推断单子迭代器的终止行为变得可行。

{name}`Iter.Step` 和 {name}`IterM.Step` 都是根据 {name}`PlausibleIterStep` 定义的；因此，这两种类型都可以与 {tech}[前导点符号] 一起用于其命名空间。
可以使用三个 {ref "match_pattern-functions"}[匹配模式函数] {name}`PlausibleIterStep.yield`、{name}`PlausibleIterStep.skip` 和 {name}`PlausibleIterStep.done` 来分析 {name}`Iter.Step` 或 {name}`IterM.Step`。
这些函数将底层 {name}`IterStep` 中的信息与周围的证明对象配对。

{docstring PlausibleIterStep}

{docstring PlausibleIterStep.yield}

{docstring PlausibleIterStep.skip}

{docstring PlausibleIterStep.done}

## 有限且高效的迭代器
%%%
tag := "zh-iterators-h004"
%%%

:::paragraph
并非所有迭代器都保证返回有限数量的结果；迭代所有自然数是完全明智的。
同样，并非所有迭代器都保证返回单个结果或终止；迭代器可以使用任意程序定义。
因此，Lean 将迭代器分为三个终止类：
* {deftech (key:="finite iterator")}_Finite_ 迭代器保证在有限数量的步骤后完成迭代。这些迭代器有一个 {name}`Finite` 实例。
* {deftech (key:="productive iterator")}_Productive_ 迭代器保证在有限多个步骤中产生一个值或终止，但它们可能产生无限多个值。这些迭代器有一个 {name}`Productive` 实例。
* 所有其他迭代器，其终止行为未知。这些迭代器都没有实例。

所有有限迭代器都必然是高效的。
:::

{docstring Finite}

{docstring Productive}

Lean 的标准库提供了许多迭代迭代器的函数。这些消费者功能通常不
对底层迭代器做出任何假设。特别是，对于某些迭代器，此类函数可能会永远运行。

有时，函数确实终止是至关重要的。
对于这些情况，组合器 {name}`Iter.ensureTermination` 会产生一个迭代器，该迭代器提供保证终止的消费者变体。
他们通常需要证明所涉及的迭代器是有限的。

{docstring Iter.ensureTermination}

{docstring IterM.ensureTermination}

::::example "Iterating Over `Nat`"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Productive)
```
:::paragraph
要编写一个依次生成每个自然数的迭代器，第一步是实现其内部状态。
这个迭代器只需要记住下一个自然数：
```lean
structure Nats where
  next : Nat
```
:::
:::paragraph
该迭代器只会产生下一个自然数。
因此，其步进函数永远不会返回 {name IterStep.skip}`skip` 或 {name IterStep.done}`done`。
每当它产生一个值时，该值将是内部状态的 {name Nats.next}`next` 字段，并且后继迭代器的 {name Nats.next}`next` 字段将大 1。
{tactic}`grind`策略足以表明该步骤确实合理：
```lean
instance [Pure m] : Iterator Nats m Nat where
  IsPlausibleStep it
    | .yield it' n =>
      n = it.internalState.next ∧
      it'.internalState.next = n + 1
    | _ => False
  step it :=
    let n := it.internalState.next
    pure <| .deflate <|
      .yield { it with internalState.next := n + 1 } n (by grind)
```

每当定义迭代器时，都应提供 {name}`IteratorLoop` 实例。
对于 {name}`Iter.toList` 或 `for` 循环等迭代器的大多数使用者来说，它们是必需的。
人们可以使用它们的默认实现，如下所示：

```lean
instance [Pure m] [Monad n] : IteratorLoop Nats m n :=
  .defaultImplementation
```
:::

:::paragraph
```lean -show
section
variable [Pure m] [inst : Iterator Nats m Nat] (it it' : IterM (α := Nats) m Nat)
```
此 {name Iterator.step}`step` 函数非常高效，因为它永远不会返回 {name IterStep.skip}`skip`。
因此，{name IterStep.skip}`skip` 的每条链具有有限长度的证明可以依赖于以下事实：当 {lean}`it` 是 {name}`Nats` 迭代器时，{lean}`Iterator.IsPlausibleStep it (.skip it') = False`：
```lean -show
end
```
```lean
instance [Pure m] : Productive Nats m where
  wf := .intro <| fun _ => .intro _ nofun
```
因为有无限多个 {name}`Nat`，所以迭代器不是有限的。
:::


:::paragraph
可以使用以下函数创建 {name}`Nats` 迭代器：
```lean
def Nats.iter : Iter (α := Nats) Nat :=
  IterM.mk { next := 0 } |>.toIter
```
:::

:::paragraph
通过运行以下函数可以打印所有自然数：
```lean
def f : IO Unit := do
  for x in Nats.iter do
    IO.println s!"{x}"
```
该函数永远不会终止，按升序打印所有自然数，一个
又一个。
:::

:::paragraph
此迭代器对于 {name}`Iter.zip` 等组合器最有用：
```lean (name := natzip)
#eval show IO Unit from do
  let xs : List String := ["cat", "dog", "pachycephalosaurus"]
  for (x, y) in Nats.iter.zip xs.iter do
    IO.println s!"{x}: {y}"
```
```leanOutput natzip
0: cat
1: dog
2: pachycephalosaurus
```
:::

:::paragraph
与前面的示例相反，此循环终止，因为 `xs.iter` 是有限迭代器，
通过提供 {name}`Finite` 实例，可以确保循环确实终止：
```lean (name := natfin)
#check type_of% (Nats.iter.zip ["cat", "dog"].iter).internalState

#synth Finite (Zip Nats Id (ListIterator String) String) Id
```
```leanOutput natfin
Zip Nats Id (ListIterator String) String : Type
```
```leanOutput natfin
Zip.instFinite₂
```
相反，`Nats.iter` 没有 `Finite` 实例，因为它产生无限多个值：
```lean (name := natinf) +error
#synth Finite Nats Id
```
```leanOutput natinf
failed to synthesize
  Finite Nats Id

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

因为有无限多个 {name}`Nat`，所以使用 {name}`Iter.ensureTermination` 会导致错误：
```lean (name := natterm) +error
#eval show IO Unit from do
  for x in Nats.iter.ensureTermination do
    IO.println s!"{x}"
```
```leanOutput natterm
failed to synthesize instance for 'for_in%' notation
  ForIn (EIO IO.Error) (Iter.Total Nat) ?m.12
```
:::
::::

::::example "Iterating Over Triples"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Finite)
```
类型 {name}`Triple` 包含三个相同类型的值：
```lean
structure Triple α where
  fst : α
  snd : α
  thd : α
```

{name}`Triple` 上的迭代器的内部状态可以由与当前位置配对的三元组组成。
该位置可以是字段之一，也可以是迭代完成的指示。
```lean
inductive TriplePos where
  | fst | snd | thd | done
```

位置可用于查找元素：

```lean
def Triple.get? (xs : Triple α) (pos : TriplePos) : Option α :=
  match pos with
  | .fst => some xs.fst
  | .snd => some xs.snd
  | .thd => some xs.thd
  | _ => none
```

每个字段的位置都有一个后继位置：
```lean
@[grind, grind cases]
inductive TriplePos.Succ : TriplePos → TriplePos → Prop where
  | fst : Succ .fst .snd
  | snd : Succ .snd .thd
  | thd : Succ .thd .done
```

迭代器本身将一个三元组与下一个元素的位置配对：
```lean
structure TripleIterator α where
  triple : Triple α
  pos : TriplePos
```

迭代从 {name TriplePos.fst}`fst` 开始：
```lean
def Triple.iter (xs : Triple α) : Iter (α := TripleIterator α) α :=
  IterM.mk {triple := xs, pos := .fst : TripleIterator α} |>.toIter
```

有两个看似合理的步骤：要么迭代器的位置有后继者，在这种情况下，下一个迭代器是与后继者位置指向相同三元组的迭代器，要么没有，在这种情况下迭代完成。
```lean
@[grind]
inductive TripleIterator.IsPlausibleStep :
    @IterM (TripleIterator α) m α →
    IterStep (@IterM (TripleIterator α) m α) α →
    Prop where
  | yield :
    it.internalState.triple = it'.internalState.triple →
    it.internalState.pos.Succ it'.internalState.pos →
    it.internalState.triple.get? it.internalState.pos = some out →
    IsPlausibleStep it (.yield it' out)
  | done :
    it.internalState.pos = .done →
    IsPlausibleStep it .done
```

相应的步骤函数产生由以下关系描述的迭代器和值：
```lean
instance [Pure m] : Iterator (TripleIterator α) m α where
  IsPlausibleStep := TripleIterator.IsPlausibleStep
  step
    | ⟨xs, pos⟩ =>
      pure <| .deflate <|
      match pos with
      | .fst => .yield ⟨xs, .snd⟩ xs.fst ?_
      | .snd => .yield ⟨xs, .thd⟩ xs.snd ?_
      | .thd => .yield ⟨xs, .done⟩ xs.thd ?_
      | .done => .done <| ?_
where finally
  all_goals grind [Triple.get?]
```

现在可以将该迭代器转换为数组：
```lean
def abc : Triple Char := ⟨'a', 'b', 'c'⟩
```
```lean (name := abcToArray)
#eval abc.iter.toArray
```
```leanOutput abcToArray
#['a', 'b', 'c']
```

一般来说，`Iter.toArray` 可能会永远运行。可以证明 `abc` 是有限的，上面的例子将在有限多个步骤后终止，通过
构造 `Finite (Triple Char) Id` 实例。
最简单的方法是从 {name}`TriplePos.done` 开始，向后推向 {name}`TriplePos.fst`，从而显示每个位置依次具有有限的后继链：

```lean
@[grind! .]
theorem acc_done [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .done : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | _, ⟨_, ⟨_, h⟩⟩ => by
      cases h <;> grind [IterStep.successor_done]

@[grind! .]
theorem acc_thd [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .thd : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

@[grind! .]
theorem acc_snd [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .snd : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

@[grind! .]
theorem acc_fst [Pure m] :
    Acc (IterM.IsPlausibleSuccessorOf (m := m))
      ⟨{ triple, pos := .fst : TripleIterator α}⟩ :=
  Acc.intro _ fun
    | ⟨{ triple, pos }⟩, ⟨h, h', h''⟩ => by
      cases h'' <;> grind [IterStep.successor_yield]

instance [Pure m] : Finite (TripleIterator α) m where
  wf := .intro <| fun
    | { internalState := { triple, pos } } => by
      cases pos <;> grind
```

要在 {keywordOf Lean.Parser.Term.doFor}`for` 循环中启用迭代器，需要 {name}`IteratorLoop` 的实例：
```lean
instance [Monad m] [Monad n] :
    IteratorLoop (TripleIterator α) m n :=
  .defaultImplementation
```
```lean (name := abc)
#eval show IO Unit from do
  for x in abc.iter do
    IO.println x
```
```leanOutput abc
a
b
c
```
::::

::::example "Iterators and Effects"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
迭代文件内容的一种方法是在每一步从 {name IO.FS.Stream}`Stream` 读取指定数量的字节。
当到达 EOF 时，迭代器可以通过让其引用计数降至零来关闭文件：
```lean
structure FileIterator where
  stream? : Option IO.FS.Stream
  count : USize := 8192
```

可以通过打开文件并将其句柄转换为流来创建迭代器：
```lean
def iterFile
    (path : System.FilePath)
    (count : USize := 8192) :
    IO (IterM (α := FileIterator) IO ByteArray) := do
  let h ← IO.FS.Handle.mk path .read
  let stream? := some (IO.FS.Stream.ofHandle h)
  return IterM.mk { stream?, count }
```

对于此迭代器，当文件仍然打开时，{name IterStep.yield}`yield` 是合理的，而当文件关闭时，{name IterStep.done}`done` 是合理的。
实际的步骤函数执行读取并在没有返回字节的情况下关闭文件：
```lean
instance : Iterator FileIterator IO ByteArray where
  IsPlausibleStep it
    | .yield .. =>
      it.internalState.stream?.isSome
    | .skip .. => False
    | .done => it.internalState.stream?.isNone
  step it := do
    let { stream?, count } := it.internalState
    match stream? with
    | none => return .deflate <| .done rfl
    | some stream =>
      let bytes ← stream.read count
      let it' :=
        { it with internalState.stream? :=
          if bytes.size == 0 then none else some stream
        }
      return .deflate <| .yield it' bytes (by grind)
```

要在循环中使用它，需要 {name}`IteratorLoop` 实例。
```lean
instance [Monad n] : IteratorLoop FileIterator IO n :=
  .defaultImplementation
```

这是足够的支持代码来使用迭代器来计算文件大小：
```lean
def fileSize (name : System.FilePath) : IO Nat := do
  let mut size := 0
  let f := (← iterFile name)
  for bytes in f do
    size := size + bytes.size
  return size
```

::::

## 访问元素
%%%
tag := "zh-iterators-h005"
%%%

一些迭代器支持高效的随机访问。
例如，数组迭代器可以通过增加其在数组中维护的索引来在恒定时间内跳过任意数量的元素。

{docstring IteratorAccess +allowMissing}

{docstring IterM.nextAtIdx?}

## 循环
%%%
tag := "zh-iterators-h006"
%%%

{docstring IteratorLoop +allowMissing}

{docstring IteratorLoop.defaultImplementation}

{docstring LawfulIteratorLoop +allowMissing}

## 宇宙层级
%%%
tag := "zh-iterators-h007"
%%%

为了使迭代器的 {tech}[宇宙层级] 更加灵活，在 {name}`Iterator.step` 的结果周围应用了包装类型 {name Std.Shrink}`Shrink`。
该类型目前是占位符。
当完整实施可用时，它的存在是为了减少重大变更的范围。

{docstring Std.Shrink}

{docstring Std.Shrink.inflate}

{docstring Std.Shrink.deflate}


## 基本迭代器
%%%
tag := "zh-iterators-h008"
%%%

除了集合类型提供的迭代器之外，还有两个不连接到任何底层数据结构的基本迭代器。
{name}`Iter.empty` 在没有产生任何数据后立即完成迭代，并且 {name}`Iter.repeat` 永远产生相同的元素。
这些迭代器主要用作使用组合器构建的大型迭代器的一部分。

{docstring Iter.empty}

{docstring IterM.empty}

{docstring Iter.repeat}


# 使用迭代器
%%%
tag := "zh-iterators-h009"
%%%

:::paragraph
使用迭代器的主要方式有以下三种：

: 将其转换为顺序数据结构

  函数 {name}`Iter.toList`、{name}`Iter.toArray` 及其一元等效函数 {name}`IterM.toList` 和 {name}`IterM.toArray` 按顺序构造包含迭代器中的值的列表或数组。
  只有 {tech}[有限迭代器] 可以转换为顺序数据结构。

: {keywordOf Lean.Parser.Term.doFor}`for` 循环

  {keywordOf Lean.Parser.Term.doFor}`for` 循环可以使用迭代器，使每个值在其主体中可用。
  这要求迭代器具有循环 monad 的 {name}`IteratorLoop` 实例。

: 单步执行迭代器

  迭代器可以一一提供它们的值，客户端代码依次显式请求每个新值。
  当单步执行时，迭代器仅执行足够的计算来产生所请求的值。
:::


:::example "Converting Iterators to Lists"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
在 {name}`countdown` 中，使用 {name}`Iter.map` 将范围上的迭代器转换为字符串上的迭代器。
对 {name}`Iter.map` 的调用不会导致对该范围进行任何迭代，直到调用 {name}`Iter.toList`，此时该范围的每个元素都会生成并转换为字符串。
```lean (name := toListEx)
def countdown : String :=
  let steps : Iter String := (0...10).iter.map (s!"{10 - ·}!\n")
  String.join steps.toList

#eval IO.println countdown
```
```leanOutput toListEx
10!
9!
8!
7!
6!
5!
4!
3!
2!
1!
```
:::

:::example "Converting Infinite Iterators to Lists"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
尝试从迭代器构建所有自然数的列表将产生无限循环：
```lean (name := toListInf) -keep
def allNats : List Nat :=
  let steps : Iter Nat := (0...*).iter
  steps.toList
```
组合器 {lean}`Iter.ensureTermination` 产生一个排除非终止的迭代器。
这些迭代器保证在有限多个步骤后终止，因此当 Lean 无法证明迭代器有限时不能使用。
```lean (name := toListInf) +error -keep
def allNats : List Nat :=
  let steps := (0...*).iter.ensureTermination
  steps.toList
```
生成的错误消息指出不存在 {name}`Finite` 实例：
```leanOutput toListInf
failed to synthesize instance of type class
  Finite (Rxi.Iterator Nat) Id

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::example "Consuming Iterators in Loops"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
该程序创建一个范围内的字符串迭代器，然后在 {keywordOf Lean.Parser.Term.doFor}`for` 循环中使用这些字符串：
```lean (name := iterFor)
def countdown (n : Nat) : IO Unit := do
  let steps : Iter String := (0...n).iter.map (s!"{n - ·}!")
  for i in steps do
    IO.println i
  IO.println "Blastoff!"

#eval countdown 5
```
```leanOutput iterFor
5!
4!
3!
2!
1!
Blastoff!
```
:::

:::example "Consuming Iterators Directly"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
函数 {name}`countdown` 直接调用范围迭代器的 {name Iter.step}`step` 函数，处理三种可能情况中的每一种。
```lean
def countdown (n : Nat) : IO Unit := do
  let steps : Iter Nat := (0...n).iter
  go steps
where
  go iter := do
    match iter.step with
    | .done _ => pure ()
    | .skip iter' _ => go iter'
    | .yield iter' i _ => do
      IO.println s!"{i}!"
      if i == 2 then
        IO.println s!"Almost there..."
      go iter'
  termination_by iter.finitelyManySteps
```
:::

## 步进迭代器
%%%
tag := "zh-iterators-h010"
%%%

使用 {name}`Iter.step` 或 {name}`IterM.step` 手动步进迭代器。

{docstring Iter.step}

{docstring IterM.step}

### 终止
%%%
tag := "zh-iterators-h011"
%%%

当手动步进有限迭代器时，终止测量 {name Iter.finitelyManySteps}`finitelyManySteps` 和 {name Iter.finitelyManySkips}`finitelyManySkips` 可用于表示每一步都使迭代更接近结束。
{ref "well-founded-recursion"}[良基递归] 的证明自动化已预先配置，以证明步骤后的递归调用会减少这些措施。

:::example "Finitely Many Skips"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
open Iterators (Productive)
```
此函数返回迭代器的第一个元素（如果有），否则返回 {name}`none`。
由于迭代器必须高效，因此保证最多在有限数量的 {name PlausibleIterStep.skip}`skip` 之后返回一个元素。
即使对于无限迭代器，该函数也会终止。
```lean
def getFirst {α β} [Iterator α Id β] [Productive α Id]
    (it : @Iter α β) : Option β :=
  match it.step with
  | .done .. => none
  | .skip it' .. => getFirst it'
  | .yield _ x .. => pure x
termination_by it.finitelyManySkips
```
:::

{docstring Iter.finitelyManySteps}

{docstring IterM.finitelyManySteps}

{docstring IterM.TerminationMeasures.Finite +allowMissing}

{docstring Iter.finitelyManySkips}

{docstring IterM.finitelyManySkips}

{docstring IterM.TerminationMeasures.Productive +allowMissing}

## 使用纯迭代器
%%%
tag := "zh-iterators-h012"
%%%

{docstring Iter.fold}

{docstring Iter.foldM}

{docstring Iter.length}

{docstring Iter.any}

{docstring Iter.anyM}

{docstring Iter.all}

{docstring Iter.allM}

{docstring Iter.find? +allowMissing}

{docstring Iter.findM? +allowMissing}

{docstring Iter.findSome? +allowMissing}

{docstring Iter.findSomeM? +allowMissing}

{docstring Iter.atIdx?}

{docstring Iter.atIdxSlow?}

## 使用 Monadic 迭代器
%%%
tag := "zh-iterators-h013"
%%%

{docstring IterM.drain}

{docstring IterM.fold}

{docstring IterM.foldM}

{docstring IterM.length}

{docstring IterM.any}

{docstring IterM.anyM}

{docstring IterM.all}

{docstring IterM.allM}

{docstring IterM.find? +allowMissing}

{docstring IterM.findM? +allowMissing}

{docstring IterM.findSome? +allowMissing}

{docstring IterM.findSomeM? +allowMissing}

{docstring IterM.atIdx?}

## 收藏家
%%%
tag := "zh-iterators-h014"
%%%

收集器使用迭代器，返回列表或数组中的所有数据。
为了被收集，迭代器必须是有限的。

{docstring Iter.toArray}

{docstring IterM.toArray}

{docstring Iter.toList}

{docstring IterM.toList}

{docstring Iter.toListRev}

{docstring IterM.toListRev}


# 迭代器组合器
%%%
tag := "zh-iterators-h015"
%%%

迭代器组合器的文档通常包括 {deftech}_大理石图_，显示底层迭代器返回的元素与组合器迭代器返回的元素之间的关系。
大理石图提供示例，而不是完整规格。
这些图由多行组成。
每行显示迭代器输出的示例，其中 `-` 表示 {name PlausibleIterStep.skip}`skip`，术语表示 {name PlausibleIterStep.yield}`yield` 返回的值，`⊥` 表示迭代结束。
空格表示没有发生迭代。
弹珠图中的未绑定标识符代表迭代器元素类型的任意值。


弹珠图中的垂直对齐表示因果关系：当两个元素对齐时，意味着消耗下面一行中的迭代器会导致上面的行被消耗。
特别是，消耗下层迭代器的第一个 $`n` 列会导致消耗上层迭代器的第一个 $`n` 列。

:::paragraph
从底层迭代器返回每个元素的恒等迭代器组合器的大理石图如下所示：
```
it    ---a-----b---c----d⊥
it.id ---a-----b---c----d⊥
```
:::
:::paragraph
复制底层迭代器的每个元素的迭代器组合器的大理石图如下所示：
```
it           ---a  ---b  ---c  ---d⊥
it.double    ---a-a---b-b---c-c---d-d⊥
```
:::
:::paragraph
{name}`Iter.filter` 的弹珠图显示了基础迭代器的某些元素如何不会出现在过滤迭代器中，而且当基础迭代器返回不满足谓词的值时，步进过滤迭代器会导致 {name PlausibleIterStep.skip}`skip`：
```
it            ---a--b--c--d-e--⊥
it.filter     ---a-----c-------⊥
```
该图需要注释：
>（假设 `f a = f c = true` 和 `f b = f d = d e = false`）
:::
:::paragraph
{name}`Iter.zip` 的图表显示了使用组合迭代器如何使用底层迭代器：
```
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```
只要 `left` 发出，压缩迭代器就会发出 {name PlausibleIterStep.skip}`skip`。
当 `left` 发出 `a` 时，压缩迭代器会再发出一个 {name PlausibleIterStep.skip}`skip`。
此后，压缩迭代器切换到消耗 `right`，并且只要 `right` 发出，它就会发出 {name PlausibleIterStep.skip}`skip`。
当 `right` 发出 `x` 时，压缩迭代器发出 `(a, x)` 对。
`left` 和 `right` 的这种交错一直持续到其中一个停止，此时压缩迭代器停止。
大理石图上行中的空白表示迭代器在该步骤中没有被消耗。
:::


## 纯组合器
%%%
tag := "zh-iterators-h016"
%%%

{docstring IterM.mk}

{docstring Iter.toIterM}

{docstring Iter.take}

{docstring Iter.takeWhile}

{docstring Iter.toTake}

{docstring Iter.drop}

{docstring Iter.dropWhile}

{docstring Iter.stepSize}

{docstring Iter.map}

{docstring Iter.mapM}

{docstring Iter.mapWithPostcondition}

{docstring Iter.uLift}

{docstring Iter.flatMap}

{docstring Iter.flatMapM}

{docstring Iter.flatMapAfter}

{docstring Iter.flatMapAfterM}

{docstring Iter.filter}

{docstring Iter.filterM}

{docstring Iter.filterWithPostcondition}

{docstring Iter.filterMap}

{docstring Iter.filterMapM}

{docstring Iter.filterMapWithPostcondition}

{docstring Iter.zip}

{docstring Iter.attachWith}


## 单子组合器
%%%
tag := "zh-iterators-h017"
%%%

{docstring IterM.toIter}

{docstring IterM.take}

{docstring IterM.takeWhile}

{docstring IterM.takeWhileM}

{docstring IterM.takeWhileWithPostcondition}

{docstring IterM.toTake}

{docstring IterM.drop}

{docstring IterM.dropWhile}

{docstring IterM.dropWhileM}

{docstring IterM.dropWhileWithPostcondition}

{docstring IterM.stepSize}

{docstring IterM.map}

{docstring IterM.mapM}

{docstring IterM.mapWithPostcondition}

{docstring IterM.uLift}

{docstring IterM.flatMap}

{docstring IterM.flatMapM}

{docstring IterM.flatMapAfter}

{docstring IterM.flatMapAfterM}

{docstring IterM.filter}

{docstring IterM.filterM}

{docstring IterM.filterWithPostcondition}

{docstring IterM.filterMap}

{docstring IterM.filterMapM}

{docstring IterM.filterMapWithPostcondition}

{docstring IterM.zip}

{docstring IterM.attachWith}

# 关于迭代器的推理
%%%
tag := "zh-iterators-h018"
%%%

## 关于消费者的推理
%%%
tag := "zh-iterators-h019"
%%%

迭代器库提供了大量有用的引理。
大多数关于有限迭代器的定理都可以通过将语句重写为关于列表的定理来证明，利用迭代器组合子和相应列表操作之间的对应关系已经被证明的事实。
在实践中，许多这样的定理已经被注册为 {tactic}`simp` 引理。

:::paragraph
引理有一个非常可预测的命名系统，许多引理都在 {tech}[默认 simp 集]中。
一些最重要的包括：

 * 诸如 {name}`Iter.all_toList`、{name}`Iter.any_toList` 和 {name}`Iter.foldl_toList` 之类的消费者引理将列表引入为模型。

 * 简化引理（例如 {name}`Iter.toList_map` 和 {name}`Iter.toList_filter`）将列表模型“向内”推向目标。

 * 生产者引理（例如 {name}`List.toList_iter` 和 {name}`Array.toList_iter`）用列表模型替换生产者，从目标中完全删除迭代器。

后两类通常是自动的，带有 {tactic}`simp`。
:::

:::example "Reasoning via Lists"
```imports -show
import Std.Data.Iterators
```
```lean -show
open Std
```
将其他迭代器消耗的数字乘以二的迭代器返回的每个元素都是偶数。
为了证明这一说法，使用 {name}`Iter.all_toList`、{name}`Iter.toList_map` 和 {name}`Array.toList_iter` 将有关迭代器的说法替换为有关列表的说法，然后 {tactic}`simp` 释放目标：
```lean
example (l : Array Nat) :
    (l.iter.map (· * 2)).all (· % 2 = 0) := by
  rw [← Iter.all_toList]
  rw [Iter.toList_map]
  rw [Array.toList_iter]
  simp
```

事实上，因为大多数所需的引理都在 {tech}[默认 simp 集]中，所以证明可以非常短：
```lean
example (l : Array Nat) :
    (l.iter.map (· * 2)).all (· % 2 = 0) := by
  simp [← Iter.all_toList]
```
:::

## 逐步推理
%%%
tag := "zh-iterators-h020"
%%%

当没有足够的引理来通过重写列表模型来证明属性时，可能有必要通过直接推理迭代器的步骤函数来证明有关迭代器的事情。
本节中的归纳原理对于逐步推理很有用。

{docstring Iter.inductSkips}

{docstring IterM.inductSkips}

{docstring Iter.inductSteps}

{docstring IterM.inductSteps}

标准库还包括所有生成器和组合器的逐步行为的引理。
示例包括 {name}`List.step_iter_nil`、{name}`List.step_iter_cons`、{name}`IterM.step_map`。

## 用于推理的 Monad
%%%
tag := "zh-iterators-h021"
%%%

{docstring Std.Iterators.PostconditionT}

{docstring Std.Iterators.PostconditionT.run}

{docstring Std.Iterators.PostconditionT.lift}

{docstring Std.Iterators.PostconditionT.liftWithProperty}

{docstring Iter.IsPlausibleIndirectOutput +allowMissing}

{docstring HetT}

{docstring IterM.stepAsHetT}

{docstring HetT.lift}

{docstring HetT.prun}

{docstring HetT.pure}

{docstring HetT.map}

{docstring HetT.pmap}

{docstring HetT.bind}

{docstring HetT.pbind}

## 等价
%%%
tag := "zh-iterators-h022"
%%%

迭代器等价性是根据迭代器的可观察行为而不是其实现来定义的。
特别是，内部状态被忽略。

{docstring Iter.Equiv}

{docstring IterM.Equiv}
