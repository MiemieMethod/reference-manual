/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

#doc (Manual) "嵌套归纳类型" =>
%%%
file := "Nested-Inductive-Types"
tag := "nested-inductive-types"
%%%

{deftech (key := "Nested inductive types")}_嵌套归纳类型_是归纳类型，其中所定义的类型的递归出现是其他归纳类型构造函数的参数。
这些递归出现“嵌套”在其他类型构造函数的下面。
满足一定要求的嵌套归纳类型可以转化为相互的归纳类型；这个翻译表明它们是合理的。
在内部，{tech (key := "kernel")}[内核] 执行此转换；如果成功，则接受_原始_嵌套的归纳类型。
这避免了翻译表面细节可能引起的性能和可用性问题。

:::paragraph
嵌套递归出现必须满足以下要求：
* 它们必须直接嵌套在归纳类型的类型构造函数下。
  不接受减少此类嵌套出现的术语。
* 局部变量（例如构造函数的参数）可能不会出现在嵌套出现的参数中。
* 嵌套事件必须严格正向发生。它们必须严格出现在它们嵌套的位置，并且它们嵌套的类型构造函数本身也必须出现在严格的正位置。
* 类型包含嵌套出现的构造函数参数不能以依赖于外部类型构造函数的特定选择的方式使用。翻译后的版本将无法在这些情况下使用。
* 嵌套出现不能用作外部类型索引类型中出现的外部类型构造函数的参数。
:::

:::example "Nested Inductive Types"
可以使用 {name}`Option` 定义自然数，而不是使用两个构造函数：
```lean
inductive ONat : Type where
  | mk (pred : Option ONat)
```

任意分支树，也称为_玫瑰树_，嵌套归纳类型：
```lean
inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : List (RTree α))
```
:::

:::::example "Invalid Nested Inductive Types"

这个任意分支玫瑰树的声明声明了 {name}`List` 的别名，而不是直接使用 {name}`List`：
```lean +error (name := viaAlias)
abbrev Children := List

inductive RTree (α : Type u) : Type u where
  | empty
  | node (val : α) (children : Children (RTree α))
```
```leanOutput viaAlias
(kernel) arg #3 of 'RTree.node' contains a non valid occurrence of the datatypes being declared
```

::::paragraph
:::leanSection
```lean -show
variable {n : Nat}
```
任意分支玫瑰树的声明使用索引跟踪树的深度。
构造函数 `DRTree.node` 有一个 {tech (key := "automatic implicit parameter")}[自动隐式参数] {lean}`n`，表示所有子树的深度。
但是，局部变量（例如构造函数参数）不允许作为嵌套出现的参数：
:::
```lean +error (name := localVar)
inductive DRTree (α : Type u) : Nat → Type u where
  | empty : DRTree α 0
  | node (val : α) (children : List (DRTree α n)) : DRTree α (n + 1)
```

::::

此声明包括嵌套在 {name}`Option` 下的归纳类型的非严格正数出现：
```lean +error (name := nonPos)
inductive WithCheck where
  | done
  | check (f : Option WithCheck → Bool)
```
```leanOutput nonPos
(kernel) arg #1 of 'WithCheck.check' has a non positive occurrence of the datatypes being declared
```

:::paragraph
这棵玫瑰树的分支因子受其参数限制：
```lean +error (name := brtree)
inductive BRTree (branches : Nat) (α : Type u) : Type u where
  | mk :
    (children : List (BRTree branches α)) →
    children.length < branches →
    BRTree branches α
```
仅允许可转换为相互归纳类型的嵌套归纳类型。
但是，转换此类型需要将 {name}`List.length` 转换为已转换类型，但函数定义可能不会出现在与归纳类型的交互块中。
生成的错误消息表明该函数未翻译，但应用于翻译类型的术语：
```leanOutput brtree
(kernel) application type mismatch
  List.length children
argument has type
  @_nested.List_1 branches α
but function has type
  List (@BRTree branches α) → Nat
```
可以将参数与完全多态函数的嵌套出现一起使用，例如 {name}`id`：
```lean (name := nondep)
inductive RTree'' (α : Type u) : Type u where
  | mk :
    (children : List (BRTree branches α)) →
    id children = children →
    BRTree branches α
```
在这种情况下，该函数同样适用于翻译版本和原始版本。
:::

:::paragraph
_palindrome_ 是颠倒后相同的列表：
```lean
inductive Palindrome (α : Type) : List α → Prop where
  | nil : Palindrome α []
  | single : Palindrome α [x]
  | cons (x : α) (p : Palindrome α xs) : Palindrome α (x :: xs ++ [x])
```
在这个谓词中，列表是一个索引，其类型取决于参数，为了清楚起见，参数是显式的。
这意味着它无法使用

:::
:::::

从嵌套归纳类型到相互归纳类型的转换过程如下：

: 嵌套出现变为归纳类型

  归纳类型的嵌套出现被转换为同一共同组中的新归纳类型，从而替换原始的嵌套出现。
  这些新的归纳类型具有与外部归纳类型相同的构造函数，只是原始参数由类型的翻译版本实例化。
  原始归纳类型成为嵌套出现已被重写的版本的别名。
  如果结果类型也是嵌套的归纳类型（例如，嵌套在 {name}`Array` 下的类型变为嵌套在 {name}`List` 下的类型，因为 {name}`Array` 的构造函数采用 {name}`List`），则重复此过程。

: 与嵌套类型之间的转换

  生成应用于新别名的外部归纳类型与生成的辅助类型之间的转换。
  然后证明这些转换是互逆的。

: 构造函数重构

  原始类型的每个构造函数都被定义为一个函数，该函数在应用适当的转换后返回翻译类型的构造函数。

: 递归重构

  嵌套归纳类型的递归器是根据转换类型的递归器构造的。
  在翻译中，嵌套事件的动机由转换函数组成，{tech (key := "minor premises")}[小前提]根据需要使用它们。
  需要证明转换函数互逆，因为编码的构造函数在一个方向上进行转换，但最终应用于另一个方向上的转换结果。


::::example "Translating Nested Inductive Types"
此嵌套归纳类型代表自然数：
```lean -keep
inductive ONat where
  | mk (pred : Option ONat) : ONat

#check ONat.rec
```

内部转换的第一步是用“内联”结果类型的辅助归纳类型替换嵌套出现的情况。
在本例中，嵌套出现位于 {name}`Option` 下；因此，辅助类型具有 {name}`Option` 的构造函数，并用 {name}`ONat'` 替换类型参数：
```lean
mutual
inductive ONat' where
  | mk (pred : OptONat) : ONat'

inductive OptONat where
  | none
  | some : ONat' → OptONat
end
```

{lean}`ONat'` 是 {lean}`ONat` 的编码：
```lean
def ONat := ONat'
```

下一步是定义转换函数，将原始嵌套类型与辅助类型相互转换：
```lean
def OptONat.ofOption : Option ONat → OptONat
  | Option.none => OptONat.none
  | Option.some o => OptONat.some o
def OptONat.toOption : OptONat → Option ONat
  | OptONat.none => Option.none
  | OptONat.some o => Option.some o
```

这些转换函数是互逆的：
```lean
def OptONat.to_of_eq_id o :
    OptONat.toOption (ofOption o) = o := by
  cases o <;> rfl
def OptONat.of_to_eq_id o :
    OptONat.ofOption (OptONat.toOption o) = o := by
  cases o <;> rfl
```

原始构造函数被转换为翻译对应构造函数的应用程序，并对嵌套出现应用适当的转换：
```lean
def ONat.mk (pred : Option ONat) : ONat :=
  ONat'.mk (.ofOption pred)
```

最后，可以翻译原始类型的递归器。
翻译后的递归器使用翻译后类型的递归器。
原始嵌套出现使用转换进行翻译，并且转换互逆的证明用于根据需要重写类型。
```lean
noncomputable def ONat.rec
    {motive1 : ONat → Sort u}
    {motive2 : Option ONat → Sort u}
    (h1 :
      (pred : Option ONat) → motive2 pred →
      motive1 (ONat.mk pred))
    (h2 : motive2 none)
    (h3 : (o : ONat) → motive1 o → motive2 (some o)) :
    (t : ONat) → motive1 t :=
  @ONat'.rec motive1 (motive2 ∘ OptONat.toOption)
    (fun pred ih =>
      OptONat.of_to_eq_id pred ▸ h1 pred.toOption ih)
    h2
    h3
```
::::
