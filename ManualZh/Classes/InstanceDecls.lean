/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "实例声明" =>
%%%
tag := "instance-declarations"
%%%


实例声明的语法几乎与定义的语法相同。
唯一的语法差异是关键字 {keywordOf Lean.Parser.Command.declaration}`def` 替换为 {keywordOf Lean.Parser.Command.declaration}`instance` 并且名称是可选的：

:::syntax Lean.Parser.Command.instance (title := "Instance Declarations")

大多数实例使用 {keywordOf Lean.Parser.Command.declaration}`where` 语法定义每个方法：

```grammar
instance $[(priority := $p:prio)]? $name? $_ where
  $_*
```

但是，类型类是归纳类型，因此可以使用具有适当类型的任何表达式来构造实例：

```grammar
instance $[(priority := $p:prio)]? $_? $_ :=
  $_
```

实例也可以通过案例来定义；但是，此功能很少在 {name}`Decidable` 实例之外使用：

```grammar
instance $[(priority := $p:prio)]? $_? $_
  $[| $_ => $_]*
```

:::

使用显式术语定义的实例通常包含包装方法实现的匿名构造函数 ({keywordOf Lean.Parser.Term.anonymousCtor}`⟨...⟩`) 或定义等价类型上的 {name}`inferInstanceAs` 调用。

实例的精化几乎与普通定义的精化相同，但下面记录的注意事项除外。
如果未提供名称，则会自动创建一个名称。
可以直接引用这个生成的名称，但是用于生成名称的算法过去已经发生变化，并且将来可能会发生变化。
最好明确命名将直接引用的实例。
在精化之后，新实例被注册为实例搜索的候选者。
将属性 {attr}`instance` 添加到名称可用于将任何其他定义的名称标记为候选名称。

::::keepEnv
:::example "Instance Name Generation"

遵循这些声明：
```lean
structure NatWrapper where
  val : Nat

instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y
```

名称 {lean}`instBEqNatWrapper` 指的是新实例。
:::
::::

::::keepEnv
:::example "Variations in Instance Definitions"

给定这种结构类型：
```lean
structure NatWrapper where
  val : Nat
```
以下所有定义 {name}`BEq` 实例的方法都是等效的：
```lean
instance : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```

除了在环境中引入不同的名称之外，以下内容也是等效的：
```lean
@[instance]
def instBeqNatWrapper : BEq NatWrapper where
  beq
    | ⟨x⟩, ⟨y⟩ => x == y

instance : BEq NatWrapper :=
  ⟨fun x y => x.val == y.val⟩

instance : BEq NatWrapper :=
  ⟨fun ⟨x⟩ ⟨y⟩ => x == y⟩
```
:::
::::

# 递归实例
%%%
tag := "recursive-instances"
%%%

{keywordOf Lean.Parser.Command.declaration}`where` 结构定义语法中定义的函数不是递归的。
因为实例声明是结构定义的一个版本，所以默认情况下类型类方法也不是递归的。
然而，递归归纳类型的实例很常见。
有一个标准习惯用法可以解决此限制：独立于实例定义递归函数，然后在实例定义中引用它。
按照约定，这些递归函数具有相应方法的名称，但在类型的命名空间中定义。

:::example "Instances are not recursive"
鉴于 {lean}`NatTree` 的定义：
```lean
inductive NatTree where
  | leaf
  | branch (left : NatTree) (val : Nat) (right : NatTree)
```
以下 {name}`BEq` 实例失败：
```lean +error (name := beqNatTreeFail)
instance : BEq NatTree where
  beq
    | .leaf, .leaf =>
      true
    | .branch l1 v1 r1, .branch l2 v2 r2 =>
      l1 == l2 && v1 == v2 && r1 == r2
    | _, _ =>
      false
```
左右递归调用均出现错误：
```leanOutput beqNatTreeFail
failed to synthesize instance of type class
  BEq NatTree

Hint: Adding the command `deriving instance BEq for NatTree` may allow Lean to derive the missing instance.
```
给定一个合适的递归函数，例如 {lean}`NatTree.beq`：
```lean
def NatTree.beq : NatTree → NatTree → Bool
  | .leaf, .leaf =>
    true
  | .branch l1 v1 r1, .branch l2 v2 r2 =>
    NatTree.beq l1 l2 && v1 == v2 && NatTree.beq r1 r2
  | _, _ =>
    false
```
可以在第二步中创建实例：
```lean
instance : BEq NatTree where
  beq := NatTree.beq
```
或者，等效地，使用匿名构造函数语法：
```lean
instance : BEq NatTree := ⟨NatTree.beq⟩
```
:::

此外，实例在其自己的定义期间不可用于实例合成。
它们在定义后首先被标记为可用于实例合成。
嵌套归纳类型（其中类型的递归出现作为某个其他归纳类型的参数）可能需要一个可用的实例，甚至可以编写递归函数。
解决此限制的标准习惯用法是在递归定义的函数中创建本地实例，其中包含对正在定义的函数的引用，利用实例合成可以使用本地上下文中具有正确类型的每个绑定这一事实。


::: example "Instances for nested types"
在 {lean}`NatRoseTree` 的此定义中，所定义的类型嵌套在另一个归纳类型构造函数 ({name}`Array`) 下：
```lean
inductive NatRoseTree where
  | node (val : Nat) (children : Array NatRoseTree)

```
检查玫瑰树的相等性需要检查数组的相等性。
但是，实例在其自己的定义期间通常不可用于实例综合，因此即使 {lean}`NatRoseTree.beq` 是递归函数并且在其自己的定义范围内，以下定义也会失败。
```lean +error (name := natRoseTreeBEqFail) -keep
def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    val1 == val2 &&
    children1 == children2
```
```leanOutput natRoseTreeBEqFail
failed to synthesize instance of type class
  BEq (Array NatRoseTree)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

为了解决这个问题，本地 {lean}`BEq NatRoseTree` 实例可能是 `let` 绑定的：

```lean
partial def NatRoseTree.beq : (tree1 tree2 : NatRoseTree) → Bool
  | .node val1 children1, .node val2 children2 =>
    let _ : BEq NatRoseTree := ⟨NatRoseTree.beq⟩
    val1 == val2 &&
    children1 == children2
```
在实例合成期间，对子级使用数组相等来查找 let 绑定实例。
:::

# `class inductive` 的实例
%%%
tag := "class-inductive-instances"
%%%

许多实例具有函数类型：任何本身递归调用实例搜索的实例都是一个函数，任何具有隐式参数的实例也是如此。
虽然大多数实例仅从其自己的实例参数投影方法实现，但类归纳类型的实例通常会对其一个或多个参数进行模式匹配，从而允许实例选择适当的构造函数。
这是使用普通的 Lean 函数语法完成的。
与其他实例一样，所讨论的函数不可用于其自身定义中的实例综合。
::::keepEnv
:::example "An instance for a sum class"
```lean -show
axiom α : Type
```
由于 {lean}`DecidableEq α` 是 {lean}`(a b : α) → Decidable (Eq a b)` 的缩写，因此可以直接使用其参数，如下例所示：

```lean
inductive ThreeChoices where
  | yes | no | maybe

instance : DecidableEq ThreeChoices
  | .yes,   .yes   =>
    .isTrue rfl
  | .no,    .no    =>
    .isTrue rfl
  | .maybe, .maybe =>
    .isTrue rfl
  | .yes,   .maybe | .yes,   .no
  | .maybe, .yes   | .maybe, .no
  | .no,    .yes   | .no,    .maybe =>
    .isFalse nofun

```

:::
::::

::::keepEnv
:::example "A recursive instance for a sum class"
类型 {lean}`StringList` 表示单态字符串列表：
```lean
inductive StringList where
  | nil
  | cons (hd : String) (tl : StringList)
```
在以下定义 {name}`DecidableEq` 实例的尝试中，在详细说明内部 {keywordOf termIfThenElse}`if` 时调用的实例综合失败，因为该实例不可用于其自己的定义中的实例综合：
```lean +error (name := stringListNoRec) -keep
instance : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
```leanOutput stringListNoRec
failed to synthesize instance of type class
  Decidable (t1 = t2)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
但是，因为它是一个普通的 Lean 函数，所以它可以递归引用它自己显式提供的名称：
```lean
instance instDecidableEqStringList : DecidableEq StringList
  | .nil, .nil => .isTrue rfl
  | .cons h1 t1, .cons h2 t2 =>
    let _ : Decidable (t1 = t2) :=
      instDecidableEqStringList t1 t2
    if h : h1 = h2 then
      if h' : t1 = t2 then
        .isTrue (by simp [*])
      else
        .isFalse (by intro hEq; cases hEq; trivial)
    else
      .isFalse (by intro hEq; cases hEq; trivial)
  | .nil, .cons _ _ | .cons _ _, .nil => .isFalse nofun
```
:::
::::


# 实例优先级
%%%
tag := "instance-priorities"
%%%

实例可以被分配{deftech}_priorities_。
实例合成时优先选择优先级高的实例；实例综合的详细信息请参见{ref "instance-synth"}[实例综​​合部分]。

:::syntax prio -open (title := "Instance Priorities")
优先级可以是数字：
```grammar
$n:num
```

如果未指定优先级，则使用与 {evalPrio}`default` 对应的默认优先级：
```grammar
default
```

当数值太细粒度时，可以使用三个命名优先级，分别对应于 {evalPrio}`low`、{evalPrio}`mid` 和 {evalPrio}`high`。
{keywordOf prioMid}`mid` 优先级低于 {keywordOf prioDefault}`default`。
```grammar
low
```
```grammar
mid
```
```grammar
high
```

最后，优先级可以进行加减操作，因此`default + 2`是有效的优先级，对应于{evalPrio}`default + 2`：
```grammar
($_)
```
```grammar
$_ + $_
```
```grammar
$_ - $_
```

:::

# 默认实例
%%%
tag := "default-instances"
%%%

{attr}`default_instance` 属性指定实例 {ref "default-instance-synth"}[应在没有足够信息来选择它的情况下用作后备]。
如果未指定优先级，则使用默认优先级 `default`。

:::syntax attr (title := "The {keyword}`default_instance` Attribute")
```grammar
default_instance $p?
```
:::

:::::keepEnv
::::example "Default Instances"
{lean}`OfNat Nat` 的默认实例用于在没有其他类型信息的情况下为自然数文字选择 {lean}`Nat`。
它在 Lean 标准库中声明，优先级为 100。
给定偶数的表示，其中偶数由其一半表示：
```lean
structure Even where
  half : Nat
```

以下实例允许将数字文字用于较小的 {lean}`Even` 值（类型类实例搜索深度的限制阻止它们用于任意大的文字）：
```lean (name := insts)
instance ofNatEven0 : OfNat Even 0 where
  ofNat := ⟨0⟩

instance ofNatEvenPlusTwo [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := ⟨(OfNat.ofNat n : Even).half + 1⟩

#eval (0 : Even)
#eval (34 : Even)
#eval (254 : Even)
```
```leanOutput insts
{ half := 0 }
```
```leanOutput insts
{ half := 17 }
```
```leanOutput insts
{ half := 127 }
```

将它们指定为优先级大于或等于 100 的默认实例会导致使用它们而不是 {lean}`Nat`：
```lean
attribute [default_instance 100] ofNatEven0
attribute [default_instance 100] ofNatEvenPlusTwo
```
```lean (name := withDefaults)
#eval 0
#eval 34
```
```leanOutput withDefaults
{ half := 0 }
```
```leanOutput withDefaults
{ half := 17 }
```

非偶数仍然使用 {lean}`OfNat Nat` 实例：
```lean (name := stillNat)
#eval 5
```
```leanOutput stillNat
5
```
::::
:::::

# 实例属性
%%%
tag := "instance-attribute"
%%%

{attr}`instance` 属性将名称声明为具有指定优先级的实例。
与其他属性一样，{attr}`instance` 可以全局应用、本地应用或仅在当前命名空间打开时应用。
{keywordOf Lean.Parser.Command.declaration}`instance` 声明是一种自动应用 {attr}`instance` 属性的定义形式。

:::syntax attr (title := "The `instance` Attribute")

声明它所应用到的定义是一个实例。
如果未提供优先级，则使用默认优先级 `default`。

```grammar
instance $p?
```


:::
