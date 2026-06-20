/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.Language.Functions
import ManualZh.Language.InductiveTypes

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "商数" =>
%%%
tag := "quotients"
%%%


{deftech (key := "Quotient types")}_商类型_允许通过减小现有类型的 {tech (key := "propositional equality")}[命题等价] 的粒度来形成新类型。
特别是，给定类型 $`A` 和等价关系 $`\sim`，商 $`A / \sim` 包含与 $`A` 相同的元素，但与 $`\sim` 相关的每对元素都被视为相等。
平等受到普遍尊重； Lean 的逻辑中没有任何内容可以观察到两个相等项之间的任何差异。
因此，商类型提供了一种构建难以逾越的抽象障碍的方法。
特别是，商类型的所有函数都必须证明它们遵循等价关系。

{docstring Quotient}

证明基础类型的两个元素通过等价关系相关就足以证明它们在 {name}`Quotient` 中相等。
但是，{tech (key := "definitional equality")}[定义等价] 不受使用 {lean}`Quotient` 的影响：商中的两个元素定义等价当且仅当它们在基础类型中定义等价时。

:::paragraph
商类型在编程中并未广泛使用。
然而，它们在数学中经常出现：

: 整数

  这些整数传统上定义为一对自然数$`(n, k)`，对整数 $`n - k` 进行编码。
  在此编码中，如果 $`n_1 + k_2 = n_2 + k_1`，则两个整数 $`(n_1, k_1)` 和 $`(n_2, k_2)` 相等。

: 有理数

  编号 $`\frac{n}{d}` can be encoded as the pair $`(n, d)`，其中 $`d \neq 0`。
  两个有理数 $`\frac{n_1}{d_1}` and $`\frac{n_2}{d_2}` are equal if $`n_1 d_2 = n_2 d_1`。

: 实数

  实数可以表示为柯西序列，但这种编码不是唯一的。
  使用商类型，当两个柯西序列的差值收敛到零时，可以使它们相等。

: 有限集

  有限集可以表示为元素列表。
  对于商类型，如果两个有限集包含相同的元素，则它们可以相等；该定义不对元素的类型强加任何要求（例如可判定的相等性或排序关系）。

:::


商类型的一种替代方法是直接推理关系引入的等价类。
这种方法的缺点是它不允许进行计算：除了知道存在一个整数是 5 与 8 的和之外，知道 $`5 + 8 = 13` 并不是一个需要证明的定理也很有用。
从等价类集合中定义函数依赖于非计算经典推理原理，而商类型的函数是额外遵循等价关系的普通计算函数。

# 商类型的替代方案
%%%
tag := "quotient-alternatives"
%%%

虽然 {name}`Quotient` 是形成具有合理计算属性的商的便捷方法，但通常也可以通过其他方式定义商。

一般来说，如果类型 $`Q` 遵循商的通用属性，则通过等价关系 $`\sim` 可以将类型 $`Q` 称为 $`A` 的商：存在一个函数 $`q:A\to Q`，其属性为 $`q(a)=q(b)` 当且仅当 $`a\sim b` 对于所有$`a` 和 $`b` 位于 $`A` 中。

由 {name}`Quotient` 形成的商在 {tech (key := "propositional equality")}[命题等价] 范围内具有此属性：与 $`\sim` 相关的 $`A` 的元素相等，因此无法区分它们。
但是，同一等价类的成员的商不一定是 {tech (key := "definitional equality")}[定义等价]。

商还可以通过在 $`A` 本身中指定每个等价类的单个代表，然后将 $`Q` 定义为 $`A` 中的元素对并证明它们是这样的规范代表来实现。
与将 $`A` 中的每个 $`a` 映射到其规范代表的函数一起，$`Q` 是 $`A` 的商。
由于{tech (key := "proof irrelevance")}[证明无关]，同一等价类的$`Q`中的代表是{tech (key := "definitional equality")}[定义等价]。

这种手动实现的商 $`Q` 比 {name}`Quotient` 更容易使用。
特别是，因为每个等价类都由其单个规范代表表示，所以无需证明商的函数遵循等价关系。
由于计算给出归一化值，它还可以具有更好的计算属性（相反，{name}`Quotient` 的元素可以用多种方式表示）。
最后，由于手动实现的商是 {tech (key := "inductive type")}[归纳类型]，因此它可以在其他类型不能使用的上下文中使用，例如定义 {ref "nested-inductive-types"}[嵌套归纳类型] 时。
然而，并非所有商都可以手动实现。


:::example "Manually Quotiented Integers"
当作为一对 {lean}`Nat` 实现时，根据所需的整数相等性，每个等价类都具有一个规范表示，其中 {lean}`Nat` 中至少有一个为零。
这可以表示为 Lean 结构：
```lean
structure Z where
  a : Nat
  b : Nat
  canonical : a = 0 ∨ b = 0
```
由于 {tech (key := "proof irrelevance")}[证明无关性]，表示相同整数的该结构类型的每个值已经相等。
使用包装器可以更方便地构建 {lean}`Z`，该包装器利用自然数的减法在零处截断的事实来自动构建证明：
```lean
def Z.mk' (n k : Nat) : Z where
  a := n - k
  b := k - n
  canonical := by omega
```

这种构造尊重整数的相等要求：
```lean
theorem Z_mk'_respects_eq :
    (Z.mk' n k = Z.mk' n' k') ↔ (n + k' = n' + k) := by
  simp [Z.mk']
  omega
```

要在示例中使用此类型，拥有 {name}`Neg`、{name}`OfNat` 和 {name}`ToString` 实例会很方便。
这些实例使阅读或编写示例变得更加容易。

```lean
instance : Neg Z where
  neg n := Z.mk' n.b n.a

instance : OfNat Z n where
  ofNat := Z.mk' n 0

instance : ToString Z where
  toString n :=
    if n.a = 0 then
      if n.b = 0 then "0"
      else s!"-{n.b}"
    else toString n.a
```
```lean (name := intFive)
#eval (5 : Z)
```
```leanOutput intFive
5
```
```lean (name := intMinusFive)
#eval (-5 : Z)
```
```leanOutput intMinusFive
-5
```


加法是基础 {lean}`Nat` 的加法：
```lean
instance : Add Z where
  add n k := Z.mk' (n.a + k.a) (n.b + k.b)
```

```lean (name := addInt)
#eval (-5 + 22: Z)
```
```leanOutput addInt
17
```

由于每个等价类都是唯一表示的，因此无需编写 {lean}`Z` 中的这些函数遵循等价关系的证明。
然而，在实践中，{ref "quotient-api"}[API 对于商]应该针对手动构造的商实现，并证明尊重通用属性。

:::

:::example "Built-In Integers as Quotients"

Lean 的内置整数类型 {lean}`Int` 满足商的通用性质，因此可以将其视为 {lean}`Nat` 对的商。
每个等价类的规范代表可以通过比较和减法来计算：{margin}[这个{lean}`toInt`函数在标准库中称为{name}`Int.subNatNat`。]
```lean
def toInt (n k : Nat) : Int :=
  if n < k then - (k - n : Nat)
  else if n = k then 0
  else (n - k : Nat)
```

它满足普遍性质。
当且仅当 {lean}`toInt` 为两对 {lean}`Int` 计算相同的 {lean}`Int` 时，两对 {lean}`Nat` 表示相同的整数：
```lean
theorem toInt_sound :
    n + k' = k + n' ↔
    toInt n k = toInt n' k' := by
  simp only [toInt]
  split <;> split <;> omega
```
:::

# 类固醇
%%%
tag := "setoids"
%%%

商类型是建立在 setoid 之上的。
{deftech}_setoid_ 是与区分的等价关系配对的类型。
与商类型不同，不强制执行抽象障碍，并且围绕相等性设计的证明自动化不能与 setoid 的等价关系一起使用。
Setoid 除了作为商类型的构建块之外，本身也很有用。

{docstring Setoid}

{docstring Setoid.refl}

{docstring Setoid.symm}

{docstring Setoid.trans}

# 等价关系
%%%
tag := "equivalence-relations"
%%%

{deftech (key := "equivalence relation")}_等价关系_是自反、对称和传递的关系。

:::syntax term (title := "Equivalence Relations")
根据类型的某些规范等价关系的等价性是使用 `≈` 编写的，它是使用 {tech (key := "type class")}[类型类] {name}`HasEquiv` 重载的。
```grammar
$_ ≈ $_
```
:::

{docstring HasEquiv}

```lean -show
section
variable (r : α → α → Prop)
```

关系 {lean}`r` 实际上是等价关系，这一事实被声明为 {lean}`Equivalence r`。

{docstring Equivalence}

```lean -show
end
```

每个 {name}`Setoid` 实例都会导致一个对应的 {name}`HasEquiv` 实例。

```lean -show
-- Check preceding para
section
variable {α : Sort u} [Setoid α]
/-- info: instHasEquivOfSetoid -/
#check_msgs in
#synth HasEquiv α
end
```

# 商 API
%%%
tag := "quotient-api"
%%%

商 API 依赖于预先存在的 {name}`Setoid` 实例。

## 商数介绍
%%%
tag := "quotient-intro"
%%%


类型 {lean}`Quotient` 需要 {lean}`Setoid` 的实例作为普通参数，而不是作为 {tech (key := "instance implicit")}[实例隐式] 参数。
这有助于确保商使用预期的等价关系。
可以通过命名实例或使用 {name}`inferInstance` 来提供实例。

商中的值是来自 setoid 基础类型的值，包装在 {lean}`Quotient.mk` 中。

{docstring Quotient.mk}

{docstring Quotient.mk'}

:::example "The Integers as a Quotient Type"
整数定义为自然数对，其中表示的整数是两个数字的差，可以通过商类型表示。
这种表示形式并不唯一：{lean}`(4, 7)` 和 {lean}`(1, 4)` 均表示 {lean  (type := "Int")}`-3`。

当两个编码整数通过 {name}`Z.eq` 相关时，应将其视为相等：

```lean
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1
```

这个关系是一个等价关系：
```lean
def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega
```

因此，它可以用作 {name}`Setoid`：
```lean
instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv
```

整数类型 {lean}`Z` 就是 {lean}`Z'` 除以 {name}`Setoid` 实例的商：

```lean
def Z : Type := Quotient Z.instSetoid
```

帮助程序 {lean}`Z.mk` 使创建整数变得更简单，而无需担心 {name}`Setoid` 实例的选择：
```lean
def Z.mk (n : Z') : Z := Quotient.mk _ n
```

然而，数字文字更方便。
{name}`OfNat` 实例允许将数字文字用于整数：
```lean
instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```
:::



## 消除商数
%%%
tag := "quotient-elim"
%%%


商的函数可以通过证明基础类型的函数遵循商的等价关系来定义。
这是使用 {lean}`Quotient.lift` 或其二进制对应物 {lean}`Quotient.lift₂` 来完成的。
变体 {lean}`Quotient.liftOn` 和 {lean}`Quotient.liftOn₂` 将商参数放在参数列表中的第一个而不是最后一个。

{docstring Quotient.lift}

{docstring Quotient.liftOn}

{docstring Quotient.lift₂}

{docstring Quotient.liftOn₂}

:::example "Integer Negation and Addition"

```lean -show
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    omega
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    omega

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n
```

给定整数的编码 {lean}`Z` 作为自然数对的商，可以通过交换第一个和第二个投影来实现求反：
```lean
def neg' : Z' → Z
  | (x, y) => .mk (y, x)
```

通过证明否定遵循等价关系，可以将其转换为从 {lean}`Z` 到 {lean}`Z` 的函数：
```lean
instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      cases n; cases k
      apply Quotient.sound
      simp [· ≈ ·, instHasEquivOfSetoid, Setoid.r, Z.eq] at *
      grind

```

同样，{lean}`Quotient.lift₂` 对于从商类型定义二元函数很有用。
加法是逐点定义的：
```lean
def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)
```

将其提升为商需要证明加法遵循等价关系：
```lean
instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, instHasEquivOfSetoid, Setoid.r, Z.eq]
      grind
```
:::

当函数的结果类型为 {tech}[subsingleton] 时，可使用 {name}`Quotient.recOnSubsingleton` 或 {name}`Quotient.recOnSubsingleton₂` 来定义函数。
因为子单例的所有元素都是相等的，所以这样的函数自动遵守等价关系，因此没有证明义务。

{docstring Quotient.recOnSubsingleton}

{docstring Quotient.recOnSubsingleton₂}

## 关于商的证明
%%%
tag := "quotient-proofs"
%%%


证明商类型元素属性的基本工具是健全性公理和归纳原理。
健全性公理指出，如果基础类型的两个元素通过商的等价关系相关，则它们在商类型中相等。
归纳原理遵循归纳类型的递归结构：为了证明谓词包含商类型的所有元素，只需证明它适用于将 {name}`Quotient.mk` 应用于基础类型的每个元素即可。
由于 {name}`Quotient` 不是 {tech (key := "inductive type")}[归纳类型]，因此策略（例如 {tactic}`cases` 和 {tactic}`induction`）要求使用 {keyword}`using` 修饰符显式指定 {name}`Quotient.ind`。

{docstring Quotient.sound}

{docstring Quotient.ind}

:::example "Proofs About Quotients"

```lean -show
def Z' : Type := Nat × Nat

def Z.eq (n k : Z') : Prop :=
  n.1 + k.2 = n.2 + k.1

def Z.eq.eqv : Equivalence Z.eq where
  refl := by
    intro (x, y)
    simp +arith [eq]
  symm := by
    intro (x, y) (x', y') heq
    simp_all only [eq]
    grind
  trans := by
    intro (x, y) (x', y') (x'', y'')
    intro heq1 heq2
    simp_all only [eq]
    grind

instance Z.instSetoid : Setoid Z' where
  r := Z.eq
  iseqv := Z.eq.eqv

def Z : Type := Quotient Z.instSetoid

def Z.mk (n : Z') : Z := Quotient.mk _ n

def neg' : Z' → Z
  | (x, y) => .mk (y, x)

instance : Neg Z where
  neg :=
    Quotient.lift neg' <| by
      intro n k equiv
      apply Quotient.sound
      simp only [· ≈ ·, instHasEquivOfSetoid, Setoid.r, Z.eq] at *
      grind

def add' (n k : Nat × Nat) : Z :=
  .mk (n.1 + k.1, n.2 + k.2)

instance : Add Z where
  add (n : Z) :=
    n.lift₂ add' <| by
      intro n k n' k'
      intro heq heq'
      apply Quotient.sound
      cases n; cases k; cases n'; cases k'
      simp_all only [· ≈ ·, instHasEquivOfSetoid, Setoid.r, Z.eq]
      grind

instance : OfNat Z n where
  ofNat := Z.mk (n, 0)
```

考虑到前面示例中将整数定义为商类型，{name}`Quotient.ind` 和 {name}`Quotient.sound` 可用于证明负数是加法逆元。
首先，{lean}`Quotient.ind` 用于将 `n` 的实例替换为 {name}`Quotient.mk` 的应用程序。
完成此操作后，通过 {name}`Quotient.lift` 的展开定义和计算规则，等式的左侧在定义上变得等于 {name}`Quotient.mk` 的单个应用程序。
这使得 {name}`Quotient.sound` 变得适用，从而产生了一个新的目标：表明双方通过等价关系相关。
这可以使用 {tactic}`simp_arith` 来证明。

```lean
theorem Z.add_neg_inverse (n : Z) : n  + (-n) = 0 := by
  cases n using Quotient.ind
  apply Quotient.sound
  simp +arith [· ≈ ·, instHasEquivOfSetoid, Setoid.r, eq]
```

:::

对于更专业的用例，{name}`Quotient.rec`、{name}`Quotient.recOn` 和 {name}`Quotient.hrecOn` 可用于定义从商类型到任何其他 Universe 中的类型的依赖函数。
声明依赖函数遵循商的等价关系需要一种方法来处理依赖结果类型是用等式两边的商的不同值实例化这一事实的。
{name}`Quotient.rec` 和 {name}`Quotient.recOn` 使用 {name}`Quotient.sound` 使相关元素相等，将适当的转换插入到相等语句中，而 {name}`Quotient.hrecOn` 使用异构相等。

{docstring Quotient.rec}

{docstring Quotient.recOn}

{docstring Quotient.hrecOn}

如果某个类型的两个元素的商相等，则它们通过 setoid 的等价关系相关。
该属性称为 {name}`Quotient.exact`。

{docstring Quotient.exact}



# 逻辑模型
%%%
tag := "quotient-model"
%%%


与函数和宇宙一样，商类型是 Lean 类型系统的内置功能。
但是，底层原语基于稍微简单的 {name}`Quot` 类型，而不是 {name}`Quotient`，并且 {name}`Quotient` 是根据 {name}`Quot` 定义的。
主要区别在于 {name}`Quot` 基于任意关系，而不是 {name}`Setoid` 实例。
所提供的关系不必是等价关系；管理 {name}`Quot` 和 {name}`Eq` 的规则自动将所提供的关系扩展为其自反、传递、对称闭包。
当关系已经是等价关系时，应使用 {name}`Quotient` 代替 {name}`Quot`，以便 Lean 可以利用该关系是等价关系的事实。

基本商类型 API 由 {lean}`Quot`、{name}`Quot.mk`、{name}`Quot.lift`、{name}`Quot.ind` 和 {name}`Quot.sound` 组成。
它们的使用方式与基于 {name}`Quotient` 的对应产品相同。

{docstring Quot}

{docstring Quot.mk}

{docstring Quot.lift}

{docstring Quot.ind}

{docstring Quot.sound}

## 商约减
%%%
tag := "quotient-reduction"
%%%

```lean -show
section
variable
  (α β : Sort u)
  (r : α → α → Prop)
  (f : α → β)
  (resp : ∀ x y, r x y → f x = f y)
  (x : α)
```
除了上述常量之外，Lean 的内核还包含 {name}`Quot.lift` 的缩减规则，该规则导致其与 {name}`Quot.mk` 一起使用时缩减，类似于归纳类型的 {tech (key := "ι-reduction")}[ι-缩减]。
给定 {lean}`r` 与 {lean}`α` 的关系，从 {lean}`α` 到 {lean}`β` 的函数 {lean}`f`，以及 {lean}`resp` 证明 {lean}`f` 尊重 {lean}`r`，术语{lean}`Quot.lift f resp (Quot.mk r x)` 是 {tech (key := "definitional equality")}[定义等于] {lean}`f x`。

```lean -show
end
```

```lean -show
section
```

```lean
variable
  (r : α → α → Prop)
  (f : α → β)
  (ok : ∀ x y, r x y → f x = f y)
  (x : α)

example : Quot.lift f ok (Quot.mk r x) = f x := rfl
```

```lean -show
end
```

## 商和归纳类型
%%%
tag := "quotients-nested-inductives"
%%%

由于 {name}`Quot` 不是归纳类型，因此作为商实现的类型可能不会出现在归纳类型声明中的 {ref "nested-inductive-types"}[嵌套出现次数] 周围。
必须重写这些类型声明以删除嵌套商，这通常可以通过定义无商版本，然后单独定义实现所需相等关系的等价关系来完成。

:::example "Nested Inductive Types and Quotients"

玫瑰树的嵌套归纳类型将 {lean}`RoseTree` 的递归出现嵌套在 {lean}`List` 下：
```lean
inductive RoseTree (α : Type u) where
  | leaf : α → RoseTree α
  | branch : List (RoseTree α) → RoseTree α
```

但是，对标识 {ref "squash-types"}[squash types] 样式的所有元素的 {name}`List` 进行商会导致 Lean 拒绝该声明：
```lean +error (name := nestedquot)
inductive SetTree (α : Type u) where
  | leaf : α → SetTree α
  | branch :
    Quot (fun (xs ys : List (SetTree α)) => True) →
    SetTree α
```
```leanOutput nestedquot
(kernel) arg #2 of 'SetTree.branch' contains a non valid occurrence of the datatypes being declared
```

:::

## 低级商 API
%%%
tag := "zh-quotients-h011"
%%%

{name}`Quot.liftOn` 是 {name}`Quot.lift` 的一个版本，它首先取商类型的值，类似于 {name}`Quotient.liftOn`。

{docstring Quot.liftOn}

Lean 还提供从 {name}`Quot` 到任何子单例的便捷消除，无需进一步的证明义务，以及与 {name}`Quotient` 所使用的相关消除原则相对应的相关消除原则。

{docstring Quot.recOnSubsingleton}

{docstring Quot.rec}

{docstring Quot.recOn}

{docstring Quot.hrecOn}


# 商和函数外延
%%%
tag := "quotient-funext"
%%%

:::::keepEnv

由于 Lean 的 定义等价 包含 {lean}`Quot.lift` 的计算归约规则，因此标准库中使用商类型来证明函数外延性，否则需要为 {ref "axioms"}[axiom]。
这是通过首先定义一种由外延相等引用的函数类型来完成的，对于该函数，外延相等根据定义成立。

```lean
variable {α : Sort u} {β : α → Sort v}

def extEq (f g : (x : α) → β x) : Prop :=
  ∀ x, f x = g x

def ExtFun (α : Sort u) (β : α → Sort v) :=
  Quot (@extEq α β)
```

扩展函数可以像普通函数一样应用。
根据定义，应用程序尊重外延平等：如果应用于函数会产生相同的结果，那么应用它们会产生相同的结果。
```lean
def extApp
    (f : ExtFun α β)
    (x : α) :
    β x :=
  f.lift (· x) fun g g' h => by
    exact h x
```

```lean -show
section
variable (f : (x : α) → β x)
```
为了证明两个外延相等的函数实际上相等，只需证明外延应用相应的外延函数所得到的函数是相等的即可。
这是因为
```leanTerm
extApp (Quot.mk _ f)
```
定义上等于
```leanTerm
fun x => (Quot.mk extEq f).lift (· x) (fun _ _ h => h x)
```
它定义上等于 {lean}`fun x => f x`，它定义上等于（通过 {tech (key := "η-equivalence")}[η-等价]）{lean}`f`。
{name}`Quot.lift` 的计算规则的命题版本是不够的，因为可约表达式出现在函数体中，并且通过函数中的等式重写已经需要函数外延性。

```lean -show
end
```

从这里，足以表明两个函数的扩展版本是相等的。
由于 {name}`Quot.sound`，这是正确的：它们处于商的等价关系中这一事实是一个假设。
该证明是标准库中的证明的更明确的版本：

```lean
theorem funext'
    {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) :
    f = g := by
  suffices extApp (Quot.mk _ f) = extApp (Quot.mk _ g) by
    unfold extApp at this
    dsimp at this
    exact this
  suffices Quot.mk extEq f = Quot.mk extEq g by
    apply congrArg
    exact this
  apply Quot.sound
  exact h
```

:::::

# 壁球类型
%%%
tag := "squash-types"
%%%

```lean -show
section
variable {α : Sort u}
```
Squash 类型是通过关联所有元素的关系得出的商，将其转换为 {tech}[subsingleton]。
换句话说，如果 {lean}`α` 是有人居住的，那么 {lean}`Squash α` 就有一个元素，如果 {lean}`α` 无人居住，那么 {lean}`Squash α` 也是无人居住的。
{lean}`Nonempty α` 是一个命题，声明 {lean}`α` 已被占用，因此在运行时由虚拟值表示，而 {lean}`Squash α` 与 {lean}`Squash α` 不同，{lean}`Squash α` 是与 {lean}`α` 表示相同的类型。
由于{lean}`Squash α`与{lean}`α`在同一个宇宙中，因此它不受命题计算数据的限制。

```lean -show
end
```

{docstring Squash}

{docstring Squash.mk}

{docstring Squash.lift}

{docstring Squash.ind}
