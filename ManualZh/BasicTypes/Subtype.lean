/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.BasicTypes.Array.Subarray
import ManualZh.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "亚型" =>
%%%
file := "Subtypes"
tag := "Subtype"
%%%

结构 {name}`Subtype` 表示满足某些谓词的类型的元素。
它们在数学和编程中广泛使用。在数学中，它们的使用方式与子集类似，而在编程中，它们允许以 Lean 逻辑可见的方式表示已知值的信息。

从语法上讲，{name}`Subtype` 的元素类似于基本类型元素的元组以及它满足命题的证明。
它们与依赖对类型 ({name}`Sigma`) 的不同之处在于，第二个元素是命题的证明而不是数据；它们与存在量化的不同之处在于，整个 {name}`Subtype` 是类型而不是命题。
尽管它们在语法上是成对的，但 {name}`Subtype` 实际上应该被视为具有相关证明义务的基本类型的元素。

子类型是 {ref "inductive-types-trivial-wrappers"}[普通包装器]。
因此，它们在编译代码中的表示方式与基本类型相同。


{docstring Subtype}

::::leanSection
```lean -show
variable {α : Type u} {p : Prop}
```
:::syntax term (title := "Subtypes")
```grammar
{ $x : $t:term // $t:term }
```

{lean}`{ x : α // p }` 是 {lean}`Subtype fun (x : α) => p` 的表示法。

类型归属可以省略：

```grammar
{ $x:ident // $t:term }
```

{lean}`{ x // p }` 是 {lean}`Subtype fun (x : _) => p` 的表示法。
:::
::::

由于 {tech (key := "proof irrelevance")}[证明无关性] 和 {tech (key := "η-equivalence")}[η-相等]，当基本类型的元素定义等价时，子类型的两个元素定义等价。
在证明中，{tactic}`ext`策略可用于将子类型元素相等的目标转换为其值相等的目标。

:::example "Definitional Equality of Subtypes"

非空字符串 {lean}`s1` 和 {lean}`s2` 在定义上是相等的，尽管它们嵌入的证明术语不同。
无需进行大小写分割即可证明它们相等。

```lean
def NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.ext_iff.mp h)

theorem s1_eq_s2 : s1 = s2 := by rfl
```
:::

:::example "Extensional Equality of Subtypes"

非空字符串 {lean}`s1` 和 {lean}`s2` 在定义上是相等的。
忽略这一事实，可以使用嵌入字符串的相等性来证明它们是相等的。
{tactic}`ext`策略将由非空字符串相等组成的目标转换为由字符串相等组成的目标。

```lean
abbrev NonEmptyString := { x : String // x ≠ "" }

def s1 : NonEmptyString :=
  ⟨"equal", ne_of_beq_false rfl⟩

def s2 : NonEmptyString where
  val := "equal"
  property :=
    fun h =>
      List.cons_ne_nil _ _ (String.ext_iff.mp h)

theorem s1_eq_s2 : s1 = s2 := by
  ext
  dsimp only [s1, s2]
  rfl
```
:::

存在从子类型到其基类型的强制。
这允许在需要基本类型的位置使用子类型，从本质上消除了该值满足谓词的证明。

:::example "Subtype Coercions"

子类型的元素可以强制为其基本类型。
此处，{name}`nine` 是从包含 {lean  (type := "Nat")}`3` 到 {lean}`Nat` 倍数的 `Nat` 子类型强制转换而来。

```lean (name := subtype_coe)
abbrev DivBy3 := { x : Nat // x % 3 = 0 }

def nine : DivBy3 := ⟨9, by rfl⟩

set_option eval.type true in
#eval Nat.succ nine
```
```leanOutput subtype_coe
10 : Nat
```

:::
