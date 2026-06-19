/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "递归示例（包含在其他地方）" =>


```lean -show
section
variable (n k : Nat) (mot : Nat → Sort u)
```
:::example "Recursion vs Recursors"
自然数的添加可以通过第二个参数的递归来定义。
该函数在结构上是直接递归的。
```lean
def add (n : Nat) : Nat → Nat
  | .zero => n
  | .succ k => .succ (add n k)
```

使用 {name}`Nat.rec` 定义，它与大多数人习惯的符号相距甚远。
```lean
def add' (n : Nat) :=
  Nat.rec (motive := fun _ => Nat)
    n
    (fun k soFar => .succ soFar)
```

对不是函数参数的直接子代的数据进行的结构递归调用需要创造力或复杂但系统的编码。
```lean
def half : Nat → Nat
  | 0 | 1 => 0
  | n + 2 => half n + 1
```
将此函数视为结构递归，它在每次调用时翻转一位，仅在设置该位时递增结果。
```lean
def helper : Nat → Bool → Nat :=
  Nat.rec (motive := fun _ => Bool → Nat)
    (fun _ => 0)
    (fun _ soFar =>
      fun b =>
        (if b then Nat.succ else id) (soFar !b))

def half' (n : Nat) : Nat := helper n false
```
```lean (name := halfTest)
#eval [0, 1, 2, 3, 4, 5, 6, 7, 8].map half'
```
```leanOutput halfTest
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

可以使用称为 {deftech}[值过程递归] 的通用技术来代替创造力。
值过程递归使用可以为每个归纳类型系统导出的帮助程序，根据递归器定义； Lean 自动导出它们。
对于每个 {lean}`Nat` {lean}`n`，类型 {lean}`n.below (motive := mot)` 为所有 {lean}`k < n` 提供 {lean}`mot k` 类型的值，表示为迭代的 {TODO}[xref sigma] 相关对类型。
值过程递归器 {name}`Nat.brecOn` 允许函数使用任何较小的 {lean}`Nat` 的结果。
用它来定义函数很不方便：
```lean
noncomputable def half'' (n : Nat) : Nat :=
  Nat.brecOn n (motive := fun _ => Nat)
    fun k soFar =>
      match k, soFar with
      | 0, _ | 1, _ => 0
      | _ + 2, ⟨_, ⟨h, _⟩⟩ => h + 1
```
该函数被标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable`，因为编译器不支持生成值过程递归的代码，该递归旨在用于推理而不是高效的代码。
内核仍可用于测试该功能，但是：
```lean (name := halfTest2)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest2
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

如果需要，{lean}`half''` 主体中的依赖模式匹配也可以使用递归器（具体来说，{name}`Nat.casesOn`）进行编码：
```lean
noncomputable def half''' (n : Nat) : Nat :=
  n.brecOn (motive := fun _ => Nat)
    fun k =>
      k.casesOn
        (motive :=
          fun k' =>
            (k'.below (motive := fun _ => Nat)) →
            Nat)
        (fun _ => 0)
        (fun k' =>
          k'.casesOn
            (motive :=
              fun k'' =>
                (k''.succ.below (motive := fun _ => Nat)) →
                Nat)
            (fun _ => 0)
            (fun _ soFar => soFar.2.1.succ))
```

这个定义仍然有效。
```lean (name := halfTest3)
#reduce [0,1,2,3,4,5,6,7,8].map half''
```
```leanOutput halfTest3
[0, 0, 1, 1, 2, 2, 3, 3, 4]
```

然而，现在它与最初的定义相去甚远，对于大多数人来说已经变得难以理解。
递归是一个很好的逻辑基础，但不是编写程序或证明的简单方法。
:::
```lean -show
end
```
