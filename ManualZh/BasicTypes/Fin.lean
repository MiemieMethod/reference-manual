/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "有限自然数" =>
%%%
tag := "Fin"
%%%

```lean -show
section
variable (n : Nat)
```

对于任何 {tech (key := "natural number")}[自然数] {lean}`n`，{lean}`Fin n` 是包含严格小于 {lean}`n` 的所有自然数的类型。
换句话说，{lean}`Fin n` 恰好具有 {lean}`n` 元素。
它可用于表示列表或数组中的有效索引，也可用作规范的 {lean}`n` 元素类型。

{docstring Fin}

{lean}`Fin` 与 {name}`UInt8`、{name}`UInt16`、{name}`UInt32`、{name}`UInt64` 和 {name}`USize` 密切相关，它们也表示有限非负积分类型。
但是，这些类型由位向量而不是自然数支持，并且它们具有固定的边界。
{lean}`Fin` 相对更灵活，但对于底层推理来说不太方便。
特别是，使用位向量而不是证明数字小于 2 的某个幂可以避免需要注意避免评估具体界限。

# 运行时特性
%%%
tag := "zh-basictypes-fin-h001"
%%%

因为 {lean}`Fin n` 是一个只有单个字段不是证明的结构，所以它是一个 {ref "inductive-types-trivial-wrappers"}[平凡的包装器]。
这意味着它在编译代码中的表示方式与底层自然数相同。

# 强制和文字
%%%
tag := "zh-basictypes-fin-h002"
%%%

有一个从 {lean}`Fin n` 到 {lean}`Nat` 的 {tech (key := "coercion")}[强制]，它丢弃数字小于界限的证明。
特别地，这个强制正是投影{name}`Fin.val`。
这样做的结果之一是 {name}`Fin.val` 的使用显示为强制，而不是证明状态中的显式投影。
:::example "Coercing from {name}`Fin` to {name}`Nat`"
{lean}`Fin n` 可以用在需要 {lean}`Nat` 的地方：
```lean (name := oneFinCoe)
#eval let one : Fin 3 := ⟨1, by omega⟩; (one : Nat)
```
```leanOutput oneFinCoe
1
```

{name}`Fin.val` 的使用在证明状态中显示为强制：
```proofState
∀(n : Nat) (i : Fin n), i < n := by
  intro n i
/--
n : Nat
i : Fin n
⊢ ↑i < n
-/

```
:::

自然数文字可用于 {lean}`Fin` 类型，通过 {name}`OfNat` 实例照常实现。
{lean}`Fin n` 的 {name}`OfNat` 实例要求上限 {lean}`n` 不为零，但不检查文字是否小于 {lean}`n`。
如果文字大于类型可以表示的值，则使用它除以 {lean}`n` 时的余数。

:::example "Numeric Literals for {name}`Fin`"

如果 {lean}`n > 0`，则自然数文字可用于 {lean}`Fin n`：
```lean
example : Fin 5 := 3
example : Fin 20 := 19
```
当文字大于或等于{lean}`n`时，使用除以{lean}`n`时的余数：
```lean (name := fivethree)
#eval (5 : Fin 3)
```
```leanOutput fivethree
2
```
```lean (name := fourthree)
#eval ([0, 1, 2, 3, 4, 5, 6] : List (Fin 3))
```
```leanOutput fourthree
[0, 1, 2, 0, 1, 2, 0]
```

如果 Lean 无法合成 {lean}`NeZero n` 的实例，则不存在 {lean}`OfNat (Fin n)` 实例：
```lean +error (name := fin0)
example : Fin 0 := 0
```
```leanOutput fin0
failed to synthesize instance of type class
  OfNat (Fin 0) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin 0
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

```lean +error (name := finK)
example (k : Nat) : Fin k := 0
```
```leanOutput finK
failed to synthesize instance of type class
  OfNat (Fin k) 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Fin k
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

# API 参考
%%%
tag := "zh-basictypes-fin-h003"
%%%

## 建造
%%%
tag := "zh-basictypes-fin-h004"
%%%

{docstring Fin.last}

{docstring Fin.succ}

{docstring Fin.pred}

## 算术
%%%
tag := "zh-basictypes-fin-h005"
%%%

通常，{name}`Fin` 上的算术运算应使用 Lean 的重载算术表示法进行访问，特别是通过实例 {inst}`Add (Fin n)`、{inst}`Sub (Fin n)`、{inst}`Mul (Fin n)`、{inst}`Div (Fin n)` 和 {inst}`Mod (Fin n)`。
诸如 {lean}`Fin.natAdd` 之类的异构运算符没有相应的异构实例（例如 {name}`HAdd`），以避免混淆类型推断行为。

{docstring Fin.add}

{docstring Fin.natAdd}

{docstring Fin.addNat}

{docstring Fin.mul}

{docstring Fin.sub}

{docstring Fin.subNat}

{docstring Fin.div}

{docstring Fin.mod}

{docstring Fin.modn}

{docstring Fin.log2}

## 按位运算
%%%
tag := "zh-basictypes-fin-h006"
%%%

通常，应使用 Lean 的重载按位运算符来访问 {name}`Fin` 上的按位操作，特别是通过实例 {inst}`ShiftLeft (Fin n)`、{inst}`ShiftRight (Fin n)`、{inst}`AndOp (Fin n)`、{inst}`OrOp (Fin n)`、{inst}`Xor (Fin n)`

{docstring Fin.shiftLeft}

{docstring Fin.shiftRight}

{docstring Fin.land}

{docstring Fin.lor}

{docstring Fin.xor}


## 转换
%%%
tag := "zh-basictypes-fin-h007"
%%%

{docstring Fin.toNat}

{docstring Fin.ofNat}

{docstring Fin.cast}

{docstring Fin.castLT}

{docstring Fin.castLE}

{docstring Fin.castAdd}

{docstring Fin.castSucc}

{docstring Fin.rev}

{docstring Fin.elim0}

## 迭代
%%%
tag := "zh-basictypes-fin-h008"
%%%

{docstring Fin.foldr}

{docstring Fin.foldrM}

{docstring Fin.foldl}

{docstring Fin.foldlM}

{docstring Fin.hIterate}

{docstring Fin.hIterateFrom}

## 推理
%%%
tag := "zh-basictypes-fin-h009"
%%%

{docstring Fin.induction}

{docstring Fin.inductionOn}

{docstring Fin.reverseInduction}

{docstring Fin.cases}

{docstring Fin.lastCases}

{docstring Fin.addCases}

{docstring Fin.succRec}

{docstring Fin.succRecOn}
