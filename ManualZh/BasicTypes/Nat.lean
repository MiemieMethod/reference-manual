/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "自然数" =>
%%%
file := "Natural-Numbers"
tag := "Nat"
%%%

{deftech (key := "natural numbers")}[自然数] 是非负整数。
从逻辑上讲，它们是数字 0、1、2、3……，由构造函数 {lean}`Nat.zero` 和 {lean}`Nat.succ` 生成。
除了计算机可用内存施加的物理约束之外，Lean 对自然数的表示没有施加上限。

由于自然数是数学推理和编程的基础，因此 Lean 的实现特别支持它们。自然数的逻辑模型为 {tech (key := "inductive type")}[归纳类型]，并且使用该模型指定算术运算。在 Lean 的内核中，解释器和编译代码、封闭的自然数被表示为高效的任意精度整数。足够小的数字是不需要通过指针间接寻址的值。算术运算是通过利用高效表示的原语来实现的。

# 逻辑模型
%%%
file := "Logical-Model"
tag := "nat-model"
%%%


{docstring Nat}

::::leanSection
```lean -show
variable (i : Nat)
```
:::example "Proofs by Induction"
自然数是 {tech (key := "inductive type")}[归纳类型]，因此 {tactic}`induction`策略可用于证明全称量化陈述。
归纳证明需要基例和归纳步骤。
基例证明该陈述对于 `0` 是正确的。
归纳步骤证明某个任意数 {lean}`i` 的陈述的真实性意味着 {lean}`i + 1` 的陈述的真实性。

该证明在归纳步骤中使用引理 `Nat.succ_lt_succ`。
```lean
example (n : Nat) : n < n + 1 := by
  induction n with
  | zero =>
    show 0 < 1
    decide
  | succ i ih => -- ih : i < i + 1
    show i + 1 < i + 1 + 1
    exact Nat.succ_lt_succ ih
```
:::
::::

## 皮亚诺公理
%%%
file := "Peano-Axioms"
tag := "peano-axioms"
%%%

皮亚诺公理是这个定义的结果。
{lean}`Nat` 生成的归纳原理是归纳公理所要求的：
```signature
Nat.rec.{u} {motive : Nat → Sort u}
  (zero : motive zero)
  (succ : (n : Nat) → motive n → motive n.succ)
  (t : Nat) :
  motive t
```
这个归纳原理也实现了原始递归。
{lean}`Nat.succ` 的单射性以及 {lean}`Nat.succ` 和 `Nat.zero` 的不相交是归纳原理的结果，使用通常称为“无混淆”的结构：
```lean
def NoConfusion : Nat → Nat → Prop
  | 0, 0 => True
  | 0, _ + 1 | _ + 1, 0 => False
  | n + 1, k + 1 => n = k

theorem noConfusionDiagonal (n : Nat) :
    NoConfusion n n :=
  Nat.rec True.intro (fun _ _ => rfl) n

theorem noConfusion (n k : Nat) (eq : n = k) :
    NoConfusion n k :=
  eq ▸ noConfusionDiagonal n

theorem succ_injective : n + 1 = k + 1 → n = k :=
  noConfusion (n + 1) (k + 1)

theorem succ_not_zero : ¬n + 1 = 0 :=
  noConfusion (n + 1) 0
```

# 运行时表示
%%%
file := "Run-Time-Representation"
tag := "nat-runtime"
%%%

`Nat` 声明所建议的表示效率极其低下，因为它本质上是一个链表。
列表的长度就是数字。
通过这种表示，加法所花费的时间与一个加数的大小成线性关系，而数字所花费的机器字数至少与其在内存中的大小一样多。
因此，自然数在内核和编译器中都有特殊支持，可以避免这种开销。

在内核中，有特殊的 `Nat` 文字值，它们使用广泛信任的高效任意精度整数库（通常为 [GMP](https://gmplib.org/)）。
诸如加法之类的基本函数被使用此表示的原语覆盖。
由于它们是内核的一部分，因此如果这些原语不符合其作为 Lean 函数的定义，则可能会破坏健全性。

在编译代码中，足够小的自然数在没有指针间接表示的情况下表示：对象指针中的最低位用于指示该值实际上不是指针，其余位用于存储数字。
对于无指针 {lean}`Nat`，31 位可用于 32 位架构，而 63 位可用于 64 位架构。
换句话说，小于 $`2^{31} = 2,147,483,648` 或 $`2^{63} = 9,223,372,036,854,775,808` 的自然数不需要分配。
如果自然数对于此表示太大，则会将其分配为普通 Lean 对象，该对象由对象标头和任意精度整数值组成。

## 性能说明
%%%
file := "Performance-Notes"
tag := "nat-performance"
%%%


使用 Lean 的内置算术运算符而不是重新定义它们是至关重要的。
{lean}`Nat` 的逻辑模型本质上是一个链表，因此加法所需的时间与一个参数的大小成线性关系。
更糟糕的是，在此模型中，乘法需要花费二次时间。
虽然从头开始定义算术可能是一种有用的学习练习，但这些重新定义的操作不会那么快。

# 句法
%%%
file := "Syntax"
tag := "nat-syntax"
%%%


自然数文字可使用 {lean}`OfNat` 类型类覆盖，这在 {ref "nat-literals"}[有关文字语法的部分] 中进行了描述。


# API 参考
%%%
file := "API-Reference"
tag := "nat-api"
%%%


## 算术
%%%
file := "Arithmetic"
tag := "nat-api-arithmetic"
%%%

{docstring Nat.pred}

{docstring Nat.add}

{docstring Nat.sub}

{docstring Nat.mul}

{docstring Nat.div}

{docstring Nat.mod}

{docstring Nat.modCore}

{docstring Nat.pow}

{docstring Nat.log2}

### 按位运算
%%%
file := "Bitwise-Operations"
tag := "nat-api-bitwise"
%%%

{docstring Nat.shiftLeft}

{docstring Nat.shiftRight}

{docstring Nat.xor}

{docstring Nat.lor}

{docstring Nat.land}

{docstring Nat.bitwise}

{docstring Nat.testBit}

## 最小值和最大值
%%%
file := "Minimum-and-Maximum"
tag := "nat-api-minmax"
%%%


{docstring Nat.min}

{docstring Nat.max}

## GCD 和 LCM
%%%
file := "GCD-and-LCM"
tag := "nat-api-gcd-lcm"
%%%


{docstring Nat.gcd}

{docstring Nat.lcm}

## 二的幂
%%%
file := "Powers-of-Two"
tag := "nat-api-pow2"
%%%


{docstring Nat.isPowerOfTwo}

{docstring Nat.nextPowerOfTwo}

## 比较
%%%
file := "Comparisons"
tag := "nat-api-comparison"
%%%


### 布尔比较
%%%
file := "Boolean-Comparisons"
tag := "nat-api-comparison-bool"
%%%


{docstring Nat.beq}

{docstring Nat.ble}

{docstring Nat.blt}

### 可判定的平等
%%%
file := "Decidable-Equality"
tag := "nat-api-deceq"
%%%

{docstring Nat.decEq}

{docstring Nat.decLe}

{docstring Nat.decLt}

### 谓词
%%%
file := "Predicates"
tag := "nat-api-predicates"
%%%

{docstring Nat.le}

{docstring Nat.lt}

## 迭代
%%%
file := "Iteration"
tag := "nat-api-iteration"
%%%

许多迭代运算符有两个版本：结构递归版本和尾递归版本。
结构递归版本通常在 定义等价 很重要的上下文中更容易使用，因为它会在仅知道自然数的某些前缀时进行计算。

{docstring Nat.repeat}

{docstring Nat.repeatTR}

{docstring Nat.fold}

{docstring Nat.foldTR}

{docstring Nat.foldM}

{docstring Nat.foldRev}

{docstring Nat.foldRevM}

{docstring Nat.forM}

{docstring Nat.forRevM}

{docstring Nat.all}

{docstring Nat.allTR}

{docstring Nat.any}

{docstring Nat.anyTR}

{docstring Nat.allM}

{docstring Nat.anyM}

## 转换
%%%
file := "Conversion"
tag := "nat-api-conversion"
%%%

{docstring Nat.toUInt8}

{docstring Nat.toUInt16}

{docstring Nat.toUInt32}

{docstring Nat.toUInt64}

{docstring Nat.toUSize}

{docstring Nat.toInt8}

{docstring Nat.toInt16}

{docstring Nat.toInt32}

{docstring Nat.toInt64}

{docstring Nat.toISize}

{docstring Nat.toFloat}

{docstring Nat.toFloat32}

{docstring Nat.isValidChar}

{docstring Nat.repr}

{docstring Nat.toDigits}

{docstring Nat.digitChar}

{docstring Nat.toSubscriptString}

{docstring Nat.toSuperscriptString}

{docstring Nat.toSuperDigits}

{docstring Nat.toSubDigits}

{docstring Nat.subDigitChar}

{docstring Nat.superDigitChar}

## 消除
%%%
file := "Elimination"
tag := "nat-api-elim"
%%%


为 {lean}`Nat` 自动生成的递归原理会产生以 {lean}`Nat.zero` 和 {lean}`Nat.succ` 表述的证明目标。
这对于用户来说不是特别友好，因此提供了另一种逻辑等效的递归原则，其结果是用 {lean}`0` 和 `n + 1` 来表述的目标。
{tech (key := "Custom eliminators")}[自定义消除器] 用于 {tactic}`induction` 和 {tactic}`cases`策略可以使用 {attr}`induction_eliminator` 和 {attr}`cases_eliminator` 属性提供。

{docstring Nat.recAux}

{docstring Nat.casesAuxOn}

### 替代归纳原理
%%%
file := "Alternative-Induction-Principles"
tag := "nat-api-induction"
%%%

{docstring Nat.strongRecOn}

{docstring Nat.caseStrongRecOn}

{docstring Nat.div.inductionOn}

{docstring Nat.div2Induction}

{docstring Nat.mod.inductionOn}
