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

#doc (Manual) "浮点数" =>
%%%
tag := "Float"
%%%

浮点数是在计算机硬件中有效实现的实数的近似值。
使用浮点数的计算非常高效；然而，它们近似实数的方式的性质很复杂，存在许多极端情况。
IEEE 754 标准定义了现代计算机上使用的浮点格式，允许硬件设计人员做出某些选择，而实际系统在这些小细节上有所不同。
例如，`NaN` 有许多不同的位表示，结果未定义的指示符，并且某些平台在通过添加两个 `NaN` 返回的 `NaN` 方面有所不同。

Lean 公开底层平台的浮点值以供编程使用，但它们未在 Lean 的逻辑中进行编码。
它们由不透明类型表示。
这意味着，如果没有额外的 {ref "axioms"}[公理]，{tech}[内核] 无法使用浮点值进行计算或推理。
这样做的结果是浮点数的相等性是不可判定的。
此外，浮点值之间的比较是可判定的，但这样做的代码是不透明的；实际上，决策过程只能在编译代码中使用。

Lean 提供两种浮点类型：{name}`Float` 表示 64 位浮点值，而 {name}`Float32` 表示 32 位浮点值。
{name}`Float` 的精度不会因 Lean 运行的平台而异。


{docstring Float (label := "type") +hideStructureConstructor +hideFields}

{docstring Float32 (label := "type") +hideStructureConstructor +hideFields}


:::example "No Kernel Reasoning About Floating-Point Numbers"
Lean内核可以比较 {lean}`Float` 类型的表达式的语法相等性，因此 {lean  (type := "Float")}`0.0` 在定义上等于其自身。
```lean
example : (0.0 : Float) = (0.0 : Float) := by rfl
```

内核无法检查需要归约才能在语法上相等的术语：
```lean +error (name := zeroPlusZero)
example : (0.0 : Float) = (0.0 + 0.0 : Float) := by rfl
```
```leanOutput zeroPlusZero
Tactic `rfl` failed: The left-hand side
  0.0
is not definitionally equal to the right-hand side
  0.0 + 0.0

⊢ 0.0 = 0.0 + 0.0
```

同样，内核在检查 定义等价 时无法评估浮点数的 {lean}`Bool` 值比较：
```lean +error (name := zeroPlusZero') -keep
theorem Float.zero_eq_zero_plus_zero :
    ((0.0 : Float) == (0.0 + 0.0 : Float)) = true :=
  by rfl
```
```leanOutput zeroPlusZero'
Tactic `rfl` failed: The left-hand side
  0.0 == 0.0 + 0.0
is not definitionally equal to the right-hand side
  true

⊢ (0.0 == 0.0 + 0.0) = true
```


但是，{tactic}`native_decide`策略可以调用 Lean 用于运行时程序的底层平台的浮点原语：
```lean
theorem Float.zero_eq_zero_plus_zero :
    ((0.0 : Float) == (0.0 + 0.0 : Float)) = true := by
  native_decide
```
该策略将决策过程作为已编译的本机代码执行。
除了内核之外，这还需要信任 Lean 编译器、解释器和内置运算符的低级实现。
为了精确地阐明这种依赖性，策略创建了公理 {name}`Float.zero_eq_zero_plus_zero._native.native_decide.ax_1`：
```lean (name := ofRed)
#print axioms Float.zero_eq_zero_plus_zero
```
```leanOutput ofRed
'Float.zero_eq_zero_plus_zero' depends on axioms: [Classical.choice,
 Float.zero_eq_zero_plus_zero._native.native_decide.ax_1]
```
:::

:::example "Floating-Point Equality Is Not Reflexive"
浮点运算可能会产生指示未定义结果的 `NaN` 值。
这些值彼此之间没有可比性；特别是，涉及 `NaN` 的所有比较都将返回 `false`，包括相等。
```lean
#eval ((0.0 : Float) / 0.0) == ((0.0 : Float) / 0.0)
```
:::

:::example "Floating-Point Equality Is Not a Congruence"
将函数应用于两个相等的浮点数可能不会产生相等的数字。
特别是，正零和负零是通过浮点相等相等的不同值，但除以正零或负零会产生正无穷大值或负无穷大值。
```lean (name := divZeroPosNeg)
def neg0 : Float := -0.0

def pos0 : Float := 0.0

#eval (neg0 == pos0, 1.0 / neg0 == 1.0 / pos0)
```
```leanOutput divZeroPosNeg
(true, false)
```
:::


# 句法
%%%
tag := "zh-basictypes-float-h001"
%%%

Lean 没有专用的浮点文字。
相反，浮点文字是通过 {name}`OfScientific` 和 {name}`Neg` 类型类的适当实例来解析的。

:::example "Floating-Point Literals"

期限
```leanTerm
(-2.523 : Float)
```
是语法糖
```leanTerm
(Neg.neg (OfScientific.ofScientific 22523 true 4) : Float)
```
和术语
```leanTerm
(413.52 : Float32)
```
是语法糖
```leanTerm
(OfScientific.ofScientific 41352 true 2 : Float32)
```

```lean -show
example : (-2.2523 : Float) = (Neg.neg (OfScientific.ofScientific 22523 true 4) : Float) := by simp [OfScientific.ofScientific]
example : (413.52 : Float32) = (OfScientific.ofScientific 41352 true 2 : Float32) := by simp [OfScientific.ofScientific]
```
:::

# API 参考
%%%
tag := "Float-api"
%%%

## 特性
%%%
tag := "zh-basictypes-float-h003"
%%%

浮点数属于以下三类之一：

 * 有限数是普通的浮点值。

 * 无穷大（可以是正数或负数）是除以零的结果。

 * `NaN` 不是数字，是其他未定义运算的结果，例如负数的平方根。

{docstring Float.isInf}

{docstring Float32.isInf}

{docstring Float.isNaN}

{docstring Float32.isNaN}

{docstring Float.isFinite}

{docstring Float32.isFinite}


## 句法
%%%
tag := "zh-basictypes-float-h004"
%%%

这些操作的存在是为了支持 {inst}`OfScientific Float` 和 {inst}`OfScientific Float32` 实例，并且通常作为文字值的结果间接调用。

{docstring Float.ofScientific}

{docstring Float32.ofScientific}


## 转换
%%%
tag := "zh-basictypes-float-h005"
%%%

{docstring Float.toBits}

{docstring Float32.toBits}

{docstring Float.ofBits}

{docstring Float32.ofBits}

{docstring Float.toFloat32}

{docstring Float32.toFloat}

{docstring Float.toString}

{docstring Float32.toString}

{docstring Float.toUInt8}

{docstring Float.toInt8}

{docstring Float32.toUInt8}

{docstring Float32.toInt8}

{docstring Float.toUInt16}

{docstring Float.toInt16}

{docstring Float32.toUInt16}

{docstring Float32.toInt16}

{docstring Float.toUInt32}

{docstring Float32.toUInt32}

{docstring Float.toInt32}

{docstring Float32.toInt32}

{docstring Float.toUInt64}

{docstring Float.toInt64}

{docstring Float32.toUInt64}

{docstring Float32.toInt64}

{docstring Float.toUSize}

{docstring Float32.toUSize}

{docstring Float.toISize}

{docstring Float32.toISize}

{docstring Float.ofInt}

{docstring Float32.ofInt}

{docstring Float.ofNat}

{docstring Float32.ofNat}

{docstring Float.ofBinaryScientific}

{docstring Float32.ofBinaryScientific}

{docstring Float.frExp}

{docstring Float32.frExp}

## 比较
%%%
tag := "zh-basictypes-float-h006"
%%%

{docstring Float.beq}

{docstring Float32.beq}

### 不平等现象
%%%
tag := "zh-basictypes-float-h007"
%%%

不等式的决策过程是逻辑中不透明的常数。
它们只能通过 {name}`Lean.ofReduceBool` 公理使用，例如通过 {tactic}`native_decide`策略。

{docstring Float.le}

{docstring Float32.le}

{docstring Float.lt}

{docstring Float32.lt}

{docstring Float.decLe}

{docstring Float32.decLe}

{docstring Float.decLt}

{docstring Float32.decLt}

## 算术
%%%
tag := "zh-basictypes-float-h008"
%%%

浮点值的算术运算通常通过 {inst}`Add Float`、{inst}`Sub Float`、{inst}`Mul Float`、{inst}`Div Float` 和 {inst}`HomogeneousPow Float` 实例以及相应的 {name}`Float32` 实例调用。

{docstring Float.add}

{docstring Float32.add}

{docstring Float.sub}

{docstring Float32.sub}

{docstring Float.mul}

{docstring Float32.mul}

{docstring Float.div}

{docstring Float32.div}

{docstring Float.pow}

{docstring Float32.pow}

{docstring Float.exp}

{docstring Float32.exp}

{docstring Float.exp2}

{docstring Float32.exp2}

### 根源
%%%
tag := "zh-basictypes-float-h009"
%%%

计算负数的平方根得到 `NaN`。

{docstring Float.sqrt}

{docstring Float32.sqrt}

{docstring Float.cbrt}

{docstring Float32.cbrt}

## 对数
%%%
tag := "zh-basictypes-float-h010"
%%%

{docstring Float.log}

{docstring Float32.log}

{docstring Float.log10}

{docstring Float32.log10}

{docstring Float.log2}

{docstring Float32.log2}

## 缩放
%%%
tag := "zh-basictypes-float-h011"
%%%

{docstring Float.scaleB}

{docstring Float32.scaleB}

## 四舍五入
%%%
tag := "zh-basictypes-float-h012"
%%%

{docstring Float.round}

{docstring Float32.round}

{docstring Float.floor}

{docstring Float32.floor}

{docstring Float.ceil}

{docstring Float32.ceil}

## 三角学
%%%
tag := "zh-basictypes-float-h013"
%%%

### 正弦
%%%
tag := "zh-basictypes-float-h014"
%%%

{docstring Float.sin}

{docstring Float32.sin}

{docstring Float.sinh}

{docstring Float32.sinh}

{docstring Float.asin}

{docstring Float32.asin}

{docstring Float.asinh}

{docstring Float32.asinh}

### 余弦
%%%
tag := "zh-basictypes-float-h015"
%%%

{docstring Float.cos}

{docstring Float32.cos}

{docstring Float.cosh}

{docstring Float32.cosh}

{docstring Float.acos}

{docstring Float32.acos}

{docstring Float.acosh}

{docstring Float32.acosh}

### 切线
%%%
tag := "zh-basictypes-float-h016"
%%%

{docstring Float.tan}

{docstring Float32.tan}

{docstring Float.tanh}

{docstring Float32.tanh}

{docstring Float.atan}

{docstring Float32.atan}

{docstring Float.atanh}

{docstring Float32.atanh}

{docstring Float.atan2}

{docstring Float32.atan2}

## 负数和绝对值
%%%
tag := "zh-basictypes-float-h017"
%%%

{docstring Float.abs}

{docstring Float32.abs}

{docstring Float.neg}

{docstring Float32.neg}
