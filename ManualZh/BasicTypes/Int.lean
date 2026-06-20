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

#doc (Manual) "整数" =>
%%%
file := "Integers"
tag := "Int"
%%%

整数是整数，包括正数和负数。
整数是任意精度的，仅受运行 Lean 的硬件功能的限制；对于编程和计算机科学中使用的 固定位宽整数，请参阅 {ref "fixed-ints"}[有关固定精度整数的部分]。

Lean 的实现特别支持整数。
整数的逻辑模型基于自然数：每个整数都建模为自然数或自然数的负后继。
使用此模型指定对整数的运算，该模型在内核和解释代码中使用。
在这些上下文中，整数代码继承了自然数特殊支持的性能优势。
在编译代码中，整数被表示为高效的任意精度整数，并且足够小的数字被存储为不需要通过指针间接寻址的值。
算术运算是通过利用高效表示的原语来实现的。

# 逻辑模型
%%%
file := "Logical-Model"
tag := "int-model"
%%%
整数表示为自然数或自然数后继者的否定。

{docstring Int}

这种整数表示法具有许多有用的属性。
它使用和理解相对简单。
与一对符号和 {lean}`Nat` 不同，$`0` 有唯一的表示形式，这简化了关于相等的推理。
整数也可以表示为一对自然数，其中一个从另一个中减去，但这需要 {ref "quotients"}[商类型] 表现良好，并且由于需要证明函数尊重等价关系，商类型可能很难使用。

# 运行时表示
%%%
file := "Run-Time-Representation"
tag := "int-runtime"
%%%

与 {ref "nat-runtime"}[自然数] 一样，足够小的整数不用指针来表示：对象指针中的最低位用于指示该值实际上不是指针。
如果整数太大而无法容纳剩余位，则会将其分配为普通 Lean 对象，该对象由对象标头和任意精度整数组成。

# 句法
%%%
file := "Syntax"
tag := "int-syntax"
%%%

```lean -show
section
variable (n : Nat)
```

{lean}`OfNat Int` 实例允许在表达式和模式上下文中将数字用作文字。
{lean}`(OfNat.ofNat n : Int)` 简化为构造函数应用程序 {lean}`Int.ofNat n`。
{inst}`Neg Int` 实例也允许使用否定。

```lean -show
open Int
```

在这些实例之上，当打开 `Int` 命名空间时，构造函数 {lean}`Int.negSucc` 可以使用特殊语法。
符号 {lean}`-[ n +1]` 暗示 $`-(n + 1)`，这就是 {lean}`Int.negSucc n` 的含义。

:::syntax term (title := "Negative Successor")

{lean}`-[ n +1]` 是 {lean}`Int.negSucc n` 的表示法。

```grammar
-[ $_ +1]
```
:::

```lean -show
end
```


# API 参考
%%%
file := "API-Reference"
tag := "zh-basictypes-int-h004"
%%%

## 特性
%%%
file := "Properties"
tag := "zh-basictypes-int-h005"
%%%

{docstring Int.sign}

## 转换
%%%
file := "Conversions"
tag := "zh-basictypes-int-h006"
%%%

{docstring Int.natAbs}

{docstring Int.toNat}

{docstring Int.toNat?}

{docstring Int.toISize}

{docstring Int.toInt8}

{docstring Int.toInt16}

{docstring Int.toInt32}

{docstring Int.toInt64}

{docstring Int.repr}

## 算术
%%%
file := "Arithmetic"
tag := "zh-basictypes-int-h007"
%%%

通常，使用 Lean 的重载算术表示法来访问整数的算术运算。
特别是，{inst}`Add Int`、{inst}`Neg Int`、{inst}`Sub Int` 和 {inst}`Mul Int` 的实例允许使用普通中缀运算符。
{ref "int-div"}[除法] 稍微复杂一些，因为整数除法有多种合理的概念。

{docstring Int.add}

{docstring Int.sub}

{docstring Int.subNatNat}

{docstring Int.neg}

{docstring Int.negOfNat}

{docstring Int.mul}

{docstring Int.pow}

{docstring Int.gcd}

{docstring Int.lcm}

### 分配
%%%
file := "Division"
tag := "int-div"
%%%
{inst}`Div Int` 和 {inst}`Mod Int` 实例实现欧几里得除法，如 {name}`Int.ediv` 的参考文献中所述。
然而，这并不是除法中舍入和余数的唯一合理约定。
提供四对除法和模函数，实现各种约定。

:::example "Division by 0"
在所有整数除法约定中，除以 {lean  (type := "Int")}`0` 定义为 {lean  (type := "Int")}`0`：

```lean (name := div0)
#eval Int.ediv 5 0
#eval Int.ediv 0 0
#eval Int.ediv (-5) 0
#eval Int.bdiv 5 0
#eval Int.bdiv 0 0
#eval Int.bdiv (-5) 0
#eval Int.fdiv 5 0
#eval Int.fdiv 0 0
#eval Int.fdiv (-5) 0
#eval Int.tdiv 5 0
#eval Int.tdiv 0 0
#eval Int.tdiv (-5) 0
```
全部评估为 0。
```leanOutput div0
0
```
:::

{docstring Int.ediv}

{docstring Int.emod}

{docstring Int.tdiv}

{docstring Int.tmod}

{docstring Int.bdiv}

{docstring Int.bmod}

{docstring Int.fdiv}

{docstring Int.fmod}

## 按位运算符
%%%
file := "Bitwise-Operators"
tag := "zh-basictypes-int-h009"
%%%

{name}`Int` 上的位运算符可以理解为无限位流上的位运算符，这些位是整数的补码表示。

{docstring Int.not}

{docstring Int.shiftRight}

## 比较
%%%
file := "Comparisons"
tag := "zh-basictypes-int-h010"
%%%

{lean}`Int` 上的等式和不等式测试通常使用其等式和排序关系的可判定性或使用 {inst}`BEq Int` 和 {inst}`Ord Int` 实例来执行。

```lean -show
example (i j : Int) : Decidable (i ≤ j) := inferInstance
example (i j : Int) : Decidable (i < j) := inferInstance
example (i j : Int) : Decidable (i = j) := inferInstance
```

{docstring Int.le}

{docstring Int.lt}

{docstring Int.decEq}
