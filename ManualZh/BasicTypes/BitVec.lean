/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option linter.typography.dashes false -- There's a reference to a Figure 5-2 below that should not be an en dash

set_option maxRecDepth 768

#doc (Manual) "位提供" =>
%%%
tag := "BitVec"
%%%

位向量是固定宽度的二进制数字序列。
它们经常用于软件验证，因为它们紧密地模拟了与硬件类似的高效数据结构和操作。
位向量可以从两个角度理解：作为位序列，或者作为由位序列编码的数字。
当位向量表示数字时，它可以作为有符号数或无符号数。
有符号数以二进制补码形式表示。

# 逻辑模型

位向量表示为具有适当界限的 {name}`Fin` 的包装器。
由于 {name}`Fin` 本身是 {name}`Nat` 的包装器，因此位向量能够使用内核的特殊支持来通过自然数进行高效计算。

{docstring BitVec}

# 运行时表示

位向量表示为具有相应范围的 {lean}`Fin`。
由于 {name}`BitVec` 是 {name}`Fin` 周围的 {ref "inductive-types-trivial-wrappers"}[简单包装器]，而 {name}`Fin` 是 {name}`Nat` 周围的简单包装器，因此位向量在编译代码中使用与 {name}`Nat` 相同的运行时表示形式。

# 句法
:::leanSection
```lean -show
variable {w n : Nat}
```
所有宽度 {lean}`w` 和自然数{lean}`n` 都有一个 {inst}`OfNat (BitVec w) n` 实例。
自然数文字（包括使用十六进制或二进制表示法的文字）可用于在已知预期类型的上下文中表示位向量。
当预期类型未知时，专用语法允许指定位向量的宽度及其值。
:::

:::example "Numeric Literals for Bitvectors"
以下文字都是等效的：
```lean
example : BitVec 8 := 0xff
example : BitVec 8 := 255
example : BitVec 8 := 0b1111_1111
```
```lean -show
-- Inline test
example : (0xff : BitVec 8) = 255 := by rfl
example : (0b1111_1111 : BitVec 8) = 255 := by rfl
```
:::

:::syntax term (title := "Fixed-Width Bitvector Literals")
```grammar
$_:num#$_
```
该表示法将数字文字与表示其宽度的术语配对。
`#` 周围禁止有空格。
超出位向量宽度的文字将被截断。
:::

:::::example "Fixed-Width Bitvector Literals"

位向量可以由自然数文字表示，因此 {lean}`(5 : BitVec 8)` 是有效的位向量。
此外，宽度可以直接在文字中指定：

```leanTerm
5#8
```


`#` 两侧不允许有空格：

```syntaxError spc1 (category := term)
5 #8
```
```leanOutput spc1
<example>:1:2-1:3: expected end of input
```

```syntaxError spc2 (category := term)
5# 8
```
```leanOutput spc2
<example>:1:3-1:4: expected no space before
```


`#` 的左侧需要一个数字文字：

```syntaxError spc3 (category := term)
(3 + 2)#8
```
```leanOutput spc3
<example>:1:7-1:8: expected end of input
```


但是，`#` 右侧允许有一个术语：
```leanTerm
5#(4 + 4)
```

如果文字太大而无法容纳指定的位数，则会被截断：
```lean (name := overflow)
#eval 7#2
```
```leanOutput overflow
3#2
```
:::::

:::syntax term (title := "Bounded Bitvector Literals") (namespace := BitVec)

```grammar
$_:num#'$_
```

仅当 `BitVec` 命名空间已打开时，此表示法才可用。
它不需要显式宽度，而是需要证明文字值可以由相应宽度的位向量表示。
:::

::::::leanSection
:::::example "Bounded Bitvector Literals"
有界位向量文字表示法可确保文字不会溢出指定的位数。
仅当打开 `BitVec` 命名空间时，该表示法才可用。

```lean
open BitVec
```

边界内的文字需要证​​明：
```lean
example : BitVec 8 := 1#'(by decide)
```

不允许使用超出范围的文字：
```lean +error (name := oob)
example : BitVec 8 := 256#'(by decide)
```
```leanOutput oob
Tactic `decide` proved that the proposition
  256 < 2 ^ 8
is false
```

:::::
::::::

# 自动化
%%%
tag := "BitVec-automation"
%%%

除了 Lean 为每种类型提供的全套自动化和工具之外，{tactic}`bv_decide`策略还可以解决许多与位向量相关的问题。
该策略调用外部自动 定理证明器 (`cadical`) 并重建它在 Lean 自己的逻辑中提供的证明。
由此产生的证明仅依赖于公理 {name}`Lean.ofReduceBool`；外部证明者不是可信代码库的一部分。

:::example "Popcount"

```imports -show
import Std.Tactic.BVDecide
```

函数 {lean}`popcount` 返回位向量中设置的位数。
它可以实现为一个 32 次迭代循环来测试每个位，如果该位被设置则递增计数器：

```lean
def popcount_spec (x : BitVec 32) : BitVec 32 :=
  (32 : Nat).fold (init := 0) fun i _ pop =>
    pop + ((x >>> i) &&& 1)
```

Henry S. Warren 的《黑客之乐》第二版中描述了 {lean}`popcount` 的替代实现，
第 5-2 页中的 Jr. 82.
它使用低级按位运算以更少的运算来计算相同的值：
```lean
def popcount (x : BitVec 32) : BitVec 32 :=
  let x := x - ((x >>> 1) &&& 0x55555555)
  let x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333)
  let x := (x + (x >>> 4)) &&& 0x0F0F0F0F
  let x := x + (x >>> 8)
  let x := x + (x >>> 16)
  let x := x &&& 0x0000003F
  x
```

使用 {tactic}`bv_decide` 可以证明这两种实现是等效的：
```lean
theorem popcount_correct : popcount = popcount_spec := by
  funext x
  simp [popcount, popcount_spec]
  bv_decide
```
:::

# API 参考
%%%
tag := "BitVec-api"
%%%


## 界限

{docstring BitVec.intMax}

{docstring BitVec.intMin}

## 建造

{docstring BitVec.fill}

{docstring BitVec.zero}

{docstring BitVec.allOnes}

{docstring BitVec.twoPow}

## 转换


{docstring BitVec.toHex}

{docstring BitVec.toInt}

{docstring BitVec.toNat}

{docstring BitVec.ofBool}

{docstring BitVec.ofBoolListBE}

{docstring BitVec.ofBoolListLE}

{docstring BitVec.ofInt}

{docstring BitVec.ofNat}

{docstring BitVec.ofNatLT}

{docstring BitVec.cast}

## 比较

{docstring BitVec.ule}

{docstring BitVec.sle}

{docstring BitVec.ult}

{docstring BitVec.slt}

{docstring BitVec.decEq}

## 散列

{docstring BitVec.hash}

## 顺序操作

这些操作将位向量视为位序列，而不是数字编码。

{docstring BitVec.nil}

{docstring BitVec.cons}

{docstring BitVec.concat}

{docstring BitVec.shiftConcat}

{docstring BitVec.truncate}

{docstring BitVec.setWidth}

{docstring BitVec.setWidth'}

{docstring BitVec.append}

{docstring BitVec.replicate}

{docstring BitVec.reverse}

{docstring BitVec.rotateLeft}

{docstring BitVec.rotateRight}

### 位提取

{docstring BitVec.msb}

{docstring BitVec.getMsbD}

{docstring BitVec.getMsb}

{docstring BitVec.getMsb?}

{docstring BitVec.getLsbD}

{docstring BitVec.getLsb}

{docstring BitVec.getLsb?}

{docstring BitVec.extractLsb}

{docstring BitVec.extractLsb'}

## 按位运算符

这些运算符修改一个或多个位向量的各个位。

{docstring BitVec.and}

{docstring BitVec.or}

{docstring BitVec.not}

{docstring BitVec.xor}

{docstring BitVec.zeroExtend}

{docstring BitVec.signExtend}

{docstring BitVec.ushiftRight}

{docstring BitVec.sshiftRight}

{docstring BitVec.sshiftRight'}

{docstring BitVec.shiftLeft}

{docstring BitVec.shiftLeftZeroExtend}


## 算术

这些运算符将位向量视为数字。
有些操作是有符号的，而另一些则没有符号。
因为位向量被理解为二进制补码，所以加法、减法和乘法对于有符号和无符号解释是一致的。


{docstring BitVec.add}

{docstring BitVec.sub}

{docstring BitVec.mul}


### 无符号操作

{docstring BitVec.udiv}

{docstring BitVec.smtUDiv}

{docstring BitVec.umod}

{docstring BitVec.uaddOverflow}

{docstring BitVec.usubOverflow}

### 签名操作

{docstring BitVec.abs}

{docstring BitVec.neg}

{docstring BitVec.sdiv}

{docstring BitVec.smtSDiv}

{docstring BitVec.smod}

{docstring BitVec.srem}

{docstring BitVec.saddOverflow}

{docstring BitVec.ssubOverflow}

## 迭代

{docstring BitVec.iunfoldr}

{docstring BitVec.iunfoldr_replace}

## 证明自动化

### 钻头爆破

标准库包含许多有助于实现位爆破的帮助器实现，这是 {tactic}`bv_decide` 用于将命题编码为外部求解器的布尔可满足性问题的技术。

{docstring BitVec.adc}

{docstring BitVec.adcb}

{docstring BitVec.carry}

{docstring BitVec.mulRec}

{docstring BitVec.divRec}

{docstring BitVec.divSubtractShift}

{docstring BitVec.shiftLeftRec}

{docstring BitVec.sshiftRightRec}

{docstring BitVec.ushiftRightRec}
