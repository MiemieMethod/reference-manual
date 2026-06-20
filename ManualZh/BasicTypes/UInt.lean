/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import ManualZh.BasicTypes.UInt.Comparisons
import ManualZh.BasicTypes.UInt.Arith

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "固定精度整数" =>
%%%
file := "Fixed-Precision-Integers"
tag := "fixed-ints"
%%%

Lean 的标准库包括 固定位宽整数 类型的常见分类。
从形式化和证明的角度来看，这些类型是适当大小的位向量的包装器；包装器确保例如的正确实现应用算术运算。
在编译的代码中，它们被有效地表示：编译器对它们有特殊的支持，就像对其他基本类型的支持一样。

# 逻辑模型
%%%
file := "Logical-Model"
tag := "zh-basictypes-uint-h001"
%%%

固定位宽整数 可以是未签名的或已签名的。
此外，它们还有五种大小：8、16、32 和 64 位，以及当前架构的字大小。
在它们的逻辑模型中，无符号整数是包装适当宽度的 {name}`BitVec` 的结构。
有符号整数包装相应的无符号整数，并使用二进制补码表示形式。

## 未签名
%%%
file := "Unsigned"
tag := "zh-basictypes-uint-h002"
%%%

{docstring USize}

{docstring UInt8}

{docstring UInt16}

{docstring UInt32}

{docstring UInt64}

## 签名
%%%
file := "Signed"
tag := "zh-basictypes-uint-h003"
%%%

{docstring ISize}

{docstring Int8}

{docstring Int16}

{docstring Int32}

{docstring Int64}

# 运行时表示
%%%
file := "Run-Time-Representation"
tag := "fixed-int-runtime"
%%%

在需要 {tech}[boxed] 表示的上下文中的编译代码中，始终表示比平台指针大小少一位的 固定位宽整数 类型，而无需额外的分配或间接寻址。
这始终包括 {lean}`Int8`、{lean}`UInt8`、{lean}`Int16` 和 {lean}`UInt16`。
在 64 位体系结构上，{lean}`Int32` 和 {lean}`UInt32` 也以不带指针的方式表示。
在 32 位体系结构上，{lean}`Int32` 和 {lean}`UInt32` 需要指向堆上对象的指针。
{lean}`ISize`、{lean}`USize`、{lean}`Int64` 和 {lean}`UInt64` 可能需要所有架构上的指针。

尽管某些固定整数类型通常需要装箱，但编译器能够在仅使用特定固定宽度类型而不是多态的代码路径中表示它们，而无需装箱或指针间接，可能在专门化过程之后。
这适用于使用这些类型的大多数实际情况：当构造函数参数、函数参数、函数返回值或中间结果已知为 固定位宽整数 类型时，它们的值使用相应的无符号固定宽度 C 类型表示。
Lean 运行时系统包括用于在 {tech (key := "inductive types")}[归纳类型] 的构造函数中存储 固定位宽整数 的原语，并且原语操作是在相应的 C 类型上定义的，因此装箱往往发生在整数计算的“边缘”，而不是针对每个中间结果。
在可能出现其他类型的上下文中，例如 {name}`Array` 等多态容器的内容，即使数组静态已知仅包含单个 固定位宽整数 类型，这些类型也会被装箱。{margin}[单态数组类型 {lean}`ByteArray` 避免对 {lean}`UInt8` 数组进行装箱。]
Lean 不专门表示归纳类型或数组。
检查 Lean 中函数的类型不足以确定如何表示 固定位宽整数 值，因为装箱值不会立即拆箱 — 从数组投影 {name}`Int64` 的函数会返回装箱整数值。

# 句法
%%%
file := "Syntax"
tag := "zh-basictypes-uint-h005"
%%%

所有 固定位宽整数 类型都有 {name}`OfNat` 实例，这些实例允许在表达式和模式上下文中将数字用作文字。
签名类型还具有 {lean}`Neg` 实例，允许应用否定。

:::example "Fixed-Width Literals"
Lean 允许将十进制和十六进制文字用于具有 {name}`OfNat` 实例的类型。
在此示例中，使用文字符号来定义掩码。

```lean
structure Permissions where
  readable : Bool
  writable : Bool
  executable : Bool

def Permissions.encode (p : Permissions) : UInt8 :=
  let r := if p.readable then 0x01 else 0
  let w := if p.writable then 0x02 else 0
  let x := if p.executable then 0x04 else 0
  r ||| w ||| x

def Permissions.decode (i : UInt8) : Permissions :=
  ⟨i &&& 0x01 ≠ 0, i &&& 0x02 ≠ 0, i &&& 0x04 ≠ 0⟩
```

```lean -show
-- Check the above
theorem Permissions.decode_encode (p : Permissions) : p = .decode (p.encode) := by
  let ⟨r, w, x⟩ := p
  cases r <;> cases w <;> cases x <;>
  simp +decide [decode]
```
:::

溢出其类型精度的文字被解释为对精度取模。
有符号类型根据底层的补码表示进行解释。

:::example "Overflowing Fixed-Width Literals"
以下陈述全部正确：
```lean
example : (255 : UInt8) = 255 := by rfl
example : (256 : UInt8) = 0   := by rfl
example : (257 : UInt8) = 1   := by rfl

example : (0x7f : Int8) = 127  := by rfl
example : (0x8f : Int8) = -113 := by rfl
example : (0xff : Int8) = -1   := by rfl
```
:::

# API 参考
%%%
file := "API-Reference"
tag := "zh-basictypes-uint-h006"
%%%

## 尺寸
%%%
file := "Sizes"
tag := "zh-basictypes-uint-h007"
%%%

每个 固定位宽整数 都有一个_size_，它是该类型可以表示的不同值的数量。
这并不等同于 C 的 `sizeof` 运算符，而是确定类型占用多少字节。

{docstring USize.size}

{docstring ISize.size}

{docstring UInt8.size}

{docstring Int8.size}

{docstring UInt16.size}

{docstring Int16.size}

{docstring UInt32.size}

{docstring Int32.size}

{docstring UInt64.size}

{docstring Int64.size}

## 范围
%%%
file := "Ranges"
tag := "zh-basictypes-uint-h008"
%%%

{docstring ISize.minValue}

{docstring ISize.maxValue}

{docstring Int8.minValue}

{docstring Int8.maxValue}

{docstring Int16.minValue}

{docstring Int16.maxValue}

{docstring Int32.minValue}

{docstring Int32.maxValue}

{docstring Int64.minValue}

{docstring Int64.maxValue}

## 转换
%%%
file := "Conversions"
tag := "zh-basictypes-uint-h009"
%%%

### 往返 `Int`
%%%
file := "To-and-From-___Int___"
tag := "zh-basictypes-uint-h010"
%%%

{docstring ISize.toInt}

{docstring Int8.toInt}

{docstring Int16.toInt}

{docstring Int32.toInt}

{docstring Int64.toInt}


{docstring ISize.ofInt}

{docstring Int8.ofInt}

{docstring Int16.ofInt}

{docstring Int32.ofInt}

{docstring Int64.ofInt}


{docstring ISize.ofIntClamp}

{docstring Int8.ofIntClamp}

{docstring Int16.ofIntClamp}

{docstring Int32.ofIntClamp}

{docstring Int64.ofIntClamp}


{docstring ISize.ofIntLE}

{docstring Int8.ofIntLE}

{docstring Int16.ofIntLE}

{docstring Int32.ofIntLE}

{docstring Int64.ofIntLE}


### 往返 `Nat`
%%%
file := "To-and-From-___Nat___"
tag := "zh-basictypes-uint-h011"
%%%

{docstring USize.ofNat}

{docstring ISize.ofNat}

{docstring UInt8.ofNat}

{docstring Int8.ofNat}

{docstring UInt16.ofNat}

{docstring Int16.ofNat}

{docstring UInt32.ofNat}

{docstring Int32.ofNat}

{docstring UInt64.ofNat}

{docstring Int64.ofNat}

{docstring USize.ofNat32}

{docstring USize.ofNatLT}

{docstring UInt8.ofNatLT}

{docstring UInt16.ofNatLT}

{docstring UInt32.ofNatLT}

{docstring UInt64.ofNatLT}

{docstring USize.ofNatClamp}

{docstring UInt8.ofNatClamp}

{docstring UInt16.ofNatClamp}

{docstring UInt32.ofNatClamp}

{docstring UInt64.ofNatClamp}

{docstring USize.toNat}

{docstring ISize.toNatClampNeg}

{docstring UInt8.toNat}

{docstring Int8.toNatClampNeg}

{docstring UInt16.toNat}

{docstring Int16.toNatClampNeg}

{docstring UInt32.toNat}

{docstring Int32.toNatClampNeg}

{docstring UInt64.toNat}

{docstring Int64.toNatClampNeg}


### 至其他 固定位宽整数
%%%
file := "To-Other-Fixed-Width-Integers"
tag := "zh-basictypes-uint-h012"
%%%

{docstring USize.toUInt8}

{docstring USize.toUInt16}

{docstring USize.toUInt32}

{docstring USize.toUInt64}

{docstring USize.toISize}


{docstring UInt8.toInt8}

{docstring UInt8.toUInt16}

{docstring UInt8.toUInt32}

{docstring UInt8.toUInt64}

{docstring UInt8.toUSize}


{docstring UInt16.toUInt8}

{docstring UInt16.toInt16}

{docstring UInt16.toUInt32}

{docstring UInt16.toUInt64}

{docstring UInt16.toUSize}


{docstring UInt32.toUInt8}

{docstring UInt32.toUInt16}

{docstring UInt32.toInt32}

{docstring UInt32.toUInt64}

{docstring UInt32.toUSize}


{docstring UInt64.toUInt8}

{docstring UInt64.toUInt16}

{docstring UInt64.toUInt32}

{docstring UInt64.toInt64}

{docstring UInt64.toUSize}


{docstring ISize.toInt8}

{docstring ISize.toInt16}

{docstring ISize.toInt32}

{docstring ISize.toInt64}


{docstring Int8.toInt16}

{docstring Int8.toInt32}

{docstring Int8.toInt64}

{docstring Int8.toISize}


{docstring Int16.toInt8}

{docstring Int16.toInt32}

{docstring Int16.toInt64}

{docstring Int16.toISize}


{docstring Int32.toInt8}

{docstring Int32.toInt16}

{docstring Int32.toInt64}

{docstring Int32.toISize}


{docstring Int64.toInt8}

{docstring Int64.toInt16}

{docstring Int64.toInt32}

{docstring Int64.toISize}



### 转浮点数
%%%
file := "To-Floating-Point-Numbers"
tag := "zh-basictypes-uint-h013"
%%%

{docstring ISize.toFloat}

{docstring ISize.toFloat32}

{docstring Int8.toFloat}

{docstring Int8.toFloat32}

{docstring Int16.toFloat}

{docstring Int16.toFloat32}

{docstring Int32.toFloat}

{docstring Int32.toFloat32}

{docstring Int64.toFloat}

{docstring Int64.toFloat32}

{docstring USize.toFloat}

{docstring USize.toFloat32}

{docstring UInt8.toFloat}

{docstring UInt8.toFloat32}

{docstring UInt16.toFloat}

{docstring UInt16.toFloat32}

{docstring UInt32.toFloat}

{docstring UInt32.toFloat32}

{docstring UInt64.toFloat}

{docstring UInt64.toFloat32}

### 往返位向量
%%%
file := "To-and-From-Bitvectors"
tag := "zh-basictypes-uint-h014"
%%%

{docstring ISize.toBitVec}

{docstring ISize.ofBitVec}

{docstring Int8.toBitVec}

{docstring Int8.ofBitVec}

{docstring Int16.toBitVec}

{docstring Int16.ofBitVec}

{docstring Int32.toBitVec}

{docstring Int32.ofBitVec}

{docstring Int64.toBitVec}

{docstring Int64.ofBitVec}

### 有限数的往返
%%%
file := "To-and-From-Finite-Numbers"
tag := "zh-basictypes-uint-h015"
%%%

{docstring USize.toFin}

{docstring UInt8.toFin}

{docstring UInt16.toFin}

{docstring UInt32.toFin}

{docstring UInt64.toFin}

{docstring USize.ofFin}

{docstring UInt8.ofFin}

{docstring UInt16.ofFin}

{docstring UInt32.ofFin}

{docstring UInt64.ofFin}

{docstring USize.repr}

### 致人物
%%%
file := "To-Characters"
tag := "zh-basictypes-uint-h016"
%%%

{name}`Char` 类型是 {name}`UInt32` 的包装器，需要证明包装的整数表示 Unicode 代码点。
该谓词是 {name}`UInt32` API 的一部分。

{docstring UInt32.isValidChar}

{include 2 ManualZh.BasicTypes.UInt.Comparisons}

{include 2 ManualZh.BasicTypes.UInt.Arith}

## 按位运算
%%%
file := "Bitwise-Operations"
tag := "zh-basictypes-uint-h017"
%%%

通常，应使用 Lean 的重载运算符（特别是 {name}`ShiftLeft`、{name}`ShiftRight`、{name}`AndOp`、{name}`OrOp` 和 {name}`XorOp` 的实例）访问 固定位宽整数 上的按位运算。

```lean -show
-- Check that all those instances really exist
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let types := [`ISize, `Int8, `Int16, `Int32, `Int64, `USize, `UInt8, `UInt16, `UInt32, `UInt64]
  let classes := [`ShiftLeft, `ShiftRight, `AndOp, `OrOp, `XorOp]
  for t in types do
    for c in classes do
      elabCommand <| ← `(example : $(mkIdent c):ident $(mkIdent t) := inferInstance)
```

{docstring USize.land}

{docstring ISize.land}

{docstring UInt8.land}

{docstring Int8.land}

{docstring UInt16.land}

{docstring Int16.land}

{docstring UInt32.land}

{docstring Int32.land}

{docstring UInt64.land}

{docstring Int64.land}

{docstring USize.lor}

{docstring ISize.lor}

{docstring UInt8.lor}

{docstring Int8.lor}

{docstring UInt16.lor}

{docstring Int16.lor}

{docstring UInt32.lor}

{docstring Int32.lor}

{docstring UInt64.lor}

{docstring Int64.lor}

{docstring USize.xor}

{docstring ISize.xor}

{docstring UInt8.xor}

{docstring Int8.xor}

{docstring UInt16.xor}

{docstring Int16.xor}

{docstring UInt32.xor}

{docstring Int32.xor}

{docstring UInt64.xor}

{docstring Int64.xor}

{docstring USize.complement}

{docstring ISize.complement}

{docstring UInt8.complement}

{docstring Int8.complement}

{docstring UInt16.complement}

{docstring Int16.complement}

{docstring UInt32.complement}

{docstring Int32.complement}

{docstring UInt64.complement}

{docstring Int64.complement}

{docstring USize.shiftLeft}

{docstring ISize.shiftLeft}

{docstring UInt8.shiftLeft}

{docstring Int8.shiftLeft}

{docstring UInt16.shiftLeft}

{docstring Int16.shiftLeft}

{docstring UInt32.shiftLeft}

{docstring Int32.shiftLeft}

{docstring UInt64.shiftLeft}

{docstring Int64.shiftLeft}

{docstring USize.shiftRight}

{docstring ISize.shiftRight}

{docstring UInt8.shiftRight}

{docstring Int8.shiftRight}

{docstring UInt16.shiftRight}

{docstring Int16.shiftRight}

{docstring UInt32.shiftRight}

{docstring Int32.shiftRight}

{docstring UInt64.shiftRight}


{docstring Int64.shiftRight}
