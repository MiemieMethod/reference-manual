/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
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

set_option verso.docstring.allowMissing true -- TODO remove after docstrings are merged

example := Char

#doc (Manual) "字节吞吐量" =>
%%%
tag := "ByteArray"
%%%

字节数组是一种特殊的数组类型，只能包含 {name}`UInt8` 类型的元素。
由于此限制，它们可以使用更有效的表示形式，而无需指针间接寻址。
与其他数组一样，字节数组在编译代码中表示为 {tech (key := "dynamic arrays")}[动态数组]，Lean 运行时专门优化了数组操作。
修改字节数组的操作首先检查该数组的{ref "reference-counting"}[引用计数]，如果没有其他对该数组的引用，则就地修改。

字节数组没有文字语法。
{name}`List.toByteArray` 可用于从列表文字构造数组。

{docstring ByteArray}

# API 参考
%%%
tag := "zh-basictypes-bytearray-h001"
%%%

## 构造字节数组
%%%
tag := "zh-basictypes-bytearray-h002"
%%%

{docstring ByteArray.empty}

{docstring ByteArray.emptyWithCapacity}

{docstring ByteArray.append}

{docstring ByteArray.fastAppend}

{docstring ByteArray.copySlice}

## 尺寸
%%%
tag := "zh-basictypes-bytearray-h003"
%%%

{docstring ByteArray.size}

{docstring ByteArray.usize}

{docstring ByteArray.isEmpty}

## 查找
%%%
tag := "zh-basictypes-bytearray-h004"
%%%

{docstring ByteArray.get}

{docstring ByteArray.uget}

{docstring ByteArray.get!}

{docstring ByteArray.extract}

## 转换
%%%
tag := "zh-basictypes-bytearray-h005"
%%%

{docstring ByteArray.toList}

{docstring ByteArray.toUInt64BE!}

{docstring ByteArray.toUInt64LE!}

### UTF-8
%%%
tag := "zh-basictypes-bytearray-h006"
%%%

{docstring ByteArray.utf8Decode?}

{docstring ByteArray.utf8DecodeChar?}

{docstring ByteArray.utf8DecodeChar}

## 修改
%%%
tag := "zh-basictypes-bytearray-h007"
%%%

{docstring ByteArray.push}

{docstring ByteArray.set}

{docstring ByteArray.uset}

{docstring ByteArray.set!}

## 迭代
%%%
tag := "zh-basictypes-bytearray-h008"
%%%

{docstring ByteArray.foldl}

{docstring ByteArray.foldlM}

{docstring ByteArray.forIn}

## 迭代器
%%%
tag := "zh-basictypes-bytearray-h009"
%%%

{docstring ByteArray.iter}

{docstring ByteArray.Iterator}

{docstring ByteArray.Iterator.pos}

{docstring ByteArray.Iterator.atEnd}

{docstring ByteArray.Iterator.hasNext}

{docstring ByteArray.Iterator.hasPrev}

{docstring ByteArray.Iterator.curr}

{docstring ByteArray.Iterator.curr'}

{docstring ByteArray.Iterator.next}

{docstring ByteArray.Iterator.next'}

{docstring ByteArray.Iterator.forward}

{docstring ByteArray.Iterator.nextn}

{docstring ByteArray.Iterator.prev}

{docstring ByteArray.Iterator.prevn}

{docstring ByteArray.Iterator.remainingBytes}

{docstring ByteArray.Iterator.toEnd}

## 切片
%%%
tag := "zh-basictypes-bytearray-h010"
%%%

{docstring ByteArray.toByteSlice}

{docstring ByteSlice}

{docstring ByteSlice.beq}

{docstring ByteSlice.byteArray}

{docstring ByteSlice.contains}

{docstring ByteSlice.empty}

{docstring ByteSlice.foldr}

{docstring ByteSlice.foldrM}

{docstring ByteSlice.forM}

{docstring ByteSlice.get}

{docstring ByteSlice.get!}

{docstring ByteSlice.getD}

{docstring ByteSlice.ofByteArray}

{docstring ByteSlice.size}

{docstring ByteSlice.slice}

{docstring ByteSlice.start}

{docstring ByteSlice.stop}

{docstring ByteSlice.toByteArray}


## 元素谓词
%%%
tag := "zh-basictypes-bytearray-h011"
%%%

{docstring ByteArray.findIdx?}

{docstring ByteArray.findFinIdx?}
