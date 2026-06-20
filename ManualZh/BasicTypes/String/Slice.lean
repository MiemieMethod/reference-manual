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

set_option pp.rawOnError true

#doc (Manual) "字符串切片" =>
%%%
tag := "string-api-slice"
%%%

{docstring String.Slice}

{docstring String.toSlice}

{docstring String.sliceFrom}

{docstring String.sliceTo}

{docstring String.Slice.Pos}

# API 参考
%%%
tag := "zh-basictypes-string-slice-h001"
%%%

## 复印
%%%
tag := "zh-basictypes-string-slice-h002"
%%%

{docstring String.Slice.copy}

## 尺寸
%%%
tag := "zh-basictypes-string-slice-h003"
%%%

{docstring String.Slice.isEmpty}

{docstring String.Slice.utf8ByteSize}

## 边界
%%%
tag := "zh-basictypes-string-slice-h004"
%%%

{docstring String.Slice.pos}

{docstring String.Slice.pos!}

{docstring String.Slice.pos?}

{docstring String.Slice.startPos}

{docstring String.Slice.endPos}

{docstring String.Slice.rawEndPos}


### 调整
%%%
tag := "zh-basictypes-string-slice-h005"
%%%

{docstring String.Slice.sliceFrom}

{docstring String.Slice.sliceTo}

{docstring String.Slice.slice}

{docstring String.Slice.slice!}

{docstring String.Slice.drop}

{docstring String.Slice.dropEnd}

{docstring String.Slice.dropEndWhile}

{docstring String.Slice.dropPrefix}

{docstring String.Slice.dropPrefix?}

{docstring String.Slice.dropSuffix}

{docstring String.Slice.dropSuffix?}

{docstring String.Slice.dropWhile}

{docstring String.Slice.take}

{docstring String.Slice.takeEnd}

{docstring String.Slice.takeEndWhile}

{docstring String.Slice.takeWhile}

## 人物
%%%
tag := "zh-basictypes-string-slice-h006"
%%%

{docstring String.Slice.front}

{docstring String.Slice.front?}

{docstring String.Slice.back}

{docstring String.Slice.back?}

## 字节
%%%
tag := "zh-basictypes-string-slice-h007"
%%%

{docstring String.Slice.getUTF8Byte}

{docstring String.Slice.getUTF8Byte!}

## 职位
%%%
tag := "zh-basictypes-string-slice-h008"
%%%

{docstring String.Slice.posGE}

{docstring String.Slice.posGT}

## 搜寻中
%%%
tag := "zh-basictypes-string-slice-h009"
%%%

{docstring String.Slice.contains}

{docstring String.Slice.startsWith}

{docstring String.Slice.endsWith}

{docstring String.Slice.all}

{docstring String.Slice.find?}

{docstring String.Slice.revFind?}

## 操纵
%%%
tag := "zh-basictypes-string-slice-h010"
%%%

{docstring String.Slice.split}

{docstring String.Slice.splitInclusive}

{docstring String.Slice.lines}

{docstring String.Slice.trimAscii}

{docstring String.Slice.trimAsciiEnd}

{docstring String.Slice.trimAsciiStart}

## 迭代
%%%
tag := "zh-basictypes-string-slice-h011"
%%%

{docstring String.Slice.chars}

{docstring String.Slice.revChars}

{docstring String.Slice.positions}

{docstring String.Slice.revPositions}

{docstring String.Slice.bytes}

{docstring String.Slice.revBytes}

{docstring String.Slice.revSplit}

{docstring String.Slice.foldl}

{docstring String.Slice.foldr}

## 转换
%%%
tag := "zh-basictypes-string-slice-h012"
%%%

{docstring String.Slice.isNat}

{docstring String.Slice.toNat!}

{docstring String.Slice.toNat?}


## 平等
%%%
tag := "zh-basictypes-string-slice-h013"
%%%

{docstring String.Slice.beq}

{docstring String.Slice.eqIgnoreAsciiCase}


# 图案
%%%
tag := "zh-basictypes-string-slice-h014"
%%%

字符串切片具有通用搜索模式。
切片上的许多操作不是被定义为仅适用于字符或字符串，而是接受任意模式。
通过定义本节中的类的实例，可以将新类型制成模式。
Lean 标准库提供的实例允许将以下类型用于向前和向后搜索：

:::table +header
* * 型号 Type
  * 含义
* * {name}`Char`
  * 匹配提供的字符
*
  * {lean}`Char → Bool`
  * 匹配任何满足谓词的字符
* * {lean}`String`
  * 匹配给定字符串的出现次数
* * {lean}`String.Slice`
  * 匹配切片表示的字符串的出现次数
:::

{docstring String.Slice.Pattern.ToForwardSearcher}

{docstring String.Slice.Pattern.ForwardPattern}

{docstring String.Slice.Pattern.ToBackwardSearcher}

{docstring String.Slice.Pattern.BackwardPattern +allowMissing}

# 职位
%%%
tag := "zh-basictypes-string-slice-h015"
%%%

## 查找
%%%
tag := "zh-basictypes-string-slice-h016"
%%%

因为它们保留了对从中绘制它们的切片的引用，所以切片位置允许查找单个字符或字节。

{docstring String.Slice.Pos.byte}

{docstring String.Slice.Pos.get}

{docstring String.Slice.Pos.get!}

{docstring String.Slice.Pos.get?}

## 递增和递减
%%%
tag := "zh-basictypes-string-slice-h017"
%%%

{docstring String.Slice.Pos.prev}

{docstring String.Slice.Pos.prev!}

{docstring String.Slice.Pos.prev?}

{docstring String.Slice.Pos.prevn}

{docstring String.Slice.Pos.next}

{docstring String.Slice.Pos.next!}

{docstring String.Slice.Pos.next?}

{docstring String.Slice.Pos.nextn}

## 其他字符串或切片
%%%
tag := "zh-basictypes-string-slice-h018"
%%%

{docstring String.Slice.Pos.cast}

{docstring String.Slice.Pos.ofSlice}

{docstring String.Slice.Pos.str}

{docstring String.Slice.Pos.copy}

{docstring String.Slice.Pos.ofSliceFrom}

{docstring String.Slice.Pos.ofSliceTo}
