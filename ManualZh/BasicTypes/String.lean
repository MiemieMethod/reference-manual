/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.BasicTypes.String.Logical
import ManualZh.BasicTypes.String.Literals
import ManualZh.BasicTypes.String.FFI
import ManualZh.BasicTypes.String.Substrings
import ManualZh.BasicTypes.String.Slice

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 250000


#doc (Manual) "弦乐" =>
%%%
tag := "String"
%%%


字符串表示 Unicode 文本。
Lean 特别支持字符串：
 * 它们有一个_逻辑模型_，根据包含 UTF-8 标量值的 {name}`ByteArray` 指定其行为。
 * 在编译的代码中，它们具有运行时表示，还包括缓存长度，以标量值的数量来衡量。
   Lean 运行时提供字符串操作的优化实现。
 * 有 {ref "string-syntax"}[字符串文字语法] 用于编写字符串。

UTF-8 是可变宽度编码。
字符可以被编码为一、二、三或四字节代码单元。
事实上，字符串是 UTF-8 编码的字节数组，这一事实在 API 中可见：
 * 没有任何操作可以将特定字符从字符串中投影出来，因为这将是一个性能陷阱。 {ref "string-iterators"}[在循环中使用迭代器]而不是 {name}`Nat`。
 * 字符串由 {name}`String.Pos` 索引，它内部记录_字节计数_而不是_字符计数_，因此需要恒定时间。
   {name}`String.Pos` 包含字节计数实际上指向 UTF-8 代码单元的开头的证明。
   除了 `0` 之外，这些不应直接构造，而应使用 {name}`String.next` 和 {name}`String.prev` 进行更新。

{include 0 ManualZh.BasicTypes.String.Logical}

# 运行时表示
%%%
tag := "string-runtime"
%%%

:::figure "Memory layout of strings" (tag := "stringffi")
```diagram
open Illuminate in
open Manual.Diagram in
layoutDiagram [
  ("m_header", .header, txt "Lean object header"),
  ("m_size", .size_t, twoLine "Byte count" "size_t"),
  ("m_capacity", .size_t, twoLine "Allocated space" "size_t"),
  ("m_length", .size_t, twoLine "Characters" "size_t"),
  ("m_data", .data none,
    some <| .styledText (base := fieldLabelStyle) <|
      "String data\n" ++ family "monospace" "char" ++ " array"),
  ("'\\0'", .data (some 30), none)
]
```
:::

字符串表示为字节的 {tech}[动态数组]，以 UTF-8 编码。
在对象头之后，字符串包含：

: 字节数

  当前包含有效字符串数据的字节数

: 容量

  当前为字符串分配的字节数

: 长度

  编码字符串的长度，由于UTF-8多字节字符，可能比字节数短

: 数据

  字符串中的实际字符数据，以 null 结尾

Lean 运行时中的许多字符串函数通过查阅对象标头中的引用计数来检查它们是否具有对其参数的独占访问权。
如果确实如此，并且字符串的容量足够，则可以更改现有字符串，而不是分配新内存。
否则，必须分配一个新字符串。


## 性能说明
%%%
tag := "string-performance"
%%%

尽管它们看起来是普通的构造函数和投影，但 {name}`String.ofByteArray` 和 {name}`String.toByteArray` 所花费的时间与字符串的长度成线性关系。
这是因为字节数组和字符串没有相同的表示形式，因此必须将字节数组的内容复制到新对象中。


{include 0 ManualZh.BasicTypes.String.Literals}

# API 参考
%%%
tag := "string-api"
%%%


## 建设中
%%%
tag := "string-api-build"
%%%


{docstring String.singleton}

{docstring String.append}

{docstring String.join}

{docstring String.intercalate}

## 转换
%%%
tag := "string-api-convert"
%%%


{docstring String.toList}

{docstring String.isNat}

{docstring String.toNat?}

{docstring String.toNat!}

{docstring String.isInt}

{docstring String.toInt?}

{docstring String.toInt!}

{docstring String.toFormat}

## 特性
%%%
tag := "string-api-props"
%%%

{docstring String.isEmpty}

{docstring String.length}

## 职位
%%%
tag := "string-api-valid-pos"
%%%

{docstring String.Pos}

### 在字符串中

{docstring String.startPos}

{docstring String.endPos}

{docstring String.pos}

{docstring String.pos?}

{docstring String.pos!}

{docstring String.extract}

### 查找

{docstring String.Pos.get}

{docstring String.Pos.get!}

{docstring String.Pos.get?}

{docstring String.Pos.set}

### 修改

{docstring String.Pos.modify}

{docstring String.Pos.byte}

### 调整

{docstring String.Pos.prev}

{docstring String.Pos.prev!}

{docstring String.Pos.prev?}

{docstring String.Pos.next}

{docstring String.Pos.next!}

{docstring String.Pos.next?}

### 其他琴弦

{docstring String.Pos.cast}

{docstring String.Pos.ofCopy}

{docstring String.Pos.toSetOfLE}

{docstring String.Pos.toModifyOfLE}

{docstring String.Pos.toSlice}

## 原始头寸
%%%
tag := "string-api-pos"
%%%

{docstring String.Pos.Raw}

### 字节位置

{docstring String.Pos.Raw.offsetOfPos}

### 有效性

{docstring String.Pos.Raw.isValid}

{docstring String.Pos.Raw.isValidForSlice}

### 边界

{docstring String.rawEndPos}

{docstring String.Pos.Raw.atEnd}

### 比较

{docstring String.Pos.Raw.min}

{docstring String.Pos.Raw.byteDistance}

{docstring String.Pos.Raw.substrEq}

### 调整

{docstring String.Pos.Raw.prev}

{docstring String.Pos.Raw.next}

{docstring String.Pos.Raw.next'}

{docstring String.Pos.Raw.nextUntil}

{docstring String.Pos.Raw.nextWhile}

{docstring String.Pos.Raw.inc}

{docstring String.Pos.Raw.increaseBy}

{docstring String.Pos.Raw.offsetBy}

{docstring String.Pos.Raw.dec}

{docstring String.Pos.Raw.decreaseBy}

{docstring String.Pos.Raw.unoffsetBy}

### 字符串查找

{docstring String.Pos.Raw.extract}

{docstring String.Pos.Raw.get}

{docstring String.Pos.Raw.get!}

{docstring String.Pos.Raw.get'}

{docstring String.Pos.Raw.get?}

### 字符串修改

{docstring String.Pos.Raw.set}

{docstring String.Pos.Raw.modify}

## 查找和修改
%%%
tag := "string-api-lookup"
%%%

选择字符串的子区域（例如，其前缀或后缀）的操作将 {ref "string-api-slice"}[slice] 返回到原始字符串中，而不是分配新字符串。
使用 {name}`String.Slice.copy` 将切片转换为新字符串。

{docstring String.take}

{docstring String.takeWhile}

{docstring String.takeEnd}

{docstring String.takeEndWhile}

{docstring String.drop}

{docstring String.dropWhile}

{docstring String.dropEnd}

{docstring String.dropEndWhile}

{docstring String.dropPrefix?}

{docstring String.dropPrefix}

{docstring String.dropSuffix?}

{docstring String.dropSuffix}

{docstring String.trimAscii}

{docstring String.trimAsciiStart}

{docstring String.trimAsciiEnd}

{docstring String.removeLeadingSpaces}

{docstring String.front}

{docstring String.back}

{docstring String.find}

{docstring String.revFind?}

{docstring String.contains}

{docstring String.replace}

{docstring String.find}

## 折叠和聚集
%%%
tag := "string-api-fold"
%%%

{docstring String.map}

{docstring String.foldl}

{docstring String.foldr}

{docstring String.all}

{docstring String.any}

## 比较
%%%
tag := "string-api-compare"
%%%

{inst}`LT String` 实例是通过基于 {inst}`LT Char` 实例的字符串的字典顺序来定义的。
从逻辑上讲，这是通过建模字符串的列表上的字典顺序来建模的，因此 `List.Lex` 定义了顺序。
它是可判定的，并且判定过程在运行时被利用字符串的运行时表示的高效代码覆盖。

{docstring String.le}

{docstring String.firstDiffPos}

{docstring String.isPrefixOf}

{docstring String.startsWith}

{docstring String.endsWith}

{docstring String.decEq}

{docstring String.hash}

## 操纵
%%%
tag := "string-api-modify"
%%%

{docstring String.splitToList}

{docstring String.splitOn}

{docstring String.push}

{docstring String.pushn}

{docstring String.capitalize}

{docstring String.decapitalize}

{docstring String.toUpper}

{docstring String.toLower}

## 遗留迭代器
%%%
tag := "string-iterators"
%%%

为了向后兼容，Lean 包括旧版字符串迭代器。
基本上，{name}`String.Legacy.Iterator` 是一对字符串和字符串中的有效位置。
迭代器提供了获取当前字符（{name String.Legacy.Iterator.curr}`curr`）、替换当前字符（{name String.Legacy.Iterator.setCurr}`setCurr`）、检查迭代器是否可以向左或向右移动（分别为 {name String.Legacy.Iterator.hasPrev}`hasPrev` 和 {name String.Legacy.Iterator.hasNext}`hasNext`）以及移动迭代器（分别为 {name String.Legacy.Iterator.prev}`prev` 和 {name String.Legacy.Iterator.next}`next`）的函数。
客户端负责检查是否到达了字符串的开头或结尾；否则，迭代器确保其位置始终指向一个字符。
但是，{name}`String.Legacy.Iterator` 不包含这些格式良好条件的证明，这可能使其更难以在经过验证的代码中使用。

{docstring String.Legacy.Iterator}

{docstring String.Legacy.iter}

{docstring String.Legacy.mkIterator}

{docstring String.Legacy.Iterator.curr}

{docstring String.Legacy.Iterator.curr'}

{docstring String.Legacy.Iterator.hasNext}

{docstring String.Legacy.Iterator.next}

{docstring String.Legacy.Iterator.next'}

{docstring String.Legacy.Iterator.forward}

{docstring String.Legacy.Iterator.nextn}

{docstring String.Legacy.Iterator.hasPrev}

{docstring String.Legacy.Iterator.prev}

{docstring String.Legacy.Iterator.prevn}

{docstring String.Legacy.Iterator.atEnd}

{docstring String.Legacy.Iterator.toEnd}

{docstring String.Legacy.Iterator.setCurr}

{docstring String.Legacy.Iterator.find}

{docstring String.Legacy.Iterator.foldUntil}

{docstring String.Legacy.Iterator.extract}

{docstring String.Legacy.Iterator.remainingToString}

{docstring String.Legacy.Iterator.remainingBytes}

{docstring String.Legacy.Iterator.pos}

{docstring String.Legacy.Iterator.toString}

{include 2 ManualZh.BasicTypes.String.Slice}

{include 2 ManualZh.BasicTypes.String.Substrings}





## 元编程
%%%
tag := "string-api-meta"
%%%

{docstring String.toName}

{docstring String.quote}


## 编码
%%%
tag := "string-api-encoding"
%%%

{docstring String.getUTF8Byte}

{docstring String.utf8ByteSize}

{docstring String.utf8EncodeChar}

{docstring String.fromUTF8}

{docstring String.fromUTF8?}

{docstring String.fromUTF8!}

{docstring String.toUTF8}

{docstring String.crlfToLf}


{include 0 ManualZh.BasicTypes.String.FFI}
