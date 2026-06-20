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
set_option maxHeartbeats 500000

example := Char

#doc (Manual) "储备" =>
%%%
file := "Arrays"
tag := "Array"
%%%

{lean}`Array` 类型表示元素序列，可通过其在序列中的位置进行寻址。
Lean 特别支持数组：
 * 它们有一个_逻辑模型_，根据元素列表指定它们的行为，元素列表指定数组上每个操作的含义。
 * 它们在编译代码中具有优化的运行时表示形式，如 {tech (key := "dynamic arrays")}[动态数组]，并且 Lean 运行时专门优化了数组操作。
 * 有 {ref "array-syntax"}[数组文字语法] 用于编写数组。

在编译代码中，数组比列表或其他序列更有效。
在某种程度上，这是因为它们提供了良好的局部性：因为序列的所有元素在内存中彼此相邻，所以可以有效地使用处理器的缓存。
更重要的是，如果只有一个对数组的引用，则可以通过突变来实现可能复制或分配数据结构的操作。
以只有一个唯一引用的方式使用数组的 Lean 代码（即使用它 {deftech (key := "linearly")}_线性_）避免了持久数据结构的性能开销，同时仍然像普通的纯函数程序一样方便地写入、读取和证明。

# 逻辑模型
%%%
file := "Logical-Model"
tag := "zh-basictypes-array-h001"
%%%

{docstring Array}

数组的逻辑模型是包含单个字段的结构，该字段是元素列表。
当在低级别指定和证明数组处理函数的属性时，这很方便。

# 运行时表示
%%%
file := "Run-Time-Representation"
tag := "array-runtime"
%%%

Lean 的数组是 {deftech (key := "dynamic arrays")}_动态数组_，它们是具有定义容量的连续内存块，通常并非全部都在使用。
只要数组中的元素数量小于容量，就可以将新项目添加到末尾，而无需重新分配或移动数据。
将项目添加到没有额外空间的数组会导致容量加倍的重新分配。
摊销开销与数组的大小成线性比例。
数组中的值按照 {ref "inductive-types-ffi"}[有关外部函数接口的部分] 中的描述进行表示。

:::figure "Memory layout of arrays" (tag := "arrayffi")
```diagram
open Illuminate in
open Manual.Diagram in
layoutDiagram [
  ("m_header", .header, txt "Lean object header"),
  ("m_size", .size_t, twoLine "Byte count" "size_t"),
  ("m_capacity", .size_t, twoLine "Allocated space" "size_t"),
  ("m_data", .data none, some <| .styledText (base := fieldLabelStyle) <|
    "Array data" ++ "\n" ++ "Array of " ++ family "monospace" "lean_object *")
]
```
:::

在对象头之后，数组包含：

: 尺寸

  当前存储在数组中的对象数量

: 容量

  适合为数组分配的内存的对象数量

: 数据

  数组中的值

Lean 运行时中的许多数组函数通过查询对象头中的引用计数来检查它们是否具有对其参数的独占访问权。
如果确实如此，并且数组的容量足够，则可以更改现有数组，而不是分配新内存。
否则，必须分配一个新数组。

## 性能说明
%%%
file := "Performance-Notes"
tag := "array-performance"
%%%


尽管它们看起来是普通的构造函数和投影，但 {name}`Array.mk` 和 {name}`Array.toList` 在编译代码中所花费的时间与数组大小成线性关系。
这是因为链表和打包数组之间的转换必须访问每个元素。

可变数组可用于编写非常高效的代码。
然而，它们是一种较差的持久数据结构。
更新共享数组排除了突变，并且需要与数组大小成线性关系的时间。
在性能关键型代码中使用数组时，确保以 {tech (key := "linearly")}[线性] 方式使用数组非常重要。

# 句法
%%%
file := "Syntax"
tag := "array-syntax"
%%%

数组字面量允许直接在代码中写入数组。
它们可以用在表达式或模式上下文中。

:::syntax term (title := "Array Literals")
数组文字以 `#[` 开头，包含以逗号分隔的术语序列，以 `]` 结尾。

```grammar
#[$t,*]
```
:::

::::keepEnv
:::example "Array Literals"
数组文字可以用作表达式或模式。

```lean
def oneTwoThree : Array Nat := #[1, 2, 3]

#eval
  match oneTwoThree with
  | #[x, y, z] => some ((x + z) / y)
  | _ => none
```
:::
::::

此外，可以使用以下语法提取 {ref "subarray"}[子数组]：
:::syntax term (title := "Sub-Arrays")
起始索引后跟冒号构造一个子数组，其中包含从起始索引开始（含）的值：
```grammar
$t[$t:term :]
```

提供开始索引和结束索引会构造一个子数组，其中包含从开始索引（包括）到结束索引（不包括）的值：
```grammar
$t[$t:term : $_:term]
```
:::

::::keepEnv
:::example "Sub-Array Syntax"

数组 {lean}`ten` 包含前十个自然数。
```lean
def ten : Array Nat :=
  .range 10
```

可以使用子数组语法构造表示 {lean}`ten` 后半部分的子数组：
```lean (name := subarr1)
#eval ten[5:]
```
```leanOutput subarr1
#[5, 6, 7, 8, 9].toSubarray
```

类似地，可以通过提供停止点来构造包含 2 到 5 的子数组：
```lean (name := subarr2)
#eval ten[2:6]
```
```leanOutput subarr2
#[2, 3, 4, 5].toSubarray
```

因为子数组仅存储底层数组中感兴趣的开始和结束索引，所以可以恢复数组本身：
```lean (name := subarr3)
#eval ten[2:6].array == ten
```
```leanOutput subarr3
true
```
:::
::::

# API 参考
%%%
file := "API-Reference"
tag := "array-api"
%%%

## 构造数组
%%%
file := "Constructing-Arrays"
tag := "zh-basictypes-array-h006"
%%%

{docstring Array.empty}

{docstring Array.emptyWithCapacity}

{docstring Array.singleton}

{docstring Array.range}

{docstring Array.range'}

{docstring Array.finRange}

{docstring Array.ofFn}

{docstring Array.replicate}

{docstring Array.append}

{docstring Array.appendList}

{docstring Array.leftpad}

{docstring Array.rightpad}

## 尺寸
%%%
file := "Size"
tag := "zh-basictypes-array-h007"
%%%

{docstring Array.size}

{docstring Array.usize}

{docstring Array.isEmpty}

## 查找
%%%
file := "Lookups"
tag := "zh-basictypes-array-h008"
%%%

{docstring Array.extract}

{docstring Array.getD}

{docstring Array.uget}

{docstring Array.back}

{docstring Array.back?}

{docstring Array.back!}

{docstring Array.getMax?}

## 查询
%%%
file := "Queries"
tag := "zh-basictypes-array-h009"
%%%

{docstring Array.count}

{docstring Array.countP}

{docstring Array.idxOf}

{docstring Array.idxOf?}

{docstring Array.finIdxOf?}

## 转换
%%%
file := "Conversions"
tag := "zh-basictypes-array-h010"
%%%

{docstring Array.toList}

{docstring Array.toListRev}

{docstring Array.toListAppend}

{docstring Array.toVector}

{docstring Array.toSubarray}

{docstring Array.ofSubarray}


## 修改
%%%
file := "Modification"
tag := "zh-basictypes-array-h011"
%%%

{docstring Array.push}

{docstring Array.pop}

{docstring Array.popWhile}

{docstring Array.erase}

{docstring Array.eraseP}

{docstring Array.eraseIdx}

{docstring Array.eraseIdx!}

{docstring Array.eraseIdxIfInBounds}

{docstring Array.eraseReps}

{docstring Array.swap}

{docstring Array.swapIfInBounds}

{docstring Array.swapAt}

{docstring Array.swapAt!}

{docstring Array.replace}

{docstring Array.set}

{docstring Array.set!}

{docstring Array.setIfInBounds}

{docstring Array.uset}

{docstring Array.modify}

{docstring Array.modifyM}

{docstring Array.modifyOp}

{docstring Array.insertIdx}

{docstring Array.insertIdx!}

{docstring Array.insertIdxIfInBounds}

{docstring Array.reverse}

{docstring Array.take}

{docstring Array.takeWhile}

{docstring Array.drop}

{docstring Array.shrink}

{docstring Array.flatten}

{docstring Array.getEvenElems}

## 排序数组
%%%
file := "Sorted-Arrays"
tag := "zh-basictypes-array-h012"
%%%

{docstring Array.qsort}

{docstring Array.qsortOrd}

{docstring Array.insertionSort}

{docstring Array.binInsert}

{docstring Array.binInsertM}

{docstring Array.binSearch}

{docstring Array.binSearchContains}



## 迭代
%%%
file := "Iteration"
tag := "zh-basictypes-array-h013"
%%%

{docstring Array.iter}

{docstring Array.iterFromIdx}

{docstring Array.iterM}

{docstring Array.iterFromIdxM}

{docstring Array.foldr}

{docstring Array.foldrM}

{docstring Array.foldl}

{docstring Array.foldlM}

{docstring Array.forM}

{docstring Array.forRevM}

{docstring Array.firstM}

{docstring Array.sum}

## 转型
%%%
file := "Transformation"
tag := "zh-basictypes-array-h014"
%%%

{docstring Array.map}

{docstring Array.mapMono}

{docstring Array.mapM}

{docstring Array.mapM'}

{docstring Array.mapMonoM}

{docstring Array.mapIdx}

{docstring Array.mapIdxM}

{docstring Array.mapFinIdx}

{docstring Array.mapFinIdxM}

{docstring Array.flatMap}

{docstring Array.flatMapM}

{docstring Array.zip}

{docstring Array.zipWith}

{docstring Array.zipWithAll}

{docstring Array.zipIdx}

{docstring Array.unzip}


## 过滤
%%%
file := "Filtering"
tag := "zh-basictypes-array-h015"
%%%

{docstring Array.filter}

{docstring Array.filterM}

{docstring Array.filterRevM}

{docstring Array.filterMap}

{docstring Array.filterMapM}

{docstring Array.filterSepElems}

{docstring Array.filterSepElemsM}

## 分区
%%%
file := "Partitioning"
tag := "zh-basictypes-array-h016"
%%%

{docstring Array.partition}

{docstring Array.groupByKey}


## 元素谓词
%%%
file := "Element-Predicates"
tag := "zh-basictypes-array-h017"
%%%

{docstring Array.contains}

{docstring Array.elem}

{docstring Array.find?}

{docstring Array.findRev?}

{docstring Array.findIdx}

{docstring Array.findIdx?}

{docstring Array.findIdxM?}

{docstring Array.findFinIdx?}

{docstring Array.findM?}

{docstring Array.findRevM?}

{docstring Array.findSome?}

{docstring Array.findSome!}

{docstring Array.findSomeM?}

{docstring Array.findSomeRev?}

{docstring Array.findSomeRevM?}

{docstring Array.all}

{docstring Array.allM}

{docstring Array.any}

{docstring Array.anyM}

{docstring Array.allDiff}

{docstring Array.isEqv}

## 比较
%%%
file := "Comparisons"
tag := "zh-basictypes-array-h018"
%%%

{docstring Array.isPrefixOf}

{docstring Array.lex}

## 终止助手
%%%
file := "Termination-Helpers"
tag := "zh-basictypes-array-h019"
%%%

{docstring Array.attach}

{docstring Array.attachWith}

{docstring Array.unattach}

{docstring Array.pmap}

{include 1 ManualZh.BasicTypes.Array.Subarray}

{include 0 ManualZh.BasicTypes.Array.FFI}
