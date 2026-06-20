/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.BasicTypes.List.Predicates
import ManualZh.BasicTypes.List.Comparisons
import ManualZh.BasicTypes.List.Partitioning
import ManualZh.BasicTypes.List.Modification
import ManualZh.BasicTypes.List.Transformation

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxHeartbeats 250000


#doc (Manual) "链表" =>
%%%
tag := "List"
%%%

链表，实现为 {tech}[归纳类型] {name}`List`，包含元素的有序序列。
与 {ref "Array"}[arrays] 不同，Lean 根据归纳类型的普通规则编译列表；但是，列表上的某些操作被使用 {attr}`csimp` 机制的编译代码中的尾递归等效项所取代。{TODO}[从此处写入和外部引用]
Lean 提供文字列表和构造函数 {name}`List.cons` 的语法。

{docstring List}

# 句法
%%%
tag := "list-syntax"
%%%

列表文字写在方括号中，列表的元素用逗号分隔。
将元素添加到列表前面的构造函数 {name}`List.cons` 由中缀运算符 {keywordOf «term_::_»}`::` 表示。
列表的语法既可以用在普通术语中，也可以用在模式中。

:::syntax term (title := "List Literals")
```grammar
[$_,*]
```

{includeDocstring «term[_]»}

:::

:::syntax term (title := "List Construction")
```grammar
$_ :: $_
```

{includeDocstring «term_::_»}

:::

:::example "Constructing Lists"
所有这些示例都是等效的：
```lean
example : List Nat := [1, 2, 3]
example : List Nat := 1 :: [2, 3]
example : List Nat := 1 :: 2 :: [3]
example : List Nat := 1 :: 2 :: 3 :: []
example : List Nat := 1 :: 2 :: 3 :: .nil
example : List Nat := 1 :: 2 :: .cons 3 .nil
example : List Nat := .cons 1 (.cons 2 (.cons 3 .nil))
```
:::

:::example "Pattern Matching and Lists"
所有这些功能都是等效的：
```lean
def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split' : List α → List α × List α
  | .nil => (.nil, .nil)
  | x :: [] => (.singleton x, .nil)
  | x :: x' :: xs =>
    let (ys, zs) := split xs
    (x :: ys, x' :: zs)
```
```lean
def split'' : List α → List α × List α
  | .nil => (.nil, .nil)
  | .cons x .nil => (.singleton x, .nil)
  | .cons x (.cons x' xs) =>
    let (ys, zs) := split xs
    (.cons x ys, .cons x' zs)
```
```lean -show
-- Test claim
example : @split = @split' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split', List.singleton]

example : @split = @split'' := by
  funext α xs
  induction xs using split.induct <;> simp [split, split'', List.singleton]
```
:::


# 性能说明
%%%
tag := "list-performance"
%%%

列表的表示形式不会被编译器覆盖或修改：它们是链表，每个元素都有一个指针间接寻址。
计算列表的长度需要完全遍历，修改列表中的元素需要遍历并重新分配修改元素之前的列表前缀。
由于 Lean 基于引用计数的内存管理，诸如 {name}`List.map` 之类的遍历列表、为先前列表中的每个列表分配新的 {name}`List.cons` 构造函数的操作可以在没有其他引用时重用原始列表的内存。

由于列表在规范中发挥着重要作用，大多数列表函数都使用结构递归尽可能简单地编写。
这使得通过归纳编写证明变得更容易，但这也意味着这些操作消耗的堆栈空间与列表的长度成正比。
许多列表函数都有尾递归版本，它们与非尾递归版本等效，但在推理时更难以使用。
在编译的代码中，自动使用尾递归版本而不是非尾递归版本。

# API 参考
%%%
tag := "list-api-reference"
%%%

{include 2 ManualZh.BasicTypes.List.Predicates}

## 构建列表
%%%
tag := "zh-basictypes-list-h004"
%%%

{docstring List.singleton}

{docstring List.concat}

{docstring List.replicate}

{docstring List.replicateTR}

{docstring List.ofFn}

{docstring List.append}

{docstring List.appendTR}

{docstring List.range}

{docstring List.range'}

{docstring List.range'TR}

{docstring List.finRange}

## 长度
%%%
tag := "zh-basictypes-list-h005"
%%%

{docstring List.length}

{docstring List.lengthTR}

{docstring List.isEmpty}

## 首尾
%%%
tag := "zh-basictypes-list-h006"
%%%

{docstring List.head}

{docstring List.head?}

{docstring List.headD}

{docstring List.head!}

{docstring List.tail}

{docstring List.tail!}

{docstring List.tail?}

{docstring List.tailD}


## 查找
%%%
tag := "zh-basictypes-list-h007"
%%%

{docstring List.get}

{docstring List.getD}

{docstring List.getLast}

{docstring List.getLast?}

{docstring List.getLastD}

{docstring List.getLast!}

{docstring List.lookup}

{docstring List.max?}

{docstring List.min?}

## 查询
%%%
tag := "zh-basictypes-list-h008"
%%%

{docstring List.count}

{docstring List.countP}

{docstring List.idxOf}

{docstring List.idxOf?}

{docstring List.finIdxOf?}

{docstring List.find?}

{docstring List.findFinIdx?}

{docstring List.findIdx}

{docstring List.findIdx?}

{docstring List.findM?}

{docstring List.findSome?}

{docstring List.findSomeM?}

## 转换
%%%
tag := "zh-basictypes-list-h009"
%%%

{docstring List.toArray}

{docstring List.toArrayImpl}

{docstring List.toByteArray}

{docstring List.toFloatArray}

{docstring List.toString}


{include 2 ManualZh.BasicTypes.List.Modification}

## 排序
%%%
tag := "zh-basictypes-list-h010"
%%%

{docstring List.mergeSort}

{docstring List.merge}

## 迭代
%%%
tag := "zh-basictypes-list-h011"
%%%

{docstring List.iter}

{docstring List.iterM}

{docstring List.forA}

{docstring List.forM}

{docstring List.firstM}

{docstring List.sum}

### 褶皱
%%%
tag := "zh-basictypes-list-h012"
%%%

:::paragraph
折叠是使用函数组合列表元素的运算符。
它们有两种类型，以函数调用的嵌套命名：

: {deftech}[左折]

  左折叠将从列表头部到末尾的元素组合在一起。
  列表的头部与初始值组合，然后该操作的结果与下一个值组合，依此类推。

: {deftech}[右折]

  右折叠从列表末尾到开头组合元素，就好像每个 {name List.cons}`cons` 构造函数都被替换为对组合函数的调用，并且 {name List.nil}`nil` 被替换为初始值。

单子折叠（用 `-M` 后缀表示）允许组合函数使用 {tech}[monad] 中的效果，其中可能包括提前停止折叠。
:::

{docstring List.foldl}

{docstring List.foldlM}

{docstring List.foldlRecOn}

{docstring List.foldr}

{docstring List.foldrM}

{docstring List.foldrRecOn}

{docstring List.foldrTR}

{include 2 ManualZh.BasicTypes.List.Transformation}

## 过滤
%%%
tag := "zh-basictypes-list-h013"
%%%

{docstring List.filter}

{docstring List.filterTR}

{docstring List.filterM}

{docstring List.filterRevM}

{docstring List.filterMap}

{docstring List.filterMapTR}

{docstring List.filterMapM}

{include ManualZh.BasicTypes.List.Partitioning}

## 元素谓词
%%%
tag := "zh-basictypes-list-h014"
%%%

{docstring List.contains}

{docstring List.elem}

{docstring List.all}

{docstring List.allM}

{docstring List.any}

{docstring List.anyM}

{docstring List.and}

{docstring List.or}

{include 2 ManualZh.BasicTypes.List.Comparisons}

## 终止助手
%%%
tag := "zh-basictypes-list-h015"
%%%

{docstring List.attach}

{docstring List.attachWith}

{docstring List.unattach}

{docstring List.pmap}
