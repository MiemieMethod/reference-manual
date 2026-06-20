/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.BasicTypes.Maps.TreeSet
import ManualZh.BasicTypes.Maps.TreeMap

import Std.Data.HashMap
import Std.Data.HashMap.Raw
import Std.Data.HashMap.RawLemmas
import Std.Data.DHashMap
import Std.Data.DHashMap.Raw
import Std.Data.DHashMap.RawLemmas
import Std.Data.ExtHashMap
import Std.Data.TreeMap
import Std.Data.DTreeMap
import Std.Data.DTreeMap.Raw
import Std.Data.ExtHashSet
import Std.Data.TreeSet
import Std.Data.HashSet
import Std.Data.HashSet.Raw
import Std.Data.HashSet.RawLemmas

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option maxHeartbeats 1000000

#doc (Manual) "地图和套装" =>
%%%
tag := "maps"
%%%

{deftech}_map_ 是将键与值关联起来的数据结构。
它们也称为 {deftech}_dictionaries_、{deftech}_associative arrays_，或简称为哈希表。


::::paragraph
在 Lean 中，地图可能具有以下属性：

: 表示

  映射在内存中的表示可以是树或哈希表。
  当共享数据结构的 {ref "reference-counting"}[引用] 时，基于树的表示会更好，因为哈希表基于 {ref "Array"}[数组]。
  当引用不唯一时，数组将在修改时完整复制，而在修改树时只需复制从树根到修改节点的路径。
  另一方面，当引用不共享时，哈希表会更有效，因为非共享数组可以在恒定时间内修改。
  此外，基于树的映射按顺序存储数据，从而支持数据的有序遍历。

: 外延性

  映射可以被视为从键到值的部分函数。
  {deftech (key := "Extensional maps")}_Extensional 映射_{index (subterm := "extensional")}[map] 是 命题等价 与此解释匹配的映射。
  这可以方便推理，但也排除了一些能够区分它们的有用操作。
  一般来说，仅在需要验证时才应使用外延映射。

: 是否依赖

  {deftech}_dependent map_{index (subterm := "dependent")}[map] 是其中每个值的类型由其对应的键确定的类型，而不是恒定的。
  从属地图具有更强的表达能力，但也更难使用。
  他们对用户提出了更多要求。
  例如，{name Std.DHashMap}`DHashMap` 上的许多操作需要 {name}`LawfulBEq` 实例而不是 {name}`BEq`。

::::

::::: leanSection

```lean -show
open Std
```


:::table +header
*
  - 地图
  - 表示
  - 外延性？
  - 依赖？

*
  - {name}`TreeMap`
  - 树
  - 否
  - 否

*
  - {name}`DTreeMap`
  - 树
  - 否
  - 是的

*
  - {name}`HashMap`
  - 哈希表
  - 否
  - 否

*
  - {name}`DHashMap`
  - 哈希表
  - 否
  - 是的

*
  - {name}`ExtHashMap`
  - 哈希表
  - 是的
  - 否

*
  - {name}`ExtDHashMap`
  - 哈希表
  - 是的
  - 是的

:::

:::::

通过将其值类型设置为 {name}`Unit`，地图始终可以用作集合。
提供了以下集合类型：
 * {name}`Std.HashSet`是一个基于哈希表的集合。其性能特征类似于{name}`Std.HashMap`：它基于数组，可以高效更新，但仅限于不共享时。
 * {name}`Std.TreeSet`是一个基于平衡树的集合。其性能特征类似于{name}`Std.TreeMap`。
 * {name}`Std.ExtHashSet` 是一种扩展哈希集类型，它与有限集的数学概念相匹配：如果两个集合包含相同的元素，则它们相等。


# 图书馆设计
%%%
tag := "zh-basictypes-maps-h001"
%%%

地图和集合上的所有基本操作都经过充分验证。
对于使用列表实现的更简单的模型，它们被证明是正确的。
同时，地图和集合具有可预测的性能。

某些类型包括尚未完全验证的附加操作。
这些操作很有用，并不是所有程序都需要充分验证。
示例包括 {name Std.HashMap.partition}`HashMap.partition` 和 {name Std.TreeMap.filterMap}`TreeMap.filterMap`。

## 融合运营
%%%
tag := "zh-basictypes-maps-h002"
%%%

根据表的预先存在的内容修改表是很常见的。
为了避免必须遍历数据结构两次，在“融合”变体中提供了许多查询/修改对，这些变体在修改映射或集合的同时执行查询。
在某些情况下，查询的结果会影响修改。

例如，{name}`Std.HashMap` 提供 {name Std.HashMap.containsThenInsert}`containsThenInsert`，它将键值对插入到映射中，同时发出信号通知以前是否已找到该映射；以及 {name Std.HashMap.containsThenInsertIfNew}`containsThenInsertIfNew`，它仅在以前不存在的情况下插入新映射。
{name Std.HashMap.alter}`alter` 函数修改给定键的值，而无需多次搜索该键；交替是由一个函数执行的，其中缺失值由 {name}`none` 表示。

## 原始数据和不变量
%%%
tag := "raw-data"
%%%

基于哈希的映射和基于树的映射都依赖于某些内部格式良好的不变量，例如树是平衡和有序的。
在Lean的标准库中，这些数据结构被表示为一对底层数据，并带有其格式良好的证明。
这个事实主要是一个内部实现细节；然而，它与一种情况下的用户相关：这种表示形式阻止它们在 {tech (key := "nested inductive types")}[嵌套归纳类型] 中使用。

为了使其能够在嵌套归纳类型中使用，标准库提供了每个容器的“{deftech}[raw]”变体及其不变量的单独“非捆绑”版本。
它们使用以下命名约定：
 * `T.Raw` 是 `T` 类型的版本，没有其不变量。例如，{name}`Std.HashMap.Raw` 是 {name}`Std.HashMap` 的一个版本，没有嵌入校样。
 * `T.Raw.WF` 是相应的格式良好谓词。例如，{name}`Std.HashMap.Raw.WF` 断言 {name}`Std.HashMap.Raw` 格式良好。
 * `T` 上的每个操作（称为 `T.f`）在 `T.Raw` 上都有一个对应的操作（称为 `T.Raw.f`）。例如，{name}`Std.HashMap.Raw.insert` 是与原始哈希映射一起使用的 {name}`Std.HashMap.insert` 版本。
 * 每个操作 `T.Raw.f` 都有一个关联的格式良好引理 `T.Raw.WF.f`。例如，{name}`Std.HashMap.Raw.WF.insert` 断言将新的键值对插入到格式良好的原始哈希映射中会产生格式良好的原始哈希映射。

由于绝大多数用例不需要它们，因此并非所有有关原始类型的引理都默认随数据结构导入。
通常需要导入 `Std.Data.T.RawLemmas`（其中 `T` 是有问题的数据结构）。

发生在映射或集合内部的嵌套归纳类型应分三个阶段定义：

 1. 首先，定义使用原始版本的映射或集合类型的嵌套归纳类型的原始版本。定义任何必要的操作。
 2. 接下来，定义一个归纳谓词，断言原始嵌套类型中的所有映射或集合都格式良好。表明对原始类型的操作保持了格式良好。
 3. 通过定义 API 来构造嵌套归纳类型的适当接口，该 API 可根据需要证明格式良好的属性，并对用户隐藏它们。

:::example "Nested Inductive Types with `Std.HashMap`"

```imports -show
import Std
```

此示例要求导入 `Std.Data.HashMap.RawLemmas`。
为了使代码更短，打开 `Std` 命名空间：
```lean
open Std
```

冒险游戏的地图可能由一系列通过通道连接的房间组成。
每个房间都有一个描述，每条通道都面向特定的方向。
这可以表示为递归结构。

```lean +error (name:=badNesting) -keep
structure Maze where
  description : String
  passages : HashMap String Maze
```

这个定义被拒绝：

```leanOutput badNesting
(kernel) application type mismatch
  DHashMap.Raw.WF inner
argument has type
  _nested.Std.DHashMap.Raw_3
but function has type
  (DHashMap.Raw String fun x => Maze) → Prop
```

要实现这项工作，需要将格式良好的谓词与结构分开。
第一步是重新定义不嵌入哈希映射不变量的类型：

```lean
structure RawMaze where
  description : String
  passages : Std.HashMap.Raw String RawMaze
```

最基本的原始迷宫没有通道：
```lean
def RawMaze.base (description : String) : RawMaze where
  description := description
  passages := ∅
```

可以使用 {name}`RawMaze.insert` 将通向进一步迷宫的通道添加到原始迷宫中：
```lean
def RawMaze.insert (maze : RawMaze)
    (direction : String) (next : RawMaze) : RawMaze :=
  { maze with
    passages := maze.passages.insert direction next
  }
```

第二步是为 {name}`RawMaze` 定义一个格式良好的谓词，以确保每个包含的哈希映射都是格式良好的。
如果 {name RawMaze.passages}`passages` 字段本身是良构的，并且其中包含的所有原始迷宫都是良构的，则原始迷宫是良构的。

```lean
inductive RawMaze.WF : RawMaze → Prop
  | mk {description passages} :
    (∀ (dir : String) v, passages[dir]? = some v → WF v) →
    passages.WF →
    WF { description, passages := passages }
```

基础迷宫是结构良好的，将通向结构良好的迷宫的通道插入到其他结构良好的迷宫中会产生结构良好的迷宫：
```lean
theorem RawMaze.base_wf (description : String) :
    RawMaze.WF (.base description) := by
  constructor
  . intro v h h'
    simp [Std.HashMap.Raw.getElem?_empty] at *
  . exact HashMap.Raw.WF.empty

def RawMaze.insert_wf (maze : RawMaze) :
    WF maze → WF next → WF (maze.insert dir next) := by
  let ⟨desc, passages⟩ := maze
  intro ⟨wfMore, wfPassages⟩ wfNext
  constructor
  . intro dir' v
    rw [HashMap.Raw.getElem?_insert wfPassages]
    split <;> intros <;> simp_all [wfMore dir']
  . simp_all [HashMap.Raw.WF.insert]
```

最后，可以定义一个更友好的界面，使用户不必担心格式良好。
{name}`Maze` 将 {name}`RawMaze` 与其格式良好的证明捆绑在一起：
```lean
structure Maze where
  raw : RawMaze
  wf : raw.WF
```

{name Maze.base}`base` 和 {name Maze.insert}`insert` 运算符负责格式良好的证明义务：
```lean
def Maze.base (description : String) : Maze where
  raw := .base description
  wf := by apply RawMaze.base_wf

def Maze.insert (maze : Maze)
    (dir : String) (next : Maze) : Maze where
  raw := maze.raw.insert dir next.raw
  wf := RawMaze.insert_wf maze.raw maze.wf next.wf
```

{name}`Maze` API 的用户可以检查当前迷宫​​的描述或尝试前往新迷宫的方向：
```lean
def Maze.description (maze : Maze) : String :=
  maze.raw.description

def Maze.go? (maze : Maze) (dir : String) : Option Maze :=
  match h : maze.raw.passages[dir]? with
  | none => none
  | some m' =>
    Maze.mk m' <| by
      let ⟨r, wf⟩ := maze
      let ⟨wfAll, _⟩ := wf
      apply wfAll dir
      apply h
```
:::

## 适合唯一性的运算符
%%%
tag := "zh-basictypes-maps-h004"
%%%

使用数据结构时应小心，以确保尽可能多的引用是唯一的，这使得 Lean 能够在幕后使用破坏性突变，同时保持纯函数式接口。
地图和集合库提供可用于维护引用唯一性的运算符。
特别是，在可能的情况下，应优先选择诸如 {name Std.HashMap.alter}`alter` 或 {name Std.HashMap.modify}`modify` 之类的操作，而不是显式检索值、修改值并重新插入值。
这些操作避免在修改期间创建对该值的第二个引用。

:::example "Modifying Values in Maps"

```imports -show
import Std
```

```lean
open Std
```

函数 {name}`addAlias` 用于跟踪某些数据集中字符串的别名。
添加别名的一种方法是首先查找现有别名，默认为空数组，然后插入新别名，最后将结果数组保存在映射中：

```lean
def addAlias (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  aliases.insert key (prior.push value)
```

此实现的性能特征很差。
由于映射保留了对先前值的引用，因此必须复制而不是更改数组。
更好的实现在修改之前显式地从映射中删除先前的值：

```lean
def addAlias' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  let prior := aliases.getD key #[]
  let aliases := aliases.erase key
  aliases.insert key (prior.push value)
```

使用 {name}`HashMap.alter` 效果更好。
它消除了显式删除并重新插入值的需要：

```lean
def addAlias'' (aliases : HashMap String (Array String))
    (key value : String) :
    HashMap String (Array String) :=
  aliases.alter key fun prior? =>
    some ((prior?.getD #[]).push value)
```

:::



# 哈希映射
%%%
tag := "HashMap"
%%%

本节中的声明应使用 `import Std.HashMap` 导入。

{docstring Std.HashMap +hideFields +hideStructureConstructor}


## 创建
%%%
tag := "zh-basictypes-maps-h006"
%%%

{docstring Std.HashMap.emptyWithCapacity}

## 特性
%%%
tag := "zh-basictypes-maps-h007"
%%%

{docstring Std.HashMap.size}

{docstring Std.HashMap.isEmpty}

{docstring Std.HashMap.Equiv}

:::syntax term (title := "Equivalence") (namespace := Std.HashMap)

关系 {name Std.HashMap.Equiv}`HashMap.Equiv` 也可以使用中缀运算符编写，其范围仅限于其命名空间：

```grammar
$_ ~m $_
```

:::

## 查询
%%%
tag := "zh-basictypes-maps-h008"
%%%

{docstring Std.HashMap.contains}

{docstring Std.HashMap.get}

{docstring Std.HashMap.get!}

{docstring Std.HashMap.get?}

{docstring Std.HashMap.getD}

{docstring Std.HashMap.getKey}

{docstring Std.HashMap.getKey!}

{docstring Std.HashMap.getKey?}

{docstring Std.HashMap.getKeyD}

{docstring Std.HashMap.keys}

{docstring Std.HashMap.keysArray}

{docstring Std.HashMap.values}

{docstring Std.HashMap.valuesArray}

## 修改
%%%
tag := "zh-basictypes-maps-h009"
%%%

{docstring Std.HashMap.alter}

{docstring Std.HashMap.modify}

{docstring Std.HashMap.containsThenInsert}

{docstring Std.HashMap.containsThenInsertIfNew}

{docstring Std.HashMap.erase}

{docstring Std.HashMap.filter}

{docstring Std.HashMap.filterMap}

{docstring Std.HashMap.insert}

{docstring Std.HashMap.insertIfNew}

{docstring Std.HashMap.getThenInsertIfNew?}

{docstring Std.HashMap.insertMany}

{docstring Std.HashMap.insertManyIfNewUnit}

{docstring Std.HashMap.partition}

{docstring Std.HashMap.union}

## 迭代
%%%
tag := "zh-basictypes-maps-h010"
%%%

{docstring Std.HashMap.iter}

{docstring Std.HashMap.keysIter}

{docstring Std.HashMap.valuesIter}

{docstring Std.HashMap.map}

{docstring Std.HashMap.fold}

{docstring Std.HashMap.foldM}

{docstring Std.HashMap.forIn}

{docstring Std.HashMap.forM}

## 转换
%%%
tag := "zh-basictypes-maps-h011"
%%%

{docstring Std.HashMap.ofList}

{docstring Std.HashMap.toArray}

{docstring Std.HashMap.toList}

{docstring Std.HashMap.unitOfArray}

{docstring Std.HashMap.unitOfList}

## 非捆绑变体
%%%
tag := "zh-basictypes-maps-h012"
%%%

未捆绑的地图将格式良好的证明与数据分开。
这在定义 {ref "raw-data"}[嵌套归纳类型] 时主要有用。
要使用这些变体，请导入模块 `Std.HashMap.Raw` 和 `Std.HashMap.RawLemmas`。

{docstring Std.HashMap.Raw}

{docstring Std.HashMap.Raw.WF}

# 依赖哈希映射
%%%
tag := "DHashMap"
%%%

本节中的声明应使用 `import Std.DHashMap` 导入。

{docstring Std.DHashMap +hideFields +hideStructureConstructor}

## 创建
%%%
tag := "zh-basictypes-maps-h014"
%%%

{docstring Std.DHashMap.emptyWithCapacity}

## 特性
%%%
tag := "zh-basictypes-maps-h015"
%%%

{docstring Std.DHashMap.size}

{docstring Std.DHashMap.isEmpty}

{docstring Std.DHashMap.Equiv}

:::syntax term (title := "Equivalence") (namespace := Std.DHashMap)

关系 {name Std.DHashMap.Equiv}`DHashMap.Equiv` 也可以使用中缀运算符编写，其范围仅限于其命名空间：

```grammar
$_ ~m $_
```

:::

## 查询
%%%
tag := "zh-basictypes-maps-h016"
%%%

{docstring Std.DHashMap.contains}

{docstring Std.DHashMap.get}

{docstring Std.DHashMap.get!}

{docstring Std.DHashMap.get?}

{docstring Std.DHashMap.getD}

{docstring Std.DHashMap.getKey}

{docstring Std.DHashMap.getKey!}

{docstring Std.DHashMap.getKey?}

{docstring Std.DHashMap.getKeyD}

{docstring Std.DHashMap.keys}

{docstring Std.DHashMap.keysArray}

{docstring Std.DHashMap.values}


{docstring Std.DHashMap.valuesArray}

## 修改
%%%
tag := "zh-basictypes-maps-h017"
%%%

{docstring Std.DHashMap.alter}

{docstring Std.DHashMap.modify}

{docstring Std.DHashMap.containsThenInsert}

{docstring Std.DHashMap.containsThenInsertIfNew}

{docstring Std.DHashMap.erase}

{docstring Std.DHashMap.filter}

{docstring Std.DHashMap.filterMap}

{docstring Std.DHashMap.insert}

{docstring Std.DHashMap.insertIfNew}

{docstring Std.DHashMap.getThenInsertIfNew?}

{docstring Std.DHashMap.insertMany}

{docstring Std.DHashMap.partition}

{docstring Std.DHashMap.union}

## 迭代
%%%
tag := "zh-basictypes-maps-h018"
%%%

{docstring Std.DHashMap.iter}

{docstring Std.DHashMap.keysIter}

{docstring Std.DHashMap.valuesIter}

{docstring Std.DHashMap.map}

{docstring Std.DHashMap.fold}

{docstring Std.DHashMap.foldM}

{docstring Std.DHashMap.forIn}

{docstring Std.DHashMap.forM}

## 转换
%%%
tag := "zh-basictypes-maps-h019"
%%%

{docstring Std.DHashMap.ofList}

{docstring Std.DHashMap.toArray}

{docstring Std.DHashMap.toList}

## 非捆绑变体
%%%
tag := "zh-basictypes-maps-h020"
%%%

未捆绑的地图将格式良好的证明与数据分开。
这在定义 {ref "raw-data"}[嵌套归纳类型] 时主要有用。
要使用这些变体，请导入模块 `Std.DHashMap.Raw` 和 `Std.DHashMap.RawLemmas`。

{docstring Std.DHashMap.Raw}

{docstring Std.DHashMap.Raw.WF}

# 扩展哈希图
%%%
tag := "ExtHashMap"
%%%

本节中的声明应使用 `import Std.ExtHashMap` 导入。

{docstring Std.ExtHashMap +hideFields +hideStructureConstructor}

## 创建
%%%
tag := "zh-basictypes-maps-h022"
%%%

{docstring Std.ExtHashMap.emptyWithCapacity}

## 特性
%%%
tag := "zh-basictypes-maps-h023"
%%%

{docstring Std.ExtHashMap.size}

{docstring Std.ExtHashMap.isEmpty}

## 查询
%%%
tag := "zh-basictypes-maps-h024"
%%%

{docstring Std.ExtHashMap.contains}

{docstring Std.ExtHashMap.get}

{docstring Std.ExtHashMap.get!}

{docstring Std.ExtHashMap.get?}

{docstring Std.ExtHashMap.getD}

{docstring Std.ExtHashMap.getKey}

{docstring Std.ExtHashMap.getKey!}

{docstring Std.ExtHashMap.getKey?}

{docstring Std.ExtHashMap.getKeyD}

## 修改
%%%
tag := "zh-basictypes-maps-h025"
%%%

{docstring Std.ExtHashMap.alter}

{docstring Std.ExtHashMap.modify}

{docstring Std.ExtHashMap.containsThenInsert}

{docstring Std.ExtHashMap.containsThenInsertIfNew}

{docstring Std.ExtHashMap.erase}

{docstring Std.ExtHashMap.filter}

{docstring Std.ExtHashMap.filterMap}

{docstring Std.ExtHashMap.insert}

{docstring Std.ExtHashMap.insertIfNew}

{docstring Std.ExtHashMap.getThenInsertIfNew?}

{docstring Std.ExtHashMap.insertMany}

{docstring Std.ExtHashMap.insertManyIfNewUnit}

## 迭代
%%%
tag := "zh-basictypes-maps-h026"
%%%

{docstring Std.ExtHashMap.map}

## 转换
%%%
tag := "zh-basictypes-maps-h027"
%%%

{docstring Std.ExtHashMap.ofList}

{docstring Std.ExtHashMap.unitOfArray}

{docstring Std.ExtHashMap.unitOfList}

# 扩展依赖哈希图
%%%
tag := "ExtDHashMap"
%%%

本节中的声明应使用 `import Std.ExtDHashMap` 导入。

{docstring Std.ExtDHashMap +hideFields +hideStructureConstructor}

## 创建
%%%
tag := "zh-basictypes-maps-h029"
%%%

{docstring Std.ExtDHashMap.emptyWithCapacity}

## 特性
%%%
tag := "zh-basictypes-maps-h030"
%%%

{docstring Std.ExtDHashMap.size}

{docstring Std.ExtDHashMap.isEmpty}


## 查询
%%%
tag := "zh-basictypes-maps-h031"
%%%

{docstring Std.ExtDHashMap.contains}

{docstring Std.ExtDHashMap.get}

{docstring Std.ExtDHashMap.get!}

{docstring Std.ExtDHashMap.get?}

{docstring Std.ExtDHashMap.getD}

{docstring Std.ExtDHashMap.getKey}

{docstring Std.ExtDHashMap.getKey!}

{docstring Std.ExtDHashMap.getKey?}

{docstring Std.ExtDHashMap.getKeyD}

## 修改
%%%
tag := "zh-basictypes-maps-h032"
%%%

{docstring Std.ExtDHashMap.alter}

{docstring Std.ExtDHashMap.modify}

{docstring Std.ExtDHashMap.containsThenInsert}

{docstring Std.ExtDHashMap.containsThenInsertIfNew}

{docstring Std.ExtDHashMap.erase}

{docstring Std.ExtDHashMap.filter}

{docstring Std.ExtDHashMap.filterMap}

{docstring Std.ExtDHashMap.insert}

{docstring Std.ExtDHashMap.insertIfNew}

{docstring Std.ExtDHashMap.getThenInsertIfNew?}

{docstring Std.ExtDHashMap.insertMany}


## 迭代
%%%
tag := "zh-basictypes-maps-h033"
%%%

{docstring Std.ExtDHashMap.map}

## 转换
%%%
tag := "zh-basictypes-maps-h034"
%%%

{docstring Std.ExtDHashMap.ofList}


# 哈希集
%%%
tag := "HashSet"
%%%

{docstring Std.HashSet}

## 创建
%%%
tag := "zh-basictypes-maps-h036"
%%%

{docstring Std.HashSet.emptyWithCapacity}

## 特性
%%%
tag := "zh-basictypes-maps-h037"
%%%

{docstring Std.HashSet.isEmpty}

{docstring Std.HashSet.size}

{docstring Std.HashSet.Equiv}

:::syntax term (title := "Equivalence") (namespace := Std.HashMap)

关系 {name Std.HashSet.Equiv}`HashSet.Equiv` 也可以使用中缀运算符编写，其范围仅限于其命名空间：

```grammar
$_ ~m $_
```

:::


## 查询
%%%
tag := "zh-basictypes-maps-h038"
%%%


{docstring Std.HashSet.contains}

{docstring Std.HashSet.get}

{docstring Std.HashSet.get!}

{docstring Std.HashSet.get?}

{docstring Std.HashSet.getD}


## 修改
%%%
tag := "zh-basictypes-maps-h039"
%%%

{docstring Std.HashSet.insert}

{docstring Std.HashSet.insertMany}

{docstring Std.HashSet.erase}

{docstring Std.HashSet.filter}

{docstring Std.HashSet.containsThenInsert}

{docstring Std.HashSet.partition}

{docstring Std.HashSet.union}

## 迭代
%%%
tag := "zh-basictypes-maps-h040"
%%%

{docstring Std.HashSet.iter}

{docstring Std.HashSet.all}

{docstring Std.HashSet.any}

{docstring Std.HashSet.fold}

{docstring Std.HashSet.foldM}

{docstring Std.HashSet.forIn}

{docstring Std.HashSet.forM}

## 转换
%%%
tag := "zh-basictypes-maps-h041"
%%%

{docstring Std.HashSet.ofList}

{docstring Std.HashSet.toList}

{docstring Std.HashSet.ofArray}

{docstring Std.HashSet.toArray}

## 非捆绑变体
%%%
tag := "zh-basictypes-maps-h042"
%%%

未捆绑的地图将格式良好的证明与数据分开。
这在定义 {ref "raw-data"}[嵌套归纳类型] 时主要有用。
要使用这些变体，请导入模块 `Std.HashSet.Raw` 和 `Std.HashSet.RawLemmas`。

{docstring Std.HashSet.Raw}

{docstring Std.HashSet.Raw.WF}


# 扩展哈希集
%%%
tag := "ExtHashSet"
%%%

{docstring Std.ExtHashSet}

## 创建
%%%
tag := "zh-basictypes-maps-h044"
%%%

{docstring Std.ExtHashSet.emptyWithCapacity}

## 特性
%%%
tag := "zh-basictypes-maps-h045"
%%%

{docstring Std.ExtHashSet.isEmpty}

{docstring Std.ExtHashSet.size}


## 查询
%%%
tag := "zh-basictypes-maps-h046"
%%%

{docstring Std.ExtHashSet.contains}

{docstring Std.ExtHashSet.get}

{docstring Std.ExtHashSet.get!}

{docstring Std.ExtHashSet.get?}

{docstring Std.ExtHashSet.getD}


## 修改
%%%
tag := "zh-basictypes-maps-h047"
%%%

{docstring Std.ExtHashSet.insert}

{docstring Std.ExtHashSet.insertMany}

{docstring Std.ExtHashSet.erase}

{docstring Std.ExtHashSet.filter}

{docstring Std.ExtHashSet.containsThenInsert}

## 转换
%%%
tag := "zh-basictypes-maps-h048"
%%%

{docstring Std.ExtHashSet.ofList}

{docstring Std.ExtHashSet.ofArray}

{include 1 ManualZh.BasicTypes.Maps.TreeMap}


# 基于树的依赖图
%%%
tag := "DTreeMap"
%%%

本节中的声明应使用 `import Std.DTreeMap` 导入。

{docstring Std.DTreeMap +hideFields +hideStructureConstructor}

## 创建
%%%
tag := "zh-basictypes-maps-h050"
%%%

{docstring Std.DTreeMap.empty}

## 特性
%%%
tag := "zh-basictypes-maps-h051"
%%%

{docstring Std.DTreeMap.size}

{docstring Std.DTreeMap.isEmpty}

## 查询
%%%
tag := "zh-basictypes-maps-h052"
%%%

{docstring Std.DTreeMap.contains}

{docstring Std.DTreeMap.get}

{docstring Std.DTreeMap.get!}

{docstring Std.DTreeMap.get?}

{docstring Std.DTreeMap.getD}

{docstring Std.DTreeMap.getKey}

{docstring Std.DTreeMap.getKey!}

{docstring Std.DTreeMap.getKey?}

{docstring Std.DTreeMap.getKeyD}

{docstring Std.DTreeMap.keys}

{docstring Std.DTreeMap.keysArray}

{docstring Std.DTreeMap.values}

{docstring Std.DTreeMap.valuesArray}

## 修改
%%%
tag := "zh-basictypes-maps-h053"
%%%

{docstring Std.DTreeMap.alter}

{docstring Std.DTreeMap.modify}

{docstring Std.DTreeMap.containsThenInsert}

{docstring Std.DTreeMap.containsThenInsertIfNew}

{docstring Std.DTreeMap.erase}

{docstring Std.DTreeMap.filter}

{docstring Std.DTreeMap.filterMap}

{docstring Std.DTreeMap.insert}

{docstring Std.DTreeMap.insertIfNew}

{docstring Std.DTreeMap.getThenInsertIfNew?}

{docstring Std.DTreeMap.insertMany}

{docstring Std.DTreeMap.partition}

## 迭代
%%%
tag := "zh-basictypes-maps-h054"
%%%

{docstring Std.DTreeMap.iter}

{docstring Std.DTreeMap.keysIter}

{docstring Std.DTreeMap.valuesIter}

{docstring Std.DTreeMap.map}

{docstring Std.DTreeMap.foldl}

{docstring Std.DTreeMap.foldlM}

{docstring Std.DTreeMap.forIn}

{docstring Std.DTreeMap.forM}

## 转换
%%%
tag := "zh-basictypes-maps-h055"
%%%

{docstring Std.DTreeMap.ofList}

{docstring Std.DTreeMap.toArray}

{docstring Std.DTreeMap.toList}

## 非捆绑变体
%%%
tag := "zh-basictypes-maps-h056"
%%%

未捆绑的地图将格式良好的证明与数据分开。
这在定义 {ref "raw-data"}[嵌套归纳类型] 时主要有用。
要使用这些变体，请导入模块 `Std.DTreeMap.Raw`。

{docstring Std.DTreeMap.Raw}

{docstring Std.DTreeMap.Raw.WF}

{include 1 ManualZh.BasicTypes.Maps.TreeSet}
