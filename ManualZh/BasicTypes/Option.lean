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

#doc (Manual) "任选值" =>
%%%
tag := "option"
%%%

:::::leanSection

```lean -show
variable {α : Type u} (v : α) {β : Type v}
```

{lean}`Option α` 是值的类型，对于某些 {lean}`v`﻿` : `﻿{lean}`α` 为 {lean}`some v`，或 {lean  (type := "Option α")}`none`。
在函数式编程中，此类型的使用方式与可空类型类似：{lean  (type := "Option α")}`none` 表示不存在值。
此外，从 {lean}`α` 到 {lean}`β` 的部分函数可以由类型 {lean}`α → Option β` 表示，其中当函数对于某些输入未定义时，结果为 {lean  (type := "Option β")}`none`。
从计算角度来看，这些部分函数代表了失败或错误的可能性，它们对应于可以提前终止但不会抛出信息性异常的程序。

{lean}`Option` 也可以被认为类似于最多包含一个元素的列表。
从这个角度来看，迭代 {lean}`Option` 包括仅当值存在时才执行操作。
{lean}`Option` API 经常使用这个视角。

::::leanSection

:::example "Options as Nullability"

```imports -show
import Std
```

```lean -show
open Std (HashMap)
variable {Coll} [BEq α] [Hashable α] (a : α) (b : β) {xs : Coll} [GetElem Coll α β fun _ _ => True] {i : α} {m : HashMap α β}
```

函数 {name}`Std.HashMap.get?` 在 {lean}`HashMap α β` 内查找指定的键 `a : α`：

```signature
Std.HashMap.get?.{u, v} {α : Type u} {β : Type v}
  [BEq α] [Hashable α]
  (m : HashMap α β) (a : α) :
  Option β
```
由于无法提前知道该键是否确实在映射中，因此返回类型为 {lean}`Option β`，其中 {lean  (type := "Option β")}`none` 表示该键不在映射中，{lean}`some b` 表示找到该键，`b` 是检索到的值。

{lean}`xs[i]` 语法用于在有可用证据证明 {lean}`i` 是 {lean}`xs` 中的有效索引时对集合进行索引，它有一个变体 {lean}`xs[i]?`，它根据给定索引是否有效返回一个可选值。
如果 {lean}`m`﻿` : `﻿{lean}`HashMap α β` 和 {lean}`a`﻿` : `﻿{lean}`α`，则 {lean}`m[a]?` 相当于 {lean}`HashMap.get? m a`。

:::
::::

:::example "Options as Safe Nullability"
在许多编程语言中，记住检查空值非常重要。
使用 {name}`Option` 时，类型系统要求在正确的位置进行这些检查：{lean}`Option α` 和 {lean}`α` 不是同一类型，从一种类型转换为另一种类型需要处理 {lean  (type := "Option α")}`none` 的情况。
这可以通过 {name}`Option.getD` 等帮助程序或模式匹配来完成。

```imports -show
import Std
```

```lean
def postalCodes : Std.HashMap Nat String :=
  Std.HashMap.emptyWithCapacity 1 |>.insert 12345 "Schenectady"
```

```lean (name := getD)
#eval postalCodes[12346]?.getD "not found"
```
```leanOutput getD
"not found"
```

```lean (name := m)
#eval
  match postalCodes[12346]? with
  | none => "not found"
  | some city => city
```
```leanOutput m
"not found"
```

```lean (name := iflet)
#eval
  if let some city := postalCodes[12345]? then
    city
  else
    "not found"
```
```leanOutput iflet
"Schenectady"
```

:::

:::::

{docstring Option}


# 强制
%%%
tag := "zh-basictypes-option-h001"
%%%

```lean -show
section
variable {α : Type u} (line : String)
```

有一个从 {lean}`α` 到 {lean}`Option α` 的 {tech}[强制] 将值包装在 {lean}`some` 中。
这允许 {name}`Option` 的使用方式与其他语言中的可空类型类似，其中缺少的值由 {name}`none` 指示，而存在的值没有特别标记。

:::example "Coercions and {name}`Option`"
在{lean}`getAlpha`中，读取一行输入。
如果该行仅由字母组成（从其开头和结尾删除空格后），则返回该行；否则，函数返回 {name}`none`。

```lean
def getAlpha : IO (Option String) := do
  let line := (← (← IO.getStdin).getLine).trim
  if line.length > 0 && line.all Char.isAlpha then
    return line
  else
    return none
```

在成功的情况下，{lean}`line` 周围没有显式的 {name}`some`。
{name}`some` 通过强制自动插入。

:::

```lean -show
end
```


# API 参考
%%%
tag := "zh-basictypes-option-h002"
%%%

## 提取值
%%%
tag := "zh-basictypes-option-h003"
%%%

{docstring Option.get}

{docstring Option.get!}

{docstring Option.getD}

{docstring Option.getDM}

{docstring Option.getM}

{docstring Option.elim}

{docstring Option.elimM}

{docstring Option.merge}


## 特性和比较
%%%
tag := "zh-basictypes-option-h004"
%%%

{docstring Option.isNone}

{docstring Option.isSome}

{docstring Option.isEqSome}

:::leanSection
```lean -show
variable {α} [DecidableEq α] [LT α] [Min α] [Max α]
```
可选值的排序通常使用 {inst}`DecidableEq (Option α)`、{inst}`LT (Option α)`、{inst}`Min (Option α)` 和 {inst}`Max (Option α)` 实例。
:::

{docstring Option.min}

{docstring Option.max}

{docstring Option.lt}

{docstring Option.decidableEqNone}

## 转换
%%%
tag := "zh-basictypes-option-h005"
%%%

{docstring Option.toArray}

{docstring Option.toList}

{docstring Option.repr}

{docstring Option.format}

## 控制
%%%
tag := "zh-basictypes-option-h006"
%%%

{name}`Option` 可以被认为是描述可能无法返回值的计算。
{inst}`Monad Option` 实例以及 {inst}`Alternative Option` 均基于这种理解。
返回 {name}`none` 也可以被认为是抛出一个不包含任何有趣信息的异常，该异常在 {inst}`MonadExcept Unit Option` 实例中捕获。

{docstring Option.guard}

{docstring Option.bind}

{docstring Option.bindM}

{docstring Option.join}

{docstring Option.sequence}

{docstring Option.tryCatch}

{docstring Option.or}

{docstring Option.orElse}


## 迭代
%%%
tag := "zh-basictypes-option-h007"
%%%

{name}`Option` 可以被认为是最多包含一个值的集合。
从这个角度来看，迭代运算符可以理解为对包含的值（如果存在）执行某些操作，或者如果不存在则不执行任何操作。

{docstring Option.all}

{docstring Option.any}

{docstring Option.filter}

{docstring Option.filterM}

{docstring Option.forM}

{docstring Option.map}

{docstring Option.mapA}

{docstring Option.mapM}

## 递归助手
%%%
tag := "zh-basictypes-option-h008"
%%%

{docstring Option.attach}

{docstring Option.attachWith}

{docstring Option.unattach}

## 推理
%%%
tag := "zh-basictypes-option-h009"
%%%

{docstring Option.choice}

{docstring Option.pbind}

{docstring Option.pelim}

{docstring Option.pmap}
