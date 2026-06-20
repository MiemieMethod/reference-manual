/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


import Std.Data.TreeSet
import Std.Data.TreeSet.Raw

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "基于树的集合" =>
%%%
tag := "TreeSet"
%%%

{docstring Std.TreeSet +hideStructureConstructor +hideFields}

# 创建
%%%
tag := "zh-basictypes-maps-treeset-h001"
%%%

{docstring Std.TreeSet.empty}

# 特性
%%%
tag := "zh-basictypes-maps-treeset-h002"
%%%

{docstring Std.TreeSet.isEmpty}

{docstring Std.TreeSet.size}

# 查询
%%%
tag := "zh-basictypes-maps-treeset-h003"
%%%

{docstring Std.TreeSet.contains}

{docstring Std.TreeSet.get}

{docstring Std.TreeSet.get!}

{docstring Std.TreeSet.get?}

{docstring Std.TreeSet.getD}

## 基于排序的查询
%%%
tag := "zh-basictypes-maps-treeset-h004"
%%%

{docstring Std.TreeSet.atIdx}

{docstring Std.TreeSet.atIdx!}

{docstring Std.TreeSet.atIdx?}

{docstring Std.TreeSet.atIdxD}

{docstring Std.TreeSet.getGE}

{docstring Std.TreeSet.getGE!}

{docstring Std.TreeSet.getGE?}

{docstring Std.TreeSet.getGED}

{docstring Std.TreeSet.getGT}

{docstring Std.TreeSet.getGT!}

{docstring Std.TreeSet.getGT?}

{docstring Std.TreeSet.getGTD}

{docstring Std.TreeSet.getLE}

{docstring Std.TreeSet.getLE!}

{docstring Std.TreeSet.getLE?}

{docstring Std.TreeSet.getLED}

{docstring Std.TreeSet.getLT}

{docstring Std.TreeSet.getLT!}

{docstring Std.TreeSet.getLT?}

{docstring Std.TreeSet.getLTD}


{docstring Std.TreeSet.min}

{docstring Std.TreeSet.min!}

{docstring Std.TreeSet.min?}

{docstring Std.TreeSet.minD}

{docstring Std.TreeSet.max}

{docstring Std.TreeSet.max!}

{docstring Std.TreeSet.max?}

{docstring Std.TreeSet.maxD}

# 修改
%%%
tag := "zh-basictypes-maps-treeset-h005"
%%%


{docstring Std.TreeSet.insert}

{docstring Std.TreeSet.insertMany}

{docstring Std.TreeSet.containsThenInsert}

{docstring Std.TreeSet.erase}

{docstring Std.TreeSet.eraseMany}

{docstring Std.TreeSet.filter}

{docstring Std.TreeSet.merge}

{docstring Std.TreeSet.partition}


# 迭代
%%%
tag := "zh-basictypes-maps-treeset-h006"
%%%

{docstring Std.TreeSet.iter}

{docstring Std.TreeSet.all}

{docstring Std.TreeSet.any}

{docstring Std.TreeSet.foldl}

{docstring Std.TreeSet.foldlM}

{docstring Std.TreeSet.foldr}

{docstring Std.TreeSet.foldrM}

{docstring Std.TreeSet.forIn}

{docstring Std.TreeSet.forM}


# 转换
%%%
tag := "zh-basictypes-maps-treeset-h007"
%%%

{docstring Std.TreeSet.toList}

{docstring Std.TreeSet.ofList}

{docstring Std.TreeSet.toArray}

{docstring Std.TreeSet.ofArray}

## 非捆绑变体
%%%
tag := "zh-basictypes-maps-treeset-h008"
%%%

非捆绑集将格式良好的证明与数据分开。
这在定义 {ref "raw-data"}[嵌套归纳类型] 时主要有用。
要使用这些变体，请导入模块 `Std.TreeSet.Raw`。

{docstring Std.TreeSet.Raw}

{docstring Std.TreeSet.Raw.WF}
