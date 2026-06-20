/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "子储备" =>
%%%
tag := "subarray"
%%%

:::leanSection
```lean -show
variable {α : Type u}
```

{lean}`Subarray α` 类型是 {lean}`Std.Slice α` 的缩写。
这意味着，除了本节中的运算符之外，{tech (key := "generalized field notation")}[通用字段表示法]还可用于调用 {namespace}`Std.Slice` 命名空间中的函数，例如 {name}`Std.Slice.foldl`。
:::

{docstring Subarray}

{docstring Subarray.empty}

# 数组数据
%%%
tag := "zh-basictypes-array-subarray-h001"
%%%

{docstring Subarray.array}

{docstring Subarray.start}

{docstring Subarray.stop}

{docstring Subarray.start_le_stop}

{docstring Subarray.stop_le_array_size}

# 调整大小
%%%
tag := "zh-basictypes-array-subarray-h002"
%%%

{docstring Subarray.drop}

{docstring Subarray.take}

{docstring Subarray.popFront}

{docstring Subarray.split}

# 查找
%%%
tag := "zh-basictypes-array-subarray-h003"
%%%

{docstring Subarray.get}

{docstring Subarray.get!}

{docstring Subarray.getD}

# 迭代
%%%
tag := "zh-basictypes-array-subarray-h004"
%%%

{docstring Subarray.foldr}

{docstring Subarray.foldrM}

{docstring Subarray.forM}

{docstring Subarray.forRevM}

{docstring Subarray.forIn}

# 元素谓词
%%%
tag := "zh-basictypes-array-subarray-h005"
%%%

{docstring Subarray.findRev?}

{docstring Subarray.findRevM?}

{docstring Subarray.findSomeRevM?}

{docstring Subarray.all}

{docstring Subarray.allM}

{docstring Subarray.any}

{docstring Subarray.anyM}
