/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "API 参考" =>

除了此处描述的一般函数之外，还有一些函数通常定义为每个集合类型的命名空间中的 API 的一部分：
 * `mapM` 映射一元函数。
 * `forM` 映射一个单子函数，丢弃结果。
 * `filterM` 使用一元谓词进行过滤，返回满足它的值。


::::example "Monadic Collection Operations"
{name}`Array.filterM` 可用于编写依赖于副作用的过滤器。

:::ioExample
```ioLean
def values := #[1, 2, 3, 5, 8]
def main : IO Unit := do
  let filtered ← values.filterM fun v => do
    repeat
      IO.println s!"Keep {v}? [y/n]"
      let answer := (← (← IO.getStdin).getLine).trimAscii.copy
      if answer == "y" then return true
      if answer == "n" then return false
    return false
  IO.println "These values were kept:"
  for v in filtered do
    IO.println s!" * {v}"
```
```stdin
y
n
oops
y
n
y
```
```stdout
Keep 1? [y/n]
Keep 2? [y/n]
Keep 3? [y/n]
Keep 3? [y/n]
Keep 5? [y/n]
Keep 8? [y/n]
These values were kept:
 * 1
 * 3
 * 8
```
:::
::::

# 丢弃结果
%%%
tag := "zh-monads-api-h001"
%%%

当使用仅为其副作用返回值的操作时，{name}`discard` 函数特别有用。

{docstring discard}

# 控制流程
%%%
tag := "zh-monads-api-h002"
%%%

{docstring guard}

{docstring optional}

# 提升布尔运算
%%%
tag := "zh-monads-api-h003"
%%%

{docstring andM}

{docstring orM}

{docstring notM}

# 克莱斯利成分
%%%
tag := "zh-monads-api-h004"
%%%

{deftech}_Kleisli Composition_是一元函数的组合，类似于普通函数的{name}`Function.comp`。

{docstring Bind.kleisliRight}

{docstring Bind.kleisliLeft}

# 重新排序的操作
%%%
tag := "zh-monads-api-h005"
%%%

有时，将函数部分应用到其第二个参数可能会很方便。
这些函数颠倒了参数的顺序，使其变得更容易。

{docstring Functor.mapRev}

{docstring Bind.bindLeft}
