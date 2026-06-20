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

#doc (Manual) "控制台输出" =>
%%%
file := "Console-Output"
tag := "zh-io-console-root"
%%%

Lean 包括用于写入 {tech (key := "standard output")}[标准输出] 和 {tech (key := "standard error")}[标准错误] 的便捷函数。
全部都使用 {lean}`ToString` 实例，并且名称以 `-ln` 结尾的变体在输出后添加换行符。
这些便捷函数只公开了 {ref "stdio"}[使用标准 I/O 流] 时可用功能的一部分。
特别是，要从 标准输入 读取一行，请使用 {lean}`IO.getStdin` 和 {lean}`IO.FS.Stream.getLine` 的组合。

{docstring IO.print}

{docstring IO.println}

{docstring IO.eprint}

{docstring IO.eprintln}

::::example "Printing"
该程序演示了控制台 I/O 的所有四个便利功能。

:::ioExample
```ioLean
def main : IO Unit := do
  IO.print "This is the "
  IO.print "Lean"
  IO.println " language reference."
  IO.println "Thank you for reading it!"
  IO.eprint "Please report any "
  IO.eprint "errors"
  IO.eprintln " so they can be corrected."
```

它将以下内容输出到 标准输出：

```stdout
This is the Lean language reference.
Thank you for reading it!
```

以及 标准错误 的以下内容：

```stderr
Please report any errors so they can be corrected.
```
:::
::::
