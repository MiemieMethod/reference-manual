/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command

import Manual.Meta
import ManualZh.BuildTools.Lake
import ManualZh.BuildTools.Elan

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "构建工具和分发" =>
%%%
tag := "build-tools-and-distribution"
shortContextTitle := "Build Tools"
%%%

:::paragraph
Lean {deftech}_toolchain_ 是命令行工具的集合，用于检查 Lean 文件集合中的校样和编译程序。
工具链由 `elan` 管理，它根据需要安装工具链。
Lean 工具链被设计为独立的，大多数命令行用户永远不需要显式调用 `lake` 和 `elan` 以外的任何工具链。
它们包含以下工具：

: `lean`

  Lean编译器，用于细化和编译Lean源文件。

: `lake`

  Lean 构建工具，用于在跟踪依赖项的同时增量调用 `lean` 和其他工具。

: `leanc`

  Lean 附带的 C 编译器是 [Clang](https://clang.llvm.org/) 的一个版本。

: `leanmake`

  `make` 构建工具的实现，用于编译 C 依赖项。

: `leanchecker`

  该工具可通过 Lean内核重播 {tech (key := ".olean files")}[`.olean` 文件] 中的精化结果，从而进一步确保所有条款均已正确检查。
:::

除了这些构建工具之外，工具链还包含构建 Lean 代码所需的文件。
这包括源代码、{tech (key := ".olean files")}[`.olean` 文件]、编译的库、C 头文件和编译的 Lean 运行时系统。
它们还包括 Lean 附带的策略使用的外部校样自动化工具，例如用于 {tactic}`bv_decide` 的 `cadical`。


{include 0 ManualZh.BuildTools.Lake}

{include 0 ManualZh.BuildTools.Elan}

# Reservoir
%%%
tag := "reservoir"
draft := true
%%%


::: planned 76
 * 概念
 * 包和工具链版本
 * 标签和构建
:::
