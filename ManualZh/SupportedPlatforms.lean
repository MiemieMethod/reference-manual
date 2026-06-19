/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

open Verso.Genre Manual

#doc (Manual) "支持的平台" =>
%%%
tag := "platforms"
file := "platforms"
number := false
htmlSplit := .never
%%%



# 1 级

:::paragraph
第 1 层平台是由我们的 CI 基础设施构建和测试 Lean 的平台。
Lean 的二进制版本可通过 {ref "elan"}[`elan`] 适用于这些平台。
一级平台是：

* `x86-64` Linux 与 glibc 2.26+
* `aarch64` Linux 与 glibc 2.27+
* `aarch64`（苹果芯片）macOS 10.15+
* `x86-64` Windows 11（任何版本）、Windows 10（版本 1903 或更高版本）、Windows Server 2022、Windows Server 2025
:::

# 2 级

第 2 层平台是 Lean 交叉编译但未经我们的 CI 测试的平台。
这些平台可以使用二进制版本。

由于缺乏自动化测试，版本可能会悄然被破坏。
欢迎问题报告和修复。

:::paragraph
2 级平台是：
* `x86-64` macOS 10.15+
* Emscripten WebAssembly
:::
