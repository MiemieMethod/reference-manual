/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joscha Mennicken
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lean 4.28.1 (2026-04-14)" =>
%%%
tag := "release-v4.28.1"
file := "v4.28.1"
%%%

此版本有 2 处更改。
除了 0 个功能添加之外，
以及下面列出的 1 个修复，
有 0 处重构更改，
0 项文档改进，
0 性能改进，
对测试套件进行 0 项改进，
以及其他 1 项变更。

# 编译器

```markdown

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  修复了 `lean_io_prim_handle_read` 中的堆缓冲区溢出问题，该溢出问题是通过
  分配大小计算中的整数溢出。此外，它还放置了几个检查的
  对所有相关分配路径进行算术运算，以消除未来潜在的溢出
  相反，会导致崩溃。现在，有问题的代码会抛出内存不足错误。

```
