/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.2.0 (2023-10-31)" =>
%%%
tag := "release-v4.2.0"
file := "v4.2.0"
%%%

```markdown
* [isDefEq 缓存不包含元变量的术语。](https://github.com/leanprover/lean4/pull/2644)。
* 将 [`Environment.mk`](https://github.com/leanprover/lean4/pull/2604) 和 [`Environment.add`](https://github.com/leanprover/lean4/pull/2642) 设为私有，并添加 [`replay`](https://github.com/leanprover/lean4/pull/2617) 作为更安全的替代方案。
* `IO.Process.output` 不再继承调用者的 标准输入。
* [不禁止缓存](https://github.com/leanprover/lean4/pull/2612) 默认级别 `match` 减少。
* [列出有效的 case 标签](https://github.com/leanprover/lean4/pull/2629) 当用户写入无效的 case 标签时。
* `DecidableEq` 的派生处理程序 [现在处理](https://github.com/leanprover/lean4/pull/2591) 相互归纳类型。
* [在 Lake 中显示导入失败的路径](https://github.com/leanprover/lean4/pull/2616)。
* [修复 macOS 上的链接器警告](https://github.com/leanprover/lean4/pull/2598)。
* **Lake：** 添加 `postUpdate?` 软件包配置选项。由包用来指定一些应在包或其下游依赖项之一成功执行 `lake update` 后运行的代码。 ([湖#185](https://github.com/leanprover/lake/issues/185))
* Lake 启动时间的改进（[#2572](https://github.com/leanprover/lean4/pull/2572)、[#2573](https://github.com/leanprover/lean4/pull/2573)）
* `refine e` 现在用在 `e` 的精化期间创建的元变量替换主要目标，并且不再捕获 `e` 中出现的预先存在的元变量 ([#2502](https://github.com/leanprover/lean4/pull/2502))。
  * 这是通过更改 `withCollectingNewGoalsFrom` 来实现的，这也会影响 `elabTermWithHoles`、`refine'`、`calc` (策略) 和 `specialize`。同样，所有这些现在仅在其输出中包含新创建的元变量。
  * 以前，`e` 中新创建的元变量和预先存在的元变量在不同的边缘情况下返回不一致，导致信息视图中出现重复目标（问题 [#2495](https://github.com/leanprover/lean4/issues/2495)）、错误关闭目标（问题 [#2434](https://github.com/leanprover/lean4/issues/2434)）以及由于以下原因导致的不直观行为`refine e` 捕获先前创建的目标意外出现在 `e` 中（没问题；请参阅 PR）。

```
