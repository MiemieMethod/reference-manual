/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.1.0 (2023-09-26)" =>
%%%
tag := "release-v4.1.0"
file := "v4.1.0"
%%%

```markdown
* 缺失令牌的错误定位已得到[改进](https://github.com/leanprover/lean4/pull/2393)。特别是，这应该可以更容易地发现不完整的策略证明中的错误。

* 制定配置文件后，Lake 现在会将配置缓存到 `lakefile.olean`。 Lake 的后续运行将导入此 OLean，而不是详细说明配置文件。这提供了显着的性能改进（基准测试表明使用 OLean 将 Lake 的启动时间减少一半），但有一些重要的细节需要记住：
  + 每次修改 `lakefile.lean` 或 `lean-toolchain` 后，Lake 将重新生成此 OLean。您还可以通过将新的 `--reconfigure` / `-R` 选项传递给 `lake` 来强制重新配置。
  + Lake 配置选项（即 `-K`）将在精化时修复。当 `lake` 使用缓存配置时设置这些选项将不起作用。要更改选项，请使用 `-R` / `--reconfigure` 运行 `lake`。
  + ** `lakefile.olean` 是本地配置，不应提交到 Git。因此，现有的 Lake 软件包需要将其添加到其 `.gitignore` 中。**

* `Lake.buildO` 的签名已更改，`args` 已拆分为 `weakArgs` 和 `traceArgs`。 `traceArgs` 包含在输入迹线中，而 `weakArgs` 则不包含在输入迹线中。请参阅 Lake 的 [FFI 示例](https://github.com/leanprover/lean4/blob/releases/v4.1.0/src/lake/examples/ffi/lib/lakefile.lean) 了解如何适应此更改的演示。

* `Lean.importModules`、`Lean.Elab.headerToImports` 和 `Lean.Elab.parseImports` 的签名

* 现在有 [`occs` 字段](https://github.com/leanprover/lean4/pull/2470)
  在 `rewrite`策略的配置对象中，
  允许控制模式的哪些出现应该被重写。
  这以前是 `Lean.MVarId.rewrite` 的单独参数，
  该字段已被删除，取而代之的是 `Rewrite.Config` 的附加字段。
  以前用户策略无法访问它。

```
