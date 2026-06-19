/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.3.0 (2023-11-30)" =>
%%%
tag := "release-v4.3.0"
file := "v4.3.0"
%%%

```markdown
* `simp [f]`不再展开`f`的部分应用。请参阅问题 [#2042](https://github.com/leanprover/lean4/issues/2042)。
  要修复受此更改影响的校样，请使用 `unfold f` 或 `simp (config := { unfoldPartialApp := true }) [f]`。
* 默认情况下，`simp` 将不再尝试使用 Decidable 实例重写术语。特别是，并非所有可判定的目标都将由 `simp` 关闭，并且 `decide`策略在这种情况下可能有用。 `decide` simp 配置选项可用于本地恢复旧的 `simp` 行为，如 `simp (config := {decide := true})` 中所示；这包括使用 Decidable 实例来验证次要目标，例如数字不等式。

* 许多错误修复：
  * [将左/右操作添加到术语树强制精化器并使 `^`` 成为右操作](https://github.com/leanprover/lean4/pull/2778)
  * [修复 #2775，不捕获最大递归深度错误](https://github.com/leanprover/lean4/pull/2790)
  * [使用 `cases`策略时 `Decidable` 实例的减少速度非常慢](https://github.com/leanprover/lean4/issues/2552)
  * [`simp` 不在活页夹中重写](https://github.com/leanprover/lean4/issues/1926)
  * [`simp` 展开 `let`，即使带有 `zeta := false` 选件](https://github.com/leanprover/lean4/issues/2669)
  * [`simp`（禁用 beta/zeta）和判别树](https://github.com/leanprover/lean4/issues/2281)
  * [`rw ... at h` 引入的未知自由变量](https://github.com/leanprover/lean4/issues/2711)
  * [`dsimp` 不使用由未应用的常数组成的 `rfl` 定理](https://github.com/leanprover/lean4/issues/2685)
  * [如果自反平等目标包含在元数据中，`dsimp` 不会关闭它们](https://github.com/leanprover/lean4/issues/2514)
  * [`rw [h]` 使用环境中的 `h`，而不是本地上下文中的 `h`](https://github.com/leanprover/lean4/issues/2729)
  * [`assumption`策略缺少 `withAssignableSyntheticOpaque`](https://github.com/leanprover/lean4/issues/2361)
  * [忽略字段警告的默认值](https://github.com/leanprover/lean4/issues/2178)
* [取消语言服务器中文档编辑的未完成任务](https://github.com/leanprover/lean4/pull/2648)。
* [删除 `Fin.mod` 和 `Fin.div` 中不必要的 `%` 操作](https://github.com/leanprover/lean4/pull/2688)
* [避免 `Array.mem` 中的 `DecidableEq`](https://github.com/leanprover/lean4/pull/2774)
* [确保 `USize.size` 与 `?m + 1` 统一](https://github.com/leanprover/lean4/issues/1926)
* [提高与emacs eglot客户端的兼容性](https://github.com/leanprover/lean4/pull/2721)

**Lake:**

* [`lake new MyProject math` 的合理默认值](https://github.com/leanprover/lean4/pull/2770)
* 将 `postUpdate?` 配置选项更改为 `post_update` 声明。有关新语法的更多信息，请参阅 `post_update` 语法文档字符串。
* [如果工作区加载时不存在清单，则会自动创建清单。](https://github.com/leanprover/lean4/pull/2680)。
* 配置声明的 `:=` 语法（即 `package`、`lean_lib` 和 `lean_exe`）已被弃用。例如，`package foo := {...}` 已弃用。
* [支持通过 `LAKE_PKG_URL_MAP` 覆盖包 URL](https://github.com/leanprover/lean4/pull/2709)
* 将默认构建目录（例如，`build`）、默认包目录（例如，`lake-packages`）和已编译配置（例如，`lakefile.olean`）移动到 Lake 输出的新专用目录 `.lake` 中。云发布构建档案也存储在这里，修复了 [#2713](https://github.com/leanprover/lean4/issues/2713)。
* 将清单格式更新为版本 7（有关更改的详细信息，请参阅 [lean4#2801](https://github.com/leanprover/lean4/pull/2801)）。
* 弃用包配置的 `manifestFile` 字段。
* 现在对 `lakefile.olean` 兼容性进行了更严格的检查（有关更多详细信息，请参阅 [#2842](https://github.com/leanprover/lean4/pull/2842)）。

```
