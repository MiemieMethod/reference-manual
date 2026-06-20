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
open Lean.MessageSeverity

#doc (Manual) "Lean 4.31.0 (2026-06-13)" =>
%%%
tag := "release-v4.31.0"
file := "v4.31.0"
%%%

在此版本中，发生了 305 项更改。
除了新增的 105 项功能外，
以及下面列出的 102 个修复，
有 17 处重构更改，
5 项文档改进，
13 项性能改进，
对测试套件进行 15 项改进，
以及 48 个其他变化。

# 亮点
%%%
file := "Highlights"
tag := "zh-releases-v4-31-0-h001"
%%%

Lean 4.31.0 是一个整合性很强的版本：除了一些面向用户的新功能（`do` 阻止精化、Lake 内置 linting 和更丰富的编辑器悬停）之外，它还付出了巨大的协调努力，使定义等价性检查正确尊重透明度级别，更快地重新实现`mvcgen'`，包括 HTTP 在内的库的重大开发，以及包括 LLVM 22 升级在内的广泛性能工作。

_此亮点部分由 Juanjo Madrigal 贡献。_

## `do` 表示法：新循环形式和新精化器
%%%
file := "___do___-Notation___-New-Loop-Forms-and-New-Elaborator"
tag := "zh-releases-v4-31-0-h002"
%%%

`do` 块中的 `while` 条件现在接受 `if` ([#13534](https://github.com/leanprover/lean4/pull/13534)) 已允许的任何条件形式。除了 `while c do …` 和 `while h : c do …` 之外，您现在还可以匹配模式，与 `:=` 或 `←` 绑定：

```
while let some x := stack.pop? do
  process x

while let .ok line ← readLine? do
  handle line
```

`repeat`/`while` 循环也变得*可验证* ([#13209](https://github.com/leanprover/lean4/pull/13209))。 `whileM` 是 `Lean.Loop.forIn` 的对应项，它承认一步展开引理 `whileM_eq`。现有的 `repeat`/`while` 循环现在可通过 `whileM` 进行扩展，而无需更改源，并且随附的 `@[spec]` 定理允许 `mvcgen`/`mvcgen'` 在给定终止措施和不变量的情况下释放循环体。另请参见 [#13689](https://github.com/leanprover/lean4/pull/13689) / [#13442](https://github.com/leanprover/lean4/pull/13442) / [#13447](https://github.com/leanprover/lean4/pull/13447)。

与此同时，新的 `do`精化器（可通过 `set_option backward.do.legacy false` 访问）也正在开发中：除了可扩展性之外，它已经产生了更精确、更可操作的诊断：

```lean (name := newDo)
set_option backward.do.legacy false in
example : IO Nat := do
  return 5
  IO.println "never runs"
```
```leanOutput newDo (severity := warning)
This `do` element and its control-flow region are dead code. Consider removing it.
```

相反，传统的精化器会拒绝相同的程序，并产生更粗略的、纯粹的结构错误：

```lean +error (name := oldDo)
example : IO Nat := do
  return 5
  IO.println "never runs"
```
```leanOutput oldDo (severity := error)
must be last element in a `do` sequence
```

相关开发在 [#13404](https://github.com/leanprover/lean4/pull/13404) / [#13542](https://github.com/leanprover/lean4/pull/13542) / [#13491](https://github.com/leanprover/lean4/pull/13491) / [#13494](https://github.com/leanprover/lean4/pull/13494) / [#13502](https://github.com/leanprover/lean4/pull/13502) / [#13506](https://github.com/leanprover/lean4/pull/13506) / [#13486](https://github.com/leanprover/lean4/pull/13486) / [#13397](https://github.com/leanprover/lean4/pull/13397) / [#13396](https://github.com/leanprover/lean4/pull/13396) / [#13399](https://github.com/leanprover/lean4/pull/13399) / [#13413](https://github.com/leanprover/lean4/pull/13413) / [#13434](https://github.com/leanprover/lean4/pull/13434) / [#13437](https://github.com/leanprover/lean4/pull/13437) / [#13507](https://github.com/leanprover/lean4/pull/13507) / [#13255](https://github.com/leanprover/lean4/pull/13255) / [#13250](https://github.com/leanprover/lean4/pull/13250)。

## Monadic 程序验证：`mvcgen'`
%%%
file := "Monadic-Program-Verification___-___mvcgen______"
tag := "zh-releases-v4-31-0-h003"
%%%

单元验证框架的工作仍在继续。 [#12965](https://github.com/leanprover/lean4/pull/12965) 引入了用于推理一元 Lean 代码的新基础，将一元 Hoare 三元组的前置/后置条件的断言语言从 `SPred` 推广到任何 `CompleteLattice`，分离终止路径和突然路径的后置条件，并解决了多个全域多态性问题。

在此基础上，[#13644](https://github.com/leanprover/lean4/pull/13644) 添加了实验性 `mvcgen'`策略，这是在新的基于 `SymM` 的符号评估框架上从头开始重新实现 `mvcgen`。在某些综合基准测试中，它的性能比 {tactic}`mvcgen` 高出 100 倍以上，并且希望实现功能完整。 `mvcgen'` 还可以用作交互式 `sym => …` 块内的步骤，其中剩余验证条件成为后续 `grind` 步骤的子目标 ([#13680](https://github.com/leanprover/lean4/pull/13680))。

## 透明度和 Defeq 纪律
%%%
file := "Transparency-and-Defeq-Discipline"
tag := "zh-releases-v4-31-0-h004"
%%%

此版本的一个跨领域主题是使定义等价检查正确尊重*透明度*：在确定两个术语是否“定义等价”时，Lean 如何积极地展开定义。普通的 `def` 在 `.default` 透明度下对其主体进行 defeq，但 `simp`/`dsimp` 在较低的 `.reducible` 级别上运行，在此级别它不会展开：

```lean +error
def x : Nat := 5

-- `rfl` checks defeq at `.default` transparency, so it closes the goal:
example : x = 5 := rfl

-- but `with_reducible` (where `simp`/`dsimp` run) won't unfold it:
example : x = 5 := by with_reducible refl

-- and `simp`/`dsimp` does not work either:
example : x = 5 := by simp
```

以前，这种透明度不匹配的情况很常见，而且很难诊断。通常的解决方法是通过将常量标记为 `@[reducible]` 来让常量在较低透明度下展开：

```lean (name := defeqFix)
@[reducible] def y : Nat := 5
example : y = 5 := by with_reducible rfl
example : y = 5 := by simp
```

*迁移：*如果证明在更严格的制度下被破坏，最常见的修复是将 `set_option backward.defeqAttrib.useBackward true in` 的范围覆盖到受影响的声明，将 `simpa using` 切换到 `simpa using!`，标记相关常量 `@[implicit_reducible]`，或者将现在所需的投影显式添加到 `simp`/`dsimp` 调用中。上述诊断（以及 `set_option diagnostics true` 和 `set_option trace.diagnostics true`）有助于找到受影响的点。

相关开发： [#13492](https://github.com/leanprover/lean4/pull/13492) / [#13363](https://github.com/leanprover/lean4/pull/13363) / [#13281](https://github.com/leanprover/lean4/pull/13281) / [#13512](https://github.com/leanprover/lean4/pull/13512) / [#13636](https://github.com/leanprover/lean4/pull/13636) / [#13833](https://github.com/leanprover/lean4/pull/13833) / [#13317](https://github.com/leanprover/lean4/pull/13317) / [#13368](https://github.com/leanprover/lean4/pull/13368) / [#13793](https://github.com/leanprover/lean4/pull/13793) / [#13280](https://github.com/leanprover/lean4/pull/13280) / [#13768](https://github.com/leanprover/lean4/pull/13768) / [#13772](https://github.com/leanprover/lean4/pull/13772)。

## 弃用模块、语法和选项
%%%
file := "Deprecating-Modules___-Syntax___-and-Options"
tag := "zh-releases-v4-31-0-h005"
%%%

此版本为库作者添加了一系列工具来管理弃用：

- [#13002](https://github.com/leanprover/lean4/pull/13002) 添加 `deprecated_module` 命令，将当前模块标记为已弃用；进口商收到建议更换的警告。 `#show_deprecated_modules` 命令列出环境中已弃用的模块。

  ```
  deprecated_module "use NewModule instead" (since := "2026-03-30")
  ```

- [#13108](https://github.com/leanprover/lean4/pull/13108) 添加了一个 `deprecated_syntax` 命令，该命令将语法类型标记为已弃用，并在详细说明已弃用的语法时（包括通过宏展开）发出 linter 警告。
- [#13195](https://github.com/leanprover/lean4/pull/13195) 允许将选项标记为已弃用，并对 `set_option` 使用发出警告（由 `linter.deprecated.options` 控制）。

一组相关的新 linter 警告冗余修饰符：`linter.redundantVisibility` 表示与默认值匹配的 `private`/`public` ([#13132](https://github.com/leanprover/lean4/pull/13132))，`linter.redundantExpose` 表示无操作 `@[expose]`/`@[no_expose]` （[#13359](https://github.com/leanprover/lean4/pull/13359)），以及带有变量或无法识别的头符号的 `@[simp]` 定理的警告（[#13325](https://github.com/leanprover/lean4/pull/13325)）。

## Lake：内置 Linting
%%%
file := "Lake___-Built-in-Linting"
tag := "zh-releases-v4-31-0-h006"
%%%

Lake 获得内置的 linting 框架，可通过 `lake lint` 标志访问（[#13393](https://github.com/leanprover/lean4/pull/13393)、[#13431](https://github.com/leanprover/lean4/pull/13431)）。它附带了来自 Batteries/Mathlib (`defLemma`/`defProp`、`checkUnivs`) 上游的环境 linter — 另请参阅 [#13356](https://github.com/leanprover/lean4/pull/13356) 中的核心上游 — 以及 `builtinLint` 包配置选项。标志包括 `--builtin-lint`、`--builtin-only`、`--clippy`、`--lint-all` 和 `--lint-only <name>`，并且 `@[builtin_nolint]` 属性抑制每个声明的特定 linters。

[#13513](https://github.com/leanprover/lean4/pull/13513) 通过将警告保留到每个模块的 `.olean` 中，将其扩展到 *text* linter，并且 [#13843](https://github.com/leanprover/lean4/pull/13843) 使模块系统目标 lint 其公共表面，与下游消费者所看到的相匹配。

## 表现
%%%
file := "Performance"
tag := "zh-releases-v4-31-0-h007"
%%%

此版本包括广泛的性能工作：

- [#13545](https://github.com/leanprover/lean4/pull/13545) 将捆绑编译器工具链从 LLVM 19 升级到 LLVM 22，根据基准测试，指令总体改进高达 5%。
- [#13788](https://github.com/leanprover/lean4/pull/13788) 为已知形状的值生成专门的 `dec` 代码，[#13669](https://github.com/leanprover/lean4/pull/13669) 优化 `lean_dec_ref_cold` 冷路径。
- [#13796](https://github.com/leanprover/lean4/pull/13796) 将 `String.compare` 简化为单个 `memcmp`，并且 [#13235](https://github.com/leanprover/lean4/pull/13235) 使用 `memcmp` 来实现 {name}`ByteArray` 相等。
- [#13651](https://github.com/leanprover/lean4/pull/13651) 将策略配置精化系统替换为直接构造配置对象并可以完全跳过术语精化的系统；配置评估现在花费的时间大约是以前的 6.2%。新系统还支持 {tactic}`simp`（例如 `(user.optionName := …)`）的自定义配置语法和用户配置选项。
- 精化本身对于具有多个字段的结构实例表示法 ([#13760](https://github.com/leanprover/lean4/pull/13760)) 和常见情况下的 `Expr.instantiateBetaRevRange` ([#13758](https://github.com/leanprover/lean4/pull/13758)) 更快。

## 图书馆亮点
%%%
file := "Library-Highlights"
tag := "zh-releases-v4-31-0-h008"
%%%

上一个版本引入的标准 HTTP 库成长为工作服务器：[#12146](https://github.com/leanprover/lean4/pull/12146) 添加了 `H1` 纯 HTTP/1.1 状态机，[#12151](https://github.com/leanprover/lean4/pull/12151) 添加了异步 HTTP/1.1 `Server`。重要的是，[#13511](https://github.com/leanprover/lean4/pull/13511) 将 `Async` 和 `Http` 模块从 `Internal` 升级到 `Std`。

其他值得注意的库添加：

- 日期/时间获得本地时间点的 `WallTime` 类型和简化的 `Timestamp` API ([#13675](https://github.com/leanprover/lean4/pull/13675))，以及用于可配置格式的 `Locale`/`LocaleSymbols` （[#13567](https://github.com/leanprover/lean4/pull/13567)）。
- `List.prod`/`Array.prod`/`Vector.prod` 镜像现有的 `sum` API，具有简化和研磨引理 ([#13200](https://github.com/leanprover/lean4/pull/13200))。
- 更多 {name}`ByteArray` `push`/`set!` 引理 ([#13457](https://github.com/leanprover/lean4/pull/13457)) 和 `Vector` 附加引理推广到不同大小的向量 ([#13693](https://github.com/leanprover/lean4/pull/13693))。
- `String.dropWhile`/`String.takeWhile` 的验证继续字符串验证工作 ([#13155](https://github.com/leanprover/lean4/pull/13155))。

许多运行时稳健性修复还将以前无声的内存耗尽故障转变为正确的错误或恐慌，而不是段错误和损坏（[#13392](https://github.com/leanprover/lean4/pull/13392)、[#13546](https://github.com/leanprover/lean4/pull/13546)、[#13547](https://github.com/leanprover/lean4/pull/13547)、 [#13548](https://github.com/leanprover/lean4/pull/13548)、[#13549](https://github.com/leanprover/lean4/pull/13549)、[#13521](https://github.com/leanprover/lean4/pull/13521))。对于安全敏感的部署，[#13401](https://github.com/leanprover/lean4/pull/13401) 添加了 `LEAN_MI_SECURE` 构建选项，可实现额外的 mimalloc 内存安全缓解。

## 编辑器和用户体验改进
%%%
file := "Editor-and-UX-Improvements"
tag := "zh-releases-v4-31-0-h009"
%%%

[#13260](https://github.com/leanprover/lean4/pull/13260) 添加了对*增量诊断*的服务器端支持。以前，在处理文件时报告诊断需要每次重新发送全套数据，这是文件处理过程中工作量的二次方。宣传 `incrementalDiagnosticSupport` 的客户端现在会收到 `PublishDiagnosticsParams.isIncremental` 标志，告诉他们追加而不是替换，从而消除了二次报告。 VS Code 扩展的客户端实现可在 [vscode-lean4#752](https://github.com/leanprover/vscode-lean4/pull/752) 中跟踪。

元变量 ([#13446](https://github.com/leanprover/lean4/pull/13446)) 和悬停 ([#13728](https://github.com/leanprover/lean4/pull/13728) / [#13399](https://github.com/leanprover/lean4/pull/13399) / [#13678](https://github.com/leanprover/lean4/pull/13678) / [#13715](https://github.com/leanprover/lean4/pull/13715))。

## 重大变化
%%%
file := "Breaking-Changes"
tag := "zh-releases-v4-31-0-h010"
%%%

除了上述与透明度相关的更改外，请注意以下事项：

- [#13807](https://github.com/leanprover/lean4/pull/13807) 使应用程序精化器beta-reduce 参数，同时将它们替换为以后的预期类型，与 `inferType` 和 `instantiateMVars` 一致。 *重大更改：*某些策略证明可能需要删除不必要的步骤，例如`dsimp only` 之前存在的步骤仅用于执行这些 beta 减少。相关地，[#13528](https://github.com/leanprover/lean4/pull/13528) 更改元变量簿记，以便元程序不再假设 `MVarId` 仅仅因为分配了元变量而发生更改（例如，当 `change` 的唯一效果是偶然分配时，`change` 不再更改 `MVarId`）；它还显示许多 `dsimp` 没有执行任何操作并且可以删除。
- [#13243](https://github.com/leanprover/lean4/pull/13243) 在 *以模式*精化结构实例符号时不再应用结构的默认值（例如添加了 `s matches { x := 1 }`). *Breaking change:* such patterns may now report “field missing” errors and need the missing fields supplied or a `..`。
- [#13476](https://github.com/leanprover/lean4/pull/13476) 在计算 `apply`/`rewrite` 子目标标签之前过滤分配的元变量，因此单个剩余目标现在继承输入目标的标签。 *重大更改：*依赖于先前标签名称的脚本（例如 `funext` 之后的 `case h => …`）可能需要更新。
- [#13030](https://github.com/leanprover/lean4/pull/13030) 更改级别元变量漂亮打印以使用每个定义索引。 *重大元编程更改：*级别漂亮打印应使用 `delabLevel` 或 `MessageData.ofLevel`； `format`/`toString` 无法访问索引，并将原始内部标识符打印为 `?_mvar.nnn`。由于索引记录分配，一些测试需要 `maxHeartbeats` 提高 20-50%。
- [#13627](https://github.com/leanprover/lean4/pull/13627) 将 `UInt8.ofNatTruncate` 重命名为 `UInt8.ofNatClamp`（以及其他宽度变体），以便与 `UIntX` API 的其余部分保持一致。
- [#13516](https://github.com/leanprover/lean4/pull/13516) 将缺失的 `namespace Lake` 添加到 `Lake.Util.Opaque`；必须更新引用 `Opaque` 而没有 `open Lake` 的代码。

# 语言
%%%
file := "Language"
tag := "zh-releases-v4-31-0-h011"
%%%

````markdown

- [#13803](https://github.com/leanprover/lean4/pull/13803)
  renames the `defLemma` linter to `defProp` and clarifies
  its warning message.

- [#13862](https://github.com/leanprover/lean4/pull/13862)
  updates the error message improvement from #10488 to also check for identifier escape characters when providing the improved message. Before, it checked only for identifier start characters.

- [#13853](https://github.com/leanprover/lean4/pull/13853)
  makes `lake lint --builtin-lint` group saved text linter diagnostics by the module
  that produced them, rather than printing one combined block under the
  top-level module being linted. Each contributing submodule now gets its own
  `-- Text linter diagnostics in <module>:` header, mirroring how the
  environment-linter side already groups results.

- [#13844](https://github.com/leanprover/lean4/pull/13844)
  makes `Lean.Linter.logLint` attach an internal tag to every
  linter warning so that `Lean.Linter.recordLints` can reliably distinguish
  linter-produced messages from other tagged messages (named errors,
  unknown-identifier messages, `hasSorry` markers, etc.). Previously,
  `recordLints` captured every message whose top-level kind was non-anonymous,
  which over-recorded non-linter diagnostics into the persistent lint log.

- [#13752](https://github.com/leanprover/lean4/pull/13752)
  makes projection notation errors always mention a private declaration on a parent structure as the cause when applicable. Previously, for projections that resolved through structure inheritance, the hint was silently omitted, leaving users without the actual cause.

- [#13813](https://github.com/leanprover/lean4/pull/13813)
  fixes an issue where `beforeElaboration` attributes were not being run on `inductive`/`structure`/`coinductive` commands. Closes #13433.

- [#13811](https://github.com/leanprover/lean4/pull/13811)
  updates the `#where` command to be able to report `module`-related scope state, for example a  `@[expose] public meta section` line in the output.

- [#13760](https://github.com/leanprover/lean4/pull/13760)
  improves elaboration performance for structure instance notation with large numbers of fields. It also uses beta-reducing substitution for structure parameters, which is already the case for structure fields.

- [#13807](https://github.com/leanprover/lean4/pull/13807)
  modifies the app elaborator to beta reduce arguments while substituting them into expected types for later arguments. This makes it consistent with `inferType` and `instantiateMVars`, which both beta reduce substitutions. In particular, this change ensures that the app elaborator behaves as if it creates metavariables for each parameter and assigns elaborated arguments to the metavariables. **Breaking change:** tactic proofs may need to be modified to remove unnecessary steps, e.g. `dsimp only` steps that were previously for beta reductions.

- [#13808](https://github.com/leanprover/lean4/pull/13808)
  enforces that Verso docstring extensions should always be meta at attribute application time, giving better error messages, and ensures that the generated argument parser helper is also meta and has the same visibility.

- [#13801](https://github.com/leanprover/lean4/pull/13801)
  adds two new fields to `DoOps`, `splitMonadApp?` and `mkMonadApp`, so that callers of `elabDoWith` can use indexed monads like `Measure α` (where `Measure : (α : Type u) → [MeasureSpace α] → Type u` carries instance arguments) that the default `m α` decomposition cannot handle. The existing behavior moves into `DoOps.default`.

- [#13800](https://github.com/leanprover/lean4/pull/13800)
  renames the `do` elaborator's `mkMonadicType` to `mkMonadApp`, aligning it with the existing `mkPureApp` / `mkBindApp` naming convention in `DoOps`.

- [#13780](https://github.com/leanprover/lean4/pull/13780)
  is part 2 to #13779. It completes the transition of the configuration evaluation metaprograms into being builtin elaborators.

- [#13779](https://github.com/leanprover/lean4/pull/13779)
  makes the command elaborators for configuration evaluation metaprogramming be builtins, to avoid bootstrapping ABI issues in core Lean due to the interpreter evaluating large parts of the elaborator before all builtin initializers are run. (This is part 1; #13780 will be applied after a stage0 update.)

- [#13762](https://github.com/leanprover/lean4/pull/13762)
  does some refactoring of the function application elaborator, and it improves `trace.Elab.app` tracing. It also improves asymptotic complexity by more carefully substituting arguments into the function's type and by changing how named argument dependency suppression is implemented. For dot notation, it now constructs base projections directly rather than using the app elaborator. It fixes a bug in the eta args feature where more explicit arguments would be turned into implicit arguments than expected, and it improves expected type propagation by following the rules from the main app elaborator.

- [#13772](https://github.com/leanprover/lean4/pull/13772)
  closes https://github.com/leanprover/lean4/issues/13770 by including `Config.zetaUnused` in `Config.toKey`. Without this, two configs that differ only in `zetaUnused` share a `WHNF`/`isDefEq` cache key, so reductions performed under one setting can be returned for the other. The new bit sits at position 22, immediately above `zetaHave`.

- [#13768](https://github.com/leanprover/lean4/pull/13768)
  fixes a long-standing bug in `Meta.Config.toKey` and `Context.setTransparency` where `TransparencyMode` was packed into only 2 bits of the cache key, even though it has 5 constructors (`.all`, `.default`, `.reducible`, `.instances`, `.none`). The `.none` case (value `4`, i.e. `0b100`) overlapped with the `foApprox` bit, so configurations differing only in transparency vs. `foApprox` could collide in the `isDefEq`/`WHNF` cache, and `Context.setTransparency` corrupted the neighbouring bit when switching to/from `.none`.

- [#13763](https://github.com/leanprover/lean4/pull/13763)
  adds `MessageData.withExprHover`, for creating messages that show information about an expression when hovered over. A `withExprHoverM` variant captures the current local context.

- [#13758](https://github.com/leanprover/lean4/pull/13758)
  improves `Expr.instantiateBetaRevRange` to be more efficient in the common case where lambda functions are not being instantiated, and it increases expression sharing in applications.

- [#13737](https://github.com/leanprover/lean4/pull/13737)
  changes the separator between the plugin file name and the initialization function in `--plugin` from `:` to `=`. This prevents clashes with the `:` in drive prefixes on Windows.

- [#13651](https://github.com/leanprover/lean4/pull/13651)
  replaces the previous tactic configuration system with a significantly more efficient one that supports custom configuration syntaxes and processing. On a simple benchmark, configuration evaluation takes 6.2% of the time it used to. The `declare_config_elab` command generates a configuration elaborator that now directly constructs configuration objects; previously it relied on `Meta.evalExpr'`, which involved running a configuration through the full term elaboration, compilation, and evaluation processes. The generated configuration elaborators now also have the capability to do direct `Syntax` evaluation in common cases, skipping term elaboration. Furthermore, the elaborator accepts configurations more liberally: any user-defined syntax that has the form of an `optConfig`-style configuration or configuration item (including, e.g., `namedArgument`s) is accepted. Import `Lean.Elab.ConfigEval` to use the system; see this module for some documentation in addition to the docstrings in `Lean.Elab.ConfigEval.Commands`. Furthermore, the `simp` tactic now also has `(user.optionName := ...)` user configuration options, which can be declared using a global `tactic.simp.user.optionName` option; use `getUserConfigOption` and `withUserConfig` to access and set these in metaprograms.

- [#13550](https://github.com/leanprover/lean4/pull/13550)
  improves the logic and performance of the `checkImpossibleInstance` function to detect more arguments that are impossible to
  infer for typeclass synthesis. It also improves the formatting of the error messages for `checkImpossibleInstance` and `checkNonClassInstance` to be more readable.

- [#13730](https://github.com/leanprover/lean4/pull/13730)
  fixes a regression introduced in #7166 where, after fixed and varying
  parameters were allowed to be reordered, three places in
  `Lean.Elab.Structural.FindRecArg` still indexed the concatenation `xs ++ ys`
  with `recArgInfo.recArgPos` even though `recArgPos` refers to the original
  parameter order. With fixed parameters interleaved with the structural
  argument, this picked the wrong element: error messages named the wrong
  parameter, and `argsInGroup`'s nested-inductive recognition silently rejected
  otherwise-valid mutual definitions.

- [#13728](https://github.com/leanprover/lean4/pull/13728)
  improves hovers and completions for compound field names in structure instance notation. Previously a field like `x.fst` would only have information associated to `x` attached to the entire syntax, but now `x` and `fst` are treated separately.

- [#13715](https://github.com/leanprover/lean4/pull/13715)
  improves the message of `unusedVariables` linter, by replacing potentially confusing "unused variable `x`" message with "Variable name `x` is not explicitly referenced. The binding can be removed (if unused) or named `_` (if used implicitly)."

- [#13710](https://github.com/leanprover/lean4/pull/13710)
  makes the test-only `waitForMessage` helper abort promptly
  when the Lean language server reports a fatalError, instead of
  blocking until the outer test framework's timeout kills the process.

- [#11313](https://github.com/leanprover/lean4/pull/11313)
  ensures that `withSetOptionIn` does not modify the infotrees or error on malformed option values, and thus avoids panics in linters that traverse the infotrees with `visitM`.

- [#13595](https://github.com/leanprover/lean4/pull/13595)
  silences the `Linter.deprecated` warnings inside of definitions that are themselves deprecated.

- [#13209](https://github.com/leanprover/lean4/pull/13209)
  adds `whileM`, a counterpart to `Lean.Loop.forIn` that admits a one-step unfolding lemma `whileM_eq` (impossible to prove for the original `partial def`). `Lean.Loop.forIn` now expands to `whileM`, so `repeat`/`while` keep working without source changes, and the `Spec.whileM`/`Spec.forIn_loop` `@[spec]` theorems let `mvcgen` discharge their bodies given a Nat variant and an `α ⊕ β` invariant.

- [#13670](https://github.com/leanprover/lean4/pull/13670)
  adds support for blockquotes to Verso docstrings, which had been missing before. It also substantially improves the robustness of Verso->Markdown rendering of docstrings, especially the handling of blockquote line prefixes.

- [#13663](https://github.com/leanprover/lean4/pull/13663)
  replaces the `check_cancel` two-way coordination protocol used by
  `tests/server_interactive/cancellation_par.lean` with a single tactic
  `block_until_cancelled "<label>"`. The first invocation for a label registers
  a promise, prints `<label>: blocked`, and loops on `Core.checkInterrupted`
  until the cancel token fires (then `finally` resolves the promise). Any later
  invocation for the same label waits on that promise — so the test only
  terminates if the first invocation actually exited the loop. If cancellation
  fails to propagate, the second invocation's `IO.wait` blocks forever and the
  test hangs (timeout = failure), with no false-success path.

- [#13548](https://github.com/leanprover/lean4/pull/13548)
  fixes possible corruption when recovering from memory exhaustion.

- [#13613](https://github.com/leanprover/lean4/pull/13613)
  makes the elaborator reject `@[foo]` when the module that registers `foo` is not visibly imported into the current file but merely loaded as IR. Previously such uses silently elaborated but led to divergence of cmdline and server behavior and caused `lake shake --fix` to flip-flop on successive runs (#13599).

- [#13510](https://github.com/leanprover/lean4/pull/13510)
  adds the ability to specify a name for the initialization function of a Lean plugin on load.

- [#13645](https://github.com/leanprover/lean4/pull/13645)
  fixes the termination checker reporting errors at the wrong
  recursive call site when a function contains structurally-identical
  recursive calls at different source locations.

- [#13547](https://github.com/leanprover/lean4/pull/13547)
  prevents silent allocation failures leading to memory corruption when not using GMP.

- [#13596](https://github.com/leanprover/lean4/pull/13596)
  fixes private(ly imported) default instances from accidentally being used in public signatures, leading to follow-up errors.

- [#13574](https://github.com/leanprover/lean4/pull/13574)
  ensures consistent metavariable behavior between Verso docstrings and Verso moduledocs by sharing more code between their elaborators. It also improves the error message when a metavariable leak is prevented.

- [#13528](https://github.com/leanprover/lean4/pull/13528)
  gives the `specialize` tactic the ability to instantiate universal quantifiers other than the first using `specialize h (y := v)` syntax. It also fixes an issue where `MVarId.assertAfter` did not record variable alias information, and an issue where `MVarId.replace` and `MVarId.replaceLocalDecl` did not take metavariables into account when calculating dependencies. Additionally it fixes some uninstantiated metavariables bugs, including one in the Infoview tactic state hypothesis diff.

- [#13428](https://github.com/leanprover/lean4/pull/13428)
  fixes parallel tactic combinators (`attempt_all_par`, `first_par`) leaking their subtasks when the server cancels elaboration on re-elaboration. Subtasks spawned via `CoreM.asTask` (and its `MetaM`/`TermElabM`/`TacticM` variants) get a fresh `IO.CancelToken`, which previously had no link to the parent token; `cancelRec` would set the command-level token but the children kept running.

- [#13569](https://github.com/leanprover/lean4/pull/13569)
  addresses two review points on `IO.CancelToken`:

  * `set` now resolves the underlying promise *before* writing the `Bool`
    fast-path flag, so observing `isSet = true` implies any synchronously
    chained `onSet` callback has already run. The previous order (flag first,
    then resolve) was a subtle footgun: code seeing `isSet = true` could not
    rely on the cancellation task having fired.
  * The underlying promise and the task it produces are kept private. The
    prior `task : Task (Option Unit)` accessor is removed; consumers should
    use `onSet` to react to cancellation. A comment on the structure records
    that re-exposing the task in the future requires re-auditing the order
    in `set` for races between the promise and the `Bool` flag.

- [#13303](https://github.com/leanprover/lean4/pull/13303)
  moves `IO.CancelToken` from `Init.System.IO` to its own file `Init.System.CancelToken`, backed by `IO.Promise Unit` instead of `IO.Ref Bool`. This enables non-polling cancellation propagation: the token's underlying promise can be used directly with `IO.waitAny`, and callbacks can be registered to fire when cancellation is requested.

- [#13542](https://github.com/leanprover/lean4/pull/13542)
  replaces the catch-all "unsupported pattern in syntax match" error that the new `do` elaborator produces for typical pattern mistakes (#2215, #8304, #10393) with the proper diagnostics from the regular pattern-var collector (e.g. "Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`", "ambiguous pattern, use fully qualified name"), pointing at the offending pattern.

- [#13359](https://github.com/leanprover/lean4/pull/13359)
  adds a `linter.redundantExpose` option (default `true`) that warns when `@[expose]` or `@[no_expose]` attributes have no effect:

  - `@[expose]` on `abbrev` (always exposed) or non-Prop `instance` (always exposed)
  - `@[expose]` on a `def` inside an `@[expose] section` (already exposed by the section)
  - `@[expose]`/`@[no_expose]` in a non-`module` file (no module system)
  - `@[no_expose]` on a declaration that wouldn't be exposed by default

- [#13492](https://github.com/leanprover/lean4/pull/13492)
  introduces stricter inference for the `@[defeq]` attribute and a
  companion `@[backward_defeq]` attribute that preserves the pre-PR behavior
  as an opt-in.

- [#13534](https://github.com/leanprover/lean4/pull/13534)
  generalizes the `while` syntax in `do` blocks so that the condition can be any `doIfCond`, the same condition form already accepted by `if`. As a result, `while let pat := e do …` and `while let pat ← e do …` are now supported in addition to `while cond do …` and `while h : cond do …`. The previously separate `doWhile` and `doWhileH` parsers and their accompanying macros are unified into a single `doWhile` parser whose macro delegates to the existing `doIf` desugaring.

- [#13523](https://github.com/leanprover/lean4/pull/13523)
  allows tactic macros and elaborators to opt out of automatic fallback to previous macros/elabs on failure. `throwUnsupportedSyntax` is unaffected.

- [#13363](https://github.com/leanprover/lean4/pull/13363)
  replaces the transparency bump from `.reducible` to `.instances` in `whnfMatcher` with an explicit allowlist in `canUnfoldAtMatcher`. Previously, `whnfMatcher` would unfold all `implicitReducible` definitions and all `fromClass` projections when reducing match discriminants. This made it impossible to mark definitions as `implicit_reducible` without silently affecting match reduction behavior.

- [#13512](https://github.com/leanprover/lean4/pull/13512)
  changes `whnfAux` in the equation-theorem generation machinery to use
  reducible transparency (`whnfR`) instead of instances transparency (`whnfI`).
  Previously, the loop in `Eqns.go` would unfold instances on the LHS, which
  interacts badly with users that mark `dite`/`ite` as `implicit_reducible`:
  equation generation would reduce past the `dite` and get stuck instead of
  committing to a branch. The original motivation for `whnfI` (reducing
  `Nat.rec ... (OfNat.ofNat 0)` residuals from `match` on numeric literals) is
  already covered by the surrounding `simpMatch?`/`simpIf?`/`simpTargetStar`
  steps in `Eqns.go`, so the full test suite continues to pass.

- [#13506](https://github.com/leanprover/lean4/pull/13506)
  appends `unreachable!` to the expansion of `break`-less `repeat` when the expected result type does not unify with `PUnit`. The continuation then has a polymorphic value, so the enclosing do block's result type is inferred without a user-written filler, and `ControlInfo` for break-less `repeat` can report `noFallthrough` honestly — dead-code warnings on subsequent elements are now actionable.

- [#13507](https://github.com/leanprover/lean4/pull/13507)
  exposes the `Pure.pure` / `Bind.bind` applications emitted by the `do` elaborator as pluggable closures, so external surface syntaxes (e.g. an `ido` notation for indexed monads) can reuse the full `do` machinery while emitting alternate constants.

- [#13491](https://github.com/leanprover/lean4/pull/13491)
  fixes the `ControlInfo` inference for a do-block `match`: the fold over the match arms started from `ControlInfo.pure` (defaults to `numRegularExits := 1`, `noFallthrough := false`), but `alternative` sums `numRegularExits` and ANDs `noFallthrough`, so the fold identity is `{ numRegularExits := 0, noFallthrough := true }`. With the wrong base, a `match` whose arms all `break`/`continue`/`return` reported `numRegularExits = 1` and `noFallthrough = false`, suppressing the dead-code warning on the continuation after the match. The fix corrects both the inference handler in `InferControlInfo.lean` and the fold in `elabDoMatchCore`.

- [#13502](https://github.com/leanprover/lean4/pull/13502)
  splits `ControlInfo`'s dead-code signal in two. `numRegularExits` is now purely syntactic: how many times the block wires its continuation into the elaborated expression, consumed by `withDuplicableCont` as a join-point duplication trigger (`> 1`). The new `noFallthrough : Bool` asserts that the next doElem in the enclosing sequence is semantically irrelevant; `false` asserts nothing. Invariant: `numRegularExits = 0 → noFallthrough`; the converse does not hold. `sequence` derives `noFallthrough := a.noFallthrough || b.noFallthrough` (and aggregates syntactic fields unconditionally); `alternative` derives it as `a.noFallthrough && b.noFallthrough`. The dead-code warning gate in `withDuplicableCont` and `ControlLifter.ofCont` now reads `noFallthrough`.

- [#13494](https://github.com/leanprover/lean4/pull/13494)
  stops the `repeat` inference handler from reporting `numRegularExits := 0` for break-less bodies. For break-less `repeat` the loop never terminates normally, so `0` looks more accurate semantically, but the loop expression still has type `m Unit` and the do block's continuation after the loop is what carries that type. Reporting `0` makes the elaborator flag that continuation as dead code, yet there is no way for the user to remove it that is also type correct — unless the enclosing do block's monadic result type happens to be `Unit`. Pinning `numRegularExits` at `1` (matching `for ... in`) eliminates those spurious warnings.

- [#13489](https://github.com/leanprover/lean4/pull/13489)
  fixes a bug where the nesting level in Verso Docstrings is forgotten when there's a doc comment with no headers.

- [#13486](https://github.com/leanprover/lean4/pull/13486)
  fixes `inferControlInfoSeq` and `ControlInfo.sequence` to keep aggregating `breaks`/`continues`/`returnsEarly`/`reassigns` past elements whose `ControlInfo` reports `numRegularExits := 0`. Previously the analysis short-circuited at such elements, so any trailing `return`/`break`/`continue` was missing from the inferred info. The elaboration framework only skips subsequent doElems syntactically for top-level `return`/`break`/`continue`; for every other `numRegularExits == 0` case (e.g. a `match`/`if`/`try` whose branches all terminate, or a `repeat` without `break`) the elaborator keeps visiting the continuation and the for/match elaborator then tripped its invariant check with `Early returning ... but the info said there is no early return`. With this change the inferred info matches what the elaborator actually sees, which also removes the need for the `numRegularExits := 1` workaround on `repeat` introduced in #13479.

- [#13477](https://github.com/leanprover/lean4/pull/13477)
  fixes a benchmark regression introduced in #13475: `eqnOptionsExt`
  was using `.async .asyncEnv` asyncMode, which accumulates state in the
  `checked` environment and can block. Switching to `.local` — consistent
  with the neighbouring `eqnsExt` and the other declaration caches in
  `src/Lean/Meta` — restores performance (the
  `build/profile/blocked (unaccounted) wall-clock` bench moves from +33%
  back to baseline). `.local` is safe here because `saveEqnAffectingOptions`
  is only called during top-level `def` elaboration and downstream readers
  see the imported state; modifications on non-main branches are merged
  into the main branch on completion.

- [#13475](https://github.com/leanprover/lean4/pull/13475)
  replaces the eager equation realization that was triggered by
  non-default values of equation-affecting options (like
  `backward.eqns.nonrecursive`) with a `MapDeclarationExtension` that
  stores non-default option values at definition time. These values are
  then restored when equations are lazily realized, so the same equations
  are produced regardless of when generation occurs.

- [#13367](https://github.com/leanprover/lean4/pull/13367)
  removes some cases where `simp` would significantly overrun a timeout.

- [#13447](https://github.com/leanprover/lean4/pull/13447)
  removes the transitional `syntax` declarations for `repeat`, `while`, and `repeat ... until` from `Init.While` and promotes the corresponding `@[builtin_doElem_parser]` defs in `Lean.Parser.Do` from `low` to default priority, making them the canonical parsers.

- [#13442](https://github.com/leanprover/lean4/pull/13442)
  promotes the `repeat`, `while`, and `repeat ... until` parsers from `syntax` declarations in `Init.While` to `@[builtin_doElem_parser]` definitions in `Lean.Parser.Do`, alongside the other do-element parsers. The `while` variants and `repeat ... until` get `@[builtin_macro]` expansions; `repeat` itself gets a `@[builtin_doElem_elab]` so a follow-up can extend it with an option-driven choice between `Loop.mk` and a well-founded `Repeat.mk`.

- [#13437](https://github.com/leanprover/lean4/pull/13437)
  adds a builtin `doElem_control_info` handler for `doRepeat`. It is ineffective as long as we have the macro for `repeat`.

- [#13434](https://github.com/leanprover/lean4/pull/13434)
  names the `repeat` syntax (`doRepeat`) and installs dedicated elaborators for it in both the legacy and new do-elaborators. Both currently expand to `for _ in Loop.mk do ...`, identical to the existing fallback macro in `Init.While`.

- [#13389](https://github.com/leanprover/lean4/pull/13389)
  adds two validation checks to `addInstance` that provide early feedback for common mistakes in instance declarations:

  1. **Non-class instance check**: errors when an instance target type is not a type class. This catches the common mistake of writing `instance` for a plain structure. Previously handled by the `nonClassInstance` linter in Batteries (`Batteries.Tactic.Lint.TypeClass`), this is now checked directly at declaration time.

  2. **Impossible argument check**: errors when an instance has arguments that cannot be inferred by instance synthesis. Specifically, it flags arguments that are not instance-implicit and do not appear in any subsequent instance-implicit argument or in the return type. Previously such instances would be silently accepted but could never be synthesised.

- [#13315](https://github.com/leanprover/lean4/pull/13315)
  fixes `processDefDeriving` to propagate the `meta` attribute to instances derived via delta deriving, so that `deriving BEq` inside a `public meta section` produces a meta instance. Previously the derived `instBEqFoo` was not marked meta, and the LCNF visibility checker rejected meta definitions that used `==` on the alias — this came up while bumping verso to v4.30.0-rc1.

- [#13404](https://github.com/leanprover/lean4/pull/13404)
  fixes #12846, where the new do elaborator produced confusing errors when a do element's continuation had a mismatched monadic result type. The errors were misleading both in location (e.g., pointing at the value of `let x ← value` rather than the `let` keyword) and in content (e.g., mentioning `PUnit.unit` which the user never wrote).

- [#13420](https://github.com/leanprover/lean4/pull/13420)
  fixes a panic when `coinductive` predicates are defined inside macro scopes where constructor names carry macro scopes. The existing guard only checked the declaration name for macro scopes, missing the case where constructor identifiers are generated inside a macro quotation and thus carry macro scopes. This caused `removeFunctorPostfixInCtor` to panic on `Name.num` components from macro scope encoding.

- [#13413](https://github.com/leanprover/lean4/pull/13413)
  adds an internal `skip` syntax for do blocks, intended for use by the `if` and `unless` elaborators to replace `pure PUnit.unit` in implicit else branches. This gives the elaborator a dedicated syntax node to attach better error messages and location info to, rather than synthesizing `pure PUnit.unit` which leaks internal details into user-facing errors.

- [#13391](https://github.com/leanprover/lean4/pull/13391)
  adds level instantiation and normalization in `getDecLevel` and `getDecLevel?` before calling `decLevel`.

- [#13395](https://github.com/leanprover/lean4/pull/13395)
  makes the `deriving Inhabited` handler for `structure`s be able to inherit `Inhabited` instances from structure parents, using the same mechanism as for class parents. This fixes a regression introduced by #9815, which lost the ability to apply `Inhabited` instances for parents represented as subobject fields. With this PR, now it works for all parents in the hierarchy.

- [#13399](https://github.com/leanprover/lean4/pull/13399)
  fixes #12827, where hovering over `for` loop variables `x` and `h` in `for h : x in xs do` showed no type information in the new do elaborator. The fix adds `Term.addLocalVarInfo` calls for the loop variable and membership proof binder after they are introduced by `withLocalDeclsD` in `elabDoFor`.

- [#13397](https://github.com/leanprover/lean4/pull/13397)
  improves error reporting when the `do` elaborator produces an ill-formed expression that fails `checkedAssign` in `withDuplicableCont`. Previously the failure was silently discarded, making it hard to diagnose bugs in the `do` elaborator. Now a descriptive error is thrown showing the join point RHS and the metavariable it failed to assign to.

- [#13396](https://github.com/leanprover/lean4/pull/13396)
  fixes #12768, where the new `do` elaborator produced a "declaration has free variables" kernel error when the bind continuation's result type was definitionally but not syntactically independent of the bound variable. The fix moves creation of the result type metavariable before `withLocalDecl`, so the unifier must reduce away the dependency.

- [#13325](https://github.com/leanprover/lean4/pull/13325)
  adds warnings when registering `@[simp]` theorems whose left-hand side has a problematic head symbol in the discrimination tree:

  - **Variable head** (`.star` key): The theorem will be tried on every `simp` step, which can be expensive. The warning notes this may be acceptable for `local` or `scoped` simp lemmas. Controlled by `warning.simp.varHead` (default: `true`).
  - **Unrecognized head** (`.other` key, e.g. a lambda expression): The theorem is unlikely to ever be applied by `simp`. Controlled by `warning.simp.otherHead` (default: `true`).

- [#13390](https://github.com/leanprover/lean4/pull/13390)
  changes the linear BEq derivation strategy to use `Nat.decEq` instead of `decEq` when comparing constructor indices. Since constructor indices are always `Nat`, using `Nat.decEq` directly is more appropriate because it is `@[reducible]`, whereas the generic `decEq` is only semireducible and does not unfold at `.reducible` transparency. This makes the generated code more transparent-friendly.

- [#13356](https://github.com/leanprover/lean4/pull/13356)
  upstreams environment linters of batteries to core lean.

- [#13360](https://github.com/leanprover/lean4/pull/13360)
  fixes #13268 where `local macro` (and other local declarations) with compound names of depth ≥ 3 would silently lose their local entries.

- [#13374](https://github.com/leanprover/lean4/pull/13374)
  fixes `SizeOf` instance generation for public inductive types that have
  private constructors. The spec theorem proof construction needs to unfold
  `_sizeOf` helper functions which may not be exposed in the public view, so
  we use `withoutExporting` for the proof construction and type check.

- [#13239](https://github.com/leanprover/lean4/pull/13239)
  fixes an issue where `(builtin_)initialize` inside `module` would not allow referencing private defs in its type unless explicitly prefixed with `private`.

- [#9815](https://github.com/leanprover/lean4/pull/9815)
  changes the `Inhabited` deriving handler for `structure` types to use default field values when present; this ensures that `{}` and `default` are interchangeable when all fields have default values. The handler effectively uses `by refine' {..} <;> exact default` to construct the inhabitant. (Note: when default field values cannot be resolved, they are ignored, as usual for ellipsis mode.)

- [#13318](https://github.com/leanprover/lean4/pull/13318)
  adds a check for OS-forbidden names and characters in module names.  This implements the functionality of `modulesOSForbidden` linter of mathlib.

- [#13262](https://github.com/leanprover/lean4/pull/13262)
  extends Lean's syntax to allow explicit universe levels in expressions such as `e.f.{u,v}`, `(f e).g.{u}`, and `e |>.f.{u,v} x y z`. It fixes a bug where universe levels would be attributed to the wrong expression; for example `x.f.{u}` would be interpreted as `x.{u}.f`. It also changes the syntax of top-level declarations to not allow space between the identifier and the universe level list, and it fixes a bug in the `checkWsBefore` parser where it would not detect whitespace across `optional` parsers.

- [#13332](https://github.com/leanprover/lean4/pull/13332)
  fixes universe unification for `for` loops with `mut` variables whose types span multiple implicit universes. The old approach used `ensureHasType (mkSort mi.u.succ)` per variable, which generated constraints like `max (?u+1) (?v+1) =?= ?u+1` that the universe solver cannot decompose. The new approach uses `getDecLevel`/`isLevelDefEq` on the decremented level, producing `max ?u ?v =?= ?u` which `solveSelfMax` handles directly.

- [#13229](https://github.com/leanprover/lean4/pull/13229)
  wraps the top-level command parser with `withPosition` to enforce indentation in `by` blocks, combined with an empty-by fallback for better error messages.

- [#13320](https://github.com/leanprover/lean4/pull/13320)
  changes the auto-generated `sizeOf` definitions to be not
  exposed and the `sizeOf_spec` theorem to be not marked `[defeq]`.

- [#13311](https://github.com/leanprover/lean4/pull/13311)
  adds an optional `markMeta : Bool := false` parameter to `addAndCompile`, so that callers can propagate the `meta` marking without manually splitting into `addDecl` + `markMeta` + `compileDecl`.

- [#13319](https://github.com/leanprover/lean4/pull/13319)
  amends #13317 to suggest `:= (rfl)` as the recommended way to avoid a theorem to be automatically marked `[defeq]`, for consistency with existing documentation. Rationale: the special treatment of `:= rfl` is based on syntax, not the proof term, so it’s appropriate to use different syntax. And also I like the way it reads like a “muted whisper of `rfl`”.

- [#13223](https://github.com/leanprover/lean4/pull/13223)
  adds a warning preventing a user from applying global attribute using `... in ...`, e.g.
  ```lean4
  theorem a : True := trivial
  attribute [simp] a in
  def b : True := a
  ```

- [#13317](https://github.com/leanprover/lean4/pull/13317)
  adds an opt-in linter (`set_option simp.rfl.checkTransparency true`) that warns when a `rfl` simp theorem's LHS and RHS are not definitionally equal at `.instances` transparency. Bad rfl-simp theorems — those that only hold at higher transparency — create problems throughout the system because `simp` and `dsimp` operate at restricted transparency. The linter suggests two fixes: use `id rfl` as the proof (to remove the `rfl` status), or mark relevant constants as `[implicit_reducible]`.

- [#13304](https://github.com/leanprover/lean4/pull/13304)
  makes the delta-deriving handler create `theorem` declarations instead of `def` declarations when the instance type is a `Prop`. Previously, `deriving instance Nonempty for Foo` would always create a `def`, which is inconsistent with the behavior of a handwritten `instance` declaration.

- [#13281](https://github.com/leanprover/lean4/pull/13281)
  marks any exposed (non-private) auxiliary match declaration as `[implicit_reducible]`. This is essential when the outer declaration is marked as `instance_reducible` — without it, reduction is blocked at the match auxiliary. We do not inherit the attribute from the parent declaration because match auxiliary declarations are reused across definitions, and the reducibility setting of the parent can change independently. This change prepares for implementing the TODO at `ExprDefEq.lean:465`, which would otherwise cause too many failures requiring manual `[implicit_reducible]` annotations on match declarations whose names are not necessarily derived from the outer function.

- [#13280](https://github.com/leanprover/lean4/pull/13280)
  adds a new option `backward.isDefEq.respectTransparency.types` that controls the transparency used when checking whether the type of a metavariable matches the type of the term being assigned to it during `checkTypesAndAssign`. Previously, this check always bumped transparency to `.default` (via `withInferTypeConfig`), which is overly permissive. The new option uses `.instances` transparency instead (via `withImplicitConfig`), matching the behavior already used for implicit arguments.

- [#13266](https://github.com/leanprover/lean4/pull/13266)
  changes the counter-example accumulator in the match compiler from
  a `List` (built with cons, producing reverse order) to an `Array` (built
  with push, preserving declaration order). Missing cases are now reported in
  the order constructors appear in the inductive type definition.

- [#13243](https://github.com/leanprover/lean4/pull/13243)
  changes elaboration of structure instance notation when used in patterns (e.g. `s matches { x := 1, y := [] }`) so that the structure's default values are not used to elaborate the pattern. The motivation is that default values frequently lead to surprisingly over-specific patterns. It will now report "field missing" errors. The error can be suppressed using `{ x := 1, .. }` ellipsis notation, which has the same behavior as before. The pretty printer is also modified to stay in sync with this feature. **Breaking change:** patterns using structure instance notation may need missing fields or a `..` added, as appropriate.

- [#13195](https://github.com/leanprover/lean4/pull/13195)
  adds support for marking options as deprecated. When a deprecated option is used via `set_option`, a warning is emitted (controlled by `linter.deprecated.options`).

- [#13255](https://github.com/leanprover/lean4/pull/13255)
  adds support for let configuration options (`(eq := h)`, `+nondep`, `+usedOnly`, `+zeta`) in `do` block `let` and `have` declarations, matching the behavior available in term-level `let`/`have`. Configuration options are rejected with `let mut` since they are incompatible with mutable bindings. `+postponeValue` and `+generalize` are also rejected in `do` blocks.

- [#13250](https://github.com/leanprover/lean4/pull/13250)
  extends the `doLet`, `doLetElse`, `doLetArrow`, and `doHave` parsers to accept `letConfig` (e.g. `(eq := h)`, `+nondep`, `+usedOnly`, `+zeta`), matching the syntax of term-level `let`/`have`. The elaborators are adjusted to handle the shifted syntax indices but do not yet process the configuration; that will be done in a follow-up PR after stage0 is updated, allowing the use of proper quotation patterns.

- [#13245](https://github.com/leanprover/lean4/pull/13245)
  extends Lean syntax for dotted function notation (`.f`) to add support for explicit mode (`@.f`), explicit universes (`.f.{u,v}`), and both simultaneously (`@.f.{u,v}`). This also includes a fix for a bug involving overloaded functions, where it used to give erroneous deprecation warnings about declarations that the function did not elaborate to.

- [#13232](https://github.com/leanprover/lean4/pull/13232)
  fixes a panic when compiling mutually recursive definitions that use `casesOn` on indexed inductive types (e.g. `Vect`). The `splitMatchOrCasesOn` function in `WF.Unfold` asserted `matcherInfo.numDiscrs = 1`, but for indexed types the casesOn recursor has multiple discriminants (indices + major premise). The fix uses the last discriminant (the major premise) and lets the `cases` tactic handle index discriminants automatically.

- [#13002](https://github.com/leanprover/lean4/pull/13002)
  adds a `deprecated_module` command that marks the current module as deprecated. When another module imports a deprecated module, a warning is emitted during elaboration suggesting replacement imports.

- [#13205](https://github.com/leanprover/lean4/pull/13205)
  fixes `FirstTokens.seq (.optTokens s) .unknown` to return `.unknown`. This occurs e.g. when an optional (with first tokens `.optTokens s`) is followed by a parser category (with first tokens `.unknown`). Previously `FirstTokens.seq` returned `.optTokens s`, ignoring the fact that the optional may be empty and then the parser category may have any first token. The correct behavior here is to return `.unknown`, which indicates that the first token may be anything.

- [#13220](https://github.com/leanprover/lean4/pull/13220)
  adds `checkSystem` calls to several code paths that can run for
  extended periods without checking for cancellation, heartbeat limits, or
  stack overflow. This improves responsiveness of the cancellation mechanism
  in the language server.

- [#13108](https://github.com/leanprover/lean4/pull/13108)
  adds a `deprecated_syntax` command that marks syntax kinds as deprecated. When deprecated syntax is elaborated (in terms, tactics, or commands), a linter warning is emitted. The warning is also emitted during quotation precheck when a macro definition uses deprecated syntax in its expansion.

- [#13219](https://github.com/leanprover/lean4/pull/13219)
  moves `hasAssignableMVar`, `hasAssignableLevelMVar`, and `isLevelMVarAssignable` from `MetavarContext.lean` to a new `Lean.Meta.HasAssignableMVar` module, changing them from generic `[Monad m] [MonadMCtx m]` functions to `MetaM` functions. This enables adding `checkSystem` calls in the recursive traversal, which ensures cancellation and heartbeat checks happen during what can be a very expensive computation.

````

# 图书馆
%%%
file := "Library"
tag := "zh-releases-v4-31-0-h012"
%%%

```markdown

- [#13863](https://github.com/leanprover/lean4/pull/13863)
  更改 `BitVec` 上的电子匹配注释，以避免自动从 `getMsbD` 理论转到 `getLsbD` 理论。关键原因是所有引理已经在 `getMsbD` 和 `getLsbD` 之间重复。因此，每当我们连接它们时，所有引理都会在两种变体中触发，即使通常一个引理就已经足够了。为了在不显着降低证明强度的情况下实现这一点，我们引入了两项更改：
  1. 编写或注释一些额外的 `BitVec.getMsbD` 引理以匹配 `BitVec.getLsbD` 的推理能力。最值得注意的是 `getMsbD_eq_getElem`，因此 `getMsbD` 可以尝试自行转换为 `getElem`。
  2. 引入 `grind_pattern getMsbD_eq_getLsbD => x.getMsbD i, x.getLsbD _`，以便每当我们在范围内具有相同值的 `getMsbD` 和 `getLsbD` 时，我们都会尝试将它们匹配。我们预计此注释*通常*不会触发太多，因为大多数 `get*D` 可能可以转换为 `getElem` 并从那里开始工作。

- [#13850](https://github.com/leanprover/lean4/pull/13850)
  删除了每当 `c[i]` 位于电子图中时就会触发 `getElem?_pos` 的研磨注释。我们这样做是为了避免仅仅因为 `c[i]` 可用而对 `c[i]?` 进行推理。只要 `c[i]?` 在范围内，实例化 `getElem?_pos` 的触发器就会保留，以便推动磨削证明或反驳边界检查。

- [#13689](https://github.com/leanprover/lean4/pull/13689)
  使 `whileM` 的展开引理可从 `Lean.Order.MonadTail` 实例导出。公共入口点是`Init.Internal.Order.While`中的`whileM_eq_of_monadTail`； `Init.While` 中的基础固定谓词 `whileM.Pred` 和条件 `whileM_eq` 引理保留在模块内部。

- [#13787](https://github.com/leanprover/lean4/pull/13787)
  修复了 `String.split` 的一个小文档错误。

- [#13748](https://github.com/leanprover/lean4/pull/13748)
  修复了当通过 `induction` 达到目标时，前提选择会默默地丢弃相关前提。

- [#13750](https://github.com/leanprover/lean4/pull/13750)
  细化 MePo 前提选择，以便 (1) 候选对象仅限于定理，匹配 `SineQuaNon` 和 `SymbolFrequency` 已使用的约定，以及 (2) 结果按 `(iteration, score)` 字典顺序排序，而不是单独按分数排序。

- [#13747](https://github.com/leanprover/lean4/pull/13747)
  修复了 MePo 前提选择器返回得分最低的前提，而不是最好的前提。

- [#13457](https://github.com/leanprover/lean4/pull/13457)
  添加了仍然在 `ZipForStd.ByteArray` 下游本地携带的缺少的 `ByteArray` 推送和 `set!` 引理。

- [#13654](https://github.com/leanprover/lean4/pull/13654)
  添加 `Dyadic.divAtPrec a b prec`，返回精度最多为 `prec` 的最大二元，其小于或等于 `a/b`（当 `b = 0` 时，返回 `0`）。镜像现有的 `invAtPrec`，还提供了表征引理 `divAtPrec_mul_le` 和 `lt_divAtPrec_add_inc_mul`。

- [#13718](https://github.com/leanprover/lean4/pull/13718)
  通过消除 Async.sleep 和 IO.sleep 的所有问题并改进 ContextAsync.race 的工作方式，修复了 context_async.lean 中的测试。

- [#13567](https://github.com/leanprover/lean4/pull/13567)
  添加了 Locale 和 LocaleSymbols 以用于可配置的日期/时间格式。它还修改alignedWeekOfMonth 和weekOfYear，因此它包含一周第一天的参数。

- [#13565](https://github.com/leanprover/lean4/pull/13565)
  修复了即使 TZ 和 TZDIR 存在，丢失 /etc/localtime 也会导致失败的问题。

- [#13675](https://github.com/leanprover/lean4/pull/13675)
  添加 `WallTime` 类型，表示自 `1970-01-01T00:00:00` 本地时间以来的纳秒时间点。它还删除了 `sinceUNIXEpoch` 和 `AssumingUTC` 后缀，因为 `Timestamp` 暗示 UTC，而 `WallTime` 暗示它基于 WallTime 纪元（在注释中定义为 `1970-01-01T00:00:00`）。

- [#13693](https://github.com/leanprover/lean4/pull/13693)
  概括了有关 `++` 的许多 `Vector` 引理，以便两个附加向量不再需要共享相同大小的索引：`sum_append`、`prod_append`、它们的 `_nat` / `_int` 变体、`flatMap_append`， `unattach_append`、`eraseIdx_append_of_lt_size` 和 `eraseIdx_append_of_length_le`。

- [#13521](https://github.com/leanprover/lean4/pull/13521)
  防止在没有 `LEAN_MMAP` 的配置上 `readModuleDataParts #[]` 中出现未定义的行为。以前这会导致索引越界。

- [#13549](https://github.com/leanprover/lean4/pull/13549)
  如果没有足够的内存来加载模块，则 `readModuleDataParts` 会报告更清晰的错误。

- [#13627](https://github.com/leanprover/lean4/pull/13627)
  将 `UInt8.ofNatTruncate` 重命名为 `UInt8.ofNatClamp`。

- [#13583](https://github.com/leanprover/lean4/pull/13583)
  将 `Invariant`、`StringInvariant` 和 `StringSliceInvariant` 从 `abbrev` 更改为 `@[spec_invariant_type, simp, grind =] def`，以便它们在证明状态中作为命名常量的应用保持可见（其中 `SymM` 不展开 `def`），并且可以通过以下方式将其检测为不变类型： `isSpecInvariantType`。 `@[simp, grind =]` 注释确保它们仍然在 `simp` 和 `grind` 下按需展开。

- [#13582](https://github.com/leanprover/lean4/pull/13582)
  向 `Std.Do.SPred` 和 `Std.Do.PostCond` 添加了几个与蕴涵相关的引理，旨在用于程序验证证明自动化期间的目标分解。

- [#12965](https://github.com/leanprover/lean4/pull/12965)
  引入了用于推理一元 Lean 代码的新基础。最终我们将在这些新基础之上移植 `mvcgen`，以使框架更加通用和健壮。

- [#13546](https://github.com/leanprover/lean4/pull/13546)
  当使用调用 libuv 的 Lean 函数时，防止内存耗尽变成段错误

- [#13511](https://github.com/leanprover/lean4/pull/13511)
  将 Async 和 Http 从 Internal 移至 Std

- [#12151](https://github.com/leanprover/lean4/pull/12151)
  引入了 Server 模块，一个异步 HTTP/1.1 服务器。

- [#13400](https://github.com/leanprover/lean4/pull/13400)
  将错误名称 `String.Pos.skipWhile_le` 修复为 `String.Pos.le_skipWhile`。

- [#13398](https://github.com/leanprover/lean4/pull/13398)
  从 H1.lean 中删除私有

- [#12146](https://github.com/leanprover/lean4/pull/12146)
  引入了 H1 模块，这是一个纯 HTTP/1.1 状态机，可以增量解析传入的字节流并发出响应字节，而不会产生副作用。

- [#13357](https://github.com/leanprover/lean4/pull/13357)
  基于对 core 中默认容器上的所有只读操作的系统审查。在合理的情况下，它会对缺乏注释的高阶操作应用专门注释，或者在道德上应该借用的参数上借用注释（例如，迭代容器时的容器）。

- [#13200](https://github.com/leanprover/lean4/pull/13200)
  为 `List`、`Array` 和 `Vector` 添加了 `prod`（乘法折叠），镜像现有的 `sum` API。包括基本 simpl 引理 (`prod_nil`、`prod_cons`、`prod_append`、`prod_singleton`、`prod_reverse`、`prod_push`、`prod_eq_foldl`)、Nat 专用引理 (`prod_pos_iff_forall_pos_nat`、 `prod_eq_zero_iff_exists_zero_nat`、`prod_replicate_nat`)、Int 专用引理 (`prod_replicate_int`)、十字型引理 (`prod_toArray`、`prod_toList`) 和带研磨图案的 `Perm.prod_nat`。

- [#13273](https://github.com/leanprover/lean4/pull/13273)
  添加了全面的公共API，用于构建最大程度的共享
  表达应用程序并在 `Sym` 框架中执行 beta 缩减。
  这些函数之前是在 VC 生成器和 cbv 中本地定义的
  策略，并且是基于 `SymM` 的下游工具所需要的。

- [#13155](https://github.com/leanprover/lean4/pull/13155)
  验证 `String.dropWhile` 和 `String.takeWhile` 功能。

- [#13235](https://github.com/leanprover/lean4/pull/13235)
  将 `std::memcmp` 用于 `ByteArray`、`BEq` 和 `DecidableEq`。

- [#13172](https://github.com/leanprover/lean4/pull/13172)
  在 `Std.Internal.UV.System` 中添加借用注释。

```

# 策略
%%%
file := "Tactics"
tag := "zh-releases-v4-31-0-h013"
%%%

```markdown

- [#13859](https://github.com/leanprover/lean4/pull/13859)
  修复了当用户提供的预策略（如 `sym => mvcgen' with (clear h)` 中的 `clear`）重写本地上下文时内核拒绝的问题。

- [#13857](https://github.com/leanprover/lean4/pull/13857)
  实现交互式 `sym =>` 模式的 `dsimp`策略。它还添加了用于声明 `dsimp` 变体的 DSL。

- [#13680](https://github.com/leanprover/lean4/pull/13680)
  使 `mvcgen'` 可用作 `sym => …` 块内的步骤。剩余的 VC 成为后续研磨步骤的子目标； `mvcgen' invariants` 内联工作，`mvcgen' invariants?` 被拒绝。

- [#13854](https://github.com/leanprover/lean4/pull/13854)
  实现声明 `SymM` 的 `dsimp` 变体的语法。

- [#13793](https://github.com/leanprover/lean4/pull/13793)
  通过类型检查错误消息扩展了 `instances` 透明度中有关类型不正确目标的新策略提示，以帮助处理比“不建议的 `unfold`”更复杂的情况。

- [#13636](https://github.com/leanprover/lean4/pull/13636)
  使 `simpa using h` 接近**可缩减**透明度，而不是之前使用的环境（默认/半可缩减）透明度，从而使 `simpa using h` 在 simp 集更改下更具可预测性。先前的行为可用作 `simpa using! h`（在 #13833 中引入）。

- [#13833](https://github.com/leanprover/lean4/pull/13833)
  添加 `simpa ... using! e` 语法作为并行形式
  `simpa ... using e`。目前，`using!` 的行为与 `using` 相同 — 两者
  以环境（默认/半可缩减）透明度关闭目标。

- [#13771](https://github.com/leanprover/lean4/pull/13771)
  添加一个新的 `impossible by t`策略组合器并将其连接到
  默认建议集 `try?`。

- [#13825](https://github.com/leanprover/lean4/pull/13825)
  实现了可重用归约 `DSimproc`（`beta`、`zeta`、`zetaAll`、`dsimpProj`、`dsimpMatch`）的集合，将它们公开为公共，以便调用者可以将它们组合成自己的 `Methods`，并修复了一些错误。

- [#13824](https://github.com/leanprover/lean4/pull/13824)
  在 `Sym.dsimp` 中添加简化活页夹的功能。

- [#13823](https://github.com/leanprover/lean4/pull/13823)
  在 `SymM` 中添加 `dsimp` 的基本基础设施。

- [#13812](https://github.com/leanprover/lean4/pull/13812)
  修复了 `mconstructor`、`mleft` 和 `mright` 在 `mhave` 块内失败的问题 (#13691)，以及 `mspecialize` 在 `mrevert; mintro` 往返后失败的问题。这两种情况都源于假设命名 `Expr.mdata` 从假设连接叶泄漏到非叶位置（内部目标，或 `SPred.imp` 目标的先行词），其中下游模式匹配无法穿透它。

- [#13766](https://github.com/leanprover/lean4/pull/13766)
  移动 `evalSuggest` 组合器和跟踪处理程序调度
  从语法类型上的硬编码 `match` 到现有的
  `tryTacticElabAttribute`的注册机制，带来了`try?`的
  可扩展性模型符合普通策略和交互式`grind`。

- [#13774](https://github.com/leanprover/lean4/pull/13774)
  使 `try?` 的 `expandUserTactic` 遍历 `TryThisInfo` 的信息树
  节点（在 #10524 中引入）而不是解析渲染的 `Try this:` 消息
  文本。之前的方法从
  消息日志，当线路格式改变时，这会中断。

- [#13430](https://github.com/leanprover/lean4/pull/13430)
  使空的 `by` 块在后台运行 `try?` 并显示其建议，同时仍然生成通常的未解决目标诊断。隐式 `try?` 仅提供信息 — 除了发出消息之外，它不会更改精化的行为。行为由新选项 `tactic.tryOnEmptyBy` 控制，目前默认禁用；将其设置为 `true` 以选择加入。默认值可能会在未来版本中翻转。

- [#13699](https://github.com/leanprover/lean4/pull/13699)
  添加了新的 `grind` 配置选项 `genLocal`，用于控制
  局部定理（例如假设）的最大项生成。它默认为
  `8`，与 `gen` 相同的值并且适用于任何时候
  `grind` 实例化一个定理，其起源是局部的而不是声明
  或用户提供的术语。由于用户几乎无法控制所使用的模式
  对于局部定理，更严格的生成界限是合理的默认值。

- [#13698](https://github.com/leanprover/lean4/pull/13698)
  改进了 `grind` 诊断输出，以便使用局部假设
  当电子匹配定理以其面向用户的名称和实例化出现时
  柜台，而不是默默地删除或匿名举报
  `local.<idx>` 标识符。

- [#13644](https://github.com/leanprover/lean4/pull/13644)
  添加了实验性策略`mvcgen'`，它将很快取代 `mvcgen`。它已使用基于 `SymM` 的新框架从头开始重新实现，以进行高效的符号评估，并且对于某些综合基准测试，其性能比 `mvcgen` 高出 100 倍以上。 `mvcgen'` 渴望与 `mvcgen` 一起实现功能完整。目前已知的例外情况包括连接点共享、本地规范的引入和较小的错误。

- [#13678](https://github.com/leanprover/lean4/pull/13678)
  确保可以将鼠标悬停在 fun_induction 中的函数名称上。修复#13673

- [#13665](https://github.com/leanprover/lean4/pull/13665)
  替换 `handleProj` 中的 `Meta.mkCongrArg` 调用点，并且 `simplifyAppFn` 替换为直接 `congrArg` 结构，这些结构重用 `Sym` 指针缓存中已有的类型。同一文件中的一些杂散不合格 `inferType` / `getLevel` / `isDefEq` 调用也会通过缓存的 `Sym` 等效项进行路由。

- [#13640](https://github.com/leanprover/lean4/pull/13640)
  添加每当 `dsimp`（或仅 rfl `simp`）重写触发时发出的跟踪事件
  因为 `[backward_defeq]` 标记定理（即，不会
  已申请但未使用 `set_option backward.defeqAttrib.useBackward true`）。

- [#13635](https://github.com/leanprover/lean4/pull/13635)
  修复了 `Sym.simp` 恐慌（“意外的内核投影项
  在简化过程中”）当匹配器 iota-reduction 时触发
  通过 struct-eta 暴露内核`Expr.proj` 术语。例如，`do`
  具有 `for` 循环的块，其状态是元组，其中 `Sym.simp`
  展开等式引理，然后下降到解构
  比赛。

- [#13624](https://github.com/leanprover/lean4/pull/13624)
  修复了可能导致恐慌的 `grind` 同余表不变违规
  当 `ite` 分支被延迟内化时（在条件变为 `True` 之后）
  或 `False`），并且该分支的等价类后来与另一个合并。

- [#13625](https://github.com/leanprover/lean4/pull/13625)
  修复了当 `cast`（或 `Eq.rec`、`Eq.ndrec`、`Eq.recOn`）应用于尚未内部化的参数时触发的 `grind` 内部错误。 `pushCastHEqs` 在内部化 `e` 的参数之前发出 `e ≍ a`，因此 heq 的 `rhs` 没有 enode，并且调试健全性检查被触发。现在，调用在参数内部化后运行。

- [#13623](https://github.com/leanprover/lean4/pull/13623)
  修复了 `grind` 投影传播器中的证明构造问题。

- [#13622](https://github.com/leanprover/lean4/pull/13622)
  修复了 `grind` AC 不变检查器中的另一个问题。

- [#13614](https://github.com/leanprover/lean4/pull/13614)
  修复了 `grind` AC 中的不变量。待办事项队列中的方程并未完全简化。

- [#13612](https://github.com/leanprover/lean4/pull/13612)
  改进了 `SymM` 使用的宇宙统一器。

- [#13611](https://github.com/leanprover/lean4/pull/13611)
  修复了简化 `have` 表达式时 `Sym.simp` 中的断言失败，该表达式的绑定器类型取决于望远镜中先前的绑定器。

- [#13368](https://github.com/leanprover/lean4/pull/13368)
  添加基础设施以帮助诊断策略与 `unfold` 类似的病例
  仅在 `.default` 透明度下将目标保留为类型正确的状态，
  导致 `rw`/`simp` 在 `.instances` 透明度下失败。

- [#13593](https://github.com/leanprover/lean4/pull/13593)
  禁用 `grind` 的 `NoopConfig` 中基于模型的理论组合 (`mbtc`)，这是派生的策略`lia`、`linarith`、`cutsat`、`order` 使用的基本配置，以及`ring`。如果没有此修复，这些策略可能会通过理论组合进行浪费性推理，导致它们在并非旨在解决的问题上运行很长时间（或达到确定性超时）。通过此修复，这些策略很快就会出现超出范围的问题，正如预期的那样。

- [#13590](https://github.com/leanprover/lean4/pull/13590)
  使 `lia`（和 `grind` 的算术案例分割启发式）识别
  其先行词是算术谓词的 `And` 或 `Or` 的蕴涵如下
  相关的案例分割候选人。此前，`Arith.isRelevantPred` 仅匹配
  `Not`、`LE`、`LT`、`Eq` 和 `Dvd`。使用 `splitImp := false`（默认），
  仅当 `p` 为
  与算术相关，因此像 `(b ≤ e ∧ e < b + c → a ≤ e ∧ e < a + d)` 这样的假设
  从未登记为候选人。 cutsat/lia 然后会找到令人满意的
  分配给它已经被告知的约束，但是那个分配
  不一定满足最初的含义，产生不好的结果
  #13575 中报告了反例。

- [#13585](https://github.com/leanprover/lean4/pull/13585)
  添加了 `ringMaxDegree` 配置选项（默认 `1024`），该选项限制 `grind` 环求解器处理的多项式的最大次数。多项式超过此阈值的等式约束将被丢弃（每个目标报告一次问题），从而防止 `r ^ (2 ^ 250 - 1)` 等输入的病理程度爆炸。

- [#13558](https://github.com/leanprover/lean4/pull/13558)
  添加选项 `grind.ematch.diagnostics`，该选项跟踪 E 匹配定理实例如何相互依赖。启用后，`grind` 会为每个新定理实例记录其生成的项参与匹配的先前实例的集合。这会生成一个描述每个实例化来源的超图 `{thm_1, ..., thm_n} => thm`。

- [#13560](https://github.com/leanprover/lean4/pull/13560)
  修复了 `propagateBetaEqs` 中的错误（在 `Lean.Meta.Tactic.Grind.Beta` 中）
  其中通过贝塔减少引入的新等式/项被添加到目标中
  不检查生成阈值。新事实的产生
  是 lambda 的最大生成，函数 `f` 及其
  参数，加一。如果没有阈值检查，β 减少可以
  在自相似的 lambda 上无限级联，例如
  `(fun b => f (b + 1)) = fun b => f b`，持续生产
  `f n = f (n + 1)` 适用于每个 `n`。该修复聚合了参数生成
  在阈值检查之前并在生成的生成时退出
  达到`maxGeneration`。

- [#13301](https://github.com/leanprover/lean4/pull/13301)
  添加了直接在给定策略上运行 `evalSuggest` 的 `try? => tac` 语法，对于单独测试 `try?` 机器很有用。它还添加了一个 server_interactive 测试 (`cancellation_par.lean`)，该测试演示了并行策略组合器的取消错误。

- [#13532](https://github.com/leanprover/lean4/pull/13532)
  即使 `lhs = rhs` 未内化在 E 图中（现有的优化），也会通知卫星求解器有关断言的等式 `lhs = rhs`。该通知允许不检查等价类（例如同态扩展）的求解器直接对断言的等式做出反应。它在等价类合并之前触发，以便将 `lhs` 和 `rhs` 标记为其内部术语的求解器在 `Solvers.mergeTerms` 触发 `processNewEq` 之前注册它们。

- [#13476](https://github.com/leanprover/lean4/pull/13476)
  优化了 `apply`策略（以及相关的策略，如 `rewrite`）命名和标记其余子目标的方式。现在*在*计算子目标标签之前过滤掉指定的元变量。因此，当只剩下一个未分配的子目标时，它会继承输入目标的标签，而不是被赋予新的后缀标签。

- [#13474](https://github.com/leanprover/lean4/pull/13474)
  修复了 `sym =>` 交互模式中的一个错误，其中元变量由 `isDefEq` 分配的目标（例如通过 `apply Eq.refl`）未被修剪。 `pruneSolvedGoals` 之前仅过滤掉标记为不一致的目标，因此已分配的目标将作为未解决的目标保留下来。现在，它还删除已分配元变量的目标。

- [#13472](https://github.com/leanprover/lean4/pull/13472)
  修复了 `sym =>` 交互模式中的错误，其中卫星解算器（`lia`、`ring`、`linarith`）如果其自动 `intros + assertAll` 预处理步骤已关闭目标，则会引发内部错误。此前，`evalCheck` 使用 `liftAction` 丢弃了闭包结果，因此后续的 `liftGoalM` 调用因缺乏主要目标而失败。 `liftAction` 现在已拆分，因此调用者可以区分关闭和子目标情况，并在预处理已完成工作时跳过求解器主体。

- [#13453](https://github.com/leanprover/lean4/pull/13453)
  修复了将 `Nat` 等式传播到承运人类型不是 `Int` 的订单结构（例如 `Rat`）时 `grind` 中的内核错误。辅助 `Lean.Grind.Order.of_nat_eq` 引理专用于 `Int`，因此当转换目标不同时，内核拒绝该申请。

- [#13451](https://github.com/leanprover/lean4/pull/13451)
  修复了 `Sym.introCore.finalize` 中的一个错误，其中原始元变量通过延迟分配无条件分配，即使没有引入绑定器也是如此。因此，`Sym.intros` 将返回 `.failed`，而目标元变量已被静默分配，从而混淆依赖于 `isAssigned` 的下游代码（例如 `mvcgen'` 中的 VC 过滤器）。

- [#13448](https://github.com/leanprover/lean4/pull/13448)
  修复了 `Sym.simp` 中的回归问题，其中 LHS 包含模式变量上的 lambda 的重写规则（例如 `∃ x, a = x`）无法匹配具有语义等效结构的目标。

- [#13088](https://github.com/leanprover/lean4/pull/13088)
  将 `PowIdentity` 类型类（来自 https://github.com/leanprover/lean4/pull/13086）连接到 `grind` 环求解器的 Groebner 基础引擎中。

- [#13086](https://github.com/leanprover/lean4/pull/13086)
  添加了 `Lean.Grind.PowIdentity` 类型类，声明 `x ^ p = x` 用于交换半环的所有元素，其中 `p` 作为 `outParam`。

- [#13289](https://github.com/leanprover/lean4/pull/13289)
  在 `Sym.Arith/` 中添加用于算术标准化的共享基础设施，
  为 `Sym.simp` 的 arith pre-simproc 和最终的 arith 奠定基础
  统一grind的`CommRing`模块。

- [#13272](https://github.com/leanprover/lean4/pull/13272)
  扩展 sym 标准化器以应用缩减（投影、匹配/ite/cond、Nat
  算术）在所有位置，而不仅仅是内部类型。以前，值 `v` 出现在
  当 `T(v)` 被归一化时，类型 `T(v)` 可以保持不变，从而打破了以下不变式：
  定义上相等的类型在规范化后结构上是相同的。

- [#13271](https://github.com/leanprover/lean4/pull/13271)
  重构 sym 规范化器中的实例规范化以正确处理
  \`Grind.nestedProof\` 和 \`Grind.nestedDecidable\` 标记。之前，规范化器
  当它无法重新合成命题实例时，会报告问题
  由 \`grind\` 本身提供或由用户通过 \`haveI\` 提供。现在，重新合成优雅地失败
  在值位置上回退到原始实例，同时保持严格的内部类型。

- [#13202](https://github.com/leanprover/lean4/pull/13202)
  修复了文件末尾环境扩展的心跳超时问题，该超时问题无法通过提高限制来避免。

```

# 编译器
%%%
file := "Compiler"
tag := "zh-releases-v4-31-0-h014"
%%%

```markdown

- [#13796](https://github.com/leanprover/lean4/pull/13796)
  优化 `String.compare` 将其变成 1 个而不是 2 个 `memcmp` 调用。

- [#13788](https://github.com/leanprover/lean4/pull/13788)
  生成用于对形状已知的值调用 `dec` 的专用代码。这减轻了 `lean_dec_ref_cold` 的分支预测压力，因为构造函数的形状现在应该编译到可执行文件中。

- [#13669](https://github.com/leanprover/lean4/pull/13669)
  通过概述“冰冷”路径并执行小型微架构优化来优化 `lean_dec_ref_cold`。后者更好，因为它向 LLVM 明确表示我们相信指针仅使用 48 位。

- [#13545](https://github.com/leanprover/lean4/pull/13545)
  将 LLVM 从版本 19 升级到版本 22。这带来了高达 5% 指令的总体性能提升，具体取决于基准测试。

- [#13493](https://github.com/leanprover/lean4/pull/13493)
  确保 `import` 正常处理文件系统中的 `EINTR` 错误。

- [#13464](https://github.com/leanprover/lean4/pull/13464)
  在 `lean_io_process_spawn` 的分叉子分支（`chdir` 故障和 `execvp` 故障路径）中将 `exit(-1)` 替换为 `_exit(-1)`。 `exit` 刷新继承的 C stdio 缓冲区，该缓冲区与父级共享底层文件描述符。如果父级打开了一个包含未刷新数据的文件句柄，则该数据将被写入子级中的文件，然后在父级稍后刷新时再次写入，从而导致重复输出。 `_exit` 跳过 stdio 刷新，因此父级的缓冲写入不再复制到继承的文件中。

- [#13435](https://github.com/leanprover/lean4/pull/13435)
  修复了 EmitC 中的一个错误，该错误可能是由于使用字符串文字 `"\x01abc"` 引起的
  Lean 并导致 C 编译器错误。

- [#13427](https://github.com/leanprover/lean4/pull/13427)
  修复了 `io.cpp` 中的两个小错误：
  1. `Std.Time.Database.Windows.getNextTransition` 的 Windows 错误路径中的资源泄漏
  2. 当可执行文件是最大路径长度的符号链接时，Linux 上的 `IO.appPath` 中会出现缓冲区溢出。

- [#13421](https://github.com/leanprover/lean4/pull/13421)
  修复了扩展重置重用过程中的一个问题，该问题在极少数情况下会导致段错误。

- [#13409](https://github.com/leanprover/lean4/pull/13409)
   将 qsort 正确地专门化到 lt 函数上

- [#13401](https://github.com/leanprover/lean4/pull/13401)
  将选项 `LEAN_MI_SECURE` 添加到我们的 CMake 构建中。可以配置值 `0`
  通过 `4`。每个增量都可以在 mimalloc 中实现额外的内存安全缓解，但代价是
  2%-20% 的指令数，具体取决于基准测试。我们的系统中默认禁用该选项
  发布版本是因为我们的大多数用户在安全敏感情况下不会使用 Lean 运行时。
  部署生产 Lean 代码的分销商和组织应考虑启用该选项：
  一项强化措施。各个级别的效果可以在https://github.com/microsoft/mimalloc/blob/v2.2.7/include/mimalloc/types.h#L56-L60.中找到

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  修复了 `lean_io_prim_handle_read` 中的堆缓冲区溢出问题，该溢出问题是通过
  分配大小计算中的整数溢出。此外，它还放置了几个检查的
  对所有相关分配路径进行算术运算，以消除未来潜在的溢出
  相反，会导致崩溃。现在，有问题的代码会抛出内存不足错误。

- [#13384](https://github.com/leanprover/lean4/pull/13384)
  修复了当结构构造函数接收不可计算实例作为实例隐式参数时出现的编译器恐慌。

- [#13234](https://github.com/leanprover/lean4/pull/13234)
  修复了 Lean 未与 libuv 链接时的构建问题。

- [#13233](https://github.com/leanprover/lean4/pull/13233)
  修复了未设置 `LEAN_MULTI_THREAD` 时的运行时构建问题。

- [#13270](https://github.com/leanprover/lean4/pull/13270)
  添加了 `Runtime.hold`，这通过保存对它的引用来确保其参数在调用站点之前保持活动状态。这对于依赖于直到程序中某个点之后才释放的 Lean 对象的不安全代码（例如 FFI）非常有用。

- [#13258](https://github.com/leanprover/lean4/pull/13258)
  在缓存未命中时在 `checkInferTypeCache` 中添加 `Core.checkInterrupted` 调用，从而允许在大型类型推理遍历期间检测取消。以前，在处理大型表达式（例如 BVDecide 证明项）时，`inferTypeImp` 可以运行 >100 毫秒，而不会进行任何中断检查，从而导致 IDE 取消无响应。

- [#13242](https://github.com/leanprover/lean4/pull/13242)
  修复了 `String` 构造函数上模式匹配的编译器处理，以符合新的 `String` 表示形式。

- [#13128](https://github.com/leanprover/lean4/pull/13128)
  通过使用 `CMAKE_RELATIVE_LIBRARY_OUTPUT_DIRECTORY` 而不是 Lake 插件的硬编码 `lib/lean` 路径来修复 Windows 开发版本。在 Windows 上，DLL 必须放置在 `bin/` 中的可执行文件旁边，但插件路径被硬编码到 `lib/lean`，导致无法找到 stage0 DLL。

```

# 漂亮的印刷
%%%
file := "Pretty-Printing"
tag := "zh-releases-v4-31-0-h015"
%%%

```markdown

- [#13761](https://github.com/leanprover/lean4/pull/13761)
  修复了 `pp.universes` 选项会导致没有 Universe 的常量不使用解展开器或点表示法的问题。例如，`p ↔ q` 会漂亮地打印为 `Iff p q`，即使 `Iff` 没有 宇宙层级。

- [#13446](https://github.com/leanprover/lean4/pull/13446)
  改进了元变量的漂亮打印及其在 InfoView 中的悬停。 InfoView 中的悬停现在包括有关特定元变量的信息 - 它包括诸如元变量的类型、是否是阻止的延迟赋值以及它被阻止的元变量以及元变量的本地上下文中存在哪些变量的差异等信息。此外，如果命名元变量无法访问，现在可以用墓碑漂亮地打印它们。延迟赋值漂亮的打印现在可以更可靠地遵循赋值链来查找待处理的元变量。

- [#13438](https://github.com/leanprover/lean4/pull/13438)
  当 `pp.instantiateMVars` 为 true 时，使 宇宙层级 漂亮的打印机实例化级别元变量。

- [#13030](https://github.com/leanprover/lean4/pull/13030)
  改进了级别元变量的漂亮打印：它们现在使用每个定义的索引而不是每个模块的内部标识符进行打印。此外，`+`与周围空间统一打印在水平表达式中。 **重大元编程更改：** 级别漂亮打印应使用 `delabLevel` 或 `MessageData.ofLevel`； `format` 或 `toString` 等函数无法访问索引，因为它们存储在当前元上下文中。如果没有索引信息，元变量将使用原始内部标识符 `?_mvar.nnn` 进行打印。 **注意：** 由于记录级别元变量索引的分配计数，心跳计数器也会增加得更快。在某些测试中，我们需要将 `maxHeartbeats` 增加 20-50% 进行补偿，但不会出现相应的减速。

```

# 文档
%%%
file := "Documentation"
tag := "zh-releases-v4-31-0-h016"
%%%

```markdown

- [#13864](https://github.com/leanprover/lean4/pull/13864)
  更新管道运算符文档字符串以提高准确性和实用性。此类运算符不是 Haskell 惯用的，因此旧文本是不正确的，并且最好解释一下该行为，而不是引用其他语言。

- [#13656](https://github.com/leanprover/lean4/pull/13656)
  记录如何执行 LLVM 升级。

```

# 服务器
%%%
file := "Server"
tag := "zh-releases-v4-31-0-h017"
%%%

```markdown

- [#13525](https://github.com/leanprover/lean4/pull/13525)
  为 `Unit` 添加 `FromJson`/`ToJson` 实例 - 编码为 `{}` - and documentation for `FromJson`/`ToJson`。

- [#13260](https://github.com/leanprover/lean4/pull/13260)
  通过 `PublishDiagnosticsParams` 上的新 `isIncremental` 字段添加了服务器端对增量诊断的支持，该字段仅在客户端在 `LeanClientCapabilities` 中设置 `incrementalDiagnosticSupport` 时由语言服务器使用。

- [#13348](https://github.com/leanprover/lean4/pull/13348)
  修复了策略自动完成会在空策略块的整个尾随空白中生成策略完成项的错误。由于 #13229 进一步限制顶级 `by` 块对缩进敏感，因此此 PR 调整逻辑以仅在“适当”缩进级别显示完成项。

- [#13257](https://github.com/leanprover/lean4/pull/13257)
  在空 `by` 块中添加测试基础设施和策略完成测试。

```

# Lake
%%%
file := "Lake"
tag := "zh-releases-v4-31-0-h018"
%%%

```markdown

- [#13949](https://github.com/leanprover/lean4/pull/13949)
  添加一个 `LAKE_RESTORE_ARTIFACTS` 环境变量，该变量覆盖工作区的默认 `restoreAllArtifacts` 配置，镜像 `LAKE_ARTIFACT_CACHE` 覆盖 `enableArtifactCache` 的方式。

- [#13936](https://github.com/leanprover/lean4/pull/13936)
  修复了未正确设置 `depPkgs` 的传递依赖关系的问题，该传递依赖关系被依赖关系图中更高级别的包覆盖。

- [#13843](https://github.com/leanprover/lean4/pull/13843)
  使 `lake lint --builtin-lint` 导入模块系统目标处于公共 (`OLeanLevel.exported`) 级别，而不是 `private`。环境检查现在会在此类模块的公共表面上进行检查，以匹配下游消费者对它们的看法。非模块目标保留其先前的行为（`private` 级别），并且通过 `lintLogExt` 记录的文本检查警告在级别更改期间保留，因为该扩展存储统一的 OLean 条目。

- [#13563](https://github.com/leanprover/lean4/pull/13563)
  公开 `Glob.ofString?`，允许从 Mathlib 中删除最后一次使用的 `open private`。

- [#13683](https://github.com/leanprover/lean4/pull/13683)
  将已编译的 Lake 配置（例如 `lakefile.olean`）从包的 `.lake/config` 目录移动到工作区的 `.lake/config`。这消除了共享依赖项的工作区之间潜在的源争用。

- [#13601](https://github.com/leanprover/lean4/pull/13601)
  更改 Lake 的模块导入图处理以等待任何 `needs` 目标或其他额外依赖项（例如云发布）的完成。这既使 `needs` 目标能够影响标头处理，又防止它们与所述处理竞争。

- [#13600](https://github.com/leanprover/lean4/pull/13600)
  修复了 Lake 问题，其中 `meta import` 的传递导入的 IR 未包含在提供给 Lean 的导入工件 Lake 中（例如，通过 `--setup`）。使用 Lake 工件缓存时，可能会由于缺少 IR 而产生“丢失数据文件”错误。

- [#13559](https://github.com/leanprover/lean4/pull/13559)
  修复了 Lake 构建监视器排空作业队列中的竞争条件。

- [#13513](https://github.com/leanprover/lean4/pull/13513)
  除了 #13431 中添加的环境 linters 之外，还扩展了 `lake lint --builtin-lint` 以支持文本 linters（即使用 `logLint`/`logLintIf` 的文本 linters）。构建期间发出的 Text-linter 警告通过新的 `Lean.Linter.lintLogExt` 环境扩展保留到每个模块的 `.olean` 中； `lake lint` 重新运行目标模块的构建并读回条目，将它们与环境 linter 输出一起报告。

- [#13516](https://github.com/leanprover/lean4/pull/13516)
  将 `namespace Lake` 添加到缺少的 `Lake.Util.Opaque` 中。从技术上讲，对于任何使用 `Opaque` 而不使用 `open Lake` 的代码来说，这是一个重大更改，但希望没有人这样做。

- [#13500](https://github.com/leanprover/lean4/pull/13500)
  添加了对空 `lake build` 调用的检查（因为空构建通常表示配置错误）。没有作业的构建现在将打印“Nothing to build”。并且在未配置默认目标的情况下调用 `lake build` 将产生警告。这将在未来升级为错误。可以使用新的 `--allow-empty` CLI 选项来抑制警告（以及未来的错误）。

- [#13431](https://github.com/leanprover/lean4/pull/13431)
  向 Lake 添加内置环境 linting 支持，可通过 `lake lint` 标志访问。它还引入了两个来自 Mathlib 上游的内置 linter（`defLemma` 和 `checkUnivs`）和 `builtinLint` 封装配置选项。

- [#13456](https://github.com/leanprover/lean4/pull/13456)
  向 Lake 添加类型缩写 `GitRev`，用于表示 Git 修订的 `String` 值。此类修订可能是 SHA1 提交哈希、分支名称或 Git 更复杂的说明符之一。

- [#13423](https://github.com/leanprover/lean4/pull/13423)
  添加了 `JobAction.reuse` 和 `JobAction.unpack`，它们为构建监视器的作业正在执行的操作提供更多信息标题。当使用 Lake 缓存中的工件时设置 `reuse`，当解压模块 `.ltar` 存档并发布（Reservoir 或 GitHub）存档时设置 `unpack`。

- [#13393](https://github.com/leanprover/lean4/pull/13393)
  添加了对 `lake builtin-lint` 命令的基本支持，该命令用于运行环境 linter，并且将来将扩展以处理核心语法 linter。

- [#13340](https://github.com/leanprover/lean4/pull/13340)
  修复了 Lake 问题，其中库构建不会产生有关错误导入的信息性错误（与模块构建不同）。

- [#13282](https://github.com/leanprover/lean4/pull/13282)
  引入了 `LakefileConfig`，它可以从 Lake 配置文件构建，而无需构建完整 `Package` 所需的所有信息。此外，工作区现在附加了格式良好的属性，可确保其包的工作区索引与其在工作区中的索引相匹配。最后，构面配置图现在拥有自己的类型：`FacetConfigMap`。

- [#13277](https://github.com/leanprover/lean4/pull/13277)
  修复了函数名称中面向公众的拼写错误：`Module.checkArtifactsExsist` -> `Module.checkArtifactsExist`。

```

# 其他
%%%
file := "Other"
tag := "zh-releases-v4-31-0-h019"
%%%

```markdown

- [#13185](https://github.com/leanprover/lean4/pull/13185)
  添加了新的增量模块序列化功能，可一次保存/加载单个模块，并通过 dep 区域和压缩器状态显式共享，概括现有的批量 saveModuleDataParts API。

- [#13740](https://github.com/leanprover/lean4/pull/13740)
  扩展了 `lake shake --explain`，还涵盖了保留超出直接引用范围的导入的原因，例如抖动注释。

- [#13530](https://github.com/leanprover/lean4/pull/13530)
  添加了一个 `trace.profiler.serve` 选项，启用该选项后，将在临时 `127.0.0.1` 端口上提供与 Firefox Profiler 兼容的配置文件 JSON，并在用户的默认浏览器中打开 `https://profiler.firefox.com/from-url/...`，类似于 `samply`。获取配置文件后，服​​务器将关闭。

- [#13630](https://github.com/leanprover/lean4/pull/13630)
  修复了在 `public section` 下在模块模式下启用 `set_option diagnostics true` 时出现的“未知常量”错误。诊断输出可能会引用记录在展开计数器中的私有声明，例如 `_match_*` 和 `_sparseCasesOn_*`；之前构建消息失败，因为环境处于导出模式并且无法解析这些名称。 `Lean.Meta.Diagnostics.reportDiag` 和 `Lean.Meta.Tactic.Simp.Diagnostics.reportDiag` 中的诊断打印路径现在在 `withoutExporting` 下运行。

- [#13589](https://github.com/leanprover/lean4/pull/13589)
  确保 `lean --error=tag` 标志实际上在升级错误时设置非零退出代码。

- [#13553](https://github.com/leanprover/lean4/pull/13553)
  修复了未启用初始化程序执行时 `runInitAttrs` 引发的错误消息中的拼写错误。该消息之前提到的是`enableInitializerExecution`（单数），但实际功能是`enableInitializersExecution`（复数）。

- [#13520](https://github.com/leanprover/lean4/pull/13520)
  使用要应用原子的谓词扩展 `grind` 同态演示。

- [#13499](https://github.com/leanprover/lean4/pull/13499)
  修复了 Linux aarch64 上 `leantar` 的架构检测，确保其与 Lean 正确捆绑。

- [#13497](https://github.com/leanprover/lean4/pull/13497)
  添加了巴黎 Lean 黑客马拉松的示例。它演示了用户如何实施 https://hackmd.io/Qd0nkWdzQImVe7TDGSAGbA

- [#13132](https://github.com/leanprover/lean4/pull/13132)
  添加 `linter.redundantVisibility` 选项（默认 `true`）来发出警告
  当可见性修饰符无效时，因为它与默认值匹配
  当前上下文：

  - `private` 在 `module` 文件中的 `public section` 之外，其中声明
    默认情况下已经在模块范围内
  - `public` 在非 `module` 文件中或 `public section` 内部，其中
    默认情况下声明已经公开

- [#13211](https://github.com/leanprover/lean4/pull/13211)
  添加了 `unlock_limits` 命令，该命令将 `maxHeartbeats`、`maxRecDepth` 和 `synthInstance.maxHeartbeats` 设置为 0，从而禁用所有核心资源限制。还使 `maxRecDepth 0` 表示“无限制”（与 `maxHeartbeats 0` 的现有行为匹配）。

- [#13226](https://github.com/leanprover/lean4/pull/13226)
  更新 `release_checklist.py` 以处理 CMake 版本变量上的 `CACHE STRING ""` 后缀。 `CACHE STRING` 格式是在 `releases/v4.30.0` 分支中引入的，但脚本的解析未更新以匹配，从而导致错误失败。

```
