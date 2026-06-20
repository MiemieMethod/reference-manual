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

#doc (Manual) "Lean 4.30.0 (2026-05-26)" =>
%%%
tag := "release-v4.30.0"
file := "v4.30.0"
%%%

此版本共进行了 306 项更改。
除了新增的 123 项功能外，
以及下面列出的 73 个修复，
有 17 处重构更改，
8 项文档改进，
19 项性能改进，
对测试套件进行 12 项改进，
以及 54 个其他变化。

# 亮点
%%%
tag := "zh-releases-v4-30-0-h001"
%%%

Lean 4.30.0 带来了新的交互式 `sym =>`策略、显着扩展的 `cbv`策略、完成了具有用户可控借用注释的新 LCNF 编译器后端，并对 Lake 的缓存基础设施进行了重大检修。

_此亮点部分由 Juanjo Madrigal 贡献。_

## 全新 `sym =>` 互动策略
%%%
tag := "zh-releases-v4-30-0-h002"
%%%

[#12970](https://github.com/leanprover/lean4/pull/12970) 添加了 `sym =>`，这是一种基于 {tactic}`grind` 构建的新交互式策略模式。与 `grind =>` 急切地引入假设并应用反证法不同，`sym =>` 为用户提供了对每个步骤的明确控制。因此，用户可以使用 `grind` 提供的所有基础设施，但采用自定义策略：

```lean  (name := sym)
example (f : Nat → Nat) (a b : Nat)
    (hinj : ∀ x y, f x = f y → x = y) (h : f a = f b) : a = b := by
  sym => instantiate ; show_eqcs ; finish
```
```leanOutput sym
[eqc] Equivalence classes
  [eqc] {a, b}
  [eqc] {f a, f b}
```

可用的策略包括 `intro`/`intros`、`apply`、`internalize`、`by_contra` 和 `simp`。像 `lia` 和 `ring` 这样的求解器会自动引入剩余的绑定器并根据需要应用矛盾。

相关开发可以在 PR 中找到： [#12996](https://github.com/leanprover/lean4/pull/12996) / [#13018](https://github.com/leanprover/lean4/pull/13018) / [#13034](https://github.com/leanprover/lean4/pull/13034) / [#13039](https://github.com/leanprover/lean4/pull/13039) / [#13040](https://github.com/leanprover/lean4/pull/13040) / [#13041](https://github.com/leanprover/lean4/pull/13041) / [#13042](https://github.com/leanprover/lean4/pull/13042) / [#13046](https://github.com/leanprover/lean4/pull/13046) / [#13048](https://github.com/leanprover/lean4/pull/13048) / [#13080](https://github.com/leanprover/lean4/pull/13080)。

## `cbv`策略扩展
%%%
tag := "zh-releases-v4-30-0-h003"
%%%

v4.29.0 中引入的 {tactic}`cbv`策略不再是实验性的，并在此版本中获得主要的新功能。

{tactic}`cbv` 执行类似于按值调用评估的过程，以简化或关闭目标。

```lean
def fact : Nat → Nat
| 0 => 1
| n+1 => (n+1) * fact n

def pow2 : Nat → Nat
| 0 => 1
| n+1 => 2 * pow2 n

-- `simp` requires providing functions
example : fact 5 < pow2 7 := by simp [fact, pow2]
-- `cbv` just executes directly
example : fact 5 < pow2 7 := by cbv
```

v4.30.0 引入了以下改进：

- [#12597](https://github.com/leanprover/lean4/pull/12597)：`cbv_simproc` 系统镜像 {tactic}`simp` 的 `simproc` 基础设施。

- [#12773](https://github.com/leanprover/lean4/pull/12773)：`at` 位置语法（`cbv at h`、`cbv at h |-` 和 `cbv at *`）。

- [#12788](https://github.com/leanprover/lean4/pull/12788)：`set_option cbv.maxSteps N` 用于用户可配置的步数限制。

- [#12763](https://github.com/leanprover/lean4/pull/12763)：`Or`/`And` 的短路评估：对于 `decide (m < n ∨ expensive)` 等表达式

- 其他改进：[#12851](https://github.com/leanprover/lean4/pull/12851) / [#12944](https://github.com/leanprover/lean4/pull/12944) / [#12875](https://github.com/leanprover/lean4/pull/12875) / [#12888](https://github.com/leanprover/lean4/pull/12888)。

## 编译器：用户借用注释和新的 LCNF 后端
%%%
tag := "zh-releases-v4-30-0-h004"
%%%

### 用户借用注释
%%%
tag := "zh-releases-v4-30-0-h005"
%%%

[#12830](https://github.com/leanprover/lean4/pull/12830) 启用对用户提供的借用注释的支持。 Users can now mark function arguments with `(x : @&Ty)` and have the borrow inference preserve these annotations, reducing引用计数pressure:

```
def process (ctx : @& Context) (data : Array Nat) : Result :=
  ...  -- `ctx` will not be reference counted
```

编译器优先考虑保留尾部调用而不是借用注释。使用 `trace.Compiler.inferBorrow` 查看编译器推理决策的详细推理。 [#12810](https://github.com/leanprover/lean4/pull/12810) 添加了此跟踪基础设施。

[#12942](https://github.com/leanprover/lean4/pull/12942) 将 {lean}`ReaderT` 的上下文参数标记为借用 (`(a : @&ρ) → m α`)，从而导致整个元编程堆栈中的 RC 压力广泛减少。

### 新 LCNF 后端完成
%%%
tag := "zh-releases-v4-30-0-h006"
%%%

[#12781](https://github.com/leanprover/lean4/pull/12781) 将 C 发射通道从 IR 移植到 LCNF，标志着 IR/LCNF 转换的最后一步，并通过新的编译基础设施实现端到端代码生成。

[#12665](https://github.com/leanprover/lean4/pull/12665) 将扩展重置/重用传递移植到 LCNF，并改进了指数级代码膨胀的预防，从而使二进制大小减少约 15%，并带来全面的小幅加速。

### 其他编译器改进
%%%
tag := "zh-releases-v4-30-0-h007"
%%%

- [#12971](https://github.com/leanprover/lean4/pull/12971) 将 Lean 的默认堆栈大小增加到 1GB（页面是动态分配的，因此不会增加内存使用量）。堆栈大小可以通过 `LEAN_STACK_SIZE_KB` 自定义。
- [#12539](https://github.com/leanprover/lean4/pull/12539) 用 `Lean.Compiler.NameDemangling` 中的单一事实来源替换了三个独立的名称重组实现（Lean、C++、Python），删除了约 1,400 行重复代码。
- [#12724](https://github.com/leanprover/lean4/pull/12724)、[#12727](https://github.com/leanprover/lean4/pull/12727) 将地面数组和装箱标量文字提取到静态初始化数据中。

## Lake 缓存检修
%%%
tag := "zh-releases-v4-30-0-h008"
%%%

此版本对 Lake 的缓存基础设施进行了全面检修：

- [#12634](https://github.com/leanprover/lean4/pull/12634)：使 Lake 能够按需从远程缓存服务下载工件，作为 `lake build` 的一部分。

- [#12927](https://github.com/leanprover/lean4/pull/12927)：`lake cache get` 更改为默认下载工件。可以使用新的 `--mappings-only` 选项按需下载工件。

- [#12974](https://github.com/leanprover/lean4/pull/12974)：使用 `curl --parallel` 进行上传和下载并行工件传输。

- [#13164](https://github.com/leanprover/lean4/pull/13164)：通过在单个批量 POST 请求中从 Reservoir 获取所有工件 URL（而不是每个工件重定向）来进行下载优化。

- [#12914](https://github.com/leanprover/lean4/pull/12914)：通过 `leantar` 进行 `.ltar` 存档打包/解包。

- [#13144](https://github.com/leanprover/lean4/pull/13144)：用于分阶段缓存上传的新 `lake cache` 子命令：`stage`、`unstage` 和 `put-staged`，与 Mathlib 中的同名命令并行运行`lake exe cache`。

- [#12935](https://github.com/leanprover/lean4/pull/12935)：新的 `fixedToolchain` 选项适用于仅在单个工具链上运行的软件包（如 Mathlib）。

## 其他语言改进
%%%
tag := "zh-releases-v4-30-0-h009"
%%%

- [#13011](https://github.com/leanprover/lean4/pull/13011) 添加了 `@[deprecated_arg]`，这是一个用于弃用单个函数参数的新属性。当调用者使用旧参数名称时，精化器会发出带有代码操作提示的弃用警告。
- [#12756](https://github.com/leanprover/lean4/pull/12756) 添加了 `deriving noncomputable instance Foo for Bar` 语法，以便可以将增量派生实例标记为不可计算。
- [#13117](https://github.com/leanprover/lean4/pull/13117) 通过在 olean 序列化时计算公理依赖关系，在模块系统下重新启用 `#print axioms`。
- [#12866](https://github.com/leanprover/lean4/pull/12866) 向 `doPatDecl` 解析器添加了 `optType` 支持，允许使用 do 表示法中的 `let ⟨width, height⟩ : Nat × Nat ← action`。
- [#12325](https://github.com/leanprover/lean4/pull/12325) 在类类型的 `def` 未声明适当的可归约性（例如 `@[reducible]` 或 `@[implicit_reducible]`）时添加警告。
- [#12233](https://github.com/leanprover/lean4/pull/12233) 将 `instantiateMVars` 替换为两遍实现，将二次复杂度从延迟分配元变量的长链降低为线性。

## 图书馆亮点
%%%
tag := "zh-releases-v4-30-0-h010"
%%%

### HTTP 库
%%%
tag := "zh-releases-v4-30-0-h011"
%%%

[#12126](https://github.com/leanprover/lean4/pull/12126)、[#12127](https://github.com/leanprover/lean4/pull/12127)、[#12128](https://github.com/leanprover/lean4/pull/12128) 和 [#12144](https://github.com/leanprover/lean4/pull/12144) 介绍核心 HTTP 数据类型：`Request`、 `Response`、`Status`、`Version`、`Method`、`Headers`、`URI` 和流式 `Body`。这是 Lean 中标准 HTTP 库的基础。

### 其他库添加
%%%
tag := "zh-releases-v4-30-0-h012"
%%%

- 字符串验证从 v4.29.0 开始继续进行，并提供 `startsWith`、`skipPrefix?`、`dropPrefix?`、`endsWith`、`dropSuffix?`、`split`、`intercalate`、`isNat` 的证明， `toNat?`、`isInt`、`toInt?`、`drop`、`take` 等。
- [#12852](https://github.com/leanprover/lean4/pull/12852) 添加 `PersistentHashMap` 迭代器，[#12844](https://github.com/leanprover/lean4/pull/12844) 添加 `append` 组合器用于迭代器串联。
- [#12385](https://github.com/leanprover/lean4/pull/12385) 添加了 `Array.mergeSort`，这是一种稳定的 O(n log n) 最坏情况排序，对于大型随机数组，测量速度大约是 `List.mergeSort` 的两倍。
- [#12430](https://github.com/leanprover/lean4/pull/12430) 提供 `WellFounded.partialExtrinsicFix` 用于实现和验证部分终止功能。
- [#12702](https://github.com/leanprover/lean4/pull/12702) 来自 Batteries/Mathlib 的 `List.splitOn` 和 `List.splitOnP` 上游。
- [#12433](https://github.com/leanprover/lean4/pull/12433) 为 `BitVec.cpop` 添加高效的并行前缀和位爆破电路。

## 实验：使用 `idbg` 进行实时调试
%%%
tag := "zh-releases-v4-30-0-h013"
%%%

[#12648](https://github.com/leanprover/lean4/pull/12648) 添加了实验性 `idbg e` 语法，用于语言服务器和正在运行的编译的 Lean 程序之间的实时调试。当放置在 `do` 块中时，`idbg` 捕获范围和表达式 `e` 中的局部变量，然后通过 TCP 将正在运行的程序连接到语言服务器，以使用实际运行时值计算 `e`。可以在程序运行时编辑表达式 - 每次编辑都会触发重新评估，并将更新的结果显示为信息诊断。这是实验性的，具有已知的局限性（一次单个 `idbg`，必须设置 `LEAN_PATH`，未在 Windows/macOS 上进行测试）。

## 重大变化
%%%
tag := "zh-releases-v4-30-0-h014"
%%%

- [#12897](https://github.com/leanprover/lean4/pull/12897)：依赖于这些实例之前的“defeq 滥用”或依赖于其特定结构的证明可能需要调整。由于 `inferInstanceAs A` 现在需要准确了解源和目标类型才能继续，因此它不能再用作 `(inferInstance : A)` 的同义词，当源和目标类型相同时，请使用后者。
- [#13005](https://github.com/leanprover/lean4/pull/13005)：直接调用 `compileDecl` 的元程序现在可能需要在适当的情况下首先调用 `markMeta`，这可能基于现有声明的 `isMarkedMeta` 的值。为此，`addAndCompile` 应分为 `addDecl` 和 `compileDecl`，以便在其间插入呼叫。
- [#12749](https://github.com/leanprover/lean4/pull/12749) 重命名元编程 API：`isStructureLike` → `isNonRecStructure`、`matchConstStructLike` → `matchConstNonRecStructure`、`getStructureLikeCtor?` → `getNonRecStructureCtor?`、`getStructureLikeNumFields` → `getNonRecStructureNumFields`。
- [#12771](https://github.com/leanprover/lean4/pull/12771) 将 `String.Slice.Pos.cast` 的签名更改为需要 `s.copy = t.copy` 而不是 `s = t`。如果需要，可以通过将 `proof` 替换为 `congrArg Slice.copy proof` 来轻松调整其用途。
- [#12435](https://github.com/leanprover/lean4/pull/12435) 更改 `Option.getElem?_inj` 的签名。
- [#12708](https://github.com/leanprover/lean4/pull/12708) 更改 `PostCond.noThrow`、`PostCond.mayThrow`、`PostCond.entails`、`PostCond.and`、`PostCond.imp` 中隐式参数的顺序，以便 `α` 始终位于 `ps` 之前。
- [#12603](https://github.com/leanprover/lean4/pull/12603)：具有以无类型绑定程序开头的构造函数的归纳类型可能需要重写，例如如果存在具有该名称的 `variable` 或者如果它旨在隐藏归纳类型的参数之一，则将 `(x)` 更改为 `(x : _)`。

# 语言
%%%
tag := "zh-releases-v4-30-0-h015"
%%%

````markdown

- [#13315](https://github.com/leanprover/lean4/pull/13315)
  fixes `processDefDeriving` to propagate the `meta` attribute to instances derived via delta deriving, so that `deriving BEq` inside a `public meta section` produces a meta instance. Previously the derived `instBEqFoo` was not marked meta, and the LCNF visibility checker rejected meta definitions that used `==` on the alias — this came up while bumping verso to v4.30.0-rc1.

- [#13311](https://github.com/leanprover/lean4/pull/13311)
  adds an optional `markMeta : Bool := false` parameter to `addAndCompile`, so that callers can propagate the `meta` marking without manually splitting into `addDecl` + `markMeta` + `compileDecl`.

- [#13304](https://github.com/leanprover/lean4/pull/13304)
  makes the delta-deriving handler create `theorem` declarations instead of `def` declarations when the instance type is a `Prop`. Previously, `deriving instance Nonempty for Foo` would always create a `def`, which is inconsistent with the behavior of a handwritten `instance` declaration.

- [#13188](https://github.com/leanprover/lean4/pull/13188)
  extends the `missingDocs` linter to detect and warn about empty doc strings (e.g. `/---/` or `/-- -/`), in addition to missing doc strings. Previously, an empty doc comment would silence the linter even though it provides no documentation value. Now empty doc strings produce a distinct "empty doc string for ..." warning, while `@[inherit_doc]` still suppresses warnings as before.

- [#13192](https://github.com/leanprover/lean4/pull/13192)
  fixes the handling of anonymous dependent `if` (`if _ : cond then ... else ...`) inside `do` blocks when using the new do elaborator.

- [#13011](https://github.com/leanprover/lean4/pull/13011)
  adds a `@[deprecated_arg]` attribute that marks individual function parameters as deprecated. When a caller uses the old parameter name, the elaborator emits a deprecation warning with a code action hint to rename or delete the argument, and silently forwards the value to the correct binder.

- [#13153](https://github.com/leanprover/lean4/pull/13153)
  registers the new `spec_invariant_type` attribute alongside the old
  `mvcgen_invariant_type`, renames internal identifiers, and replaces the
  hardcoded `Invariant` check in `Spec.lean` with `isSpecInvariantType`.

- [#13117](https://github.com/leanprover/lean4/pull/13117)
  re-enables `#print axioms` under the module system by computing axiom dependencies at olean serialization time. It reverts #8174 and replaces it with a proper fix.

- [#13142](https://github.com/leanprover/lean4/pull/13142)
  replaces the per-level `OLeanLevel → Array α` return type of `exportEntriesFnEx` with a new `OLeanEntries (Array α)` structure that bundles exported, server, and private entries together. This allows extensions to share expensive computation across all three olean levels instead of being called three separate times.

- [#13120](https://github.com/leanprover/lean4/pull/13120)
  reverts the `mvcgen witnesses` syntax addition and undoes the back compat hack in `elabMVCGen`.

- [#13111](https://github.com/leanprover/lean4/pull/13111)
  reverts #12882 which added the `@[mvcgen_witness_type]` tag attribute and `witnesses` section to `mvcgen`. Théophile Wallez confirmed he doesn't need this feature and can get by with `invariants`, so there is no use in having it.

- [#13059](https://github.com/leanprover/lean4/pull/13059)
  switches `normalizeInstance` from using `isMetaSection` to the existing `declName?` pattern (already used by `unsafe` in `BuiltinNotation.lean` and `private_decl%` in `BuiltinTerm.lean`) for determining whether aux defs should be marked `meta`.

- [#12973](https://github.com/leanprover/lean4/pull/12973)
  makes theorems opaque in almost all ways, including in the kernel.

- [#12987](https://github.com/leanprover/lean4/pull/12987)
  extracts the functional (lambda) passed to `brecOn` in structural
  recursion into a named `_f` helper definition (e.g. `foo._f`), similar to
  how well-founded recursion uses `._unary`. This way the functional shows up
  with a helpful name in kernel diagnostics rather than as an anonymous lambda.

- [#13043](https://github.com/leanprover/lean4/pull/13043)
  fixes a bug where `inferInstanceAs` and the default `deriving` handler, when used inside a `meta section`, would create auxiliary definitions (via `normalizeInstance`) that were not marked as `meta`. This caused the compiler to reject the parent `meta` definition with:

  ```
  `meta` 定义无效 `instEmptyCollectionNamePrefixRel`、`instEmptyCollectionNamePrefixRel._aux_1` 未标记 `meta`
  ```

- [#13029](https://github.com/leanprover/lean4/pull/13029)
  removes the unused `change ... with` tactic syntax.

- [#12897](https://github.com/leanprover/lean4/pull/12897)
  adjusts the results of `inferInstanceAs` and the `def` `deriving` handler to conform to recently strengthened restrictions on reducibility. This change ensures that when deriving or inferring an instance for a semireducible type definition, the definition's RHS is not leaked when the instance is reduced at lower than semireducible transparency.

- [#13005](https://github.com/leanprover/lean4/pull/13005)
  further enforces that all modules used in compile-time execution must be meta imported in preparation for enabling https://github.com/leanprover/lean4/pull/10291

- [#12840](https://github.com/leanprover/lean4/pull/12840)
  fixes an issue where the use of private imports led to unknown namespaces in downstream modules.

- [#12953](https://github.com/leanprover/lean4/pull/12953)
  fixes an issue where the `induction` and `cases` tactics would swallow diagnostics (such as unsolved goals errors) when the `using` clause contains a nested tactic.

- [#12979](https://github.com/leanprover/lean4/pull/12979)
  makes `#print` show the full internal private name (including
  module prefix) in the declaration signature when `pp.privateNames` is
  set to true. Previously, `pp.privateNames` only affected names in the
  body but the signature always stripped the private prefix.

- [#12964](https://github.com/leanprover/lean4/pull/12964)
  fixes an issue where `realizeConst` would generate auxiliary declarations
  (like `_sparseCasesOn`) using the original defining module's private name prefix
  rather than the realizing module's prefix. When two modules independently realized
  the same imported constant, they produced identically-named auxiliary declarations,
  causing "environment already contains" errors on diamond import.

- [#12881](https://github.com/leanprover/lean4/pull/12881)
  adds `Invariant.withEarlyReturnNewDo`, `StringInvariant.withEarlyReturnNewDo`, and `StringSliceInvariant.withEarlyReturnNewDo` which use `Prod` instead of `MProd` for the state tuple, matching the new do elaborator's output. The existing `withEarlyReturn` definitions are reverted to `MProd` for backwards compatibility with the legacy do elaborator. Tests and invariant suggestions are updated to use the `NewDo` variants.

- [#12880](https://github.com/leanprover/lean4/pull/12880)
  applies `@[mvcgen_invariant_type]` to `Std.Do.Invariant` and removes the hard-coded fallback in `isMVCGenInvariantType` that was needed for bootstrapping (cf. #12874). It also extracts `StringInvariant` and `StringSliceInvariant` as named abbreviations tagged with `@[mvcgen_invariant_type]`, so that `mvcgen` classifies string and string slice loop invariants correctly.

- [#12874](https://github.com/leanprover/lean4/pull/12874)
  adds an `@[mvcgen_invariant_type]` tag attribute so that users can mark
  custom types as invariant types for the `mvcgen` tactic. Goals whose type is an
  application of a tagged type are classified as invariants rather than verification
  conditions. The hard-coded check for `Std.Do.Invariant` is kept as a fallback
  until a stage0 update allows applying the attribute directly.

- [#12767](https://github.com/leanprover/lean4/pull/12767)
  makes sure that identifiers with `Meta` or `Simproc` in their name do not show up in library search results.

- [#12866](https://github.com/leanprover/lean4/pull/12866)
  adds `optType` support to the `doPatDecl` parser, allowing
  `let ⟨width, height⟩ : Nat × Nat ← action` in do-notation. Previously, only
  the less ergonomic `let ⟨width, height⟩ : Nat × Nat := ← action` workaround
  was available. The type annotation is propagated to the monadic action as an
  expected type, matching `doIdDecl`'s existing behavior.

- [#12698](https://github.com/leanprover/lean4/pull/12698)
  adds a `result? : Option TraceResult` field to `TraceData` and populates it in `withTraceNode` and `withTraceNodeBefore`, so that metaprograms walking trace trees can determine success/failure structurally instead of string-matching on emoji.

- [#12233](https://github.com/leanprover/lean4/pull/12233)
  replaces the default `instantiateMVars` implementation with a two-pass variant that fuses fvar substitution into the traversal, avoiding separate `replace_fvars` calls for delayed-assigned MVars and preserving sharing. The old single-pass implementation is removed entirely.

- [#12560](https://github.com/leanprover/lean4/pull/12560)
  changes the way the linting for `linter.unusedSimpArgs` gets the value from the environment. This is achieved by using the appropriate helper functions defined in `Lean.Linter.Basic`.

- [#11427](https://github.com/leanprover/lean4/pull/11427)
  modifies `#eval e` to elaborate `e` with section variables in scope. While evaluating expressions with free variables is not possible, this lets `#eval` give a better error message than "unknown identifier."

- [#12841](https://github.com/leanprover/lean4/pull/12841)
  changes the elaboration of the `structure`/`class` commands so that default values have later fields in context as well. This allows field defaults to depend on fields that come both before and after them. While this was already the case for inherited fields to some degree, it now applies uniformly to all fields. Additionally, when elaborating the default value for a field, all fields that depend on it are cleared from the context to avoid situations where the default value depends on itself.

- [#12749](https://github.com/leanprover/lean4/pull/12749)
  changes "structure-like" terminology to "non-recursive structure" across internal documentation, error messages, the metaprogramming API, and the kernel, to clarify Lean's type theory. A *structure* is a one-constructor inductive type with no indices — these can be created by either the `structure` or `inductive` commands — and are supported by the primitive `Expr.proj` projections. Only *non-recursive* structures have an eta conversion rule. The PR description contains the APIs that were renamed.

- [#12662](https://github.com/leanprover/lean4/pull/12662)
  adjusts the module parser to set the leading whitespace of the first token to the whitespace up to that token. If there are no actual tokens in the file, the leading whitespace is set on the final (empty) EOI token. This ensures that we do not lose the initial whitespace (e.g. comments) of a file in `Syntax`.

- [#12325](https://github.com/leanprover/lean4/pull/12325)
  adds a warning to any `def` of class type that does not also declare an appropriate reducibility.

- [#12817](https://github.com/leanprover/lean4/pull/12817)
  moves the universe-level-count check from `unfold_definition_core` into `is_delta`, establishing the invariant that if `is_delta` succeeds then `unfold_definition` also succeeds. This prevents a crash (SIGSEGV or garbled error) that occurred when call sites in `lazy_delta_reduction_step` unconditionally dereferenced the result of `unfold_definition` even on a level-parameter-count mismatch.

- [#12802](https://github.com/leanprover/lean4/pull/12802)
  re-applies https://github.com/leanprover/lean4/pull/12757 (reverted in https://github.com/leanprover/lean4/pull/12801) with the `release-ci` label to test whether it causes the async extension PANIC seen in the v4.29.0-rc5 tag CI.

- [#12789](https://github.com/leanprover/lean4/pull/12789)
  skips the noncomputable pre-check in `processDefDeriving` when the instance type is `Prop`. Since proofs are erased by the compiler, computability is irrelevant for `Prop`-valued instances.

- [#12776](https://github.com/leanprover/lean4/pull/12776)
  fixes `@[implicit_reducible]` on well-founded recursive definitions.

- [#12778](https://github.com/leanprover/lean4/pull/12778)
  fixes an inconsistency in `getStuckMVar?` where the instance argument to class projection functions and auxiliary parent projections was not whnf-normalized before checking for stuck metavariables. Every other case in `getStuckMVar?` (recursors, quotient recursors, `.proj` nodes) normalizes the major argument via `whnf` before recursing — class projection functions and aux parent projections were the exception.

- [#12756](https://github.com/leanprover/lean4/pull/12756)
  adds `deriving noncomputable instance Foo for Bar` syntax so that delta-derived instances can be marked noncomputable. Previously, when the underlying instance was noncomputable, `deriving instance` would fail with an opaque async compilation error.

- [#12699](https://github.com/leanprover/lean4/pull/12699)
  gives the `generate` function's "apply @Foo to Goal" trace nodes their own trace sub-class `Meta.synthInstance.apply` instead of sharing the parent `Meta.synthInstance` class.

- [#12701](https://github.com/leanprover/lean4/pull/12701)
  fixes a gap in how `@[implicit_reducible]` is assigned to parent projections during structure elaboration.

- [#12719](https://github.com/leanprover/lean4/pull/12719)
  marks `levelZero` and `Level.ofNat` as `@[implicit_reducible]` so that `Level.ofNat 0 =?= Level.zero` succeeds when the definitional equality checker respects transparency annotations. Without this, coercions between structures with implicit `Level` parameters fail, as reported by @FLDutchmann on [Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/near/576131374).

- [#12695](https://github.com/leanprover/lean4/pull/12695)
  fixes a bug in `Meta.zetaReduce` where `have` expressions were not being zeta reduced. It also adds a feature where applications of local functions are beta reduced, and another where zeta-delta reduction can be disabled. These are all controllable by flags:
  - `zetaDelta` (default: true) enables unfolding local definitions
  - `zetaHave` (default: true) enables zeta reducing `have` expressions
  - `beta` (default: true) enables beta reducing applications of local definitions

- [#12696](https://github.com/leanprover/lean4/pull/12696)
  fixes a test case reported by Alexander Bentkamp that runs into a heartbeat limit due to daring use of `withDefault` `rfl` in `mvcgen`.

- [#12680](https://github.com/leanprover/lean4/pull/12680)
  fixes an issue where `mutual public structure` would have a private constructor. The fix copies the fix from #11940.

- [#12602](https://github.com/leanprover/lean4/pull/12602)
  restricts and in particular simplifies the semantics of `evalConst` with `(checkMeta := true)` (which is the default): it now fails iff the passed constant name is not `meta` (and we are under `module`).

- [#12603](https://github.com/leanprover/lean4/pull/12603)
  adds a feature where `inductive` constructors can override the binder kinds of the type's parameters, like in #9480 for `structure`. For example, it's possible to make `x` explicit in the constructor `Eq.refl`, rather than implicit:
  ```lean
  inductive Eq {α : Type u} (x : α) : α → Prop where
    | refl (x) : 方程 x x
  ```

- [#12647](https://github.com/leanprover/lean4/pull/12647)
  adds the missing `popScopes` call to `withNamespace`, which previously
  only dropped scopes from the elaborator's `Command.State` but did not pop the
  environment's `ScopedEnvExtension` state stacks. This caused scoped syntax
  declarations to leak keywords outside their namespace when `withNamespace` had
  been called.

- [#12673](https://github.com/leanprover/lean4/pull/12673)
  allows for a leightweight version of dependent `match` in the new `do` elaborator: discriminant types get abstracted over previous discriminants. The match result type and the local context still are not considered for abstraction. For example, if both `i : Nat` and `h : i < len` are discrminants, then if an alternative matches `i` with `0`, we also have `h : 0 < len`:

  ```lean
  example {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
    let rec 循环 (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
      将 i、h 与
      | 0, _ => 纯 b
      |我+1，h =>
        有 h' : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
        有： as.size - 1 < as.size := Nat.sub_lt (Nat.zero_lt_of_lt h') （由决定）
        有： as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
        匹配 (← f as[as.size - 1 - i] (Array.getElem_mem this) b) 与
        | ForInStep.done b => 纯 b
        | ForInStep.yield b => 循环 i (Nat.le_of_lt h') b
    循环 as.size (Nat.le_refl _) b
  ```

- [#12608](https://github.com/leanprover/lean4/pull/12608)
  continues #9674, cleaning up binder annotations inside the bodies of `let rec` and `where` definitions.

- [#12666](https://github.com/leanprover/lean4/pull/12666)
  fixes spurious unused variable warnings for variables used in non-atomic match discriminants in `do` notation. For example, in `match Json.parse s >>= fromJson? with`, the variable `s` would be reported as unused.

- [#12661](https://github.com/leanprover/lean4/pull/12661)
  fixes false-positive "unused variable" warnings for mutable variables reassigned inside `try`/`catch` blocks with the new do elaborator.

````

# 图书馆
%%%
tag := "zh-releases-v4-30-0-h016"
%%%

```markdown

- [#13175](https://github.com/leanprover/lean4/pull/13175)
  修复了 http_body 中流的错误行为。

- [#12144](https://github.com/leanprover/lean4/pull/12144)
  引入了 `Body` 类型类、`ChunkStream` 和 `Full` 类型，用于表示请求和响应的流主体。

- [#13129](https://github.com/leanprover/lean4/pull/13129)
  实现向后模式的验证基础设施，类似于现有的前向模式基础设施。在此基础上，它增加了对字符串上的 `skipSuffix?`、`endsWith` 和 `dropSuffix?` 函数的验证。

- [#12912](https://github.com/leanprover/lean4/pull/12912)
  添加有关 `ExceptCpsT.runK` 的简单引理以匹配有关 `.run` 的现有引理。

- [#13109](https://github.com/leanprover/lean4/pull/13109)
  添加有关 `String` 操作 `drop`、`dropEnd`、`take`、`takeEnd` 的引理。

- [#13106](https://github.com/leanprover/lean4/pull/13106)
  通过提供低级 API `nextn_zero`/`nextn_add_one` 以及 `Splits` 引理来验证 `String.Pos.nextn`。

- [#13105](https://github.com/leanprover/lean4/pull/13105)
  证明了`theorem front?_eq {s : String} : s.front? = s.toList.head?`及相关结果。

- [#13098](https://github.com/leanprover/lean4/pull/13098)
  概括了有关 `Nat.ofDigitChars` 的一些定理，这些定理不必要地限制为基数 10。

- [#13096](https://github.com/leanprover/lean4/pull/13096)
  显示给定 `c : l.Cursor` 的简单结果，我们有 `c.pos ≤ l.length`。

- [#13092](https://github.com/leanprover/lean4/pull/13092)
  修复了 `Std.Iter.joinString` 由于实际上不必要的 `IteratorLoop` 实例而具有额外的 Universe 参数的问题。

- [#13091](https://github.com/leanprover/lean4/pull/13091)
  添加函数 `String.Slice.join` 并添加有关 `String.join` 和 `String.Slice.join` 的引理。

- [#13090](https://github.com/leanprover/lean4/pull/13090)
  添加单个引理 `Char.toNat_mk`。

- [#13061](https://github.com/leanprover/lean4/pull/13061)
  在 `List String.Slice` 上添加有关 `BEq` 的引理。

- [#13058](https://github.com/leanprover/lean4/pull/13058)
  将 `EquivBEq` 和 `LawfulHashable` 实例添加到 `String.Slice`。

- [#13057](https://github.com/leanprover/lean4/pull/13057)
  添加了有关 `String.toNat?` 和朋友的现有引理的一些变体。

- [#13056](https://github.com/leanprover/lean4/pull/13056)
  添加功能 `Std.Iter.joinString` 和 `Std.Iter.intercalateString`。

- [#13054](https://github.com/leanprover/lean4/pull/13054)
  添加 simproc String.reduceToSingleton`, which is disabled by default and turns `"c"` into `String.singleton 'c'`。

- [#13003](https://github.com/leanprover/lean4/pull/13003)
  重新组织实例 `ToString Int` 和 `Repr Int`，以便它们都指向公共定义 `Int.repr`（`Nat` 使用相同的设置）。然后它验证函数 `Int.repr`、`String.isInt` 和 `String.toInt`。

- [#12999](https://github.com/leanprover/lean4/pull/12999)
  验证我们各种模式的 `String.dropPrefix?` 功能。

- [#12469](https://github.com/leanprover/lean4/pull/12469)
  添加 `Thunk` 的 `Inhabited` 实例。

- [#12128](https://github.com/leanprover/lean4/pull/12128)
  引入 `URI` 数据类型。

- [#12990](https://github.com/leanprover/lean4/pull/12990)
  验证我们各种模式类型的 `String.startsWith` 和 `String.skipPrefix?` 函数。

- [#12988](https://github.com/leanprover/lean4/pull/12988)
  引入函数 `String.Slice.skipPrefix?`、`String.Slice.Pos.skip?`、`String.Slice.skipPrefixWhile`、`String.Slice.Pos.skipWhile` 并重新定义 `String.Slice.takeWhile` 和 `String.Slice.dropWhile` 以使用这些新函数。

- [#12984](https://github.com/leanprover/lean4/pull/12984)
  将函数 `ForwardPattern.dropPrefix?` 重命名为 `ForwardPattern.skipPrefix`？

- [#12828](https://github.com/leanprover/lean4/pull/12828)
  重新定义 `String.isNat` 函数以使用更少的状态并执行短路。然后，它验证 `String.isNat` 和 `String.toNat?` 功能。

- [#12980](https://github.com/leanprover/lean4/pull/12980)
  添加有关 `Char`、`Nat` 和 `List` 的定理。

- [#12977](https://github.com/leanprover/lean4/pull/12977)
  删除了 #12945 中添加的大部分 `simp` 注释，以减轻性能影响。引理仍然存在。

- [#12966](https://github.com/leanprover/lean4/pull/12966)
  添加了将 `n.digitChar = '0'` 简化为 `n = 0` 的 simpl 引理以及将 `n.digitChar = '!'` 简化为 `False` 的 simproc。

- [#12924](https://github.com/leanprover/lean4/pull/12924)
  修复了 Lean 4.29.0-rc2 中引入的回归，其中由于 `backward.isDefEq.respectTransparency` 更改，`simp` 不再简化内部类型类实例参数。这会破坏像 `(a :: l).length` 这样的术语同时出现在主表达式和隐式实例参数中的证明（例如，确定 `BitVec` 宽度）。

- [#12950](https://github.com/leanprover/lean4/pull/12950)
  添加了将内核友好函数名称与其等效运算符表示法等同的简单引理：`Nat.land_eq`、`Nat.lor_eq`、`Nat.xor_eq`、`Nat.shiftLeft_eq'`、`Nat.shiftRight_eq'` 和 `Bool.rec_eq`。当证明涉及反射并且需要将内核简化项简化回运算符符号时，这些非常有用。

- [#12955](https://github.com/leanprover/lean4/pull/12955)
  使用信号处理程序修复 Windows 构建。

- [#12945](https://github.com/leanprover/lean4/pull/12945)
  将一些 `forall` 引理添加到 `simp` 集中。

- [#12900](https://github.com/leanprover/lean4/pull/12900)
  修复了一些编号错误的过程信号。

- [#12127](https://github.com/leanprover/lean4/pull/12127)
  引入了 `Headers` 数据类型，它为解析、查询和编码 HTTP/1.1 标头提供了良好且方便的抽象。

- [#12936](https://github.com/leanprover/lean4/pull/12936)
  修复了 `Id.run_seqLeft` 和 `Id.run_seqRight` 以在两个 monad 结果不同时应用。

- [#12909](https://github.com/leanprover/lean4/pull/12909)
  修复了 `Int.sq_nonnneg` 中的拼写错误。

- [#12919](https://github.com/leanprover/lean4/pull/12919)
  修复了 `HSub PlainTime Duration` 实例，该实例的操作数颠倒了：它计算的是 `duration - time` 而不是 `time - duration`。例如，从 `time("13:02:01")` 中减去 2 分钟将得到 `time("10:57:59")`，而不是预期的 `time("13:00:01")`。我们还注意到 `HSub PlainDateTime Millisecond.Offset` 也受到类似的影响。

- [#12885](https://github.com/leanprover/lean4/pull/12885)
  移动 `Init` 中的一些材料，以确保基本类型的 `ToString` 实例不依赖于 `String.Internal.append`。

- [#12857](https://github.com/leanprover/lean4/pull/12857)
  删除了 HTTP 库中 `native_decide` 的使用，并添加了删除 `panic!` 的证据。

- [#12852](https://github.com/leanprover/lean4/pull/12852)
  实现 `PersistentHashMap` 的迭代器。

- [#12844](https://github.com/leanprover/lean4/pull/12844)
  提供迭代器组合器 `append`，允许连接两个迭代器。

- [#12481](https://github.com/leanprover/lean4/pull/12481)
  在树图和树集中提供有关 `toArray` 和 `keysArray` 的引理，类似于现有的 `toList` 和 `keys` 引理。

- [#12385](https://github.com/leanprover/lean4/pull/12385)
  在数组上实现合并排序算法。经测量，对于具有随机元素的大型数组，它的速度大约是 `List.mergeSort` 的两倍，但对于小型或几乎排序的数组，列表实现速度更快。与 `Array.qsort` 相比，它很稳定并且具有 O(n log n) 最坏情况成本。注意：仍有很大的优化潜力。当前的实现分配 O(n log n) 个数组，每个递归调用分配一个数组。

- [#12821](https://github.com/leanprover/lean4/pull/12821)
  从 `List.getElem_of_getElem?` 和 `Vector.getElem_of_getElem?` 中删除 `@[grind →]` 属性。这些在 Mathlib 中被 https://github.com/leanprover/lean4/issues/12805. 识别为有问题

- [#12807](https://github.com/leanprover/lean4/pull/12807)
  生成有关最近添加到公共声明中的 `String.find?` 和 `String.contains` 的引理。

- [#12757](https://github.com/leanprover/lean4/pull/12757)
  将 `Id.run` 标记为 `[implicit_reducible]`，以确保使用 `.implicitReducible` 透明度设置时 `Id.instMonadLiftTOfPure` 和 `instMonadLiftT Id` 在定义上相等。

- [#12793](https://github.com/leanprover/lean4/pull/12793)
  采用更原则性的方法，通过简化为类似于实例定义方式的更简单的情况来导出 `String` 模式引理。

- [#12126](https://github.com/leanprover/lean4/pull/12126)
  介绍了核心 HTTP 数据类型：`Request`、`Response`、`Status`、`Version` 和 `Method`。目前，URI 表示为 `String`，标头表示为 `HashMap String (Array String)`。这些是占位符，未来的 PR 将用严格的实现取代它们。

- [#12783](https://github.com/leanprover/lean4/pull/12783)
  为 `s.contains t` 添加面向用户的 API 引理，其中 `s` 和 `t` 都是字符串或切片。

- [#12760](https://github.com/leanprover/lean4/pull/12760)
  添加 `ExceptConds` 合取的一般投影引理：

  - `ExceptConds.and_elim_left`: `(x ∧ₑ y) ⊢ₑ x`
  - `ExceptConds.and_elim_right`: `(x ∧ₑ y) ⊢ₑ y`

- [#12779](https://github.com/leanprover/lean4/pull/12779)
  为字符串模式提供 `ForwardPatternModel`，并从切片模式的相应结果中推导出定理和合法性实例。

- [#12777](https://github.com/leanprover/lean4/pull/12777)
  添加有关 `String.find?` 和 `String.contains` 的引理。

- [#12771](https://github.com/leanprover/lean4/pull/12771)
  概括了 `String.Slice.Pos.cast`，它将 `s.Pos` 转换为 `t.Pos`，不再需要 `s = t`，而只需要 `s.copy = t.copy`。

- [#12433](https://github.com/leanprover/lean4/pull/12433)
  为 `BitVec.cpop` 添加了一个位爆破电路，具有并行前缀和的分而治之功能。

- [#12435](https://github.com/leanprover/lean4/pull/12435)
  提供 `List.getElem`、`List.getElem?`、`List.getElem!` 和 `List.getD` 以及 `Option` 的单射引理。注意：这引入了重大更改，更改了 `Option.getElem?_inj` 的签名。

- [#12725](https://github.com/leanprover/lean4/pull/12725)
  显示合法搜索者将空字符串拆分为 `[""]`。

- [#12723](https://github.com/leanprover/lean4/pull/12723)
  将 `String.split` 与 `List.splitOn` 和 `List.splitOnP` 关联起来，前提是我们按字符或字符谓词进行拆分。

- [#12710](https://github.com/leanprover/lean4/pull/12710)
  弃用了核心中涉及组件 `cons₂` 的少数名称，转而使用 `cons_cons`。

- [#12709](https://github.com/leanprover/lean4/pull/12709)
  添加了各种 `String` 引理，这些引理对于导出有关 `String.split` 的高级定理非常有用。

- [#12708](https://github.com/leanprover/lean4/pull/12708)
  更改隐式参数 `α` 和 `ps` 的顺序，使得 `α` 在 `PostCond.noThrow`、`PostCond.mayThrow`、`PostCond.entails`、`PostCond.and`、`PostCond.imp` 中始终位于 `ps` 之前，定理。

- [#12707](https://github.com/leanprover/lean4/pull/12707)
  添加有关 `String.intercalate` 和 `String.Slice.intercalate` 的引理。

- [#12706](https://github.com/leanprover/lean4/pull/12706)
  添加了一个 dsimproc，用于计算 `String.singleton ' '` 到 `" "`。

- [#12697](https://github.com/leanprover/lean4/pull/12697)
  向 Std.Do 添加了两个新的展开定理：`PostCond.entails.mk` 和 `Triple.of_entails_wp`。

- [#12702](https://github.com/leanprover/lean4/pull/12702)
  来自 Batteries/mathlib 的上游 `List.splitOn` 和 `List.splitOnP`。

- [#12405](https://github.com/leanprover/lean4/pull/12405)
  在 `List`、`Array` 和 `Vector` 缺失时添加几个有用的引理，从而提高 API 的覆盖率和这些类型之间的一致性。
  - `size_singleton`/`sum_singleton`/`sum_push`
  - `foldlM_toArray`/`foldlM_toList`/`foldl_toArray`/`foldl_toList`/`foldrM_toArray`/`foldrM_toList`/`foldr_toList`
  - `toArray_toList`
  - `foldl_eq_apply_foldr`/`foldr_eq_apply_foldl`、`foldr_eq_foldl`：将 `foldl` 和 `foldr` 与恒等关联运算关联起来
  - `sum_eq_foldl`：将 sum 与 `foldl` 关联，以进行与恒等的关联运算
  - `Perm.pairwise_iff`/`Perm.pairwise`：在数组排列下保留成对属性

- [#12430](https://github.com/leanprover/lean4/pull/12430)
  提供 `WellFounded.partialExtrinsicFix`，这使得实现和验证部分终止功能成为可能，安全地构建在看似不太通用的 `extrinsicFix`（现在称为 `totalExtrinsicFix`）之上。仅为了正式验证 `partialExtrinsicFix` 的行为才需要终止证明。

- [#12685](https://github.com/leanprover/lean4/pull/12685)
  添加了一些有关跨子切片操作 `slice`、`sliceFrom`、`sliceTo` 转移位置的缺失材料。

- [#12678](https://github.com/leanprover/lean4/pull/12678)
  将 `List.flatten`、`List.flatMap`、`List.intercalate` 标记为不可计算，以确保其 `csimp` 变体在任何地方都使用。

- [#12668](https://github.com/leanprover/lean4/pull/12668)
  添加有关字符串位置和模式的引理，这对于为 `String.split` 和朋友提供高级 API 引理非常有用。

```

# 策略
%%%
tag := "zh-releases-v4-30-0-h017"
%%%

```markdown

- [#13177](https://github.com/leanprover/lean4/pull/13177)
  将 `@[expose]` 添加到 `Lean.Grind.abstractFn` 并
  `Lean.Grind.simpMatchDiscrsOnly` 以便内核可以在以下情况下展开它们：
  在 `module` 块内对 `grind` 生成的证明进行类型检查。其他
  类似的小工具（`nestedDecidable`、`PreMatchCond`、`alreadyNorm`）
  已经暴露了；这两个只是被错过了。

- [#13166](https://github.com/leanprover/lean4/pull/13166)
  用新的类型定向标准化器 (`Sym.canon`) 替换了 `grind` 标准化器，该标准化器进入绑定器并在类型位置上应用有针对性的减少，从而消除了基于 O(n^2) `isDefEq` 的方法。

- [#13149](https://github.com/leanprover/lean4/pull/13149)
  通过消除死状态和不必要的状态来简化 `grind` 规范化器
  复杂性，并修复了清理过程中发现的两个错误。

- [#13080](https://github.com/leanprover/lean4/pull/13080)
  添加了 `SymExtension`，这是 `SymM` 的类型化可扩展状态机制，
  遵循与 `Grind.SolverExtension` 相同的模式。扩展名是
  在初始化时通过 `registerSymExtension` 注册并提供
  类型为 `getState`/`modifyState` 访问器。扩展状态持续存在
  `sym =>` 块内的 `simp` 调用，并在每次调用时重新初始化
  `SymM.run`。

- [#13048](https://github.com/leanprover/lean4/pull/13048)
  添加了两个新的 `sym_simproc` DSL 原语和辅助研磨模式
  策略。

- [#13046](https://github.com/leanprover/lean4/pull/13046)
  防止 `Sym.simp` 循环排列定理，例如
  `∀ x y, x + y = y + x`。

- [#13042](https://github.com/leanprover/lean4/pull/13042)
  在 `sym =>` 模式下扩展 `simp`策略以支持本地
  额外定理列表中的假设。

- [#13041](https://github.com/leanprover/lean4/pull/13041)
  扩展 `mkTheoremFromDecl` 和 `mkTheoremFromExpr` 来处理
  结论不等式的定理，使 `Sym.simp` 能够使用
  更广泛的一类引理作为重写规则。

- [#13040](https://github.com/leanprover/lean4/pull/13040)
  向 `register_sym_simp` 命令添加验证：

  - 拒绝重复的变体名称
  - 通过 `elabSymSimproc` 详细说明 `pre`/`post` 语法来验证它们
    在最小的 `GrindTacticM` 上下文中，捕获未知的定理名称
    和未知定理在注册时设置参考

- [#13039](https://github.com/leanprover/lean4/pull/13039)
  将 `simp`策略添加到 `sym =>` 交互模式，完成
  `Sym.simp` 交互式基础设施。

- [#13034](https://github.com/leanprover/lean4/pull/13034)
  添加 `register_sym_simp` 命令用于声明名为 `Sym.simp`
  具有 `pre`/`post` simproc 链和可选配置覆盖的变体。

- [#13033](https://github.com/leanprover/lean4/pull/13033)
  将 `r == e` 防护添加到 `Int.Linear.simpEq?` 的 `norm_eq_var` 和 `norm_eq_var_const` 分支。如果没有这些保护，`simpEq?` 会为 `x = -1` 等已经标准化的方程返回一个重要的证明，导致 `exists_prop_congr` 反复触发并构建无限增长的项。

- [#13032](https://github.com/leanprover/lean4/pull/13032)
  修复了 #12842，其中 `grind` 在涉及高次多项式的目标上耗尽内存，例如 `(x + y)^2 = x^128 + y^2` 超过 `Fin 2`。

- [#13031](https://github.com/leanprover/lean4/pull/13031)
  添加了 #13026 中引入的 `sym_simproc` 和 `sym_discharger` DSL 语法类别的内置精化器。

- [#13027](https://github.com/leanprover/lean4/pull/13027)
  修复了 `grind` 中由 `BEq`/`Hashable` 不变量引起的不确定性崩溃
  违反同余表。 `congrHash` 使用每个表达式自己的 `funCC` 标志来
  计算其哈希值（`funCC = true` 的一级分解、完全递归分解
  对于 `funCC = false`），但 `isCongruent` 仅检查存储的表达式的标志。当两个
  具有不匹配的 `funCC` 标志的表达式意外发生哈希冲突（通过基于指针的
  `ptrAddrUnsafe` 散列），`isCongruent` 可以声明它们一致，尽管不同
  参数计数，导致 `mkCongrProof` 中的断言失败。

- [#13026](https://github.com/leanprover/lean4/pull/13026)
  添加了 simproc 和放电器 DSL 的基础设施，用于指定 `pre`/`post` simproc 链和 `Sym.simp` 变体中的条件重写放电器。

- [#13024](https://github.com/leanprover/lean4/pull/13024)
  修复了 `grind` 可以单独证明每个合取但在合取上失败的问题。根本原因：`solverAction` 的 `.propagated` 路径调用 `processNewFacts`，从而耗尽 `newFacts` 队列，但生成的传播级联（同余闭包、或传播、`propagateForallPropDown`）可以调用 `addNewRawFact`，排队到单独的队列`newRawFacts` 队列。这些原始事实从未被耗尽。

- [#13018](https://github.com/leanprover/lean4/pull/13018)
  添加具有关联属性的 `Sym.simp` 的命名定理集，遵循与 `Meta.simp` 的 `register_simp_attr` 相同的模式。

- [#12996](https://github.com/leanprover/lean4/pull/12996)
  将每个结果的 `contextDependent` 跟踪添加到 `Sym.Simp.Result` 并将简化器缓存分为持久（上下文无关）和瞬态（上下文相关，在活页夹输入时清除）。这取代了粗略的 `wellBehavedMethods` 标志。

- [#12970](https://github.com/leanprover/lean4/pull/12970)
  添加进入交互式符号模拟的 `sym =>`策略
  模式基于 `grind` 构建。与`grind =>`不同的是，它并没有急于介绍
  假设或应用矛盾，让用户明确控制
  `intro`、`apply` 和 `internalize` 步骤。

- [#12944](https://github.com/leanprover/lean4/pull/12944)
  更改 `@[cbv_opaque]` 和 `@[cbv_eval]` 之间的交互
  `cbv`策略中的属性。此前，`@[cbv_opaque]`完全被屏蔽
  所有减少，包括 `@[cbv_eval]` 重写规则。现在，`@[cbv_eval]` 规则
  可以触发 `@[cbv_opaque]` 常量，允许用户提供自定义重写
  规则而不暴露完整的定义。方程定理，展开定理，
  对于不透明常数，内核的减少仍然受到抑制。

- [#12923](https://github.com/leanprover/lean4/pull/12923)
  修复了 SymM 的模式匹配中 `max u v` 和 `max v u` 无法匹配的错误。 `processLevel`（第 1 阶段）和 `isLevelDefEqS`（第 2 阶段）都按位置处理 `max`，因此 `max u v ≠ max v u` 在结构上即使它们在语义上相同。

- [#12920](https://github.com/leanprover/lean4/pull/12920)
  将 eta 缩减添加到 sym 判别树查找函数（`getMatch`、`getMatchWithExtra`、`getMatchLoop`）。如果没有这个，像 `StateM Nat` 这样展开为 eta 扩展形式 `(fun α => StateT Nat Id α)` 的表达式将无法匹配 eta 缩减形式 `(StateT Nat Id)` 的判别树条目。

- [#12887](https://github.com/leanprover/lean4/pull/12887)
  优化 `String.reduceEq`、`String.reduceNe` 和 `Sym.Simp` 字符串相等 simproc，以生成内核高效证明。以前，这些使用 `String.decEq` 强制内核运行 UTF-8 编码/解码和字节数组比较，导致短字符串上出现 86+内核展开。

- [#12908](https://github.com/leanprover/lean4/pull/12908)
  使 `@[cbv_opaque]` 无条件阻止常量的所有计算
  由`cbv`，包括`@[cbv_eval]`重写规则。以前，`@[cbv_eval]` 可以
  旁路 `@[cbv_opaque]`，对于裸常数（不是应用程序），`isOpaqueConst`
  可能会进入 `handleConst`，这将展开定义主体。

- [#12888](https://github.com/leanprover/lean4/pull/12888)
  将 `String` 特定的 simproc 添加到 `cbv`策略。

- [#12882](https://github.com/leanprover/lean4/pull/12882)
  添加了 `@[mvcgen_witness_type]` 标记属性，类似于 `@[mvcgen_invariant_type]`，允许用户将类型标记为见证类型。类型为标记类型应用的目标被分类为见证而不是验证条件，并出现在 `mvcgen`策略语法中的新 `witnesses` 部分中（在 `invariants` 之前）。

- [#12875](https://github.com/leanprover/lean4/pull/12875)
  添加 `cbv` simprocs 用于从数组中获取元素。

- [#12597](https://github.com/leanprover/lean4/pull/12597)
  为 `cbv`策略添加 `cbv_simproc` 系统，镜像 simp 的 `simproc` 基础设施，但针对 cbv 的三相管道（`↓` pre、`cbv_eval` eval、`↑` post）进行定制。用户定义的简化程序通过判别树模式进行索引，并在 CBV 标准化期间进行调度。

- [#12851](https://github.com/leanprover/lean4/pull/12851)
  添加对使用 `attribute [-cbv_eval]` 擦除 `@[cbv_eval]` 注释的支持，镜像 simpl 引理的现有 `@[-simp]` 机制。

- [#12805](https://github.com/leanprover/lean4/pull/12805)
  添加 `set_option grind.unusedLemmaThreshold`，当设置为 N > 0 时
  并且 `grind` 成功，报告至少激活 N 个的 E 匹配引理
  次但没有出现在最终的证明项中。这有助于识别 `@[grind]`
  经常触发但不提供证明的注释。

- [#12563](https://github.com/leanprover/lean4/pull/12563)
  使 `omit`、`unusedSectionVars` 和 `loopingSimpArgs` linters 遵循 `linter.all` 选项：
  当 `linter.all` 设置为 false（并且未设置相应的 linter 选项）时，linter 不应报告错误。

- [#12816](https://github.com/leanprover/lean4/pull/12816)
  解决了处理 `ite`/`dite`、`decide` 时的三个不同问题。

- [#12788](https://github.com/leanprover/lean4/pull/12788)
  添加了一个 `set_option cbv.maxSteps N` 选项来控制最大
  `cbv`策略执行的简化步骤数。之前的极限
  被硬编码为 `Sym.Simp.Config` 默认值 100,000，无法
  用户覆盖它。该选项通过 `cbvCore`、`cbvEntry`、
  `cbvGoal` 和 `cbvDecideGoal`。

- [#12782](https://github.com/leanprover/lean4/pull/12782)
  为磨环包络中的 `OfSemiring.Q` 实例添加高优先级。导入 Mathlib 时，`OfSemiring.Q Nat` 等类型的实例合成变得非常昂贵，因为求解器在找到正确的实例之前会探索许多不相关的路径。通过将这些实例标记为高优先级并添加基本操作的快捷方式实例（`Add`、`Sub`、`Mul`、`Neg`、`OfNat`、`NatCast`、`IntCast`、`HPow`），实例合成可解决快点。

- [#12773](https://github.com/leanprover/lean4/pull/12773)
  将 `at` 位置语法添加到 `cbv`策略，匹配 `simp at` 的接口。此前`cbv`只能降低目标；现在它支持 `cbv at h`、`cbv at h |-` 和 `cbv at *`。

- [#12766](https://github.com/leanprover/lean4/pull/12766)
  为 `Decidable.decide` 添加专用的 cbv simproc，它直接匹配 `isTrue`/`isFalse` 实例，生成更简单的证明项，并避免通过 `Decidable.rec` 进行不必要的展开。

- [#12677](https://github.com/leanprover/lean4/pull/12677)
  通过替换对 `Decidable.decide` 的调用，更改了 `simpIteCbv` 和 `simpDIteCbv` 中的方法
  在 `isTrue`/`isFalse` 的 `Decidable` 实例上减少并直接使用模式匹配。这会产生更简单的证明项。

- [#12763](https://github.com/leanprover/lean4/pull/12763)
  将预传递 simprocs `simpOr` 和 `simpAnd` 添加到 `cbv`策略，首先仅评估 `Or`/`And` 的左侧参数，在确定结果而不评估右侧时短路。以前，`cbv` 通过同余处理 `Or`/`And`，它始终评估两个参数。对于像 `decide (m < n ∨ expensive)` 这样的表达式，当 `m < n` 为 true 时，现在会完全跳过昂贵的右侧。

- [#12607](https://github.com/leanprover/lean4/pull/12607)
  修复了 `withLocation` 未保存信息上下文的问题，这意味着使用 `at *` 位置语法并执行术语精化的策略将保存信息树但恢复元上下文，从而导致 Infoview 消息，例如“更新错误：获取目标时出错：Rpc 错误：内部错误：未知元变量”（如果策略在某些位置失败，但在其他位置成功。

```

# 编译器
%%%
tag := "zh-releases-v4-30-0-h018"
%%%

```markdown

- [#13270](https://github.com/leanprover/lean4/pull/13270)
  添加了 `Runtime.hold`，这通过保存对它的引用来确保其参数在调用站点之前保持活动状态。这对于依赖于直到程序中某个点之后才释放的 Lean 对象的不安全代码（例如 FFI）非常有用。

- [#13392](https://github.com/leanprover/lean4/pull/13392)
  修复了 `lean_io_prim_handle_read` 中的堆缓冲区溢出问题，该溢出问题是通过
  分配大小计算中的整数溢出。此外，它还放置了几个检查的
  对所有相关分配路径进行算术运算，以消除未来潜在的溢出
  相反，会导致崩溃。现在，有问题的代码会抛出内存不足错误。

- [#13152](https://github.com/leanprover/lean4/pull/13152)
  通知 RC 优化器，标记值也可以被视为“借用”，因为我们不需要将它们视为借用分析的自有值（它们当然没有实际借用的分配）。

- [#13136](https://github.com/leanprover/lean4/pull/13136)
  将 RC 操作合并到 RC 优化器中。每当我们对一个基本块内的单个值执行多个 `inc` 时，在第一个 `inc` 侧立即执行所有这些 `inc` 是合法的。出现这种情况是因为该值至少在最后一个 `inc` 之前一直保持活动状态，因此永远无法通过 `RC=1` 观察到。因此，`inc` 位置的这种变化绝不会破坏重用机会。

- [#13147](https://github.com/leanprover/lean4/pull/13147)
  修复了代码生成器中处理 `Array.get!Internal` 时的理论漏洞。
  目前，代码生成器假定 `get!Internal` 返回的值源自
  `Array` 论证。然而，这通常不成立，因为我们也可能返回 `Inhabited`
  发生越界访问时的值（回想一下，我们在恐慌后继续执行
  默认）。这意味着我们有时会将 `Array.get!Internal` 转换为
  `Array.get!InternalBorrowed` 当我们不被允许这样做时，因为在恐慌情况下
  `Inhabited` 实例可以被返回，如果它是一个拥有的值，它将泄漏。

- [#13138](https://github.com/leanprover/lean4/pull/13138)
  引入 `weak_specialize` 属性。与 `nospecialize` 属性不同，它不
  完全用此类型标记的参数的块专门化。相反，`weak_specialize`
  仅当另一个参数引起专门化时，参数才专门化。如果没有这样的
  参数存在，它们被视为 `nospecialize`。

- [#13118](https://github.com/leanprover/lean4/pull/13118)
  修复了 `--load-dynlib` 与模块系统的不兼容性。

- [#13116](https://github.com/leanprover/lean4/pull/13116)
  确保从常量中读取在借用推理分析中算作借用。这可以减少持续读取时的 RC 压力。

- [#13094](https://github.com/leanprover/lean4/pull/13094)
  将核心中标记为 `extern` 的所有函数的 `Inhabited` 参数标记为借用
  （恐慌数组访问器和 `panic!` 本身）。这反过来又会在整个过程中产生传递效应
  代码库，并将大多数（如果不是全部）`Inhabited` 参数提升为借用的函数。

- [#13097](https://github.com/leanprover/lean4/pull/13097)
  使编译器跟踪包含有关 `inc`/`dec` 类型的更多信息
  正在进行（`persistent`、`checked` 等）

- [#13066](https://github.com/leanprover/lean4/pull/13066)
  更改用户定义借用上下文中的前向和后向投影传播的行为。让它们“强制”覆盖（即也覆盖用户注释）的原因是用户注释的借用值可能会通过投影传递到重置重用中，因此必须具有准确的引用计数。不再需要这样做的原因是：
  1. 无论如何，转发永远不必强制，它只能影响 `let z := oproj x i` 中的 `z`，用户无法对其进行注释
  2. 不再需要向后，因为用户注释的前向传播器会阻止重置重用插入完全使用具有用户定义的借用注释的值。

- [#13064](https://github.com/leanprover/lean4/pull/13064)
  告知借用推论，如果借用 `Array` 并且我们对其进行索引，那么我们获得的值实际上也是借用的值。这有助于改进在包含数组（例如尝试或持久哈希映射）的链接结构上递归的操作的 ABI。

- [#12942](https://github.com/leanprover/lean4/pull/12942)
  将 `ReaderT` 的上下文参数标记为借用，从而导致有用的借用注释在整个元堆栈中广泛传播，从而减少了 RC 压力。这引入了一个重要的新行为：修改 `ReaderT` 上下文时，例如通过 `withReader` 这几乎总是会导致分配。鉴于 `ReaderT` 上下文经常以非线性方式使用，无论如何我们认为这是可接受的行为。

- [#13052](https://github.com/leanprover/lean4/pull/13052)
  修复了与 `export` 注释相关的借用推理中的错误。

- [#13017](https://github.com/leanprover/lean4/pull/13017)
  确保当声明标记为 `@[export]` 时，编译器在以下情况下抛出错误
  它的任何参数都被标记为借用。

- [#12971](https://github.com/leanprover/lean4/pull/12971)
  将 Lean 的默认堆栈大小（包括 Lean 可执行文件的主线程）增加至 1GB。

- [#12830](https://github.com/leanprover/lean4/pull/12830)
  启用对尊重用户提供的借用注释的支持。这允许用户使用 `(x : @&Ty)` 标记其定义或本地函数的参数，并让借用推理尽力保留此注释，从而可能减少 RC 压力。请注意，在某些情况下这可能是不可能的。例如，编译器优先考虑保留尾调用而不是保留借用注释。可以使用 `trace.Compiler.inferBorrow` 获得编译器选择做出推理决策的精确推理。

- [#12952](https://github.com/leanprover/lean4/pull/12952)
  确保当函数标记为 `export` 时，其借用注释（如果存在）始终被忽略。

- [#12930](https://github.com/leanprover/lean4/pull/12930)
  将 `set_option compiler.ignoreBorrowAnnotation true in` 置于所有 `export`/`extern` 上
  对。这是必要的，因为 `export` 强制所有参数作为拥有的参数传递，而 `extern`
  尊重借用注释。目前 `export`/`extern` 技巧的方法总是被打破
  但从未浮出水面。然而，随着即将发生的变化，许多 `export`/`extern` 对将被
  受借用注释的影响，如果没有这个注释就会崩溃。

- [#12886](https://github.com/leanprover/lean4/pull/12886)
  添加了对忽略用户定义的借用注释的支持。这在定义时很有用
  `extern`/`export` 对，因为 `extern` 在 `export` 中时可能会受到借用注释的感染
  他们已经被忽视了。

- [#12781](https://github.com/leanprover/lean4/pull/12781)
  将 C 发射通道从 IR 移植到 LCNF，标志着 IR/LCNF 转换的最后一步，从而通过新的编译基础设施实现端到端代码生成。

- [#12850](https://github.com/leanprover/lean4/pull/12850)
  优化 `match_same_ctor.het` 的处理，使其发出良好的匹配树，而不是未优化的 CPS 样式代码。

- [#12539](https://github.com/leanprover/lean4/pull/12539)
  用 `Lean.Compiler.NameDemangling` 中的单一事实来源替换了三个独立的名称重组实现（Lean、C++、Python）。新模块处理完整的管道：前缀解析（`l_`、`lp_`、`_init_`、`initialize_`、`lean_apply_N`、`_lean_main`）、后处理（后缀标志、私有名称剥离、卫生后缀剥离、专业化）上下文）、回溯行解析以及通过 `@[export]` 进行 C 导出。

- [#12810](https://github.com/leanprover/lean4/pull/12810)
  在借用推理中添加跟踪，以向用户解释为什么得出结论。

- [#12796](https://github.com/leanprover/lean4/pull/12796)
  修复了当 `uv_tcp_accept` 受到多个线程争用时的死锁。

- [#12795](https://github.com/leanprover/lean4/pull/12795)
  修复了在 `lean_uv_dns_get_name` 错误路径上触发的内存泄漏

- [#12790](https://github.com/leanprover/lean4/pull/12790)
  使编译器删除无效的连接点的参数，避免一堆死的
  存储在字节码和初始 C 中（尽管 LLVM 肯定能够进一步优化它们）
  已经下线了）。

- [#12759](https://github.com/leanprover/lean4/pull/12759)
  将 `inlineCandidate?` 内的 `shouldInline` 函数中的 `isImplicitReducible` 检查替换为 `Meta.isInstance`。

- [#12724](https://github.com/leanprover/lean4/pull/12724)
  实现对将简单的地面数组文字提取到静态初始化数据中的支持。

- [#12727](https://github.com/leanprover/lean4/pull/12727)
  为装箱标量值实现简单的地面文字提取。

- [#12715](https://github.com/leanprover/lean4/pull/12715)
  确保编译器将 `Array`/`ByteArray`/`FloatArray` 文字提取为一个大的封闭项，以避免封闭项初始化时的二次开销。

- [#12705](https://github.com/leanprover/lean4/pull/12705)
  将简单的基础表达提取过程从 IR 移植到 LCNF。

- [#12665](https://github.com/leanprover/lean4/pull/12665)
  将扩展重置/重用通道从 IR 移植到 LCNF。此外，与旧代码不同，它可以防止指数代码生成。这导致二进制文件大小减少约 15%，并且整体速度略有加快。

- [#12687](https://github.com/leanprover/lean4/pull/12687)
  实现扩展复位重用过程所需的 LCNF 指令。

- [#12663](https://github.com/leanprover/lean4/pull/12663)
  当声明被显式标记为不可专业化时，避免在模块系统下出现有关专业化限制的误报错误消息。它还可以提供一些较小的公共规模并重建储蓄。

```

# 漂亮的印刷
%%%
tag := "zh-releases-v4-30-0-h019"
%%%

````markdown

- [#10384](https://github.com/leanprover/lean4/pull/10384)
  makes notations such as `∨`, `∧`, `≤`, and `≥` pretty print using ASCII versions when `pp.unicode` is false.

- [#12745](https://github.com/leanprover/lean4/pull/12745)
  fixes `pp.fvars.anonymous` to display loose free variables as `_fvar._` instead of `_` when the option is set to `false`. This was the intended behavior in https://github.com/leanprover/lean4/pull/12688 but the fix was committed locally and not pushed before that PR was merged.

- [#12688](https://github.com/leanprover/lean4/pull/12688)
  adds a `pp.fvars.anonymous` option (default `true`) that controls the display of loose free variables (fvars not in the local context).

- [#12654](https://github.com/leanprover/lean4/pull/12654)
  fixes two aspects of pretty printing of private names.
  1. Name unresolution. Now private names are not special cased: the private prefix is stripped off and the `_root_` prefix is added, then it tries resolving all suffixes of the result. This is sufficient to handle imported private names in the new module system. (Additionally, unresolution takes macro scopes into account now.)
  2. Delaboration. Inaccessible private names use a deterministic algorithm to convert private prefixes into macro scopes. The effect is that the same private name appearing in multiple times in the same delaborated expression will now have the same `✝` suffix each time. It used to use fresh macro scopes per occurrence.

- [#12606](https://github.com/leanprover/lean4/pull/12606)
  adds the pretty printer option `pp.mdata`, which causes the pretty printer to annotate terms with any metadata that is present. For example,
  ```lean
  set_option pp.mdata true
  /-- 信息: [mdata noindex:true] 2 : Nat -/
  #guard_msgs in #check no_index 2
  ```

````

# 文档
%%%
tag := "zh-releases-v4-30-0-h020"
%%%

```markdown

- [#13115](https://github.com/leanprover/lean4/pull/13115)
  更新 `inferInstanceAs` 文档字符串以反映当前行为：它需要
  上下文中的预期类型，不应用作简单的 `inferInstance` 同义词。的
  旧示例 (`#check inferInstanceAs (Inhabited Nat)`) 不再有效，因此已被替换
  其中一个演示了预期的运输用例。

- [#13065](https://github.com/leanprover/lean4/pull/13065)
  重写 `Lean.ReducibilityHints` 上的文档字符串以准确描述
  内核的惰性增量减少策略：比较两个时哪一侧展开
  定义、如何计算定义高度以及提示如何与
  `@[reducible]`/`@[irreducible]`精化器属性。

- [#12959](https://github.com/leanprover/lean4/pull/12959)
  修复了文档字符串中的一系列错误。

```

# 服务器
%%%
tag := "zh-releases-v4-30-0-h021"
%%%

```markdown

- [#12948](https://github.com/leanprover/lean4/pull/12948)
  将 `RequestCancellationToken` 从 `IO.Ref` 移动到 `IO.CancelToken`。

- [#12905](https://github.com/leanprover/lean4/pull/12905)
  调整来自 `{"p": "n"}` to `{"__rpcref": "n"}`. Existing clients will continue to work unchanged, but should eventually move to the new format by advertising the `rpcWireFormat` 客户端功能的 RPC 引用的 JSON 编码。

```

# Lake
%%%
tag := "zh-releases-v4-30-0-h022"
%%%

```markdown

- [#13683](https://github.com/leanprover/lean4/pull/13683)
  将已编译的 Lake 配置（例如 `lakefile.olean`）从包的 `.lake/config` 目录移动到工作区的 `.lake/config`。这消除了共享依赖项的工作区之间潜在的源争用。

- [#13600](https://github.com/leanprover/lean4/pull/13600)
  修复了 Lake 问题，其中 `meta import` 的传递导入的 IR 未包含在提供给 Lean 的导入工件 Lake 中（例如，通过 `--setup`）。使用 Lake 工件缓存时，可能会由于缺少 IR 而产生“丢失数据文件”错误。

- [#13164](https://github.com/leanprover/lean4/pull/13164)
  将 `lake cache get` 更改为在单个批量 POST 请求中从 Reservoir 获取工件云存储 URL，而不是依赖于每个工件的 HTTP 重定向。下载许多工件时，基于重定向的方法会将每个工件发送一个请求到 Reservoir Web 主机 (Netlify)，这可能很慢，并且有达到速率限制的风险。批量端点会立即返回所有 URL，因此，curl 之后仅与 CDN 通信。

- [#13151](https://github.com/leanprover/lean4/pull/13151)
  如果进程以非零返回代码退出，则将 `Lake.proc` 更改为始终将进程输出记录为 `info`。这样，它在出现错误时的行为与 `captureProc` 相同。

- [#13144](https://github.com/leanprover/lean4/pull/13144)
  添加了三个用于分阶段缓存上传的新 `lake cache` 子命令：`stage`、`unstage` 和 `put-staged`。这些命令的设计目的是与 Mathlib 的 `lake exe cache` 中的同名命令并行。

- [#13141](https://github.com/leanprover/lean4/pull/13141)
  更改 Lake 的具体化过程，以在更新依赖项存储库时运行删除跟踪目录中的未跟踪文件（通过 `git clean -xf`）。这可确保源树中陈旧的残留物被删除。

- [#13110](https://github.com/leanprover/lean4/pull/13110)
  修复了 `Cache.saveArtifact` 中的竞争条件，当两个库方面（例如 `static` 和 `static.export`）生成具有相同内容哈希的工件并尝试同时缓存它们时，该竞争条件会导致间歇性“权限被拒绝”错误。

- [#13028](https://github.com/leanprover/lean4/pull/13028)
  添加了拒绝 Lake 配置的检查，其中多个可执行文件共享相同的根模块名称。以前，Lake 会静默编译一次根模块并将其链接到所有可执行文件中，无论 `srcDir` 设置如何不同，都会生成相同的二进制文件。

- [#13014](https://github.com/leanprover/lean4/pull/13014)
  使 `lake cache get` / `lake cache put` 工件中的错误传输更加详细，这有助于调试。它还修复了按需下载工件时的错误报告问题。

- [#12993](https://github.com/leanprover/lean4/pull/12993)
  修复了 Lake 的错误，如果 `restoreAllArtifacts` 也是 `true`，则缓存通过 `lake build -o` 生成的 `ltar` 将失败。

- [#12974](https://github.com/leanprover/lean4/pull/12974)
  更改 `lake cache get` 和 `lake cache put` 以在上传或急切下载工件时并行传输工件（使用 `curl --parallel`）。传输仍被一一记录在输出中——还没有进度表。

- [#12957](https://github.com/leanprover/lean4/pull/12957)
  修复了 #12540 引入的 macOS 上的构建失败。 macOS BSD `ar` 不支持 #12540 无条件启用的 `@file` 响应文件语法。在 macOS 上，构建核心（即 `bootsrap := true`）时，`recBuildStatic` 现在使用 `libtool -static -filelist`，它可以本机处理长参数列表。

- [#12954](https://github.com/leanprover/lean4/pull/12954)
  更改 Lake `CacheMap` 数据结构以跟踪输出的平台依赖性。与平台无关的包将不再在 `lake build -o` 生成的输出文件中包含与平台相关的映射。

- [#12540](https://github.com/leanprover/lean4/pull/12540)
  将 Lake 对响应文件 (`@file`) 的使用从仅限 Windows 扩展到所有平台，从而避免在使用多个对象文件调用 `clang`/`ar` 时的 `ARG_MAX` 限制。

- [#12935](https://github.com/leanprover/lean4/pull/12935)
  添加了 `fixedToolchain` Lake 封装配置选项。将其设置为 `true` 会通知 Lake 该软件包仅在单个工具链上运行（如 Mathlib）。这会导致 Lake 的工具链更新过程优先考虑其工具链，并避免需要按 Lake 缓存中的工具链版本分离包的输入到输出映射。

- [#12914](https://github.com/leanprover/lean4/pull/12914)
  使用 `leantar` 将模块工件添加到 `.ltar` 存档中。

- [#12927](https://github.com/leanprover/lean4/pull/12927)
  将 `lake cache get` 更改为默认下载工件。可以使用新的 `--mappings-only` 选项按需下载工件（`--download-arts` 现已过时）。

- [#12837](https://github.com/leanprover/lean4/pull/12837)
  更改 `restoreAllArtifacts` 包配置的默认行为以镜像工作区的默认行为。如果工作区也未设置它，则默认值保持不变 (`false`)。

- [#12835](https://github.com/leanprover/lean4/pull/12835)
  如果普通跟踪文件已存在，则将 Lake 更改为仅发出 `.nobuild` 跟踪（在 #12076 中引入）。这修复了 `lake build --no-build` 将创建构建目录并从而阻止未来构建中的云发布获取的问题。

- [#12799](https://github.com/leanprover/lean4/pull/12799)
  更改 Lake 以使用跟踪的修改时间（如果可用）作为工件修改时间。

- [#12634](https://github.com/leanprover/lean4/pull/12634)
  使 Lake 能够按需从远程缓存服务下载工件，作为 `lake build` 的一部分。它还重构了大部分缓存 API 以使其类型更加安全。

```

# 其他
%%%
tag := "zh-releases-v4-30-0-h023"
%%%

```markdown

- [#13499](https://github.com/leanprover/lean4/pull/13499)
  修复了 Linux aarch64 上 `leantar` 的架构检测，确保其与 Lean 正确捆绑。

- [#12865](https://github.com/leanprover/lean4/pull/12865)
  修复了存储库使用时 release_checklist.py 中的崩溃
  `leanprover/lean4-nightly:` 工具链前缀（例如，leansqlite）。的
  `is_version_gte` 功能仅检查 `leanprover/lean4:nightly-`，但
  不是 `leanprover/lean4-nightly:`，导致“ValueError：无效文字”
  int() 以 10 为基数： 'nightly'` 尝试解析版本时。

- [#12963](https://github.com/leanprover/lean4/pull/12963)
  修复了应用于仅标头文件且不带尾随换行符时 `lake shake` 中的恐慌

- [#12836](https://github.com/leanprover/lean4/pull/12836)
  添加了 `lake-ci` 标签，可在 CI 中启用完整的 Lake 测试套件，
  避免需要临时提交和恢复更改
  `tests/CMakeLists.txt`。 `lake-ci` 标签暗示 `release-ci`（检查级别
  3），所以所有的发布平台也都经过测试。

- [#12822](https://github.com/leanprover/lean4/pull/12822)
  下载 `leantar` 的预构建版本，并将其与 Lean 捆绑在一起作为核心构建的一部分。

- [#12700](https://github.com/leanprover/lean4/pull/12700)
  修复了导致 `-DLEAN_VERSION_*` 覆盖无效的 CMake 作用域错误。

- [#12638](https://github.com/leanprover/lean4/pull/12638)
  将四个轻量级工作流程从 `pull_request` 切换为
  `pull_request_target` 阻止 GitHub 在以下情况下需要手动批准：
  `mathlib-lean-pr-testing[bot]` 应用程序触发标签事件（例如添加
  `builds-mathlib`)。由于机器人永远不会向 master 提交提交，因此
  永远被视为“首次贡献者”，并且每个 `pull_request`
  它触发的事件需要批准。 `pull_request_target` 事件始终运行
  未经批准，因为他们执行来自基础分支的可信代码。

- [#12682](https://github.com/leanprover/lean4/pull/12682)
  使用仅最小化特定模块的标志扩展 `lake shake`

- [#12648](https://github.com/leanprover/lean4/pull/12648)
  添加了实验性的 `idbg e`，这是一种新的 do 元素（和术语）语法，用于在语言服务器和正在运行的编译的 Lean 程序之间进行实时调试。

```
