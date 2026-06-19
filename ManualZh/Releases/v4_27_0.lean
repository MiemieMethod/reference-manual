/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown
import Std.Data.Iterators
import Std.Data.TreeMap

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Std.Iterators
open Std (TreeMap)
open Std (Iterator Iter IterM IteratorLoop)
open Std (HashMap)
open Std (Iter IterM IteratorLoop)

#doc (Manual) "Lean 4.27.0 (2026-01-24)" =>
%%%
tag := "release-v4.27.0"
file := "v4.27.0"
%%%

此版本有 372 项更改。除了下面列出的 118 项功能添加和 71 项修复之外，还有 28 项重构更改、13 项文档改进、25 项性能改进、6 项测试套件改进和 111 项其他更改。

# 亮点

## 模块系统稳定

[#11637](https://github.com/leanprover/lean4/pull/11637) 声明模块系统不再是实验性的，并使 {option}`experimental.module` 选项成为无操作。

有关文档，请参阅参考手册中的 {ref "module-scopes"}[模块和可见性] 部分。

## 向后兼容性选项

[#11304](https://github.com/leanprover/lean4/pull/11304) 记录 `backward.*` 选项只是临时的
移民辅助工具，可能会在 6 个月后消失，恕不另行通知
经过他们的介绍。如果用户依赖的话，请举报
关于这些选项。

## 性能提升

此版本包含许多性能改进，特别是：

- [#11162](https://github.com/leanprover/lean4/pull/11162) 减少语言服务器的内存消耗（
  特别是看门狗进程）。在Mathlib中，它减少了内存
  消耗约1GB。

- [#11507](https://github.com/leanprover/lean4/pull/11507) 优化导入期间的文件系统访问，获得约 3% 的胜利
  在 Linux 上，其他平台上可能有更多。

## 错误信息

此版本包含对错误消息的一系列更改，旨在使其更加有用和可操作。
具体来说，一些消息现在有提示、建议和解释链接。

公关：
[#11119](https://github.com/leanprover/lean4/pull/11119),
[#11245](https://github.com/leanprover/lean4/pull/11245),
[#11346](https://github.com/leanprover/lean4/pull/11346),
[#11347](https://github.com/leanprover/lean4/pull/11347),
[#11456](https://github.com/leanprover/lean4/pull/11456),
[#11482](https://github.com/leanprover/lean4/pull/11482),
[#11518](https://github.com/leanprover/lean4/pull/11518),
[#11554](https://github.com/leanprover/lean4/pull/11554),
[#11555](https://github.com/leanprover/lean4/pull/11555),
[#11621](https://github.com/leanprover/lean4/pull/11621)。

## 研磨的新功能

### 函数值同余闭包

[#11323](https://github.com/leanprover/lean4/pull/11323) 引入了新的 {tactic}`grind` 选项 `funCC`（默认启用），
它将同余闭包扩展到函数值相等。当
`funCC` 已启用，`grind` 跟踪*部分应用的等式
函数*，允许推理步骤，例如：

```
a : Nat → Nat
f : (Nat → Nat) → (Nat → Nat)
h : f a = a
⊢ (f a) m = a m

g : Nat → Nat
f : Nat → Nat → Nat
h : f a = g
⊢ f a b = g b
```

此功能大大提高了 `grind` 对高阶和高阶的支持
部分应用函数等式，同时保持与
禁用 `funCC` 时的一阶 SMT 行为。

有关使用的更多详细信息，请参阅 PR 描述。

### 控制定理实例化

[#11428](https://github.com/leanprover/lean4/pull/11428) 在 {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` 中实现对 *guards* 的支持。新的
功能提供了对定理实例化的额外控制。对于
例如，考虑以下单调性定理：

```lean
opaque f : Nat → Nat
theorem fMono : x ≤ y → f x ≤ f y := sorry
```

通过新的 `guard` 功能，我们可以指示 {tactic}`grind` 实例化
theorem *only if* `x ≤ y` is already known to be true in the current `grind` state:

```lean
grind_pattern fMono => f x, f y where
  guard x ≤ y
  x =/= y
```

这可以显着减少定理实例化的数量。

有关更详细的讨论和示例证明跟踪，请参阅 PR 描述。

### 提供任意参数

[#11268](https://github.com/leanprover/lean4/pull/11268) 实现对任意 {tactic}`grind` 参数的支持。特点
与 {tactic}`simp` 中提供的类似，其中处理证明项
作为局部宇宙多态引理。此功能依赖于 `grind -revert`（请参阅 [#11248](https://github.com/leanprover/lean4/pull/11248)）。
例如，用户现在可以编写：

```lean
def snd (p : α × β) : β := p.2
theorem snd_eq (a : α) (b : β) : snd (a, b) = b := rfl

/--
trace: [grind.ematch.instance] snd_eq (a + 1): snd (a + 1, Type) = Type
[grind.ematch.instance] snd_eq (a + 1): snd (a + 1, true) = true
-/
#guard_msgs (trace) in
set_option trace.grind.ematch.instance true in
example (a : Nat) :
    (snd (a + 1, true), snd (a + 1, Type), snd (2, 2)) =
    (true, Type, snd (2, 2)) := by
  grind [snd_eq (a + 1)]
```

请注意，在上面的示例中，`snd_eq` 仅实例化两次，但具有不同的 Universe 参数。

### 研磨回复

[#11248](https://github.com/leanprover/lean4/pull/11248) 实现选项 `revert`，该选项设置为 `false`
默认。

这是与还原假设相关的内部变化。
使用新的默认值，{tactic}`grind` 生成的迹线、反例和证明项有所不同。
要恢复旧的 `grind` 行为，请使用 `grind +revert`。

### Grind 的其他新功能

- `grind ring` 中的 `BitVec` 支持 ([#11639](https://github.com/leanprover/lean4/pull/11639))
  和 `grind lia` ([#11640](https://github.com/leanprover/lean4/pull/11640));

- 新配置选项 `grind -reducible`，允许扩展不可简化声明
  在 定义等价 测试期间（[#11480](https://github.com/leanprover/lean4/pull/11480)）；

- 支持异构构造函数单射性（[#11491](https://github.com/leanprover/lean4/pull/11491)）；

- 支持 `LawfulOfScientific` 类 ([#11331](https://github.com/leanprover/lean4/pull/11331))；

- `grind`策略块内的语法 `use [ns Foo]` 和 `instantiate only [ns Foo]`，
  它具有激活所有范围内的研磨模式的效果
  namespace ([#11335](https://github.com/leanprover/lean4/pull/11335));

- 新的 `grind_pattern` 约束（[#11405](https://github.com/leanprover/lean4/pull/11405) 和
  [#11409](https://github.com/leanprover/lean4/pull/11409))。

## 良基递归上 `Nat`

使用良基递归的定义通常是不可约的。
对于 [#7965](https://github.com/leanprover/lean4/pull/7965)，当终止措施的类型为 {name}`Nat` 时，
这样的定义可以减少，并且接受显式的 `@[semireducible]` 注释
没有通常的警告。

## 图书馆亮点

此版本完成了 {name}`String` API 的修订，包括相关类型的 {name}`String.Pos`、
对 {name}`String.Slice` 的完整 API 支持，以及使用新的 `Iterator` API 的迭代器。
{name}`TreeMap`/{name}`HashMap` API 还添加了许多内容，包括交集、差值和相等。

这些更新包括一些“重大更改”，即：

- [#11180](https://github.com/leanprover/lean4/pull/11180) 重新定义了 {name}`String.take` 和要操作的变体
  {name}`String.Slice`。虽然以前的函数返回一个子字符串
  输入有时返回 {name}`String` 有时返回
  {name}`Substring.Raw`，他们现在统一返回{name}`String.Slice`。

  这是一个重大变化，因为现在许多函数都有不同的
  返回类型。例如，如果 `s` 是一个字符串，而 `f` 是一个函数
  接受字符串，`f (s.drop 1)` 将不再编译，因为
  `s.drop 1` 是 `String.Slice`。要解决此问题，请插入对 `copy` 的调用
  恢复旧行为：`f (s.drop 1).copy`。

  当然，很多情况下，还会有更高效的选择。对于
  例如，不要写 `f <| s.drop 1 |>.copy |>.dropEnd 1 |>.copy`，写
  改为 `f <| s.drop 1 |>.dropEnd 1 |>.copy`。另外，代替`(s.drop
  1).copy = "Hello"`, write `s.drop 1 == "Hello".toSlice`.

## 重大变化

- [#11474](https://github.com/leanprover/lean4/pull/11474) 和
  [11562](https://github.com/leanprover/lean4/pull/11562)
  将 `noConfusion` 结构推广到异构
  等式（假设参数和索引之间的命题等价）。
  对于使用 `noConfusion` 原理的人来说，这是一个重大变化
  对于带有索引的类型手动并显式地
  传递合适的 `rfl` 参数，并根据需要对结果等式使用 `eq_of_heq`。

- [#11490](https://github.com/leanprover/lean4/pull/11490) 防止嵌套 `simp` 中的 `try` 吞咽心跳错误
  调用，更一般地确保 `isRuntime` 标志通过
  `throwNestedTacticEx`。这可以防止证明的行为（特别是
  使用 `aesop` 的用户）受到当前递归深度的影响或
  心跳限制。
  这会破坏 Mathlib 中的单个调用者，其中 `simp` 使用引理
  形成 `x = f (g x)` 和堆栈溢出，可以通过以下方式修复
  概括 `g x`。

# 语言

````markdown

* [#7965](https://github.com/leanprover/lean4/pull/7965) lets recursive functions defined by well-founded recursion use a
  different `fix` function when the termination measure is of type `Nat`.
  This fix-point operator use structural recursion on “fuel”, initialized
  by the given measure, and is thus reasonable to reduce, e.g. in `by
  decide` proofs.

* [#11196](https://github.com/leanprover/lean4/pull/11196) avoids match splitter calculation from testing all quadratically
  many pairs of alternatives for overlaps, by keeping track of possible
  overlaps during matcher calculation, storing that information in the
  `MatcherInfo`, and using that during matcher calculation.

* [#11200](https://github.com/leanprover/lean4/pull/11200) changes how sparse case expressions represent the
  none-of-the-above information. Instead of many `x.ctorIdx ≠ i`
  hypotheses, it introduces a single `Nat.hasNotBit mask x.ctorIdx`
  hypothesis which compresses that information into a bitmask. This avoids
  a quadratic overhead during splitter generation, where all n assumptions
  would be refined through `.subst` and `.cases` constructions for all n
  assumption of the splitter alternative.

* [#11221](https://github.com/leanprover/lean4/pull/11221) lets `realizeConst` use `withDeclNameForAuxNaming` so that
  auxiliary definitions created there get non-clashing names.

* [#11222](https://github.com/leanprover/lean4/pull/11222) implements `elabToSyntax` for creating scoped syntax `s :
  Syntax` for an arbitrary elaborator `el : Option Expr -> TermElabM Expr`
  such that `elabTerm s = el`.

* [#11236](https://github.com/leanprover/lean4/pull/11236) extracts two modules from `Match.MatchEqs`, in preparation of
  #11220
  and to use the module system to draw clear boundaries between concerns
  here.

* [#11239](https://github.com/leanprover/lean4/pull/11239) adds a `Unit` assumption to alternatives of the splitter that
  would otherwise not have arguments. This fixes #11211.

* [#11245](https://github.com/leanprover/lean4/pull/11245) improves the error message encountered in the case of a type
  class instance resolution failure, and adds an error explanation that
  discusses the common new-user case of binary operation overloading and
  points to the `trace.Meta.synthInstance` option for advanced debugging.

* [#11256](https://github.com/leanprover/lean4/pull/11256) replaces `MatcherInfo.numAltParams` with a more detailed data
  structure that allows us, in particular, to distinguish between an
  alternative for a constructor with a `Unit` field and the alternative
  for a nullary constructor, where an artificial `Unit` argument is
  introduced.

* [#11261](https://github.com/leanprover/lean4/pull/11261) continues the homogenization between matchers and splitters,
  following up on #11256. In particular it removes the ambiguity whether
  `numParams` includes the `discrEqns` or not.

* [#11269](https://github.com/leanprover/lean4/pull/11269) adds support for decidable equality of empty lists and empty
  arrays. Decidable equality for lists and arrays is suitably modified so
  that all diamonds are definitionally equal.

* [#11292](https://github.com/leanprover/lean4/pull/11292) adds intersection operation on
  `ExtDTreeMap`/`ExtTreeMap`/`ExtTreeSet` and proves several lemmas about
  it.

* [#11301](https://github.com/leanprover/lean4/pull/11301) allows setting reducibilityCoreExt in async contexts (e.g. when
  using `mkSparseCasesOn` in a realizable definition)

* [#11302](https://github.com/leanprover/lean4/pull/11302) renames the CTests tests to use filenames as test names. So
  instead of
  ```
          2080-leanruntest_issue5767.lean（失败）
  ```
  we get
  ```
          2080 - 测试/Lean/运行/issue5767.lean（失败）
  ```
  which allows Ctrl-Click’ing on them in the VSCode terminal.

* [#11303](https://github.com/leanprover/lean4/pull/11303) renames rename wrongly named `backwards.` options to
  `backward.`

* [#11304](https://github.com/leanprover/lean4/pull/11304) documents that `backward.*` options are only temporary
  migration aids and may disappear without further notice after 6 months
  after their introduction. Users are kindly asked to report if they rely
  on these options.

* [#11305](https://github.com/leanprover/lean4/pull/11305) removes the `group` field from option descriptions. It is
  unused, does not have a clear meaning and often matches the first
  component of the option name.

* [#11307](https://github.com/leanprover/lean4/pull/11307) removes all code that sets the `Option.Decl.group` field, which
  is unused and has no clearly documented meaning.

* [#11325](https://github.com/leanprover/lean4/pull/11325) adds `CoreM.toIO'`, the analogue of `CoreM.toIO` dropping the
  state from the return type, and similarly for `TermElabM.toIO'` and
  `MetaM.toIO'`.

* [#11333](https://github.com/leanprover/lean4/pull/11333) adds infrastructure for parallel execution across Lean's tactic
  monads.

* [#11338](https://github.com/leanprover/lean4/pull/11338) upstreams the `with_weak_namespace` command from Mathlib:
  `with_weak_namespace <id> <cmd>` changes the current namespace to `<id>`
  for the duration of executing command `<cmd>`, without causing scoped
  things to go out of scope. This is in preparation for upstreaming the
  `scoped[Foo.Bar]` syntax from Mathlib, which will be useful now that we
  are adding `grind` annotations in scopes.

* [#11346](https://github.com/leanprover/lean4/pull/11346) modifies the error message for type synthesis failure for the
  case where the type class in question is potentially derivable using a
  `deriving` command. Also changes the error explanation for type class
  instance synthesis failure with an illustration of this pattern.

* [#11347](https://github.com/leanprover/lean4/pull/11347) adds a focused error explanation aimed at the case where someone
  tries to use Natural-Numbers-Game-style `induction` proofs directly in
  Lean, where such proofs are not syntactically valid.

* [#11353](https://github.com/leanprover/lean4/pull/11353) applies beta reduction to specialization keys, allowing us to
  reuse specializations in more situations.

* [#11379](https://github.com/leanprover/lean4/pull/11379) sets `@[macro_inline]` on the (trivial) `.ctorIdx` for inductive
  types with one constructor, to reduce the number of symbols generated by
  the compiler.

* [#11385](https://github.com/leanprover/lean4/pull/11385) lets implicit instance names avoid name clashes with private
  declarations. This fixes #10329.

* [#11408](https://github.com/leanprover/lean4/pull/11408) adds a difference operation on
  `ExtDTreeMap`/`ExtTreeMap`/`TreeSet` and proves several lemmas about it.

* [#11422](https://github.com/leanprover/lean4/pull/11422) uses a kernel-reduction optimized variant of `Mon.mul` in `grind`.

* [#11425](https://github.com/leanprover/lean4/pull/11425) changes `Lean.Order.CCPO` and `.CompleteLattice` to carry a
  Prop. This avoids the `CCPO IO` instance from being `noncomputable`.

* [#11432](https://github.com/leanprover/lean4/pull/11432) fixes a typo in the docstring of `#guard_mgs`.

* [#11453](https://github.com/leanprover/lean4/pull/11453) fixes undefined behavior where `delete` (instead of `delete[]`)
  is called on an object allocated with `new[]`.

* [#11456](https://github.com/leanprover/lean4/pull/11456) refines several error messages, mostly involving invalid
  use of field notation, generalized field notation, and numeric
  projection. Provides a new error explanation for field notation.

* [#11463](https://github.com/leanprover/lean4/pull/11463) fixes a panic in `getEqnsFor?` when called on matchers generated
  from match expressions in theorem types.

* [#11474](https://github.com/leanprover/lean4/pull/11474) generalizes the `noConfusion` constructions to heterogeneous
  equalities (assuming propositional equalities between the indices). This
  lays ground work for better support for applying injection to
  heterogeneous equalities in grind.

* [#11476](https://github.com/leanprover/lean4/pull/11476) adds a `` {givenInstance}`C` `` documentation role that adds an
  instance of `C` to the document's local assumptions.

* [#11482](https://github.com/leanprover/lean4/pull/11482) gives suggestions based on the currently-available constants
  when projecting from an unknown type.

* [#11485](https://github.com/leanprover/lean4/pull/11485) ensures that `Nat`s in `.olean` files use a deterministic
  serialization in the case where `LEAN_USE_GMP` is not set.

* [#11490](https://github.com/leanprover/lean4/pull/11490) prevents `try` swallowing heartbeat errors from nested `simp`
  calls, and more generally ensures the `isRuntime` flag is propagated by
  `throwNestedTacticEx`. This prevents the behavior of proofs (especially
  those using `aesop`) being affected by the current recursion depth or
  heartbeat limit.

* [#11492](https://github.com/leanprover/lean4/pull/11492) uses the helper functions withImplicitBinderInfos and
  mkArrowN in more places.

* [#11493](https://github.com/leanprover/lean4/pull/11493) makes `Match.MatchEqs` a leaf module, to be less restricted in
  which features we can use there.

* [#11502](https://github.com/leanprover/lean4/pull/11502) adds two benchmarks for elaborating match statements of many
  `Nat` literals, one without and one with splitter generation.

* [#11508](https://github.com/leanprover/lean4/pull/11508) avoids generating hyps when not needed (i.e. if there is a
  catch-all so no completeness checking needed) during matching on values.

  This tweak was made possible by #11220.

* [#11510](https://github.com/leanprover/lean4/pull/11510) avoids running substCore twice in caseValues.

* [#11511](https://github.com/leanprover/lean4/pull/11511) implements a linter that warns when a deprecated coercion is
  applied. It also warns when the `Option` coercion or the
  `Subarray`-to-`Array` coercion is used in `Init` or `Std`. The linter is
  currently limited to `Coe` instances; `CoeFun` instances etc. are not
  considered.

* [#11518](https://github.com/leanprover/lean4/pull/11518) provides an additional hint when the type of an autobound
  implicit is required to have function type or equality type — this
  fails, and the existing error message does not address the fact that the
  source of the error is an unknown identifier that was automatically
  bound.

* [#11541](https://github.com/leanprover/lean4/pull/11541) adds support for underscores as digit separators in
  String.toNat?, String.toInt?, and related parsing functions. This makes
  the string parsing functions consistent with Lean's numeric literal
  syntax, which already supports underscores for readability (e.g.,
  100_000_000).

* [#11554](https://github.com/leanprover/lean4/pull/11554) adds `@[suggest_for]` annotations to Lean, allowing lean to
  provide corrections for `.every` or `.some` methods in place of `.all`
  or `.any` methods for most default-imported types (arrays, lists,
  strings, substrings, and subarrays, and vectors).

* [#11555](https://github.com/leanprover/lean4/pull/11555) scans the environment for viable replacements for a dotted
  identifier (like `.zero`) and suggests concrete alternatives as
  replacements.

* [#11562](https://github.com/leanprover/lean4/pull/11562) makes the `noConfusion` principles even more heterogeneous, by
  allowing not just indices but also parameters to differ.

* [#11566](https://github.com/leanprover/lean4/pull/11566) lets the compiler treat per-constructor `noConfusion` like the
  general one, and moves some more logic closer to no confusion
  generation.

* [#11571](https://github.com/leanprover/lean4/pull/11571) lets `whnf` not consult `isNoConfusion`, to speed up this hot
  path a bit.

* [#11587](https://github.com/leanprover/lean4/pull/11587) adjusts the new `meta` keyword of the experimental module system
  not to imply `partial` for general consistency.

* [#11607](https://github.com/leanprover/lean4/pull/11607) makes argument-less tactic invocations of `Std.Do` tactics such
  as `mintro` emit a proper error message "`mintro` expects at least one
  pattern" instead of claiming that `Std.Tactic.Do` needs to be imported.

* [#11611](https://github.com/leanprover/lean4/pull/11611) fixes a `noConfusion` compilation introduced by #11562.

* [#11619](https://github.com/leanprover/lean4/pull/11619) allows Lean to present suggestions based on `@[suggest_for]`
  annotations for unknown identifiers without internal dots. (The
  annotations in #11554 only gave suggestion for dotted identifiers like
  `Array.every`->`Array.all` and not for bare identifiers like
  `Result`->`Except` or `ℕ`->`Nat`.)

* [#11620](https://github.com/leanprover/lean4/pull/11620) ports Batteries.WF to Init.WFC for executable well-founded
  fixpoints. It introduces `csimp` theorems to replace the recursors and
  non-executable definitions with executable definitions.

* [#11621](https://github.com/leanprover/lean4/pull/11621) causes Lean to search through `@[suggest_for]` annotations on
  certain errors that look like unknown identifiers that got incorrectly
  autobound. This will correctly identify that a declaration of type
  `Maybe String` should be `Option String` instead.

* [#11624](https://github.com/leanprover/lean4/pull/11624) fixes a SIGFPE crash on x86_64 when evaluating `INT_MIN / -1` or
  `INT_MIN % -1` for signed integer types.

* [#11637](https://github.com/leanprover/lean4/pull/11637) declares the module system as no longer experimental and makes
  the `experimental.module` option a no-op, to be removed.

* [#11644](https://github.com/leanprover/lean4/pull/11644) makes `.ctorIdx` not an abbrev; we don't want `grind` to unfold
  it.

* [#11645](https://github.com/leanprover/lean4/pull/11645) fixes the docstring of `propagateForallPropUp`. It was
  copy’n’pasta before.

* [#11652](https://github.com/leanprover/lean4/pull/11652) teaches `grind` how to reduce `.ctorIdx` applied to
  constructors. It can also handle tasks like
  ```
  xs ≍ Vec.cons x xs' → xs.ctorIdx = 1
  ```
  thanks to a `.ctorIdx.hinj` theorem (generated on demand).

* [#11657](https://github.com/leanprover/lean4/pull/11657) improves upon #11652 by keeping the kernel-reduction-optimized
  definition.

````

# 图书馆

```markdown

* [#8406](https://github.com/leanprover/lean4/pull/8406) 添加 `getElem_swapIfInBounds*` 形式的引理并弃用
  `getElem_swap'`。

* [#9302](https://github.com/leanprover/lean4/pull/9302) 修改 `Option.instDecidableEq` 和 `Option.decidableEqNone`
  这样后者就可以成为一个全局实例而不会导致
  钻石。它还添加了 `Option.decidableNoneEq`。

* [#10204](https://github.com/leanprover/lean4/pull/10204) 更改 `ForIn`、`ForIn'` 和 `ForM` 的接口
  类型类不采用 `Monad m` 参数。这是一个重大改变
  对于大多数下游 `instance`，现在需要假设
  `[Monad m]`。

* [#10945](https://github.com/leanprover/lean4/pull/10945) 添加了 `Std.Tricho r`，这是一个用于标识关系的类型类
  他们作为三分法。这优于 `Std.Antisymm (¬ r · ·)`
  所有情况（它相当于）。

* [#11038](https://github.com/leanprover/lean4/pull/11038) 引入了一个新的定点组合器，
  `WellFounded.extrinsicFix`。终止证明（如果提供的话）可以
  是从外部给出的，即从外部看该术语，并且
  仅当人们打算正式验证该行为时才需要
  固定点。然后将新的组合器应用于迭代器 API。
  `toList` 或 `ForIn` 等消费者不再需要证明
  底层迭代器是有限的。如果想确保终止
  从本质上讲，有严格的终止变体可用
  例如，`it.ensureTermination.toList` 而不是 `it.toList`。

* [#11112](https://github.com/leanprover/lean4/pull/11112) 在 `DHashMap`/`HashMap`/`HashSet` 上添加交集运算
  并提供了关于其行为的几个引理。

* [#11141](https://github.com/leanprover/lean4/pull/11141) 为切片和 MPL 提供多态 `ForIn` 实例
  使用 `for ... in` 对切片进行迭代的 `spec` 引理。它还
  提供专门用于 `Subarray` 的版本。

* [#11165](https://github.com/leanprover/lean4/pull/11165) 提供 `DTreeMap`/`TreeMap`/`TreeSet` 和 `TreeSet` 上的交集
  提供了几个关于它的引理。

* [#11178](https://github.com/leanprover/lean4/pull/11178) 提供了更多关于 `Subarray` 和 `ListSlice` 的引理
  还添加了对这两种类型切片的子切片的支持。

* [#11180](https://github.com/leanprover/lean4/pull/11180) 重新定义了 `String.take` 和要操作的变体
  `String.Slice`。虽然以前的函数返回一个子字符串
  输入有时返回 `String` 有时返回
  `Substring.Raw`，他们现在统一返回`String.Slice`。

* [#11212](https://github.com/leanprover/lean4/pull/11212) 添加了对差分运算的支持
  `DHashMap`/`HashMap`/`HashSet` 并证明了有关它的几个引理。

* [#11218](https://github.com/leanprover/lean4/pull/11218) 将 `String.offsetOfPos` 重命名为 `String.Pos.Raw.offsetOfPos`
  与其他 `String.Pos.Raw` 操作保持一致。

* [#11222](https://github.com/leanprover/lean4/pull/11222) 实现 `elabToSyntax` 用于创建作用域语法：
  语法` for an arbitrary elaborator `el：选项 Expr -> TermElabM Expr`
  这样`elabTerm s = el`。

* [#11223](https://github.com/leanprover/lean4/pull/11223) 添加了与 `emptyWithCapacity`/`empty` 相关的缺失引理和
  `toList`/`keys`/`values` 适用于 `DHashMap`/`HashMap`/`HashSet`。

* [#11231](https://github.com/leanprover/lean4/pull/11231) 添加了几个相关的引理
  `getMin`/`getMin?`/`getMin!`/`getMinD` 并插入到空
  (D)TreeMap/TreeSet 及其扩展变体。

* [#11232](https://github.com/leanprover/lean4/pull/11232) 弃用 `String.toSubstring`，转而使用
  `String.toRawSubstring`（参见#11154）。

* [#11235](https://github.com/leanprover/lean4/pull/11235) 在以下位置注册 `Lean.Parser.Term.elabToSyntax` 的节点类型
  为了支持 `Lean.Elab.Term.elabToSyntax` 功能，无需
  为用户可访问的语法注册专用解析器。

* [#11237](https://github.com/leanprover/lean4/pull/11237) 修复了 `UInt64.fromJson?` 引发的错误和
  `USize.fromJson?` 使用缺失的 `s!`。

* [#11240](https://github.com/leanprover/lean4/pull/11240) 将 `String.ValidPos` 重命名为 `String.Pos`、`String.endValidPos`
  至 `String.endPos` 和 `String.startValidPos` 至 `String.startPos`。

* [#11241](https://github.com/leanprover/lean4/pull/11241) 提供交集运算
  `ExtDHashMap`/`ExtHashMap`/`ExtHashSet` 并证明了几个引理
  它。

* [#11242](https://github.com/leanprover/lean4/pull/11242) 显着更改了 `ToIterator` 类型的签名
  类。获得的迭代器的状态不再是依值类型的并且
  是 `outParam`，而不是捆绑在类中。除其他外
  好处是，`simp` 现在可以在 `Slice.toList` 内部进行重写，并且
  `Slice.toArray`。缺点是我们失去了灵活性。例如，
  `Subarray` 迭代器的前一个基于组合器的实现是
  不再可行，因为状态是依值类型的。因此，
  此 PR 提供了 `Subarray` 的手写迭代器，它没有
  需要一种依值类型的状态并且比前一个状态更快。

* [#11243](https://github.com/leanprover/lean4/pull/11243) 将 `ofArray` 添加到 `DHashMap`/`HashMap`/`HashSet` 并证明
  simpl 引理允许将 `ofArray` 重写为 `ofList`。

* [#11250](https://github.com/leanprover/lean4/pull/11250) 引入了一个函数 `String.split`，它基于
  `String.Slice.split` 因此支持所有模式类型和
  返回 `Std.Iter String.Slice`。

* [#11255](https://github.com/leanprover/lean4/pull/11255) 减少使用字符串模式时的分配。在
  特别的
  `startsWith`、`dropPrefix?`、`endsWith`、`dropSuffix?` 已优化。

* [#11263](https://github.com/leanprover/lean4/pull/11263) 修复了新 `String` API 中的多个内存泄漏问题。

* [#11266](https://github.com/leanprover/lean4/pull/11266) 为 `DHashMap`/`HashMap`/`HashSet` 添加 `BEq` 实例及其
  扩展变体并证明与等价相关的引理
  哈希图/扩展变体的相等。

* [#11267](https://github.com/leanprover/lean4/pull/11267) 重命名并集的同余引理
  `DHashMap`/`HashMap`/`HashSet`/`DTreeMap`/`TreeMap`/`TreeSet` 适合
  位于 `Equiv` 命名空间中的约定。

* [#11276](https://github.com/leanprover/lean4/pull/11276) 清理 `String.find` 周围的 API 并将其统一移动到
  新位置类型 `String.ValidPos` 和 `String.Slice.Pos`

* [#11281](https://github.com/leanprover/lean4/pull/11281) 添加了一些对从未存在过的函数的弃用
  这对于在#11180 之后迁移代码的人们仍然有帮助。

* [#11282](https://github.com/leanprover/lean4/pull/11282) 为 `String.Slice.contains` 添加别名 `String.Slice.any`。

* [#11285](https://github.com/leanprover/lean4/pull/11285) 将 `p : Char -> Prop` 的 `Std.Slice.Pattern` 实例添加为
  只要 `DecidablePred p`，允许像 `"hello".dropWhile (· =
  'h'）`。

* [#11286](https://github.com/leanprover/lean4/pull/11286) 添加函数 `String.Slice.length`，其内容如下
  弃用字符串：切片上没有恒定时间长度函数。
  如果您只需要知道，请使用 `s.positions.count` 或 `isEmpty`
  切片是否为空。

* [#11289](https://github.com/leanprover/lean4/pull/11289) 重新定义 `String.foldl`、`String.isNat` 以使用它们的
  `String.Slice`对应。

* [#11290](https://github.com/leanprover/lean4/pull/11290) 将 `String.replaceStartEnd` 重命名为 `String.slice`，
  `String.replaceStart` 至 `String.sliceFrom`，以及 `String.replaceEnd` 至
  `String.sliceTo`，与上的相应功能类似
  `String.Slice`。

* [#11299](https://github.com/leanprover/lean4/pull/11299) 为 `Fin` 添加许多 `@[grind]` 注释，并更新
  测试。

* [#11308](https://github.com/leanprover/lean4/pull/11308) 重新定义 `String` 上的 `front` 和 `back` 以进行处理
  `String.Slice` 并添加了新的 `String` 功能 `front?`、`back?`、
  `positions`、`chars`、`revPositions`、`revChars`、`byteIterator`、
  `revBytes`、`lines`。

* [#11316](https://github.com/leanprover/lean4/pull/11316) 添加 `grind_pattern Exists.choose_spec => P.choose`。

* [#11317](https://github.com/leanprover/lean4/pull/11317) 添加 `grind_pattern Subtype.property => self.val`。

* [#11321](https://github.com/leanprover/lean4/pull/11321) 提供有关 `Nat` 范围的专门引理，包括 `simp`
  用于证明所有人属性的注释和归纳原理
  范围。

* [#11327](https://github.com/leanprover/lean4/pull/11327) 添加两个引理来证明 `a / c < b / c`。

* [#11341](https://github.com/leanprover/lean4/pull/11341) 添加从 `String` 到 `String.Slice` 的强制转换。

* [#11343](https://github.com/leanprover/lean4/pull/11343) 将 `String.bytes` 重命名为 `String.toByteArray`。

* [#11354](https://github.com/leanprover/lean4/pull/11354) 添加了简单的引理，表明从 a 中的某个位置进行搜索
  字符串返回至少位于该位置的内容。

* [#11357](https://github.com/leanprover/lean4/pull/11357) 更新了 `foldr`、`all`、`any` 和 `contains` 函数
  `String` 根据 `String.Slice` 对应项进行定义。

* [#11358](https://github.com/leanprover/lean4/pull/11358) 添加了 `String.Slice.toInt?` 和变体。

* [#11376](https://github.com/leanprover/lean4/pull/11376) 旨在提高 `String.contains` 的性能，
  使用 `Char` 或 `Char -> Bool` 类型的模式时的 `String.find` 等
  通过将针移出迭代器状态，从而解决
  编译器中缺少拆箱。

* [#11380](https://github.com/leanprover/lean4/pull/11380) 将 `String.Slice.Pos.ofSlice` 重命名为 `String.Pos.ofToSlice`
  遵守（尚未记录的）映射命名约定
  职位到职位。然后它添加了几个新功能，以便
  从字符串和切片构造切片的各种方法，现在有
  用于沿此向前和向后映射位置的函数
  建设。

* [#11384](https://github.com/leanprover/lean4/pull/11384) 为 `grind` 添加必要的实例来进行推理
  `String.Pos.Raw`、`String.Pos` 和 `String.Slice.Pos`。

* [#11399](https://github.com/leanprover/lean4/pull/11399) 添加了对差分运算的支持
  `ExtDHashMap`/`ExtHashMap`/`ExtHashSet` 并证明了几个引理
  它。

* [#11404](https://github.com/leanprover/lean4/pull/11404) 为 `DTreeMap`/`TreeMap`/`TreeSet` 添加 BEq 实例及其
  扩展变体并证明与等价相关的引理
  哈希图/扩展变体的相等。

* [#11407](https://github.com/leanprover/lean4/pull/11407) 对 `DTreeMap`/`TreeMap`/`TreeSet` 添加差分运算
  并证明了关于它的几个引理。

* [#11421](https://github.com/leanprover/lean4/pull/11421) 向 `DHashMap`/`HashMap`/`HashSet` 添加可判定的相等性，并且
  他们的扩展变体。

* [#11439](https://github.com/leanprover/lean4/pull/11439) 对字符串 API 执行小型维护

* [#11448](https://github.com/leanprover/lean4/pull/11448) 以常量 `DTreeMap` 移动 `Inhabited` 实例（并且
  相关）查询，例如 `Const.get!`，其中 `Inhabited` 实例
  可以在证明密钥之前提供。

* [#11452](https://github.com/leanprover/lean4/pull/11452) 添加引理，说明如果 get 操作返回一个值，
  那么查询的键必须包含在集合中。这些引理
  为基于 HashMap 和 TreeMap 的集合添加了类似的
  还为 `Init.getElem` 添加了引理。

* [#11465](https://github.com/leanprover/lean4/pull/11465) 修复了文档和代码库中的各种拼写错误
  评论。

* [#11503](https://github.com/leanprover/lean4/pull/11503) 将 `Char -> Bool` 模式标记为字符串的默认实例
  搜索。这意味着像 `" ".find (·.isWhitespace)` 这样的东西现在可以
  详尽无误。

* [#11521](https://github.com/leanprover/lean4/pull/11521) 修复了初始化时触发的分段错误
  同时调用了一个新的计时器和重置。

* [#11527](https://github.com/leanprover/lean4/pull/11527) 向 `DTreeMap`/`TreeMap`/`TreeSet` 添加可判定的相等性，并且
  他们的扩展变体。

* [#11528](https://github.com/leanprover/lean4/pull/11528) 在键列表中添加与 `minKey?` 和 `min?` 相关的引理
  所有 `DTreeMap` 以及由此派生的其他容器。

* [#11542](https://github.com/leanprover/lean4/pull/11542) 从 `List.countP_eq_length_filter` 中删除 `@[grind =]` 并
  `Array.countP_eq_size_filter`，正如用户报告的那样，这是有问题的。

* [#11548](https://github.com/leanprover/lean4/pull/11548) 添加 `Lean.ToJson` 和 `Lean.FromJson` 实例
  `String.Slice`。

* [#11565](https://github.com/leanprover/lean4/pull/11565) 添加了与 `insert`/`insertIfNew` 和 `toList` 相关的引理
  `DTreeMap`/`DHashMap` 派生容器。

* [#11574](https://github.com/leanprover/lean4/pull/11574) 添加了一个引理，将自然数转换为任何有序的
  环是非负的。我们不能直接为 `grind` 进行注释，但是
  可能会将其添加到 `grind` 的 linarith 内部结构中。

* [#11578](https://github.com/leanprover/lean4/pull/11578) 重构了 `get` 操作的用法
  `HashMap`/`TreeMap`/`ExtHashMap`/`ExtTreeMap` 到 `getElem` 实例。

* [#11591](https://github.com/leanprover/lean4/pull/11591) 添加了有关 `ReaderT.run`、`OptionT.run`、
  `StateT.run` 和 `ExceptT.run` 与 `MonadControl` 操作交互。

* [#11596](https://github.com/leanprover/lean4/pull/11596) 在 `Int` 上添加 `@[suggest_for ℤ]`，在
  `Rat`，遵循 `@[suggest_for ℕ]` 在 `Nat` 上建立的模式
  在#11554。

* [#11600](https://github.com/leanprover/lean4/pull/11600) 在基本操作上添加了一些关于 `EStateM.run` 的引理。

* [#11625](https://github.com/leanprover/lean4/pull/11625) 将 `@[expose]` 添加到 `decidable_of_bool`，以便
  在其他地方通过-`decide` 进行证明，减少到 `decidable_of_bool` 继续
  减少。

* [#11654](https://github.com/leanprover/lean4/pull/11654) 更新 `grind` 文档字符串。仍然提到 `cutsat`
  已更名为 `lia`。 ItaLean 期间报告了此问题。

```

# 策略

````markdown

* [#11226](https://github.com/leanprover/lean4/pull/11226) finally removes the old `grind` framework `SearchM`. It has been
  replaced with the new `Action` framework.

* [#11244](https://github.com/leanprover/lean4/pull/11244) fixes minor issues in `grind`. In preparation for adding `grind
  -revert`.

* [#11247](https://github.com/leanprover/lean4/pull/11247) fixes an issue in the `grind` preprocessor. `simp` may introduce
  assigned (universe) metavariables (e.g., when performing
  zeta-reduction).

* [#11248](https://github.com/leanprover/lean4/pull/11248) implements the option `revert`, which is set to `false` by
  default. To recover the old `grind` behavior, you should use `grind
  +revert`. Previously, `grind` used the `RevSimpIntro` idiom, i.e., it
  would revert all hypotheses and then re-introduce them while simplifying
  and applying eager `cases`. This idiom created several problems:

  * Users reported that `grind` would include unnecessary parameters. See
  [here](https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Grind.20aggressively.20includes.20local.20hypotheses.2E/near/554887715).
  * Unnecessary section variables were also being introduced. See the new
  test contributed by Sebastian Graf.
  * Finally, it prevented us from supporting arbitrary parameters as we do
  in `simp`. In `simp`, I implemented a mechanism that simulates local
  universe-polymorphic theorems, but this approach could not be used in
  `grind` because there is no mechanism for reverting (and re-introducing)
  local universe-polymorphic theorems. Adding such a mechanism would
  require substantial work: I would need to modify the local context
  object. I considered maintaining a substitution from the original
  variables to the new ones, but this is also tricky, because the mapping
  would have to be stored in the `grind` goal objects, and it is not just
  a simple mapping. After reverting everything, I would need to keep a
  sequence of original variables that must be added to the mapping as we
  re-introduce them, but eager case splits complicate this quite a bit.
  The whole approach felt overly messy.

* [#11265](https://github.com/leanprover/lean4/pull/11265) marks the automatically generated `sizeOf` theorems as `grind`
  theorems.

* [#11268](https://github.com/leanprover/lean4/pull/11268) implements support for arbitrary `grind` parameters. The feature
  is similar to the one available in `simp`, where a proof term is treated
  as a local universe-polymorphic lemma. This feature relies on `grind
  -revert` (see #11248). For example, users can now write:

  ```lean
  def snd (p : α × β) : β := p.2
  theorem snd_eq (a : α) (b : β) : snd (a, b) = b := rfl

* [#11273](https://github.com/leanprover/lean4/pull/11273) 修复了 `grind` 中证明构造期间的错误。

* [#11295](https://github.com/leanprover/lean4/pull/11295) 修复了所使用的 `ite` 和 `dite` 的传播规则中的错误
  在 `grind` 中。该错误阻止了等式传播到
  卫星解算器。以下是受此问题影响的示例。

* [#11315](https://github.com/leanprover/lean4/pull/11315) 修复了影响 `grind -revert` 的问题。在此模式下，分配
  假设中的元变量没有被实例化。这个问题是
  影响 Mathlib 中的两个文件。

* [#11318](https://github.com/leanprover/lean4/pull/11318) 修复了 `grind` 中的本地声明内部化
  使用 `grind -revert` 时暴露。此错误正在影响 `grind`
  Mathlib 中的证明。

* [#11319](https://github.com/leanprover/lean4/pull/11319) 改进了当 `n` 不是 `grind` 时对 `Fin n` 的支持
  数字。

* [#11323](https://github.com/leanprover/lean4/pull/11323) 引入了新的 `grind` 选项 `funCC`（默认启用），
  它将同余闭包扩展到*函数值*等式。当
  `funCC` 已启用，`grind` 跟踪 **部分应用的等式
  函数**，允许推理步骤，例如：
  ```lean
  a : Nat → Nat
  f : (Nat → Nat) → (Nat → Nat)
  h : f a = a
  ⊢ (f a) m = a m

* [#11326](https://github.com/leanprover/lean4/pull/11326) ensures that users can provide `grind` proof parameters whose
  types are not `forall`-quantified. Examples:

  ```lean
  不透明 f : Nat → Nat
  公理 le_f (a : Nat) : a ≤ f a

* [#11330](https://github.com/leanprover/lean4/pull/11330) 将 `cutsat`策略重命名为 `lia`，以便更好地与
  定理证明界的标准术语。

* [#11331](https://github.com/leanprover/lean4/pull/11331) 在 `grind` 中添加了对 `LawfulOfScientific` 类的支持。
  示例：
  ```lean
  open Lean Grind Std
  variable [LE α] [LT α] [LawfulOrderLT α] [Field α] [OfScientific α]
           [LawfulOfScientific α] [IsLinearOrder α] [OrderedRing α]
  example : (2 / 3 : α) ≤ (0.67 : α) := by  grind
  example : (1.2 : α) ≤ (1.21 : α) := by grind
  example : (2 / 3 : α) ≤ (67 / 100 : α) := by grind
  example : (1.2345 : α) ≤ (1.2346 : α) := by grind
  example : (2.3 : α) ≤ (4.5 : α) := by grind
  example : (2.3 : α) ≤ (5/2 : α) := by grind
  ```

* [#11332](https://github.com/leanprover/lean4/pull/11332) 添加标记文件的 `grind_annotated "YYYY-MM-DD"` 命令
  如手动注释的研磨。

* [#11334](https://github.com/leanprover/lean4/pull/11334) 为环约束添加显式归一化层
  `grind linarith` 模块。例如，它将用于清理
  当环是域时的分母。

* [#11335](https://github.com/leanprover/lean4/pull/11335) 启用语法 `use [ns Foo]` 和“仅实例化”
  Foo]` inside a `grind`策略块，并具有激活的效果
  所有研磨模式的范围都在该命名空间内。我们可以用它来
  使用 `grind` 实现专门的策略，但仅受控子集
  定理。

* [#11348](https://github.com/leanprover/lean4/pull/11348) 激活 `grind_annotated` 命令
  `Init.Data.List.Lemmas` 通过删除 TODO 注释并取消注释
  命令。

* [#11350](https://github.com/leanprover/lean4/pull/11350) 为 `grind` 实现帮助程序 simproc。它是
  用于清理 `grind linarith` 中分母的基础设施。

* [#11365](https://github.com/leanprover/lean4/pull/11365) 在 `try?` 中启用并行性。目前，我们更换了
  `attempt_all` 级（有两个，一个用于内置策略，包括
  `grind` 和 `simp_all`，以及所有用户分机的第二个）
  并行版本。我们（还没有？）改变 `first` 的行为
  为基础的阶段。

* [#11373](https://github.com/leanprover/lean4/pull/11373) 使库建议扩展状态在以下情况下可用
  从 `module` 文件导入。

* [#11375](https://github.com/leanprover/lean4/pull/11375) 添加了对清理 `grind linarith` 中分母的支持
  当类型为 `Field` 时。

* [#11391](https://github.com/leanprover/lean4/pull/11391) 为 `grind_pattern` 实施新的约束类型
  命令。这些约束允许用户控制定理实例化
  在 `grind` 中。
  它需要手动 `update-stage0`，因为更改会影响
  `.olean` 格式，如果没有它，PR 将失败。

* [#11396](https://github.com/leanprover/lean4/pull/11396) 更改 `set_library_suggestions` 以创建辅助
  定义标记为 `@[library_suggestions]`，而不是存储
  `Syntax` 直接在环境中扩展。这可以更好地
  跨模块的库建议的持久性和一致性。

* [#11405](https://github.com/leanprover/lean4/pull/11405) 实现以下 `grind_pattern` 约束：
  ```lean
  grind_pattern fax => f x  where
    depth x < 2

* [#11409](https://github.com/leanprover/lean4/pull/11409) implements support for the `grind_pattern` constraints
  `is_value` and `is_strict_value`.

* [#11410](https://github.com/leanprover/lean4/pull/11410) fixes a kernel type mismatch error in grind's denominator
  cleanup feature. When generating proofs involving inverse numerals (like
  `2⁻¹`), the proof context is compacted to only include variables
  actually used. This involves renaming variable indices - e.g., if
  original indices were `{0: r, 1: 2⁻¹}` and only `2⁻¹` is used, it gets
  renamed to index 0.

* [#11412](https://github.com/leanprover/lean4/pull/11412) fixes an issue where `grind` would fail after multiple
  `norm_cast`
  calls with the error "unexpected metadata found during internalization".

* [#11428](https://github.com/leanprover/lean4/pull/11428) implements support for **guards** in `grind_pattern`. The new
  feature provides additional control over theorem instantiation. For
  example, consider the following monotonicity theorem:

  ```lean
  不透明 f : Nat → Nat
  theorem fMono : x ≤ y → f x ≤ f y := ...
  ```

* [#11429](https://github.com/leanprover/lean4/pull/11429) documents the `grind_pattern` command for manually selecting
  theorem instantiation patterns, including multi-patterns and the
  constraint system (`=/=`, `=?=`, `size`, `depth`, `is_ground`,
  `is_value`, `is_strict_value`, `gen`, `max_insts`, `guard`, `check`).

* [#11462](https://github.com/leanprover/lean4/pull/11462) adds `solve_by_elim` as a fallback in the `try?` tactic's simple
  tactics. When `rfl` and `assumption` both fail but `solve_by_elim`
  succeeds (e.g., for goals requiring hypothesis chaining or
  backtracking), `try?` will now suggest `solve_by_elim`.

* [#11464](https://github.com/leanprover/lean4/pull/11464) improves the error message when no library suggestions engine is
  registered to recommend importing `Lean.LibrarySuggestions.Default` for
  the built-in engine.

* [#11466](https://github.com/leanprover/lean4/pull/11466) removes the "first pass" behavior where `exact?` and `apply?`
  would try `solve_by_elim` on the original goal before doing library
  search. This simplifies the `librarySearch` API and focuses these
  tactics on their primary purpose: finding library lemmas.

* [#11468](https://github.com/leanprover/lean4/pull/11468) adds `+suggestions` support to `solve_by_elim`, following the
  pattern established by `grind +suggestions` and `simp_all +suggestions`.

* [#11469](https://github.com/leanprover/lean4/pull/11469) adds `+grind` and `+try?` options to `exact?` and `apply?`
  tactics.

* [#11471](https://github.com/leanprover/lean4/pull/11471) fixes an incorrect reducibility setting when using `grind`
  interactive mode.

* [#11480](https://github.com/leanprover/lean4/pull/11480) adds the `grind` option `reducible` (default: `true`). When
  enabled, definitional equality tests expand only declarations marked as
  `@[reducible]`.
  Use `grind -reducible` to allow expansion of non-reducible declarations
  during definitional equality tests.
  This option affects only definitional equality; the canonicalizer and
  theorem pattern internalization always unfold reducible declarations
  regardless of this setting.

* [#11481](https://github.com/leanprover/lean4/pull/11481) fixes a bug in `grind?`. The suggestion using the `grind`
  interactive mode was dropping the configuration options provided by the
  user. In the following account, the third suggestion was dropping the
  `-reducible` option.

* [#11484](https://github.com/leanprover/lean4/pull/11484) fixes a bug in the `grind` pattern validation. The bug affected
  type classes that were propositions.

* [#11487](https://github.com/leanprover/lean4/pull/11487) adds a heterogeneous version of the constructor injectivity
  theorems. These theorems are useful for indexed families, and will be
  used in `grind`.

* [#11491](https://github.com/leanprover/lean4/pull/11491) implements heterogeneous constructor injectivity in `grind`.

* [#11494](https://github.com/leanprover/lean4/pull/11494) re-enables star-indexed lemmas as a fallback for `exact?` and
  `apply?`.

* [#11519](https://github.com/leanprover/lean4/pull/11519) marks `Nat` power and divisibility theorems for `grind`. We use
  the new `grind_pattern` constraints to control theorem instantiation.
  Examples:

  ```lean
  example {x m n : Nat} (h : x = 4 ^ (m + 1) * n) : x % 4 = 0 := by
    磨

* [#11520](https://github.com/leanprover/lean4/pull/11520) 在 `grind_pattern` 中实现约束 `not_value x`
  命令。它是约束 `is_value` 的否定。

* [#11522](https://github.com/leanprover/lean4/pull/11522) 为 `Nat` 运算符实现 `grind` 传播器
  simproc 与它们相关，但没有任何理论求解器支持。
  示例：

  ```lean
  example (a b : Nat) : a = 3 → b = 6 → a &&& b = 2 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a ||| b = 7 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a ^^^ b = 5 := by grind
  example (a b : Nat) : a = 3 → b = 6 → a <<< b = 192 := by grind
  example (a b : Nat) : a = 1135 → b = 6 → a >>> b = 17 := by grind
  ```

* [#11547](https://github.com/leanprover/lean4/pull/11547) 确保由
  `register_try?_tactic` 是内部实现细节，应该
  对面向用户的 linter 不可见。

* [#11556](https://github.com/leanprover/lean4/pull/11556) 向 `exact?` 和 `apply?` 添加了一个 `+all` 选项，用于收集所有
  成功的引理而不是停在第一个完整的解决方案上。

* [#11573](https://github.com/leanprover/lean4/pull/11573) 修复了 `grind` 拒绝点表示法术语，将其误认为
  局部假设。

* [#11579](https://github.com/leanprover/lean4/pull/11579) 确保基本定理被正确处理为 `grind`
  参数。此外，`grind [(thm)]` 和 `grind [thm]` 应为
  以同样的方式处理。

* [#11580](https://github.com/leanprover/lean4/pull/11580) 添加了缺失的 `Nat.cast` 缺失标准化规则
  `grind`。例子：
  ```lean
  example (n : Nat) : Nat.cast n = n := by
    grind
  ```

* [#11589](https://github.com/leanprover/lean4/pull/11589) 改进了 `grind` 模式的索引。我们现在包括符号
  发生在嵌套的地面图案中。这对于最大限度地减少
  激活的 E 匹配定理的数量。

* [#11593](https://github.com/leanprover/lean4/pull/11593) 修复了 `grind` 不显示弃用的问题
  当在其参数列表中使用已弃用的引理时发出警告。

* [#11594](https://github.com/leanprover/lean4/pull/11594) 修复了 `grind?` 以包含术语参数（例如 `[show P by
  tac]`）在其建议中。此前，这些被删除的原因是
  术语参数存储在 `extraFacts` 中，并且不通过电子匹配进行跟踪
  就像命名引理一样。

* [#11604](https://github.com/leanprover/lean4/pull/11604) 修复了 `grind` 中如何处理不带参数的定理。

* [#11605](https://github.com/leanprover/lean4/pull/11605) 修复了`grind 中 `a^p` 术语的内部化器中的错误
  利纳里斯`。

* [#11609](https://github.com/leanprover/lean4/pull/11609) 改进了 `grind` 中的大小写启发式。在这个公关中，我们做
  不增加第一个案例中的案例拆分数量。这个想法是
  利用非时间顺序回溯：如果第一个案例得到解决
  使用不依赖于案例假设的证明，我们回溯
  并直接关闭原来的目标。在这种情况下，案例分割
  是“免费的”，它对证明没有贡献。如果不计算它，我们
  当案例分割结果无关紧要时，允许进行更深入的探索。
  新的启发式解决了 #11545 中的第二个示例

* [#11613](https://github.com/leanprover/lean4/pull/11613) 确保我们将环归一化器应用于等式
  从 `grind` 核心模块传播到 `grind lia`。它还确保
  我们在标准化时使用安全/托管多项式函数。

* [#11615](https://github.com/leanprover/lean4/pull/11615) 添加了 `Int.subNatNat` 到 `grind` 的标准化规则。

* [#11628](https://github.com/leanprover/lean4/pull/11628) 为 `Semiring` 添加了一些 `*` 规范化规则到 `grind`。

* [#11629](https://github.com/leanprover/lean4/pull/11629) 在使用的模式标准化代码中添加了缺失条件
  在 `grind` 中。它应该忽略支持基础术语。

* [#11635](https://github.com/leanprover/lean4/pull/11635) 确保 `grind` 中使用的模式标准化器确实违反
  小工具 `Grind.genPattern` 所做的假设和
  `Grind.getHEqPattern`。

* [#11638](https://github.com/leanprover/lean4/pull/11638) 修复了 `grind` 中的位向量文字内部化。修复
  确保由 `BitVec.ofNat` 索引的定理被正确激活。

* [#11639](https://github.com/leanprover/lean4/pull/11639) 在 `grind ring` 中添加了对 `BitVec.ofNat` 的支持。例子：

  ```lean
  example (x : BitVec 8) : (x - 16#8)*(x + 272#8) = x^2 := by
    grind
  ```

* [#11640](https://github.com/leanprover/lean4/pull/11640) 在 `grind lia` 中添加了对 `BitVec.ofNat` 的支持。例子：

  ```lean
  example (x y : BitVec 8) : y < 254#8 → x > 2#8 + y → x > 1#8 + y := by
    grind
  ```

* [#11653](https://github.com/leanprover/lean4/pull/11653) 添加与 `Semiring` 对应的传播规则
  #11628 中引入的标准化规则。新规则仅适用于
  非交换半环，因为 `grind` 对它们的支持有限。
  规范化规则在 Mathlib 中引入了意外行为
  因为它们中和了 `one_mul` 等参数：任何定理
  instance associated with such a parameter is reduced to `True` by the
  标准化器。

* [#11656](https://github.com/leanprover/lean4/pull/11656) 增加了对 `Int.sign`、`Int.fdiv`、`Int.tdiv`、`Int.fmod`、
  `Int.tmod` 和 `Int.bmod` 至 `grind`。这些操作只是
  预处理掉。我们假设它们在实践中并不常见。
  示例：
  ```lean
  example {x y : Int} : y = 0 → (x.fdiv y) = 0 := by grind
  example {x y : Int} : y = 0 → (x.tdiv y) = 0 := by grind
  example {x y : Int} : y = 0 → (x.fmod y) = x := by grind
  example {x y : Int} : y = 1 → (x.fdiv (2 - y)) = x := by grind
  example {x : Int} : x > 0 → x.sign = 1 := by grind
  example {x : Int} : x < 0 → x.sign = -1 := by grind
  example {x y : Int} : x.sign = 0 → x*y = 0 := by grind
  ```

* [#11658](https://github.com/leanprover/lean4/pull/11658) 修复了参数文字内部化的错误
  `grind`。即，类型为 `BitVec _` 或 `Fin _` 的文字。

* [#11659](https://github.com/leanprover/lean4/pull/11659) 生成模式时添加 `MessageData.withNamingContext`
  `@[grind]` 的建议。它修复了期间报告的另一个问题
  意大利Lean。

* [#11660](https://github.com/leanprover/lean4/pull/11660) 修复了 `grind` 中的另一个定理激活问题。

* [#11663](https://github.com/leanprover/lean4/pull/11663) 修复了 `grind` 模式验证器。它涵盖了以下情况：
  instance is not tagged with the implicit instance binder. This happens
  在声明中，例如
  ```lean
  ZeroMemClass.zero_mem {S : Type} {M : outParam Type} {inst1 : Zero M} {inst2 : SetLike S M}
    [self : @ZeroMemClass S M inst1 inst2] (s : S) : 0 ∈ s
  ```

````

# Compiler

```markdown

* [#11082](https://github.com/leanprover/lean4/pull/11082) 防止（非 `@[export]`）定义之间的符号冲突
  来自不同的 Lean 封装。

* [#11185](https://github.com/leanprover/lean4/pull/11185) 修复了要考虑的 `reduceArity` 编译器传递
  过度应用数量减少的函数。
  以前，此传递假设参数数量
  应用程序中的参数数量始终相同
  签名。这通常是正确的，因为编译器急切地引入
  只要返回类型是函数类型，就会产生参数
  返回类型不是函数类型的函数。然而，对于
  依值类型 有时是函数类型，有时不是，
  这个假设被打破，导致附加参数被打破
  掉了。

* [#11210](https://github.com/leanprover/lean4/pull/11210) 修复了在工作时发现的 LCNF 简化器中的错误
  第11078章在由 `unsafeCast` 引起的某些情况下，简化器会
  记录有关 `cases` 的错误信息，导致进一步的错误
  线。

* [#11215](https://github.com/leanprover/lean4/pull/11215) 修复了正确跟踪标头嵌套级别的问题
  在模块文档之间，但不在模块文档内。

* [#11217](https://github.com/leanprover/lean4/pull/11217) 修复了 #10982 中闭包分配器更改的影响。到目前为止
  据我们所知
  此错误仅在非默认构建配置中有意义地体现
  没有mimalloc，例如：
  `cmake --preset release -DUSE_MIMALLOC=OFF`

* [#11310](https://github.com/leanprover/lean4/pull/11310) 使专用程序（正确地）跨域共享更多缓存键
  调用，使我们产生更少的代码膨胀。

* [#11340](https://github.com/leanprover/lean4/pull/11340) 修复了遇到非投影时的错误编译
  琐碎的结构类型。

* [#11362](https://github.com/leanprover/lean4/pull/11362) 加速 ElimDeadBranches 编译器通道的终止。

* [#11366](https://github.com/leanprover/lean4/pull/11366) 按升序对输入 ElimDeadBranches 的声明进行排序
  尺寸。当我们处理大量数据时，这可以提高性能
  迭代。

* [#11381](https://github.com/leanprover/lean4/pull/11381) 修复了封闭术语提取不尊重的错误
  的隐式不变量
  c 发射器首先具有封闭项 decls，然后是其他 decls，在一个
  南卡罗来纳州。这个bug还没有出现
  在野外被触发，但在即将推出的工作期间被发现
  的修改
  专家。

* [#11383](https://github.com/leanprover/lean4/pull/11383) 修复了未装箱的结构投影的编译
  标记为 `extern` 的参数，添加缺少的 `dec` 指令。这导致了
  当此类函数用作闭包时，会泄漏单个分配或
  在口译员中。

* [#11388](https://github.com/leanprover/lean4/pull/11388) 是 #11381 的后续，并强制执行排序不变量
  EmitC 所需的闭项和常量正确通过
  在将声明保存到环境中之前进行拓扑排序。

* [#11426](https://github.com/leanprover/lean4/pull/11426) 关闭#11356。

* [#11445](https://github.com/leanprover/lean4/pull/11445) 稍微改进了创建盒装所涉及的类型
  声明。以前的类型
  返回盒装时，用于返回的 vdecl 始终为 `tobj`
  标量。这还不是最
  我们可以给出精确的注释。

* [#11451](https://github.com/leanprover/lean4/pull/11451) 将 LCNF 中的 lambda 提升器改编为 eta 合约，而不是
  如果可能的话，拉姆达升力。这可以防止创建数百个
  代码库中不必要的 lambda。

* [#11517](https://github.com/leanprover/lean4/pull/11517) 实现 Nat.mul 的常量折叠

* [#11525](https://github.com/leanprover/lean4/pull/11525) 使 LCNF 简化器消除所有替代项都是的情况
  `.unreach` 改为 `.unreach`。
    `.unreach`

* [#11530](https://github.com/leanprover/lean4/pull/11530) 引入了新的 `tagged_return` 属性。它允许用户
  标记 `extern` 声明以保证始终返回 `tagged`
  返回值。与 `object` 或 `tobject` 不同，编译器不
  为它们发出引用计数操作。在未来的信息中
  此属性将用于更强大的分析以删除
  尽可能进行引用计数。

* [#11576](https://github.com/leanprover/lean4/pull/11576) 删除旧的 ElimDeadBranches 通道并移动新通道
  过去的 lambda 提升。

* [#11586](https://github.com/leanprover/lean4/pull/11586) 允许在 IR 类型系统中投影 `tagged` 值。

```

# Documentation

```markdown

* [#11119](https://github.com/leanprover/lean4/pull/11119) 引入了对“未定义标识符”错误的澄清说明
  当未定义的标识符位于语法位置时的消息
  自动绑定通常可能适用，但是自动绑定在哪里
  禁用。 `lean.unknownIdentifier` 中做了相应的注释
  错误解释。

* [#11364](https://github.com/leanprover/lean4/pull/11364) 为出现在
  参考手册。

* [#11472](https://github.com/leanprover/lean4/pull/11472) 添加 `mkSlice` 方法缺少的文档字符串。

* [#11550](https://github.com/leanprover/lean4/pull/11550) 查看将出现在 Lean 中的 `Std.Do` 的文档字符串
  参考手册并添加了缺失的内容。

* [#11575](https://github.com/leanprover/lean4/pull/11575) 修复了 `cases`策略文档字符串中的拼写错误。

* [#11595](https://github.com/leanprover/lean4/pull/11595) 在 `tests/lean/run/` 中进行测试的文档
  `-Dlinter.all=false`，并解释了如何在以下情况下启用特定的 linter：
  测试 linter 行为。

```

# Server

```markdown

* [#11162](https://github.com/leanprover/lean4/pull/11162) 减少语言服务器的内存消耗（
  特别是看门狗进程）。在Mathlib中，它减少了内存
  消耗约1GB。

* [#11164](https://github.com/leanprover/lean4/pull/11164) 确保针对未知标识符提供的代码操作
  将 `public` 和/或 `meta` 正确插入 `module` 中

* [#11577](https://github.com/leanprover/lean4/pull/11577) 修复了策略框架报告文件进度条范围
  掩盖了嵌套在策略中的策略块内的进度
  组合器。这是纯粹的视觉变化，增量重新精化
  内部支持的组合器不受影响。

```

# Lake

```markdown

* [#11198](https://github.com/leanprover/lean4/pull/11198) 修复了 Lake 中建议不正确的错误消息
  Lakefile 语法。

* [#11216](https://github.com/leanprover/lean4/pull/11216) 确保 `computeArtifact` 的 `text` 参数始终为
  在 Lake 代码中提供，修复了哈希错误
  `buildArtifactUnlessUpToDate` 正在处理中。

* [#11270](https://github.com/leanprover/lean4/pull/11270) 在 Lake 中添加模块解析过程以消除歧义
  在多个包中定义的模块。

* [#11500](https://github.com/leanprover/lean4/pull/11500) 将工作空间索引添加到构建使用的包的名称中
  目标。为了澄清不同用途之间的区别
  包的名称，此 PR 还弃用了 `Package.name` 以获得更多信息
  特定于用途的变体（例如，`Package.keyName`、`Package.prettyName`、
  `Package.origName`)。

```

# Other

````markdown

* [#11328](https://github.com/leanprover/lean4/pull/11328) 修复了释放每个文档意外保留的内存的问题
  某些精化工作负载上的语言服务器中的版本。的
  问题肯定是从 4.18.0 开始就存在的。

* [#11437](https://github.com/leanprover/lean4/pull/11437) 添加了录制功能，使 `shake` 可以更多
  精确跟踪进口是否应仅为其保留
  `attribute` 命令。

* [#11496](https://github.com/leanprover/lean4/pull/11496) 为 `shake` 实现新的标志和注释，以用于
  Mathlib：

  > 选项：
  > --保持暗示
  > 保留其他导入所隐含的现有导入，从而
  技术上不需要
  > 不再了
  >
  > --保留前缀
  > 如果将导入 `X` 替换为更具体的导入
  `X.Y...` 这意味着，
  > 而是保留原始导入。更一般地说，更喜欢
  插入 `import X` 即使
  > 不是原始进口的一部分，只要它是原始进口的一部分
  传递性导入关闭
  > 当前模块的。
  >
  > --保持公开
  > 保留所有 `public` 导入以避免外部的重大更改
  下游模块
  >
  > --add-public
  > 如果新导入已在原始公开中，则将其添加为 `public`
  关闭该模块。
  > 换句话说，公共导入不会从模块中删除
  除非它们甚至没有被使用
  > 在私有范围内，那些被删除的将被重新添加为
  下游 `public`
  > 模块，即使只在私有范围内需要。不像
  `--keep-public`，这可能
  > 引入重大更改，但仍会限制插入的数量
  进口。
  >
  > 注释：
  > 可以将以下注释添加到 Lean 文件中，以便
  配置的行为
  > `shake`。仅子字符串 `shake: ` 直接后跟指令
  已检查，因此多个
  > 指令可以混合在一行中，例如 `-- shake：
  keep-downstream, shake: keep-all`，他们
  > 可以被任意注释包围，例如 `-- shake: keep
  （元程序输出依赖）`。
  >
  > * `module -- shake: keep-downstream`:
  > 在所有（当前）下游模块中保留此模块，添加新的
  如果需要的话进口它。
  >
  > * `module -- shake: keep-all`:
  > 按原样保留此模块中的所有现有导入。现在新进口
  由于上游需要
  > 仍可能添加更改。
  >
  > * `import X -- shake: keep`:
  > 在当前模块中保留此特定导入。最常见的
  用例是保留一个
  > 下游模块需要公共导入才有意义
  的输出
  > 本模块中定义的元程序。例如，如果策略是
  定义可以合成
  > 运行时引用一个定理，`shake` 无法检测到
  这本身和
  > 该定理的模块应该公开导入并注释为
  `keep` 在策略的
  > 模块。
  > ```
  > public import X -- shake: keep (元程序输出依赖)
  >
  > ...
  >
  > elab \"my_tropic\" :策略=> 执行
  > ... mkConst ``f -- `f`，在 `X` 中定义，可能出现在输出中
  这个策略
  > ```

* [#11507](https://github.com/leanprover/lean4/pull/11507) 优化导入期间的文件系统访问，获得约 3% 的胜利
  在 Linux 上，其他平台上可能有更多。

````
