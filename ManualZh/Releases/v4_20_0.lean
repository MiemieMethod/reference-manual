/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre

-- TODO: figure out why this is needed with the new codegen
set_option maxRecDepth 9000

#doc (Manual) "Lean 4.20.0 (2025-06-02)" =>
%%%
tag := "release-v4.20.0"
file := "v4.20.0"
%%%

````markdown
For this release, 346 changes landed. In addition to the 108 feature additions and 85 fixes listed below there were 6 refactoring changes, 7 documentation improvements, 8 performance improvements, 4 improvements to the test suite and 126 other changes.

## Highlights
%%%
tag := "zh-releases-v4-20-0-h001"
%%%

The Lean v4.20.0 release brings multiple new features, bug fixes, improvements to Lake, and groundwork for the module system.

### Language Features
%%%
tag := "zh-releases-v4-20-0-h002"
%%%

* [#6432](https://github.com/leanprover/lean4/pull/6432) implements tactics called `extract_lets` and `lift_lets` that
  manipulate `let`/`let_fun` expressions. The `extract_lets` tactic
  creates new local declarations extracted from any `let` and `let_fun`
  expressions in the main goal. For top-level lets in the target, it is
  like the `intros` tactic, but in general it can extract lets from deeper
  subexpressions as well. The `lift_lets` tactic moves `let` and `let_fun`
  expressions as far out of an expression as possible, but it does not
  extract any new local declarations. The option `extract_lets +lift`
  combines these behaviors.

* [#7806](https://github.com/leanprover/lean4/pull/7806) modifies the syntaxes of the `ext`, `intro` and `enter` conv
  tactics to accept `_`. The introduced binder is an inaccessible name.

* [#7830](https://github.com/leanprover/lean4/pull/7830) modifies the syntax of `induction`, `cases`, and other tactics
  that use `Lean.Parser.Tactic.inductionAlts`. If a case omits `=> ...`
  then it is assumed to be `=> ?_`. Example:
  ```lean
  example (p : Nat × Nat) : p.1 = p.1 := by
    案例 p 与 | _ p1 p2
    /-
    案例MK
    p1 p2 : 纳特
    ⊢ (p1, p2).fst = (p1, p2).fst
    -/
  ```
  This works with multiple cases as well. Example:
  ```lean
  example (n : Nat) : n + 1 = 1 + n := by
    归纳法 n 与 |零|苏克尼赫
    /-
    案例零
    ⊢ 0 + 1 = 1 + 0

    案例成功
    n : 纳特
    ih : n + 1 = 1 + n
    ⊢ n + 1 + 1 = 1 + (n + 1)
    -/
  ```
  The `induction n with | zero | succ n ih` is short for `induction n with
  | zero | succ n ih => ?_`, which is short for `induction n with | zero
  => ?_ | succ n ih => ?_`. Note that a consequence of parsing is that
  only the last alternative can omit `=>`. Any `=>`-free alternatives
  before an alternative with `=>` will be a part of that alternative.

* [#7831](https://github.com/leanprover/lean4/pull/7831) adds extensibility to the `evalAndSuggest` procedure used to
  implement `try?`. Users can now implement their own handlers for any
  tactic.
  ```lean
  -- 为 `assumption` 安装 `TryTactic` 处理程序
  @[try_tactic assumption]
  def evalTryApply : TryTactic := fun tac => do
    -- 我们只使用默认实现，但返回不同的策略。
    评估假设 tac
    `(策略|（跟踪“有效”；假设））

  /-- 信息：试试这个：·跟踪“工作”；假设 -/
  #guard_msgs (info) in
  example (h : False) : False := by
    尝试？ (max := 1) -- 最多一个解决方案

  -- `try?` 使用 `evalAndSuggest` 属性 `[try_tactic]` 用于扩展 `evalAndSuggest`。
  -- 让我们定义我们自己的使用 `evalAndSuggest` 的 `try?`
  elab stx:"my_try?" : tactic => do
    -- 值得尝试的事情
    让 toTry ← `(策略| attempts_all | 假设 | 应用 True | rfl)
    evalAndSuggest stx 尝试

  /--
  信息：尝试这些：
  •· 跟踪“有效”；假设
  • rfl
  -/
  #guard_msgs (info) in
  example (a : Nat) (h : a = a) : a = a := by
    我的_尝试？
  ```

* [#8055](https://github.com/leanprover/lean4/pull/8055) adds an implementation of an async IO multiplexing framework as
  well as an implementation of it for the `Timer` API in order to
  demonstrate it.

* [#8088](https://github.com/leanprover/lean4/pull/8088) adds the “unfolding” variant of the functional induction and
  functional cases principles, under the name `foo.induct_unfolding` resp.
  `foo.fun_cases_unfolding`. These theorems combine induction over the
  structure of a recursive function with the unfolding of that function,
  and should be more reliable, easier to use and more efficient than just
  case-splitting and then rewriting with equational theorems.

  For example instead of

  ```
  阿克曼感应
    （动机：Nat → Nat → Prop）
    （情况 1：∀（m：Nat），动机 0 m）
    (case2 : ∀ (n : Nat), 动机 n 1 → 动机 (Nat.succ n) 0)
    (case3 : ∀ (n m : Nat), 动机 (n + 1) m → 动机 n (ackermann (n + 1) m) → 动机 (Nat.succ n) (Nat.succ m))
    (x x : Nat) : 动机 x x
  ```

  one gets

  ```
  ackermann.fun_cases_unfolding
    （动机：Nat → Nat → Nat → Prop）
    （情况1：∀（m：Nat），动机0 m（m + 1））
    (case2 : ∀ (n : Nat), 动机 n.succ 0 (ackermann n 1))
    (case3 : ∀ (n m : Nat), 动机 n.succ m.succ (ackermann n (ackermann (n + 1) m)))
    (x✝ x✝1 : Nat) : 动机 x✝ x✝1 (阿克曼 x✝ x✝1)
  ```

* [#8097](https://github.com/leanprover/lean4/pull/8097) adds support for inductive and coinductive predicates defined
  using lattice theoretic structures on `Prop`. These are syntactically
  defined using `greatest_fixpoint` or `least_fixpoint` termination
  clauses for recursive `Prop`-valued functions. The functionality relies
  on `partial_fixpoint` machinery and requires function definitions to be
  monotone. For non-mutually recursive predicates, an appropriate
  (co)induction proof principle (given by Park induction) is generated.

### Library Highlights
%%%
tag := "zh-releases-v4-20-0-h003"
%%%

[#8004](https://github.com/leanprover/lean4/pull/8004) adds extensional hash maps and hash sets under the names
  `Std.ExtDHashMap`, `Std.ExtHashMap` and `Std.ExtHashSet`. Extensional
  hash maps work like regular hash maps, except that they have
  extensionality lemmas which make them easier to use in proofs. This
  however makes it also impossible to regularly iterate over its entries.

Other notable library developments in this release include:
- Updates to the `Option` API,
- Async runtime developments: added support for multiplexing via UDP and TCP sockets, as well as channels,
- New `BitVec` definitions related to overflow handling,
- New lemmas for `Nat.lcm`, and `Int` variants for `Nat.gcd` and `Nat.lcm`,
- Upstreams from Mathlib related to `Nat` and `Int`,
- Additions to numeric types APIs, such as `UIntX.ofInt`, `Fin.ofNat'_mul` and `Fin.mul_ofNat'`, `Int.toNat_sub''`,
- Updates to `Perm` API in `Array`, `List`, and added support for `Vector`,
- Additional lemmas for `Array`/`List`/`Vector`.

### Lake
%%%
tag := "zh-releases-v4-20-0-h004"
%%%

* [#7909](https://github.com/leanprover/lean4/pull/7909) adds Lake support for building modules given their source file
  path. This is made use of in both the CLI and the server.

### Breaking Changes
%%%
tag := "zh-releases-v4-20-0-h005"
%%%

* [#7474](https://github.com/leanprover/lean4/pull/7474) updates `rw?`, `show_term`, and other tactic-suggesting tactics
  to suggest `expose_names` when necessary and validate tactics prior to
  suggesting them, as `exact?` already did, and it also ensures all such
  tactics produce hover info in the messages showing tactic suggestions.

  This introduces a **breaking change** in the `TryThis` API: the `type?` parameter
  of `addRewriteSuggestion` is now an `LOption`, not an `Option`, to obviate the need
  for a hack we previously used to indicate that a rewrite closed the goal.

* [#7789](https://github.com/leanprover/lean4/pull/7789) fixes `lean` potentially changing or interpreting arguments
  after `--run`.

  **Breaking change**: The Lean file to run must now be passed directly
  after `--run`, which accidentally was not enforced before.

* [#7813](https://github.com/leanprover/lean4/pull/7813) fixes an issue where `let n : Nat := sorry` in the Infoview
  pretty prints as ``n : ℕ := sorry `«Foo:17:17»``. This was caused by
  top-level expressions being pretty printed with the same rules as
  Infoview hovers. Closes [#6715](https://github.com/leanprover/lean4/issues/6715). Refactors `Lean.Widget.ppExprTagged`; now
  it takes a delaborator, and downstream users should configure their own
  pretty printer option overrides if necessary if they used the `explicit`
  argument (see `Lean.Widget.makePopup.ppExprForPopup` for an example).
  **Breaking change:** `ppExprTagged` does not set `pp.proofs` on the root
  expression.

* [#7855](https://github.com/leanprover/lean4/pull/7855) moves `ReflBEq` to `Init.Core` and changes `LawfulBEq` to extend
  `ReflBEq`.

  **Breaking changes:**
  - The `refl` field of `ReflBEq` has been renamed to `rfl` to match
  `LawfulBEq`
  - `LawfulBEq` extends `ReflBEq`, so in particular `LawfulBEq.rfl` is no
  longer valid

* [#7873](https://github.com/leanprover/lean4/pull/7873) fixes a number of bugs related to the handling of the source
  search path in the language server, where deleting files could cause
  several features to stop functioning and both untitled files and files
  that don't exist on disc could have conflicting module names.

  See the PR description for the details on changes in URI <-> module name conversion.

  **Breaking changes:**
  - `Server.documentUriFromModule` has been renamed to
  `Server.documentUriFromModule?` and doesn't take a `SearchPath` argument
  anymore, as the `SearchPath` is now computed from the `LEAN_SRC_PATH`
  environment variable. It has also been moved from `Lean.Server.GoTo` to
  `Lean.Server.Utils`.
  - `Server.moduleFromDocumentUri` does not take a `SearchPath` argument
  anymore and won't return an `Option` anymore. It has also been moved
  from `Lean.Server.GoTo` to `Lean.Server.Utils`.
  - The `System.SearchPath.searchModuleNameOfUri` function has been
  removed. It is recommended to use `Server.moduleFromDocumentUri`
  instead.
  - The `initSrcSearchPath` function has been renamed to
  `getSrcSearchPath` and has been moved from `Lean.Util.Paths` to
  `Lean.Util.Path`. It also doesn't need to take a `pkgSearchPath`
  argument anymore.

* [#7967](https://github.com/leanprover/lean4/pull/7967) adds a `bootstrap` option to Lake which is used to identify the
  core Lean package. This enables Lake to use the current stage's include
  directory rather than the Lean toolchains when compiling Lean with Lean
  in core.

  **Breaking change:** The Lean library directory is no longer part of
  `getLeanLinkSharedFlags`. FFI users should provide this option
  separately when linking to Lean (e.g.. via `s!"-L{(←getLeanLibDir).toString}"`).
  See the FFI example for a demonstration.

## Language
%%%
tag := "zh-releases-v4-20-0-h006"
%%%

* [#6325](https://github.com/leanprover/lean4/pull/6325) ensures that environments can be loaded, repeatedly, without
  executing arbitrary code

* [#6432](https://github.com/leanprover/lean4/pull/6432) implements tactics called `extract_lets` and `lift_lets` that
  manipulate `let`/`let_fun` expressions. The `extract_lets` tactic
  creates new local declarations extracted from any `let` and `let_fun`
  expressions in the main goal. For top-level lets in the target, it is
  like the `intros` tactic, but in general it can extract lets from deeper
  subexpressions as well. The `lift_lets` tactic moves `let` and `let_fun`
  expressions as far out of an expression as possible, but it does not
  extract any new local declarations. The option `extract_lets +lift`
  combines these behaviors.

* [#7474](https://github.com/leanprover/lean4/pull/7474) updates `rw?`, `show_term`, and other tactic-suggesting tactics
  to suggest `expose_names` when necessary and validate tactics prior to
  suggesting them, as `exact?` already did, and it also ensures all such
  tactics produce hover info in the messages showing tactic suggestions.

* [#7797](https://github.com/leanprover/lean4/pull/7797) adds a monolithic `CommRing` class, for internal use by `grind`,
  and includes instances for `Int`/`BitVec`/`IntX`/`UIntX`.

* [#7803](https://github.com/leanprover/lean4/pull/7803) adds normalization rules for function composition to `grind`.

* [#7806](https://github.com/leanprover/lean4/pull/7806) modifies the syntaxes of the `ext`, `intro` and `enter` conv
  tactics to accept `_`. The introduced binder is an inaccessible name.

* [#7808](https://github.com/leanprover/lean4/pull/7808) adds missing forall normalization rules to `grind`.

* [#7816](https://github.com/leanprover/lean4/pull/7816) fixes an issue where `x.f.g` wouldn't work but `(x.f).g` would
  when `x.f` is generalized field notation. The problem was that `x.f.g`
  would assume `x : T` should be the first explicit argument to `T.f`. Now
  it uses consistent argument insertion rules. Closes #6400.

* [#7825](https://github.com/leanprover/lean4/pull/7825) improves support for `Nat` in the `cutsat` procedure used in
  `grind`:

  - `cutsat` no longer *pollutes* the local context with facts of the form
  `-1 * NatCast.natCast x <= 0` for each `x : Nat`. These facts are now
  stored internally in the `cutsat` state.
  - A single context is now used for all `Nat` terms.

* [#7829](https://github.com/leanprover/lean4/pull/7829) fixes an issue in the cutsat counterexamples. It removes the
  optimization (`Cutsat.State.terms`) that was used to avoid the new
  theorem `eq_def`. In the two new tests, prior to this PR, `cutsat`
  produced a bogus counterexample with `b := 2`.

* [#7830](https://github.com/leanprover/lean4/pull/7830) modifies the syntax of `induction`, `cases`, and other tactics
  that use `Lean.Parser.Tactic.inductionAlts`. If a case omits `=> ...`
  then it is assumed to be `=> ?_`. Example:
  ```lean
  example (p : Nat × Nat) : p.1 = p.1 := by
    案例 p 与 | _ p1 p2
    /-
    案例MK
    p1 p2 : 纳特
    ⊢ (p1, p2).fst = (p1, p2).fst
    -/
  ```
  This works with multiple cases as well. Example:
  ```lean
  example (n : Nat) : n + 1 = 1 + n := by
    归纳法 n 与 |零|苏克尼赫
    /-
    案例零
    ⊢ 0 + 1 = 1 + 0

    案例成功
    n : 纳特
    ih : n + 1 = 1 + n
    ⊢ n + 1 + 1 = 1 + (n + 1)
    -/
  ```
  The `induction n with | zero | succ n ih` is short for `induction n with
  | zero | succ n ih => ?_`, which is short for `induction n with | zero
  => ?_ | succ n ih => ?_`. Note that a consequence of parsing is that
  only the last alternative can omit `=>`. Any `=>`-free alternatives
  before an alternative with `=>` will be a part of that alternative.

* [#7831](https://github.com/leanprover/lean4/pull/7831) adds extensibility to the `evalAndSuggest` procedure used to
  implement `try?`. Users can now implement their own handlers for any
  tactic. The new test demonstrates how this feature works.

* [#7859](https://github.com/leanprover/lean4/pull/7859) allows the LRAT parser to accept any proof that derives the
  empty clause at somepoint, not necessarily in the last line. Some tools
  like lrat-trim occasionally include deletions after the derivation of
  the empty clause but the proof is sound as long as it soundly derives
  the empty clause somewhere.

* [#7861](https://github.com/leanprover/lean4/pull/7861) fixes an issue that prevented theorems from being activated in
  `grind`.

* [#7862](https://github.com/leanprover/lean4/pull/7862) improves the normalization of `Bool` terms in `grind`. Recall
  that `grind` currently does not case split on Boolean terms to reduce
  the size of the search space.

* [#7864](https://github.com/leanprover/lean4/pull/7864) adds support to `grind` for case splitting on implications of
  the form `p -> q` and `(h : p) -> q h`. See the new option `(splitImp :=
  true)`.

* [#7865](https://github.com/leanprover/lean4/pull/7865) adds a missing propagation rule for implication in `grind`. It
  also avoids unnecessary case-splits on implications.

* [#7870](https://github.com/leanprover/lean4/pull/7870) adds a mixin type class for `Lean.Grind.CommRing` recording the
  characteristic of the ring, and constructs instances for `Int`, `IntX`,
  `UIntX`, and `BitVec`.

* [#7885](https://github.com/leanprover/lean4/pull/7885) fixes the counterexamples produced by the cutsat procedure in
  `grind` for examples containing `Nat` terms.

* [#7892](https://github.com/leanprover/lean4/pull/7892) improves the support for `funext` in `grind`. We will push
  another PR to minimize the number of case-splits later.

* [#7902](https://github.com/leanprover/lean4/pull/7902) introduces a dedicated option for checking whether elaborators
  are running in the language server.

* [#7905](https://github.com/leanprover/lean4/pull/7905) fixes an issue introduced by bug #6125 where an `inductive` or
  `structure` with an autoimplicit parameter with a type that has a
  metavariable would lead to a panic. Closes #7788.

* [#7907](https://github.com/leanprover/lean4/pull/7907) fixes two bugs in `grind`.
  1. Model-based theory combination was creating type-incorrect terms.
  2. `Nat.cast` vs `NatCast.natCast` issue during normalization.

* [#7914](https://github.com/leanprover/lean4/pull/7914) adds a function hook `PersistentEnvExtension.saveEntriesFn` that
  can be used to store server-only metadata such as position information
  and docstrings that should not affect (re)builds.

* [#7920](https://github.com/leanprover/lean4/pull/7920) introduces a fast path based on comparing the (cached) hash
  value to the `DecidableEq` instance of the core expression data type in
  `bv_decide`'s bitblaster.

* [#7926](https://github.com/leanprover/lean4/pull/7926) fixes two issues that were preventing `grind` from solving
  `getElem?_eq_some_iff`.
  1. Missing propagation rule for `Exists p = False`
  2. Missing conditions at `isCongrToPrevSplit` a filter for discarding
  unnecessary case-splits.

* [#7937](https://github.com/leanprover/lean4/pull/7937) implements a lookahead feature to reduce the size of the search
  space in `grind`. It is currently effective only for arithmetic atoms.

* [#7949](https://github.com/leanprover/lean4/pull/7949) adds the attribute `[grind ext]`. It is used to select which
  `[ext]` theorems should be used by `grind`. The option `grind +extAll`
  instructs `grind` to use all `[ext]` theorems available in the
  environment.
  After updating stage0, we need to add the builtin `[grind ext]`
  annotations to key theorems such as `funext`.

* [#7950](https://github.com/leanprover/lean4/pull/7950) modifies `all_goals` so that in recovery mode it commits changes
  to the state only for those goals for which the tactic succeeds (while
  preserving the new message log state). Before, we were trusting that
  failing tactics left things in a reasonable state, but now we roll back
  and admit the goal. The changes also fix a bug where we were rolling
  back only the metacontext state and not the tactic state, leading to an
  inconsistent state (a goal list with metavariables not in the
  metacontext). Closes #7883

* [#7952](https://github.com/leanprover/lean4/pull/7952) makes two improvements to the local context when there are
  autobound implicits in `variable`s. First, the local context no longer
  has two copies of every variable (the local context is rebuilt if the
  types of autobound implicits have metavariables). Second, these
  metavariables get names using the same algorithm used by binders that
  appear in declarations (with `mkForallFVars'` instead of
  `mkForallFVars`).

* [#7957](https://github.com/leanprover/lean4/pull/7957) ensures that `mkAppM` can be used to construct terms that are
  only type-correct at default transparency, even if we are in
  `withReducible` (e.g. in `simp`), so that `simp` does not stumble over
  simplifying `let` expression with simplifiable type.reliable.

* [#7961](https://github.com/leanprover/lean4/pull/7961) fixes a bug in `bv_decide` where if it was presented with a match
  on an enum with as many arms as constructors but the last arm being a
  default match it would (wrongly) give up on the match.

* [#7975](https://github.com/leanprover/lean4/pull/7975) reduces the priority of the parent projections of
  `Lean.Grind.CommRing`, to avoid these being used in type class inference
  in Mathlib.

* [#7976](https://github.com/leanprover/lean4/pull/7976) ensure that `bv_decide` can handle the simp normal form of a
  shift.

* [#7978](https://github.com/leanprover/lean4/pull/7978) adds a repro for a non-determinism problem in `grind`.

* [#7980](https://github.com/leanprover/lean4/pull/7980) adds a simple type for representing monomials in a `CommRing`.
  This is going to be used in `grind`.

* [#7986](https://github.com/leanprover/lean4/pull/7986) implements reverse lexicographical and graded reverse
  lexicographical orders for `CommRing` monomials.

* [#7989](https://github.com/leanprover/lean4/pull/7989) adds functions and theorems for `CommRing` multivariate
  polynomials.

* [#7992](https://github.com/leanprover/lean4/pull/7992) add a function for converting `CommRing` expressions into
  multivariate polynomials.

* [#7997](https://github.com/leanprover/lean4/pull/7997) removes all type annotations (optional parameters, auto
  parameters, out params, semi-out params, not just optional parameters as
  before) from the type of functional induction principles.

* [#8011](https://github.com/leanprover/lean4/pull/8011) adds `IsCharP` support to the multivariate‑polynomial library in
  `CommRing`.

* [#8012](https://github.com/leanprover/lean4/pull/8012) adds the option `debug.terminalTacticsAsSorry`. When enabled,
  terminal tactics such as `grind` and `omega` are replaced with `sorry`.
  Useful for debugging and fixing bootstrapping issues.

* [#8014](https://github.com/leanprover/lean4/pull/8014) makes `RArray` universe polymorphic.

* [#8016](https://github.com/leanprover/lean4/pull/8016) fixes several issues in the `CommRing` multivariate polynomial
  library:
  1. Replaces the previous array type with the universe polymorphic
  `RArray`.
  2. Properly eliminates cancelled monomials.
  3. Sorts monomials in decreasing order.
  4. Marks the parameter `p` of the `IsCharP` class as an output
  parameter.
  5. Adds `LawfulBEq` instances for the types `Power`, `Mon`, and `Poly`.

* [#8025](https://github.com/leanprover/lean4/pull/8025) simplifies the `CommRing` monomials, and adds
  1. Monomial `lcm`
  2. Monomial division
  3. S-polynomials

* [#8029](https://github.com/leanprover/lean4/pull/8029) implements basic support for `CommRing` in `grind`. Terms are
  already being reified and normalized. We still need to process the
  equations, but `grind` can already prove simple examples such as:
  ```lean
  open Lean.Grind in
  example [CommRing α] (x : α) : (x + 1)*(x - 1) = x^2 - 1 := by
    磨+环

* [#8032](https://github.com/leanprover/lean4/pull/8032) 添加了对 `grind` 的支持，以检测不可满足的交换
  当环特性已知时，可以求解环方程。示例：
  ```lean
  example (x : Int) : (x + 1)*(x - 1) = x^2 → False := by
    grind +ring

* [#8033](https://github.com/leanprover/lean4/pull/8033) adds functions for converting `CommRing` reified terms back into
  Lean expressions.

* [#8036](https://github.com/leanprover/lean4/pull/8036) fixes a linearity issue in `bv_decide`'s bitblaster, caused by
  the fact that the higher order combinators `AIG.RefVec.zip` and
  `AIG.RefVec.fold` were not being properly specialised.

* [#8042](https://github.com/leanprover/lean4/pull/8042) makes `IntCast` a field of `Lean.Grind.CommRing`, along with
  additional axioms relating it to negation of `OfNat`. This allows use to
  use existing instances which are not definitionally equal to the
  previously given construction.

* [#8043](https://github.com/leanprover/lean4/pull/8043) adds `NullCert` type for representing Nullstellensatz
  certificates that will be produced by the new commutative ring procedure
  in `grind`.

* [#8050](https://github.com/leanprover/lean4/pull/8050) fixes missing trace messages when produced inside `realizeConst`

* [#8055](https://github.com/leanprover/lean4/pull/8055) adds an implementation of an async IO multiplexing framework as
  well as an implementation of it for the `Timer` API in order to
  demonstrate it.

* [#8064](https://github.com/leanprover/lean4/pull/8064) adds a failing `grind` test, showing a bug where grind is trying
  to assign a metavariable incorrectly.

* [#8065](https://github.com/leanprover/lean4/pull/8065) adds a (failing) test case for an obstacle I've been running
  into setting up `grind` for `HashMap`.

* [#8068](https://github.com/leanprover/lean4/pull/8068) ensures that for modules opted into the experimental module
  system, we do not import module docstrings or declaration ranges.

* [#8076](https://github.com/leanprover/lean4/pull/8076) fixes `simp?!`, `simp_all?!` and `dsimp?!` to do auto-unfolding.

* [#8077](https://github.com/leanprover/lean4/pull/8077) adds simprocs to simplify appends of non-overlapping Bitvector
  adds. We add a simproc instead of just a `simp` lemma to ensure that we
  correctly rewrite bitvector appends. Since bitvector appends lead to
  computation at the bitvector width level, it seems to be more stable to
  write a simproc.

* [#8083](https://github.com/leanprover/lean4/pull/8083) fixes #8081.

* [#8086](https://github.com/leanprover/lean4/pull/8086) makes sure that the functional induction principles for mutually
  recursive structural functions with extra parameters are split deeply,
  as expected.

* [#8088](https://github.com/leanprover/lean4/pull/8088) adds the “unfolding” variant of the functional induction and
  functional cases principles, under the name `foo.induct_unfolding` resp.
  `foo.fun_cases_unfolding`. These theorems combine induction over the
  structure of a recursive function with the unfolding of that function,
  and should be more reliable, easier to use and more efficient than just
  case-splitting and then rewriting with equational theorems.

* [#8090](https://github.com/leanprover/lean4/pull/8090) adjusts the experimental module system to elide theorem bodies
  (i.e. proofs) from being imported into other modules.

* [#8094](https://github.com/leanprover/lean4/pull/8094) fixes the generation of functional induction principles for
  functions with nested nested well-founded recursion and late fixed
  parameters. This is a follow-up for #7166. Fixes #8093.

* [#8096](https://github.com/leanprover/lean4/pull/8096) lets `induction` accept eliminator where the motive application
  in the conclusion has complex arguments; these are abstracted over using
  `kabstract` if possible. This feature will go well with unfolding
  induction principles (#8088).

* [#8097](https://github.com/leanprover/lean4/pull/8097) adds support for inductive and coinductive predicates defined
  using lattice theoretic structures on `Prop`. These are syntactically
  defined using `greatest_fixpoint` or `least_fixpoint` termination
  clauses for recursive `Prop`-valued functions. The functionality relies
  on `partial_fixpoint` machinery and requires function definitions to be
  monotone. For non-mutually recursive predicates, an appropriate
  (co)induction proof principle (given by Park induction) is generated.

* [#8101](https://github.com/leanprover/lean4/pull/8101) fixes a parallelism regression where linters that e.g. check for
  errors in the command would no longer find such messages.

* [#8102](https://github.com/leanprover/lean4/pull/8102) allows ASCII `<-` in `if let` clauses, for consistency with
  bind, where both are allowed. Fixes #8098.

* [#8111](https://github.com/leanprover/lean4/pull/8111) adds the helper type class `NoZeroNatDivisors` for the
  commutative ring procedure in `grind`. Core only implements it for
  `Int`. It can be instantiated in Mathlib for any type `A` that
  implements `NoZeroSMulDivisors Nat A`.
  See `findSimp?` and `PolyDerivation` for details on how this instance
  impacts the commutative ring procedure.

* [#8122](https://github.com/leanprover/lean4/pull/8122) implements the generation of compact proof terms for
  Nullstellensatz certificates in the new commutative ring procedure in
  `grind`. Some examples:
  ```lean
  example [CommRing α] (x y : α) : x = 1 → y = 2 → 2*x + y = 4 := by
    磨+环

* [#8126](https://github.com/leanprover/lean4/pull/8126) 实现新交换环程序的主循环
  在 `grind` 中。在主循环中，对于待办事项队列中的每个多项式 `p`，
  程序：
  - 使用当前基础对其进行简化。
  - 使用基础中已有的多项式计算关键对并相加
  他们排队。

* [#8128](https://github.com/leanprover/lean4/pull/8128) 在新的交换环中实现等式传播
  `grind` 中的程序。这个想法是将隐含的平等传播回来
  到执行同余闭包的 `grind` 核心模块。在
  以下示例中，等式：`x^2*y = 1` 和 `x*y^2 - y = 0` 意味着
  `y*x` 等于 `y*x*y`，这通过同余意味着 `f
  (y*x) = f (y*x*y)`。
  ```lean
  example [CommRing α] (x y : α) (f : α → Nat) : x^2*y = 1 → x*y^2 - y = 0 → f (y*x) = f (y*x*y) := by
    grind +ring
  ```

* [#8129](https://github.com/leanprover/lean4/pull/8129) 更新了 If-Normalization 示例，分别给出
  实现并随后证明规范（使用 fun_induction），
  而不是之前直接在子类型中构建术语。在
  同时，添加了一个（失败的）`grind` 测试用例来说明问题
  与未使用的比赛证人。

* [#8131](https://github.com/leanprover/lean4/pull/8131) 添加了一个配置选项，用于控制最大数量
  `grind` 中交换环过程执行的步骤。

* [#8133](https://github.com/leanprover/lean4/pull/8133) 修复了交换环过程使用的单项式阶数
  在 `grind` 中。接下来的新测试现在很快终止。
  ```lean
  example [CommRing α] (a b c : α)
    : a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      a^4 + b^4 + c^4 = 9 := by
    grind +ring
  ```

* [#8134](https://github.com/leanprover/lean4/pull/8134) 确保 `set_option grind.debug true` 在以下情况下正常工作
  使用 `grind +ring`。它还添加了辅助函数 `mkPropEq` 和
  `mkExpectedPropHint`。

* [#8137](https://github.com/leanprover/lean4/pull/8137) 改进了等式传播（也称为理论组合）
  以及未实现环的多项式简化
  `NoZeroNatDivisors`级。通过这些修复，`grind` 现在可以解决：
  ```lean
  example [CommRing α] (a b c : α) (f : α → Nat)
    : a + b + c = 3 →
      a^2 + b^2 + c^2 = 5 →
      a^3 + b^3 + c^3 = 7 →
      f (a^4 + b^4) + f (9 - c^4) ≠ 1 := by
    grind +ring
  ```
  此示例使用交换环过程，线性整数
  算术求解器和同余闭包。
  对于实现 `NoZeroNatDivisors` 的环，多项式现在也是
  除以其系数的最大公约数 (gcd)，当
  被插入到基础中。

* [#8157](https://github.com/leanprover/lean4/pull/8157) 修复了 `replayConst` 的不兼容性，例如
  `aesop` 与 `native_decide` - 使用策略如 `bv_decide`

* [#8158](https://github.com/leanprover/lean4/pull/8158) 修复了 `grind +splitImp` 和箭头传播器。给定`p：
  Prop`, the propagator was incorrectly assuming `A` 始终是
  箭头 `A -> p` 中的命题。还添加了一个缺失的
  标准化规则为 `grind`。

* [#8159](https://github.com/leanprover/lean4/pull/8159) 添加了对以下导入变体的支持
  实验模块系统：

  * `private import`：使导入的常量仅在
  非导出上下文，例如证明。特别是进口不会
  当当前模块被加载或需要存在时
  导入到其他模块中。
  * `import all`：制作非导出信息，例如证明
  导入的模块在当前的非导出上下文中可用
  模块。主要目的是允许对导入进行推理
  定义，否则它们是不透明的。 TODO：调整名称
  分辨率，以便可以通过以下方式访问导入的 `private` 声明
  语法。

* [#8161](https://github.com/leanprover/lean4/pull/8161) 更改 `Lean.Grind.CommRing` 以内联 `NatCast` 实例
  （即由用户提供）而不是从
  现有数据。如果没有这个改变，我们就无法构造实例
  `grind` 可以使用的 Mathlib。

* [#8163](https://github.com/leanprover/lean4/pull/8163) 为 `grind +ring` 添加了一些当前失败的测试，结果
  在内核类型不匹配（错误）或内核深度递归中
  （也许只是一个太大的问题）。

* [#8167](https://github.com/leanprover/lean4/pull/8167) 改进了用于计算基础和简化的启发式方法
  `grind` 中使用的交换过程中的多项式。

* [#8168](https://github.com/leanprover/lean4/pull/8168) 修复了构建证明项时的错误
  新交换环产生的 Nullstellensatz 证书
  `grind` 中的程序。内核拒绝证明项。

* [#8170](https://github.com/leanprover/lean4/pull/8170) 添加了用于在
  `grind` 中使用的交换过程。

* [#8189](https://github.com/leanprover/lean4/pull/8189) 在交换环中实现**逐步证明项**
  `grind` 使用的程序。这些条款可作为替代条款
  传统 Nullstellensatz 证书的代表，旨在
  解决通常相关的**最坏情况指数级复杂性**
  与证书建设。

* [#8231](https://github.com/leanprover/lean4/pull/8231) 更改 `apply?` 的行为，以便它使用 `sorry`
  接近的目标是非合成的。 （回想一下，正确使用合成
  抱歉，策略也会生成错误消息，其中
  我们不想在这种情况下这样做。）此 PR 或 #8230 都是
  足以防御 #8212 中报告的问题。

* [#8254](https://github.com/leanprover/lean4/pull/8254) 修复了 `ToJson`、`FromJson` 和 `Repr` 的意外内联
  实例，这导致 `deriving` 中的编译时间呈指数级增长
  大型结构的条款。

## 图书馆

* [#6081](https://github.com/leanprover/lean4/pull/6081) 将 `inheritEnv` 字段添加到 `IO.Process.SpawnArgs`。如果
  `false`，生成的进程不会继承其父进程的环境。

* [#7108](https://github.com/leanprover/lean4/pull/7108) 证明 `List.head_of_mem_head?` 和类似的
  `List.getLast_of_mem_getLast?`。

* [#7400](https://github.com/leanprover/lean4/pull/7400) 为 `filter`、`map` 和 `filterMap` 函数添加引理
  哈希映射。

* [#7659](https://github.com/leanprover/lean4/pull/7659) 添加 SMT-LIB 运算符来检测溢出
  `BitVec.(umul_overflow, smul_overflow)`，根据定义
  [此处](https://github.com/SMT-LIB/SMT-LIB-2/blob/2.7/Theories/FixedSizeBitVectors.smt2),
  以及证明这些定义与以下等价的定理
  `BitVec` 库函数（`umulOverflow_eq`、`smulOverflow_eq`）。
  这些证明的支持定理是`BitVec.toInt_one_of_lt，
  BitVec.toInt_mul_toInt_lt、BitVec.le_toInt_mul_toInt、
  BitVec.toNat_mul_toNat_lt、BitVec.two_pow_le_toInt_mul_toInt_iff、
  BitVec.toInt_mul_toInt_lt_neg_two_pow_iff` and `Int.neg_mul_le_mul,
  Int.bmod_eq_self_of_le_mul_two，Int.mul_le_mul_of_natAbs_le，
  Int.mul_le_mul_of_le_of_le_of_nonneg_of_nonpos，Int.pow_lt_pow`。公关
  还包括一组测试。

* [#7671](https://github.com/leanprover/lean4/pull/7671) 包含证明有符号除法 x.toInt / 的定理
  y.toInt 仅在 `x = intMin w` 和 `y = allOnes w` 时溢出（对于 `0 <
  w`)。
  为了表明这是发生溢出的*唯一*情况，我们参考
  否定溢出
  (`BitVec.sdivOverflow_eq_negOverflow_of_neg_one`)：事实上，
  `x.toInt/(allOnes w).toInt = - x.toInt`，即溢出条件
  对于 `x` 与 `negOverflow` 相同，然后对符号进行推理
  操作数与各自的定理。
  这些 BitVec 定理本身依赖于许多 `Int.ediv_*` 定理，
  仔细设置整数有符号除法的界限。

* [#7761](https://github.com/leanprover/lean4/pull/7761) 实现 Bitwuzla 重写的核心定理
  [NORM_BV_NOT_OR_SHL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L1495-L1510)
  和
  [BV_ADD_SHL](https://github.com/bitwuzla/bitwuzla/blob/e09c50818b798f990bd84bf61174553fef46d561/src/rewrite/rewrites_bv.cpp#L395-L401),
  它将混合布尔算术表达式转换为纯
  算术表达式：

  ```lean
  theorem add_shiftLeft_eq_or_shiftLeft {x y : BitVec w} :
      x + (y <<< x) =  x ||| (y <<< x)
  ```

* [#7770](https://github.com/leanprover/lean4/pull/7770) 添加共享互斥锁（或读写锁）作为 `Std.SharedMutex`。

* [#7774](https://github.com/leanprover/lean4/pull/7774) 添加了 `Option.pfilter`、`Option.filter` 的变体和几个
  它和其他 `Option` 函数的引理。这些引理被分开
  从#7400开始。

* [#7791](https://github.com/leanprover/lean4/pull/7791) 添加有关 `Nat.lcm` 的引理。

* [#7802](https://github.com/leanprover/lean4/pull/7802) 添加了所有 `Nat.gcd` 和 `Int.gcd` 和 `Int.lcm` 变体
  `Nat.lcm` 引理。

* [#7818](https://github.com/leanprover/lean4/pull/7818) 弃用 `Option.merge` 和 `Option.liftOrGet`，转而使用
  `Option.zipWith`。

* [#7819](https://github.com/leanprover/lean4/pull/7819) 扩展 `Std.Channel` 以提供完全同步和异步 API，如下所示
  以及无界、零大小和有界通道。

* [#7835](https://github.com/leanprover/lean4/pull/7835) 添加 `BitVec.[toInt_append|toFin_append]`。

* [#7847](https://github.com/leanprover/lean4/pull/7847) 从所有已弃用的定理中删除 `@[simp]`。 `simp` 将
  仍然使用这样的引理，没有任何警告消息。

* [#7851](https://github.com/leanprover/lean4/pull/7851) 部分恢复 #7818，因为调用的函数
  `Option.zipWith` 中的 PR 实际上并不对应于
  `List.zipWith`。我们选择 `Option.merge` 作为名称。

* [#7855](https://github.com/leanprover/lean4/pull/7855) 将 `ReflBEq` 移动到 `Init.Core` 并更改 `LawfulBEq` 以扩展
  `ReflBEq`。

* [#7856](https://github.com/leanprover/lean4/pull/7856) 更改定义和定理以不使用成员资格
  instance on `Option` unless the theorem is specifically about the
  会员资格实例。

* [#7869](https://github.com/leanprover/lean4/pull/7869) 修复了 #7445 中引入的回归，其中新的
  `Array.emptyWithCapacity` 意外地没有标记正确的
  函数来实际分配容量。

* [#7871](https://github.com/leanprover/lean4/pull/7871) 概括了单子 `Option` 上的类型类假设
  功能。

* [#7879](https://github.com/leanprover/lean4/pull/7879) 添加 `Int.toNat_emod`，类似于 `Int.toNat_add/mul`。

* [#7880](https://github.com/leanprover/lean4/pull/7880) 添加函数 `UIntX.ofInt` 和基本引理。

* [#7886](https://github.com/leanprover/lean4/pull/7886) 添加 `UIntX.pow` 和 `Pow UIntX Nat` 实例，类似地
  签名为 固定位宽整数。这些目前还只是幼稚的
  实施，并且随后需要通过替换
  `@[extern]` 具有快速实现（追踪于#7887）。

* [#7888](https://github.com/leanprover/lean4/pull/7888) 添加 `Fin.ofNat'_mul` 和 `Fin.mul_ofNat'`，与
  关于 `add` 的现有引理。

* [#7889](https://github.com/leanprover/lean4/pull/7889) 添加了 `Int.toNat_sub''` 的 `Int.toNat_sub` 变体
  不平等假设，而不是期望论证被提出
  自然数。这与现有的 `toNat_add` 平行，并且
  `toNat_mul`。

* [#7890](https://github.com/leanprover/lean4/pull/7890) 添加关于 `Int.bmod` 的缺失引理，与关于 `Int.bmod` 的引理平行
  其他 `mod` 变体。

* [#7891](https://github.com/leanprover/lean4/pull/7891) 为 `x : Int` 添加 rfl simpl 引理 `Int.cast x = x`。

* [#7893](https://github.com/leanprover/lean4/pull/7893) 添加 `BitVec.pow` 和 `Pow (BitVec w) Nat`。实施情况
  是幼稚的，稍后应该被 `@[extern]` 取代。这个
  追踪于 https://github.com/leanprover/lean4/issues/7887.

* [#7897](https://github.com/leanprover/lean4/pull/7897) 清理 `Option` 开发，将一些结果上传到上游
  在此过程中来自 mathlib 。

* [#7899](https://github.com/leanprover/lean4/pull/7899) 随机排列一些有关整数的结果，以确保
  当前存在的有关 `Int.bmod` 的所有材料均位于
  `DivMod/Lemmas.lean` 而不是其下游。

* [#7901](https://github.com/leanprover/lean4/pull/7901) 添加 `instance [Pure f] : Inhabited (OptionT f α)`，以便
  `Inhabited (OptionT Id Empty)` 合成。

* [#7912](https://github.com/leanprover/lean4/pull/7912) 添加 `List.Perm.take/drop` 和 `Array.Perm.extract`，
  当子列表/子数组恒定时，将排列限制为子列表/子数组
  其他地方。

* [#7913](https://github.com/leanprover/lean4/pull/7913) 添加了一些缺失的 `List/Array/Vector lemmas`
  `isSome_idxOf?`，`isSome_finIdxOf?`，`isSome_findFinIdx？，
  `isSome_findIdx?` 和相应的 `isNone` 版本。

* [#7933](https://github.com/leanprover/lean4/pull/7933) 添加有关 `Int.bmod` 的引理以实现奇偶校验
  `Int.bmod` 和 `Int.emod`/`Int.fmod`/`Int.tmod`。此外，它还添加了
  缺少 `emod`/`fmod`/`tmod` 的引理并对名称执行清理
  以及所有四项行动的声明，也是为了
  增加与相应 `Nat.mod` 引理的一致性。

* [#7938](https://github.com/leanprover/lean4/pull/7938) 添加有关 `List/Array/Vector.countP/count` 交互的引理
  与 `replace`。 （专门针对 `_self` 和 `_ne` 引理似乎并不
  很有用，因为 RHS 上仍然有 `if`。）

* [#7939](https://github.com/leanprover/lean4/pull/7939) 添加了 `Array.count_erase` 和专业化。

* [#7953](https://github.com/leanprover/lean4/pull/7953) 概括了 `List.Perm` API 中的一些类型类假设
  （远离 `DecidableEq`），并复制 `List.Perm.mem_iff`
  `Array`，并修复了`Array.Perm.extract`语句中的错误。

* [#7971](https://github.com/leanprover/lean4/pull/7971) 来自 `Mathlib/Data/Nat/Init.lean` 的大部分材料的上游
  和 `Mathlib/Data/Nat/Basic.lean`。

* [#7983](https://github.com/leanprover/lean4/pull/7983) 将 `Mathlib/Data/Int/Init.lean` 的许多结果上传到上游。

* [#7994](https://github.com/leanprover/lean4/pull/7994) 为 `Vector` 重现 `Array.Perm` API。两人都还在
  `List.Perm` 的开发程度明显低于 API。

* [#7999](https://github.com/leanprover/lean4/pull/7999) 将 `Array.Perm` 和 `Vector.Perm` 替换为单字段
  结构。这可以避免 `List` 的点表示法像例如
  `h.cons 3`，其中 `h` 是 `Array.Perm`。

* [#8000](https://github.com/leanprover/lean4/pull/8000) 弃用一些 `Int.ofNat_*` 引理，转而使用
  `Int.natCast_*`。

* [#8004](https://github.com/leanprover/lean4/pull/8004) 在名称下添加扩展哈希映射和哈希集
  `Std.ExtDHashMap`、`Std.ExtHashMap` 和 `Std.ExtHashSet`。外延性
  哈希映射的工作方式与常规哈希映射类似，只是它们具有
  外延引理使它们更容易在证明中使用。这个
  然而，也无法定期迭代其条目。

* [#8030](https://github.com/leanprover/lean4/pull/8030) 添加了一些缺失的引理
  `List/Array/Vector.findIdx?/findFinIdx?/findSome?/idxOf?`。

* [#8044](https://github.com/leanprover/lean4/pull/8044) 介绍模块 `Std.Data.DTreeMap.Raw`，
  `Std.Data.TreeMap.Raw` 和 `Std.Data.TreeSet.Raw` 并将它们导入
  `Std.Data`。与原始树图相关的所有模块都导入到
  这些新模块现在是 `Std` 的传递依赖项。

* [#8067](https://github.com/leanprover/lean4/pull/8067) 修复了 `Substring.isNat` 不允许为空的行为
  字符串。

* [#8078](https://github.com/leanprover/lean4/pull/8078) 是 #8055 的后续版本，并实现了异步 `Selector`
  TCP 为了允许 IO 使用 TCP 套接字进行复用。

* [#8080](https://github.com/leanprover/lean4/pull/8080) 修复了 `Json.parse` 以正确处理代理对。

* [#8085](https://github.com/leanprover/lean4/pull/8085) 将强制 `α → Option α` 移动到新文件
  `Init.Data.Option.Coe`。该文件可能无法导入到 `Init` 中的任何位置
  或 `Std`。

* [#8089](https://github.com/leanprover/lean4/pull/8089) 为 `Int` 和 `Nat` 添加优化的除法函数
  已知参数是可整除的（例如在标准化时
  有理）。这些由 gmp 函数 `mpz_divexact` 和
  `mpz_divexact_ui`。另请参阅leanprover-community/batteries#1202。

* [#8136](https://github.com/leanprover/lean4/pull/8136) 添加一组初始 `@[grind]` 注释
  `List`/`Array`/`Vector`，足以使用以下命令设置一些回归测试
  关于 `List` 的证明中的 `grind`。更多注释请关注。

* [#8139](https://github.com/leanprover/lean4/pull/8139) 是 #8055 的后续版本，并实现了异步 `Selector`
  UDP 以允许 IO 使用 UDP 套接字进行复用。

* [#8144](https://github.com/leanprover/lean4/pull/8144) 将 `Option.guard` 的谓词更改为 `p : α → Bool`
  而不是 `p : α → Prop`。这使其与其他同类产品保持一致
  功能类似于 `Option.filter`。

* [#8147](https://github.com/leanprover/lean4/pull/8147) 添加 `List.findRev?` 和 `List.findSomeRev?`，用于与
  现有的数组 API，以及将它们转换为现有的简单引理
  操作。

* [#8148](https://github.com/leanprover/lean4/pull/8148) 概括 `List.eraseDups` 以允许任意
  比较关系。此外，它证明了 `eraseDups_append : (as ++
  bs).eraseDups = as.eraseDups ++ (bs.removeAll as).eraseDups`。

* [#8150](https://github.com/leanprover/lean4/pull/8150) 是 #8055 的后续版本，并实现了一个选择器
  `Std.Channel` 为了允许
   使用通道进行复用。

* [#8154](https://github.com/leanprover/lean4/pull/8154) 添加无条件引理
  `HashMap.getElem?_insertMany_list` 以及现有的
  有相当强的前提条件。也适用于 TreeMap（和
  依赖/扩展变体）。

* [#8175](https://github.com/leanprover/lean4/pull/8175) 添加了有关 `List`/`Array`/`Vector.contains` 的简化/研磨引理。
  在存在 `LawfulBEq` 的情况下，这些实际上已经通过
  将 `contains` 简化为 `mem`，但现在这些也无需
  `LawfulBEq`。

* [#8184](https://github.com/leanprover/lean4/pull/8184) 为所有地图变体添加 `insertMany_append` 引理。

## 编译器

* [#6063](https://github.com/leanprover/lean4/pull/6063) 更新了 LLVM 和 clang 所使用和附带的版本
  Lean 至 19.1.2

* [#7824](https://github.com/leanprover/lean4/pull/7824) 修复了使用“不可计算”定义时可能会出现的问题
  错误编译，同时还删除了“不可计算”的使用
  完全定义。 “不可计算”定义的一些用途（例如
  Classical.propDecidable) 无法通过类型擦除正确编译。
  对结果运行优化器可以导致它们被优化
  远离，逃避后来对不可计算的使用的 IR 级别检查
  定义。

* [#7838](https://github.com/leanprover/lean4/pull/7838) 添加了对 mpz 对象（即大数字）的支持
  `shareCommon` 功能。

* [#7854](https://github.com/leanprover/lean4/pull/7854) 引入了基本的 API 来分发模块数据
  为模块系统做准备的多个文件。

* [#7945](https://github.com/leanprover/lean4/pull/7945) 修复了 `IO.getTaskState` 与中的任务之间的潜在竞争
  问题完成，导致未定义的行为。

* [#7958](https://github.com/leanprover/lean4/pull/7958) 确保 `main` 完成后我们仍然等待专用
  任务而不是强行退出。如果用户想暴力杀人
  他们的专用任务在 main 末尾，而不是他们可以运行
  `IO.Process.exit` 改为 `main` 末尾。

* [#7990](https://github.com/leanprover/lean4/pull/7990) 在新代码中更多类型擦除的情况下采用 lcAny
  发电机。

* [#7996](https://github.com/leanprover/lean4/pull/7996) 在基础阶段禁用局部函数声明的 CSE
  新的编译器。这引入了 lambda 之间的共享以进行绑定
  使用 `do` 表示法进行调用，这导致它们后来不再被内联。

* [#8006](https://github.com/leanprover/lean4/pull/8006) 将新代码生成器的内联启发式更改为
  与旧的匹配，这确保单子折叠得到充分的
  内联以便将尾递归暴露给代码生成器。

* [#8007](https://github.com/leanprover/lean4/pull/8007) 将新编译器中的 eager lambda 提升启发式更改为
  匹配旧的编译器，这确保内联/专门化一元
  代码不会意外地创建相互尾递归，该代码
  发电机无法处理。

* [#8008](https://github.com/leanprover/lean4/pull/8008) 更改新代码生成器中的专业化以考虑
  被调用者参数是地面变量，这提高了专业化
  的多态函数。

* [#8009](https://github.com/leanprover/lean4/pull/8009) 限制在 case 表达式之外提升 a 的值
  可判定类型，因为我们无法正确表示对
  在编译器的后期阶段删除了命题。

* [#8010](https://github.com/leanprover/lean4/pull/8010) 修复带有 Implemented_by 的 caseOn 表达式以使其正常工作
  即使精化器生成项，也可以正确使用哈希 consing
  重建判别式而不仅仅是重用变量。

* [#8015](https://github.com/leanprover/lean4/pull/8015) 修复了 IR elim_dead_branches 传递以正确处理连接
  没有参数的点，目前被认为是无法访问的。我是
  无法使用旧编译器找到简单的重现，但它
  使用新编译器引导 Lean 时会发生这种情况。

* [#8017](https://github.com/leanprover/lean4/pull/8017) 使 IR elim_dead_branches 正确传递句柄 extern
  函数通过将它们视为具有最高返回值来实现。这个修复是
  使用新编译器引导 Init/ 目录是必需的。

* [#8023](https://github.com/leanprover/lean4/pull/8023) 修复了 IR Expand_reset_reuse 传递以正确处理
  来自相同基数/索引的重复投影。这不会发生（在
  使用旧编译器最不容易），但在引导时会发生
  使用新编译器的 Lean。

* [#8124](https://github.com/leanprover/lean4/pull/8124) 正确处理 LCNF 中的转义函数
  elimDeadBranches 通过，将所有参数设置为 top 而不是
  可能会使它们保持默认底部值。

* [#8125](https://github.com/leanprover/lean4/pull/8125) 向新编译器添加了对 `init` 属性的支持。

* [#8127](https://github.com/leanprover/lean4/pull/8127) 在新编译器中添加了对借用参数的支持，这
  需要在 LCNF 类型处理中添加对 .mdata 表达式的支持。

* [#8132](https://github.com/leanprover/lean4/pull/8132) 添加了对降低新版本中内置类型的 `casesOn` 的支持
  编译器。

* [#8156](https://github.com/leanprover/lean4/pull/8156) 修复了旧编译器的 lcnf 转换 expr 缓存的错误
  未在密钥中包含所有相关信息，导致
  术语不经意地被删除。 `root` 变量用于
  确定应用程序的 lambda 参数是否应该被 let
  绑定与否，这反过来会影响以后关于类型的决定
  擦除（erase_irrelevant 假设任何非原子参数都是
  无关）。

* [#8236](https://github.com/leanprover/lean4/pull/8236) 修复了 `extern_lib` 和
  `precompileModules` 会导致“找不到符号”错误。

## 漂亮的印刷

* [#7805](https://github.com/leanprover/lean4/pull/7805) 修改原始自然数文字的漂亮打印；现在
  `pp.explicit` 和 `pp.natLit` 均启用 `nat_lit` 前缀。安
  这样做的效果是，将鼠标悬停在信息视图中的此类文字上
  `nat_lit` 前缀。

* [#7812](https://github.com/leanprover/lean4/pull/7812) 修改 pi 类型的漂亮打印。现在 `∀` 将是
  如果域不是命题，则命题优先于 `→`。
  例如，`∀ (n : Nat), True` 漂亮地打印为 `∀ (n : Nat), True`
  而不是 `Nat → True`。现在还有一个选项 `pp.foralls`
  （默认 true）当 false 时完全禁用使用 `∀`，对于
  教学目的。还调整实例隐式绑定器
  漂亮的打印 - 独立的 pi 类型不会显示实例绑定器
  名字。关闭#1834。

* [#7813](https://github.com/leanprover/lean4/pull/7813) 修复了 Infoview 中 `let n : Nat := sorry` 的问题
  漂亮的打印如 ``n : ℕ := 抱歉 `«Foo:17:17»``。这是由于
  顶级表达式的打印规则与
  信息视图悬停。关闭#6715。重构`Lean.Widget.ppExprTagged`；现在
  这需要一个delaborator，下游用户应该配置自己的
  如果他们使用 `explicit`，则如有必要，漂亮的打印机选项将被覆盖
  参数（有关示例，请参见 `Lean.Widget.makePopup.ppExprForPopup`）。
  重大更改：`ppExprTagged` 未在根目录上设置 `pp.proofs`
  表达。

* [#7840](https://github.com/leanprover/lean4/pull/7840) 导致结构实例符号被标记为
  当 `pp.tagAppFns` 为 true 时构造函数。这将使 docgen 将具有
  `{` 和 `}` 链接到结构构造函数。

* [#8022](https://github.com/leanprover/lean4/pull/8022) 修复了在上下文中完成漂亮打印的错误
  清除本地实例。这些已被清除，因为本地上下文是
  在名称清理步骤期间更新，但保留本地实例
  有效，因为对本地上下文的修改仅影响用户
  名称。

## 文档

* [#7947](https://github.com/leanprover/lean4/pull/7947) 添加了一些文档字符串来阐明
  `Lean.mkFreshId`、`Lean.Core.mkFreshUserName`、
  `Lean.Elab.Term.mkFreshBinderName`，和
  `Lean.Meta.mkFreshBinderNameForTactic`。

* [#8018](https://github.com/leanprover/lean4/pull/8018) 将 RArray 文档字符串调整为 #8014 中的新现实。

## 服务器

* [#7610](https://github.com/leanprover/lean4/pull/7610) 调整 `TryThis` 小部件以在小部件消息中也起作用
  而不仅仅是作为面板小部件。它还添加了额外的
  解释为什么需要进行此更改的文档。

* [#7873](https://github.com/leanprover/lean4/pull/7873) 修复了一些与源处理相关的错误
  语言服务器中的搜索路径，删除文件可能会导致
  几个功能停止运行，无标题文件和文件
  光盘上不存在的模块名称可能会发生冲突。

* [#7882](https://github.com/leanprover/lean4/pull/7882) 修复了先前文档的精化的回归
  版本不会因文档更改而取消。

* [#8242](https://github.com/leanprover/lean4/pull/8242) 修复了“目标已完成”诊断。他们是
  在#7902 中意外损坏。

## Lake

* [#7796](https://github.com/leanprover/lean4/pull/7796) 将 Lean 的共享库路径移动到工作区之前
  Lake 的增强环境（例如 `lake env`）。

* [#7809](https://github.com/leanprover/lean4/pull/7809) 修复了通过以下方式加载库时的顺序
  `lean` 中的 `--load-dynlib` 或 `--plugin` 以及将它们链接到
  共享库或可执行文件。 `Dynlib` 现在跟踪其依赖关系并
  它们在传递给链接或链接之前先进行拓扑排序
  正在加载。

* [#7822](https://github.com/leanprover/lean4/pull/7822) 将 Lake 更改为对其各种内容使用标准化绝对路径
  文件和目录。

* [#7860](https://github.com/leanprover/lean4/pull/7860) 恢复内置函数的使用（例如初始化器、精化器、
  和宏）了解 DSL 功能以及 Lake 插件在
  服务器。

* [#7906](https://github.com/leanprover/lean4/pull/7906) 更改 Lake 构建跟踪以跟踪其混合输入。的
  跟踪的输入保存为 `.trace` 文件的一部分，该文件可以
  极大地帮助调试跟踪问题。此外，这个公关
  调整一些现有的 Lake 轨迹。最重要的模块 olean 痕迹
  不再合并其模块的源跟踪。

* [#7909](https://github.com/leanprover/lean4/pull/7909) 添加了 Lake 对在给定源文件的情况下构建模块的支持
  路径。 CLI 和服务器均使用此功能。

* [#7963](https://github.com/leanprover/lean4/pull/7963) 添加辅助函数以在 `Lake.EStateT` 和
  `EStateM`。

* [#7967](https://github.com/leanprover/lean4/pull/7967) 在 Lake 中添加了 `bootstrap` 选项，用于标识
  核心Lean封装。这使得 Lake 能够使用当前阶段的包含
  使用 Lean 编译 Lean 时的目录而不是 Lean 工具链
  在核心。

* [#7987](https://github.com/leanprover/lean4/pull/7987) 修复了 #7967 中破坏外部库链接的错误。

* [#8026](https://github.com/leanprover/lean4/pull/8026) 修复了 #7809 和 #7909 中未部分捕获的错误
  因为 `badImport` 测试已被禁用。

* [#8048](https://github.com/leanprover/lean4/pull/8048) 将 Lake DSL 语法移动到专用模块中，只需最少的
  进口。

* [#8152](https://github.com/leanprover/lean4/pull/8152) 修复了非预编译模块构建会出现的回归问题
  `--load-dynlib` 封装 `extern_lib` 目标。

* [#8183](https://github.com/leanprover/lean4/pull/8183) 使 Lake 测试的输出更加详细。它还修复了一些
  由于禁用测试而错过的错误。最重要的是，
  目标说明符 `@pkg`（例如，在 `lake build` 中）现在始终
  解释为一个包。之前它被含糊地解释为
  #7909 中的更改。

* [#8190](https://github.com/leanprover/lean4/pull/8190) 添加本机库选项的文档（例如 `dynlibs`、
  `plugins`、`moreLinkObjs`、`moreLinkLibs`) 和 `needs` 至 Lake
  自述文件。它还包括有关指定目标的信息
  Lake CLI 以及 Lean 和 TOML 配置文件中。

## 其他

* [#7785](https://github.com/leanprover/lean4/pull/7785) 为发布过程添加了进一步的自动化，处理
  标记并自动创建新的 `bump/v4.X.0` 分支，以及
  修复一些错误。

* [#7789](https://github.com/leanprover/lean4/pull/7789) 修复了 `lean` 可能更改或解释参数的问题
  `--run` 之后。

* [#8060](https://github.com/leanprover/lean4/pull/8060) 修复了 Lean内核中的错误。在减少`Nat.pow`期间，
  内核未验证第一个参数的 WHNF 是否为
  `Nat` 文字，然后将其解释为 `mpz` 数字。添加
  丢失的支票。


````
