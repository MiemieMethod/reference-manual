/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Anne Baanen
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.23.0 (2025-09-15)" =>
%%%
tag := "release-v4.23.0"
file := "v4.23.0"
%%%

````markdown
For this release, 610 changes landed. In addition to the 95 feature additions and 139 fixes listed below there were 61 refactoring changes, 12 documentation improvements, 71 performance improvements, and 232 other changes.

## Highlights
%%%
tag := "zh-releases-v4-23-0-h001"
%%%

Lean v4.23.0 release brings significant performance improvements, better error messages,
and a plethora of bug fixes, refinements, and consolidations in `grind`, the compiler, and other components of Lean.

In terms of user experience, noteworthy new features are:

- Improved 'Go to Definition' navigation ([#9040](https://github.com/leanprover/lean4/pull/9040))

  - Using 'Go to Definition' on a type class projection now extracts
    the specific instances that were involved and provides them as locations
    to jump to. For example, using 'Go to Definition' on the `toString` of
    `toString 0` yields results for `ToString.toString` and `ToString Nat`.
  - Using 'Go to Definition' on a macro that produces syntax with type
    class projections now also extracts the specific instances that were
    involved and provides them as locations to jump to. For example, using
    'Go to Definition' on the `+` of `1 + 1` yields results for
    `HAdd.hAdd`, `HAdd α α α` and `Add Nat`.
  - Using 'Go to Declaration' now provides all the results of 'Go to
    Definition' in addition to the elaborator and the parser that were
    involved. For example, using 'Go to Declaration' on the `+` of `1 + 1`
    yields results for `HAdd.hAdd`, `HAdd α α α`, `Add Nat`,
    `` macro_rules | `($x + $y) => ... `` and `infixl:65 " + " => HAdd.hAdd`.
  - Using 'Go to Type Definition' on a value with a type that contains
    multiple constants now provides 'Go to Definition' results for each
    constant. For example, using 'Go to Type Definition' on `x` for `x : Array Nat`
    yields results for `Array` and `Nat`.

- Interactive code-action hints for errors:

  - for "invalid named argument" error, suggest valid argument names ([#9315](https://github.com/leanprover/lean4/pull/9315))

  - for "invalid case name" error, suggest valid case names ([#9316](https://github.com/leanprover/lean4/pull/9316))

  - for "fields missing" error in structure instances, suggest to insert all the missing fields ([#9317](https://github.com/leanprover/lean4/pull/9317))

  You can try all of these in the [Lean playground](https://live.lean-lang.org/#codez=PQWghAUAxABAEgSwHYBcDOMBmB7ATjZANwEMAbBAExiWIFsBTK43AcwFcHUNkYAHYlCnq4kaCCGAQIyCmwDGKBIXowAKjADuAC2H0IMGAB8YtANYBGGAAoAHjACeMAF4wAXDABC2bKQCUU+hs6XlIVKxQ3NV83AF59EwE5LRgIjQQULXjjADozSytHVxiU3DZ6aKsNWJKyipcirDI0cpgYgD5rfylQSFhELiw8GDliZuo6ejEJAKDaELCAI0ivH2j3ADkBaoX7eJHmjAW90ZUkbCRAhDQhVFa2+IM0UwRebvBoeGR0QfxaK7RkCwYNdSgo2LgVMhrsQkHIVJgEPRSBQppIICD5ChwSoAMqaHQQ+IIpEUSwbARExHIgBMkQAavQFENNhFicjzDNgqFIniivEAN4AXwgQA).

### Breaking Changes
%%%
tag := "zh-releases-v4-23-0-h002"
%%%

- [#9800](https://github.com/leanprover/lean4/pull/9800) improves the delta deriving handler, giving it the ability to
  process definitions with binders, as well as the ability to recursively
  unfold definitions. **Breaking change**: the
  derived instance's name uses the `instance` command's name generator,
  and the new instance is added to the current namespace.

- [#9040](https://github.com/leanprover/lean4/pull/9040) improves the 'Go to Definition' UX.
  **Breaking change**: `InfoTree.hoverableInfoAt?` has been generalized to
  `InfoTree.hoverableInfoAtM?` and now takes a general `filter` argument
  instead of several boolean flags, as was the case before.

- [#9594](https://github.com/leanprover/lean4/pull/9594) optimizes `Lean.Name.toString`, giving a 10% instruction
  benefit.

  Crucially this is a **breaking change** as the old `Lean.Name.toString`
  method used to support a method for identifying tokens. This method is
  now available as `Lean.Name.toStringWithToken` in order to allow for
  specialization of the (highly common) `toString` code path which sets
  this function to just return `false`.

- [#9729](https://github.com/leanprover/lean4/pull/9729) introduces a canonical way to endow a type with an order
  structure. **Breaking changes:**

  - The requirements of the `lt_of_le_of_lt`/`le_trans` lemmas for
    `Vector`, `List` and `Array` are simplified. They now require an
    `IsLinearOrder` instance. The new requirements are logically equivalent
    to the old ones, but the `IsLinearOrder` instance is not automatically
    inferred from the smaller type classes.
  - Hypotheses of type `Std.Total (¬ · < · : α → α → Prop)` are replaced
    with the equivalent class `Std.Asymm (· < · : α → α → Prop)`. Breakage
    should be limited because there is now an instance that derives the
    latter from the former.
  - In `Init.Data.List.MinMax`, multiple theorem signatures are modified,
    replacing explicit parameters for antisymmetry, totality, `min_ex_or`
    etc. with corresponding instance parameters.

## Language
%%%
tag := "zh-releases-v4-23-0-h003"
%%%

* [#6732](https://github.com/leanprover/lean4/pull/6732) adds support for the `clear` tactic in conversion mode.

* [#8666](https://github.com/leanprover/lean4/pull/8666) adjusts the experimental module system to not import the IR of
  non-`meta` declarations. It does this by replacing such IR with opaque
  foreign declarations on export and adjusting the new compiler
  accordingly.

* [#8842](https://github.com/leanprover/lean4/pull/8842) fixes the bug that `collectAxioms` didn't collect axioms
  referenced by other axioms. One of the results of this bug is that
  axioms collected from a theorem proved by `native_decide` may not
  include `Lean.trustCompiler`.

* [#9015](https://github.com/leanprover/lean4/pull/9015) makes `isDefEq` detect more stuck definitional equalities
  involving smart unfoldings. Specifically, if `t =?= defn ?m` and `defn`
  matches on its argument, then this equality is stuck on `?m`. Prior to
  this change, we would not see this dependency and simply return `false`.

* [#9084](https://github.com/leanprover/lean4/pull/9084) adds `binrel%` macros for `!=` and `≠` notation defined in
  `Init.Core`. This allows the elaborator to insert coercions on both
  sides of the relation, instead of committing to the type on the left
  hand side.

* [#9090](https://github.com/leanprover/lean4/pull/9090) fixes a bug in `whnfCore` where it would fail to reduce
  applications of recursors/auxiliary defs.

* [#9097](https://github.com/leanprover/lean4/pull/9097) ensures that `mspec` uses the configured transparency setting
  and makes `mvcgen` use default transparency when calling `mspec`.

* [#9099](https://github.com/leanprover/lean4/pull/9099) improves the “expected type mismatch” error message by omitting
  the type's types when they are defeq, and putting them into separate
  lines when not.

* [#9103](https://github.com/leanprover/lean4/pull/9103) prevents truncation of `panic!` messages containing null bytes.

* [#9108](https://github.com/leanprover/lean4/pull/9108) fixes an issue that may have caused inline expressions in
  messages to be unnecessarily rendered on a separate line.

* [#9113](https://github.com/leanprover/lean4/pull/9113) improves the `grind` doc string and tries to make it more
  approachable to new user.

* [#9130](https://github.com/leanprover/lean4/pull/9130) fixes unexpected occurrences of the `Grind.offset` gadget in
  ground patterns. See new test

* [#9131](https://github.com/leanprover/lean4/pull/9131) adds a `usedLetOnly` parameter to `LocalContext.mkLambda` and
  `LocalContext.mkForall`, to parallel the `MetavarContext` versions.

* [#9133](https://github.com/leanprover/lean4/pull/9133) adds support for `a^(m+n)` in the `grind` normalizer.

* [#9143](https://github.com/leanprover/lean4/pull/9143) removes a rather ugly hack in the module system, exposing the
  bodies of theorems whose type mention `WellFounded`.

* [#9146](https://github.com/leanprover/lean4/pull/9146) adds "safe" polynomial operations to `grind ring`. The use the
  usual combinators: `withIncRecDepth` and `checkSystem`.

* [#9149](https://github.com/leanprover/lean4/pull/9149) generalizes the `a^(m+n)` grind normalizer to any semirings.
  Example:
  ```
  variable [Field R]

* [#9150](https://github.com/leanprover/lean4/pull/9150) 在 `grind` 中使用的 `toPoly` 函数中添加了缺失的情况。

* [#9153](https://github.com/leanprover/lean4/pull/9153) 改进了 linarith `markVars`，并确保它不会
  产生虚假的问题消息。

* [#9168](https://github.com/leanprover/lean4/pull/9168) 解决了 defeq 菱形，该菱形导致 Mathlib 中出现问题：
  ```
  import Mathlib

* [#9172](https://github.com/leanprover/lean4/pull/9172) fixes a bug at `matchEqBwdPat`. The type may contain pattern
  variables.

* [#9173](https://github.com/leanprover/lean4/pull/9173) fixes an incompatibility in the experimental module system when
  trying to combine wellfounded recursion with public exposed definitions.

* [#9176](https://github.com/leanprover/lean4/pull/9176) makes `mvcgen` split ifs rather than applying specifications.
  Doing so fixes a bug reported by Rish.

* [#9182](https://github.com/leanprover/lean4/pull/9182) tries to improve the E-matching pattern inference for `grind`.
  That said, we still need better tools for annotating and maintaining
  `grind` annotations in libraries.

* [#9184](https://github.com/leanprover/lean4/pull/9184) fixes stealing of `⇓` syntax by the new notation for total
  postconditions by demoting it to non-builtin syntax and scoping it to
  `Std.Do`.

* [#9191](https://github.com/leanprover/lean4/pull/9191) lets the equation compiler unfold abstracted proofs again if
  they would otherwise hide recursive calls.

  This fixes #8939.

* [#9193](https://github.com/leanprover/lean4/pull/9193) fixes the unexpected kernel projection issue reported by issue
  #9187

* [#9194](https://github.com/leanprover/lean4/pull/9194) makes the logic and tactics of `Std.Do` universe polymorphic, at
  the cost of a few definitional properties arising from the switch from
  `Prop` to `ULift Prop` in the base case `SPred []`.

* [#9196](https://github.com/leanprover/lean4/pull/9196) implements `forall` normalization using a simproc instead of
  rewriting rules in `grind`. This is the first part of the PR; after
  updating stage0, we must remove the normalization theorems.

* [#9200](https://github.com/leanprover/lean4/pull/9200) implements `exists` normalization using a simproc instead of
  rewriting rules in `grind`. This is the first part of the PR; after
  updating stage0, we must remove the normalization theorems.

* [#9202](https://github.com/leanprover/lean4/pull/9202) extends the `Eq` simproc used in `grind`. It covers more cases
  now. It also adds 3 reducible declarations to the list of declarations
  to unfold.

* [#9214](https://github.com/leanprover/lean4/pull/9214) implements support for local and scoped `grind_pattern`
  commands.

* [#9225](https://github.com/leanprover/lean4/pull/9225) improves the `congr` tactic so that it can handle function
  applications with fewer arguments than the arity of the head function.
  This also fixes a bug where `congr` could not make progress with
  `Set`-valued functions in Mathlib, since `Set` was being unfolded and
  making such functions have an apparently higher arity.

* [#9228](https://github.com/leanprover/lean4/pull/9228) improves the startup time for `grind ring` by generating the
  required type classes on demand. This optimization is particularly
  relevant for files that make hundreds of calls to `grind`, such as
  `tests/lean/run/grind_bitvec2.lean`. For example, before this change,
  `grind` spent 6.87 seconds synthesizing type classes, compared to 3.92
  seconds after this PR.

* [#9241](https://github.com/leanprover/lean4/pull/9241) ensures that the type class instances used to implement the
  `ToInt` adapter (in `grind cutsat`) are generated on demand.

* [#9244](https://github.com/leanprover/lean4/pull/9244) improves the instance generation in the `grind linarith` module.

* [#9251](https://github.com/leanprover/lean4/pull/9251) demotes the builtin elaborators for `Std.Do.PostCond.total` and
  `Std.Do.Triple` into macros, following the DefEq improvements of #9015.

* [#9267](https://github.com/leanprover/lean4/pull/9267) optimizes support for `Decidable` instances in `grind`. Because
  `Decidable` is a subsingleton, the canonicalizer no longer wastes time
  normalizing such instances, a significant performance bottleneck in
  benchmarks like `grind_bitvec2.lean`. In addition, the
  congruence-closure module now handles `Decidable` instances, and can
  solve examples such as:
  ```lean
  example (p q : Prop) (h₁ : Decidable p) (h₂ : Decidable (p ∧ q)) : (p ↔ q) → h₁ ≍ h₂ := by
    磨
  ```

* [#9271](https://github.com/leanprover/lean4/pull/9271) improves the performance of the formula normalizer used in
  `grind`.

* [#9287](https://github.com/leanprover/lean4/pull/9287) rewords the "application type mismatch" error message so that
  the argument and its type precede the application expression.

* [#9293](https://github.com/leanprover/lean4/pull/9293) replaces the `reduceCtorEq` simproc used in `grind` by a much
  more efficient one. The default one use in `simp` is just overhead
  because the `grind` normalizer is already normalizing arithmetic.
  In a separate PR, we will push performance improvements to the default
  `reduceCtorEq`.

* [#9305](https://github.com/leanprover/lean4/pull/9305) uses the `mkCongrSimpForConst?` API in `simp` to reduce the
  number of times the same congruence lemma is generated. Before this PR,
  `grind` would spend `1.5`s creating congruence theorems during
  normalization in the `grind_bitvec2.lean` benchmark. It now spends
  `0.6`s. should make an even bigger difference after we merge
  #9300.

* [#9315](https://github.com/leanprover/lean4/pull/9315) adds improves the "invalid named argument" error message in
  function applications and match patterns by providing clickable hints
  with valid argument names. In so doing, it also fixes an issue where
  this error message would erroneously flag valid match-pattern argument
  names.

* [#9316](https://github.com/leanprover/lean4/pull/9316) adds clickable code-action hints to the "invalid case name"
  error message.

* [#9317](https://github.com/leanprover/lean4/pull/9317) adds to the "fields missing" error message for structure
  instance notation a code-action hint that inserts all missing fields.

* [#9324](https://github.com/leanprover/lean4/pull/9324) improves the functions for checking whether two terms are
  disequal in `grind`

* [#9325](https://github.com/leanprover/lean4/pull/9325) optimizes the Boolean disequality propagator used in `grind`.

* [#9326](https://github.com/leanprover/lean4/pull/9326) optimizes `propagateEqUp` used in `grind`.

* [#9340](https://github.com/leanprover/lean4/pull/9340) modifies the encoding from `Nat` to `Int` used in `grind
  cutsat`. It is simpler, more extensible, and similar to the generic
  `ToInt`. After update stage0, we will be able to delete the leftovers.

* [#9351](https://github.com/leanprover/lean4/pull/9351) optimizes the `grind` preprocessing steps by skipping steps when
  the term is already present in the hash-consing table.

* [#9358](https://github.com/leanprover/lean4/pull/9358) adds support for generating lattice-theoretic (co)induction
  proof principles for predicates defined via `mutual` blocks using
  `inductive_fixpoint`/`coinductive_fixpoint` constructs.

* [#9367](https://github.com/leanprover/lean4/pull/9367) implements a minor optimization to the `grind` preprocessor.

* [#9369](https://github.com/leanprover/lean4/pull/9369) optimizes the `grind` preprocessor by skipping unnecessary steps
  when possible.

* [#9371](https://github.com/leanprover/lean4/pull/9371) fixes an issue that caused some `deriving` handlers to fail when
  the name of the type being declared matched that of a declaration in an
  open namespace.

* [#9372](https://github.com/leanprover/lean4/pull/9372) fixes a performance issue that occurs when generating equation
  lemmas for functions that use match-expressions containing several
  literals. This issue was exposed by #9322 and arises from a combination
  of factors:

  1. Literal values are compiled into a chain of dependent if-then-else
  expressions.
  2. Dependent if-then-else expressions are significantly more expensive
  to simplify than regular ones.
  3. The `split` tactic selects a target, splits it, and then invokes
  `simp` on the resulting subgoals. Moreover, `simp` traverses the entire
  goal bottom-up and does not stop after reaching the target.

* [#9385](https://github.com/leanprover/lean4/pull/9385) replaces the `isDefEq` test in the `simpEq` simproc used in
  `grind`. It is too expensive.

* [#9386](https://github.com/leanprover/lean4/pull/9386) improves a confusing error message that occurred when attempting
  to project from a zero-field structure.

* [#9387](https://github.com/leanprover/lean4/pull/9387) adds a hint to the "invalid projection" message suggesting the
  correct nested projection for expressions of the form `t.n` where `t` is
  a tuple and `n > 2`.

* [#9395](https://github.com/leanprover/lean4/pull/9395) fixes a bug at `mkCongrSimpCore?`. It fixes the issue reported
  by @joehendrix at #9388.
  The fix is just commit: afc4ba617fe2ca5828e0e252558d893d7791d56b. The
  rest of the PR is just cleaning up the file.

* [#9398](https://github.com/leanprover/lean4/pull/9398) avoids the expensive `inferType` call in `simpArith`. It also
  cleans up some of the code and removes anti-patterns.

* [#9408](https://github.com/leanprover/lean4/pull/9408) implements a simple optimization: dependent implications are no
  longer treated as E-matching theorems in `grind`. In
  `grind_bitvec2.lean`, this change saves around 3 seconds, as many
  dependent implications are generated. Example:
  ```lean
   ∀ (h : i + 1 ≤ w), x.abs.getLsbD i = x.abs[i]
   ```

* [#9414](https://github.com/leanprover/lean4/pull/9414) increases the number of cases where `isArrowProposition` returns
  a result other than `.undef`. This function is used to implement the
  `isProof` predicate, which is invoked on every subterm visited by
  `simp`.

* [#9421](https://github.com/leanprover/lean4/pull/9421) fixes a bug that caused error explanations to "steal" the
  Infoview's container in the Lean web editor.

* [#9423](https://github.com/leanprover/lean4/pull/9423) updates the formatting of, and adds explanations for, "unknown
  identifier" errors as well as "failed to infer type" errors for binders
  and definitions.

* [#9424](https://github.com/leanprover/lean4/pull/9424) improves the error messages produced by the `split` tactic,
  including suggesting syntax fixes and related tactics with which it
  might be confused.

* [#9443](https://github.com/leanprover/lean4/pull/9443) makes cdot function expansion take hygiene information into
  account, fixing "parenthesis capturing" errors that can make erroneous
  cdots trigger cdot expansion in conjunction with macros. For example,
  given
  ```lean
  macro "baz% " t:term : term => `(1 + ($t))
  ```
  it used to be that `baz% ·` would expand to `1 + fun x => x`, but now
  the parentheses in `($t)` do not capture the cdot. We also fix an
  oversight where cdot function expansion ignored the fact that type
  ascriptions and tuples were supposed to delimit expansion, and also now
  the quotation prechecker ignores the identifier in `hygieneInfo`. (#9491
  added the hygiene information to the parenthesis and cdot syntaxes.)

* [#9447](https://github.com/leanprover/lean4/pull/9447) ensures that `mvcgen` not only tries to close stateful subgoals
  by assumption, but also pure Lean goals.

* [#9448](https://github.com/leanprover/lean4/pull/9448) addresses the lean crash (stack overflow) with nested induction
  and the generation of the `SizeOf` spec lemmas, reported at #9018.

* [#9451](https://github.com/leanprover/lean4/pull/9451) adds support in the `mintro` tactic for introducing `let`/`have`
  binders in stateful targets, akin to `intro`. This is useful when
  specifications introduce such let bindings.

* [#9454](https://github.com/leanprover/lean4/pull/9454) introduces tactic `mleave` that leaves the `SPred` proof mode by
  eta expanding through its abstractions and applying some mild
  simplifications. This is useful to apply automation such as `grind`
  afterwards.

* [#9464](https://github.com/leanprover/lean4/pull/9464) makes `PProdN.reduceProjs` also look for projection functions.
  Previously, all redexes were created by the functions in `PProdN`, which
  used primitive projections. But with `mkAdmProj` the projection
  functions creep in via the types of the `admissible_pprod_fst` theorem.
  So let's just reduce both of them.

* [#9472](https://github.com/leanprover/lean4/pull/9472) fixes another issue at the `congr_simp` theorems that was
  affecting Mathlib. Many thanks to Johan Commelin for creating the mwe.

* [#9476](https://github.com/leanprover/lean4/pull/9476) fixes the bridge between `Nat` and `Int` in `grind cutsat`.

* [#9479](https://github.com/leanprover/lean4/pull/9479) improves the `evalInt?` function, which is used to evaluate
  configuration parameters from the `ToInt` type class. also adds
  a new `evalNat?` function for handling the `IsCharP` type class, and
  introduces a configuration option:
  ```
  研磨（exp := <num>）
  ```
  This option controls the maximum exponent size considered during
  expression evaluation. Previously, `evalInt?` used `whnf`, which could
  run out of stack space when reducing terms such as `2^1024`.

* [#9480](https://github.com/leanprover/lean4/pull/9480) adds a feature where `structure` constructors can override the
  inferred binder kinds of the type's parameters. In the following, the
  `(p)` binder on `toLp` causes `p` to be an explicit parameter to
  `WithLp.toLp`:
  ```lean
  structure WithLp (p : Nat) (V : Type) where toLp (p) ::
    脂压：V
  ```
  This reflects the syntax of the feature added in #7742 for overriding
  binder kinds of structure projections. Similarly, only those parameters
  in the header of the `structure` may be updated; it is an error to try
  to update binder kinds of parameters included via `variable`.

* [#9481](https://github.com/leanprover/lean4/pull/9481) fixes a kernel type mismatch that occurs when using `grind` on
  goals containing non-standard `OfNat.ofNat` terms. For example, in issue
  #9477, the `0` in the theorem `range_lower` has the form:
  ```lean
  （@OfNat.ofNat
    (Std.PRange.Bound (Std.PRange.RangeShape.lower (Std.PRange.RangeShape.mk Std.PRange.BoundShape.close Std.PRange.BoundShape.open)) Nat)
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```
  instead of the more standard form:
  ```lean
  （@OfNat.ofNat
    纳特
    (nat_lit 0)
    (instOfNatNat (nat_lit 0)))
  ```

* [#9487](https://github.com/leanprover/lean4/pull/9487) fixes an incorrect proof term constructed by `grind linarith`,
  as reported in #9485.

* [#9491](https://github.com/leanprover/lean4/pull/9491) adds hygiene info to paren/tuple/typeAscription syntaxes, which
  will be used to implement hygienic cdot function expansion in #9443.

* [#9496](https://github.com/leanprover/lean4/pull/9496) improves the error messages produced by the `set_option`
  command.

* [#9500](https://github.com/leanprover/lean4/pull/9500) adds a `HPow \a Int \a` field to `Lean.Grind.Field`, and
  sufficient axioms to connect it to the operations, so that in future we
  can reason about exponents in `grind`. To avoid collisions, we also move
  the `HPow \a Nat \a` field in `Semiring` from the extends clause to a
  field. Finally, we add some failing tests about normalizing exponents.

* [#9505](https://github.com/leanprover/lean4/pull/9505) removes vestigial syntax definitions in
  `Lean.Elab.Tactic.Do.VCGen` that when imported undefine the `mvcgen`
  tactic. Now it should be possible to import Mathlib and still use
  `mvcgen`.

* [#9506](https://github.com/leanprover/lean4/pull/9506) adds a few missing simp lemmas to `mleave`.

* [#9507](https://github.com/leanprover/lean4/pull/9507) makes `mvcgen` `mintro` let/have bindings.

* [#9509](https://github.com/leanprover/lean4/pull/9509) surfaces kernel diagnostics even in `example`.

* [#9512](https://github.com/leanprover/lean4/pull/9512) makes `mframe`, `mspec` and `mvcgen` respect hygiene.
  Inaccessible stateful hypotheses can now be named with a new tactic
  `mrename_i` that works analogously to `rename_i`.

* [#9516](https://github.com/leanprover/lean4/pull/9516) ensures that private declarations made inaccessible by the
  module system are noted in the relevant error messages

* [#9518](https://github.com/leanprover/lean4/pull/9518) ensures previous "is marked as private" messages are still
  triggered under the module system

* [#9520](https://github.com/leanprover/lean4/pull/9520) corrects the changes to `Lean.Grind.Field` made in #9500.

* [#9522](https://github.com/leanprover/lean4/pull/9522) uses `withAbstractAtoms` to prevent the kernel from accidentally
  reducing the atoms in the arith normlizer while typechecking. This PR
  also sets `implicitDefEqProofs := false` in the `grind` normalizer

* [#9532](https://github.com/leanprover/lean4/pull/9532) generalizes `Process.output` and `Process.run` with an optional
  `String` argument that can be piped to `stdin`.

* [#9551](https://github.com/leanprover/lean4/pull/9551) fixes the error position for the "dependent elimination failed"
  error for the `cases` tactic.

* [#9553](https://github.com/leanprover/lean4/pull/9553) fixes a bug introduced in #7830 where if the cursor is at the
  indicated position
  ```lean
  example (as bs : List Nat) : (as.append bs).length = as.length + bs.length := by
    归纳法与
    | nil => -- 光标
    |缺点 b bs ih =>
  ```
  then the Infoview would show "no goals" rather than the `nil` goal. The
  PR also fixes a separate bug where placing the cursor on the next line
  after the `induction`/`cases` tactics like in
  ```lean
    归纳法与
    |无 => 抱歉
    |缺点 b bs ih => 抱歉
    I -- < 光标
  ```
  would report the original goal in the goal list. Furthermore, there are
  numerous improvements to error recovery (including `allGoals`-type logic
  for pre-tactics) and the visible tactic states when there are errors.
  Adds `Tactic.throwOrLogErrorAt`/`Tactic.throwOrLogError` for throwing or
  logging errors depending on the recovery state.

* [#9571](https://github.com/leanprover/lean4/pull/9571) restores the feature where in `induction`/`cases` for `Nat`, the
  `zero` and `succ` labels are hoverable. This was added in #1660, but
  broken in #3629 and #3655 when custom eliminators were added. In
  general, if a custom eliminator `T.elim` for an inductive type `T` has
  an alternative `foo`, and `T.foo` is a constant, then the `foo` label
  will have `T.foo` hover information.

* [#9574](https://github.com/leanprover/lean4/pull/9574) adds the option `abstractProof` to control whether `grind`
  automatically creates an auxiliary theorem for the generated proof or
  not.

* [#9575](https://github.com/leanprover/lean4/pull/9575) optimizes the proof terms generated by `grind ring`. For
  example, before this PR, the kernel took 2.22 seconds (on a M4 Max) to
  type-check the proof in the benchmark `grind_ring_5.lean`; it now takes
  only 0.63 seconds.

* [#9578](https://github.com/leanprover/lean4/pull/9578) fixes an issue in `grind`'s disequality proof construction. The
  issue occurs when an equality is merged with the `False` equivalence
  class, but it is not the root of its congruence class, and its
  congruence root has not yet been merged into the `False` equivalence
  class yet.

* [#9579](https://github.com/leanprover/lean4/pull/9579) ensures `ite` and `dite` are to selected as E-matching patterns.
  They are bad patterns because the then/else branches are only
  internalized after `grind` decided whether the condition is
  `True`/`False`.

* [#9592](https://github.com/leanprover/lean4/pull/9592) updates the styling and wording of error messages produced in
  inductive type declarations and anonymous constructor notation,
  including hints for inferable constructor visibility updates.

* [#9595](https://github.com/leanprover/lean4/pull/9595) improves the error message displayed when writing an invalid
  projection on a free variable of function type.

* [#9606](https://github.com/leanprover/lean4/pull/9606) adds notes to the deprecation warning when the replacement
  constant has a different type, visibility, and/or namespace.

* [#9625](https://github.com/leanprover/lean4/pull/9625) improves trace messages around wf_preprocess.

* [#9628](https://github.com/leanprover/lean4/pull/9628) introduces a `mutual_induct` variant of the generated
  (co)induction proof principle for mutually defined (co)inductive
  predicates. Unlike the standard (co)induction principle (which projects
  conclusions separately for each predicate), `mutual_induct` produces a
  conjunction of all conclusions.

* [#9633](https://github.com/leanprover/lean4/pull/9633) updates various error messages produced by or associated with
  built-in tactics and adapts their formatting to current conventions.

* [#9634](https://github.com/leanprover/lean4/pull/9634) modifies dot identifier notation so that `(.a : T)` resolves
  `T.a` with respect to the root namespace, like for generalized field
  notation. This lets the notation refer to private names, follow aliases,
  and also use open namespaces. The LSP completions are improved to follow
  how dot ident notation is resolved, but it doesn't yet take into account
  aliases or open namespaces.

* [#9637](https://github.com/leanprover/lean4/pull/9637) improves the readability of the "maximum universe level offset
  exceeded" error message.

* [#9646](https://github.com/leanprover/lean4/pull/9646) uses a more simple approach to proving the unfolding theorem for
  a function defined by well-founded recursion. Instead of looping a bunch
  of tactics, it uses simp in single-pass mode to (try to) exactly undo
  the changes done in `WF.Fix`, using a dedicated theorem that pushes the
  extra argument in for each matcher (or `casesOn`).

* [#9649](https://github.com/leanprover/lean4/pull/9649) fixes an issue where a macro unfolding to multiple commands
  would not be accepted inside `mutual`

* [#9653](https://github.com/leanprover/lean4/pull/9653) adds error explanations for two common errors caused by large
  elimination from `Prop`. To support this functionality, "nested" named
  errors thrown by sub-tactics are now able to display their error code
  and explanation.

* [#9666](https://github.com/leanprover/lean4/pull/9666) addresses an outstanding feature in the module system to
  automatically mark `let rec` and `where` helper declarations as private
  unless they are defined in a public context such as under `@[expose]`.

* [#9670](https://github.com/leanprover/lean4/pull/9670) add constructors `.intCast k` and `.natCast k` to
  `CommRing.Expr`. We need them because terms such as `Nat.cast (R := α)
  1` and `(1 : α)` are not definitionally equal. This is pervaise in
  Mathlib for the numerals `0` and `1`.

* [#9671](https://github.com/leanprover/lean4/pull/9671) fixes support for `SMul.smul` in `grind ring`. `SMul.smul`
  applications are now normalized. Example:
  ```lean
  example (x : BitVec 2) : x - 2 • x + x = 0 := by
    磨
  ```

* [#9675](https://github.com/leanprover/lean4/pull/9675) adds support for `Fin.val` in `grind cutsat`. Examples:
  ```lean
  example (a b : Fin 2) (n : Nat) : n = 1 → ↑(a + b) ≠ n → a ≠ 0 → b = 0 → False := by
    磨

* [#9676](https://github.com/leanprover/lean4/pull/9676) 为非标准算术实例添加标准化器。类型
  `Nat` 和 `Int` 在 `grind` 中有内置支持，它使用
  这些类型的标准实例，并假设它们是正在使用的实例。
  然而，用户可以定义自己的替代实例
  定义上等于标准的。标准化这样的
  使用 simprocs 的实例。这种情况实际上发生在Mathlib中。
  示例：

  ```lean
  class Distrib (R : Type _) extends Mul R where

* [#9679](https://github.com/leanprover/lean4/pull/9679) produces a warning for redundant `grind` arguments.

* [#9682](https://github.com/leanprover/lean4/pull/9682) fixes a regression introduced by an optimization in the
  `unfoldReducible` step used by the `grind` normalizer. It also ensures
  that projection functions are not reduced, as they are folded in a later
  step.

* [#9686](https://github.com/leanprover/lean4/pull/9686) applies `clear` to implementation detail local declarations
  during the `grind` preprocessing steps.

* [#9699](https://github.com/leanprover/lean4/pull/9699) adds propagation rules for functions that take singleton types.
  This feature is useful for discharging verification conditions produced
  by `mvcgen`. For example:

  ```lean
  example (h : (fun (_ : Unit) => x + 1) = (fun _ => 1 + y)) : x = y := by
    磨
  ```

* [#9700](https://github.com/leanprover/lean4/pull/9700) fixes assertion violations when `checkInvariants` is enabled in
  `grind`

* [#9701](https://github.com/leanprover/lean4/pull/9701) switches to a non-verloading local `Std.Do.Triple` notation in
  SpecLemmas.lean to work around a stage2 build failure.

* [#9702](https://github.com/leanprover/lean4/pull/9702) fixes an issue in the `match` elaborator where pattern variables
  like `__x` would not have the kind `implDetail` in the local context.
  Now `kindOfBinderName` is `LocalDeclKind.ofBinderName`.

* [#9704](https://github.com/leanprover/lean4/pull/9704) optimizes the proof terms produced by `grind cutsat`. Additional
  performance improvements will be merged later.

* [#9706](https://github.com/leanprover/lean4/pull/9706) combines `Poly.combine_k` and `Poly.mul_k` steps used in the
  `grind cutsat` proof terms.

* [#9710](https://github.com/leanprover/lean4/pull/9710) improves some of the proof terms produced by `grind ring` and
  `grind cutsat`.

* [#9714](https://github.com/leanprover/lean4/pull/9714) adds a version of `CommRing.Expr.toPoly` optimized for kernel
  reduction. We use this function not only to implement `grind ring`, but
  also to interface the ring module with `grind cutsat`.

* [#9716](https://github.com/leanprover/lean4/pull/9716) moves the validation of cross-package `import all` to Lake and
  the syntax validation of import keywords (`public`, `meta`, and `all`)
  to the two import parsers.

* [#9728](https://github.com/leanprover/lean4/pull/9728) fixes #9724

* [#9735](https://github.com/leanprover/lean4/pull/9735) extends the propagation rule implemented in #9699 to constant
  functions.

* [#9736](https://github.com/leanprover/lean4/pull/9736) implements the option `mvcgen +jp` to employ a slightly lossy VC
  encoding for join points that prevents exponential VC blowup incurred by
  naïve splitting on control flow.

* [#9754](https://github.com/leanprover/lean4/pull/9754) makes `mleave` apply `at *` and improves its simp set in order to
  discharge some more trivialities (#9581).

* [#9755](https://github.com/leanprover/lean4/pull/9755) implements a `mrevert ∀n` tactic that "eta-reduces" the stateful
  goal and is adjoint to `mintro ∀x1 ... ∀xn`.

* [#9767](https://github.com/leanprover/lean4/pull/9767) fixes equality congruence proof terms constructed by `grind`.

* [#9772](https://github.com/leanprover/lean4/pull/9772) fixes a bug in the projection over constructor propagator used
  in `grind`. It may construct type-incorrect terms when an equivalence
  class contains heterogeneous equalities.

* [#9776](https://github.com/leanprover/lean4/pull/9776) combines the simplification and unfold-reducible-constants steps
  in `grind` to ensure that no potential normalization steps are missed.

* [#9780](https://github.com/leanprover/lean4/pull/9780) extends the test suite for `grind` working category theory, to
  help debug outstanding problems in Mathlib.

* [#9781](https://github.com/leanprover/lean4/pull/9781) ensures that `mvcgen` is hygienic. The goals it generates should
  now introduce all locals inaccessibly.

* [#9785](https://github.com/leanprover/lean4/pull/9785) splits out an implementation detail of
  MVarId.getMVarDependencies into a top-level function. Aesop was relying
  on the function defined in the where clause, which is no longer possible
  after #9759.

* [#9798](https://github.com/leanprover/lean4/pull/9798) introduces `Lean.realizeValue`, a new metaprogramming API for
  parallelism-aware caching of `MetaM` computations

* [#9800](https://github.com/leanprover/lean4/pull/9800) improves the delta deriving handler, giving it the ability to
  process definitions with binders, as well as the ability to recursively
  unfold definitions. Furthermore, delta deriving now tries all explicit
  non-out-param arguments to a class, and it can handle "mixin" instance
  arguments. The `deriving` syntax has been changed to accept general
  terms, which makes it possible to derive specific instances with for
  example `deriving OfNat _ 1` or `deriving Module R`. The class is
  allowed to be a pi type, to add additional hypotheses; here is a Mathlib
  example:
  ```lean
  def Sym (α : Type*) (n : ℕ) :=
    { s : Multiset α // Multiset.card s = n }
  推导 [DecidableEq α] → DecidableEq _
  ```
  This underscore stands for where `Sym α n` may be inserted, which is
  necessary when `→` is used. The `deriving instance` command can refer to
  scoped variables when delta deriving as well. Breaking change: the
  derived instance's name uses the `instance` command's name generator,
  and the new instance is added to the current namespace.

* [#9804](https://github.com/leanprover/lean4/pull/9804) allows trailing comma in the argument list of `simp?`, `dsimp?`,
  `simpa`, etc... Previously, it was only allowed in the non `?` variants
  of `simp`, `dsimp`, `simp_all`.

* [#9807](https://github.com/leanprover/lean4/pull/9807) adds `Std.List.Zipper.pref` to the simp set of `mleave`.

* [#9809](https://github.com/leanprover/lean4/pull/9809) adds a script for analyzing `grind` E-matching annotations. The
  script is useful for detecting matching loops. We plan to add
  user-facing commands for running the script in the future.

* [#9813](https://github.com/leanprover/lean4/pull/9813) fixes an unexpected bound variable panic in `unfoldReducible`
  used in `grind`.

* [#9814](https://github.com/leanprover/lean4/pull/9814) skips the `normalizeLevels` preprocessing step in `grind` when
  it is not needed.

* [#9818](https://github.com/leanprover/lean4/pull/9818) fixes a bug where the `DecidableEq` deriving handler did not
  take universe levels into account for enumerations (inductive types
  whose constructors all have no fields). Closes #9541.

* [#9819](https://github.com/leanprover/lean4/pull/9819) makes the `unsafe t` term create an auxiliary opaque
  declaration, rather than an auxiliary definition with opaque
  reducibility hints.

* [#9831](https://github.com/leanprover/lean4/pull/9831) adds a delaborator for `Std.Range` notation.

* [#9832](https://github.com/leanprover/lean4/pull/9832) adds simp lemmas `SPred.entails_<n>` to replace
  `SPred.entails_cons` which was dysfunctional as a simp lemma due to
  #8074.

* [#9833](https://github.com/leanprover/lean4/pull/9833) works around a DefEq bug in `mspec` involving delayed
  assignments.

* [#9834](https://github.com/leanprover/lean4/pull/9834) fixes a bug in `mvcgen` triggered by excess state arguments to
  the `wp` application, a situation which arises when working with
  `StateT` primitives.

* [#9841](https://github.com/leanprover/lean4/pull/9841) migrates the ⌜p⌝ notation for embedding pure `p : Prop` into
  `SPred σs` to expand into a simple, first-order expression `SPred.pure p`
  that can be supported by E-matching in `grind`.

* [#9843](https://github.com/leanprover/lean4/pull/9843) makes `mvcgen` produce deterministic case labels for the
  generated VCs. Invariants will be named `inv<n>` and every other VC will
  be named `vc<n>.*`, where the `*` part serves as a loose indication of
  provenance.

* [#9852](https://github.com/leanprover/lean4/pull/9852) removes the `inShareCommon` quick filter used in `grind`
  preprocessing steps. `shareCommon` is no longer used only for fully
  preprocessed terms.

* [#9853](https://github.com/leanprover/lean4/pull/9853) adds `Nat` and `Int` numeral normalizers in `grind`.

* [#9857](https://github.com/leanprover/lean4/pull/9857) ensures `grind` can E-match patterns containing universe
  polymorphic ground sub-patterns. For example, given
  ```
  set_option pp.universes true in
  attribute [grind?] Id.run_pure
  ```
  the pattern
  ```
  Id.run_pure.{u_1}：[@Id.run.{u_1} #1 (@pure.{u_1, u_1} `[Id.{u_1}] `[Applicative.toPure.{u_1, u_1}] _ #0)]
  ```
  contains two nested universe polymorphic ground patterns
  - `Id.{u_1}`
  - `Applicative.toPure.{u_1, u_1}`

* [#9860](https://github.com/leanprover/lean4/pull/9860) fixes E-matching theorem activation in `grind`.

* [#9865](https://github.com/leanprover/lean4/pull/9865) adds improved support for proof-by-reflection to the kernel type
  checker. It addresses the performance issue exposed by #9854. With this
  PR, whenever the kernel type-checks an argument of the form `eagerReduce
  _`, it enters "eager-reduction" mode. In this mode, the kernel is more
  eager to reduce terms. The new `eagerReduce _` hint is often used to
  wrap `Eq.refl true`. The new hint should not negatively impact any
  existing Lean package.

* [#9867](https://github.com/leanprover/lean4/pull/9867) fixes a nondeterministic behavior in `grind ring`.

* [#9880](https://github.com/leanprover/lean4/pull/9880) ensures a local forall is activated at most once per pattern in
  `grind`.

* [#9883](https://github.com/leanprover/lean4/pull/9883) refines the warning message for redundant `grind` arguments. It
  is not based on the actual inferred pattern instead provided kind.

* [#9885](https://github.com/leanprover/lean4/pull/9885) is initially motivated by noticing `Lean.Grind.Preorder.toLE`
  appearing in long Mathlib type class searches; this change will prevent
  these searches. These changes are also helpful preparation for
  potentially dropping the custom `Lean.Grind.*` type classes, and unifying
  with the new type classes introduced in #9729.
````

````markdown
## Library
%%%
tag := "zh-releases-v4-23-0-h004"
%%%

* [#7450](https://github.com/leanprover/lean4/pull/7450) implements `Nat.dfold`, a dependent analogue of `Nat.fold`.

* [#9096](https://github.com/leanprover/lean4/pull/9096) removes some unnecessary `Decidable*` instance arguments by
  using lemmas in the `Classical` namespace instead of the `Decidable`
  namespace.

* [#9121](https://github.com/leanprover/lean4/pull/9121) allows `grind` to case on the universe variants of `Prod`.

* [#9129](https://github.com/leanprover/lean4/pull/9129) fixes simp lemmas about boolean equalities to say `(!x) = y`
  instead of `(!decide (x = y)) = true`

* [#9135](https://github.com/leanprover/lean4/pull/9135) allows the result type of `forIn`, `foldM` and `fold` on pure
  iterators (`Iter`) to be in a different universe than the iterators.

* [#9142](https://github.com/leanprover/lean4/pull/9142) changes `Fin.reverseInduction` from using well-founded recursion
  to using `let rec`, which makes it have better definitional equality.
  Co-authored by @digama0. See the test below:

  ```lean
  namespace Fin

* [#9145](https://github.com/leanprover/lean4/pull/9145) 修复了两个拼写错误。

* [#9176](https://github.com/leanprover/lean4/pull/9176) 使 `mvcgen` 拆分 if，而不是应用规范。
  这样做修复了 Rish 报告的错误。

* [#9194](https://github.com/leanprover/lean4/pull/9194) 使 `Std.Do` 的逻辑和策略宇宙多态，在
  由于转换而产生的一些定义属性的成本
  基本外壳 `SPred []` 中的 `Prop` 至 `ULift Prop`。

* [#9249](https://github.com/leanprover/lean4/pull/9249) 将定理 `BitVec.clzAuxRec_eq_clzAuxRec_of_getLsbD_false` 添加为
  比 `BitVec.clzAuxRec_eq_clzAuxRec_of_le` 更一般的声明，
  在 Bitblaster 中也替换了后者。

* [#9260](https://github.com/leanprover/lean4/pull/9260) 删除了 Lean 本身中 `Lean.RBMap` 的使用。

* [#9263](https://github.com/leanprover/lean4/pull/9263) 修复 `toISO8601String` 以生成符合以下条件的字符串
  ISO 8601 格式规范。之前的实现将
  分钟和秒片段带有 `.` 而不是 `:` 并包含在内
  时区偏移量，没有用 分隔的小时和分钟片段
  `:`。

* [#9285](https://github.com/leanprover/lean4/pull/9285) 删除了 `BEq α` 的不必要要求
  `Array.any_push`、`Array.any_push'`、`Array.all_push`、`Array.all_push'`
  以及 `Vector.any_push` 和 `Vector.all_push`。

* [#9301](https://github.com/leanprover/lean4/pull/9301) 在 `Zipper` 相关的内容上添加 `simp` 和 `grind` 注释
  改进有关 `Std.Do` 不变量推理的定理。

* [#9391](https://github.com/leanprover/lean4/pull/9391) 替换简化引理 `Nat.zero_mod` 的证明
  与
  `rfl`，因为根据设计，它是 定义等价。这解决了一个
  问题
  引理在“dsimp”中时无法被简化器使用
  模式。

* [#9441](https://github.com/leanprover/lean4/pull/9441) 修复了 `String.prev` 的行为，调整运行时
  与参考实现的实现。特别是，
  以下陈述现在成立：
  - `(s.prev p).byteIdx` 至少为 `p.byteIdx - 4` 且至多
  `p.byteIdx - 1`
  - `s.prev 0 = 0`
  - `s.prev` 单调

* [#9449](https://github.com/leanprover/lean4/pull/9449) 修复 `String.next` 在标量边界上的行为 (`2 ^
  63 - 1`（在 64 位平台上）。

* [#9451](https://github.com/leanprover/lean4/pull/9451) 在 `mintro`策略中添加了支持，以引入 `let`/`have`
  有状态目标中的绑定器，类似于 `intro`。这在以下情况下很有用：
  规范引入了这样的 let 绑定。

* [#9454](https://github.com/leanprover/lean4/pull/9454) 引入了策略`mleave`，它离开了 `SPred` 证明模式
  eta 通过其抽象进行扩展并应用一些温和的
  简化。这对于应用自动化（例如 `grind`）很有用
  之后。

* [#9504](https://github.com/leanprover/lean4/pull/9504) 添加了更多 `*.by_wp`“充分性定理”，允许
  使用 `Std.Do` 证明 `ReaderM` 和 `ExceptM` 中程序的事实
  框架。

* [#9528](https://github.com/leanprover/lean4/pull/9528) 添加 `List.zipWithM` 和 `Array.zipWithM`。

* [#9529](https://github.com/leanprover/lean4/pull/9529) 从电池向上游传输 `NameSet` 的一些帮助程序实例。

* [#9538](https://github.com/leanprover/lean4/pull/9538) 添加了两个与 `Iter.toArray` 相关的引理。

* [#9577](https://github.com/leanprover/lean4/pull/9577) 添加有关 `UIntX.toBitVec`、`UIntX.ofBitVec` 和 `^` 的引理。

* [#9586](https://github.com/leanprover/lean4/pull/9586) 在 `Vector α n` 上添加分量代数运算，并且
  相关实例。

* [#9594](https://github.com/leanprover/lean4/pull/9594) 优化 `Lean.Name.toString`，给出 10% 的指令
  好处。

* [#9609](https://github.com/leanprover/lean4/pull/9609) 将 `@[grind =]` 添加到 `Prod.lex_def`。请注意，`omega` 有
  对 `Prod.Lex` 进行特殊处理，这对于 `grind` 的 cutsat 是必需的
  模块实现奇偶校验。

* [#9616](https://github.com/leanprover/lean4/pull/9616) 引入检查以确保 IO 函数产生
  当输入包含 NUL 字节时出错（而不是忽略所有内容
  在第一个 NUL 字节之后）。

* [#9620](https://github.com/leanprover/lean4/pull/9620) 添加单独的方向
  `List.pairwise_iff_forall_sublist` 为命名引理。

* [#9621](https://github.com/leanprover/lean4/pull/9621) 将 `Xor` 重命名为 `XorOp`，以匹配 `AndOp` 等。

* [#9622](https://github.com/leanprover/lean4/pull/9622) 添加了有关 `List.sum` 的缺失引理和研磨注释。

* [#9701](https://github.com/leanprover/lean4/pull/9701) 切换到非重载本地 `Std.Do.Triple` 表示法
  SpecLemmas.lean 解决 stage2 构建失败的问题。

* [#9721](https://github.com/leanprover/lean4/pull/9721) 使用 `int_toBitVec` 标记更多 `SInt` 和 `UInt` 引理，因此
  `bv_decide`
  可以处理它们之间的强制转换和否定。

* [#9729](https://github.com/leanprover/lean4/pull/9729) 引入了一种赋予类型顺序的规范方法
  结构。基本操作（`LE`、`LT`、`Min`、`Max` 以及稍后的
  PR `BEq`、`Ord`，...）和任何更高级别的属性（预购、
  然后将其与 `LE` 相关联，如下所示：
  必要的。 PR 为许多核心类型提供 `IsLinearOrder` 实例
  并更新了一些引理的签名。

* [#9732](https://github.com/leanprover/lean4/pull/9732) 使用 Lean 而不是 C++ 重新实现 `IO.waitAny`。这是为了
  减小尺寸并
  `task_manager` 的复杂性，以便于将来的重构。

* [#9736](https://github.com/leanprover/lean4/pull/9736) 实现选项 `mvcgen +jp` 以采用稍微有损的 VC
  连接点编码可防止指数 VC 爆炸
  控制流上的天真分裂。

* [#9739](https://github.com/leanprover/lean4/pull/9739) 从 `lexOrd` 中删除 `instance` 属性
  意外应用于`Std.Classes.Ord.Basic`。

* [#9757](https://github.com/leanprover/lean4/pull/9757) 为关键 `Std.Do.SPred` 引理添加 `grind` 注释。

* [#9782](https://github.com/leanprover/lean4/pull/9782) 更正 `StdGen` 的 `Inhabited` 实例，以使用有效的
  伪随机数生成器的初始状态。此前，
  `default` 生成器具有 `Prod.snd (stdNext 默认值) = 的属性
  default`，所以它只会产生常量序列。

* [#9787](https://github.com/leanprover/lean4/pull/9787) 添加一个简单引理 `PostCond.const_apply`。

* [#9792](https://github.com/leanprover/lean4/pull/9792) 将 `@[expose]` 添加到两个具有 `where` 子句的定义中
  电池证明有关定理。

* [#9799](https://github.com/leanprover/lean4/pull/9799) 修复了 #9410 问题。

* [#9805](https://github.com/leanprover/lean4/pull/9805) 改进了 API 的不变量和后置条件等
  对现有预发布版 API 进行了一些重大更改
  `Std.Do`。它还添加了 Markus Himmel 的 `pairsSumToZero` 示例作为
  测试用例。

* [#9832](https://github.com/leanprover/lean4/pull/9832) 添加简单引理 `SPred.entails_<n>` 来替换
  `SPred.entails_cons` 作为一个简单引理功能失调，因为
  第8074章

* [#9841](https://github.com/leanprover/lean4/pull/9841) 将用于嵌入纯 `p : Prop` 的 ⌜p⌝ 表示法迁移到
  `SPred σs` 扩展为简单的一阶表达式 `SPred.pure p`
  `grind` 中的电子匹配可以支持该功能。

* [#9848](https://github.com/leanprover/lean4/pull/9848) 在 `Std.PRange` 处添加 `forIn` 和 `forIn'` 的 `@[spec]` 引理。

* [#9850](https://github.com/leanprover/lean4/pull/9850) 添加 `Std.PRange` 表示法的精化器。

## 编译器
%%%
tag := "zh-releases-v4-23-0-h005"
%%%

* [#8691](https://github.com/leanprover/lean4/pull/8691) 确保使用编译时恢复状态
  新的编译器失败。这对于不可计算的情况尤其重要
  sections where the compiler might generate half-compiled functions which
  然后在编译其他函数时可能会被错误地使用。

* [#9134](https://github.com/leanprover/lean4/pull/9134) 更改 ToIR 以调用 `lowerEnumToScalarType?`
  `ConstructorVal.induct` 而不是构造函数本身的名称。
  这是新编译器中一些代码重构的疏忽
  在着陆之前。它不应该影响编译代码的运行时（由于
  额外的标记/取消标记由 LLVM 优化），但它确实使
  IR对于口译员来说效率稍高一些。

* [#9144](https://github.com/leanprover/lean4/pull/9144) 添加了对将更多归纳性表示为枚举的支持，
  总结为向那些未能成为枚举的人提供支持
  因为参数或不相关的字段。虽然这很高兴，
  它实际上是由未来期望的正确性所驱动
  优化。现有的类型表示是不健全的，如果我们
  实现 `object`/`tobject` 值之间的区分保证
  对象指针和那些也可能是标记标量的对象。在
  特别是，像此 PR 测试中添加的类型将具有所有
  他们的构造函数通过标记值进行编码，但在自然条件下
  现有类型表示规则的扩展
  考虑 `object` 而不是 `tobject`。

* [#9154](https://github.com/leanprover/lean4/pull/9154) 收紧了围绕闭包应用的 IR 类型规则。
  当重新阅读一些代码时，我意识到`mkPartialApp`中的代码
  有一个明显的拼写错误 — `.object` 和 `type` 应该交换。然而，它
  没关系，因为后来的 IR 通过消除了这里的不匹配。它
  预先严格并要求应用更有意义
  闭包始终返回 `.object`。

* [#9159](https://github.com/leanprover/lean4/pull/9159) 在基础阶段强制执行 _override 实现的非内联
  LCNF 编译。当前情况允许构造函数/案例
  不匹配暴露给简化器，这会触发断言
  失败。 Expr 没有更早出现的原因是 Expr 已经
  其计算字段 getter 的自定义 extern 实现。

* [#9177](https://github.com/leanprover/lean4/pull/9177) 使 `pullInstances` 传递避免拉动任何实例
  包含被删除命题的表达式，因为我们不正确
  表示擦除后保留的依赖关系。

* [#9198](https://github.com/leanprover/lean4/pull/9198) 更改编译器的专业化分析以考虑
  以仅改变其值的方式重新捆绑的高阶参数
  `Prop` 参数已修复。这意味着他们专门从事
  只是 `@[specialize]`，而不是编译器必须选择
  更积极的参数特定专业化。

* [#9207](https://github.com/leanprover/lean4/pull/9207) 使错误消息中的违规声明可点击
  当某些东西应该被标记为 `noncomputable` 时产生。

* [#9209](https://github.com/leanprover/lean4/pull/9209) 更改 `elimDeadBranches` 的 `getLiteral` 辅助函数
  使用构造函数正确处理归纳法。这个功能不是
  尽可能频繁地使用，这使得这个问题很少在外部出现
  有针对性的测试用例。

* [#9218](https://github.com/leanprover/lean4/pull/9218) 使 LCNF `elimDeadBranches` 传递句柄有点不安全 decls
  更仔细地。现在，不安全的 decl 的结果只会变成 ⊤ 如果
  递归调用产生价值流。

* [#9221](https://github.com/leanprover/lean4/pull/9221) 删除了错误假设 LCNF 局部变量的代码
  可以以类型出现。 `ElimDead.lean`还有其他评论
  断言这是不可能的，所以这一定是一个改变
  在新编译器开发的早期。

* [#9224](https://github.com/leanprover/lean4/pull/9224) 更改 `toMono` 传递以考虑应用程序的类型
  并删除与已删除参数对应的所有参数。这使得
  通过改变 a 的单声道类型进行相关性分析的轻量级形式
  声明。我希望将其与行为统一起来
  构造函数，但我尝试为构造函数提供相同的行为
  #9222（为这次公关做准备）有一个小表现
  回归确实是变化所附带的。尽管如此，我还是决定
  暂时搁置它。未来，我们希望能够
  将其扩展到构造函数、外部声明等。

* [#9266](https://github.com/leanprover/lean4/pull/9266) 在 LCNF 单声道类型中添加了对 `.mdata` 的支持（然后删除它）
  相反，在 IR 类型级别）。这更符合
  旧编译器的 C++ 代码中的 extern decls 仍在使用中
  目前用于创建 extern decl，很快就会被替换。

* [#9268](https://github.com/leanprover/lean4/pull/9268) 将 `lean_add_extern`/`addExtern` 的实现从
  C++ 转换为 Lean。我相信这是最后一个 C++ 辅助函数
  新编译器依赖的库/编译器目录。我把
  它到它自己的文件中并复制一些代码，因为这个函数
  需要在 CoreM 中执行，而其他 IR 函数则位于它们的
  自己的 monad 堆栈。删除C++编译器后，我们可以移动IR
  函数集成到 CoreM 中。

* [#9275](https://github.com/leanprover/lean4/pull/9275) 删除了用 C++ 编写的旧编译器。

* [#9279](https://github.com/leanprover/lean4/pull/9279) 修复了将 `compiler.extract_closed` 选项迁移到
  Lean（并添加一个测试，以便将来会被捕获）。

* [#9310](https://github.com/leanprover/lean4/pull/9310) 修复了 IR 构造函数参数降低以正确处理
  在所有情况下，都会为相关参数传递不相关的参数。
  发生这种情况是因为构造函数参数降低（不完全）
  重新实现了一般的 LCNF-to-IR 参数降低，解决方法是
  只需采用通用辅助函数即可。这可能是由于
  当新编译器仍在分支上时，重构不完整。

* [#9336](https://github.com/leanprover/lean4/pull/9336) 更改 `trace.Compiler.result` 的实现以使用
  声明它们是提供的，而不是在 LCNF mono 中查找它们
  环境扩展，这似乎是为了省去麻烦
  在打印 decl 之前重新标准化 fvar ID。这意味着
  由 `extractClosed` 通行证创建的 `._closed` 声明现在将
  包含在输出中，如果您之前肯定会感到困惑
  不知道发生了什么。

* [#9344](https://github.com/leanprover/lean4/pull/9344) 正确填充 `IR.FnBody.case` 的 `xType` 字段
  构造函数。事实证明这并没有明显的后果
  不正确，因为它是由 `Boxing` 保守地重新计算的
  通过。

* [#9393](https://github.com/leanprover/lean4/pull/9393) 修复了一个不安全的技巧，即 Exprs 哈希表的哨兵
  （由指针键控）是通过构造一个值来创建的，该值的运行时
  表示永远不可能是有效的 Expr。为此选择的值
  目的是 Unit.unit，这违反了 Expr 没有的推论
  标量构造函数。相反，我们将其更改为新分配的单元
  × 单位值。

* [#9411](https://github.com/leanprover/lean4/pull/9411) 添加了对子单例 `casesOn` 编译的支持。我们
  依靠精化器的类型检查将其限制为电感式
  `Prop`实际上可以消除为`Type n`。这还没有
  涵盖这些类型的其他递归器（或不在 `Prop` 中的感应器）
  那件事）。

* [#9703](https://github.com/leanprover/lean4/pull/9703) 更改 LCNF `elimDeadBranches` 通道，以便考虑
  所有非 `Nat` 文字类型均为 `⊤`。事实证明，将其修复为
  使用当前抽象值正确处理所有这些类型
  代表性是令人惊讶的不平凡，最好直接登陆
  首先修复。

* [#9720](https://github.com/leanprover/lean4/pull/9720) 删除了一个错误，该错误隐式假定类型的排序
  正在添加的测试中存在的已擦除类型之间的依赖关系不能
  发生。仅使用
  LCNF 类型中存在的信息，并且很少是持续的
  值（我不记得它曾经发现过实际问题），所以它使得
  删除它更有意义。

* [#9827](https://github.com/leanprover/lean4/pull/9827) 更改了 `Quot.lcInv` 的降低（编译器内部形式
  `toMono` 中的 `Quot.lift`），以支持过度应用。

* [#9847](https://github.com/leanprover/lean4/pull/9847) 在此定制内联路径中添加了对递归声明的检查，
  它修复了旧编译器的回归。

* [#9864](https://github.com/leanprover/lean4/pull/9864) 添加了 `Array.getInternal` 的新变体和
  `Array.get!Internal` 返回借用的参数，即没有
  引用计数增量。这些是供编译器使用的
  可以确定数组将继续保存的情况
  在返回值的生命周期内对元素的有效引用。

## 漂亮的印刷
%%%
tag := "zh-releases-v4-23-0-h006"
%%%

* [#8391](https://github.com/leanprover/lean4/pull/8391) 为 `Vector.mk` 添加一个解展开器，用于解展开 `Vector.mk
  #[...]_` to `#v[...]`。
  ```lean
  -- previously:
  #check #v[1, 2, 3] -- { toArray := #[1, 2, 3], size_toArray := ⋯ } : Vector Nat 3
  -- now:
  #check #v[1, 2, 3] -- #v[1, 2, 3] : Vector Nat 3
  ```

* [#9475](https://github.com/leanprover/lean4/pull/9475) 修复了一些语法由于缺失而打印得非常漂亮的问题
  空白建议。

* [#9494](https://github.com/leanprover/lean4/pull/9494) 修复了导致某些错误消息尝试
  显示悬停不存在的标识符。

* [#9555](https://github.com/leanprover/lean4/pull/9555) 允许消息数据中的提示来指定自定义预览范围
  超出代码操作指定的编辑区域。

* [#9778](https://github.com/leanprover/lean4/pull/9778) 修改要使用的匿名元变量的漂亮打印
  索引而不是内部名称。这导致较小的数值
  `?m.123` 中的后缀，因为索引在给定范围内编号
  元变量上下文而不是跨整个文件，因此每个
  命令有自己的编号。这还不影响漂亮的打印
  宇宙层级 元变量。

## 文档
%%%
tag := "zh-releases-v4-23-0-h007"
%%%

* [#9093](https://github.com/leanprover/lean4/pull/9093) 添加了 `ToFormat.toFormat` 缺失的文档字符串。

* [#9152](https://github.com/leanprover/lean4/pull/9152) 修复了 `registerDerivingHandler` 的过时文档字符串

* [#9593](https://github.com/leanprover/lean4/pull/9593) 显着简化了 `propext` 的文档字符串。

## 服务器
%%%
tag := "zh-releases-v4-23-0-h008"
%%%

* [#9040](https://github.com/leanprover/lean4/pull/9040) 改进了“转到定义”用户体验，具体来说：
  - 现在，在类型类投影上使用“转到定义”将提取
  所涉及的具体实例并提供它们作为位置
  跳到。例如，在 `toString` 上使用“转到定义”
  `toString 0` 将产生 `ToString.toString` 和 `ToString 的结果
  纳特`。
  - 在生成带有类型的语法的宏上使用“转到定义”
  class projections will now also extract the specific instances that were
  参与并提供它们作为跳转到的位置。例如，使用
  `1 + 1` 的 `+` 上的“转到定义”将产生以下结果
  `HAdd.hAdd`、`HAdd α α α` 和 `Add Nat`。
  - 使用“转到声明”现在将提供“转到声明”的所有结果
  定义”除了精化器和解析器之外
  参与。例如，在 `1 + 1` 的 `+` 上使用“转到声明”
  将产生 `HAdd.hAdd`、`HAdd α α α`、`Add Nat` 的结果，
  ``macro_rules | ``macro_rules | ``macro_rules | ``macro_rules | ``macro_rules | ``macro_rules | ``macro_rules | ``macro_rules | `($x + $y) => ...`` and `infixl:65 " + " => HAdd.hAdd`。
  - 对类型包含的值使用“转到 Type 定义”
  多个常量现在将为每个常量提供“转到定义”结果
  常数。例如，在 `x` 上使用“转到 Type 定义”作为“x”：
  数组 Nat` will yield results for `Array` and `Nat`。

* [#9163](https://github.com/leanprover/lean4/pull/9163) 禁止使用 `lake setup-file` 生成的标头
  现在的服务器。一旦考虑到 Lake，它将重新启用
  处理工作区模块时服务器给出的标头。
  如果没有这个，当文件 `setup-file` 标头可能会产生奇怪的行为
  在磁盘上和编辑器中对于文件是否参与存在分歧
  模块系统。

* [#9563](https://github.com/leanprover/lean4/pull/9563) 对 `~20%` 的模糊匹配执行一些微观优化
  指令获胜。

* [#9784](https://github.com/leanprover/lean4/pull/9784) 确保编辑器进度条更好地反映实际情况
  并行精化的进展。

## Lake
%%%
tag := "zh-releases-v4-23-0-h009"
%%%

* [#9053](https://github.com/leanprover/lean4/pull/9053) 更新 Lake 以解析可传递的 `.olean` 文件
  通过 `lean --setup` 的 `modules` 字段导入 Lean。这个
  启用意味着 Lean 现在可以直接使用来自
  Lake 缓存，无需将它们定位在特定的层次结构中
  路径。

* [#9101](https://github.com/leanprover/lean4/pull/9101) 修复了 #9081 引入的源文件被删除的错误
  从模块输入跟踪中删除了一些条目
  模块作业日志。

* [#9162](https://github.com/leanprover/lean4/pull/9162) 更改 Lake 用于内容中 `,ir` 工件的密钥
  hash数据结构改为`r`，保持单一的约定
  字符键名称。

* [#9165](https://github.com/leanprover/lean4/pull/9165) 修复了 Lake 创建静态过程的两个问题
  档案。

* [#9332](https://github.com/leanprover/lean4/pull/9332) 更改了 Lake 中的依赖克隆机制，因此日志
  消息称 Lake 正在克隆
  依赖发生在它完成之前（而不是在它之前）
  开始）。这已经是一个
  对于不明白为什么 Lake 看起来像的用户来说，这是一个巨大的困惑源
  只是被困住了
  原因是在设置新项目时，现在的输出是：
  ```
  λ lake +lean4 new math math
  info: downloading mathlib `lean-toolchain` file
  info: math: no previous manifest, creating one from scratch
  info: leanprover-community/mathlib: cloning https://github.com/leanprover-community/mathlib4
  <hang>
  info: leanprover-community/mathlib: checking out revision 'cd11c28c6a0d514a41dd7be9a862a9c8815f8599'
  ```

* [#9434](https://github.com/leanprover/lean4/pull/9434) 更改 Lake 本地缓存基础架构以进行恢复
  缓存中的可执行文件以及共享库和静态库。这意味着
  他们保留了预期的名称，一些用例仍然依赖这些名称。

* [#9435](https://github.com/leanprover/lean4/pull/9435) 添加 `libPrefixOnWindows` 包和库配置
  选项。启用后，Lake 将为静态库和共享库添加前缀
  Windows 上的 `lib`（即与 Unix 上的方式相同）。

* [#9436](https://github.com/leanprover/lean4/pull/9436) 将运行的作业数添加到 Lake 生成的最终消息中
  成功运行 `lake build`。

* [#9478](https://github.com/leanprover/lean4/pull/9478) 添加了对 `meta import` 的正确 Lake 支持。模块 IR 现在是
  在跟踪和预解析模块中进行跟踪 Lake 传递到“Lean”
  --设置`。

* [#9525](https://github.com/leanprover/lean4/pull/9525) 修复了 Lake 对模块系统 `import all` 的处理。
  此前，Lake 将 `import all` 视为与非模块 `import` 相同，
  导入传递导入树中的所有私有数据。现在Lake
  区分两者，`import all M` 只是导入私有
  `M` 的数据。接下来是`M`的直接私人导入，但是他们
  没有得到晋升。

* [#9559](https://github.com/leanprover/lean4/pull/9559) 更改 `lake setup-file` 以使用服务器提供的标头
  工作区模块。

* [#9604](https://github.com/leanprover/lean4/pull/9604) 将 Lake 的精简档案生成限制为仅 Windows
  核心构建（即 `bootstrap = true`）。通常使用非捆绑的 `ar`
  对于 macOS 上的核心版本不支持 `--thin`，因此我们避免使用它
  除非有必要。

* [#9677](https://github.com/leanprover/lean4/pull/9677) 将构建时间添加到构建监视器的每个构建步骤（在
  `-v` 或 CI 中）并延迟在 `--no-build` 上退出，直到
  构建监视器完成。因此，现在将报告 `--no-build` 故障
  其目标是通过需要重建来阻止 Lake。

* [#9697](https://github.com/leanprover/lean4/pull/9697) 修复了 `lake lean` 和 `lake setup-file` 中的处理
  具有多个点的库源文件（例如，`src/Foo.Bar.lean`）。

* [#9698](https://github.com/leanprover/lean4/pull/9698) 将 `lake query` 的格式化类型类调整为 no
  不再需要文本和 JSON 形式，而是使用任何
  两者的结合。课程也已更名。此外，
  文本模块标题的查询格式已改进为仅
  产生有效的标头。

## 其他
%%%
tag := "zh-releases-v4-23-0-h010"
%%%

* [#9106](https://github.com/leanprover/lean4/pull/9106) 修复了“未定义符号：lean::mpz::divexact(lean::mpz const&,
  Lean::mpz const&)` when building without `LEAN_USE_GMP`

* [#9114](https://github.com/leanprover/lean4/pull/9114) 进一步提高发布自动化，自动合并
  来自凸块中 `nightly-testing` 和 `bump/v4.X.0` 分支的材料
  PR 到下游存储库。

* [#9659](https://github.com/leanprover/lean4/pull/9659) 修复了 `trace.profiler.output` 选项与
  较新版本的 Firefox Profiler

````
