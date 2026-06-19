/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.6.0 (2024-02-29)" =>
%%%
tag := "release-v4.6.0"
file := "v4.6.0"
%%%

````markdown
* Add custom simplification procedures (aka `simproc`s) to `simp`. Simprocs can be triggered by the simplifier on a specified term-pattern. Here is an small example:
  ```lean
  import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

  def foo (x : Nat) : Nat :=
    x+10

  /--
  `simproc` `reduceFoo` 根据与模式 `foo _` 匹配的术语进行调用。
  -/
  simproc reduceFoo(foo _) :=
    /- `Expr → SimpM Step 类型的项 -/
    有趣的 e => 做
      /-
      `Step` 类型具有三个构造函数：`.done`、`.visit`、`.continue`。
      * 构造函数 `.done` 指示 `simp` 结果是
        不需要进一步简化。
      * 构造函数 `.visit` 指示 `simp` 访问结果表达式。
      * 构造函数 `.continue` 指示 `simp` 尝试其他简化过程。

      所有三个构造函数都采用 `Result`。 `.continue` 构造函数也可以采用 `none`。
      `Result` 有两个字段 `expr`（新表达式）和 `proof?`（可选证明）。
       如果新表达式在定义上等于输入表达式，则可以省略 `proof?` 或将其设置为 `none`。
      -/
      /- `simp` 使用匹配的模约简性。因此，我们确保该术语是 `foo` 应用程序。 -/
      除非 e.isAppOfArity ``foo 1 执行
        返回.继续
      // `Nat.fromExpr?` 尝试将表达式转换为 `Nat` 值 -/
      让一些n←Nat.fromExpr？ e.appArg！
        |返回.继续
      返回.done { expr := Lean.mkNatLit (n+10) }
  ```
  We disable simprocs support by using the command `set_option simprocs false`. This command is particularly useful when porting files to v4.6.0.
  Simprocs can be scoped, manually added to `simp` commands, and suppressed using `-`. They are also supported by `simp?`. `simp only` does not execute any `simproc`. Here are some examples for the `simproc` defined above.
  ```lean
  example : x + foo 2 = 12 + x := by
    set_option simprocs false in
      /- 由于 `simproc` 被禁用，此 `simp` 命令不会取得进展。 -/
      失败如果成功简单
    简单的阿里斯

  example : x + foo 2 = 12 + x := by
    // `simp only` 不得使用默认的 simproc 集。 -/
    仅fail_if_success simp
    简单的阿里斯

  example : x + foo 2 = 12 + x := by
    /-
    `simp only` 不使用默认的 simproc 设置，
    但我们可以提供 simprocs 作为参数。 -/
    仅简化 [reduceFoo]
    简单的阿里斯

  example : x + foo 2 = 12 + x := by
    /- 我们可以使用 `-` 禁用 `simproc`。 -/
    fail_if_success simp [-reduceFoo]
    简单的阿里斯
  ```
  The command `register_simp_attr <id>` now creates a `simp` **and** a `simproc` set with the name `<id>`. The following command instructs Lean to insert the `reduceFoo` simplification procedure into the set `my_simp`. If no set is specified, Lean uses the default `simp` set.
  ```lean
  simproc [my_simp] reduceFoo (foo _) := ...
  ```

* The syntax of the `termination_by` and `decreasing_by` termination hints is overhauled:

  * They are now placed directly after the function they apply to, instead of
    after the whole `mutual` block.
  * Therefore, the function name no longer has to be mentioned in the hint.
  * If the function has a `where` clause, the `termination_by` and
    `decreasing_by` for that function come before the `where`. The
    functions in the `where` clause can have their own termination hints, each
    following the corresponding definition.
  * The `termination_by` clause can only bind “extra parameters”, that are not
    already bound by the function header, but are bound in a lambda (`:= fun x
    y z =>`) or in patterns (`| x, n + 1 => …`). These extra parameters used to
    be understood as a suffix of the function parameters; now it is a prefix.

  Migration guide: In simple cases just remove the function name, and any
  variables already bound at the header.
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by foo a b => a - b
  +终止_by a b => a - b
  ```
  or
  ```diff
   def foo : Nat → Nat → Nat := …
  -termination_by _ a b => a - b
  +终止_by a b => a - b
  ```

  If the parameters are bound in the function header (before the `:`), remove them as well:
  ```diff
   def foo (a b : Nat) : Nat := …
  -termination_by foo a b => a - b
  +终止_由 a - b
  ```

  Else, if there are multiple extra parameters, make sure to refer to the right
  ones; the bound variables are interpreted from left to right, no longer from
  right to left:
  ```diff
   def foo : Nat → Nat → Nat → Nat
     | a、b、c => …
  -termination_by foo b c => b
  +终止_by a b => b
  ```

  In the case of a `mutual` block, place the termination arguments (without the
  function name) next to the function definition:
  ```diff
  -相互的
  -def foo : Nat → Nat → Nat := …
  -def bar : Nat → Nat := …
  -结束
  -终止者
  -  foo a b => a - b
  -  条 a => a
  +相互
  +def foo : Nat → Nat → Nat := …
  +终止_by a b => a - b
  +def bar : Nat → Nat := …
  +终止_a => a
  +结束
  ```

  Similarly, if you have (mutual) recursion through `where` or `let rec`, the
  termination hints are now placed directly after the function they apply to:
  ```diff
  -def foo (a b : Nat) : Nat := …
  -  其中 bar (x : Nat) : Nat := ...
  -终止者
  -  foo a b => a - b
  -  条 x => x
  +def foo (a b : Nat) : Nat := …
  +终止_由 a - b
  +  哪里
  +    条 (x : Nat) : Nat := …
  +    由 x 终止

  -def foo (a b : Nat) : Nat :=
  -  让rec bar (x : Nat) : Nat := …
  -  ……
  -终止者
  -  foo a b => a - b
  -  条 x => x
  +def foo (a b : Nat) : Nat :=
  +  让rec bar (x : Nat) : Nat := …
  +    由 x 终止
  +  ……
  +终止_由 a - b
  ```

  In cases where a single `decreasing_by` clause applied to multiple mutually
  recursive functions before, the tactic now has to be duplicated.

* The semantics of `decreasing_by` changed; the tactic is applied to all
  termination proof goals together, not individually.

  This helps when writing termination proofs interactively, as one can focus
  each subgoal individually, for example using `·`. Previously, the given
  tactic script had to work for _all_ goals, and one had to resort to tactic
  combinators like `first`:

  ```diff
   def foo (n : Nat) := … foo e1 … foo e2 …
  -decreising_by
  -simp_wf
  -第一|应用something_about_e1； ……
  -      |应用something_about_e2； ……
  +减少_by
  +all_goals simp_wf
  +· 应用 some_about_e1； ……
  +· 应用 some_about_e2； ……
  ```

  To obtain the old behaviour of applying a tactic to each goal individually,
  use `all_goals`:
  ```diff
   def foo (n : Nat) := …
  -按某种策略减少
  +按所有目标减少一些_战术
  ```

  In the case of mutual recursion each `decreasing_by` now applies to just its
  function. If some functions in a recursive group do not have their own
  `decreasing_by`, the default `decreasing_tactic` is used. If the same tactic
  ought to be applied to multiple functions, the `decreasing_by` clause has to
  be repeated at each of these functions.

* Modify `InfoTree.context` to facilitate augmenting it with partial contexts while elaborating a command. This breaks backwards compatibility with all downstream projects that traverse the `InfoTree` manually instead of going through the functions in `InfoUtils.lean`, as well as those manually creating and saving `InfoTree`s. See [PR #3159](https://github.com/leanprover/lean4/pull/3159) for how to migrate your code.

* Add language server support for [call hierarchy requests](https://www.youtube.com/watch?v=r5LA7ivUb2c) ([PR #3082](https://github.com/leanprover/lean4/pull/3082)). The change to the .ilean format in this PR means that projects must be fully rebuilt once in order to generate .ilean files with the new format before features like "find references" work correctly again.

* Structure instances with multiple sources (for example `{a, b, c with x := 0}`) now have their fields filled from these sources
  in strict left-to-right order. Furthermore, the structure instance elaborator now aggressively use sources to fill in subobject
  fields, which prevents unnecessary eta expansion of the sources,
  and hence greatly reduces the reliance on costly structure eta reduction. This has a large impact on mathlib,
  reducing total CPU instructions by 3% and enabling impactful refactors like leanprover-community/mathlib4#8386
  which reduces the build time by almost 20%.
  See [PR #2478](https://github.com/leanprover/lean4/pull/2478) and [RFC #2451](https://github.com/leanprover/lean4/issues/2451).

* Add pretty printer settings to omit deeply nested terms (`pp.deepTerms false` and `pp.deepTerms.threshold`) ([PR #3201](https://github.com/leanprover/lean4/pull/3201))

* Add pretty printer options `pp.numeralTypes` and `pp.natLit`.
  When `pp.numeralTypes` is true, then natural number literals, integer literals, and rational number literals
  are pretty printed with type ascriptions, such as `(2 : Rat)`, `(-2 : Rat)`, and `(-2 / 3 : Rat)`.
  When `pp.natLit` is true, then raw natural number literals are pretty printed as `nat_lit 2`.
  [PR #2933](https://github.com/leanprover/lean4/pull/2933) and [RFC #3021](https://github.com/leanprover/lean4/issues/3021).

Lake updates:
* improved platform information & control [#3226](https://github.com/leanprover/lean4/pull/3226)
* `lake update` from unsupported manifest versions [#3149](https://github.com/leanprover/lean4/pull/3149)

Other improvements:
* make `intro` be aware of `let_fun` [#3115](https://github.com/leanprover/lean4/pull/3115)
* produce simpler proof terms in `rw` [#3121](https://github.com/leanprover/lean4/pull/3121)
* fuse nested `mkCongrArg` calls in proofs generated by `simp` [#3203](https://github.com/leanprover/lean4/pull/3203)
* `induction using` followed by a general term [#3188](https://github.com/leanprover/lean4/pull/3188)
* allow generalization in `let` [#3060](https://github.com/leanprover/lean4/pull/3060), fixing [#3065](https://github.com/leanprover/lean4/issues/3065)
* reducing out-of-bounds `swap!` should return `a`, not `default`` [#3197](https://github.com/leanprover/lean4/pull/3197), fixing [#3196](https://github.com/leanprover/lean4/issues/3196)
* derive `BEq` on structure with `Prop`-fields [#3191](https://github.com/leanprover/lean4/pull/3191), fixing [#3140](https://github.com/leanprover/lean4/issues/3140)
* refine through more `casesOnApp`/`matcherApp` [#3176](https://github.com/leanprover/lean4/pull/3176), fixing [#3175](https://github.com/leanprover/lean4/pull/3175)
* do not strip dotted components from lean module names [#2994](https://github.com/leanprover/lean4/pull/2994), fixing [#2999](https://github.com/leanprover/lean4/issues/2999)
* fix `deriving` only deriving the first declaration for some handlers [#3058](https://github.com/leanprover/lean4/pull/3058), fixing [#3057](https://github.com/leanprover/lean4/issues/3057)
* do not instantiate metavariables in kabstract/rw for disallowed occurrences [#2539](https://github.com/leanprover/lean4/pull/2539), fixing [#2538](https://github.com/leanprover/lean4/issues/2538)
* hover info for `cases h : ...` [#3084](https://github.com/leanprover/lean4/pull/3084)
````
