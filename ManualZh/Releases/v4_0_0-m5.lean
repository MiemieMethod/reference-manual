/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.0.0-m5 (2022-08-22)" =>
%%%
tag := "release-v4.0.0-m5"
file := "v4.0.0-m5"
%%%

````markdown
This is the fifth milestone release of Lean 4. It contains many improvements and many new features.
 We had  1495 commits since the last milestone.

Contributors:
```
   第885章 莱昂纳多·德·莫拉
   第310章 塞巴斯蒂安·乌尔里希
    69 艾尔斯
    66 沃伊切赫·纳罗基
    49 加布里埃尔·艾伯纳
    38 马里奥·卡内罗
    22 拉斯克21
    10 泰德
     6 艾德·艾尔斯
     6 玛丽安娜·阿拉尼斯
     4 克里斯·洛维特
     3 詹尼斯·林佩尔格
     2 弗朗索瓦·G·多赖斯
     2 亨里克·博文
     2 雅各布·冯·劳默
     2 斯科特·莫里森
     2悉达多
     1 安德烈斯·戈恩斯
     1 阿瑟·保利诺
     1 康纳·贝克
     1 约沙
     1 卡塞夸克
     1 拉尔斯
     1 台 Mac
     1 马库斯·罗塞尔
     1 帕特里克·马索特
     1 悉达多·巴特
     1 蒂莫
     1 文森特·德·哈恩
     1 威廉·布莱克
     1 尤里·德·维特
     1 阿姆克恩
     1 asdasd1dsadsa
     1克兹维
```



* Update Lake to v4.0.0. See the [v4.0.0 release notes](https://github.com/leanprover/lake/releases/tag/v4.0.0) for detailed changes.

* Mutual declarations in different namespaces are now supported. Example:
  ```lean
  相互的
    def Foo.boo (x : Nat) :=
      将 x 与
      | 0 => 1
      | x + 1 => 2*Boo.bla x

    def Boo.bla (x : Nat) :=
      将 x 与
      | 0 => 2
      | x+1 => 3*Foo.boo x
  end
  ```
  A `namespace` is automatically created for the common prefix. Example:
  ```lean
  相互的
    def Tst.Foo.boo (x : Nat) := ...
    def Tst.Boo.bla (x : Nat) := ...
  end
  ```
  expands to
  ```lean
  namespace Tst
  相互的
    def Foo.boo (x : Nat) := ...
    def Boo.bla (x : Nat) := ...
  end
  end Tst
  ```

* Allow users to install their own `deriving` handlers for existing type classes.
  See example at [Simple.lean](https://github.com/leanprover/lean4/blob/master/tests/pkg/deriving/UserDeriving/Simple.lean).

* Add tactic `congr (num)?`. See doc string for additional details.

* [Missing doc linter](https://github.com/leanprover/lean4/pull/1390)

* `match`-syntax notation now checks for unused alternatives. See issue [#1371](https://github.com/leanprover/lean4/issues/1371).

* Auto-completion for structure instance fields. Example:
  ```lean
  example : Nat × Nat := {
    f——这里
  }
  ```
  `fst` now appears in the list of auto-completion suggestions.

* Auto-completion for dotted identifier notation. Example:
  ```lean
  example : Nat :=
    .su——这里
  ```
  `succ` now appears in the list of auto-completion suggestions.

* `nat_lit` is not needed anymore when declaring `OfNat` instances. See issues [#1389](https://github.com/leanprover/lean4/issues/1389) and [#875](https://github.com/leanprover/lean4/issues/875). Example:
  ```lean
  inductive Bit where
    |零
    |一

  instance inst0 : OfNat Bit 0 where
    ofNat := Bit.0

  instance : OfNat Bit 1 where
    ofNat := Bit.one

  example : Bit := 0
  example : Bit := 1
  ```

* Add `[elabAsElim]` attribute (it is called `elab_as_eliminator` in Lean 3). Motivation: simplify the Mathlib port to Lean 4.

* `Trans` type class now accepts relations in `Type u`. See this [Zulip issue](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Calc.20mode/near/291214574).

* Accept unescaped keywords as inductive constructor names. Escaping can often be avoided at use sites via dot notation.
  ```lean
  inductive MyExpr
    |让： ...

  def f : MyExpr → MyExpr
    | .让... => .让...
  ```

* Throw an error message at parametric local instances such as `[Nat -> Decidable p]`. The type class resolution procedure
  cannot use this kind of local instance because the parameter does not have a forward dependency.
  This check can be disabled using `set_option checkBinderAnnotations false`.

* Add option `pp.showLetValues`. When set to `false`, the info view hides the value of `let`-variables in a goal.
  By default, it is `true` when visualizing tactic goals, and `false` otherwise.
  See [issue #1345](https://github.com/leanprover/lean4/issues/1345) for additional details.

* Add option `warningAsError`. When set to true, warning messages are treated as errors.

* Support dotted notation and named arguments in patterns. Example:
  ```lean
  def getForallBinderType (e : Expr) : Expr :=
    将 e 与
    | .forallE (binderType := 类型) .. => 类型
    | _ => 恐慌！ “一切都在预料之中”
  ```

* "jump-to-definition" now works for function names embedded in the following attributes
  `@[implementedBy funName]`, `@[tactic parserName]`, `@[termElab parserName]`, `@[commandElab parserName]`,
  `@[builtinTactic parserName]`, `@[builtinTermElab parserName]`, and `@[builtinCommandElab parserName]`.
   See [issue #1350](https://github.com/leanprover/lean4/issues/1350).

* Improve `MVarId` methods discoverability. See [issue #1346](https://github.com/leanprover/lean4/issues/1346).
  We still have to add similar methods for `FVarId`, `LVarId`, `Expr`, and other objects.
  Many existing methods have been marked as deprecated.

* Add attribute `[deprecated]` for marking deprecated declarations. Examples:
  ```lean
  def g (x : Nat) := x + 1

  -- 每当使用 `f` 时，都会生成一条警告消息，建议改用 `g`。
  @[deprecated g]
  def f (x : Nat) := x + 1

  #check f 0 -- warning: `f` has been deprecated, use `g` instead

  -- 每当使用 `h` 时，都会生成警告消息。
  @[deprecated]
  def h (x : Nat) := x + 1

  #check h 0 -- warning: `h` has been deprecated
  ```

* Add type `LevelMVarId` (and abbreviation `LMVarId`) for universe level metavariable ids.
  Motivation: prevent meta-programmers from mixing up universe and expression metavariable ids.

* Improve `calc` term and tactic. See [issue #1342](https://github.com/leanprover/lean4/issues/1342).

* [Relaxed antiquotation parsing](https://github.com/leanprover/lean4/pull/1272) further reduces the need for explicit `$x:p` antiquotation kind annotations.

* Add support for computed fields in inductives. Example:
  ```lean
  inductive Exp
    | var（i：Nat）
    |应用程序（a b : Exp）
  与
    @[computedField] hash : Exp → Nat
      | .var我=>我
      | .app a b => a.hash * b.hash + 1
  ```
  The result of the `Exp.hash` function is then stored as an extra "computed" field in the `.var` and `.app` constructors;
  `Exp.hash` accesses this field and thus runs in constant time (even on dag-like values).

* Update `a[i]` notation. It is now based on the type class
  ```lean
  class GetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop)) where
    getElem (xs : cont) (i : idx) (h : dom xs i) : Elem
  ```
  The notation `a[i]` is now defined as follows
  ```lean
  macro:max x:term noWs "[" i:term "]" : term => `(getElem $x $i (by get_elem_tactic))
  ```
  The proof that `i` is a valid index is synthesized using the tactic `get_elem_tactic`.
  For example, the type `Array α` has the following instances
  ```lean
  instance : GetElem (Array α) Nat α fun xs i => LT.lt i xs.size where ...
  instance : GetElem (Array α) USize α fun xs i => LT.lt i.toNat xs.size where ...
  ```
  You can use the notation `a[i]'h` to provide the proof manually.
  Two other notations were introduced: `a[i]!` and `a[i]?`, For `a[i]!`, a panic error message is produced at
  runtime if `i` is not a valid index. `a[i]?` has type `Option α`, and `a[i]?` evaluates to `none` if the
  index `i` is not valid.
  The three new notations are defined as follows:
  ```lean
  @[inline] def getElem' [GetElem cont idx elem dom] (xs : cont) (i : idx) (h : dom xs i) : elem :=
  getElem xs i h

  @[inline] def getElem! [GetElem cont idx elem dom] [Inhabited elem] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem :=
    if h : _ then getElem xs i h 否则恐慌！ “索引越界”

  @[inline] def getElem? [GetElem cont idx elem dom] (xs : cont) (i : idx) [Decidable (dom xs i)] : Option elem :=
    if h : _ then some (getElem xs i h) else none

  macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)
  macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)
  macro x:term noWs "[" i:term "]'" h:term:max : term => `(getElem' $x $i $h)
  ```
  See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/String.2EgetOp/near/287855425).
  Examples:
  ```lean
  example (a : Array Int) (i : Nat) : Int :=
    a[i] -- 错误：未能证明索引有效...

  example (a : Array Int) (i : Nat) (h : i < a.size) : Int :=
    a[i]——好的

  example (a : Array Int) (i : Nat) : Int :=
    人工智能]！ -  好的

  example (a : Array Int) (i : Nat) : Option Int :=
    人工智能]？ -  好的

  example (a : Array Int) (h : a.size = 2) : Int :=
    a[0]'(by rw [h];决定) -- 好的

  example (a : Array Int) (h : a.size = 2) : Int :=
    有：0 < a.size := by rw [h];决定
    有：1 < a.size := by rw [h];决定
    a[0] + a[1] -- 好的

  example (a : Array Int) (i : USize) (h : i.toNat < a.size) : Int :=
    a[i]——好的
  ```
  The `get_elem_tactic` is defined as
  ```lean
  macro "get_elem_tactic" : tactic =>
    `（首先
      |获取元素战术琐碎
      |失败“未能证明索引有效，...”
     ）
  ```
  The `get_elem_tactic_trivial` auxiliary tactic can be extended using `macro_rules`. By default, it tries `trivial`, `simp_arith`, and a special case for `Fin`. In the future, it will also try `linarith`.
  You can extend `get_elem_tactic_trivial` using `my_tactic` as follows
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(策略| my_tropic)
  ```
  Note that `Idx`'s type in `GetElem` does not depend on `Cont`. So, you cannot write the instance `instance : GetElem (Array α) (Fin ??) α fun xs i => ...`, but the Lean library comes equipped with the following auxiliary instance:
  ```lean
  instance [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
    getElem xs i h := getElem xs i.1 h
  ```
  and helper tactic
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(策略| 应用 Fin.val_lt_of_le; get_elem_tropic_trivial; 完成)
  ```
  Example:
  ```lean
  example (a : Array Nat) (i : Fin a.size) :=
    a[i]——好的

  example (a : Array Nat) (h : n ≤ a.size) (i : Fin n) :=
    a[i]——好的
  ```

* Better support for qualified names in recursive declarations. The following is now supported:
  ```lean
  namespace Nat
    def fact : Nat → Nat
    | 0 => 1
    | n+1 => (n+1) * Nat.fact n
  end Nat
  ```

* Add support for `CommandElabM` monad at `#eval`. Example:
  ```lean
  import Lean

  open Lean Elab Command

  #eval do
    让 id := mkIdent `foo
    elabCommand (← `(def $id := 10))

  #eval foo -- 10
  ```

* Try to elaborate `do` notation even if the expected type is not available. We still delay elaboration when the expected type
  is not available. This change is particularly useful when writing examples such as
  ```lean
  #eval do
    IO.println“你好”
    IO.println“世界”
  ```
  That is, we don't have to use the idiom `#eval show IO _ from do ...` anymore.
  Note that auto monadic lifting is less effective when the expected type is not available.
  Monadic polymorphic functions (e.g., `ST.Ref.get`) also require the expected type.

* On Linux, panics now print a backtrace by default, which can be disabled by setting the environment variable `LEAN_BACKTRACE` to `0`.
  Other platforms are TBD.

* The `group(·)` `syntax` combinator is now introduced automatically where necessary, such as when using multiple parsers inside `(...)+`.

* Add ["Typed Macros"](https://github.com/leanprover/lean4/pull/1251): syntax trees produced and accepted by syntax antiquotations now remember their syntax kinds, preventing accidental production of ill-formed syntax trees and reducing the need for explicit `:kind` antiquotation annotations. See PR for details.

* Aliases of protected definitions are protected too. Example:
  ```lean
  protected def Nat.double (x : Nat) := 2*x

  namespace Ex
  export Nat (double) -- 为 Nat.double 添加别名 Ex.double
  end Ex

  open Ex
  #check Ex.double -- Ok
  #check double -- Error, `Ex.double` is alias for `Nat.double` which is protected
  ```

* Use `IO.getRandomBytes` to initialize random seed for `IO.rand`. See discussion at [this PR](https://github.com/leanprover/lean4-samples/pull/2).

* Improve dot notation and aliases interaction. See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Namespace-based.20overloading.20does.20not.20find.20exports/near/282946185) for additional details.
  Example:
  ```lean
  def Set (α : Type) := α → Prop
  def Set.union (s₁ s₂ : Set α) : Set α := fun a => s₁ a ∨ s₂ a
  def FinSet (n : Nat) := Fin n → Prop

  namespace FinSet
    导出集（联合）——FinSet.union 现在是 `Set.union` 的别名
  end FinSet

  example (x y : FinSet 10) : FinSet 10 :=
    x.union y -- 作品
  ```

* `ext` and `enter` conv tactics can now go inside let-declarations. Example:
  ```lean
  example (g : Nat → Nat) (y : Nat) (h : let x := y + 1; g (0+x) = x) : g (y + 1) = y + 1 := by
    h 处的转换 => 输入 [x, 1, 1]； rw [Nat.zero_add]
    /-
      g : 纳特 → 纳特
      y : 纳特
      h : 让 x := y + 1;
          克x=x
      ⊢ g (y + 1) = y + 1
    -/
    精确的小时
  ```

* Add `zeta` conv tactic to expand let-declarations. Example:
  ```lean
  example (h : let x := y + 1; 0 + x = y) : False := by
    h => zeta 处的转换； rw [Nat.zero_add]
    /-
      y : 纳特
      h : y + 1 = y
      ⊢ 错误
    -/
    simp_arith 在 h
  ```

* Improve namespace resolution. See issue [#1224](https://github.com/leanprover/lean4/issues/1224). Example:
  ```lean
  import Lean
  open Lean Parser Elab
  open Tactic -- now opens both `Lean.Parser.Tactic` and `Lean.Elab.Tactic`
  ```

* Rename `constant` command to `opaque`. See discussion at [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/What.20is.20.60opaque.60.3F/near/284926171).

* Extend `induction` and `cases` syntax: multiple left-hand-sides in a single alternative. This extension is very similar to the one implemented for `match` expressions. Examples:
  ```lean
  inductive Foo where
    | mk1 (x : 纳特) | mk2（x：Nat）| MK3

  def f (v : Foo) :=
    将 v 与
    | .mk1 x => x + 1
    | .mk2 x => 2*x + 1
    | .mk3 => 1

  theorem f_gt_zero : f v > 0 := by
    案例 v 与
    | MK1 X | mk2 x => simp_arith!  -- 这里使用了新功能！
    | mk3 => 决定
  ```

* [`let/if` indentation in `do` blocks in now supported.](https://github.com/leanprover/lean4/issues/1120)

* Add unnamed antiquotation `$_` for use in syntax quotation patterns.

* [Add unused variables linter](https://github.com/leanprover/lean4/pull/1159). Feedback welcome!

* Lean now generates an error if the body of a declaration body contains a universe parameter that does not occur in the declaration type, nor is an explicit parameter.
  Examples:
  ```lean
  /-
  以下声明现在会产生错误，因为 `PUnit` 是 Universe 多态，
  但 Universe 参数未出现在函数类型 `Nat → Nat` 中
  -/
  def f (n : Nat) : Nat :=
    让 aux (_ : PUnit) : Nat := n + 1
    辅助⟨⟩

  /-
  接受以下声明，因为在
  函数签名。
  -/
  def g.{u} (n : Nat) : Nat :=
    让 aux (_ : PUnit.{u}) : Nat := n + 1
    辅助⟨⟩
  ```

* Add `subst_vars` tactic.

* [Fix `autoParam` in structure fields lost in multiple inheritance.](https://github.com/leanprover/lean4/issues/1158).

* Add `[eliminator]` attribute. It allows users to specify default recursor/eliminators for the `induction` and `cases` tactics.
  It is an alternative for the `using` notation. Example:
  ```lean
  @[eliminator] protected def recDiag {motive : Nat → Nat → Sort u}
      （zero_zero：动机 0 0）
      (succ_zero : (x : Nat) → 动机 x 0 → 动机 (x + 1) 0)
      (zero_succ : (y : Nat) → 动机 0 y → 动机 0 (y + 1))
      (succ_succ : (x y : Nat) → 动机 x y → 动机 (x + 1) (y + 1))
      (x y : Nat) : 动机 x y :=
    let rec go : (x y : Nat) → 动机 x y
      | 0, 0 => 零_零
      | x+1, 0 => succ_zero x (go x 0)
      | 0, y+1 => Zero_succ y (转到 0 y)
      | x+1, y+1 => succ_succ x y (去 x y)
    去 x y
  Termination_by go x y => (x, y)

  def f (x y : Nat) :=
    将 x, y 与
    | 0, 0 => 1
    | x+1, 0 => f x 0
    | 0, y+1 => f 0 y
    | x+1, y+1 => f x y
  终止_by f x y => (x, y)

  example (x y : Nat) : f x y > 0 := by
    感应 x, y <;> simp [f, *]
  ```

* Add support for `casesOn` applications to structural and well-founded recursion modules.
  This feature is useful when writing definitions using tactics. Example:
  ```lean
  inductive Foo where
    |一个 |乙| c
    |对： Foo × Foo → Foo

  def Foo.deq (a b : Foo) : Decidable (a = b) := by
    案例 a <;> 案例 b
    any_goals apply isFalse Foo.noConfusion
    any_goals apply isTrue rfl
    案例对 a b =>
      让 (a₁, a2) := a
      让 (b₁, b2) := b
      与 deq a₁ b₁、deq a2 b2 完全匹配
      | isTrue h₁, isTrue h2 => isTrue (by rw [h₁,h2])
      | isFalse h₁, _ => isFalse (fun h => 按情况 h; 情况 (h₁ rfl))
      | _, isFalse h2 => isFalse (fun h => 按情况 h; 情况 (h2 rfl))
  ```

* `Option` is again a monad. The auxiliary type `OptionM` has been removed. See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Do.20we.20still.20need.20OptionM.3F/near/279761084).

* Improve `split` tactic. It used to fail on `match` expressions of the form `match h : e with ...` where `e` is not a free variable.
  The failure used to occur during generalization.


* New encoding for `match`-expressions that use the `h :` notation for discriminants. The information is not lost during delaboration,
  and it is the foundation for a better `split` tactic. at delaboration time. Example:
  ```lean
  #print Nat.decEq
  /-
  protected def Nat.decEq : (n m : Nat) → 可判定 (n = m) :=
  有趣的米=>
    匹配 h : Nat.beq n m 与
    | true => isTrue (_ : n = m)
    | false => isFalse (_ : Øn = m)
  -/
  ```

* `exists` tactic is now takes a comma separated list of terms.

* Add `dsimp` and `dsimp!` tactics. They guarantee the result term is definitionally equal, and only apply
  `rfl`-theorems.

* Fix binder information for `match` patterns that use definitions tagged with `[matchPattern]` (e.g., `Nat.add`).
  We now have proper binder information for the variable `y` in the following example.
  ```lean
  def f (x : Nat) : Nat :=
    将 x 与
    | 0 => 1
    | y + 1 => y
  ```

* (Fix) the default value for structure fields may now depend on the structure parameters. Example:
  ```lean
  structure Something (i: Nat) where
  n1: 自然:= 1
  n2:自然数:= 1 + i

  def s : Something 10 := {}
  example : s.n2 = 11 := rfl
  ```

* Apply `rfl` theorems at the `dsimp` auxiliary method used by `simp`. `dsimp` can be used anywhere in an expression
  because it preserves definitional equality.

* Refine auto bound implicit feature. It does not consider anymore unbound variables that have the same
  name of a declaration being defined. Example:
  ```lean
  def f : f → Bool := -- Error at second `f`
    有趣 _ => 真实

  inductive Foo : List Foo → Type -- Error at second `Foo`
    | x : 富 []
  ```
  Before this refinement, the declarations above would be accepted and the
  second `f` and `Foo` would be treated as auto implicit variables. That is,
  `f : {f : Sort u} → f → Bool`, and
  `Foo : {Foo : Type u} → List Foo → Type`.


* Fix syntax highlighting for recursive declarations. Example
  ```lean
  inductive List (α : Type u) where
    | nil ：列表 α -- `List` 不再突出显示为变量
    | cons (头: α) (尾: 列表 α) : 列表 α

  def List.map (f : α → β) : List α → List β
    | [] => []
    | a::as => f a :: map f as -- `map` 不再突出显示为变量
  ```
* Add `autoUnfold` option to `Lean.Meta.Simp.Config`, and the following macros
  - `simp!` for `simp (config := { autoUnfold := true })`
  - `simp_arith!` for `simp (config := { autoUnfold := true, arith := true })`
  - `simp_all!` for `simp_all (config := { autoUnfold := true })`
  - `simp_all_arith!` for `simp_all (config := { autoUnfold := true, arith := true })`

  When the `autoUnfold` is set to true, `simp` tries to unfold the following kinds of definition
  - Recursive definitions defined by structural recursion.
  - Non-recursive definitions where the body is a `match`-expression. This
    kind of definition is only unfolded if the `match` can be reduced.
  Example:
  ```lean
  def append (as bs : List α) : List α :=
    匹配为
    | [] =>废话
    | a :: as => a :: 追加为 bs

  theorem append_nil (as : List α) : append as [] = as := by
    归纳为 <;> simp_all！

  theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
    归纳为 <;> simp_all！
  ```

* Add `save` tactic for creating checkpoints more conveniently. Example:
  ```lean
  example : <some-proposition> := by
    tac_1
    tac_2
    保存
    tac_3
    ...
  ```
  is equivalent to
  ```lean
  example : <some-proposition> := by
    检查站
      tac_1
      tac_2
    tac_3
    ...
  ```

* Remove support for `{}` annotation from inductive datatype constructors. This annotation was barely used, and we can control the binder information for parameter bindings using the new inductive family indices to parameter promotion. Example: the following declaration using `{}`
  ```lean
  inductive LE' (n : Nat) : Nat → Prop where
    | refl {} : LE' n n -- 希望 `n` 明确
    | succ : LE' n m → LE' n (m+1)
  ```
  can now be written as
  ```lean
  inductive LE' : Nat → Nat → Prop where
    | refl (n : Nat) : LE' n n
    | succ : LE' n m → LE' n (m+1)
  ```
  In both cases, the inductive family has one parameter and one index.
  Recall that the actual number of parameters can be retrieved using the command `#print`.

* Remove support for `{}` annotation in the `structure` command.

* Several improvements to LSP server. Examples: "jump to definition" in mutually recursive sections, fixed incorrect hover information in "match"-expression patterns, "jump to definition" for pattern variables, fixed auto-completion in function headers, etc.

* In `macro ... xs:p* ...` and similar macro bindings of combinators, `xs` now has the correct type `Array Syntax`

* Identifiers in syntax patterns now ignore macro scopes during matching.

* Improve binder names for constructor auto implicit parameters. Example, given the inductive datatype
  ```lean
  inductive Member : α → List α → Type u
    | head : 成员 a (a::as)
    | tail : 成员 a bs → 成员 a (b::bs)
  ```
  before:
  ```lean
  #check @Member.head
  -- @Member.head : {x : Type u_1} → {a : x} → {as : List x} → 成员 a (a :: as)
  ```
  now:
  ```lean
  #check @Member.head
  -- @Member.head : {α : Type u_1} → {a : α} → {as : List α} → 成员 a (a :: as)
  ```

* Improve error message when constructor parameter universe level is too big.

* Add support for `for h : i in [start:stop] do .. ` where `h : i ∈ [start:stop]`. This feature is useful for proving
  termination of functions such as:
  ```lean
  inductive Expr where
    | app (f : 字符串) (args : 数组表达式)

  def Expr.size (e : Expr) : Nat := Id.run do
    将 e 与
    |应用程序 f 参数 =>
      让 mut sz := 1
      对于 h : i in [: args.size] 做
        -- h.upper : i < args.size
        sz := sz + 大小 (args.get ⟨i, h.upper⟩)
      返回尺寸
  ```

* Add tactic `case'`. It is similar to `case`, but does not admit the goal on failure.
  For example, the new tactic is useful when writing tactic scripts where we need to use `case'`
  at `first | ... | ...`, and we want to take the next alternative when `case'` fails.

* Add tactic macro
  ```lean
  macro "stop" s:tacticSeq : tactic => `(repeat sorry)
  ```
  See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Partial.20evaluation.20of.20a.20file).

* When displaying goals, we do not display inaccessible proposition names
if they do not have forward dependencies. We still display their types.
For example, the goal
  ```lean
  案例节点.inl.节点
  β：Type u_1
  b : BinTree β
  k : 纳特
  v : β
  左：树β
  关键：纳特
  值：β
  右：树β
  ihl : BST 左 → Tree.find？ (Tree.insert left k v) k = 一些 v
  ihr : BST 右 → Tree.find？ (Tree.insert right k v) k = 一些 v
  h✝ : k < 键
  a✝³：BST 左
  a✝² : ForallTree (fun k v => k < key) left
  a✝1：BST 右
  a✝ : ForallTree (fun k v => key < k) 对
  ⊢ BST 左
  ```
  is now displayed as
  ```lean
  案例节点.inl.节点
  β：Type u_1
  b : BinTree β
  k : 纳特
  v : β
  左：树β
  关键：纳特
  值：β
  右：树β
  ihl : BST 左 → Tree.find？ (Tree.insert left k v) k = 一些 v
  ihr : BST 右 → Tree.find？ (Tree.insert right k v) k = 一些 v
   : k < 键
   : 英国夏令时间左
   : ForallTree (fun k v => k < key) 左
   : 英国标准时间右
   : ForallTree(fun k v => key < k) 对
  ⊢ BST 左
  ```

* The hypothesis name is now optional in the `by_cases` tactic.

* [Fix inconsistency between `syntax` and kind names](https://github.com/leanprover/lean4/issues/1090).
  The node kinds `numLit`, `charLit`, `nameLit`, `strLit`, and `scientificLit` are now called
  `num`, `char`, `name`, `str`, and `scientific` respectively. Example: we now write
  ```lean
  macro_rules | `($n:num) => `("hello")
  ```
  instead of
  ```lean
  macro_rules | `($n:numLit) => `("hello")
  ```

* (Experimental) New `checkpoint <tactic-seq>` tactic for big interactive proofs.

* Rename tactic `nativeDecide` => `native_decide`.

* Antiquotations are now accepted in any syntax. The `incQuotDepth` `syntax` parser is therefore obsolete and has been removed.

* Renamed tactic `nativeDecide` => `native_decide`.

* "Cleanup" local context before elaborating a `match` alternative right-hand-side. Examples:
  ```lean
  example (x : Nat) : Nat :=
    将 g x 与
    | (a, b) => _ -- 本地上下文不再包含辅助 `_discr := g x`

  example (x : Nat × Nat) (h : x.1 > 0) : f x > 0 := by
    将 x 与
    | (a, b) => _ -- 本地上下文不再包含 `h✝ : x.fst > 0`
  ```

* Improve `let`-pattern (and `have`-pattern) macro expansion. In the following example,
  ```lean
  example (x : Nat × Nat) : f x > 0 := by
    让 (a, b) := x
    完成
  ```
  The resulting goal is now `... |- f (a, b) > 0` instead of `... |- f x > 0`.

* Add cross-compiled [aarch64 Linux](https://github.com/leanprover/lean4/pull/1066) and [aarch64 macOS](https://github.com/leanprover/lean4/pull/1076) releases.

* [Add tutorial-like examples to our documentation](https://github.com/leanprover/lean4/tree/master/doc/examples), rendered using LeanInk+Alectryon.

````
