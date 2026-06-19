/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.0.0-m4 (2022-03-27)" =>
%%%
tag := "release-v4.0.0-m4"
file := "v4.0.0-m4"
%%%

````markdown
This is the fourth milestone release of Lean 4. It contains many improvements and many new features.
We had more than 600 commits since the last milestone.

Contributors:

```
$ git Shortlog -s -n v4.0.0-m3..v4.0.0-m4
   第501章 莱昂纳多·德·莫拉
    65 塞巴斯蒂安·乌尔里希
    11 丹尼尔·法比安
    10 拉斯克21
     5 加布里埃尔·艾伯纳
     2 艾尔斯
     2 乔纳森·科茨
     2 乔沙
     2 马里奥·卡内罗
     2 阿姆克恩
     1 克里斯·洛维特
     1 弗朗索瓦·G·多赖斯
     1 雅各布·冯·劳默
     1 拉尔斯
     1 帕特里克·史蒂文斯
     1 沃伊切赫·纳罗基
     1 王旭柏
     1 个卡萨瓦卡
     1 济吉
```

* `simp` now takes user-defined simp-attributes. You can define a new `simp` attribute by creating a file (e.g., `MySimp.lean`) containing
  ```lean
  import Lean
  open Lean.Meta

  初始化 my_ext : SimpExtension ← registerSimpAttr `my_simp "我自己的 simp 属性"
  ```
  If you don't need to access `my_ext`, you can also use the macro
  ```lean
  import Lean

  register_simp_attr my_simp "我自己的 simp 属性"
  ```
  Recall that the new `simp` attribute is not active in the Lean file where it was defined.
  Here is a small example using the new feature.
  ```lean
  import MySimp

  def f (x : Nat) := x + 2
  def g (x : Nat) := x + 1

  @[my_simp] theorem f_eq : f x = x + 2 := rfl
  @[my_simp] theorem g_eq : g x = x + 1 := rfl

  example : f x + g x = 2*x + 3 := by
    simp_arith [我的_simp]
  ```

* Extend `match` syntax: multiple left-hand-sides in a single alternative. Example:
  ```lean
  def fib : Nat → Nat
  | 0 | 1 => 1
  | n+2 => 斐波那契 n + 斐波那契 (n+1)
  ```
  This feature was discussed at [issue 371](https://github.com/leanprover/lean4/issues/371). It was implemented as a macro expansion. Thus, the following is accepted.
  ```lean
  inductive StrOrNum where
    | S（s：字符串）
    |我（我：整数）

  def StrOrNum.asString (x : StrOrNum) :=
    将 x 与
    |我一个| S a => toString a
  ```


* Improve `#eval` command. Now, when it fails to synthesize a `Lean.MetaEval` instance for the result type, it reduces the type and tries again. The following example now works without additional annotations
  ```lean
  def Foo := List Nat

  def test (x : Nat) : Foo :=
    [x,x+1,x+2]

  #eval test 4
  ```

* `rw` tactic can now apply auto-generated equation theorems for a given definition. Example:
  ```lean
  example (a : Nat) (h : n = 1) : [a].length = n := by
    rw [列表长度]
    跟踪状态 -- .. |- [].length + 1 = n
    rw [列表长度]
    跟踪状态 -- .. |- 0 + 1 = n
    读写[h]
  ```

* [Fuzzy matching for auto completion](https://github.com/leanprover/lean4/pull/1023)

* Extend dot-notation `x.field` for arrow types. If type of `x` is an arrow, we look up for `Function.field`.
For example, given `f : Nat → Nat` and `g : Nat → Nat`, `f.comp g` is now notation for `Function.comp f g`.

* The new `.<identifier>` notation is now also accepted where a function type is expected.
  ```lean
  example (xs : List Nat) : List Nat := .map .succ xs
  example (xs : List α) : Std.RBTree α ord := xs.foldl .insert ∅
  ```

* [Add code folding support to the language server](https://github.com/leanprover/lean4/pull/1014).

* Support notation `let <pattern> := <expr> | <else-case>` in `do` blocks.

* Remove support for "auto" `pure`. In the [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/for.2C.20unexpected.20need.20for.20type.20ascription/near/269083574), the consensus seemed to be that "auto" `pure` is more confusing than it's worth.

* Remove restriction in `congr` theorems that all function arguments on the left-hand-side must be free variables. For example, the following theorem is now a valid `congr` theorem.
  ```lean
  @[congr]
  theorem dep_congr [DecidableEq ι] {p : ι → Set α} [∀ i, Inhabited (p i)] :
                    ∀ {i j} (h : i = j) (x : p i) (y : α) (hx : x = y), Pi.single (f := (p ·)) i x = Pi.single (f := (p ·)) j ⟨y, hx ▸ h ▸ x.2⟩ :=
  ```

* [Partially applied congruence theorems.](https://github.com/leanprover/lean4/issues/988)

* Improve elaboration postponement heuristic when expected type is a metavariable. Lean now reduces the expected type before performing the test.

* [Remove deprecated leanpkg](https://github.com/leanprover/lean4/pull/985) in favor of [Lake](https://github.com/leanprover/lake) now bundled with Lean.

* Various improvements to go-to-definition & find-all-references accuracy.

* Auto generated congruence lemmas with support for casts on proofs and `Decidable` instances (see [wishlist](https://github.com/leanprover/lean4/issues/988)).

* Rename option `autoBoundImplicitLocal` => `autoImplicit`.

* [Relax auto-implicit restrictions](https://github.com/leanprover/lean4/pull/1011). The command `set_option relaxedAutoImplicit false` disables the relaxations.

* `contradiction` tactic now closes the goal if there is a `False.elim` application in the target.

* Renamed tatic `byCases` => `by_cases` (motivation: enforcing naming convention).

* Local instances occurring in patterns are now considered by the type class resolution procedure. Example:
  ```lean
  def concat : List ((α : Type) × ToString α × α) → String
    | [] =>“”
    | ⟨_, _, a⟩ :: as => toString a ++ concat as
  ```

* Notation for providing the motive for `match` expressions has changed.
  before:
  ```lean
  匹配 x, rfl : (y : Nat) → x = y → Nat 与
  | 0，h => ...
  | x+1，h => ...
  ```
  now:
  ```lean
  匹配 (动机 := (y : Nat) → x = y → Nat) x, rfl 与
  | 0，h => ...
  | x+1，h => ...
  ```
  With this change, the notation for giving names to equality proofs in `match`-expressions is not whitespace sensitive anymore. That is,
  we can now write
  ```lean
  匹配 h : sort.swap a b with
  | (r₁, r2) => ... -- `h : sort.swap a b = (r₁, r₂)`
  ```

* `(generalizing := true)` is the default behavior for `match` expressions even if the expected type is not a proposition. In the following example, we used to have to include `(generalizing := true)` manually.
  ```lean
  inductive Fam : Type → Type 1 where
    |任意：Fam α
    | nat : Nat → Fam Nat

  example (a : α) (x : Fam α) : α :=
    将 x 与
    | Fam.any => a
    | Fam.nat n => n
  ```

* We now use `PSum` (instead of `Sum`) when compiling mutually recursive definitions using well-founded recursion.

* Better support for parametric well-founded relations. See [issue #1017](https://github.com/leanprover/lean4/issues/1017). This change affects the low-level `termination_by'` hint because the fixed prefix of the function parameters in not "packed" anymore when constructing the well-founded relation type. For example, in the following definition, `as` is part of the fixed prefix, and is not packed anymore. In previous versions, the `termination_by'` term would be written as `measure fun ⟨as, i, _⟩ => as.size - i`
  ```lean
  def sum (as : Array Nat) (i : Nat) (s : Nat) : Nat :=
    如果 h : i < as.size 那么
      求和为 (i+1) (s + as.get ⟨i, h⟩)
    否则
      s
  Termination_by' 测量 fun ⟨i, _⟩ => as.size - i
  ```

* Add `while <cond> do <do-block>`, `repeat <do-block>`, and `repeat <do-block> until <cond>` macros for `do`-block. These macros are based on `partial` definitions, and consequently are useful only for writing programs we don't want to prove anything about.

* Add `arith` option to `Simp.Config`, the macro `simp_arith` expands to `simp (config := { arith := true })`. Only `Nat` and linear arithmetic is currently supported. Example:
  ```lean
  example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
    简单的阿里斯
  ```

* Add `fail <string>?` tactic that always fail.

* Add support for acyclicity at dependent elimination. See [issue #1022](https://github.com/leanprover/lean4/issues/1022).

* Add `trace <string>` tactic for debugging purposes.

* Add nontrivial `SizeOf` instance for types `Unit → α`, and add support for them in the auto-generated `SizeOf` instances for user-defined inductive types. For example, given the inductive datatype
  ```lean
  inductive LazyList (α : Type u) where
    | nil : LazyList α
    | cons (hd : α) (tl : LazyList α) : LazyList α
    |延迟 (t : Thunk (LazyList α)) : LazyList α
  ```
  we now have `sizeOf (LazyList.delayed t) = 1 + sizeOf t` instead of `sizeOf (LazyList.delayed t) = 2`.

* Add support for guessing (very) simple well-founded relations when proving termination. For example, the following function does not require a `termination_by` annotation anymore.
  ```lean
  def Array.insertAtAux (i : Nat) (as : Array α) (j : Nat) : Array α :=
    如果 h : i < j 那么
      让 as := as.swap！ (j-1)j；
      insertAtAux i as (j-1)
    否则
      作为
  ```

* Add support for `for h : x in xs do ...` notation where `h : x ∈ xs`. This is mainly useful for showing termination.

* Auto implicit behavior changed for inductive families. An auto implicit argument occurring in inductive family index is also treated as an index (IF it is not fixed, see next item). For example
  ```lean
  inductive HasType : Index n → Vector Ty n → Ty → Type where
  ```
  is now interpreted as
  ```lean
  inductive HasType : {n : Nat} → Index n → Vector Ty n → Ty → Type where
  ```

* To make the previous feature more convenient to use, we promote a fixed prefix of inductive family indices to parameters. For example, the following declaration is now accepted by Lean
  ```lean
  inductive Lst : Type u → Type u
    |无：Lst α
    |缺点：α → Lst α → Lst α
  ```
  and `α` in `Lst α` is a parameter. The actual number of parameters can be inspected using the command `#print Lst`. This feature also makes sure we still accept the declaration
  ```lean
  inductive Sublist : List α → List α → Prop
    | slnil : 子列表 [] []
    | cons l₁ l2 a : 子列表 l₁ l2 → 子列表 l₁ (a :: l2)
    | cons2 l₁ l2 a : 子列表 l₁ l2 → 子列表 (a :: l₁) (a :: l2)
  ```

* Added auto implicit "chaining". Unassigned metavariables occurring in the auto implicit types now become new auto implicit locals. Consider the following example:
  ```lean
  inductive HasType : Fin n → Vector Ty n → Ty → Type where
    |停止：HasType 0 (ty :: ctx) ty
    | pop : HasType k ctx ty → HasType k.succ (u :: ctx) ty
  ```
  `ctx` is an auto implicit local in the two constructors, and it has type `ctx : Vector Ty ?m`. Without auto implicit "chaining", the metavariable `?m` will remain unassigned. The new feature creates yet another implicit local `n : Nat` and assigns `n` to `?m`. So, the declaration above is shorthand for
  ```lean
  inductive HasType : {n : Nat} → Fin n → Vector Ty n → Ty → Type where
    |停止 : {ty : Ty} → {n : Nat} → {ctx : Vector Ty n} → HasType 0 (ty :: ctx) ty
    | pop : {n : Nat} → {k : Fin n} → {ctx : Vector Ty n} → {ty : Ty} → HasType k ctx ty → HasType k.succ (u :: ctx) ty
  ```

* Eliminate auxiliary type annotations (e.g, `autoParam` and `optParam`) from recursor minor premises and projection declarations. Consider the following example
  ```lean
  structure A :=
    x : 纳特
    h : x = 1 := 通过平凡

  example (a : A) : a.x = 1 := by
    有 aux := a.h
    -- `aux` 现在的类型为 `a.x = 1` 而不是 `autoParam (a.x = 1) auto✝`
    精确辅助

  example (a : A) : a.x = 1 := by
    案例 a 与
    | mk x h =>
      -- `h` 现在的类型为 `x = 1` 而不是 `autoParam (x = 1) auto✝`
      假设
  ```

* We now accept overloaded notation in patterns, but we require the set of pattern variables in each alternative to be the same. Example:
  ```lean
  inductive Vector (α : Type u) : Nat → Type u
    | nil : 向量 α 0
    |缺点 : α → 向量 α n → 向量 α (n+1)

  infix:67 " :: " => Vector.cons -- 重载 `::` 符号

  def head1 (x : List α) (h : x ≠ []) : α :=
    将 x 与
    | a :: as => a -- `::` 在这里是 `List.cons`

  def head2 (x : Vector α (n+1)) : α :=
    将 x 与
    | a :: as => a -- `::` 在这里是 `Vector.cons`
  ```

* New notation `.<identifier>` based on Swift. The namespace is inferred from the expected type. See [issue #944](https://github.com/leanprover/lean4/issues/944). Examples:
  ```lean
  def f (x : Nat) : Except String Nat :=
    如果 x > 0 则
      .好的x
    否则
      .错误“x为零”

  namespace Lean.Elab
  open Lsp

  def identOf : Info → Option (RefIdent × Bool)
    | .ofTermInfo ti => 将 ti.expr 与
      | .const n .. => 一些 (.const n, ti.isBinder)
      | .fvar id .. => 一些（.fvar id，ti.isBinder）
      | _ => 无
    | .ofFieldInfo fi => 一些 (.const fi.projName, false)
    | _ => 无

  def isImplicit (bi : BinderInfo) : Bool :=
    bi 匹配 .implicit

  end Lean.Elab
  ```
````
