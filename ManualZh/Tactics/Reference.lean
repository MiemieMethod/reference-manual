/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta
import Manual.Papers
import ManualZh.Tactics.Reference.Simp


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

set_option maxHeartbeats 250000

#doc (Manual) "策略参考" =>
%%%
tag := "tactic-ref"
%%%

# 古典逻辑
%%%
tag := "tactic-ref-classical"
%%%

:::tactic "classical"
:::


# 假设
%%%
tag := "tactic-ref-assumptions"
%%%

:::tactic Lean.Parser.Tactic.assumption
:::

:::tactic "apply_assumption"
:::

# 量词
%%%
tag := "tactic-ref-quantifiers"
%%%

:::tactic "exists"
:::

:::tactic "intro"
:::


:::tactic "intros"
:::

:::tactic "rintro"
:::


# 关系
%%%
tag := "tactic-ref-relations"
%%%

:::tactic "rfl"
:::

:::tactic "rfl'"
:::


:::tactic Lean.Parser.Tactic.applyRfl
:::

:::syntax attr (title := "Reflexive Relations")
{attr}`refl` 属性将引理标记为某些关系的自反性证明。
这些引理由 {tactic}`rfl`、{tactic}`rfl'` 和 {tactic}`apply_rfl`策略使用。

```grammar
refl
```
:::

:::tactic "symm"
:::

:::tactic "symm_saturate"
:::

:::syntax attr (title := "Symmetric Relations")
{attr}`symm` 属性将引理标记为关系对称的证明。
这些引理由 {tactic}`symm` 和 {tactic}`symm_saturate`策略使用。

```grammar
symm
```
:::

:::tactic "calc"
:::

{docstring Trans}

## 平等
%%%
tag := "tactic-ref-equality"
%%%

:::tactic "subst"
:::

:::tactic "subst_eqs"
:::

:::tactic "subst_vars"
:::

:::tactic "congr"
:::

:::tactic "eq_refl"
:::

:::tactic "ac_rfl"
:::

# 结合性和交换性
%%%
tag := "tactic-ref-associativity-commutativity"
%%%

:::tactic "ac_nf"
:::

:::tactic "ac_nf0"
:::


# 引理
%%%
tag := "tactic-ref-lemmas"
%%%

:::tactic "exact"
:::

:::tactic "apply"
:::

:::tactic "refine"
:::

:::tactic "refine'"
:::

:::tactic "solve_by_elim"
:::

:::tactic "apply_rules"
:::

:::tactic "as_aux_lemma"
:::


# 谬误
%%%
tag := "tactic-ref-false"
%%%

:::tactic "exfalso"
:::

:::tactic "contradiction"
:::

:::tactic "false_or_by_contra"
:::


# 目标管理
%%%
tag := "tactic-ref-goals"
%%%

:::tactic "suffices"
:::

:::tactic "change"
:::

:::tactic "generalize"
:::

:::tactic "specialize"
:::

:::tactic "obtain"
:::

:::tactic "show"
:::

:::tactic Lean.Parser.Tactic.showTerm
:::


# 演员管理
%%%
tag := "tactic-ref-casts"
%%%

本节中的策略可以更轻松地避免卡在 {deftech}_casts_ 上，这些函数将数据从一种类型强制转换为另一种类型，例如将自然数转换为相应的整数。
{citet castPaper}[] 对它们进行了更详细的描述。

:::tactic Lean.Parser.Tactic.tacticNorm_cast__
:::

:::tactic Lean.Parser.Tactic.pushCast
:::

:::tactic Lean.Parser.Tactic.tacticExact_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticApply_mod_cast_
:::

:::tactic Lean.Parser.Tactic.tacticRw_mod_cast___
:::

:::tactic Lean.Parser.Tactic.tacticAssumption_mod_cast_
:::

# 管理 `let` 表达式

:::tactic "extract_lets"
:::

:::tactic "lift_lets"
:::

:::tactic "let_to_have"
:::

:::tactic "clear_value"
:::


# 外延性
%%%
tag := "tactic-ref-ext"
%%%

:::tactic "ext"
:::

:::tactic Lean.Elab.Tactic.Ext.tacticExt1___
:::

:::tactic Lean.Elab.Tactic.Ext.applyExtTheorem
:::

:::tactic "funext"
:::

# SMT 启发的自动化
:::tactic "grind"
:::

:::tactic "grind?"
:::

:::tactic "lia"
:::

:::tactic "grobner"
:::


{include 0 ManualZh.Tactics.Reference.Simp}

# 重写
%%%
tag := "tactic-ref-rw"
%%%

:::tactic "rw"
:::

:::tactic "rewrite"
:::

:::tactic "erw"
:::

:::tactic Lean.Parser.Tactic.tacticRwa__
:::

{docstring Lean.Meta.Rewrite.Config +allowMissing}

{docstring Lean.Meta.Occurrences}

{docstring Lean.Meta.TransparencyMode +allowMissing}

{docstring Lean.Meta.Rewrite.NewGoals +allowMissing}


:::tactic "unfold"

由 {name}`Lean.Elab.Tactic.evalUnfold` 实现。
:::

:::tactic "replace"
:::

:::tactic "delta"
:::


# 归纳类型
%%%
tag := "tactic-ref-inductive"
%%%

## 介绍
%%%
tag := "tactic-ref-inductive-intro"
%%%

:::tactic "constructor"
:::


:::tactic "injection"
:::

:::tactic "injections"
:::

:::tactic "left"
:::

:::tactic "right"
:::

## 消除
%%%
tag := "tactic-ref-inductive-elim"
%%%

消除策略使用 {ref "recursors"}[recursors] 和自动派生的 {ref "recursor-elaboration-helpers"}[`casesOn` helper] 来实现归纳和案例分割。
由这些策略产生的 {tech}[子目标] 由消除器的小前提类型确定，并且使用具有 {keyword}`using` 选项的不同消除器会产生不同的子目标。

:::::leanSection
```lean -show
variable {n : Nat}
```
::::example "Choosing Eliminators"

:::tacticExample
```setup
intro n i
```
{goal -show}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre -show
n : Nat
i : Fin (n + 1)
⊢ 0 + i = i
```

当尝试证明 {lean}`∀(i : Fin (n + 1)), 0 + i = i` 时，引入假设后，策略{tacticStep}`induction i` 结果为：

```post
case mk
n val✝ : Nat
isLt✝ : val✝ < n + 1
⊢ 0 + ⟨val✝, isLt✝⟩ = ⟨val✝, isLt✝⟩
```

这是因为 {name}`Fin` 是具有单个非递归构造函数的 {tech}[结构]。
它的递归器对于这个构造函数有一个小前提：
```signature
Fin.rec.{u} {n : Nat} {motive : Fin n → Sort u}
  (mk : (val : Nat) →
    (isLt : val < n) →
    motive ⟨val, isLt⟩)
  (t : Fin n) : motive t
```
:::
:::tacticExample
```setup
intro n i
```
{goal -show}`∀(n : Nat) (i : Fin (n + 1)), 0 + i = i`

```pre -show
n : Nat
i : Fin (n + 1)
⊢ 0 + i = i
```

使用策略{tacticStep}`induction i using Fin.induction` 会导致：

```post
case zero
n : Nat
⊢ 0 + 0 = 0

case succ
n : Nat
i✝ : Fin n
a✝ : 0 + i✝.castSucc = i✝.castSucc
⊢ 0 + i✝.succ = i✝.succ
```

{name}`Fin.induction` 是一种替代消除器，它在底层 {name}`Nat` 上实现归纳：
```signature
Fin.induction.{u} {n : Nat}
  {motive : Fin (n + 1) → Sort u}
  (zero : motive 0)
  (succ : (i : Fin n) →
    motive i.castSucc →
    motive i.succ)
  (i : Fin (n + 1)) : motive i
```
:::

::::
:::::

{deftech}[自定义消除器] 可以使用 {attr}`induction_eliminator` 和 {attr}`cases_eliminator` 属性进行注册。
消除器是为其显式目标（即消除器函数的显式参数而不是隐式参数）注册的，并且当 {tactic}`induction` 或 {tactic}`cases` 用于这些类型的目标时将应用消除器。
当存在时，自定义消除器优先于递归器。
将 {option}`tactic.customEliminators` 设置为 {lean}`false` 将禁用自定义消除器。

:::syntax attr (title := "Custom Eliminators")
{attr}`induction_eliminator` 属性注册一个消除器以供 {tactic}`induction`策略使用。
```grammar
induction_eliminator
```

{attr}`cases_eliminator` 属性注册一个消除器以供 {tactic}`cases`策略使用。
```grammar
cases_eliminator
```
:::

:::tactic "cases"
:::

:::tactic "rcases"
:::

:::tactic "fun_cases"
:::

:::tactic "induction"
:::

:::tactic "fun_induction"
:::


:::tactic "nofun"
:::

:::tactic "nomatch"
:::


# 图书馆检索
%%%
tag := "tactic-ref-search"
%%%

库搜索策略旨在用于交互式使用。
运行时，它们会在 Lean 库中搜索引理或重写可能适用于当前情况的规则，并建议新的策略。
这些策略不应留在校样中；相反，他们的建议应该被采纳。

:::tactic "exact?"
:::

:::tactic "apply?"
:::




:::tacticExample
{goal -show}`∀ (i j k : Nat), i < j → j < k → i < k`
```setup
intro i j k h1 h2
```
在这个证明状态下：
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```

调用 {tacticStep}`apply?` 表明：

```tacticOutput
Try this:
  [apply] exact Nat.lt_trans h1 h2
```

```post -show

```
:::


:::tactic "rw?"
:::

# 案例分析
%%%
tag := "tactic-ref-cases"
%%%


:::tactic "split"
:::

:::tactic "by_cases"
:::

# 决策程序
%%%
tag := "tactic-ref-decision"
%%%


:::tactic Lean.Parser.Tactic.decide (show := "decide")
:::

:::tactic Lean.Parser.Tactic.nativeDecide (show := "native_decide")
:::

:::tactic "omega"
:::

:::tactic "bv_omega"
:::


## SAT 求解器集成
%%%
tag := "tactic-ref-sat"
%%%

:::tactic "bv_decide"
:::

:::tactic "bv_normalize"
:::

:::tactic "bv_check"
:::

:::tactic Lean.Parser.Tactic.bvTraceMacro
:::

# 按价值评估
%%%
tag := "tactic-ref-cbv"
%%%

{tactic}`cbv`策略模拟按值调用评估以减少术语。
在 {deftech}[按值调用计算] 中，函数的参数在函数调用减少之前会减少为值。
粗略地说，_values_ 要么是函数，要么是构造函数对值的应用；函数体不需要是一个值，函数本身也可以算作一个值。
此评估策略与 Lean 编译器生成的代码的执行顺序相匹配，这使其非常适合为在运行时良好运行而编写的代码。

{tactic}`cbv` 使用 {tech}[方程引理] 展开定义，并应用自动证明 {tech}[匹配函数] 的类似定理，在每一步生成 命题等价 证明。
因为展开是命题性的而不是定义性的，所以 {tactic}`cbv` 可以减少通过 {ref "well-founded-recursion"}[良基递归] 或 {ref "partial-fixpoint"}[部分固定点] 定义的函数。
一般来说，这些函数在定义上并不等于它们的展开，因此内核的定义缩减不会减少它们的递归调用。

{tactic}`cbv` 生成的证明仅使用三个标准公理（{name}`propext`、{name}`Quot.sound` 和 {name}`Classical.choice`）。
特别是，与 {tactic}`native_decide` 不同，它们不需要信任代码生成器的正确性。

由于 {tactic}`cbv` 通过 {name}`congrArg` 和 {name}`congrFun` 重写子项，因此它无法重写出现在从属位置的子项。
重写从属函数的参数将改变后续参数的类型，并且即使具有异构相等性，也没有适用于任意从属函数的合适的同余引理。

:::paragraph
在减少持续应用时，{tactic}`cbv` 按顺序尝试以下策略：

 1. 自定义{attr}`cbv_eval`重写规则
 2. {tech}[方程引理]（例如，`foo.eq_1`、`foo.eq_2`）
 3. 展开方程
 4. 内核匹配器还原

除非提供匹配的 {attr}`cbv_eval` 重写规则，否则永远不会展开标有 {attr}`cbv_opaque` 的声明。
:::

:::syntax tactic (title := "Call-by-Value Evaluation")
```grammar
cbv $[at $[$h]*]?
```
:::

:::tactic Lean.Parser.Tactic.cbv (show := "cbv")
:::

```lean -show
-- The `cbv` tactic is presently experimental, and a warning is issued when it is used.
-- This option disables the warning:
set_option cbv.warning false
```

:::example "Reducing Well-Founded Recursive Functions"
函数 {lean}`countdown` 是使用良基递归定义的，因此它在定义上不等于其展开。
普通{tactic}`rfl`无法关闭球门：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean +error (name := countdownRfl)
example : countdown 3 = [3, 2, 1, 0] := by rfl
```
```leanOutput countdownRfl
Tactic `rfl` failed: The left-hand side
  countdown 3
is not definitionally equal to the right-hand side
  [3, 2, 1, 0]

⊢ countdown 3 = [3, 2, 1, 0]
```
{tactic}`cbv`策略可以通过命题重写来约简 {lean}`countdown 3`，然后通过 {tactic}`rfl` 关闭方程目标：
```lean
example : countdown 3 = [3, 2, 1, 0] := by
  cbv
```
:::

:::example "Reducing Hypotheses"
{tactic}`cbv`策略支持标准 `at` 位置语法。
与 `at h` 一起使用时，它会减少假设 `h` 的类型。
当与 `at *` 一起使用时，它减少了所有非依赖命题
假设和目标。
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean
example (x : List Nat) (h : x = countdown 2) :
    x = [2, 1, 0] := by
  cbv at h
  exact h
```
:::

:::example "`cbv` as a Non-Finishing Tactic"
与 {tactic}`decide` 不同，{tactic}`cbv` 不是终端策略。
它尽可能地简化目标，但可能留下需要进一步推理的目标。
此处，{tactic}`cbv` 减少了对 {lean}`countdown` 的调用，但保留了成员资格目标：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean +error (name := cbvNonFinishing)
example : 1 ∈ countdown 2 := by
  cbv
```
```leanOutput cbvNonFinishing
unsolved goals
⊢ List.Mem 1 [2, 1, 0]
```
:::

:::example "Dependent Positions"
```imports -show
import Std.Data.DTreeMap
import Std.Data.TreeMap
```

函数 {name}`wfLength` 是 {name}`List.length` 的一个版本，它是通过 {tech}[良基递归] 而不是 {ref "structural-recursion"}[结构递归] 定义的。
结果是 {tech}[不可约]：
```lean
def wfLength : List Nat → Nat
  | [] => 0
  | _ :: xs => wfLength xs + 1
termination_by xs => xs
```
```lean -show
set_option cbv.warning false
```

在非依赖 {name}`Std.TreeMap` 中，{tactic}`cbv` 可以减少计算密钥 {lean}`wfLength [1, 2]`：
```lean
def myTreeMap : Std.TreeMap Nat Nat :=
  .empty |>.insert (wfLength [1, 2]) 42

example : myTreeMap.toList = [⟨2, 42⟩] := by
  cbv
```
但是，考虑一个依赖树映射 {lean}`FinMap`，它将每个键 `n` 映射到 `Fin (n + 1)` 类型的值：
```lean
abbrev FinMap :=
  Std.DTreeMap Nat (fun n => Fin (n + 1))
```
这里 {tactic}`cbv` 陷入困境，因为值类型 `Fin (n + 1)` 取决于键：
```lean +error (name := depPosition)
example :
    let m : FinMap :=
      .empty |>.insert (wfLength [1, 2])
        ⟨0, by decide_cbv⟩
    m.toList = [⟨2, ⟨0, by omega⟩⟩] := by
  cbv
```
```leanOutput depPosition
unsolved goals
⊢ [⟨wfLength [1, 2], ⟨0, ⋯⟩⟩] = [⟨2, ⟨0, ⋯⟩⟩]
```
:::

## {tactic}`decide_cbv`

:::tactic Lean.Parser.Tactic.decide_cbv (show := "decide_cbv")
:::

:::example "`decide_cbv`"
{tactic}`decide_cbv`策略通过 {tech}[按值调用评估] 减少 {name}`Decidable` 实例来关闭可判定命题的目标：
```lean
example : 2 + 3 = 5 ∧ 10 < 20 := by
  decide_cbv
```
与 {tactic}`native_decide` 不同，{tactic}`decide_cbv` 不需要信任代码生成器。
与使用定义约简的 {tactic}`decide` 不同，{tactic}`decide_cbv` 可以处理由 {ref "well-founded-recursion"}[良基递归] 定义的函数：
```lean
def isAllPositive : List Int → Bool
  | [] => true
  | x :: xs => x > 0 && isAllPositive xs
termination_by xs => xs

example : isAllPositive [1, 2, 3] = true := by
  decide_cbv
```
:::

::::example "Prime Power Testing with `decide_cbv`"
由于 {tactic}`decide_cbv` 使用命题展开，因此它可以评估涉及 {ref "well-founded-recursion"}[有充分依据的递归]函数的复杂决策过程。
此处，{lean}`Nat.minFac` 查找数字的最小除数，而助手 {lean}`minFacAux` 搜索最小奇数除数：
```lean
def minFacAux (n k : Nat) : Nat :=
  if h : n < k * k then n
  else
    if h' : k ∣ n then k
    else
      have : k ≤ n := by
        have := Nat.le_mul_self k; grind
      minFacAux n (k + 2)
termination_by n + 2 - k

def Nat.minFac (n : Nat) : Nat :=
  if 2 ∣ n then 2 else minFacAux n 3
```
:::leanSection
```lean -show
variable {b n : Nat}
```
{lean}`Nat.log b n` 通过重复平方计算 {lean}`n` 的底 {lean}`b` 对数的下限：
:::
```lean
def Nat.log (b n : Nat) : Nat :=
  if b ≤ 1 then 0 else (go b n).2 where
  go : Nat → Nat → Nat × Nat
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then
        (q, 2 * e)
      else
        (q / b, 2 * e + 1)
```
这里，即使存在自由变量 `k`，{tactic}`decide_cbv` 也可以减少决策过程的结果：
```lean
example : ¬∃ k,
    k ≤ Nat.log 2 15151515151515 ∧
    0 < k ∧
    15151515151515 =
      Nat.minFac 15151515151515 ^ k := by
  decide_cbv

```
::::

## 控制 {tactic}`cbv` 行为

:::syntax attr (title := "Custom `cbv` Rewrite Rules")
{attr}`cbv_eval` 属性将定理注册为 {tactic}`cbv` 在尝试 {tech}[方程引理] 之前应用的自定义重写规则。
该定理必须是无条件等式；一侧（通常是左侧）必须是常数的应用。

```grammar
cbv_eval
```

`←` 修饰符指示 {tactic}`cbv` 从右到左应用规则：
```grammar
cbv_eval ←
```
:::

:::example "`cbv_eval`"
自定义重写规则可用于控制 {tactic}`cbv` 如何评估特定函数。
例如，反转的简单定义 {lean}`slowReverse` 由于重复使用 {name}`List.append` 而具有二次复杂度。
通过 {lean}`fastReverse` 提供尾递归表征，{tactic}`cbv` 可以有效评估 {lean}`slowReverse`：
```lean
def slowReverse : List Nat → List Nat
  | [] => []
  | x :: xs => slowReverse xs ++ [x]

def fastReverse (xs : List Nat) : List Nat :=
  go [] xs
where
  go (acc : List Nat) : List Nat → List Nat
  | [] => acc
  | x :: xs => go (x :: acc) xs

theorem reverse_spec_aux (xs acc : List Nat) :
    fastReverse.go acc xs =
      slowReverse xs ++ acc := by
  fun_induction fastReverse.go
    <;> grind [slowReverse]

@[cbv_eval] theorem slowReverse_cbv
    (xs : List Nat) :
    slowReverse xs = fastReverse xs := by
  simp [fastReverse, reverse_spec_aux]
```
```lean
example : slowReverse [1, 2, 3, 4, 5] = [5, 4, 3, 2, 1] := by
  cbv
```
:::

:::syntax attr (title := "Opaque Declarations for `cbv`")
{attr}`cbv_opaque` 属性阻止 {tactic}`cbv` 使用其 {tech}[方程引理] 展开声明或展开定理。
但是，{attr}`cbv_eval` 重写规则始终优先于 {attr}`cbv_opaque`：如果声明存在匹配的 {attr}`cbv_eval` 规则，则即使声明标记为 {attr}`cbv_opaque`，也会应用该规则。
这允许用一组受控的评估规则替换默认的展开行为。

```grammar
cbv_opaque
```
:::

::::example "Opaque Definitions with `@[cbv_opaque]`"
将 {lean}`countdown` 标记为 {attr}`cbv_opaque` 会阻止 {tactic}`cbv` 展开它，因此之前由 {tactic}`cbv` 关闭的目标现在仍未解决：
```lean
def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n
termination_by n
```
```lean -show
set_option cbv.warning false
```
```lean
attribute [cbv_opaque] countdown
```
```lean +error (name := opaqueError)
example : countdown 3 = [3, 2, 1, 0] := by
  cbv
```
```leanOutput opaqueError
unsolved goals
⊢ countdown 3 = [3, 2, 1, 0]
```
::::

### 定制简化程序

:::paragraph
{deftech}[cbv 简化过程] ({tactic}`cbv` simproc) 是用户定义的元程序，{tactic}`cbv` 在与给定模式匹配的子表达式上调用它。
虽然 {attr}`cbv_eval` 规则仅限于静态相等，但 {tactic}`cbv` simprocs 可以执行任意计算来决定如何重写子表达式。
常见用例包括定义用于根据文字值或短路控制流评估函数的过程。

{tactic}`cbv` 使用的 simproc 具有 {name}`Lean.Meta.Sym.Simp.Simproc` 类型，该类型不同于 {tactic}`simp`策略使用的 {name}`Lean.Meta.Simp.Simproc` 类型。
这两个系统是独立的：注册 {tactic}`cbv` simproc 对 {tactic}`simp` 没有影响，反之亦然。
:::

:::syntax command (title := "Custom `cbv` Simplification Procedures")
```lean -show
open Lean Lean.Meta.Sym.Simp
```
主体的类型必须为 {name}`Simproc`（即 {lean}`Expr → SimpM Result`）。
该模式是一个有漏洞的表达式 (`_`)，用于确定哪些子表达式触发该过程。
展开可约简定义并对两侧应用 {tech (key := "β")}[β]-、{tech (key := "η-equivalence")}[η]- 和 {tech (key := "ζ")}[z]-约简后，模式在结构上与子表达式进行匹配。
匹配是模 α 等价（绑定变量名称被忽略），并且模式中的证明和实例参数被视为通配符。
可选的阶段说明符控制在规范化过程中何时触发该过程。
当未指定阶段时，默认为 `↑`（后）。

: `↓`（预）

   在 {tactic}`cbv` 减少每个子表达式之前触发它。争论仍然没有减少。使用此阶段覆盖 {tactic}`cbv` 的默认按值调用评估顺序。典型的用例是延迟计算参数或短路计算（如内置 {name}`ite` 和 {name}`Or` 过程所做的那样）。

: `cbv_eval`（评估）

  在参数已减少到值之后，但在函数展开之前触发。使用此阶段提供有效的地面评估程序。

: `↑`（后置，默认）

  {tactic}`cbv` 尝试标准简化（方程引理、展开、内核匹配）后触发。当应首先尝试标准还原时使用此阶段。

```grammar
cbv_simproc name (pattern) := body
```

可以在名称之前放置可选的阶段说明符：

```grammar
cbv_simproc ↓ name (pattern) := body
```

```grammar
cbv_simproc cbv_eval name (pattern) := body
```

`cbv_simproc_decl` 变体声明该过程而不激活它。
稍后可以使用 {attr}`cbv_simproc` 激活它。

```grammar
cbv_simproc_decl name (pattern) := body
```
:::

:::syntax attr (title := "Simplification Procedure Attribute for `cbv`")
{attr}`cbv_simproc` 属性激活先前声明的简化过程（使用 `cbv_simproc_decl` 定义）以供 {tactic}`cbv` 使用。
可选的阶段说明符控制在规范化过程中何时触发该过程。

```grammar
cbv_simproc
```

阶段说明符控制程序何时触发：

```grammar
cbv_simproc ↓
```

```grammar
cbv_simproc ↑
```

```grammar
cbv_simproc cbv_eval
```
:::


::::example "Declaring a `cbv_simproc`"

```imports -show
import Lean.Meta.Tactic.Cbv.CbvSimproc
```

通过提供 {name}`Lean.Meta.Sym.Simp.Simproc` 类型的模式和主体来声明简化过程。
该模式是一个有漏洞的表达式 (`_`)，用于确定哪些子表达式触发该过程。
此处，模式为 (`myConst _`)，它与 {name}`myConst` 的任何应用程序匹配。
过程 ({lean (type := "Simproc")}`fun _e => do return .rfl`) 忽略表达式，返回指示不执行重写的结果。

```lean
opaque myConst : Nat → Nat

open Lean Meta Sym.Simp in
cbv_simproc evalMyConst (myConst _) := fun _e => do
  -- A real simproc would inspect `e`, compute a result,
  -- and return `.step result proof`.
  return .rfl
```

{keywordOf Lean.Parser.«command_Cbv_simproc_decl_(_):=_»}`cbv_simproc_decl` 变体声明该过程而不激活它。
{attr}`cbv_simproc` 属性可用于稍后激活它，也可以选择在特定阶段激活它：

```lean
open Lean Meta Sym.Simp in
cbv_simproc_decl evalMyConst2 (myConst _) := fun _e =>
  return .rfl

attribute [cbv_simproc cbv_eval] evalMyConst2
```

::::

::::example "Lazy evaluation of a head of the list"
```imports -show
import Lean.Meta.Sym.Simp
```
```lean -show
open Lean Meta Sym.Simp
variable (α : Type)
variable (a : α)
variable (as : List α)
```

这是预阶段简化过程的一个示例，它打破了传统的按值调用求值顺序以实现惰性。
`↓` 修饰符确保 {name}`evalListHead` 在计算 {name}`List.head?` 的参数之前触发。
它使用 {name}`List.head?_cons` 将 {lean}`List.head? (a :: as)` 重写为 {lean}`some a`，丢弃尾部 {lean}`as` 而不对其进行评估。
仅头部元素 {lean}`a` 随后被 {tactic}`cbv` 减少。

```lean
cbv_simproc ↓ evalListHead (List.head? _) := fun e => do
  let_expr List.head? α listExpr := e | return .rfl
  let_expr List.cons _ a as := listExpr | return .rfl
  let Level.succ u ← Sym.getLevel α | return .rfl
  let result ← Sym.share <| mkApp2 (mkConst ``Option.some [u]) α a
  let proof := mkApp3 (mkConst ``List.head?_cons [u]) α a as
  return .step result proof

theorem cbv_simproc_test : [5 + 5,6].head? = .some 10 := by cbv
```
检查证明项确认简化过程被触发：{name}`List.head?_cons` 直接出现在证明中，表明 {tactic}`cbv` 使用了 simproc 的重写，而不是通过展开其定义来减少 {name}`List.head?`。

```lean -show (name := cbvSimprocTest)
#print cbv_simproc_test
```
```leanOutput cbvSimprocTest
theorem cbv_simproc_test : [5 + 5, 6].head? = some 10 :=
of_eq_true
  (Eq.trans (congrFun' (congrArg Eq (Eq.trans List.head?_cons (congrArg some (Eq.refl 10)))) (some 10))
    (eq_self (some 10)))
```

::::

:::paragraph
Lean 包括 {tactic}`cbv` 的许多内置简化程序。
这些处理控制流（`ite`、`dite`、`cond`、`Decidable.decide`、`Decidable.rec`）、逻辑连接词（`Or`、`And`）和数据结构操作（数组索引、字符串操作）。
控制流程序使用 `↓`（预）阶段来启用短路评估，而阵列和串程序使用 `cbv_eval` 阶段来直接减少接地应用。
:::

## 选项

{optionDocs cbv.maxSteps}

{optionDocs cbv.warning}

# 控制减少
%%%
tag := "tactic-reducibility"
%%%

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic "with_unfolding_all"
:::

:::tactic "with_unfolding_none"
:::


# 控制流程
%%%
tag := "tactic-ref-control"
%%%


:::tactic "skip"
:::


:::tactic Lean.Parser.Tactic.guardHyp
:::

:::tactic Lean.Parser.Tactic.guardTarget
:::

:::tactic Lean.Parser.Tactic.guardExpr
:::

:::tactic "done"
:::

:::tactic "sleep"
:::

:::tactic "stop"
:::


# 术语精化后端
%%%
tag := "tactic-ref-term-helpers"
%%%


这些策略在精化条款期间使用，以满足产生的义务。

:::tactic tacticDecreasing_with_
:::

:::tactic "get_elem_tactic"
:::

:::tactic "get_elem_tactic_trivial"
:::


# 调试实用程序
%%%
tag := "tactic-ref-debug"
%%%


:::tactic "sorry"
:::

:::tactic "admit"
:::

:::tactic "dbg_trace"
:::

:::tactic Lean.Parser.Tactic.traceState
:::

:::tactic Lean.Parser.Tactic.traceMessage
:::

# 建议

:::tactic "∎"
:::

:::tactic "suggestions"
:::


# 其他
%%%
tag := "tactic-ref-other"
%%%

:::tactic "trivial"
:::

:::tactic "solve"
:::

:::tactic "and_intros"
:::

:::tactic "infer_instance"
:::

:::tactic "expose_names"
:::

:::tactic Lean.Parser.Tactic.tacticUnhygienic_
:::

:::tactic Lean.Parser.Tactic.runTac
:::

# 验证条件生成
%%%
tag := "tactic-ref-mvcgen"
%%%

:::tactic "mvcgen"
:::

## 策略用于 `Std.Do.SPred` 中的状态目标
%%%
tag := "tactic-ref-spred"
%%%

### 启动和停止校样模式

:::tactic "mstart"
:::

:::tactic "mstop"
:::

:::tactic "mleave"
:::

### 证明国家目标

:::tactic "mspec"
:::

:::tactic Lean.Parser.Tactic.mintroMacro
:::

:::tactic "mexact"
:::

:::tactic "massumption"
:::

:::tactic "mrefine"
:::

:::tactic "mconstructor"
:::

:::tactic "mleft"
:::

:::tactic "mright"
:::

:::tactic "mexists"
:::

:::tactic "mpure_intro"
:::

:::tactic "mexfalso"
:::

### 操纵状态假设

:::tactic "mclear"
:::

:::tactic "mdup"
:::

:::tactic "mhave"
:::

:::tactic "mreplace"
:::

:::tactic "mspecialize"
:::

:::tactic "mspecialize_pure"
:::

:::tactic "mcases"
:::

:::tactic "mrename_i"
:::

:::tactic "mpure"
:::

:::tactic "mframe"
:::
