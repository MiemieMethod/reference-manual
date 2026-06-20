/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sebastian Graf
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Std.Tactic.Do

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External (lit)

set_option pp.rawOnError true

set_option verso.docstring.allowMissing true

set_option linter.unusedVariables false

set_option linter.typography.quotes true
set_option linter.typography.dashes true

set_option mvcgen.warning false

open Manual (comment)

open Std.Do

#doc (Manual) "`mvcgen`策略" =>
%%%
tag := "mvcgen-tactic"
%%%

:::tutorials
 * {ref "mvcgen-tactic-tutorial" (remote := "tutorials")}[使用 `mvcgen` 验证命令式程序]
:::

{tactic}`mvcgen`策略实现_monadic 验证条件生成器_：
它将涉及使用 Lean 的命令式 {keywordOf Lean.Parser.Term.do}`do` 表示法编写的程序的目标分解为多个足以证明该目标的较小的 {tech (key := "verification conditions")}_验证条件_ ({deftech}[VCs])。
除了描述 {tactic}`mvcgen` 使用的参考之外，本章还包括可以独立于参考阅读的 {ref "mvcgen-tactic-tutorial" (remote := "tutorials")}[教程]。

为了使用 {tactic}`mvcgen`策略，必须导入 {module}`Std.Tactic.Do` 并且必须打开命名空间 {namespace}`Std.Do`。


# 概述
%%%
tag := "zh-vcgen-h001"
%%%



{tactic}`mvcgen` 的工作流程包括以下内容：

1. Monadic 程序根据 {tech (key := "predicate transformer semantics")}[谓词转换器语义] 重新解释。
   {name}`WP` 的实例决定了 monad 的解释。
   每个程序都被解释为从任意 {tech (key := "postconditions")}[后置条件] 到 {tech (key := "weakest precondition")}[最弱前置条件] 的映射，以确保后置条件。
   此步骤对于大多数用户来说是不可见的，但是想要使其 monad 能够与 {tactic}`mvcgen` 一起使用的库作者需要理解它。
2. 程序由较小的程序组成。
   {keywordOf Lean.Parser.Term.do}`do` 块中的每个语句都与谓词转换器关联，并且存在将这些语句与排序和控制流运算符组合的通用规则。
   带有前置条件和后置条件的语句称为 {tech (key := "Hoare triple")}_Hoare Triple_。
   在程序中，每个语句的后置条件应该足以证明下一个语句的前置条件，并且循环需要指定的 {deftech}_loop invariant_，这是一个在循环开始和每次迭代结束时必须为 true 的语句。
   指定的 {tech (key := "specification lemmas")}_specation lemmas_ 将函数与指定它们的 Hoare 三元组关联起来。
3. 将一元程序的最弱前提条件语义应用于所需的证明目标会导致证明目标必须成立的前提条件。
   任何缺失的步骤，例如循环不变量或证明语句的前提条件暗示其后置条件都会成为新的子目标。
   这些缺失的步骤称为 {deftech (key := "verification conditions")}_验证条件_。
   {tactic}`mvcgen`策略执行此转换，用其验证条件替换目标。
   在此转换期间，{tactic}`mvcgen` 使用规范引理来释放有关各个语句的证明。
4. 在提供循环不变量之后，许多验证条件实际上可以自动解除。
   那些不能用{ref "tactic-ref-spred"}[特殊证明模式]或普通Lean策略来证明的，取决于它们是用程序断言的逻辑表达还是用普通命题表达。


# 谓词变压器
%%%
tag := "zh-vcgen-h002"
%%%

{deftech (key := "predicate transformer semantics")}_谓词转换器语义_是将程序解释为从谓词到谓词的函数，而不是从值到值的函数。
{deftech}_postcondition_ 是在运行程序后成立的断言，而 {deftech}_precondition_ 是在运行程序之前必须成立的断言，以便保证后置条件成立。

{tactic}`mvcgen` 使用的谓词转换器语义将后置条件转换为 {deftech (key := "weakest preconditions")}_最弱的前提条件_，在此情况下程序将确保后置条件。
如果在所有状态下 $`P'` 足以证明 $`P`，但 $`P` 不足以证明 $`P'`，则断言 $`P` 弱于 $`P'`。
逻辑上等价的断言被认为是相等的。

所讨论的谓词是有状态的：它们可以提及程序的当前状态。
此外，后置条件可以将返回值和程序抛出的任何异常与最终状态相关联。
{name}`SPred` 是一种在单子状态上参数化的谓词，表示为构成状态的字段类型列表。
通常的逻辑连接词和量词是为 {name}`SPred` 定义的。
可与 {tactic}`mvcgen` 一起使用的每个 monad 都由 {name}`WP` 的实例分配一个状态类型，而 {name}`Assertion` 是该 monad 的对应断言类型，用于前提条件。
{name}`Assertion` 是 {name}`SPred` 的包装器：{name}`SPred` 由状态类型列表参数化，而 {name}`Assertion` 由信息更丰富的类型参数化，该类型将转换为 {name}`SPred` 的状态类型列表。
{name}`PostCond` 将有关返回值的 {name}`Assertion` 与有关潜在异常的断言配对；可用的异常也由 monad 的 {name}`WP` 实例指定。


## 状态谓词
%%%
tag := "zh-vcgen-h003"
%%%

一元程序的谓词变换器语义基于命题可能提及程序状态的逻辑。
这里，“状态”不仅指可变状态，还指只读值，例如通过 {name}`ReaderT` 提供的值。
不同的 monad 有不同的可用状态类型，但每个单独的状态总是有一个类型。
给定状态类型列表，{name}`SPred` 是这些状态的一种谓词。

{name}`SPred` 本质上并不与单子验证框架相关。
相关的 {name}`Assertion` 为通过其 {name}`WP` 实例的 {name}`PostShape` 输出参数表示的 monad 状态计算合适的 {name}`SPred`。

{docstring Std.Do.SPred}

::::leanSection
```lean -show
variable {P : Prop} {σ : List (Type u)}
```
不提及状态的普通命题可以通过添加一个简单的全称量化来用作有状态谓词。
这是用语法 {lean (type := "SPred σ")}`⌜P⌝` 编写的，它是 {name}`SPred.pure` 的语法糖。
:::syntax term (title := "Notation for `SPred`") (namespace := Std.Do)
```grammar
⌜$_:term⌝
```
{includeDocstring Std.Do.«term⌜_⌝»}
:::
::::

{docstring SPred.pure}

:::example "Stateful Predicates"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```
谓词 {name}`ItIsSecret` 表示 {name}`String` 类型的状态是 {lean}`"secret"`：
```lean
def ItIsSecret : SPred [String] := fun s => ⌜s = "secret"⌝
```
:::

### 蕴涵
%%%
tag := "zh-vcgen-h004"
%%%

有状态谓词通过_entailment_相关。
有状态谓词的蕴含被定义为全称量化蕴涵：如果 $`P` 和 $`Q` 是状态 $`\sigma` 上的谓词，则当 $`∀ s : \sigma, P(s) → Q(s)` 时，$`P` 蕴含 $`Q`（写作 $`P \vdash_s Q`）。

{docstring Std.Do.SPred.entails}

{docstring Std.Do.SPred.bientails}

:::syntax term (title := "Notation for `SPred`") (namespace := Std.Do)
```grammar
$_:term ⊢ₛ $_:term
```
{includeDocstring Std.Do.«term_⊢ₛ_»}

```grammar
⊢ₛ $_:term
```
{includeDocstring Std.Do.«term⊢ₛ_»}

```grammar
$_:term ⊣⊢ₛ $_:term
```

{includeDocstring Std.Do.«term_⊣⊢ₛ_»}
:::

:::leanSection
```lean -show
variable {σ : List (Type u)} {P Q : SPred σ}
```
有状态谓词的逻辑包括蕴涵连接词。
蕴涵和蕴涵之间的区别在于蕴涵是 Lean 逻辑中的语句，而蕴涵是状态逻辑的内部。
给定状态 {lean}`σ` 的状态谓词 {lean}`P` 和 {lean}`Q`，{lean (type := "Prop")}`P ⊢ₛ Q` 是 {lean}`Prop`，而 {lean (type := "SPred σ")}`spred(P → Q)` 是 {lean}`SPred σ`。
:::

### 符号
%%%
tag := "zh-vcgen-h005"
%%%

有状态谓词的语法与普通 Lean 术语的语法重叠。
特别是，有状态谓词使用逻辑连接词和量词的常用语法。
与有状态谓词相关的语法在上下文中自动启用，例如明确意图的前置条件和后置条件；其他上下文必须显式选择使用 {keywordOf Std.Do.«termSpred(_)»}`spred` 的语法。
可以使用 {keywordOf Std.Do.«termTerm(_)»}`term` 运算符恢复这些运算符的通常含义。

:::syntax term (title := "Predicate Terms") (namespace := Std.Do)
{keywordOf Std.Do.«termSpred(_)»}`spred` 表示逻辑连接词和量词应被理解为与状态谓词相关的连接词和量词，而 {keywordOf Std.Do.«termTerm(_)»}`term` 表示它们应具有通常的含义。
```grammar
spred($t)
```
```grammar
term($t)
```
:::

### 连接词和量词
%%%
tag := "zh-vcgen-h006"
%%%

:::syntax term (title := "Predicate Connectives") (namespace := Std.Do)
```grammar
spred($_ ∧ $_)
```
{name}`SPred.and` 的语法糖。

```grammar
spred($_ ∨ $_)
```
{name}`SPred.or` 的语法糖。

```grammar
spred(¬ $_)
```
{name}`SPred.not` 的语法糖。

```grammar
spred($_ → $_)
```
{name}`SPred.imp` 的语法糖。

```grammar
spred($_ ↔ $_)
```
{name}`SPred.iff` 的语法糖。
:::


{docstring SPred.and}

{docstring SPred.conjunction}

{docstring SPred.or}

{docstring SPred.not}

{docstring SPred.imp}

{docstring SPred.iff}

:::syntax term (title := "Predicate Quantifiers") (namespace := Std.Do)
```grammar
spred(∀ $x:ident, $_)
```
```grammar
spred(∀ $x:ident : $ty,  $_)
```
```grammar
spred(∀ ($x:ident $_* : $ty),  $_)
```
```grammar
spred(∀ _, $_)
```
```grammar
spred(∀ _ : $ty,  $_)
```
```grammar
spred(∀ (_ $_* : $ty),  $_)
```
全称量化的每种形式都是在以量化变量作为参数的函数上调用 {name}`SPred.forall` 的语法糖。

```grammar
spred(∃ $x:ident, $_)
```
```grammar
spred(∃ $x:ident : $ty,  $_)
```
```grammar
spred(∃ ($x:ident $_* : $ty),  $_)
```
```grammar
spred(∃ _, $_)
```
```grammar
spred(∃ _ : $ty,  $_)
```
```grammar
spred(∃ (_ $_* : $ty),  $_)
```
存在量化的每种形式都是在以量化变量作为参数的函数上调用 {name}`SPred.exists` 的语法糖。
:::

{docstring SPred.forall}

{docstring SPred.exists}

### 有状态的值
%%%
tag := "zh-vcgen-h007"
%%%

正如 {name}`SPred` 表示状态上的谓词一样，{name}`SVal` 表示从状态派生的值。

{docstring SVal}

{docstring SVal.getThe}

{docstring SVal.StateTuple}

{docstring SVal.curry}

{docstring SVal.uncurry}


## 断言
%%%
tag := "zh-vcgen-h008"
%%%

关于单子程序的断言语言由 {deftech}_postcondition shape_ 参数化，它描述了给定单子中计算的输入和输出。
前置条件可能会提到 monad 状态的初始值，而后置条件可能会提到返回值、monad 状态的最终值，并且还必须考虑可能引发的任何异常。
给定 monad 的后置条件形状决定了 monad 中的状态和异常。
{name}`PostShape.pure` 描述一个单子，其中断言可能不提及任何状态，{name}`PostShape.arg` 描述状态值，{name}`PostShape.except` 描述可能的异常。
因为这些构造函数可以不断添加，所以可以根据底层转换后的单子的后置条件形状来定义单子变换器的后置条件形状。
在幕后，通过将后置条件形状转换为状态类型列表并丢弃异常，将 {name}`Assertion` 转换为适当的 {name}`SPred`。

{docstring PostShape}

{docstring PostShape.args}

{docstring Assertion}

{docstring PostCond}

:::syntax term (title := "Postconditions")
```grammar
⇓ $_* => $_
```
产品构造函数的嵌套序列的语法糖，以 {lean}`()` 终止，其中第一个元素是关于非异常返回值的断言，其余元素是关于后置条件的异常情况的断言。
:::


{docstring ExceptConds}

:::leanSection
```lean -show
universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}} [WP m ps] {P : Assertion ps} {α  : Type u}  {prog : m α} {Q' : α → Assertion ps}
```
可能引发异常的程序的后置条件有两种。 {deftech (key := "total correctness interpretation")}_总正确性解释_ {lean}`⦃P⦄ prog ⦃⇓ r => Q' r⦄` 断言，如果 {lean}`P` 成立，则 {lean}`prog` 终止_并且_ {lean}`Q'` 对于结果成立。 {deftech (key := "partial correctness interpretation")}_部分正确性解释_ {lean}`⦃P⦄ prog ⦃⇓? r => Q' r⦄` 断言，给定 {lean}`P` 成立，并且_if_ {lean}`prog` 终止_then_ {lean}`Q'` 对于结果成立。
:::


:::syntax term (title := "Exception-Free Postconditions")
```grammar
⇓ $_* => $_
```
{includeDocstring PostCond.noThrow}
:::

{docstring PostCond.noThrow}

:::syntax term (title := "Partial Postconditions")
```grammar
⇓? $_* => $_
```
{includeDocstring PostCond.mayThrow}
:::

{docstring PostCond.mayThrow}

:::syntax term (title := "Postcondition Entailment")
```grammar
$_ ⊢ₚ $_
```
{name}`PostCond.entails` 的语法糖
:::

{docstring PostCond.entails}


:::syntax term (title := "Postcondition Conjunction")
```grammar
$_ ∧ₚ $_
```
{name}`PostCond.and` 的语法糖
:::

{docstring PostCond.and}

:::syntax term (title := "Postcondition Implication")
```grammar
$_ →ₚ $_
```
{name}`PostCond.imp` 的语法糖
:::

{docstring PostCond.imp}


## 谓词变压器
%%%
tag := "zh-vcgen-h009"
%%%

谓词变换器是从某些后置条件状态的后置条件到该状态的断言的函数。
该函数必须是 {deftech}_conjunctive_，这意味着它必须分布在 {name}`PostCond.and` 上。

{docstring PredTrans}

{docstring PredTrans.Conjunctive}

{docstring PredTrans.Monotonic}

:::leanSection
```lean -show
variable {σ : List (Type u)} {ps : PostShape} {x y : PredTrans ps α} {Q : Assertion ps}
```
{inst}`LE PredTrans` 实例是根据其逻辑强度来定义的；如果应用一个变压器的结果总是包含应用另一个变压器的结果，那么一个变压器就比另一个强。
换句话说，先是 {lean}`∀ Q, y Q ⊢ₛ x Q`，然后是 {lean}`x ≤ y`。
这意味着较强的谓词转换器被认为比较弱的谓词转换器更大。
:::

谓词转换器形成一个 monad。
{name}`pure` 运算符是身份转换器；它只是用它的参数实例化后置条件。
{name}`bind` 运算符组成谓词转换器。

{docstring PredTrans.pure}

{docstring PredTrans.bind}

辅助运算符 {name}`PredTrans.pushArg`、{name}`PredTrans.pushExcept` 和 {name}`PredTrans.pushOption` 通过添加标准副作用来修改谓词转换器。
它们用于实现 {name}`StateT`、{name}`ExceptT` 和 {name}`OptionT` 等变压器的 {name}`WP` 实例；它们还可以用于实现可以根据其中之一来考虑的 monad。
例如，{name}`PredTrans.pushArg` 通常用于状态 monad，但也可用于实现读取器 monad 的实例，将读取器的值视为只读状态。

{docstring PredTrans.pushArg}

{docstring PredTrans.pushExcept}

{docstring PredTrans.pushOption}

### 最弱的先决条件
%%%
tag := "zh-vcgen-h010"
%%%

monad 的 {tech}[weakest precondition] 语义由 {name}`WP` 类型类提供。
{name}`WP` 的实例确定 monad 的后置条件形状，并提供将 monad 的操作解释为其后置条件形状中的谓词变换器的逻辑规则。

{docstring WP}

:::syntax term (title := "Weakest Preconditions")
```grammar
wp⟦$_ $[: $_]?⟧
```
{includeDocstring Std.Do.«termWp⟦_:_⟧»}
:::

### 最弱先决条件单子态射
%%%
tag := "zh-vcgen-h011"
%%%

除了 {name}`WP` 实例之外，{tactic}`mvcgen` 的大多数内置规范引理还依赖于 {name}`WPMonad` 实例的存在。
除了合法之外，单子实现 {name}`pure` 和 {name}`bind` 的最弱前提条件还应该对应于谓词变换单子的 {name}`pure` 和 {name}`bind` 运算符。
如果没有 {name}`WPMonad` 实例，{tactic}`mvcgen` 通常会返回原始证明目标不变。

{docstring WPMonad}

:::example "Missing `WPMonad` Instance"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

{name}`Id` 的重新实现有一个 {name}`WP` 实例，但没有 {name}`WPMonad` 实例：
```lean
def Identity (α : Type u) : Type u := α

variable {α : Type u}

def Identity.run (act : Identity α) : α := act

instance : Monad Identity where
  pure x := x
  bind x f := f x

instance : WP Identity .pure where
  wp x := PredTrans.pure x

theorem Identity.of_wp_run_eq {x : α} {prog : Identity α}
    (h : Identity.run prog = x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a => ⟨P a⟩)) → P x := by
  simp_all [WP.wp, Identity.run, ← h]
```

```lean -show
instance : LawfulMonad Identity :=
  LawfulMonad.mk' Identity
    (id_map := fun _ => rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun _ _ _ => rfl)
```

缺少的实例会阻止 {tactic}`mvcgen` 使用其 {name}`pure` 和 {name}`bind` 的规范。
这往往表现为等于原始目标的验证条件。
该函数反转列表：
```lean
def rev (xs : List α) : Identity (List α) := do
  let mut out := []
  for x in xs do
    out := x :: out
  return out
```
如果等于{name}`List.reverse`则正确。
然而，{tactic}`mvcgen` 并没有让目标更容易证明：
```lean +error -keep (name := noInst)
theorem rev_correct :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_wp_run_eq h
  mvcgen [rev]
```
```leanOutput noInst
unsolved goals
case vc1
α✝ : Type u_1
xs x : List α✝
h : (rev xs).run = x
out✝ : List α✝ := []
⊢ (wp⟦do
      let r ←
        forIn xs out✝ fun x r => do
            pure PUnit.unit
            pure (ForInStep.yield (x :: r))
      pure r⟧
    (PostCond.noThrow fun a => { down := a = xs.reverse })).down
```
当验证条件只是原始问题时，甚至没有对 {name}`bind` 进行任何简化，问题通常是缺少 {name}`WPMonad` 实例。
该问题可以通过添加合适的实例来解决：
```lean
instance : WPMonad Identity .pure where
  wp_pure _ := rfl
  wp_bind _ _ := rfl
```
通过这个实例，以及合适的不变量，{tactic}`mvcgen` 和 {tactic}`grind` 可以证明该定理。
```lean
theorem rev_correct :
    (rev xs).run = xs.reverse := by
  generalize h : (rev xs).run = x
  apply Identity.of_wp_run_eq h
  simp only [rev]
  mvcgen invariants
  · ⇓⟨xs, out⟩ =>
    ⌜out = xs.prefix.reverse⌝
  with grind
```
:::

### 充分性引理
%%%
tag := "mvcgen-adequacy"
%%%

可以从纯代码调用的 Monad 通常提供一个调用运算符，该运算符将任何所需的输入状态作为参数，并返回与输出状态配对的值或某种异常值。
示例包括 {name}`StateT.run`、{name}`ExceptT.run` 和 {name}`Id.run`。
{deftech}_Adequacy lemmas_ 在有关单子程序调用的语句与这些程序的 {tech (key := "weakest precondition")}[最弱前提条件] 语义（由其 {name}`WP` 实例给出）之间提供桥梁。
它们表明，如果最弱的前提条件为真，则有关调用的属性为真。

{docstring Id.of_wp_run_eq}

{docstring StateM.of_wp_run_eq}

{docstring StateM.of_wp_run'_eq}

{docstring ReaderM.of_wp_run_eq}

{docstring Except.of_wp_eq}

{docstring EStateM.of_wp_run_eq}

## 霍尔三元组
%%%
tag := "zh-vcgen-h013"
%%%

{deftech (key := "Hoare triple")}_Hoare Triple_{citep hoare69}[] 由前置条件、程序和后置条件组成。
在前置条件为 true 的状态下运行程序会导致后置条件为 true 的状态。

{docstring Triple}

::::syntax term (title := "Hoare Triples")
```grammar
⦃ $_ ⦄ $_ ⦃ $_ ⦄
```
:::leanSection
```lean -show
variable [WP m ps] {x : m α} {P : Assertion ps} {Q : PostCond α ps}
```
{lean}`⦃P⦄ x ⦃Q⦄` 是 {lean}`Triple x P Q` 的语法糖。
:::
::::

{docstring Triple.and}

{docstring Triple.mp}

## 规范引理
%%%
tag := "zh-vcgen-h014"
%%%

{deftech (key := "Specification lemmas")}_规范引理_是将霍尔三元组与函数关联起来的指定定理。
当 {tactic}`mvcgen` 遇到函数时，它会检查是否有任何已注册的规范引理，并尝试使用它们来释放中间 {tech (key := "verification conditions")}[验证条件]。
如果没有适用的规范引理，则语句的前置条件和后置条件之间的连接将成为验证条件。
规范引理允许对一元代码库进行组合推理。

当应用于其陈述为 Hoare 三元组的定理时，{attr}`spec` 属性将该定理注册为规范引理。
这些引理按优先级顺序使用。

{attr}`spec` 属性也可以应用于定义。
在定义上，表示验证条件生成时应展开定义。

:::syntax attr (title := "Specification Lemmas")
```grammar
spec $[$_:prio]?
```
{includeDocstring Lean.Parser.Attr.spec}
:::

规范引理中的全称量化变量可用于将输入状态与输出状态和返回值相关联。
这些变量称为 {deftech (key := "schematic variables")}_原理图变量_。

:::example "Schematic Variables"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

函数 {name}`double` 将 {name}`Nat` 状态的值加倍：
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
它的规范应该与初始状态和最终状态相关，但它无法知道它们的精确值。
该规范使用一个示意性变量来代表初始状态：
```lean
theorem double_spec :
    ⦃ fun s => ⌜s = n⌝ ⦄ double ⦃ ⇓ () s => ⌜s = 2 * n⌝ ⦄ := by
  simp [double]
  mvcgen with grind
```

前提条件中的断言是一个函数，因为 {lean}`StateM Nat` 的 {name}`PostShape` 是 {lean (type := "PostShape.{0}")}`.arg Nat .pure`，并且 {lean}`Assertion (.arg Nat .pure)` 是 {lean}`SPred [Nat]`。

:::
```lean -show -keep
-- Test preceding examples' claims
#synth WP (StateM Nat) (.arg Nat .pure : PostShape.{0})
example : Assertion (.arg Nat .pure) = SPred [Nat] := rfl
```

## 规格不变
%%%
tag := "zh-vcgen-h015"
%%%

这些类型用于不变量。
{name}`ForIn.forIn` 和 {name}`ForIn'.forIn'` 的 {tech (key := "specification lemmas")}[规范引理] 采用 {name}`Invariant` 类型的参数，并且 {tactic}`mvcgen` 确保其他自动化不会意外生成不变量。

{docstring Invariant}

{docstring Invariant.withEarlyReturn}

不变量使用列表对 {keywordOf Lean.Parser.Term.doFor}`for` 循环中的值序列进行建模。
循环中的当前位置通过 {name}`List.Cursor` 进行跟踪，该 {name}`List.Cursor` 将列表中的位置表示为位置左侧元素和右侧元素的组合。
这种类型不是传统的拉链，其中前缀是相反的以实现高效移动：它旨在用于规范和证明，而不是运行时代码，因此前缀按原始顺序排列。

{docstring List.Cursor}

{docstring List.Cursor.at}

{docstring List.Cursor.pos}

{docstring List.Cursor.current}

{docstring List.Cursor.tail}

{docstring List.Cursor.begin}

{docstring List.Cursor.end}


# 验证条件
%%%
tag := "zh-vcgen-h016"
%%%

{tactic}`mvcgen`策略将以 {name}`SPred` 和最弱先决条件表示的目标转换为一组不变量和验证条件，这些不变量和验证条件一起足以证明原始目标。
特别是，{tech (key := "Hoare triples")}[霍尔三元组]是根据最弱前提条件定义的，因此可以使用 {tactic}`mvcgen` 来证明它们。

:::leanSection
```lean -show
variable [Monad m] [WPMonad m ps] {e : m α} {P : Assertion ps} {Q : PostCond α ps}
```
目标的验证条件生成如下：
1. 应用了许多简化和重写。
2. 目标现在应该采用 {lean}`P ⊢ₛ wp⟦e⟧ Q` 的形式（即，从一组有状态假设到暗示所需后置条件的最弱前提条件的蕴涵）。
3. {tech (key := "Reducible")}[可约]常量和表达式 {lean}`e` 中标记为 {attrs}`@[spec]` 的定义已展开。
4. 如果表达式是 {tech (key := "auxiliary matching function")}[辅助匹配函数] 或条件（{name}`ite` 或 {name}`dite`）的应用，则首先对其进行简化。
   每个匹配器的 {tech (key := "match discriminant")}[判别式] 被简化，并且整个项被减少以试图消除匹配器或条件。
   如果失败，则会为每个分支生成一个新目标。
5. 如果表达式是常量的应用，则按优先级顺序尝试标记为 {attrs}`@[spec]` 的适用引理。
   Lean 包括常量的规范引理，例如 {name Bind.bind}`bind`、{name Pure.pure}`pure` 和 {name}`ForIn.forIn`，这些常量是由脱糖 {keywordOf Lean.Parser.Term.do}`do` 表示法产生的。
   实例化引理有时会解除其前提，特别是由于与目标的定义等价而导致的示意性变量。
   然而，{name}`Invariant` 类型的假设永远不会以这种方式实例化。
   如果规范引理的前置条件或后置条件与目标的前置条件或后置条件不完全匹配，则创建新的元变量来证明必要的蕴涵。
   如果这些不能使用简单的自动化立即释放，尝试使用局部假设并分解后置条件中的连词，那么它们仍然作为验证条件。
6. 如果此过程创建的每个剩余目标的格式为 {lean}`P ⊢ₛ wp⟦e⟧ Q`，则将针对验证条件递归处理该目标。如果不是，则将其添加到不变量或验证条件集中。
7. 由此产生的不变量和验证条件的子目标在证明状态中被分配了合适的名称。
8. 根据策略的配置参数，在每个验证条件下尝试 {tactic}`mvcgen_trivial` 和 {tactic}`mleave`。
:::

可以通过为库定义适当的 {tech (key := "specification lemmas")}[规范引理] 来改进验证条件生成。
良好规范引理的存在会导致生成的验证条件更少。
此外，确保术语的 {tech (key := "simp normal form")}[simp 范式] 适用于模式匹配，并且默认 simp 集中有足够的引理来将每个可能的术语简化为该范式，可能会导致更多条件和模式匹配被消除。

# 为 Monad 启用 `mvcgen`
%%%
tag := "zh-vcgen-h017"
%%%

如果 monad 是根据 Lean 标准库提供的 {tech (key := "monad transformers")}[monad 转换器] 实现的，例如 {name}`ExceptT` 和 {name}`StateT`，那么它不需要额外的实例。
其他 monad 将需要 {name}`WP`、{name}`LawfulMonad` 和 {name}`WPMonad` 的实例。
策略旨在支持对具有可能被中断状态的单线程控制进行建模的 monad；换句话说，就是普通命令式编程中存在的效果。
更多奇特效应尚未得到研究。

提供基本实例后，下一步就是证明 {ref "mvcgen-adequacy"}[充分性引理]。
这个引理应该表明，运行单子计算和断言所需谓词的最弱前提条件实际上足以证明该谓词。

除了 monad 的定义之外，典型的库还提供一组原始运算符。
其中每一个都应提供 {tech (key := "specification lemma")}[规范引理]。
将状态内部设为私有并导出一组精心设计的断言运算符可能也很有用。

理想情况下，库的原始运算符的规范引理应该是作为谓词转换器的运算符的精确规范。
虽然通常更容易思考运算符如何将输入状态转换为输出状态，但当后置条件完全自由时，{tech (key := "verification condition")}[验证条件]生成将更可靠地工作。
这允许自动化使用下一个语句的精确前提条件来实例化后置条件，而不需要显示蕴涵。
换句话说，将前置条件指定为后置条件的函数的规范在实践中比仅关联前置条件和后置条件的规范效果更好。

:::example "Schematic Postconditions"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

函数 {name}`double` 将自然数状态加倍：
```lean
def double : StateM Nat Unit := do
  modify (2 * ·)
```
按时间顺序思考，一个合理的规范是输出状态的值是输入状态的两倍。
这是使用代表初始状态的示意图变量来表达的：
```lean -keep
theorem double_spec :
    ⦃ fun s => ⌜s = n⌝ ⦄ double ⦃ ⇓ () s => ⌜s = 2 * n⌝ ⦄ := by
  simp [double]
  mvcgen with grind
```
然而，当 {name}`double` 用于其他函数时，示意性地处理后置条件的等效规范将导致更小的验证条件：
```lean
@[spec]
theorem better_double_spec {Q : PostCond Unit (.arg Nat .pure)} :
    ⦃ fun s => Q.1 () (2 * s) ⦄ double ⦃ Q ⦄ := by
  simp [double]
  mvcgen with grind
```
后置条件的第一个投影是它的状态断言。
现在，前置条件仅规定后置条件应保持初始状态的两倍。
:::

:::example "A Logging Monad"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```

monad {name}`LogM` 在计算期间维护一个仅附加日志：
```lean
structure LogM (β : Type u) (α : Type v) : Type (max u v) where
  log : Array β
  value : α

instance : Monad (LogM β) where
  pure x := ⟨#[], x⟩
  bind x f :=
    let { log, value } := f x.value
    { log := x.log ++ log, value }
```
它还有一个 {name}`LawfulMonad` 实例。
```lean -show
instance : LawfulMonad (LogM β) where
  map_const := rfl
  id_map x := rfl
  seqLeft_eq x y := rfl
  seqRight_eq x y := rfl
  pure_seq g x := by
    simp [pure, Seq.seq, Functor.map]
  bind_pure_comp f x := by
    simp [pure, bind, Functor.map]
  bind_map f x := by
    simp [bind, Seq.seq, Functor.map]
  pure_bind x f := by
    simp [pure, bind]
  bind_assoc x f g := by
    simp [bind]
```

可以使用 {name}`log` 写入日志，并且可以使用 {name}`LogM.run` 计算值和关联的日志。
```lean
def log (v : β) : LogM β Unit := { log := #[v], value := () }

def LogM.run (x : LogM β α) : α × Array β := (x.value, x.log)
```

{name}`WP` 实例使用 {name}`PredTrans.pushArg`，而不是从头开始编写。
该运算符旨在对状态单子进行建模，但 {name}`LogM` 可以被视为只能附加到状态的状态单子。
此附加在实例的主体中可见，其中附加了初始状态和操作产生的日志：
```lean
instance : WP (LogM β) (.arg (Array β) .pure) where
  wp
    | { log, value } =>
      PredTrans.pushArg (fun s => PredTrans.pure (value, s ++ log))
```

{name}`WPMonad` 实例也受益于作为状态单子的概念模型，并允许非常简短的证明：
```lean
instance : WPMonad (LogM β) (.arg (Array β) .pure) where
  wp_pure x := by
    ext
    simp [wp, pure]

  wp_bind _ _ := by
    ext
    simp [wp, bind]
```

充分性引理有一个重要细节：最弱前提条件变换的结果应用于空数组。
这是必要的，因为日志记录计算已被建模为仅附加状态，因此必须有一些初始状态。
从语义上讲，空数组是正确的选择，以便不将不是来自程序的项目放入日志中；从技术上讲，它还必须是一个可以与数组上的追加运算符进行交换的值。
```lean
theorem LogM.of_wp_run_eq {x : α × Array β} {prog : LogM β α}
    (h : LogM.run prog = x) (P : α × Array β → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ v l => ⌜P (v, l)⌝) #[]) → P x := by
  rw [← h]
  intro h'
  simp [wp] at h'
  exact h'
```

接下来，应该为库中的每个运算符提供一个规范引理。
只有一个：{name}`log`。
对于新的单子，这些证明必须经常打破 {tech (key := "Hoare triples")}[Hoare 三元组] 的抽象边界和最弱的前提条件；然后，图书馆的客户可以抽象地使用它们提供的规范。
```lean
theorem log_spec {x : β} :
    ⦃ fun s => ⌜s = s'⌝ ⦄ log x ⦃ ⇓ () s => ⌜s = s'.push x⌝ ⦄ := by
  simp [log, Triple, wp]
```

{name}`log` 的更好规范使用示意性后置条件：
```lean
variable {Q : PostCond Unit (.arg (Array β) .pure)}

@[spec]
theorem log_spec_better {x : β} :
    ⦃ fun s => Q.1 () (s.push x) ⦄ log x ⦃ Q ⦄ := by
  simp [log, Triple, wp]
```

将所有自然数记录到某个界限的函数 {name}`logUntil` 将始终生成长度等于其参数的日志：
```lean
def logUntil (n : Nat) : LogM Nat Unit := do
  for i in 0...n do
    log i

theorem logUntil_length : (logUntil n).run.2.size = n := by
  generalize h : (logUntil n).run = x
  unfold logUntil at h
  apply LogM.of_wp_run_eq h
  mvcgen invariants
  · ⇓⟨xs, _⟩ s => ⌜xs.pos = s.size⌝
  with
    simp_all [List.Cursor.pos] <;>
    grind [Std.PRange.Nat.size_rco, Std.Rco.length_toList]
```
:::

# 校样模式
%%%
tag := "mvcgen-proof-mode"
%%%

有状态目标可以使用特殊的_证明模式_来证明，其中目标通过两个假设上下文来呈现：普通的 Lean 上下文，其中包含 Lean 变量，以及特殊的有状态上下文，其中包含有关单子状态的假设。
在证明模式下，目标是{name}`SPred`，而不是{lean}`Prop`，整个目标相当于从假设的合取到结论的蕴涵关系（{name}`SPred.entails`）。

:::syntax Std.Tactic.Do.mgoalStx (title := "Proof Mode Goals")
证明模式目标呈现为一系列命名假设，每行一个，后跟 {keywordOf Std.Tactic.Do.mgoalStx}`⊢ₛ` 和一个目标。
```grammar
$[$_:ident : $t:term]*
⊢ₛ $_:term
```
:::

在证明模式下，特殊的策略操纵有状态上下文。
这些策略在 {ref "tactic-ref-spred"}[策略参考中其自己的部分] 中进行了描述。

当使用具体的 monad 时，{tactic}`mvcgen` 通常不会产生有状态的证明目标——它们被简化了。
然而，单子多态定理可以导致有状态的目标保留。

:::example "Stateful Proofs"
```imports -show
import Std.Do
import Std.Tactic.Do
```
```lean -show
open Std.Do

set_option mvcgen.warning false

```
函数 {name}`bump` 将其状态增加指定的量并返回结果值。
```lean
variable [Monad m] [WPMonad m ps]
def bump (n : Nat) : StateT Nat m Nat := do
  modifyThe Nat (· + n)
  getThe Nat
```

{name}`bump` 的规范引理以有意的低级方式进行证明，以演示中间证明状态：
```lean
theorem bump_correct :
      ⦃ fun n => ⌜n = k⌝ ⦄
      bump (m := m) i
      ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  mintro n_eq_k
  unfold bump
  unfold modifyThe
  mspec
  mspec
  mpure_intro
  constructor
  . trivial
  . simp_all
```

引理也可以仅使用简化器来证明：
```lean
theorem bump_correct' :
    ⦃ fun n => ⌜n = k⌝ ⦄
    bump (m := m) i
    ⦃ ⇓ r n => ⌜r = n ∧ n = k + i⌝ ⦄ := by
  mintro _
  simp_all [bump]
```
:::
