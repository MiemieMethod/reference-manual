/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import ManualZh.Tactics.Reference
import ManualZh.Tactics.Conv
import ManualZh.Tactics.Custom

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean.Elab.Tactic

#doc (Manual) "策略样张" =>
%%%
file := "Tactic-Proofs"
tag := "tactics"
%%%

策略语言是一种用于构造证明的专用编程语言。
在 Lean 中，{tech (key := "propositions")}[命题] 由类型表示，证明是居住在这些类型中的术语。
{margin}[{ref "propositions"}[关于命题的部分]更详细地描述了命题。]
虽然术语旨在方便地指示某个类型的特定居民，但策略的设计目的是方便地证明某个类型有人居住。
存在这种区别是因为定义挑选出感兴趣的精确对象并且程序返回预期结果很重要，但证明无关性意味着没有_技术_理由来选择一个证明项而不是另一个证明项。
例如，给定给定类型的两个假设，必须仔细编写程序才能使用正确的假设，而证明可以使用其中任何一个而不会产生任何后果。

策略是修改 {deftech}_proof state_.{index}[proof state] 的命令式程序
证明状态由 {deftech}_goals_ 的有序序列组成，它们是局部假设以及要居住的类型的上下文；策略可能会通过可能为空的进一步目标序列（称为 {deftech}_subgoals_）而“成功”，如果无法取得进展，则可能会“失败”。
如果策略成功且没有子目标，则证明完成。
如果它成功实现了一个或多个子目标，那么当这些子目标被证明时，它的一个或多个目标也将被证明。
证明状态中的第一个目标称为 {deftech}_main goal_.{index (subterm := "main")}[goal]{index}[main goal]
虽然大多数策略仅影响主要目标，但 {tactic}`<;>` 和 {tactic}`all_goals` 等运算符可用于将策略应用到许多目标，而子弹、{tactic}`next` 或 {tactic}`case` 等运算符可将后续策略的焦点缩小到仅一个目标目标处于证明状态。

策略在幕后构造 {deftech (key := "proof terms")}[证明条款]。
证明项是定理正确性的可独立检查的证据，以 Lean 的 类型论 形式编写。
每个证明都在 {tech (key := "kernel")}[内核] 中进行检查，并且可以使用独立实现的外部检查器进行验证，因此策略中的错误最糟糕的结果是令人困惑的错误消息，而不是不正确的证明。
策略证明中的每个目标对应于证明项的不完整部分。

# 运行策略
%%%
file := "Running-Tactics"
tag := "by"
%%%

:::TODO
`by` 的语法在下面用逗号而不是分号显示
:::

:::syntax Lean.Parser.Term.byTactic (title := "Tactic Proofs with {keyword}`by`")
策略包含在使用 {keywordOf Lean.Parser.Term.byTactic}`by` 的术语中，后跟策略的序列，其中每个序列具有相同的缩进：
```grammar
by
$t
```

或者，可以使用明确的大括号和分号：
```grammar
by { $t* }
```
:::

策略使用 {keywordOf Lean.Parser.Term.byTactic}`by` 术语调用。
当精化器遇到 {keywordOf Lean.Parser.Term.byTactic}`by` 时，它会调用策略解释器来构造结果项。
策略证明可以通过 {keywordOf Lean.Parser.Term.byTactic}`by` 嵌入到术语可能出现的任何上下文中。

# 阅读校样状态
%%%
file := "Reading-Proof-States"
tag := "proof-states"
%%%

验证状态下的目标按顺序显示，主要目标位于顶部。
目标可以是命名的，也可以是匿名的。
命名目标在顶部用 `case` 表示（称为 {deftech}_case label_），而匿名目标则没有此类指示符。
策略通常根据构造函数名称、参数名称、结构字段名称或策略实现的推理步骤的性质来分配目标名称。

::::example "Named goals"
```customCSS
#lawful-option-cases .goal-name { background-color: var(--lean-compl-yellow); }
```

该证明状态包含四个目标，所有目标均已命名。
这是{lean}`Monad Option`实例合法的证明的一部分（即提供{lean}`LawfulMonad Option`实例），并且案例名称（下面突出显示）来自{name}`LawfulMonad`的字段名称。

```proofState (tag := "lawful-option-cases")
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
intro α β γ x f g
rotate_right
intro α β x f
rotate_right
intro α β f x
rotate_right
```
::::


::::example "Anonymous Goals"
该证明状态包含单个匿名目标。

```proofState
∀ (n k : Nat), n + k = k + n := by
intro n k
```
::::

{tactic}`case` 和 {tactic}`case'`策略可用于使用所需目标的名称来选择新的主要目标。
当在本身具有名称的目标上下文中分配名称时，新目标的名称将附加到主目标的名称中，并在它们之间加一个点 (`'.', Unicode FULL STOP (0x2e)`)。

::::example "Hierarchical Goal Names"

:::tacticExample
```setup
intro n k
induction n
```


在尝试证明 {goal}`∀ (n k : Nat), n + k = k + n` 的过程中，可能会出现以下证明状态：
```pre
case zero
k : Nat
⊢ 0 + k = k + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```

在 {tacticStep}`induction k` 之后，两个新案例的名称以 `zero` 作为前缀，因为它们是在名为 `zero` 的目标中创建的：

```customCSS
#hierarchical-case-names .goal:not(:last-child) .goal-name { background-color: var(--lean-compl-yellow); }
```

```post (tag := "hierarchical-case-names")
case zero.zero
⊢ 0 + 0 = 0 + 0

case zero.succ
n✝ : Nat
a✝ : 0 + n✝ = n✝ + 0
⊢ 0 + (n✝ + 1) = n✝ + 1 + 0

case succ
k n✝ : Nat
a✝ : n✝ + k = k + n✝
⊢ n✝ + 1 + k = k + (n✝ + 1)
```
:::
::::


每个目标都包含一系列假设和期望的结论。
每个假设都有一个名称和类型；结论是一种类型。
假设是某种类型的任意元素或被假定为真的陈述。

::::example "Assumption Names and Conclusion"

```customCSS
#ex-assumption-names .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

这个目标有四个假设：

```proofState (tag := "ex-assumption-names")
∀ (α) (xs : List α), xs ++ [] = xs := by
intro α xs
induction xs
sorry
rename_i x xs ih
```

:::keepEnv
```lean -show
axiom α : Type
axiom x : α
axiom xs : List α
axiom ih : xs ++ [] = xs
```

他们是：

 * {lean}`α`，任意类型
 * {lean}`x`、任意{lean}`α`
 * {lean}`xs`，任意 {lean}`List α`
 * {lean}`ih`，归纳假设，断言将空列表附加到 {lean}`xs` 等于 {lean}`xs`。

结论是这样的陈述：在归纳假设中的等式两边添加 `x` 会产生相等的列表。
:::

::::

一些假设是 {deftech}_inaccessible_、{index}[inaccessible] {index (subterm := "inaccessible")}[asstitution]，这意味着它们不能通过名称显式引用。
当创建假设时没有指定名称或假设的名称被后来的假设所掩盖时，就会出现无法访问的假设。
无法获得的假设应被视为匿名；它们被呈现得好像它们有名称一样，因为它们可能会在后面的假设或结论中被引用，并且显示名称可以使这些引用彼此区分。
特别是，难以接近的假设在其名称后用匕首（`†`）表示。


::::example "Accessible Assumption Names"
```customCSS
#option-cases-accessible .hypothesis .name { background-color: var(--lean-compl-yellow); }
```

在这种证明状态下，所有假设都是可以实现的。

```proofState (tag := "option-cases-accessible")
LawfulMonad Option := by
constructor
intro α β f x
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
::::


::::example "Inaccessible Assumption Names"
```customCSS
#option-cases-inaccessible .hypotheses .hypothesis:nth-child(even) .name { background-color: var(--lean-compl-yellow); }
```

在这个证明状态下，只有第一个和第三个假设是可用的。
第二个和第四个是无法访问的，它们的名字中包含一把匕首，以表明它们无法被引用。

```proofState (tag := "option-cases-inaccessible")
LawfulMonad Option := by
constructor
intro α _ f _
rotate_right
sorry
rotate_right
sorry
rotate_right
sorry
rotate_right
```
::::


仍然可以使用无法达到的假设。
策略（例如 {tactic}`assumption` 或 {tactic}`simp`）可以扫描整个假设列表，找到有用的假设，而 {tactic}`contradiction` 可以通过找到不可能的假设而不命名它来消除当前目标。
其他策略（例如 {tactic}`rename_i` 和 {tactic}`next`）可用于命名不可访问的假设，从而使它们可访问。
此外，假设可以通过其类型来引用，方法是将类型写在单个 guillemets 中。

::::syntax term (title := "Assumptions by Type")
术语周围的单个 guillemets 表示对该类型范围内某个术语的引用。

```grammar
‹$t›
```

这可以用来通过定理陈述而不是名称来引用局部引理，或者用来引用假设，无论它们是否有明确的名称。
::::

::::example "Assumptions by Type"

:::keepEnv
```lean -show
variable (n : Nat)
```
在下面的证明中，重复使用 {tactic}`cases` 来分析数字。
在证明的开始，该数字被命名为 `x`，但 {tactic}`cases` 为后续数字生成了一个不可访问的名称。
该证明没有提供名称，而是利用了这样一个事实：在任何给定时间都存在一个 {lean}`Nat` 类型的假设，并使用 {lean}`‹Nat›` 来引用它。
迭代后，有一个假设 `n + 3 < 3`，{tactic}`contradiction` 可使用该假设从考虑中删除目标。
:::
```lean
example : x < 3 → x ∈ [0, 1, 2] := by
  intros
  iterate 3
    cases ‹Nat›
    . decide
  contradiction
```
::::

::::example "Assumptions by Type, Outside Proofs"

Single-guillemet 语法也适用于证明之外：

```lean (name := evalGuillemets)
#eval
  let x := 1
  let y := 2
  ‹Nat›
```
```leanOutput evalGuillemets
2
```

然而，对于非命题来说，这通常不是一个好主意——当选择类型的哪个元素很重要时，最好显式选择它。
::::

## 隐藏证明和大项
%%%
file := "Hiding-Proofs-and-Large-Terms"
tag := "hiding-terms-in-proof-states"
%%%

证明状态中的项可能相当大，并且可能有很多假设。
由于定义证明的无关性，证明术语通常提供很少的有用信息。
默认情况下，它们不会显示在证明状态的目标中，除非它们是 {deftech}_atomic_，这意味着它们不包含子项。
隐藏校样由两个选项控制：{option}`pp.proofs` 打开和关闭该功能，而 {option}`pp.proofs.threshold` 确定校样隐藏的大小阈值。

:::example "Hiding Proof Terms"
在此证明状态下，`0 < n` 的证明被隐藏。

```proofState
∀ (n : Nat) (i : Fin n), i.val > 5 → (⟨0, by cases i; omega⟩ : Fin n) < i := by
  intro n i gt
/--
n : Nat
i : Fin n
gt : ↑i > 5
⊢ ⟨0, ⋯⟩ < i
-/

```
:::



{optionDocs pp.proofs}

{optionDocs pp.proofs.threshold}


此外，当非证明项太大时，它们可能会被隐藏。
特别是，Lean 将隐藏低于可配置深度阈值的术语，并且一旦打印了一定数量的术语，它将隐藏术语的其余部分。
可以使用选项 {option}`pp.deepTerms` 启用或禁用显示深度术语，并且可以使用选项 {option}`pp.deepTerms.threshold` 配置深度阈值。
漂亮打印机步骤的最大数量可以使用选项 {option}`pp.maxSteps` 进行配置。
打印非常大的术语可能会导致工具速度减慢甚至堆栈溢出；调整这些选项的值时请保持保守。

{optionDocs pp.deepTerms}

{optionDocs pp.deepTerms.threshold}

{optionDocs pp.maxSteps}

## 元变量
%%%
file := "Metavariables"
tag := "metavariables-in-proofs"
%%%

以问号开头的术语是 {deftech}_metavariables_，对应于未知值。
它们可能代表 {tech}[universe] 级别或术语。
当还没有足够的信息来确定值时，一些元变量会作为 Lean 的精化过程的一部分出现。
这些元变量的名称末尾有一个数字部分，例如 `?m.392` 或 `?u.498`。
其他元变量是由于策略或 {tech (key := "synthetic holes")}[合成孔]而出现的。
这些元变量的名称没有数字部分。
由策略生成的元变量经常显示为 {tech}[case labels] 与元变量名称匹配的目标。


::::example "Universe Level Metavariables"
在这个证明状态下，`α` 的 宇宙层级 是未知的：
```proofState
∀ (α : _) (x : α) (xs : List α), x ∈ xs → xs.length > 0 := by
  intros α x xs elem
/--
α : Type ?u.912
x : α
xs : List α
elem : x ∈ xs
⊢ xs.length > 0
-/
```
::::

::::example "Type Metavariables"
在此证明状态下，列表元素的类型未知。
元变量会重复，因为未知类型在两个位置必须相同。
```proofState
∀ (x : _) (xs : List _), x ∈ xs → xs.length > 0 := by
  intros x xs elem
/--
x : ?m.1035
xs : List ?m.1035
elem : x ∈ xs
⊢ xs.length > 0
-/
```
::::


::::example "Metavariables in Proofs"

:::tacticExample

{goal -show}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

在这种证明状态下，
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
应用策略{tacticStep}`apply Nat.lt_trans` 会导致以下证明状态，其中传递性步骤 `?m` 的中间值未知：
```post
case h₁
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?m

case a
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?m < k

case m
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat
```
:::
::::

::::example "Explicitly-Created Metavariables"
:::tacticExample
{goal -show}`∀ (i j k  : Nat), i < j → j < k → i < k`

```setup
  intros i j k h1 h2
```

显式命名的漏洞由元变量表示，并且还产生证明目标。
在这种证明状态下，
```pre
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < k
```
应用策略{tacticStep}`apply @Nat.lt_trans i ?middle k ?p1 ?p2` 会导致以下证明状态，其中传递性步骤 `?middle` 的中间值未知，并且已为术语中的每个命名孔创建了目标：
```post
case middle
i j k : Nat
h1 : i < j
h2 : j < k
⊢ Nat

case p1
i j k : Nat
h1 : i < j
h2 : j < k
⊢ i < ?middle

case p2
i j k : Nat
h1 : i < j
h2 : j < k
⊢ ?middle < k
```
:::
::::

可以使用 {option}`pp.mvars` 禁用元变量编号的显示。
当使用 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 等将 Lean 的输出与所需字符串进行匹配的功能时，这非常有用，这在为自定义策略编写测试时非常有用。

{optionDocs pp.mvars}

::::draft
:::planned 68
演示并解释差异标签，这些标签显示证明状态步骤之间的差异。
:::
::::

# 策略语言
%%%
file := "The-Tactic-Language"
tag := "tactic-language"
%%%

策略脚本由策略序列组成，用分号或换行符分隔。
当用换行符分隔时，策略必须缩进到同一级别。
可以使用显式的花括号和分号来代替缩进。
策略序列可以用括号分组。
这允许在语法上预期为单个策略的位置使用策略序列。

一般来说，执行是从上到下进行的，每个策略都在前一个策略留下的证明状态下运行。
策略语言包含许多可以修改此流程的控制结构。

每个策略都是 `tactic` 类别中的语法扩展。
这意味着策略可以自由定义自己的具体语法和解析规则。
然而，除了少数例外，大多数策略都可以通过前导关键字来识别；例外情况通常是常用的内置控制结构，例如 {tactic}`<;>`。

## 控制结构
%%%
file := "Control-Structures"
tag := "tactic-language-control"
%%%

严格来说，控制结构与其他策略没有根本区别。
任何策略都可以自由地将其他人作为参数，并在它认为合适的任何上下文中安排它们的执行。
然而，即使这种区别是任意的，它仍然是有用的。
本节中的策略类似于编程中的传统控制结构，或者_仅_重组其他策略而不是本身取得进展。

### 成功与失败
%%%
file := "Success-and-Failure"
tag := "tactic-language-success-failure"
%%%

在验证状态下运行时，每个策略要么成功，要么失败。
策略故障类似于异常：故障通常会“冒泡”直到得到处理。
与异常不同的是，没有操作符来区分失败的原因； {tactic}`first` 仅采用第一个成功的分支。

::: tactic "fail"
:::

:::tactic "fail_if_success"
:::

:::tactic "try"
:::

:::tactic "first"
:::


### 分枝
%%%
file := "Branching"
tag := "tactic-language-branching"
%%%

策略证明可以使用模式匹配和条件。
然而，它们的含义与术语中的含义并不完全相同。
虽然术语预计在其变量值已知后执行，但证明是在其变量保持抽象的情况下执行的，并且应同时考虑_所有_情况。
因此，当策略中使用{keyword}`if`和{keyword}`match`时，它们的含义是案例推理而不是选择具体分支。
它们的所有分支都会被执行，并且条件或模式匹配用于通过每个分支中的更多信息来细化主要目标，而不是选择单个分支。

:::tactic "if"

:::

:::example "Reasoning by cases with `if`"
在 {keywordOf Lean.Parser.Tactic.tacIfThenElse}`if` 的每个分支中，添加一个假设来反映 `n = 0` 是否成立。

```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  if n = 0 then
    simp [*]
  else
    simp only [↓reduceIte, gt_iff_lt, *]
    omega
```
:::

:::tactic Lean.Parser.Tactic.match (show := "match")

当模式匹配时，目标中 {tech (key := "match discriminant")}[判别式] 的实例将替换为每个分支中与它们匹配的模式。
然后每个分支必须证明细化的目标。
与 `cases`策略相比，使用 `match` 可以在执行的案例分析中提供更大程度的灵活性，但每个分支完全解决其目标的要求使得合并到更大的自动化脚本中变得更加困难。
:::

:::example "Reasoning by cases with `match`"
在 {keywordOf Lean.Parser.Tactic.match}`match` 的每个分支中，判别式 `n` 已替换为 `0` 或 `k + 1`。
```lean
example (n : Nat) : if n = 0 then n < 1 else n > 0 := by
  match n with
  | 0 =>
    simp
  | k + 1 =>
    simp
```
:::

### 目标选择
%%%
file := "Goal-Selection"
tag := "tactic-language-goal-selection"
%%%


大多数策略影响 {tech (key := "main goal")}[主要目标]。
目标选择策略提供了一种将不同目标视为主要目标的方法，从而重新排列证明状态中的目标顺序。


:::tactic "case"
:::

:::tactic "case'"
:::


:::tactic "rotate_left"
:::

:::tactic "rotate_right"
:::

#### 测序
%%%
file := "Sequencing"
tag := "tactic-language-sequencing"
%%%

除了逐个运行策略（每个都用于解决主要目标）之外，策略语言还支持根据目标生成方式对策略进行排序。
{tactic}`<;>`策略组合器允许将策略应用于由其他策略生成的_every_ {tech (key := "subgoal")}[子目标]。
如果没有生成新目标，则不会运行第二个策略。

:::tactic "<;>"

如果策略在任何 {tech (key := "subgoals")}[子目标] 上失败，则整个 {tactic}`<;>`策略失败。
:::

::::example "Subgoal Sequencing"
:::tacticExample

```setup
  intro x h
```


{goal -show}`∀x, x = 1 ∨ x = 2 → x < 3`

在这个证明状态下：
```pre
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```
策略{tacticStep}`cases h` 产生以下两个目标：
```post
case inl
x : Nat
h✝ : x = 1
⊢ x < 3

case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

:::
:::tacticExample

```setup
  intro x h
```

{goal -show}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre -show
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

运行 {tacticStep}`cases h ; simp [*]` 会导致 {tactic}`simp` 解决第一个目标，留下第二个目标：
```post
case inr
x : Nat
h✝ : x = 2
⊢ x < 3
```

:::

:::tacticExample

```setup
  intro x h
```

{goal -show}`∀x, x = 1 ∨ x = 2 → x < 3`

```pre -show
x : Nat
h : x = 1 ∨ x = 2
⊢ x < 3
```

用 {tactic}`<;>` 替换 `;` 并运行 {tacticStep}`cases h <;> simp [*]` 可以通过 {tactic}`simp` 解决*两个*新目标：

```post

```

:::

::::

#### 致力于多个目标
%%%
file := "Working-on-Multiple-Goals"
tag := "tactic-language-multiple-goals"
%%%

策略{tactic}`all_goals` 和 {tactic}`any_goals` 允许将策略应用于证明状态下的每个目标。
它们之间的区别在于，如果策略在任何一个目标中失败，{tactic}`all_goals` 本身就会失败，而 {tactic}`any_goals` 仅当策略在所有目标中失败时才失败。

:::tactic "all_goals"
:::

:::tactic "any_goals"
:::


### 聚焦
%%%
file := "Focusing"
tag := "tactic-language-focusing"
%%%

关注策略会从一些进一步的策略的考虑中删除证明目标的一些子集（通常只留下主要目标）。
除了此处描述的策略之外，{tactic}`case` 和 {tactic}`case'`策略重点关注选定的目标。

:::tactic Lean.cdot (show := "·")

每当策略线产生多个新子目标时，通常认为使用子弹是良好的 Lean 风格。
这使得阅读和维护证明变得更加容易，因为推理步骤之间的联系更加清晰，并且编辑证明时子目标数量的任何变化都会产生局部效果。
:::

:::tactic "next"
:::


:::tactic "focus"
:::

### 重复与迭代
%%%
file := "Repetition-and-Iteration"
tag := "tactic-language-iteration"
%%%

:::tactic "iterate"
:::

:::tactic "repeat"
:::

:::tactic "repeat'"
:::

:::tactic "repeat1'"
:::


## 姓名和卫生
%%%
file := "Names-and-Hygiene"
tag := "tactic-language-hygiene"
%%%

策略在幕后生成证明项。
这些证明项存在于局部上下文中，因为证明状态中的假设对应于局部绑定项。
假设的使用对应于变量引用。
假设的命名是可预测的，这一点非常重要；否则，对策略的内部实现进行微小更改可能会导致变量捕获，或者如果导致选择不同的名称，则会导致引用损坏。

Lean 的策略语言是_卫生_。 {index (subterm := "in tactics")}[卫生]
这意味着策略语言遵循词法范围：策略中出现的名称引用源代码中的封闭绑定，而不是由生成的代码确定，并且策略框架负责维护此属性。
策略脚本中的变量引用引用脚本开头范围内的名称或作为策略的一部分显式引入的绑定，而不是选择在幕后证明术语中使用的名称。

卫生策略的结果是引用假设的唯一方法是明确命名它。
策略不能自己分配假设名称，而必须接受用户的名称；用户相应地有义务提供他们希望引用的假设的名称。
当假设没有用户提供的名称时，它会在证明状态中显示为匕首 (`'†', DAGGER	0x2020`)。
匕首表明该名称_不可访问_且无法显式引用。

可以通过将选项 {option}`tactic.hygienic` 设置为 `false` 来禁用卫生功能。
不建议这样做，因为许多策略依赖卫生系统来防止捕获，因此不会产生仔细的手动名称选择的开销。

{optionDocs tactic.hygienic}

::::example "Tactic hygiene: inaccessible assumptions"
:::tacticExample

```setup
skip
```
证明{goal}`∀ (n : Nat), 0 + n = n`时，初始证明状态为：

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

策略{tacticStep}`intro` 导致证明状态具有无法访问的假设：

```post
n✝ : Nat
⊢ 0 + n✝ = n✝
```
:::
::::

::::example "Tactic hygiene: accessible assumptions"
:::tacticExample

```setup
skip
```
证明{goal}`∀ (n : Nat), 0 + n = n`时，初始证明状态为：

```pre
⊢ ∀ (n : Nat), 0 + n = n
```

策略{tacticStep}`intro n` 具有显式名称 `n`，会产生具有可访问命名假设的证明状态：

```post
n : Nat
⊢ 0 + n = n
```
:::
::::

### 获取假设
%%%
file := "Accessing-Assumptions"
tag := "tactic-language-assumptions"
%%%

许多策略提供了一种为其引入的假设指定名称的方法。
例如，{tactic}`intro` 和 {tactic}`intros` 将假设名称作为参数，而 {tactic}`induction` 的 {keywordOf Lean.Parser.Tactic.induction}`with` 形式允许同时进行案例选择、假设命名和聚焦。
当假设没有名称时，可以使用 {tactic}`next`、{tactic}`case` 或 {tactic}`rename_i` 进行分配。

:::tactic "rename_i"
:::

## 假设管理
%%%
file := "Assumption-Management"
tag := "tactic-language-assumption-management"
%%%

更大的证明可以受益于证明状态的管理，消除不相关的假设并使它们的名称更容易理解。
与这些运算符一起，{tactic}`rename_i` 允许重命名无法访问的假设，并且 {tactic}`intro`、{tactic}`intros` 和 {tactic}`rintro` 将暗示或全称量化的目标转换为具有附加假设的目标。

:::tactic "rename"
:::

:::tactic "revert"
:::

:::tactic "clear"
:::


## 局部定义和证明
%%%
file := "Local-Definitions-and-Proofs"
tag := "tactic-language-local-defs"
%%%

{tactic}`have` 和 {tactic}`let` 均创建局部假设。
一般来说，证明中间引理时应使用{tactic}`have`； {tactic}`let` 应保留用于本地定义。

:::tactic "have"
:::

:::tactic Lean.Parser.Tactic.tacticHave__
:::

:::tactic Lean.Parser.Tactic.tacticHave'
:::

:::tactic Lean.Parser.Tactic.tacticLet__ (show := "let")
:::

:::tactic Lean.Parser.Tactic.letrec (show := "let rec")
:::

:::tactic Lean.Parser.Tactic.tacticLetI__
:::

:::tactic Lean.Parser.Tactic.tacticLet'__
:::

## 配置
%%%
file := "Configuration"
tag := "tactic-config"
%%%

许多策略是可配置的。{index (subterm := "of tactics")}[配置]
按照惯例，策略共享配置语法，使用 {syntaxKind}`optConfig` 进行描述。
策略的文档中介绍了每个策略可用的特定选项。

:::syntax Lean.Parser.Tactic.optConfig -open (title := "Tactic Configuration")
策略配置由零个或多个 {deftech (key := "configuration items")}[配置项] 组成：
```grammar
$x:configItem*
```
:::

:::syntax Lean.Parser.Tactic.configItem -open (title := "Tactic Configuration Items")
每个配置项都有一个与基础策略选项相对应的名称。
可以使用前缀 `+` 和 `-` 启用或禁用布尔选项：
```grammar
+$x
```
```grammar
-$x
```

可以使用类似于命名函数参数的语法为选项分配特定值：
```grammar
($x:ident := $t)
```

最后保留名称`config`；它用于将一整套选项作为数据结构传递。
预期的具体类型取决于策略。
```grammar
(config := $t)
```

:::

## 命名空间和选项管理
%%%
file := "Namespace-and-Option-Management"
tag := "tactic-language-namespaces-options"
%%%

可以使用与术语中相同的语法在策略脚本中调整命名空间和选项。

:::tactic Lean.Parser.Tactic.set_option (show := "set_option")
:::

:::tactic Lean.Parser.Tactic.open (show := "open")
:::

### 控制展开
%%%
file := "Controlling-Unfolding"
tag := "tactic-language-unfolding"
%%%

默认情况下，仅展开标记为可简化的定义，检查 定义等价 时除外。
这些运算符允许针对策略脚本的某些部分调整此默认值。

:::tactic Lean.Parser.Tactic.withReducibleAndInstances
:::

:::tactic Lean.Parser.Tactic.withReducible
:::

:::tactic Lean.Parser.Tactic.withUnfoldingAll
:::


# 选项
%%%
file := "Options"
tag := "tactic-language-options"
%%%

这些选项影响策略的含义。

{optionDocs tactic.customEliminators}

{optionDocs tactic.skipAssignedInstances}

{optionDocs tactic.simp.trace}


{include 0 ManualZh.Tactics.Reference}

{include 0 ManualZh.Tactics.Conv}

# 命名绑定变量
%%%
file := "Naming-Bound-Variables"
tag := "bound-variable-name-hints"
%%%

当 {ref "the-simplifier"}[simplifier] 或 {tactic}`rw`策略引入新的绑定形式（例如函数参数）时，它们会根据所应用的重写规则的语句中的名称来选择绑定变量的名称。
如有必要，该名称可以是唯一的。
在某些情况下，例如{ref "well-founded-preprocessing"}[使用良基递归的终止证明的预处理定义]，终止证明义务中出现的名称应该是原始函数定义中编写的对应名称。

{name}`binderNameHint` {tech}[gadget] 可用于指示应根据其他术语中绑定的变量来命名绑定变量。
按照惯例，术语 {lean}`()` 用于指示名称不应取自原始定义。

{docstring binderNameHint}


{include 0 ManualZh.Tactics.Custom}
