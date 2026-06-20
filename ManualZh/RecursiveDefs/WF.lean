/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Papers
import ManualZh.RecursiveDefs.WF.GuessLexExample
import ManualZh.RecursiveDefs.WF.PreprocessExample

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "良基递归" =>
%%%
tag := "well-founded-recursion"
%%%

由 {deftech}_well-founded recursion_ 定义的函数是这样的函数，其中每个递归调用的参数都比函数的参数_小_（在 {ref "wf-rel"}[适当的意义上]）。
与 {ref "structural-recursion"}[结构递归] 不同，其中递归定义必须满足特定的语法要求，而使用良基递归的定义则采用语义参数。
这允许接受更大类别的递归定义。
此外，当Lean的自动化无法构建终止证明时，可以手动指定一个。

Lean 编译器对所有定义的处理方式相同。
在 Lean 的逻辑中，使用良基递归的定义通常不会减少 {tech (key := "definitional equality")}[定义]。
然而，这些约简确实作为命题等式成立，并且 Lean 自动证明了它们。
这通常不会使证明使用良基递归的定义的属性变得更加困难，因为命题约简可用于推理函数的行为。
然而，这确实意味着在类型中使用这些函数通常效果不佳。
即使约简行为恰好在定义上成立，它通常也比内核中的结构递归定义慢得多，后者必须随定义一起展开终止证明。
如果可能，应使用结构递归定义用于 定义等价 很重要的类型或其他情况的递归函数。

要显式使用良基递归，可以使用 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句来注释函数或定理定义，该子句指定函数终止的 {deftech}_measure_。
该度量应该是在每次递归调用时减少的项；它可以是函数的参数之一或参数的元组，但也可以是任何其他术语。
度量的类型必须配备 {tech}[有充分基础的关系]，它确定度量减少意味着什么。

:::syntax Lean.Parser.Termination.terminationBy (title := "Explicit Well-Founded Recursion")

{keywordOf Lean.Parser.Command.declaration}`termination_by` 子句引入了终止参数。

```grammar
termination_by $[$_:ident* =>]? $term
```

可选 `=>` 之前的标识符可以将函数参数带入非
已经绑定在声明头中，并且强制术语必须指示函数的参数之一，无论是在头中引入还是在子句中本地引入。
:::

:::example "Division by Iterated Subtraction"
除法可以指定为从被除数中减去除数的次数。
无法使用结构递归详细说明此操作，因为减法不是模式匹配。
`n` 的值确实会随着每次递归调用而减小，因此良基递归可用于通过迭代减法来证明除法的定义合理。

```lean
def div (n k : Nat) : Nat :=
  if k = 0 then 0
  else if k > n then 0
  else 1 + div (n - k) k
termination_by n
```
:::

# 基础良好的关系
%%%
tag := "wf-rel"
%%%

如果不存在无限下降链，则关系 `≺` 是 {deftech}_有充分基础的关系_

$$` x_0 ≻ x_1 ≻ \cdots`

在 Lean 中，配备有规范基础关系的类型是 {name}`WellFoundedRelation` 类型类的实例。

{docstring WellFoundedRelation}

```lean -show
section
variable {α : Type u} {β : Type v} (a₁ a₂ : α) (b₁ b₂ : β) [WellFoundedRelation α] [WellFoundedRelation β]
variable {γ : Type u} (x₁ x₂ : γ) [SizeOf γ]
local notation x " ≺ " y => WellFoundedRelation.rel x y
```

最重要的实例是：

* {name}[`Nat`]，由 {lean  (type := "Nat → Nat → Prop")}`(· < ·)` 订购。

* {name}[`Prod`]，按字典顺序排序：{lean}`(a₁, b₁) ≺ (a₂, b₂)` 当且仅当 {lean}`a₁ ≺ a₂` 或 {lean}`a₁ = a₂` 和 {lean}`b₁ ≺ b₂`。

* 作为 {name}`SizeOf` 类型类实例（提供方法 {name}`SizeOf.sizeOf`）的每个类型都具有良好基础的关系。
  对于这些类型，{lean}`x₁ ≺ x₂` 当且仅当 {lean}`sizeOf x₁ < sizeOf x₂`。对于 {tech}[归纳类型]，{lean}`SizeOf` 实例由 Lean 自动派生。

```lean -show
end
```

请注意，存在一个低优先级实例 {name}`instSizeOfDefault`，它为任何类型提供 {lean}`SizeOf` 实例，并且始终返回 {lean}`0`。
此实例不能用于证明函数使用良基递归终止，因为 {lean}`0 < 0` 为 false。

```lean -show

-- Check claims about instSizeOfDefault

example {α} (x : α) : sizeOf x = 0 := by rfl

/-- info: instSizeOfDefault.{u} (α : Sort u) : SizeOf α -/
#check_msgs in
#check instSizeOfDefault

```

:::example "Default Size Instance"

一般来说，函数类型不具有对终止证明有用的有根据的关系。
{ref "instance-synth"}[实例综合]因此选择{name}`instSizeOfDefault`和相应的有根据的关系。
如果度量是函数，则选择默认的 {name}`SizeOf` 实例，证明无法成功。

```lean -keep
def fooInst (b : Bool → Bool) : Unit := fooInst (b ∘ b)
termination_by b
decreasing_by
  guard_target =
    @sizeOf (Bool → Bool) (instSizeOfDefault _) (b ∘ b) < sizeOf b
  simp only [sizeOf, default.sizeOf]
  guard_target = 0 < 0
  simp
  guard_target = False
  sorry
```
:::

# 终止证明
%%%
tag := "zh-recursivedefs-wf-h002"
%%%

一旦指定了 {tech}[measure] 并确定了其 {tech}[well-founded relation]，Lean 就会确定每个递归调用的终止证明义务。

```lean -show
section
variable {α : Type u} {β : α → Type v} {β' : Type v} (more : β') (g : (x : α) → (y : β x) → β' → γ) [WellFoundedRelation γ] (a₁ p₁ : α) (a₂ : β a₁) (p₂ : β p₁)

local notation (name := decRelStx) x " ≺ " y => WellFoundedRelation.rel x y
local notation "…" => more

```

每个递归调用的证明义务的形式为 {lean}`g a₁ a₂ … ≺ g p₁ p₂ …`，其中：
 * {lean}`g` 是作为参数函数的测量值，
 * {name WellFoundedRelation.rel}`≺` 是推断的有根据的关系，
 * {lean}`a₁` {lean}`a₂` {lean}`…` 是递归调用的参数，
 * {lean}`p₁` {lean}`p₂` {lean}`…` 是函数定义的参数。

证明义务的上下文是递归调用的本地上下文。
特别是，局部假设（例如 `if h : _`、`match h : _ with ` 或 `have` 引入的假设）可用。
如果函数参数是模式匹配的 {tech (key := "match discriminant")}[判别式]（例如，通过 {keywordOf Lean.Parser.Term.match}`match` 表达式），则该参数将被细化为证明义务中的匹配模式。

```lean -show
end
```

整体终止证明义务由每个递归调用的一个目标组成。
默认情况下，策略{tactic}`decreasing_trivial` 用于证明每个证明义务。
可以使用可选的 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句（位于 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句之后）提供自定义策略脚本。
此策略脚本运行一次，每个证明义务都有一个目标，而不是针对每个证明义务单独运行。

```lean -show
section
variable {n : Nat}
```

::::example "Termination Proof Obligations"

以下斐波那契数列的递归定义有两次递归调用，这导致终止证明中有两个目标。

```lean +error -keep (name := fibGoals)
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals (whitespace := lax) -show
unsolved goals
   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h : ¬n ≤ 1
   ⊢ n - 2 < n
```

```proofState
∀ (n : Nat), (h : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n h
  apply And.intro ?_ ?_
/--
n : Nat
h : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h : ¬n ≤ 1
⊢ n - 2 < n
-/

```



这里，{tech}[measure] 只是参数本身，有根据的顺序是自然数上的小于关系。
第一个证明目标要求用户证明第一个递归调用的参数（即 {lean}`n - 1`）严格小于函数的参数 {lean}`n`。

两种端接证明均可使用 {tactic}`omega`策略轻松解除。

```lean -keep
def fib (n : Nat) :=
  if h : n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  · omega
  · omega
```
::::
```lean -show
end
```

:::example "Refined Parameters"

如果函数的参数是模式匹配的 {tech (key := "match discriminant")}[判别式]，则证明义务会提到精炼参数。

```lean +error -keep (name := fibGoals2)
def fib : Nat → Nat
  | 0 | 1 => 1
  | .succ (.succ n) => fib (n + 1) + fib n
termination_by n => n
decreasing_by
  skip
```
```leanOutput fibGoals2 (whitespace := lax) -show
unsolved goals
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
```

```proofState
∀ (n : Nat), n + 1 < n.succ.succ ∧ n < n.succ.succ := by
  intro n
  apply And.intro ?_ ?_
/--
n : Nat
⊢ n + 1 < n.succ.succ

n : Nat
⊢ n < n.succ.succ
-/

```

:::

:::paragraph
此外，上下文还通过额外的假设得以丰富，可以更容易地证明终止。
一些例子包括：

 * 在 {ref "if-then-else"}[if-then-else] 表达式的分支中，添加了断言当前分支条件的假设，就像使用了依赖的 if-then-else 语法一样。
 * 在某些高阶函数的函数参数中，函数体的上下文通过有关参数的假设来丰富。

该列表并不详尽，并且该机制是可扩展的。
{ref "well-founded-preprocessing"}[预处理部分]中有详细描述。
:::

```lean -show
section
variable {x : Nat} {xs : List Nat} {n : Nat}
```

:::example "Enriched Proof Obligation Contexts"

这里，{keywordOf termIfThenElse}`if` 没有将关于条件（即，是否 {lean}`n ≤ 1`）的本地假设添加到分支中的本地上下文。


```lean +error -keep (name := fibGoals3)
def fib (n : Nat) :=
  if n ≤ 1 then
    1
  else
    fib (n - 1) + fib (n - 2)
termination_by n
decreasing_by
  skip
```

```leanOutput fibGoals3 (whitespace := lax) -show
unsolved goals
   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 1 < n

   n : Nat
   h✝ : ¬n ≤ 1
   ⊢ n - 2 < n
```

尽管如此，这些假设在终止证明的上下文中是可用的：

```proofState
∀ (n : Nat), («h✝» : ¬ n ≤ 1) → n - 1 < n ∧ n - 2 < n := by
  intro n «h✝»
  apply And.intro ?_ ?_
/--
n : Nat
h✝ : ¬n ≤ 1
⊢ n - 1 < n

n : Nat
h✝ : ¬n ≤ 1
⊢ n - 2 < n
-/

```

{keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` 循环体中的终止证明义务也得到了丰富，在本例中具有 {name}`Std.Legacy.Range` 成员资格假设：

```lean +error -keep (name := nestGoal3)
def f (xs : Array Nat) : Nat := Id.run do
  let mut s := xs.sum
  for i in [:xs.size] do
    s := s + f (xs.take i)
  pure s
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal3 (whitespace := lax) -show
unsolved goals
xs : Array Nat
s : Nat := xs.sum
i : Nat
h✝ : i ∈ [:xs.size]
⊢ sizeOf (xs.take i) < sizeOf xs
```

```proofState
∀ (xs : Array Nat)
  (i : Nat)
  («h✝» : i ∈ [:xs.size]),
   sizeOf (xs.take i) < sizeOf xs := by
  set_option tactic.hygienic false in
  intros
```

类似地，在以下（人为的）示例中，终止证明包含一个附加假设，显示 {lean}`x ∈ xs`。

```lean +error -keep (name := nestGoal1)
def f (n : Nat) (xs : List Nat) : Nat :=
  List.sum (xs.map (fun x => f x []))
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal1 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
h✝ : x ∈ xs
⊢ sizeOf [] < sizeOf xs
```

```proofState
∀ (n : Nat) (xs : List Nat) (x : Nat) («h✝» : x ∈ xs), sizeOf ([] : List Nat) < sizeOf xs := by
  set_option tactic.hygienic false in
  intros
/--
n : Nat
xs : List Nat
x : Nat
h✝ : x ∈ xs
⊢ sizeOf [] < sizeOf xs
-/
```

此功能需要对嵌套递归调用的高阶函数进行特殊设置，如 {ref "well-founded-preprocessing"}[预处理部分]中所述。
在下面的定义中，除了使用自定义的等效函数而不是 {name}`List.map` 之外，与上面的定义相同，证明义务上下文未得到丰富：

```lean +error -keep (name := nestGoal4)
def List.myMap := @List.map
def f (n : Nat) (xs : List Nat) : Nat :=
  List.sum (xs.myMap (fun x => f x []))
termination_by xs
decreasing_by
  skip
```
```leanOutput nestGoal4 (whitespace := lax) -show
unsolved goals
n : Nat
xs : List Nat
x : Nat
⊢ sizeOf [] < sizeOf xs
```

```proofState
∀ (n : Nat) (xs : List Nat) (x : Nat), sizeOf ([] : List Nat) < sizeOf xs := by
  set_option tactic.hygienic false in
  intros
```

:::

```lean -show
end
```


```lean -show
section
```

::::TODO

:::example "Nested recursive calls and subtypes"

我（Joachim）想提供一个很好的例子，其中递归调用相互嵌套，并且可能需要在结果中引入一种子类型才能使其通过。但现在想不出什么好的和自然的。

:::

::::

# 默认终止证明策略
%%%
tag := "zh-recursivedefs-wf-h003"
%%%

如果未给出 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句，则隐式使用 {tactic}`decreasing_tactic`，并分别应用于每个证明义务。


:::tactic "decreasing_tactic" +replace

策略{tactic}`decreasing_tactic` 主要处理元组的字典顺序，如果乘积的左侧组件是 {tech (key := "definitional equality")}[定义等价]，则应用 {name}`Prod.Lex.right`，否则应用 {name}`Prod.Lex.left`。
以这种方式预处理元组后，它调用 {tactic}`decreasing_trivial`策略。

:::


:::tactic "decreasing_trivial"

策略{tactic}`decreasing_trivial` 是可扩展的策略，它应用一些常见的启发式方法来解决终止目标。
特别是，它尝试以下策略和定理：

* {tactic}`simp_arith`
* {tactic}`assumption`
* 定理 {name}`Nat.sub_succ_lt_self`、{name}`Nat.pred_lt_of_lt` 和 {name}`Nat.pred_lt`，处理常见算术目标
* {tactic}`omega`
* {tactic}`array_get_dec`和{tactic}`array_mem_dec`，证明数组元素的大小小于数组的大小
* {tactic}`sizeOf_list_dec` 列表元素的大小小于列表的大小
* {name}`String.Legacy.Iterator.sizeOf_next_lt_of_hasNext` 和 {name}`String.Legacy.Iterator.sizeOf_next_lt_of_atEnd`，使用 {keywordOf Lean.Parser.Term.doFor}`for` 处理字符串迭代

该策略旨在使用 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 进行进一步的启发式扩展。

:::


:::example "No Backtracking of Lexicographic Order"

需要更复杂的 {tech}[measure] 的递归函数的一个经典示例是 Ackermann 函数：

```lean -keep
def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)
```

该度量是一个元组，因此每个递归调用都必须针对按字典顺序小于参数的参数。
默认的 {tactic}`decreasing_tactic` 可以处理这个问题。

特别要注意的是，第三个递归调用具有小于第二个参数的第二个参数和定义上等于第一个参数的第一个参数。
这允许 {tactic}`decreasing_tactic` 申请 {name}`Prod.Lex.right`。

```signature
Prod.Lex.right {α β} {ra : α → α → Prop} {rb : β → β → Prop}
  (a : α) {b₁ b₂ : β}
  (h : rb b₁ b₂) :
  Prod.Lex ra rb (a, b₁) (a, b₂)
```

但是，使用以下修改后的函数定义会失败，其中第三个递归调用的第一个参数可证明小于或等于第一个参数，但在语法上不相等：

```lean -keep +error (name := synack)
def synack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
```
```leanOutput synack (whitespace := lax)
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
m n : Nat
⊢ m / 2 + 1 < m + 1
```

由于{name}`Prod.Lex.right`不适用，所以策略使用了{name}`Prod.Lex.left`，从而导致上述目标无法证明。

此函数定义可能需要使用更通用的定理 {name}`Prod.Lex.right'` 进行手动证明，该定理允许元组的第一个组件（必须为 {name}`Nat` 类型）小于或等于而不是严格相等：
```signature
Prod.Lex.right' {β} (rb : β → β → Prop)
  {a₂ : Nat} {b₂ : β} {a₁ : Nat} {b₁ : β}
  (h₁ : a₁ ≤ a₂) (h₂ : rb b₁ b₂) :
  Prod.Lex Nat.lt rb (a₁, b₁) (a₂, b₂)
```

```lean -keep
def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
decreasing_by
  · apply Prod.Lex.left
    omega
  -- the next goal corresponds to the third recursive call
  · apply Prod.Lex.right'
    · omega
    · omega
  · apply Prod.Lex.left
    omega
```

{tactic}`decreasing_tactic`策略不使用更强的 {name}`Prod.Lex.right'`，因为它需要在失败时回溯。

:::

# 推断良基递归
%%%
tag := "inferring-well-founded-recursion"
%%%

如果递归函数定义未指示终止 {tech}[measure]，Lean 将尝试自动发现终止。
如果 {keywordOf Lean.Parser.Command.declaration}`termination_by` 和 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 均未提供，则 Lean 将在尝试良基递归之前尝试 {ref "inferring-structural-recursion"}[推断结构递归]。
如果存在 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句，则仅尝试良基递归。

为了推断合适的终止 {tech}[measure]，Lean 考虑多个 {deftech}_basic TerminationMeasures_（它们是类型 {name}`Nat` 的终止测量），然后尝试这些测量的所有元组。

考虑的基本终止措施是：

* 其类型具有非平凡 {name}`SizeOf` 实例的所有参数
* 每当递归调用的本地上下文假设类型为 `e₁ < e₂` 或 `e₁ ≤ e₂` 时，表达式 `e₂ - e₁` ，其中 `e₁` 和 `e₂` 的类型为 {name}`Nat` 并且仅取决于函数的参数。 {margin}[此方法基于 {citehere manolios2006}[] 的工作。]
* 在相互组中，使用附加的基本措施来区分对组中其他函数的递归调用和对正在定义的函数的递归调用（详细信息请参见{ref "mutual-well-founded-recursion"}[有关相互良基递归的部分]）

{deftech}_候选度量_是基本度量或基本度量的元组。
如果任何候选措施允许通过终止证明策略（即 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 指定的策略或 {tactic}`decreasing_trivial`，如果没有 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句）来解除所有证明义务，则选择任意此类候选措施作为自动终止措施。

{keyword}`termination_by?` 子句导致显示推断的终止注释。
可以使用提供的建议或代码操作将其自动添加到源文件中。

为了避免尝试所有度量元组的组合爆炸，Lean 首先将所有 {tech}[基本终止度量] 制成表格，确定基本度量是递减、严格递减还是非递减。
递减测度至少对于一次递归调用来说较小，并且在任何递归调用中都不会增加，而严格递减测度对于所有递归调用都较小。
非递减度量是终止策略无法显示递减或严格递减的度量。
根据表选择合适的元组。{margin}[此方法基于 {citehere bulwahn2007}[]。]
当找不到自动测量值时，此表会显示在错误消息中。

{spliceContents ManualZh.RecursiveDefs.WF.GuessLexExample}

```lean -show
section
variable {e₁ e₂ i j : Nat}
```
:::example "Array Indexing"

将 {lean}`e₂ - e₁` 形式的表达式视为度量的目的是支持计数到某个上限的常见习惯用法，特别是在以可能有趣的方式遍历数组时。
在以下对排序数组执行二分搜索的函数中，此启发式帮助 Lean 查找 {lean}`j - i` 度量。

```lean (name := binarySearch)
def binarySearch (x : Int) (xs : Array Int) : Option Nat :=
  go 0 xs.size
where
  go (i j : Nat) (hj : j ≤ xs.size := by omega) :=
    if h : i < j then
      let mid := (i + j) / 2
      let y := xs[mid]
      if x = y then
        some mid
      else if x < y then
        go i mid
      else
        go (mid + 1) j
    else
      none
  termination_by?
```

事实上，推断终止参数使用某种任意度量，而不是最佳或最小度量，这一事实在推断度量中可见，其中包含冗余的 `j`：
```leanOutput binarySearch
Try this:
  [apply] termination_by (j, j - i)
```

:::

```lean -show
end
```

:::example "Termination Proof Tactics During Inference"

在推断终止 {tech}[measure] 时，{keywordOf Lean.Parser.Command.declaration}`decreasing_by` 指示的策略的使用方式与实际终止证明中的使用方式略有不同。

* 在推理过程中，它应用于_单个_目标，尝试在 {name}`Nat` 上证明 {name LT.lt}`<` 或 {name LE.le}`≤`。
* 在终止证明期间，它应用于许多同时目标（每个递归调用一个），并且目标可能涉及对的字典顺序。

结果是，单独解决目标并使用显式终止参数成功工作的 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 块可能会导致终止措施的推断失败：

```lean -keep +error
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    omega
  · apply Prod.Lex.left
    omega
```

每当给出显式 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 证明时，建议始终包含 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句。

:::

:::example "Inference too powerful"

由于 {tactic}`decreasing_tactic` 避免了由于字典排序不完整而需要回溯，因此 Lean 可能会推断出终止 {tech}[measure]，从而导致策略无法证明的目标。
在这种情况下，错误消息是由于策略失败而导致的错误消息，而不是由于无法找到度量而导致的错误消息。
这是 {lean}`notAck` 中发生的情况：

```lean +error (name := badInfer)
def notAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => notAck m 1
  | m + 1, n + 1 => notAck m (notAck (m / 2 + 1) n)
decreasing_by all_goals decreasing_tactic
```
```leanOutput badInfer
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
m n : Nat
⊢ m / 2 + 1 < m + 1
```

在这种情况下，明确声明终止 {tech}[measure] 会有所帮助。

:::

# 相互良基递归
%%%
tag := "mutual-well-founded-recursion"
%%%

Lean 支持使用 {tech}[良基递归] 定义 {tech}[互递归]函数。
可以使用 {tech}[mutual block] 引入相互递归，但它也可以由 {keywordOf Lean.Parser.Term.letrec}`let rec` 表达式和 {keywordOf Lean.Parser.Command.declaration}`where` 块产生。
相互良基递归的规则应用于一组实际相互递归、提升的定义，这些定义由相互组的 {ref "mutual-syntax"}[精化步骤] 产生。

如果交互组中的任何函数具有 {keywordOf Lean.Parser.Command.declaration}`termination_by` 或 {keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句，则尝试使用良基递归。
如果使用 {keywordOf Lean.Parser.Command.declaration}`termination_by` 为交互组中的 _any_ 函数指定终止 {tech}[measure]，则该组中的 _all_ 函数必须指定终止测量，并且它们必须具有相同的类型。

如果未指定终止参数，则终止参数为 {ref "inferring-well-founded-recursion"}[推断，如上所述]。在相互递归的情况下，在推理过程中考虑第三类基本度量，即对于相互组中的每个函数，该函数的度量为 `1`，其他函数的度量为 `0`。这允许 Lean 对函数进行排序，以便即使参数不减少，也允许从一个函数到另一个函数的某些调用。

:::example "Mutual recursion without parameter decrease"

在以下互函数定义中，从 {lean}`g` 到 {lean}`f` 的调用中参数不会减少。
尽管如此，由于附加基本措施对功能本身强加了顺序，因此该定义被接受。

```lean (name := fg)
mutual
  def f : (n : Nat) → Nat
    | 0 => 0
    | n + 1 => g n
  termination_by?

  def g (n : Nat) : Nat := (f n) + 1
  termination_by?
end
```

{lean}`f` 的推断终止参数为：
```leanOutput fg
Try this:
  [apply] termination_by n => (n, 0)
```

{lean}`g` 的推断终止参数为：
```leanOutput fg
Try this:
  [apply] termination_by (n, 1)
```

:::

# 预处理函数定义
%%%
tag := "well-founded-preprocessing"
%%%

Lean 在确定每个调用站点的证明义务之前_预处理_函数的主体，将其转换为可能包含附加信息的等效定义。
此预处理步骤主要用于通过附加假设来丰富本地上下文，这些假设可能是解决终止证明义务所必需的，从而使用户无需手动执行等效转换。
预处理使用 {ref "the-simplifier"}[简化器]，并且可由用户扩展。

:::paragraph

预处理分三个步骤进行：

1.  Lean 使用 {name}`wfParam` {tech}[gadget] 注释函数参数或参数子项的出现。

    ```signature
    wfParam {α} (a : α) : α
    ```

    更准确地说，函数参数的每次出现都包含在 {name}`wfParam` 中。
    每当 {keywordOf Lean.Parser.Term.match}`match` 表达式将 _any_ 判别式包装在 {name}`wfParam` 中时，该小工具就会被删除，并且每次出现的模式匹配变量（无论它是否来自 {name}`wfParam` 小工具的判别式）都会包装在 {name}`wfParam` 中。
    {name}`wfParam` 设备也从 {tech}[投影功能] 应用程序中浮出。

2.  带注释的函数体使用 {ref "the-simplifier"}[简化器] 进行简化，仅使用 {attr}`wf_preprocess` {tech}[自定义 simp 集] 中的简化规则。

3.  最后，删除所有剩余的 {name}`wfParam` 标记。

注释用于良基递归的函数参数允许预处理简化规则区分参数和其他术语。
:::

:::syntax attr (title := "Preprocessing Simp Set for Well-Founded Recursion")
```grammar
wf_preprocess
```

{includeDocstring Lean.Parser.Attr.wf_preprocess}

:::

{docstring wfParam}

{attr}`wf_preprocess` simp 集中的一些重写规则通常适用，无需注意 {lean}`wfParam` 标记。
特别是，定理 {name}`ite_eq_dite` 用于扩展 {ref "if-then-else"}[if-then-else] 表达式分支的上下文，并带有有关条件的假设：{margin}[此假设的名称应该是基于 `h` 的不可访问名称，如使用 {name}`binderNameHint` 和术语所示{lean}`()`。活页夹名称提示在 {ref "bound-variable-name-hints"}[策略语言参考]中进行了描述。]

```signature
ite_eq_dite {P : Prop} {α : Sort u} {a b : α} [Decidable P]  :
  (if P then a else b) =
  if h : P then
    binderNameHint h () a
  else
    binderNameHint h () b
```


```lean -show
section
variable (xs : List α) (p : α → Bool) (f : α → β) (x : α)
```

:::paragraph

其他重写规则使用 {name}`wfParam` 标记来限制其适用性；它们仅在将函数（如 {name}`List.map`）应用于参数或参数的子项时使用，否则不使用。
这通常分两步完成：

1.  诸如 {name}`List.map_wfParam` 之类的定理识别对函数参数（或子项）的 {name}`List.map` 调用，并使用 {name}`List.attach` 来丰富列表元素的类型，断言它们确实是该列表的元素：

    ```signature
    List.map_wfParam (xs : List α) (f : α → β) :
      (wfParam xs).map f = xs.attach.unattach.map f
    ```
2. {name}`List.map_unattach` 等定理使得该断言可用于 {name}`List.map` 的函数参数。

    ```signature
    List.map_unattach (P : α → Prop)
      (xs : List { x : α // P x }) (f : α → β) :
      xs.unattach.map f = xs.map fun ⟨x, h⟩ =>
        binderNameHint x f <|
        binderNameHint h () <|
        f (wfParam x)
    ```

  如果 {lean}`f` 是 lambda 表达式，则该定理使用 {name}`binderNameHint` 小工具来保留用户选择的绑定程序名称。

通过将 {name}`List.attach` 的引入与引入的假设的传播分开，即使在 `(xs.reverse.filter p).map f` 等链中，也可以为 {lean}`f` 提供所需的 {lean}`x ∈ xs` 假设。

:::

```lean -show
end
```

可以通过将选项 {option}`wf.preprocess` 设置为 {lean}`false` 来禁用此预处理。
要查看删除 {name}`wfParam` 标记之前和之后的预处理函数定义，请将选项 {option}`trace.Elab.definition.wf` 设置为 {lean}`true`。

{optionDocs trace.Elab.definition.wf}

{spliceContents ManualZh.RecursiveDefs.WF.PreprocessExample}

# 理论与构建
%%%
tag := "zh-recursivedefs-wf-h007"
%%%

```lean -show
section
variable {α : Type u}
```

本节通过 {tech}[良基递归] 非常简要地介绍了终止证明背后的数学结构，这些数学结构有时可能会出现。
良基递归定义的函数精化基于 {name}`WellFounded.fix` 运算符。

{docstring WellFounded.fix}

类型 {lean}`α` 使用函数的（变化的）参数进行实例化，并使用 {name}`PSigma` 打包为一种类型。
{name}`WellFounded` 关系是通过 {name}`invImage` 从终结点 {tech}[measure] 构建的。

{docstring invImage}

The function's body is passed to {name}`WellFounded.fix`, with parameters suitably packed and unpacked, and recursive calls are replaced with a call to the value provided by {name}`WellFounded.fix`.
{keywordOf Lean.Parser.Command.declaration}`decreasing_by`策略生成的终止证明插入到正确的位置。

最后，由{name}`WellFounded.fix_eq`证明了递归函数的方程和展开定理。
这些定理隐藏了打包和解包参数的细节，并根据原始定义描述了函数的行为。

在互递归的情况下，通过使用 {name}`PSum` 组合函数的参数，并在结果类型和主体中对该和类型进行模式匹配，可以构造等效的非互函数。

{name}`WellFounded` 的定义建立在关系的_可访问元素_的概念之上：

{docstring WellFounded}

{docstring Acc}

::: example "Division by Iterated Subtraction: Termination Proof"

迭代减法除法的定义可以使用良基递归显式编写。
```lean
noncomputable def div (n k : Nat) : Nat :=
  (inferInstance : WellFoundedRelation Nat).wf.fix
    (fun n r =>
      if h : k = 0 then 0
      else if h : k > n then 0
      else 1 + (r (n - k) <| by
        show (n - k) < n
        omega))
    n
```
该定义必须标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable`，因为编译器不支持良基递归。
与 {tech}[recursors] 一样，它是 Lean 逻辑的一部分。

除法的定义应满足以下方程：
 * {lean}`∀{n k : Nat}, (k = 0) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k > n) → div n k = 0`
 * {lean}`∀{n k : Nat}, (k ≠ 0) → (¬ k > n) → div n k = 1 + div (n - k) k`

这种归约行为不支持 {tech (key := "definitional equality")}[定义]：
```lean +error (name := nonDef) -keep
theorem div.eq0 : div n 0 = 0 := by rfl
```
```leanOutput nonDef
Tactic `rfl` failed: The left-hand side
  div n 0
is not definitionally equal to the right-hand side
  0

n : Nat
⊢ div n 0 = 0
```
然而，使用 `WellFounded.fix_eq` 展开良基递归，可以证明三个方程成立：
```lean
theorem div.eq0 : div n 0 = 0 := by
  unfold div
  apply WellFounded.fix_eq

theorem div.eq1 : k > n → div n k = 0 := by
  intro h
  unfold div
  rw [WellFounded.fix_eq]
  simp only [gt_iff_lt, dite_eq_ite, ite_eq_left_iff, Nat.not_lt]
  intros; omega

theorem div.eq2 :
    ¬ k = 0 → ¬ (k > n) →
    div n k = 1 + div (n - k) k := by
  intros
  unfold div
  rw [WellFounded.fix_eq]
  simp_all only [
    gt_iff_lt, Nat.not_lt,
    dite_false, dite_eq_ite,
    ite_false, ite_eq_right_iff
  ]
  omega
```
:::
