/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`propRecLargeElim`" =>
%%%
tag := "zh-errorexplanations-propreclargeelim-root"
shortTitle := "propRecLargeElim"
%%%

{errorExplanationHeader lean.propRecLargeElim}


当试图将命题的证明消除到更高类型的宇宙中时，会发生此错误。
由于 Lean 的 类型论 不允许从 {lean}`Prop` 进行大量消除，因此无效
对此类值进行模式匹配- 例如，通过使用 {keywordOf Lean.Parser.Term.let}`let` 或
{keywordOf Lean.Parser.Term.match}`match`—在非命题宇宙中产生一条数据
（即 `Type u`）。更准确地说，命题递归器的动机必须是一个命题。
（有关例外情况，请参阅手册中有关 {ref "subsingleton-elimination"}[Subsingleton Elimination] 的部分
遵守此规则。）

请注意，任何将证明消除为证明的表达式都会出现此错误
非命题宇宙，即使该表达式出现在另一个表达式中
命题类型（例如，在证明中的 {keywordOf Lean.Parser.Term.let}`let` 绑定中）。的
下面的“在证明中定义中间数据值”示例演示了这种情况。
此类错误通常可以通过将递归应用程序“向外”移动来解决，以便
它的动机是被证明的命题而不是数据值术语的类型。

# 示例
%%%
tag := "zh-errorexplanations-propreclargeelim-h001"
%%%

:::errorExample "Defining an Intermediate Data Value Within a Proof"
```broken
example {α : Type} [inst : Nonempty α] (p : α → Prop) :
    ∃ x, p x ∨ ¬ p x :=
  let val :=
    match inst with
    | .intro x => x
  ⟨val, Classical.em (p val)⟩
```
```output
Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Nonempty.casesOn` can only eliminate into `Prop`

α : Type
motive : Nonempty α → Sort ?u.48
h_1 : (x : α) → motive ⋯
inst✝ : Nonempty α
⊢ motive inst✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
```fixed
example {α : Type} [inst : Nonempty α] (p : α → Prop) :
    ∃ x, p x ∨ ¬ p x :=
  match inst with
  | .intro x => ⟨x, Classical.em (p x)⟩
```
尽管定义的 {keywordOf Lean.Parser.Command.example}`example` 有一个命题
类型，`val` 的主体没有；它的类型为 `α : Type`。因此，证明上的模式匹配
`Nonempty α`（一个命题）生成 `val` 需要将该证明消除为
非命题类型，是不允许的。相反，{keywordOf Lean.Parser.Term.match}`match`
表达式必须移至 `example` 的顶层，其中结果是
示例标题中所述存在性命题的 {lean}`Prop` 值证明。这个
重组也可以使用模式匹配{keywordOf Lean.Parser.Term.let}`let` 来完成
绑定。
:::

:::errorExample "Extracting the Witness from an Existential Proof"

```broken
def getWitness {α : Type u} {p : α → Prop} (h : ∃ x, p x) : α :=
  match h with
  | .intro x _ => x
```
```output
Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`

α : Type u
p : α → Prop
motive : (∃ x, p x) → Sort ?u.52
h_1 : (x : α) → (h : p x) → motive ⋯
h✝ : ∃ x, p x
⊢ motive h✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
```
```fixed "in Prop"
-- This is `Exists.elim`
theorem useWitness {α : Type u} {p : α → Prop} {q : Prop}
    (h : ∃ x, p x) (hq : (x : α) → p x → q) : q :=
  match h with
  | .intro x hx => hq x hx
```
```fixed "in Type"
def getWitness {α : Type u} {p : α → Prop}
    (h : (x : α) ×' p x) : α :=
  match h with
  | .mk x _ => x
```
在这个例子中，简单地重新定位模式匹配是不够的；尝试的定义
`getWitness` 根本上是不健全的。 （考虑 `p` 的情况
{lean}`fun (n : Nat) => n > 0`：如果 `h` 和 `h'` 是 {lean}`∃ x, x > 0` 的证明，其中 `h` 使用
证人 `1` 和 `h'` 证人 `2`，则由于 `h = h'` 通过证明无关性，得出结论：
`getWitness h = getWitness h'`—即 `1 = 2`。）

相反，必须重写 `getWitness`：函数的结果类型必须是
命题（上面的第一个固定示例），或者 `h` 一定不是命题（第二个）。

在第一个更正的示例中，`useWitness` 的结果类型现在是命题 `q`。这个
允许我们在 `h` 上进行模式匹配（因为我们要消除为命题类型）并传递
解压后的值为 `hq`。从程序化的角度来看，可以将 `useWitness` 视为重写
`getWitness` 采用连续传递风格，限制后续计算使用其结果
仅根据禁止命题大的要求在 {lean}`Prop` 中构造值
消除。请注意，`useWitness` 是存在消除原理 {name}`Exists.elim`。

第二个更正的示例将 `h` 的类型从存在命题更改为
{lean}`Type` 值依赖对（对应于 {name}`PSigma` 类型构造函数）。自从
该类型不是命题，消去 `α : Type u` 不再无效，并且
以前尝试的模式匹配现在进行类型检查。
:::
