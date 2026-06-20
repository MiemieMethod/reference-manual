/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "公理" =>
%%%
tag := "axioms"
htmlSplit := .never
%%%
:::leanSection

```lean -show
universe u
```

{deftech}_Axioms_ 是假设常数。
虽然公理的类型本身必须是类型（即，它必须具有类型 {lean}`Sort u`），但没有其他要求。
公理不会 {tech (key := "reduction")}[简化]为其他项。
:::

在投入时间构建模型或证明定理之前，可以使用公理来试验某个想法的结果。
它们还可以用于采用 Lean 的 类型论 中无法访问的推理原理； Lean 本身提供了已知是一致的 {ref "standard-axioms"}[三个这样的公理]。
然而，应该谨慎使用公理：彼此不一致或完全错误的公理会破坏证明的基础。
Lean 自动跟踪每个证明所依赖的公理，以便对其进行审核。

# 公理声明
%%%
tag := "axiom-declarations"
%%%

Axioms 声明包括名称和类型：

:::syntax Lean.Parser.Command.axiom (title := "Axiom Declarations")
```grammar
axiom $_ $_
```
:::

Axioms 声明可以使用所有可能的 {ref "declaration-modifiers"}[声明修饰符] 进行修改。
文档注释、属性、{keyword}`private` 和 {keyword}`protected` 与其他声明具有相同的含义。
修饰符 {keyword}`partial`、{keyword}`nonrec`、{keyword}`noncomputable` 和 {keyword}`unsafe` 无效。

# 一致性
%%%
tag := "axiom-consistency"
%%%

使用公理是有风险的。
因为它们引入了任何类型的新常量，并且命题类型的居民算作命题的证明，所以公理甚至可以用来证明假命题。
任何依赖于公理的证明只有在该公理既真实又与所使用的其他公理一致的情况下才可以被信任。
就其本质而言，Lean 无法检查新公理是否一致；添加公理时请小心。

:::example "Inconsistencies From Axioms"
公理可能单独或与其他公理结合引入不一致。

假设一个错误的陈述允许任何陈述被证明：
```lean
axiom false_is_true : False

theorem two_eq_five : 2 = 5 := false_is_true.elim
```

与 Lean 的其他属性不兼容的公理也可能引起不一致。
例如，参数性在支持它的语言中使用时是一种强大的推理技术，但它与 Lean 的标准公理不兼容。
如果参数性成立，那么 Wadler 的 [_Theorems for Free_](https://dl.acm.org/doi/pdf/10.1145/99370.99404) (1989) 介绍中的“自由定理”将是正确的，该定理描述了一种使用参数性推导有关多态函数的定理的技术。
作为一条公理，它写道：
```lean
axiom List.free_theorem {α β}
  (f : {α : _} → List α → List α) (g : α → β) :
  f ∘ (List.map g) = (List.map g) ∘ f
```
然而，排中的结果是所有命题都是可判定的；这意味着函数可以_检查_它们是真还是假。
这个函数无法编译，但它仍然存在。
这可用于定义非参数的多态函数：
```lean
open Classical in
noncomputable def nonParametric
    {α : _} (xs : List α) :
    List α :=
  if α = Nat then [] else xs
```
这个函数的存在与“自由定理”相矛盾：
```lean
theorem unit_not_nat : Unit ≠ Nat := by
  intro eq
  have ⟨allEq⟩ := eq ▸ (inferInstance : Subsingleton Unit)
  specialize allEq 0 1
  contradiction

example : False := by
  have := List.free_theorem nonParametric (fun () => 42)

  unfold nonParametric at this
  simp [unit_not_nat] at this

  have := congrFun this [()]
  contradiction
```
:::

# 减少
%%%
tag := "axiom-reduction"
%%%

即使一致的公理也会造成困难。
{tech (key := "Definitional equality")}[定义等价] 标识项模归约规则。
{tech}[ι-reduction]规则指定了递归器和构造函数的交互；因为公理不是构造函数，所以它不适用于它们。
通常，没有自由变量的项会简化为构造函数的应用，但公理可能会导致它们“卡住”，从而导致项很大。

:::example "Axioms and Stuck Reduction"
使用公理向 {lean}`Nat` 添加额外的 `0` 会导致一些定义归约陷入困境。
在此示例中，两个 {name}`Nat.succ` 构造函数通过归约成功移至项外，但 {name}`Nat.rec` 在遇到 {lean}`Nat.otherZero` 后无法取得进一步的进展。
```lean (name := otherZero)
axiom Nat.otherZero : Nat

#reduce 4 + (Nat.otherZero + 2)
```
```leanOutput otherZero
((Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) Nat.otherZero).1 4).succ.succ
```
:::

此外，Lean 编译器无法生成公理代码。
在运行时，Lean 值必须由内存中的具体数据表示，但公理没有具体表示。
包含依赖公理的非证明代码的定义必须标记为 {keyword}`noncomputable` 并且无法编译。

:::example "Axioms and Compilation"
使用公理向 {lean}`Nat` 添加额外的 `0` 会使使用它的函数无法编译。
特别是，{name}`List.length'` 返回公理 {name}`Nat.otherZero` 而不是 {name}`Nat.zero` 作为空列表的长度。
```lean (name := otherZero2) +error
axiom Nat.otherZero : Nat

def List.length' : List α → Nat
  | [] => Nat.otherZero
  | _ :: _ => xs.length
```
```leanOutput otherZero2
`Nat.otherZero` not supported by code generator; consider marking definition as `noncomputable`
```

在证明中而不是在程序中使用的公理不会阻止函数的编译。
编译器不会生成证明代码，因此证明中的公理没有问题。
{lean}`nextOdd` 从 {lean}`Nat` 计算下一个奇数，该奇数可以是数字本身或更大的数字：
```lean
def nextOdd (k : Nat) :
    { n : Nat // n % 2 = 1 ∧ (n = k ∨ n = k + 1) } where
  val := if k % 2 = 1 then k else k + 1
  property := by
    by_cases k % 2 = 1 <;>
    simp [*] <;> omega
```
策略证明生成一个传递依赖于三个公理的项：
```lean (name:=printAxNextOdd)
#print axioms nextOdd
```
```leanOutput printAxNextOdd
'nextOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
```
因为它们只出现在证明中，所以编译器生成代码没有问题：
```lean (name := evalNextOdd)
#eval (nextOdd 4, nextOdd 5)
```
```leanOutput evalNextOdd
(5, 5)
```
:::

# 标准公理
%%%
tag := "standard-axioms"
%%%

Lean 中有七个标准公理。前三个公理是 Lean 中数学计算方式的重要部分：
 * ```signature
   Classical.choice.{u} {α : Sort u} : Nonempty α → α
   ```
 * ```signature
   propext {a b : Prop} : (a ↔ b) → a = b
   ```
 * ```signature
   Quot.sound.{u} {α : Sort u}
     {r : α → α → Prop} {a b : α} :
     r a b → Quot.mk r a = Quot.mk r b
   ```

All three of these axioms are discussed in the book [Theorem Proving in Lean](https://lean-lang.org/theorem_proving_in_lean4/find/?domain=Verso.Genre.Manual.section&name=axioms-and-computation).

The axiom {name}`sorryAx` is used as part of the implementation of the {tactic}`sorry` tactic and {lean}`sorry` term.
Uses of this axiom are not intended to occur in finished proofs, as it can be used to prove anything:
 * ```signature
   sorryAx {α : Sort u} (synthetic := true) : α
   ```

最后三个公理就其_数学_内容而言并不真正存在；从数学的角度来看，他们证明了一些微不足道的陈述：

 * ```signature
    Lean.trustCompiler : True
   ```

 * ```signature
    Lean.ofReduceBool (a b : Bool) : Lean.reduceBool a = b → a = b
   ```
 * ```signature
    Lean.ofReduceNat (a b : Nat) : Lean.reduceNat a = b → a = b
   ```

These axioms instead track proofs that depend on the correctness of the entire compiler, and not just on the much smaller {tech}`kernel`.

:::example "Creating and Tracking Proofs That Trust the Compiler"
The functions {name}`Lean.reduceBool` and {name}`Lean.reduceNat` can be invoked to have the compiler perform a calculation; this can greatly improve performance of implementations of proof by reflection.

```lean
def largeNumber : Nat := Lean.reduceNat (230_000 + 4_500 + 1_000_067)
```

The resulting term depends on the axiom {name}`Lean.trustCompiler` in order to track the fact that this calculation depends on the correctness of the compiler.

```lean (name := printAxExC1)
#print axioms largeNumber
```
```leanOutput printAxExC1
'largeNumber' depends on axioms: [Lean.trustCompiler]
```
:::

:::example "Axioms and the `native_decide` Tactic"
Instead of appealing to {name}`Lean.trustCompiler`, the {tactic}`native_decide` tactic creates a bespoke axiom for each invocation.
This allows each axiom to be audited for the precise statement that it proves.

```lean (name := printAxExC2)
def bigSum : (List.range 1_001).sum = 500_500 := by native_decide
#print axioms bigSum
```
```leanOutput printAxExC2
'bigSum' depends on axioms: [bigSum._native.native_decide.ax_1]
```

The axiom's type can be checked directly:
```lean (name := printAxExC3)
#check bigSum._native.native_decide.ax_1
```
```leanOutput printAxExC3
bigSum._native.native_decide.ax_1 : decide ((List.range 1001).sum = 500500) = true
```
:::

# Displaying Axiom Dependencies
%%%
tag := "print-axioms"
%%%

The command {keywordOf Lean.Parser.Command.printAxioms}`#print axioms`, followed by a defined identifier, displays all the axioms that a definition transitively relies on.
In other words, if a proof uses another proof, which itself uses an axiom, then the axiom is reported by {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` for both.

::::keepEnv

This can be used to audit the assumptions made by a proof, for instance detecting that a proof transitively depends on the {tactic}`sorry` tactic.

```lean
def lazy : 4 == 2 + 1 + 1 := by sorry
```
```lean (name := printAxEx4)
#print axioms lazy
```
```leanOutput printAxEx4
'lazy' depends on axioms: [sorryAx]
```

:::example "Printing Axioms of Simple Definitions" (keep := true)

Consider the following three constants:

```lean
def addThree (n : Nat) : Nat := 1 + n + 2
theorem excluded_middle (P : Prop) : P ∨ ¬ P := Classical.em P
theorem simple_equality (P : Prop) : (P ∨ False) = P := or_false P
```

Regular functions like {lean}`addThree` that we might want to actually evaluation typically do not depend on any axioms:

```lean (name := printAxEx2)
#print axioms addThree
```
```leanOutput printAxEx2
'addThree' does not depend on any axioms
```

The excluded middle theorem is only true if we use classical reasoning, so the foundation for classical reasoning shows up alongside other axioms:

```lean (name := printAxEx1)
#print axioms excluded_middle
```
```leanOutput printAxEx1
'excluded_middle' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Finally, the idea that two equivalent propositions are equal directly relies on {tech}[propositional extensionality].

```lean (name := printAxEx3)
#print axioms simple_equality
```
```leanOutput printAxEx3
'simple_equality' depends on axioms: [propext]
```
:::

:::example "Using {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` with {keywordOf Lean.guardMsgsCmd}`#guard_msgs`"

You can use {keywordOf Lean.Parser.Command.printAxioms}`#print axioms`
together with {keywordOf Lean.guardMsgsCmd}`#guard_msgs` to ensure
that updates to libraries from other projects cannot silently
introduce unwanted dependencies on axioms.

For example, if the proof of {name}`double_neg_elim` below changed in such a way that it used more
axioms than those listed, then the {keywordOf Lean.guardMsgsCmd}`#guard_msgs` command would report an error.

```lean
theorem double_neg_elim (P : Prop) : (¬ ¬ P) = P :=
  propext Classical.not_not

/--
info: 'double_neg_elim' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms double_neg_elim

```
:::


::::
