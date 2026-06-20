/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean Lean.Grind Lean.Meta.Grind


#doc (Manual) "约束传播" =>
%%%
file := "Constraint-Propagation"
tag := "grind-propagation"
%%%

{deftech (key := "Constraint propagation")}[约束传播] 适用于白板的 {lean}`True` 和 {lean}`False` 存储桶。
每当将术语添加到其中一个存储桶时，{tactic}`grind` 都会触发数十个小型 {deftech (key := "forward rules")}_forward 规则_，这些规则从其逻辑结果中获取更多信息：

: 布尔连接词

  ::::leanSection
  ```lean -show
  variable {A B : Prop}
  ```
  :::paragraph
  布尔连接词的真值表可用于导出进一步的真假事实。
  例如：
   * 如果 {lean}`A` 为 {lean}`True`，则 {lean}`A ∨ B` 变为 {lean}`True`。
   * 如果 {lean}`A ∧ B` 为 {lean}`True`，则 {lean}`A` 和 {lean}`B` 均变为 {lean}`True`。
   * 如果{lean}`A ∧ B`是{lean}`False`，则{lean}`A`、{lean}`B`中的至少一个变为{lean}`False`。
  :::
  ::::

: 归纳类型

  如果将同一 {tech (key := "inductive type")}[归纳类型] 的两个不同构造函数（例如 {name}`none` 和 {name}`some`）的应用所形成的项置于同一等价类中，则会产生矛盾。
  如果由同一构造函数的应用形成的两个项被放置在同一等价类中，则它们的参数也相等。

: 预测
  :::leanSection
  ```lean -show
  variable {x x' : α} {y y' : β} {h : (x, y) = (x', y')} {a : α}
  ```

  从 {typed}`h : (x, y) = (x', y')` 中我们得出 {lean}`x = x'` 和 {lean}`y = y'`。
  :::

: 演员阵容

  :::leanSection
  ```lean -show
  variable {h : α = β} {a : α}
  ```
  任何术语 {typed}`cast h a : β` 都立即与 {typed}`a : α` 等同（使用 {tech (key := "heterogeneous equality")}[异构相等]）。
  :::

: 减少

  ::::keepEnv
  :::leanSection
  ```lean -show
  variable {α : Type u} {β : Type v} {a : α} {b : β}
  structure S α β where
    x : α
    y : β
  variable {p : S α β}
  ```
  定义归约被传播，因此 {lean}`(a, b).1` 等同于 {lean}`a`。
  :::
  ::::

:::paragraph
下面是传播者的_代表性切片_，展示了它们的整体风格。
每个都遵循相同的骨架。

1. 它检查子表达式的真值。

2. 如果可以导出进一步的事实，它可以使用 ({lean}`pushEq`) 使术语相等（在隐喻白板上连接它们），或者使用 ({lean}`pushEqTrue` / {lean}`pushEqFalse`) 指示真值。
   这些步骤使用内部辅助引理（例如 {name}`Grind.and_eq_of_eq_true_left`）生成证明项。

3. 如果出现矛盾，则使用 ({lean}`closeGoal`) 关闭目标。

{deftech (key := "Upward propagation")}_向上传播_从有关子项的事实导出有关项的事实，而{deftech (key := "downward propagation")}_向下传播_从有关项的事实导出有关子项的事实。
:::

```lean -show
namespace ExamplePropagators
```
```lean -keep

/-- Propagate equalities *upwards* for conjunctions. -/
builtin_grind_propagator propagateAndUp ↑And := fun e => do
  let_expr And a b := e | return ()
  if (← isEqTrue a) then
    -- a = True  ⇒  (a ∧ b) = b
    pushEq e b <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_left)
        a b (← mkEqTrueProof a)
  else if (← isEqTrue b) then
    -- b = True  ⇒  (a ∧ b) = a
    pushEq e a <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_true_right)
        a b (← mkEqTrueProof b)
  else if (← isEqFalse a) then
    -- a = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_left)
        a b (← mkEqFalseProof a)
  else if (← isEqFalse b) then
    -- b = False  ⇒  (a ∧ b) = False
    pushEqFalse e <|
      mkApp3 (mkConst ``Grind.and_eq_of_eq_false_right)
        a b (← mkEqFalseProof b)

/--
Truth flows *down* when the whole `And` is proven `True`.
-/
builtin_grind_propagator propagateAndDown ↓And :=
  fun e => do
  if (← isEqTrue e) then
    let_expr And a b := e | return ()
    let h ← mkEqTrueProof e
    -- (a ∧ b) = True  ⇒  a = True
    pushEqTrue a <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_left) a b h
    -- (a ∧ b) = True  ⇒  B = True
    pushEqTrue b <| mkApp3
      (mkConst ``Grind.eq_true_of_and_eq_true_right) a b h
```
```lean -show
end ExamplePropagators
```



其他频繁触发的传播器遵循相同的模式：

::::leanSection
```lean -show
variable {A B : Prop} {a b : α}
```

:::table +header
*
  * 传播者
  * 手柄
  * 注释
*
  * {lean}`propagateOrUp` / {lean}`propagateOrDown`
  * {lean}`A ∨ B`
  * 使用真值表进行析取以导出进一步的真值
*
  * {lean}`propagateNotUp` / {lean}`propagateNotDown`
  * {lean}`¬ A`
  * 确保 {lean}`¬ A` 和 {lean}`A` 具有相反的真值
*
  * {lean}`propagateEqUp` / {lean}`propagateEqDown`
  * `a = b`
  * 桥接布尔值，检测构造函数冲突 {TODO}[“桥接布尔值”是什么意思？找出来]
*
  * {lean}`propagateIte` / {lean}`propagateDIte`
  * {name}`ite` / {name}`dite`
  * 一旦条件的真值已知，则将该项与所选分支等同
*
  * `propagateEtaStruct`
  * 标记为 `[grind ext]` 的结构的值
  * 生成 η 展开式 `a = ⟨a.1, …⟩`
:::
::::

:::comment
TODO (@kim-em)：我们不添加上面的 `{lean}` literal type to `propagateEtaStruct`，因为它是私有的。
:::

{lean}`Bool` 的许多专门变体完全反映了这些规则（例如 {lean}`propagateBoolAndUp`）。

# 仅传播示例
%%%
file := "Propagation___Only-Examples"
tag := "zh-grind-constraintpropagation-h001"
%%%

这些目标“纯粹”通过约束传播来封闭——没有案例分割，没有理论求解器：

```lean
-- Boolean connective: a && !a is always false.
example (a : Bool) : (a && !a) = false := by
  grind

-- Conditional (ite):
-- once the condition is true, ite picks the 'then' branch.
example (c : Bool) (t e : Nat) (h : c = true) :
    (if c then t else e) = t := by
  grind

-- Negation propagates truth downwards.
example (a : Bool) (h : (!a) = true) : a = false := by
  grind
```

这些片段会立即运行，因为一旦假设被内化，相关传播器（{lean}`propagateBoolAndUp`、{lean}`propagateIte`、{lean}`propagateBoolNotDown`）就会立即触发。
将选项 {option}`trace.grind.eqc` 设置为 {lean}`true` 会导致 {tactic}`grind` 每次两个等价类合并时打印一行，这对于查看实际传播非常方便。


:::TODO

执行该命令时，应取消此部分的注释：

```lean -show
-- Test to ensure that this section is uncommented when the command is implemented
/--
error: elaboration function for `Lean.Parser.«command_Grind_propagator___(_):=_»` has not been implemented
-/
#guard_msgs in
grind_propagator ↑x(y) := _
```

{tactic}`grind` 仍在积极开发中，其实现可能会发生变化。
在 API 稳定之前，我们建议_不要编写自定义精化器或卫星求解器_。
如果确实需要项目本地自定义传播器，则应使用 {keywordOf «command_Grind_propagator___(_):=_»}`grind_propagator` 命令定义它，而不是 {keywordOf «command_Builtin_grind_propagator____:=_»}`builtin_grind_propagator` （后者是为 Lean 自己的代码保留的）。
添加新的传播器时，请保持它们“小且正交”——它们应该在 ≤1μs 内触发，要么推动一个事实，要么关闭目标。
这使得传播阶段可预测且易于调试。
:::

传播规则集随着时间的推移而扩展和完善，因此 InfoView 将显示越来越丰富的 {lean}`True` 和 {lean}`False` 存储桶。
完整的等价类仅在 {tactic}`grind` 失败时自动显示，并且仅针对无法关闭的第一个子目标 - 使用此输出来检查缺失的事实并了解子目标保持打开状态的原因。

:::example "Identifying Missing Facts"
在此示例中，{tactic}`grind` 失败：

```lean +error (name := missing)
example :
    x = y ∧ y = z →
    w = x ∨ w = v →
    w = z := by
  grind
```
生成的错误消息包括已识别的等价类以及真命题和假命题：
```leanOutput missing (expandTrace := eqc)
`grind` failed
case grind
α : Sort u_1
x y z w v : α
left : x = y
right : y = z
h_1 : w = x ∨ w = v
h_2 : ¬w = z
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] w = x ∨ w = v
    [prop] w = v
  [eqc] False propositions
    [prop] w = x
    [prop] w = z
  [eqc] Equivalence classes
    [eqc] {x, y, z}
    [eqc] {w, v}
```
`x = y` 和 `y = z` 都是通过来自 `x = y ∧ y = z` 前提的约束传播发现的。
在此证明中，{tactic}`grind` 对 `w = x ∨ w = v` 执行案例拆分。
在第二个分支中，它无法将 `w` 和 `z` 置于同一等价类中。
:::
