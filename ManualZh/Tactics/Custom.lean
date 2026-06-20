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

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
set_option verso.docstring.allowMissing true

open Lean.Elab.Tactic

#doc (Manual) "定制策略" =>
%%%
file := "Custom-Tactics"
tag := "custom-tactics"
%%%


```lean -show
open Lean
```

策略是语法类别 `tactic` 中的产品。 {TODO}[语法的外部引用宏\_cats]
给定策略的语法，策略解释器负责执行策略单子 {name}`TacticM` 中的操作，它是 Lean 的术语精化器的包装器，用于跟踪执行所需的附加状态策略。
自定义策略包含 `tactic` 类别的扩展以及：
 * 将新语法转换为现有语法的 {tech (key := "macro")}[宏]，或者
 * 执行 {name}`TacticM` 操作以实现策略的精化器。

# 策略宏
%%%
file := "Tactic-Macros"
tag := "tactic-macros"
%%%

定义新策略的最简单方法是将 {tech (key := "macro")}[宏] 扩展为已存在的策略。
宏展开与策略交错执行。
策略解释器首先在解释策略宏之前对其进行扩展。
由于策略宏在运行策略脚本之前未完全展开，因此它们可以使用递归；只要宏语法的递归出现位于可执行的策略之下，就不会有无限的扩展链。

::::keepEnv
:::example "Recursive tactic macro"
类似于 {tactic}`repeat` 的策略的递归实现是通过宏展开定义的。
当参数 `$t` 失败时，永远不会调用 {tactic}`rep` 的递归发生，因此永远不会进行宏扩展。
```lean
syntax "rep" tactic : tactic
macro_rules
  | `(tactic|rep $t) =>
  `(tactic|
    first
      | $t; rep $t
      | skip)

example : 0 ≤ 4 := by
  rep (apply Nat.le.step)
  apply Nat.le.refl
```
:::
::::

与其他 Lean 宏一样，策略宏是 {tech (key := "hygiene")}[卫生]。
对全局名称的引用在定义宏时解析，并且策略宏引入的名称无法从其调用站点捕获名称。

定义策略宏时，指定匹配或构造的语法适用于语法类别 `tactic` 非常重要。
否则，语法将被解释为术语的语法，这将与策略匹配或构造不正确的 AST。

## 可扩展策略宏
%%%
file := "Extensible-Tactic-Macros"
tag := "tactic-macro-extension"
%%%


由于宏展开可能会失败，因此 {TODO}[xref] 多个宏可以匹配相同的语法，从而允许回溯。
策略宏更进一步：即使策略宏扩展成功，如果在解释时扩展失败，策略解释器将尝试下一次扩展。
这用于使许多 Lean 的内置策略可扩展 — 可以通过添加 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明将新行为添加到策略。

::::keepEnv
:::example "Extending {tactic}`trivial`"

{tactic}`trivial` 被许多其他策略用于快速调度不值得打扰用户的子目标，旨在通过新的宏扩展进行扩展。
Lean 的默认 {lean}`trivial` 无法解决 {lean}`IsEmpty []` 目标：
```lean
def IsEmpty (xs : List α) : Prop :=
  ¬ xs ≠ []
```
```lean +error
example (α : Type u) : IsEmpty (α := α) [] := by trivial
```

该错误消息是 {tactic}`trivial` 最后尝试 {tactic}`assumption` 的产物。
添加另一个扩展允许 {tactic}`trivial` 实现以下目标：
```lean
def emptyIsEmpty : IsEmpty (α := α) [] := by simp [IsEmpty]

macro_rules | `(tactic|trivial) => `(tactic|exact emptyIsEmpty)

example (α : Type u) : IsEmpty (α := α) [] := by
  trivial
```
:::
::::

::::keepEnv
:::example "Expansion Backtracking"
当扩展语法的任何部分出现故障时，宏展开可能会导致回溯。
可以通过在单独的 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明中提供多个扩展来定义 {tactic}`first` 的中缀版本：
```lean
syntax tactic "<|||>" tactic : tactic
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t1
macro_rules
  | `(tactic|$t1 <|||> $t2) => pure t2

example : 2 = 2 := by
  rfl <|||> apply And.intro

example : 2 = 2 := by
  apply And.intro <|||> rfl
```

需要多个 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明，因为每个声明都定义一个模式匹配函数，该函数始终采用第一个匹配替代项。
回溯是按 {keywordOf Lean.Parser.Command.macro_rules}`macro_rules` 声明的粒度进行的，而不是按个别情况进行。
:::
::::
