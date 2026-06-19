/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`redundantMatchAlt`" =>
%%%
shortTitle := "redundantMatchAlt"
%%%

{errorExplanationHeader lean.redundantMatchAlt}

当永远无法达到模式匹配中的替代值时，就会发生此错误：任何可能会出现的值
匹配提供的模式也将匹配一些前面的替代方案。请参阅
{ref "pattern-matching"}[模式匹配] 手册部分了解更多详细信息
关于模式匹配。

此错误可能出现在任何模式匹配表达式中，包括
{keywordOf Lean.Parser.Term.match}`match` 表达式、方程函数定义、`if let`
绑定，以及带有后备子句的一元 {keywordOf Lean.Parser.Term.let}`let` 绑定。

在多臂模式匹配中，如果不太具体的模式出现在
它所包含的更具体的一项。请记住，表达式与来自的模式相匹配
从上到下，因此特定模式应先于通用模式。

在 {keywordOf termIfLet}`if let` 绑定和带有后备的一元 {keywordOf Lean.Parser.Term.let}`let` 绑定中
子句中，仅指定了一种模式，此错误表明指定的模式
总是会匹配的。在这种情况下，有问题的绑定可以替换为标准
模式匹配{keywordOf Lean.Parser.Term.let}`let`。

导致此错误的一个常见原因是用于匹配构造函数的模式是
相反，解释为变量绑定。例如，如果构造函数
名称（例如，`cons`）在该类型的命名空间之外写入时没有前缀（{name}`List`）。
默认情况下启用的构造函数名称作为变量 linter 将在任何变量上显示警告
类似于构造函数名称的模式。

此错误几乎总是表明出现该错误的代码存在问题。不过，如果需要的话，
`set_option match.ignoreUnusedAlts true` 将禁用对此错误的检查并允许模式
与通过丢弃未使用的臂来编译的冗余替代品进行匹配。

# 示例

:::errorExample "Incorrect Ordering of Pattern Matches"
```broken
def seconds : List (List α) → List α
  | [] => []
  | _ :: xss => seconds xss
  | (_ :: x :: _) :: xss => x :: seconds xss
```
```output
Redundant alternative: Any expression matching
  (head✝ :: x :: tail✝) :: xss
will match one of the preceding alternatives
```
```fixed
def seconds : List (List α) → List α
  | [] => []
  | (_ :: x :: _) :: xss => x :: seconds xss
  | _ :: xss => seconds xss
```

由于任何匹配 `(_ :: x :: _) :: xss` 的表达式也将匹配 `_ :: xss`，所以最后一个
在损坏的实现中永远无法实现替代方案。我们通过移动更多来解决这个问题
在更一般的选择之前有特定的选择。
:::

:::errorExample "Unnecessary Fallback Clause"
```broken
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
    | return 0
  return m + n
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```fixed
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
  return m + n
```

此处，后备子句充当与 `(m, n)` 不匹配的 `p` 的所有值的包罗万象。
但是，不存在这样的值，因此后备子句是不必要的，可以删除。类似的
当 `e` 始终与 `pat` 匹配时，使用 `if let pat := e` 时会出现错误。
:::

:::errorExample "Pattern Treated as Variable, Not Constructor"
```broken
example (xs : List Nat) : Bool :=
  match xs with
  | nil => false
  | _ => true
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```fixed
example (xs : List Nat) : Bool :=
  match xs with
  | .nil => false
  | _ => true
```

在原始示例中，`nil` 被视为变量，而不是构造函数名称，因为这
定义不在 {name}`List` 命名空间内。因此，`xs` 的所有值都将与第一个值匹配
模式，渲染第二个未使用的。请注意，构造函数名称作为变量 linter 显示
`nil` 处发出警告，表明其与有效构造函数名称相似。使用点前缀表示法，
如固定示例所示，或指定完整的构造函数名称 {name}`List.nil`
实现预期的行为。
:::
