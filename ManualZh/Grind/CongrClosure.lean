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

#doc (Manual) "同余闭包" =>
%%%
tag := "congruence-closure"
%%%

:::leanSection
```lean -show
variable {a a' : α} {b b' : β} {f : α → β → γ}
```
{deftech (key := "Congruence closure")}_同余闭包_在“等于”的自反、对称和传递闭包下维护术语的等价类_并且_相等的参数产生相等的函数结果的规则。
形式上，如果 {lean}`a = a'` 和 {lean}`b = b'`，则添加 {lean}`f a b = f a' b'`。
该算法合并等价类，直到达到固定点。
如果发现矛盾，那么可以立即关闭目标。
:::

::::leanSection
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
```
:::paragraph
用共享白板来比喻：

1. 每个假设 {typed}`h : t₁ = t₂` 都写一条连接 {lean}`t₁` 和 {lean}`t₂` 的线。

2. 每当两项通过一条或多条线连接时，它们就被认为是相等的。
   很快，整个星座（{lean}`f a`、{lean}`g (f a)`，...）就连接起来了。

3. 如果同一归纳类型的两个不同构造函数通过一根或多根线连接，则发现矛盾并关闭目标。
   例如，将 {lean}`True` 和 {lean}`False` 或 {lean  (type := "Option Nat")}`none` 和 {lean}`some 1` 等同起来会产生矛盾。

:::
::::

:::example "Congruence Closure" (open := true)
使用同余闭包证明该定理：
```lean
example {α} (f g : α → α) (x y : α)
    (h₁ : x = y) (h₂ : f y = g y) :
    f x = g x := by
  grind
```
最初，`f y`、`g y`、`x` 和 `y` 位于不同的等价类中。
同余闭包引擎使用 `h₁` 合并 `x` 和 `y`，之后等价类为 `{x, y}`, `f y` 和 `g y`。
接下来，`h₂` 用于合并 `f y` 和 `g y`，之后的类为 `{x, y}` and `{f y, g y}`。
这足以证明`f x = g x`，因为`y`和`x`属于同一类。

类似的推理也适用于构造函数：
```lean
example (a b c : Nat) (h : a = b) : (a, c) = (b, c) := by
  grind
```
由于对构造函数 {name}`Prod.mk` 遵循同余，因此只要将 `a` 和 `b` 放置在同一类中，元组就变得相等。
:::


# 同余闭包与简化
%%%
tag := "zh-grind-congrclosure-h001"
%%%

::::leanSection
```lean -show
variable {t₁ t₂ : α} {h : t₁ = t₂} {a : α} {f : α → β} {g : β → β}
```
:::paragraph
同余闭包是与简化完全不同的操作：

* {tactic}`simp` _重写_ 目标，一旦看到 {typed}`h : t₁ = t₂`，就将出现的 {lean}`t₁` 替换为 {lean}`t₂`。
  重写是定向的、破坏性的。
* {tactic}`grind` 双向_累加_相等。  没有术语被重写；相反，两位代表住在同一个班级。  所有其他引擎（{tech (key := "E‑matching")}[E 匹配]、理论求解器、{tech (key := "constraint propagation")}[传播]）都可以查询这些类并添加新事实，然后闭包增量更新。

这使得同余闭包在存在对称推理、相互递归和构造函数的大型嵌套（重写会重复工作）的情况下特别强大。
:::
::::
