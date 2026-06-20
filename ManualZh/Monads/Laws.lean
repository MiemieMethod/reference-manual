/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "法律" =>
%%%
tag := "monad-laws"
%%%

::::keepEnv

```lean -show
section Laws
universe u u' v
axiom f : Type u → Type v
axiom m : Type u → Type v
variable [Functor f]
variable [Applicative f]
variable [Monad m]
axiom α : Type u'
axiom β : Type u'
axiom γ : Type u'
axiom x : f α
```


```lean -show
section F
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {h : β → γ} {x : f α}
```

拥有具有适当类型的 {name Functor.map}`map`、{name Pure.pure}`pure`、{name Seq.seq}`seq` 和 {name Bind.bind}`bind` 运算符并不足以拥有函子、应用函子或 monad。
这些运算符还必须满足某些公理，这些公理通常称为类型类的 {deftech}_laws_。

对于函子，{name Functor.map}`map` 操作必须保留标识和函数组合。换句话说，给定一个所谓的 {name}`Functor` {lean}`f`，对于所有 {lean}`x`​` : `​{lean}`f α`：
 * {lean}`id <$> x = x`，和
 * 适用于 {lean}`g` 和 {lean}`h`、{lean}`(h ∘ g) <$> x = h <$> g <$> x` 的所有功能。

违反这些假设的实例可能会非常令人惊讶！
此外，由于 {lean}`Functor` 包括 {name Functor.mapConst}`mapConst` 以使实例能够提供更高效的实现，因此合法函子的 {name Functor.mapConst}`mapConst` 应与其默认实现等效。

Lean 标准库不需要在 {name}`Functor` 的每个实例中提供这些属性的证明。
尽管如此，如果一个实例违反了它们，那么它应该被视为一个错误。
当需要证明这些属性时，可以使用 {lean}`LawfulFunctor f` 类型的实例隐式参数。
{name}`LawfulFunctor` 类包括必要的证明。

{docstring LawfulFunctor}

```lean -show
end F
```


除了证明潜在优化的 {name}`SeqLeft.seqLeft` 和 {name}`SeqRight.seqRight` 操作与其默认实现等效之外，应用函子 {lean}`f` 还必须满足四个定律。

:::TODO
讨论传统适用法与本演示文稿之间的关系
:::

{docstring LawfulApplicative}

{deftech (key := "monad laws")}[monad law] 指定 {name}`pure` 后跟 {name}`bind` 应等效于函数应用程序（即 {name}`pure` 没有效果），{name}`bind` 后跟 {name}`pure` 围绕函数应用程序等效于 {name Functor.map}`map`，并且{name}`bind` 是结合的。


{docstring LawfulMonad}


{docstring LawfulMonad.mk'}

::::
