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

#doc (Manual) "状态" =>
%%%
tag := "state-monads"
%%%

{tech (key := "State monads")}[状态单子] 提供对可变值的访问。
底层实现可以使用元组来模拟可变性，或者可以使用 {name}`ST.Ref` 之类的东西来确保突变。
即使那些使用元组的实现实际上也可能在运行时使用突变，因为当存在对值的唯一引用时 Lean 使用突变，但这需要一种更喜欢 {name}`modify` 和 {name}`modifyGet` 而不是 {name}`get` 和 {name}`set` 的编程风格。

# 一般状态 API
%%%
tag := "zh-monads-zoo-state-h001"
%%%

{docstring MonadState}

{docstring get}

{docstring modify}

{docstring modifyGet}

{docstring getModify}

{docstring MonadStateOf}

{docstring getThe}

{docstring modifyThe}

{docstring modifyGetThe}

# 基于元组的状态 Monad
%%%
tag := "zh-monads-zoo-state-h002"
%%%

```lean -show
variable {α σ : Type u}
```

基于元组的状态单子表示具有 {lean}`σ` 类型的状态的计算，生成 {lean}`α` 类型的值，作为采用起始状态并生成与最终状态配对的值的函数，例如{lean}`σ → α × σ`。
{name}`Monad` 操作通过计算正确地对状态进行线程化。

{docstring StateM}

{docstring StateT}

{docstring StateT.run}

{docstring StateT.get}

{docstring StateT.set}

{docstring StateT.orElse}

{docstring StateT.failure}

{docstring StateT.run'}

{docstring StateT.bind}

{docstring StateT.modifyGet}

{docstring StateT.lift}

{docstring StateT.map}

{docstring StateT.pure}

# 连续传递风格的状态单子
%%%
tag := "zh-monads-zoo-state-h003"
%%%

延续传递风格的状态单子将状态计算表示为函数，对于任何类型，该函数都采用初始状态和接受值和更新状态的延续（建模为函数）。
这种类型的一个例子是 {lean}`(δ : Type u) → σ → (α → σ → δ) → δ`，尽管 {lean}`StateCpsT` 是一个可以应用于任何 monad 的转换器。
连续传递风格的状态单子与基于元组的状态单子具有不同的性能特征；对于某些应用程序，可能值得对它们进行基准测试。


```lean -show
/-- info: (δ : Type u) → σ → (α → σ → Id δ) → δ -/
#check_msgs in
#reduce (types := true) StateCpsT σ Id α
```
{docstring StateCpsT}

{docstring StateCpsT.lift}

{docstring StateCpsT.runK}

{docstring StateCpsT.run'}

{docstring StateCpsT.run}

# 来自可变引用的状态 Monad
%%%
tag := "zh-monads-zoo-state-h004"
%%%

```lean -show
variable {m : Type → Type} {σ ω : Type} [STWorld σ m]
```

monad {lean}`StateRefT σ m` 是一种专用状态 monad 转换器，当 {lean}`m` 是可以将 {name}`ST` 计算提升到的 monad 时，可以使用它。
它使用 {name}`ST.Ref` 而不是纯函数来实现 {name}`MonadState` 的操作。
这确保了突变在运行时实际使用。

{name}`ST` 和 {name}`EST` 需要一个幻像类型参数，该参数与 {name}`runST` 的多态函数参数一起使用以封装可变性。
不需要将此作为变压器的参数，而是使用辅助类型类 {name}`STWorld` 直接从 {lean}`m` 传播它。

变压器本身被定义为 {ref "syntax-ext"}[语法扩展] 和 {ref "elaborators"}[精化器]，而不是普通函数。
这是因为 {name}`STWorld` 没有方法：它的存在只是为了将信息从内部 monad 传播到转换后的 monad。
然而，它的实例是术语；保留它们可能会导致不必要的大型类型。

{docstring STWorld}

:::syntax term (title := "`StateRefT`")
{lean}`StateRefT σ m` 的语法接受两个参数：

```grammar
StateRefT $_ $_
```

其精化器合成 {lean}`STWorld ω m` 的实例，以确保 {lean}`m` 支持可变引用。
发现 {lean}`ω` 的值后，它会生成项 {lean}`StateRefT' ω σ m`，并丢弃合成的实例。
:::

{docstring StateRefT'}

{docstring StateRefT'.get}

{docstring StateRefT'.set}

{docstring StateRefT'.modifyGet}

{docstring StateRefT'.run}

{docstring StateRefT'.run'}

{docstring StateRefT'.lift}
