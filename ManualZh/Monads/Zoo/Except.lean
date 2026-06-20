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

#doc (Manual) "例外情况" =>
%%%
file := "Exceptions"
tag := "exception-monads"
%%%

异常单子描述提前终止（失败）的计算。
失败的计算为其调用者提供一个_异常_值，该值描述了_为什么_失败。
换句话说，计算要么返回一个值，要么返回一个异常。
归纳类型{name}`Except` 捕获了这种模式，并且它本身就是一个 monad。

# 例外情况
%%%
file := "Exceptions"
tag := "zh-monads-zoo-except-h001"
%%%

{docstring Except}

{docstring Except.pure}

{docstring Except.bind}

{docstring Except.map}

{docstring Except.mapError}

{docstring Except.tryCatch}

{docstring Except.orElseLazy}

{docstring Except.isOk}

{docstring Except.toOption}

{docstring Except.toBool}


# Type级
%%%
file := "Type-Class"
tag := "zh-monads-zoo-except-h002"
%%%

{docstring MonadExcept}

{docstring MonadExcept.ofExcept}

{docstring MonadExcept.orElse}

{docstring MonadExcept.orelse'}

{docstring MonadExceptOf}

{docstring throwThe}

{docstring tryCatchThe}

# “最后”计算
%%%
file := "___Finally___-Computations"
tag := "zh-monads-zoo-except-h003"
%%%

{docstring MonadFinally}

# 变压器
%%%
file := "Transformer"
tag := "zh-monads-zoo-except-h004"
%%%

{docstring ExceptT}

{docstring ExceptT.lift}

{docstring ExceptT.run}

{docstring ExceptT.pure}

{docstring ExceptT.bind}

{docstring ExceptT.bindCont}

{docstring ExceptT.tryCatch}

{docstring ExceptT.mk}

{docstring ExceptT.map}

{docstring ExceptT.adapt}


# 连续传递风格中的异常 Monad
%%%
file := "Exception-Monads-in-Continuation-Passing-Style"
tag := "zh-monads-zoo-except-h005"
%%%

```lean -show
universe u
variable (α : Type u)
variable (ε : Type u)
variable {m : Type u → Type v}
```

连续传递式异常 monad 将可能失败的计算表示为采用成功和失败连续的函数，这两个连续都返回相同的类型，返回该类型。
它们必须适用于 _any_ 返回类型。
此类类型的一个示例是 {lean}`(β : Type u) → (α → β) → (ε → β) → β`。
{lean}`ExceptCpsT`是一个可以应用于任何monad的变压器，因此{lean}`ExceptCpsT ε m α`实际上被定义为{lean}`(β : Type u) → (α → m β) → (ε → m β) → m β`。
连续传递风格的异常 monad 与基于 {name}`Except` 的状态 monad 相比具有不同的性能特征；对于某些应用程序，可能值得对它们进行基准测试。

```lean -show
/-- info: (β : Type u) → (α → m β) → (ε → m β) → m β -/
#check_msgs in
#reduce (types := true) ExceptCpsT ε m α
```

{docstring ExceptCpsT}

{docstring ExceptCpsT.runCatch}

{docstring ExceptCpsT.runK}

{docstring ExceptCpsT.run}

{docstring ExceptCpsT.lift}
