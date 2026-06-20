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

#doc (Manual) "选项" =>
%%%
file := "Option"
tag := "option-monad"
%%%

通常，{lean}`Option` 被视为数据，类似于可为 null 的类型。
它也可以被视为一个单子，因此是一种执行计算的方式。
{lean}`Option` monad 及其转换器 {lean}`OptionT` 可以理解为描述可能提前终止并丢弃结果的计算。
调用者可以使用 {name}`OrElse.orElse` 或将其视为 {lean}`MonadExcept Unit` 来检查是否提前终止并调用回退（如果需要）。

{docstring OptionT}

{docstring OptionT.run}

{docstring OptionT.lift}

{docstring OptionT.mk}

{docstring OptionT.pure}

{docstring OptionT.bind}

{docstring OptionT.fail}

{docstring OptionT.orElse}

{docstring OptionT.tryCatch}
