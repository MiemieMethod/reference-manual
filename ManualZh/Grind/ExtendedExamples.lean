/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

import ManualZh.Grind.ExtendedExamples.Integration
import ManualZh.Grind.ExtendedExamples.IfElseNorm

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Grind

#doc (Manual) "更大的例子" =>
%%%
file := "Bigger-Examples"
tag := "grind-bigger-examples"
%%%

:::TODO
正确链接到教程部分
:::

{include 1 ManualZh.Grind.ExtendedExamples.Integration}

{include 1 ManualZh.Grind.ExtendedExamples.IfElseNorm}
