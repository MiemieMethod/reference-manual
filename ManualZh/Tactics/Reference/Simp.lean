/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "简化" =>
%%%
file := "Simplification"
tag := "simp-tactics"
%%%

{ref "the-simplifier"}[其专用章节]中更详细地描述了该简化器。

:::tactic "simp"
:::

:::tactic "simp!"
:::

:::tactic "simp?"
:::

:::tactic "simp?!"
:::

:::tactic "simp_arith"
:::

:::tactic "simp_arith!"
:::

:::tactic "dsimp"
:::

:::tactic "dsimp!"
:::

:::tactic "dsimp?"
:::

:::tactic "dsimp?!"
:::


:::tactic "simp_all"
:::

:::tactic "simp_all!"
:::

:::tactic "simp_all?"
:::

:::tactic "simp_all?!"
:::


:::tactic "simp_all_arith"
:::


:::tactic "simp_all_arith!"
:::


:::tactic "simpa"
:::


:::tactic "simpa!"
:::

:::tactic "simpa?"
:::

:::tactic "simpa?!"
:::

:::tactic "simp_wf"
:::
