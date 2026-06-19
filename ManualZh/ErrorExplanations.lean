/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import Manual.Meta.ErrorExplanation
import ManualZh.ErrorExplanations.CtorResultingTypeMismatch
import ManualZh.ErrorExplanations.DependsOnNoncomputable
import ManualZh.ErrorExplanations.InductionWithNoAlts
import ManualZh.ErrorExplanations.InductiveParamMismatch
import ManualZh.ErrorExplanations.InductiveParamMissing
import ManualZh.ErrorExplanations.InferBinderTypeFailed
import ManualZh.ErrorExplanations.InferDefTypeFailed
import ManualZh.ErrorExplanations.InvalidDottedIdent
import ManualZh.ErrorExplanations.InvalidField
import ManualZh.ErrorExplanations.ProjNonPropFromProp
import ManualZh.ErrorExplanations.PropRecLargeElim
import ManualZh.ErrorExplanations.RedundantMatchAlt
import ManualZh.ErrorExplanations.SynthInstanceFailed
import ManualZh.ErrorExplanations.UnknownIdentifier

open Lean
open Verso (reportError)
open Verso.Doc Elab
open Verso.Genre Manual


/- Renders the suffix of an error explanation, allowing line breaks before capital letters. -/
inline_extension Inline.errorExplanationShortName (errorName : Name) where
  data := toJson (getBreakableSuffix errorName)
  traverse := fun _ _ _ => pure none
  extraCss := [".error-explanation-short-name { hyphenate-character: ''; }"]
  toTeX := none
  toHtml := some fun _go _id info _content =>
    open Verso.Output Html in do
    let .ok (some errorName) := fromJson? (α := Option String) info
      | reportError "Invalid data for explanation name element"
        pure .empty
    let html := {{ <code class="error-explanation-short-name">{{errorName}}</code> }}
    return html


/--
Renders a table-of-contents like summary of the error explanations defined by the current Lean
implementation.
-/
@[block_command]
def error_explanation_table : BlockCommandOf Unit
  | () => do
    let entries ← getErrorExplanations
    let columns := 4
    let header := true
    let name := "error-explanation-table"
    let alignment : Option TableConfig.Alignment := none
    let headers ← #["Name", "Summary", "Severity", "Since"]
      |>.mapM fun s => ``(Verso.Doc.Block.para #[Inline.text $(quote s)])
    let vals ← entries.flatMapM fun (name, explan) => do
      let sev := quote <| if explan.metadata.severity == .warning then "Warning" else "Error"
      let sev ← ``(Inline.text $sev)
      let nameLink ←
        ``(Inline.other (Inline.ref $(quote name.toString) $(quote errorExplanationDomain) Option.none)
          #[Inline.other (Inline.errorExplanationShortName $(quote name)) #[]])
      let summary ← ``(Inline.text $(quote explan.metadata.summary))
      let since ← ``(Inline.text $(quote explan.metadata.sinceVersion))
      #[nameLink, summary, sev, since]
        |>.mapM fun s => ``(Verso.Doc.Block.para #[$s])
    let blocks := (headers ++ vals).map fun c => Syntax.TSepArray.mk #[c]
    ``(Block.other (Block.table $(quote columns) $(quote header) $(quote name) $(quote alignment)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])

#doc (Manual) "错误说明" =>
%%%
number := false
htmlToc := false
%%%

本节提供可能生成的错误和警告的说明
处理源文件时通过 Lean。下面列出的所有错误名称都有
`lean` 封装前缀。

{error_explanation_table}

{include 0 ManualZh.ErrorExplanations.CtorResultingTypeMismatch}

{include 0 ManualZh.ErrorExplanations.DependsOnNoncomputable}

{include 0 ManualZh.ErrorExplanations.InductionWithNoAlts}

{include 0 ManualZh.ErrorExplanations.InductiveParamMismatch}

{include 0 ManualZh.ErrorExplanations.InductiveParamMissing}

{include 0 ManualZh.ErrorExplanations.InferBinderTypeFailed}

{include 0 ManualZh.ErrorExplanations.InferDefTypeFailed}

{include 0 ManualZh.ErrorExplanations.InvalidDottedIdent}

{include 0 ManualZh.ErrorExplanations.InvalidField}

{include 0 ManualZh.ErrorExplanations.ProjNonPropFromProp}

{include 0 ManualZh.ErrorExplanations.PropRecLargeElim}

{include 0 ManualZh.ErrorExplanations.RedundantMatchAlt}

{include 0 ManualZh.ErrorExplanations.SynthInstanceFailed}

{include 0 ManualZh.ErrorExplanations.UnknownIdentifier}
