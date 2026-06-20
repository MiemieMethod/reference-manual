/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual
import Manual.Meta.Figure
import Lean.Elab.InfoTree

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab

namespace Manual

def Block.noVale : Block where
  name := `Manual.Block.noVale

@[block_extension Block.noVale]
def Block.noVale.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="no-vale">{{← content.mapM goB}}</div>}}

/-- Closes the last-opened section, throwing an error on failure. -/
def closeEnclosingSection : PartElabM Unit := do
  -- Markdown headers carry no source extent of their own, so end the section at the end of the
  -- current reference. This keeps each part's range valid (the selection stays within
  -- `[rangeStart, endPos]`) for the TOC range conversion.
  let endPos := (← getRef).getTailPos?.getD default
  if let some ctxt' := (← getThe PartElabM.State).partContext.close endPos then
    modifyThe PartElabM.State fun st => {st with partContext := ctxt'}
  else
    throwError m!"Failed to close the last-opened explanation part"

/-- Closes as many sections as were created by markdown processing. -/
def closeEnclosingSections (headerMapping : Markdown.HeaderMapping) : PartElabM Unit := do
  for _ in headerMapping do
    closeEnclosingSection

/-- Closes Markdown-created sections whose Markdown level is at least `level`. -/
partial def closeMarkdownSectionsTo (headerMapping : Markdown.HeaderMapping) (level : Nat) :
    PartElabM Markdown.HeaderMapping := do
  match headerMapping with
  | [] => pure []
  | docLevel :: more =>
    if docLevel ≥ level then
      closeEnclosingSection
      closeMarkdownSectionsTo more level
    else
      pure headerMapping

def markdownHeaderTag (tagPrefix : String) (index : Nat) : String :=
  s!"markdown-{tagPrefix}-h{index}"

/--
Adds Markdown blocks while assigning stable ASCII tags to Markdown headings.

The default Verso tag generator derives tags from heading text. Chinese headings may therefore
slugify to the same underscore-only string, so release-note Markdown needs explicit tags.
-/
def addTaggedPartFromMarkdown (tagPrefix : String) (block : MD4Lean.Block)
    (currentHeaderLevels : Markdown.HeaderMapping) (nextHeaderIndex : Nat) :
    PartElabM (Markdown.HeaderMapping × Nat) := do
  match block with
  | .header level txt => do
    let currentHeaderLevels ← closeMarkdownSectionsTo currentHeaderLevels level
    let titleTexts ← match txt.mapM Markdown.stringFromMarkdownText with
      | .ok t => pure t
      | .error e => throwError m!"Unsupported Markdown in header:\n{e}"
    let titleText := titleTexts.foldl (· ++ ·) ""
    let titleSyntax ← getRef
    let titleInline ← `(Verso.Doc.Inline.text $(quote titleText))
    let tag := markdownHeaderTag tagPrefix nextHeaderIndex
    let metadata ← `({ tag := some (Tag.provided $(quote tag)) : PartMetadata })
    PartElabM.push {
      rangeSyntax := titleSyntax
      selectionSyntax := titleSyntax
      expandedTitle := some (titleText, #[titleInline])
      metadata := some metadata
      blocks := #[]
      priorParts := #[]
    }
    pure (level :: currentHeaderLevels, nextHeaderIndex + 1)
  | block => do
    PartElabM.addBlock (← Markdown.blockFromMarkdown block)
    pure (currentHeaderLevels, nextHeaderIndex)

@[part_command Lean.Doc.Syntax.codeblock]
def markdown : PartCommand
  | `(Lean.Doc.Syntax.codeblock| ``` $markdown:ident $args*| $txt ``` ) => do
     let x ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo markdown
     if x != by exact decl_name% then Elab.throwUnsupportedSyntax
     for arg in args do
       let h ← MessageData.hint m!"Remove it" #[""] (ref? := arg)
       logErrorAt arg m!"No arguments expected{h}"
     let some ast := MD4Lean.parse txt.getString
       | throwError "Failed to parse body of markdown code block"
     let mut currentHeaderLevels : Markdown.HeaderMapping := {}
     let mut nextHeaderIndex := 1
     let tagPrefix := toString (hash txt.getString)
     for block in ast.blocks do
       let (currentHeaderLevels', nextHeaderIndex') ←
         addTaggedPartFromMarkdown tagPrefix block currentHeaderLevels nextHeaderIndex
       currentHeaderLevels := currentHeaderLevels'
       nextHeaderIndex := nextHeaderIndex'
     closeEnclosingSections currentHeaderLevels
  | _ => Elab.throwUnsupportedSyntax
