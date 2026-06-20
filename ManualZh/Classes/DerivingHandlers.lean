/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

section

open Lean Elab Command

/- Needed due to big infotree coming out of the instance quotation in the example here -/
set_option maxRecDepth 1024
set_option maxHeartbeats 650_000

/-- Classes that are part of the manual, not to be shown -/
-- TODO: When moving to v4.26.0-rc1, @kim-em removed `Plausible.Arbitrary` from this list.
-- Should it be restored?
private def hiddenDerivable : Array Name := #[``Manual.Toml.Test]

private def derivableClasses : IO (Array Name) := do
  let handlers ← derivingHandlersRef.get
  let derivable :=
    handlers.toList.map (·.fst)
      |>.toArray
      |>.filter (fun x => !hiddenDerivable.contains x && !(`Lean).isPrefixOf x)
      |>.qsort (·.toString < ·.toString)
  pure derivable

private def checkDerivable (expected : Array Name) : CommandElabM Unit := do
  let classes ← derivableClasses
  let extra := classes.filter (· ∉ expected)
  let missing := expected.filter (· ∉ classes)
  if extra.isEmpty && missing.isEmpty then
    Verso.Log.logSilentInfo m!"Derivable classes match!"
  else
    unless extra.isEmpty do
      logError
        m!"These classes were not expected. If they should appear in the list here, \
           then add them to the call; otherwise, add them to `{.ofConstName ``hiddenDerivable}`: \
           {.andList <| extra.toList.map (.ofConstName ·)}"
    unless missing.isEmpty do
      logError
        m!"These classes were expected but not present. Check whether the text needs updating, then \
           then remove them from the call."

end


#eval checkDerivable #[``BEq, ``DecidableEq, ``Hashable, ``Inhabited, ``Nonempty, ``Ord, ``Repr, ``SizeOf, ``TypeName, ``LawfulBEq, ``ReflBEq]

open Verso Doc Elab ArgParse in
open Lean in
open SubVerso Highlighting in
@[directive_expander derivableClassList]
def derivableClassList : DirectiveExpander
  | args, contents => do
    -- No arguments!
    ArgParse.done.run args
    if contents.size > 0 then throwError "Expected empty directive"
    let classNames ← derivableClasses
    let itemStx ← classNames.mapM fun n => do
      let hl : Highlighted ← constTok n n.toString
      `(Inline.other {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote n.toString)])
    let theList ← `(Verso.Doc.Block.ul #[$[⟨#[Verso.Doc.Block.para #[$itemStx]]⟩],*])
    return #[theList]

open Lean Elab Command

#doc (Manual) "派生处理程序" =>
%%%
file := "Deriving-Handlers"
tag := "deriving-handlers"
%%%

实例派生使用 {deftech}_deriving handlers_ 表，该表将类型类名称映射到为其派生实例的元程序。
可以使用 {lean}`registerDerivingHandler` 将派生处理程序添加到表中，这应该在 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中调用。
每个派生处理程序的类型应为 {lean}`Array Name → CommandElabM Bool`。
当用户请求派生类的实例时，一次调用一个其注册的处理程序。
它们提供了要为其派生实例的共同块中的所有名称，并且应该正确派生实例并返回 {lean}`true`，或者没有效果并返回 {lean}`false`。
当处理程序返回 {lean}`true` 时，不会再调用其他处理程序。

Lean 包括以下类的派生处理程序：

:::derivableClassList
:::

{docstring Lean.Elab.registerDerivingHandler}


::::keepEnv
:::example "Deriving Handlers"

```imports -show
import Lean.Elab
```

{name}`IsEnum` 类的实例通过在类型和适当大小的 {name}`Fin` 之间提供双射来证明该类型是有限枚举：
```lean
class IsEnum (α : Type) where
  size : Nat
  toIdx : α → Fin size
  fromIdx : Fin size → α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x
```

对于归纳类型来说，这些枚举是简单的枚举，没有构造函数需要任何参数，所以此类的实例非常重复。
`Bool` 的实例是典型的：
```lean
instance : IsEnum Bool where
  size := 2
  toIdx
    | false => 0
    | true => 1
  fromIdx
    | 0 => false
    | 1 => true
  to_from_id
    | 0 => rfl
    | 1 => rfl
  from_to_id
    | false => rfl
    | true => rfl
```

派生处理程序以编程方式构造每个模式情况，类似于 {lean}`IsEnum Bool` 实现：
```lean
open Lean Elab Parser Term Command

def deriveIsEnum (declNames : Array Name) : CommandElabM Bool := do
  if h : declNames.size = 1 then
    let env ← getEnv
    if let some (.inductInfo ind) := env.find? declNames[0] then
      let mut tos : Array (TSyntax ``matchAlt) := #[]
      let mut froms := #[]
      let mut to_froms := #[]
      let mut from_tos := #[]
      let mut i := 0

      for ctorName in ind.ctors do
        let c := mkIdent ctorName
        let n := Syntax.mkNumLit (toString i)

        tos      := tos.push      (← `(matchAltExpr| | $c => $n))
        from_tos := from_tos.push (← `(matchAltExpr| | $c => rfl))
        froms    := froms.push    (← `(matchAltExpr| | $n => $c))
        to_froms := to_froms.push (← `(matchAltExpr| | $n => rfl))

        i := i + 1

      let cmd ← `(instance : IsEnum $(mkIdent declNames[0]) where
                    size := $(quote ind.ctors.length)
                    toIdx $tos:matchAlt*
                    fromIdx $froms:matchAlt*
                    to_from_id $to_froms:matchAlt*
                    from_to_id $from_tos:matchAlt*)
      elabCommand cmd

      return true
  return false

initialize
  registerDerivingHandler ``IsEnum deriveIsEnum
```
:::
::::
