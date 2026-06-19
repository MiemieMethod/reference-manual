/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual hiding seeAlso
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Term (doSeq)

set_option pp.rawOnError true

set_option linter.unusedVariables false

open Lean

#doc (Manual) "扩展 `do` 表示法" =>

%%%
tag := "do-elab"
%%%

宏和精化器可用于使用新命令和术语扩展 Lean。
此外，{keywordOf Lean.Parser.Term.do}`do` 表示法可以扩展。
{keywordOf Lean.Parser.Term.do}`do` 表示法的扩展定义了新类型的 {keywordOf Lean.Parser.Term.do}`do` 元素。
宏将新的 {keywordOf Lean.Parser.Term.do}`do` 元素转换为先前存在的 {keywordOf Lean.Parser.Term.do}`do` 元素，而精化器可以访问更多信息，并可以在 Lean 的 类型论 中生成任意项。

:::paragraph
本章介绍可用于 {keywordOf Lean.Parser.Term.do}`do` 表示法的扩展机制。
Lean 版本 4.29.0 中引入了可扩展的 {keywordOf Lean.Parser.Term.do}`do` 表示法；在此版本之前，它是不可扩展的。
可扩展 {keywordOf Lean.Parser.Term.do}`do`精化器由选项 {option}`backward.do.legacy` 控制：

{optionDocs backward.do.legacy}

当 {option}`backward.do.legacy` 为 `false` 时，启用可扩展精化器。
自定义 {keywordOf Lean.Parser.Term.do}`do` 元素精化器扩展了 {ref "do-notation"}[单子语法部分]中描述的脱糖。
:::

# 精化概述

{tech}[语法类型] `doElem` 表示各个 {tech}[`do` 元素]。
这些元素的序列由语法类型 {name}`doSeq` 表示，它构成了 {keywordOf Lean.Parser.Term.do}`do` 块的主体。
{keywordOf Lean.Parser.Term.do}`do` 的精化器在其主体中的 {name}`doSeq` 上调用专门的精化框架，依次详细说明每个 `doElem`。
这个专门的框架允许序列中的每个元素修改后续元素的精化，以及跟踪诸如封闭循环（对于 {keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue`）、通过 {keywordOf Lean.Parser.Term.doReturn}`return` 转义的方式以及可变变量集等信息。

{keywordOf Lean.Parser.Term.do}`do`-elements 的精化与术语非常相似。
首先，如果所讨论的语法是 {tech}[宏]，则它会被扩展。
重复此操作，直到宏展开的结果不再是宏。
接下来，查询内部表以查找与 {keywordOf Lean.Parser.Term.do}`do` 元素的语法类型关联的精化过程。
该表与术语精化器表分开，因为 {keywordOf Lean.Parser.Term.do}`do` 元素精化器具有不同的类型。
如果 {keywordOf Lean.Parser.Term.do}`do` 元素仅包含术语，则 Lean 解析器将其包装在语法类型 {name Lean.Parser.Term.doExpr}`doExpr` 中；它的精化器调用术语精化器，确保该术语具有 {keywordOf Lean.Parser.Term.do}`do` 块的正确类型。

# `do` 表示法中的宏

宏展开发生在 {keywordOf Lean.Parser.Term.do}`do` 元素的精化期间。
{keywordOf Lean.Parser.Term.do}`do` 元素宏与术语或命令宏之间没有根本区别；它们的区别在于其定义的语法属于 `doElem` 语法类别的一部分。

::::example "Multi-Way `if`"
```imports -show
import Lean.Elab
```
```lean -show
open Lean
open Lean.Parser.Term (doSeq)
```
作为 {keywordOf Lean.Parser.Term.doIf}`if` 术语嵌套序列的替代方案，此“多路 {keywordOf Lean.Parser.Term.doIf}`if`”将每个条件置于相同的语法级别：
```lean
syntax (name := multiIfTerm)
  "if " withPosition(
    (colGe atomic("|" (atomic(ident " : "))? term) " => " term)+
    colGe "|" " else " " => " term
  ) : term
```
它是 {ref "syntax-indentation"}[缩进敏感]。
它可以实现为递归宏，发出预期的嵌套 {keywordOf Lean.Parser.Term.if}`if`：
```lean
def mkTermIf (h? : Option Ident) (g b e : Term) : MacroM Term :=
  match h? with
  | some h => `(if $h:ident : $g then $b else $e)
  | none => `(if $g then $b else $e)

macro_rules
  | `(if | $[$h?:ident :]? $g:term => $b:term | else => $e:term) =>
      mkTermIf h? g b e
  | `(if | $[$h?:ident :]? $g:term => $b:term
         | $[$h2?:ident :]? $g2:term => $b2:term
         $[| $[$hs?:ident :]? $gs:term => $bs:term]*
         | else => $e:term) => do
      mkTermIf h? g b
        (← `(if | $[$h2?:ident :]? $g2 => $b2
                $[| $[$hs?:ident :]? $gs => $bs]*
                | else => $e))
```

它可以像任何其他术语一样使用：
```lean (name := multiDemo)
#eval
  let sign : Int → String := fun n =>
    if
      | n < 0 => "neg"
      | n = 0 => "zero"
      | else => "pos"
  (sign (-2), sign 0, sign 5)
```
```leanOutput multiDemo
("neg", "zero", "pos")
```

通过将该宏放在 `doElem` 语法类别中并用 {name}`doSeq` 而不是 {name}`Term` 替换多路 {keywordOf Lean.Parser.Term.doIf}`if` 的每个臂，可以将该宏改编为 {keywordOf Lean.Parser.Term.do}`do` 元素。
语法定义几乎相同；但是，{keywordOf Lean.Parser.Term.doIf}`else` 分支是可选的：
```lean
syntax (name := multiIf)
  "if " withPosition(
    (colGe atomic("|" (atomic(ident " : "))? term) " => " doSeq)+
    (colGe "|" " else " " => " doSeq)?
  ) : doElem
```
同样，将可选条件假设名称附加到 {keywordOf Lean.Parser.Term.doIf}`if` 的辅助函数也很有用：
```lean
def mkDoIf (h? : Option Ident) (g : Term) (b : TSyntax ``doSeq)
    (els? : Option (TSyntax ``doSeq)) : MacroM (TSyntax `doElem) :=
  match h? with
  | some h =>
    `(doElem| if $h : $g then $b $[else $els?]?)
  | none =>
    `(doElem| if $g then $b $[else $els?]?)
```
作为递归宏的实现也几乎相同：
```lean
macro_rules
  | `(doElem| if | $[$h?:ident :]? $g:term => $b:doSeq
                   $[| else => $e:doSeq]?) =>
      mkDoIf h? g b e
  | `(doElem| if | $[$h?:ident :]? $g:term => $b:doSeq
                 | $[$h2?:ident :]? $g2:term => $b2:doSeq
                 $[| $[$hs?:ident :]? $gs:term => $bs:doSeq]*
                 $[| else => $e:doSeq]?) => do
      mkDoIf h? g b <| some
        (← `(doSeq| if | $[$h2?:ident :]? $g2 => $b2
                       $[| $[$hs?:ident :]? $gs => $bs]*
                       $[| else => $e]?))
```

可用于{keywordOf Lean.Parser.Term.do}`do`：
```lean
def getEven : IO { n : Nat // n % 2 = 0 ∨ n % 3 = 0} := do
  let n ← (← IO.getStdin).getLine
  let some n := n.toNat?
    | throw <| IO.userError s!"Not a Nat: {n}"
  if
    | h : n % 2 = 0 =>
      IO.println s!"{n} is even."
      return ⟨n, .inl h⟩
    | h : n % 3 = 0 =>
      IO.println s!"{n} is divisible by 3."
      return ⟨n, .inr h⟩
    | else =>
      throw <| IO.userError s!"Invalid input {n}"
```
::::

## 局限性

:::paragraph
当扩展可以作为宏实现时，通常最好这样做。
宏的维护要简单得多，并且它们从它们扩展的语法的实现中继承了错误修复。
然而，宏不能实现所有可能的扩展：
 * 他们无法访问有关可变变量集的信息，也无法覆盖它。
 * 它们无法实现无法用内置控制结构来表达的新颖控制结构。
 * 他们无法将 {keywordOf Lean.Parser.Term.do}`do` 序列放入某些新上下文中（例如在活页夹下），同时将其保留为封闭的 {keywordOf Lean.Parser.Term.do}`do` 块的一部分，以实现早期返回和可变变量的目的。

在这些情况下，可能需要定义精化器。
:::

::::example "Freezing Mutable Variables with a Macro"
在 {keywordOf Lean.Parser.Term.do}`do` 块内，新的 {keywordOf Lean.Parser.Term.doLet}`let` 绑定可能不会影响现有的 {keywordOf Lean.Parser.Term.doLet}`let mut` 绑定。
然而，许多可变变量在初始化后就不会被修改。
通过消除它们的可变性来表明这一事实可能会很方便。

没有现有方法可以用不可变变量替换可变变量，因此无法使用扩展为现有 {keywordOf Lean.Parser.Term.do}`do` 元素的宏来实现此功能，这使得变量对于块的其余部分不可变。
但是，可以构造该运算符，以便通过扩展为函数调用来引入可变变量不可变的范围：
```lean
macro "freeze " x:ident " in " body:doSeq : doElem =>
  `(doElem| (fun $x => do $body) $x)
```


虽然看起来很有希望，但这种基于宏的解决方案有严重的缺点。
首先，结果函数的主体构成了一个新的 {keywordOf Lean.Parser.Term.do}`do` 块。
这意味着周围块中的可变变量不能被修改：
```lean +error (name := noMutFreeze)
#eval Id.run do
  let mut x : Nat := 0
  x := x + 1
  let mut y := 0
  freeze x in
    y := 2 * x
  return y
```
```leanOutput noMutFreeze
`y` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intend to mutate but define `y`, consider using `let y` instead
```
此外，早期的 {keywordOf Lean.Parser.Term.doReturn}`return` 退出内部 {keywordOf Lean.Parser.Term.do}`do`，而不是周围的 {keywordOf Lean.Parser.Term.doReturn}`return`，正如预期返回 {lean}`Unit`（在本例中为宇宙多态 {name}`PUnit`）这一事实所表明的那样：
```lean +error (name := noInnerReturn)
#eval Id.run do
  let mut x : Nat := 0
  x := x + 1
  let mut y := 0
  freeze x in
    return x
  return y
```
```leanOutput noInnerReturn
Application type mismatch: The argument
  x
has type
  Nat
but is expected to have type
  PUnit
in the application
  pure x
```
::::

# 精化


{keywordOf Lean.Parser.Term.do}`do` 元素的精化出现在 {name Lean.Elab.Do.DoElabM}`DoElabM` 单子中。
此 monad 是 {name Lean.Elab.Term.TermElabM}`TermElabM` 的包装器，它提供一个额外的 {ref "reader-monad"}[reader] 值：{keywordOf Lean.Parser.Term.do}`do`-精化上下文。
精化器还收到一个附加参数：精化{deftech}_continuation_ 的描述。
延续代表 {keywordOf Lean.Parser.Term.do}`do` 块中当前元素之后的剩余部分；它包括一个 {name Lean.Elab.Do.DoElabM}`DoElabM` 操作（将详细说明块的其余部分）和名称，该术语将通过该名称来引用当前精化步骤的结果。
与将详细术语返回到周围精化上下文的术语精化器不同，{keywordOf Lean.Parser.Term.do}`do` 元素精化器调用提供的延续来安排 {keywordOf Lean.Parser.Term.do}`do` 块其余部分的精化。


{docstring Lean.Elab.Do.Context +allowMissing}

{docstring Lean.Elab.Do.MonadInfo +allowMissing}

{docstring Lean.Elab.Do.CodeLiveness}

为了避免实现中的循环，{name Lean.Elab.Do.Context.contInfo}`Context.contInfo`和{name Lean.Elab.Do.Context.ops}`Context.ops`字段是构造后填充的引用。
使用{name Lean.Elab.Do.ContInfoRef.toContInfo}`ContInfoRef.toContInfo`和{name Lean.Elab.Do.DoOpsRef.toDoOps}`DoOpsRef.toDoOps`恢复底层数据：

{docstring Lean.Elab.Do.ContInfoRef.toContInfo +allowMissing}

{docstring Lean.Elab.Do.ContInfo +allowMissing}

{docstring Lean.Elab.Do.DoOpsRef.toDoOps +allowMissing}

{docstring Lean.Elab.Do.DoOps +allowMissing}

精化器使用 {attr}`doElem_elab` 属性与语法类型相关联。
它们的类型应为 {name Lean.Elab.Do.DoElab}`DoElab`。
除了精化器之外，通过精化器实现的每个自定义 {keywordOf Lean.Parser.Term.do}`do` 元素还必须提供 {ref "do-elab-control-info"}[控制信息]。

{docstring Lean.Elab.Do.DoElab}

:::syntax attr (title := "Do Element Elaborators")
```grammar
doElem_elab
```
{includeDocstring Lean.Elab.Do.doElemElabAttribute}
:::

此外，{keywordOf Lean.Parser.Command.«elab_rules»}`elab_rules` 可用于同时定义精化器并将其与语法关联。
正如 `elab_rules : term <= ty` 将预期类型绑定到 `ty`，`elab_rules : doElem <= dec` 将延续绑定到 `dec`。

正如术语精化器可以通过调用诸如 {name Lean.Elab.Term.elabTerm}`elabTerm` 之类的函数来递归地调用其子术语上的精化一样，{keywordOf Lean.Parser.Term.do}`do` 元素精化器可以精化嵌套的 {keywordOf Lean.Parser.Term.do}`do` 元素或 {keywordOf Lean.Parser.Term.do}`do` 元素序列。
要详细说明单个 {keywordOf Lean.Parser.Term.do}`do` 元素，请调用 {name Lean.Elab.Do.elabDoElem}`elabDoElem`。
要详细说明 {keywordOf Lean.Parser.Term.do}`do` 元素的非空数组，请调用 {name Lean.Elab.Do.elabDoElems1}`elabDoElems1`。
要详细说明 {keywordOf Lean.Parser.Term.do}`do` 元素的序列，请调用 {name Lean.Elab.Do.elabDoSeq}`elabDoSeq`。

{docstring Lean.Elab.Do.elabDoElem +allowMissing}

{docstring Lean.Elab.Do.elabDoSeq +allowMissing}

{docstring Lean.Elab.Do.elabDoElems1 +allowMissing}

## 单子操作

精化框架提供了几个帮助器，可以更方便、更高效地构建当前 monad 及其操作的应用程序。

{docstring Lean.Elab.Do.mkMonadApp}

{docstring Lean.Elab.Do.mkPureApp}

{docstring Lean.Elab.Do.mkBindApp}

{docstring Lean.Elab.Do.mkPUnitUnit}

## 延续

{keywordOf Lean.Parser.Term.do}`do`-精化延续由等待当前元素的结果的精化器以及元数据（例如该结果预期具有的类型）组成。

{docstring Lean.Elab.Do.DoElemCont}

{docstring Lean.Elab.Do.DoElemContKind +allowMissing}

许多精化器要求延续期望其结果具有特定类型。
例如，如果精化器不返回结果，则生成 {name}`Unit` 是很常见的。
在早期阶段检查类型可以产生更好的错误消息：

{docstring Lean.Elab.Do.DoElemCont.ensureUnit}

{docstring Lean.Elab.Do.DoElemCont.ensureUnitAt}

{docstring Lean.Elab.Do.DoElemCont.ensureHasTypeAt}

调用延续包括向其提供当前 {keywordOf Lean.Parser.Term.do}`do` 元素的结果。
可以通过三种主要方法来实现此目的。
{name Lean.Elab.Do.DoElemCont.continueWithUnit}`DoElemCont.continueWithUnit` 确保延续需要 {name}`Unit`，然后调用它。
{name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode` 在断言代码不可访问的上下文中调用延续，通常会导致延续不生成任何代码，并且如果存在代码也会警告用户。
{name Lean.Elab.Do.DoElemCont.mkBindUnlessPure}`DoElemCont.mkBindUnlessPure` 负责将 {keywordOf Lean.Parser.Term.do}`do` 表示法标准脱糖到 {name}`bind` 的应用程序中；它用于在详细精化由单子类型项组成的 {keywordOf Lean.Parser.Term.do}`do` 元素后调用延续，并且它包含一个优化，用 {keywordOf Lean.Parser.Term.«let»}`let` 绑定替换 {name}`pure` 周围的 {name}`bind`。

{docstring Lean.Elab.Do.DoElemCont.continueWithUnit}

{docstring Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}

{docstring Lean.Elab.Do.DoElemCont.mkBindUnlessPure}

:::example "Invoking Continuations"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
内置语法 {keywordOf Lean.Parser.Term.InternalSyntax.doSkip}`skip` 的一个版本（相当于 {lean (type := "Option Unit")}`pure ()`）可以使用精化器来实现，该精化器立即调用其延续性 {name}`Unit`。
为了获得更好的错误消息，它还断言延续需要 {name}`Unit`。
```lean
syntax (name := doNothing) "nothing" : doElem

@[doElem_elab doNothing]
def elabDoNothing : DoElab := fun stx dec => do
  let dec ← dec.ensureUnitAt stx
  dec.continueWithUnit
```
为了生成控制结构的代码，{keywordOf Lean.Parser.Term.do}`do` 元素精化框架需要有关每个元素可能执行的副作用的信息。
此 {ref "do-elab-control-info"}[控制信息] 通过 {attr}`doElem_control_info` 属性注册。
由于 {keywordOf doNothing}`nothing` 不会修改可变变量、引发异常、提前终止循环或执行任何其他操作，因此其控制信息为 {name}`ControlInfo.pure`。
```lean
@[doElem_control_info doNothing]
def doNothing.control : ControlInfoHandler := fun _ => do return .pure
```

它确实相当于 {lean (type := "Option Unit")}`pure ()`：
```lean (name := doNothing)
#eval show Option Unit from do nothing
```
```leanOutput doNothing
some ()
```
:::

:::example "Elaborating `do`-elements with `elab_rules`"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
{keywordOf doNothing}`nothing` 的替代版本（相当于内置语法 {keywordOf Lean.Parser.Term.InternalSyntax.doSkip}`skip`）可以使用 {keywordOf Lean.Parser.Command.«elab_rules»}`elab_rules` 来实现，作为具有 {attr}`doElem_elab` 属性的精化器的替代方案。
```lean
syntax (name := doNothing) "nothing" : doElem

elab_rules : doElem <= dec
  | `(doElem|nothing%$tk) => do
    let dec ← dec.ensureUnitAt tk
    dec.continueWithUnit

@[doElem_control_info doNothing]
def doNothing.control : ControlInfoHandler := fun _ => do return .pure
```

它相当于 {lean (type := "Option Unit")}`pure ()`：
```lean (name := doNothing')
#eval show Option Unit from do nothing
```
```leanOutput doNothing'
some ()
```
:::

由于精化器显式调用其延续，而不是简单地返回值，因此它可以控制精化的上下文。
特别是，它可以使用 {name}`withReader` 修改上下文，并且可以多次调用延续以支持具有分支的控制结构。
为了防止代码大小爆炸，延续会跟踪它们是否可以在 {name Lean.Elab.Do.DoElemCont.kind}`DoElemCont.kind` 中多次详细说明。
如果延续可以被多次调用，则为 {deftech}_duplicable_，否则为 {deftech}_nonduplicable_。
可以使用 {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont` 将不可重复的延续转换为可重复的延续。

{docstring Lean.Elab.Do.DoElemCont.withDuplicableCont}

无法访问的代码不需要详细说明。
当 {keywordOf Lean.Parser.Term.do}`do` 元素的精化器检测到延续的精化的结果不可访问时，它可以直接返回其结果项，而不是将其传递给精化延续。
它应该产生一个术语来证明放弃该程序是合理的，例如调用 {name}`False.elim`。
在返回该术语之前，它应该在延续上调用 {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode`，这会警告用户延续将详细说明的代码无法访问。

:::example "Unreachable Code"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term Do
set_option backward.do.legacy false
```

当提供 {name}`False` 的证明时，运算符 {keywordOf doAbsurd}`absurd` 将代码标记为不可访问，这表明当前本地上下文在逻辑上不一致。
如果通过了证明，则使用它；否则，它会尝试一些自动化。
```lean
syntax (name := doAbsurd) "absurd" (" by " tacticSeq)? : doElem
```

由于 {keywordOf doAbsurd}`absurd` 永远无法返回，并且控制永远无法越过它，因此其控制信息将 {name Lean.Elab.Do.ControlInfo.numRegularExits}`numRegularExits` 设置为 {lean}`0`，将 {name Lean.Elab.Do.ControlInfo.noFallthrough}`noFallthrough` 设置为 {lean}`true`：
```lean
@[doElem_control_info doAbsurd]
def inferAbsurd : ControlInfoHandler := fun _ =>
  return { numRegularExits := 0, noFallthrough := true }
```

精化器首先提取证明语法，如果未提供则回退到默认值。
然后，它将证明精化为错误的证明。
如果成功，它会使用 {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode` 将 {keywordOf Lean.Parser.Term.do}`do` 序列的其余部分标记为死代码，并使用 {name}`False.elim` 作为结果项，直接返回而不是继续。
{name}`False.elim` 提供了该术语预期具有的类型，该类型是使用 {name}`Lean.Elab.Do.mkMonadApp` 与结果类型一起确定的。
使用 {name Lean.Elab.Do.Context.doBlockResultType}`Do.Context.doBlockResultType` 而不是延续的结果类型非常重要，因为 {ref "do-elab-effect-lift"}[效果提升] 可能已本地修改该类型。
```lean
@[doElem_elab doAbsurd]
def elabAbsurd : DoElab := fun stx dec => do
  let `(doElem| absurd $[by $tac?]?) := stx
    | throwUnsupportedSyntax
  let proofStx : Term ←
    if let some tac := tac? then
      `(by $tac)
    else
      `(by first | contradiction | grind)
  let proof ← elabTermEnsuringType proofStx (mkConst ``False)
  dec.elabAsSyntacticallyDeadCode
  let ty ← mkMonadApp (← read).doBlockResultType
  return (← Meta.mkAppOptM ``False.elim #[some ty, some proof])
```

{keywordOf doAbsurd}`absurd` 允许从嵌套条件中累积信息来排除无法访问的 {keywordOf Lean.Parser.Term.doIf}`else` 子句：
```lean
#eval show Id (String × String × String) from do
  let classify : Nat → String := fun n => Id.run do
    if n < 3 then return "small"
    else if h1 : n < 10 then return "medium"
    else if h2 : n ≥ 10 then return "large"
    else absurd
  return (classify 1, classify 5, classify 99)
```

由于调用 {name Lean.Elab.Do.DoElemCont.elabAsSyntacticallyDeadCode}`DoElemCont.elabAsSyntacticallyDeadCode`，{keywordOf doAbsurd}`absurd` 之后的步骤收到死代码警告：
```lean (name := absurdOut)
def xs := #[1, 3, 5]
theorem xs_all_odd : ∀ x, x ∈ xs → x % 2 = 1 := by
  simp [xs]

#eval show Id Nat from do
  for h : n in 0...5 do
    let k := n * 2
    if h' : k ∈ xs then
      absurd by grind [xs_all_odd]
      return k
  pure 100
```
```leanOutput absurdOut
This `do` element and its control-flow region are dead code. Consider removing it.
```
但是，它确实运行成功：
```leanOutput absurdOut
100
```
:::

## 控制流：`return`、`break` 和 `continue`
%%%
tag := "do-elab-return-continue-break"
%%%

{keywordOf Lean.Parser.Term.do}`do` 表示法支持三个非本地跳转指令： {keywordOf Lean.Parser.Term.doReturn}`return`，提前终止整个 {keywordOf Lean.Parser.Term.do}`do` 块； {keywordOf Lean.Parser.Term.doBreak}`break`，提前终止循环； {keywordOf Lean.Parser.Term.doContinue}`continue`，提前终止循环的单次迭代。
{keywordOf Lean.Parser.Term.doReturn}`return` 始终是允许的，而 {keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue` 仅在循环体内有效。
在精化期间，这三个跳转中的每一个都由一个延续表示。

{docstring Lean.Elab.Do.getReturnCont +allowMissing}

{docstring Lean.Elab.Do.getBreakCont +allowMissing}

{docstring Lean.Elab.Do.getContinueCont +allowMissing}

这三个延续是使用帮助程序 {name Lean.Elab.Do.enterLoopBody}`enterLoopBody` 安装在上下文中的。

{docstring Lean.Elab.Do.enterLoopBody}

:::example "Single-Iteration Loop"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Term Do
set_option backward.do.legacy false
```
单次迭代循环 {keywordOf doOnce}`once` 执行一次其主体，跳至 {keywordOf Lean.Parser.Term.doBreak}`break` 或 {keywordOf Lean.Parser.Term.doContinue}`continue` 上的循环末尾：
```lean
syntax (name := doOnce) "once " doSeq : doElem
```
它的控制信息基于身体的控制信息。
{keywordOf doOnce}`once` 永远不会中断或继续自身，因为它在其主体中处理 {keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue`；因此，它将 {name ControlInfo.breaks}`breaks` 和 {name ControlInfo.continues}`continues` 设置为 {lean}`false`。
{name ControlInfo.numRegularExits}`numRegularExits` 是控制可以到达 {keywordOf doOnce}`once` 之后的代码的次数。
主体的正常下降、{keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue` 都将控制权转移到循环末尾，因此控制最多留下 {keywordOf doOnce}`once` 一次。
因此，当主体可以以这些方式中的任何一种退出时，{name ControlInfo.numRegularExits}`numRegularExits` 为 {lean}`1`，否则为 {lean}`0`，在这种情况下设置 {name ControlInfo.noFallthrough}`noFallthrough`。
```lean
@[doElem_control_info doOnce]
def inferOnce : ControlInfoHandler := fun stx => do
  let `(doElem| once $body) := stx | throwUnsupportedSyntax
  let bodyInfo ← InferControlInfo.ofSeq body
  let exits :=
    bodyInfo.numRegularExits > 0 ||
    bodyInfo.breaks ||
    bodyInfo.continues
  return { bodyInfo with
    breaks := false
    continues := false
    numRegularExits := if exits then 1 else 0
    noFallthrough := !exits
  }
```
{keywordOf doOnce}`once` 的实际精化器使用 {name Lean.Elab.Do.enterLoopBody}`enterLoopBody` 将精化器的整体延续与主体内的 {keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue` 延续关联起来。
由于精心设计的主体可以从多个位置到达该延续，因此精化器计算了这些用途。
主体的控制信息并不指示 {keywordOf Lean.Parser.Term.doBreak}`break` 和 {keywordOf Lean.Parser.Term.doContinue}`continue` 可以被调用多少次，因此它们近似为每个出口，安全地确保如果使用其中任何一个，则延续将被复制。
总的近似使用计数被传递到 {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont`，当使用计数大于 1 时，它会共享延续而不是在每次使用时重复它，从而避免代码爆炸。
它直接从主体计算此计数，因为控制信息处理程序报告的值最多为 {lean}`1` 并且不反映内部使用的数量。
```lean
@[doElem_elab doOnce]
def elabOnce : DoElab := fun stx dec => do
  let `(doElem| once $body) := stx | throwUnsupportedSyntax
  let dec ← dec.ensureUnit
  let bodyInfo ← InferControlInfo.ofSeq body
  let numRegularExits :=
    bodyInfo.numRegularExits +
    (if bodyInfo.breaks then 2 else 0) +
    (if bodyInfo.continues then 2 else 0)
  dec.withDuplicableCont { bodyInfo with numRegularExits } fun dec => do
    let returnCont ← getReturnCont
    let exitCont := dec.continueWithUnit
    enterLoopBody exitCont exitCont returnCont do
      elabDoSeq body dec
```

{keywordOf doOnce}`once` 可用于终止计算的某些部分，而无需使用 {keywordOf Lean.Parser.Term.doReturn}`return` 终止整个 {keywordOf Lean.Parser.Term.do}`do` 块：
```lean (name := once)
#eval show Id Nat from do
  let mut x := 0
  once
    x := x + 2
    if x % 2 = 0 then break
    x := 0
  return x
```
```leanOutput once
2
```
:::

## 控制信息
%%%
tag := "do-elab-control-info"
%%%

除了精化器之外，自定义 {keywordOf Lean.Parser.Term.do}`do` 元素还必须提供 {deftech}_控制信息_。
这描述了自定义元素如何与周围的控制结构和可变变量交互。
控制信息允许Lean生成适当的代码；特别是，它允许 {name Lean.Elab.Do.DoElemCont.withDuplicableCont}`DoElemCont.withDuplicableCont` 分析延续要详细说明的代码，从而实现更好的代码生成。
控制信息与精化器是分开的，因为精化器需要能够在精化子元素之前分析子元素的_语法_，以便知道如何构造其延续。
*定制 {keywordOf Lean.Parser.Term.do}`do` 元件必须提供准确的控制信息。不正确的控制信息可能会导致错误的代码生成。*

:::syntax attr (title := "Do Element Control Information")
```grammar
doElem_control_info
```
{includeDocstring Lean.Elab.Do.controlInfoElemAttribute}
:::

{docstring Lean.Elab.Do.ControlInfoHandler}

如果 {keywordOf Lean.Parser.Term.do}`do` 元素既不重新分配变量也不导致提前返回或终止，则处理程序可以返回 {name Lean.Elab.Do.ControlInfo.pure}`ControlInfo.pure`。
如果它表示没有常规退出且没有其他控制效果的代码，则处理程序可以返回 {name Lean.Elab.Do.ControlInfo.empty}`ControlInfo.empty`；否则，将 {name Lean.Elab.Do.ControlInfo.numRegularExits}`ControlInfo.numRegularExits` 设置为 {lean}`0`，将 {name Lean.Elab.Do.ControlInfo.noFallthrough}`ControlInfo.noFallthrough` 设置为 {lean}`true`，同时记录任何早期返回、重新分配或循环终止。


{docstring Lean.Elab.Do.ControlInfo}

{docstring Lean.Elab.Do.ControlInfo.pure +allowMissing}

{docstring Lean.Elab.Do.ControlInfo.empty}

如果 {keywordOf Lean.Parser.Term.do}`do` 元素本身包含其他 {keywordOf Lean.Parser.Term.do}`do` 元素，则它可以使用组合器 {name Lean.Elab.Do.ControlInfo.sequence}`ControlInfo.sequence` 和 {name Lean.Elab.Do.ControlInfo.alternative}`ControlInfo.alternative` 来组合来自其子元素的控制信息。
{name Lean.Elab.Do.ControlInfo.sequence}`ControlInfo.sequence` 用于顺序步骤，{name Lean.Elab.Do.ControlInfo.alternative}`ControlInfo.alternative` 用于合并控制流分支。

{docstring Lean.Elab.Do.ControlInfo.sequence +allowMissing}

{docstring Lean.Elab.Do.ControlInfo.alternative +allowMissing}

一般来说，控制信息应使用{name Lean.Elab.Do.inferControlInfoElem}`inferControlInfoElem`或{name Lean.Elab.Do.inferControlInfoSeq}`inferControlInfoSeq`计算。

{docstring Lean.Elab.Do.inferControlInfoElem +allowMissing}

{docstring Lean.Elab.Do.inferControlInfoSeq +allowMissing}

在某些高级情况下，可能需要 {namespace}`Lean.Elab.Do.InferControlInfo` 中的功能之一：

{docstring Lean.Elab.Do.InferControlInfo.ofElem +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofSeq +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofOptionSeq +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofLetOrReassign +allowMissing}

{docstring Lean.Elab.Do.InferControlInfo.ofLetOrReassignArrow +allowMissing}

## 可变变量

上下文的一个重要部分是可用于正在详细说明的 {keywordOf Lean.Parser.Term.do}`do` 元素的一组可变变量。
这在两个字段中可用：{name Lean.Elab.Do.Context.mutVars}`mutVars` 提供最初绑定变量的标识符，而 {name Lean.Elab.Do.Context.mutVarDefs}`mutVarDefs` 将它们的名称映射到表示它们的局部变量。
由于{tech}[卫生]，{name Lean.Elab.Do.Context.mutVars}`mutVars`中的标识符包含{tech}[宏范围]；在构建面向用户的错误消息之前，应使用 {name}`Name.simpMacroScopes` 删除这些内容。

每个可变变量对应至少一个详细变量 ({name}`Expr.fvar`)。
这些详细变量存在于跟踪其用户可见名称的本地上下文中。
突变是通过影子 {keywordOf Lean.Parser.Term.«let»}`let` 绑定实现的，并且 {keywordOf Lean.Parser.Term.do}`do` 块中的后续步骤在上下文中详细说明，其中该影子 {keywordOf Lean.Parser.Term.«let»}`let` 是变量的用户可见名称的绑定。
使用标准精化帮助程序 {name}`Lean.Meta.getFVarFromUserName` 和 {name}`Lean.Meta.getLocalDeclFromUserName` 检索与用户名关联的局部变量，并使用 {name}`TSyntax.getId` 将 {name}`Ident` 转换为可查找的用户名。

当使用 {keywordOf Lean.Parser.Term.doLet}`let mut` 建立可变变量时，将创建一个 {keywordOf Lean.Parser.Term.«let»}`let` 绑定来表示它，并且初始变量的绑定标识符和 {name}`Expr.fvar` 将添加到在延续周围使用的上下文，该延续在 {name}`withReader` 下调用以添加新变量。
建立 {keywordOf Lean.Parser.Term.«let»}`let` 绑定后，使用 {name Lean.Elab.Do.declareMutVar}`declareMutVar` 注册一个可变变量或一组可变变量。

{docstring Lean.Elab.Do.declareMutVar}

{docstring Lean.Elab.Do.declareMutVars}

要确保标识符引用可变变量，请使用 {name Lean.Elab.Do.throwUnlessMutVarDeclared}`throwUnlessMutVarDeclared`：

{docstring Lean.Elab.Do.throwUnlessMutVarDeclared}

{docstring Lean.Elab.Do.throwUnlessMutVarsDeclared}

::::example "Tracing Mutable Variables"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
新语法 {keywordOf dbgMut}`dbg_mut` 跟踪所有可变变量的当前值。

```lean
syntax (name := dbgMut) "dbg_mut" : doElem

@[doElem_elab dbgMut] def elabDbgMut : DoElab := fun _stx cont => do
  let ctx ← readThe Do.Context
  let parts : Array Term ← ctx.mutVars.mapM fun (x : Ident) => do
    let nameLit := x.getId.simpMacroScopes.toString
    `(term| s!"{$(quote nameLit)} = {repr $x}")
  let msg ← `(term| String.intercalate ", " [$parts,*])
  elabDoElem (← `(doElem| dbg_trace $msg)) cont
```

{keywordOf dbgMut}`dbg_mut` 没有有趣的控制信息。
```lean
@[doElem_control_info dbgMut]
def dbgMut.control : ControlInfoHandler := fun _ => do return .pure
```

跟踪计算斐波那契数的循环会显示所有中间状态：
```lean (name := mutDbg)
#eval show IO Unit from do
  let mut x := 1
  let mut y := 1
  for _ in 0...5 do
    let z := y
    dbg_mut
    y := x + y
    x := z
```
```leanOutput mutDbg
x = 1, y = 1
x = 1, y = 2
x = 2, y = 3
x = 3, y = 5
x = 5, y = 8
```
::::

可变变量的内置精化器负责许多微妙的细节，例如将可变变量的每个生成的 {keywordOf Lean.Parser.Term.«let»}`let` 绑定注册为别名，以便 IDE 可以提供适当的反馈。
如果可能的话，最好通过宏或通过在适当的语法上调用 {name Lean.Elab.Do.elabDoElem}`elabDoElem` 来重用这些内置的精化器。

:::example "Mutating Variables"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do
set_option backward.do.legacy false
```
运算符 {keywordOf doCensor}`censor` 将所有可变变量替换为其类型的 {name}`Inhabited` 实例中定义的默认值。

```lean
syntax (name := doCensor) "censor" : doElem

@[doElem_elab doCensor]
def elabCensor : DoElab := fun stx dec => do
  let vars := (← readThe Do.Context).mutVars
  let dec ← dec.ensureUnitAt stx
  if h : vars.size = 0 then
    logErrorAt stx "There are no mutable variables to censor."
    dec.continueWithUnit
  else
    let assigns ← vars.mapM fun v =>
      `(doElem| $v:ident := Inhabited.default)
    elabDoElems1 assigns dec
```

{keywordOf Lean.Parser.Term.do}`do`-精化上下文在控制信息处理程序中不可用，因此无法精确返回正在修改的所有可变变量的集合。
然而，所有局部变量的用户名都是一个合适的过度近似：
```lean
@[doElem_control_info doCensor]
def doCensor.control : ControlInfoHandler := fun _ => do
  return { ControlInfo.pure with
      reassigns := (← getLCtx).decls.map (·.map (·.userName))
        |>.foldl (init := .empty) fun
          | names, some n => names.insert n
          | names, none => names
    }
```

使用 {keywordOf doCensor}`censor` 后，所有可变变量都已重置为其类型的默认值：
```lean (name := censor)
#eval show IO Unit from do
  let mut x := 0
  let mut c := 'm'
  x := x + 1
  IO.println s!"x: {x}, c: {c}"
  c := 'f'
  IO.println s!"x: {x}, c: {c}"
  censor
  IO.println s!"x: {x}, c: {c}"
```
```leanOutput censor
x: 1, c: m
x: 1, c: f
x: 0, c: A
```

:::

## 提升效果
%%%
tag := "do-elab-effect-lift"
%%%

许多有用的单子运算符采用返回类型在单子内的函数，以某种修改的方式运行该函数。
示例包括 {name}`withReader`、{name}`tryCatch` 和 {name}`IO.FS.withFile`。
像 {name}`tryCatch` 这样的函数具有专用语法，允许可能引发异常的代码和处理异常的代码成为周围 {keywordOf Lean.Parser.Term.do}`do` 块的一部分，因此能够重新分配可变变量或提前返回。
这些其他运算符没有这样的语法。

{keywordOf Lean.Parser.Term.do}`do` 元素精化器可以将传递给详细表达式中的这些运算符之一的函数体安排为源 {keywordOf Lean.Parser.Term.do}`do` 块的一部分，就像异常处理语法一样。
这是使用 {name Lean.Elab.Do.ControlLifter}`ControlLifter` 完成的，它围绕 {keywordOf Lean.Parser.Term.do}`do` 元素的内部序列和函数本身生成合适的包装器代码。
共有三个步骤：
1. 内部序列的 {name Lean.Elab.Do.ControlLifter}`ControlLifter` 是使用 {name Lean.Elab.Do.ControlLifter.ofCont}`ControlLifter.ofCont` 根据其控制信息和当前元素的延续创建的。
2. 内部序列使用 {name Lean.Elab.Do.ControlLifter.lift}`ControlLifter.lift` 进行详细说明，它为内部精化器提供生成包装代码的合适延续。
3. 精化器不调用原始延续，而是调用 {name Lean.Elab.Do.ControlLifter.restoreCont}`ControlLifter.restoreCont` 生成的延续，这会向结果添加合适的解包代码。

提升代码类似于 Lean 的内置 {ref "monad-transformers"}[monad 变压器] 的实现。
例如，如果内部 {keywordOf Lean.Parser.Term.do}`do` 序列改变一个变量，则包装和解包代码会安排该变量传递给提升的代码并以元组形式返回，就像 {name}`StateT` 一样。
如果内部 {keywordOf Lean.Parser.Term.do}`do` 序列可能引发异常，则提升版本类似于 {name}`ExceptT` 的使用。

{docstring Lean.Elab.Do.ControlLifter +allowMissing}

{docstring Lean.Elab.Do.ControlLifter.ofCont +allowMissing}

{docstring Lean.Elab.Do.ControlLifter.lift +allowMissing}

{docstring Lean.Elab.Do.ControlLifter.restoreCont +allowMissing}

:::example "Syntax for {name}`withReader`"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do Term
set_option backward.do.legacy false
```

在 {keywordOf Lean.Parser.Term.do}`do` 块中，{keywordOf doLocally}`locally` 允许使用修改后的 {name}`MonadReader` 上下文运行一系列 {keywordOf Lean.Parser.Term.do}`do` 元素：

```lean
syntax (name := doLocally)
  "locally " ident " => " termBeforeDo " do " doSeq : doElem
```

{name Lean.Parser.Term.termBeforeDo}`termBeforeDo` 解析器匹配 Lean 术语，这些术语本身不包含括号或方括号之外的 {keywordOf Lean.Parser.Term.do}`do`。
由于此新语法包含一系列 {keywordOf Lean.Parser.Term.do}`do` 元素，因此必须根据这些元素计算其控制信息：
```lean
@[doElem_control_info doLocally]
def inferLocally : ControlInfoHandler := fun stx => do
  let `(doElem| locally $_:ident => $_ do $seq) := stx
    | throwUnsupportedSyntax
  InferControlInfo.ofSeq seq
```

实际的精化器首先计算主体的控制信息，然后从控制信息和原始延续中导出控制提升器。
这个控制举升机可以修饰身体；它为精化器提供了自己的延续。
普通术语精化技术用于构造 {name}`withReader` 的应用程序，特别注意确保函数参数是在 monad 的正确宇宙中使用非依赖函数类型来详细说明的（在 {name}`Context.monadInfo` 中可用作 {name}`MonadInfo.u`）。
最后，再次使用控制提升器为完整的精化结果重建合适的延续：
```lean
@[doElem_elab doLocally] def elabDoLocally : DoElab := fun stx dec => do
  let `(doElem| locally $x:ident => $e do $seq) := stx
    | throwUnsupportedSyntax
  let lifter ← ControlLifter.ofCont (← inferControlInfoElem stx) dec
  let body ← lifter.lift (elabDoSeq seq)
  let ρ ← Meta.mkFreshExprMVar (mkSort (.succ (← read).monadInfo.u))
  let f ← Term.elabTermEnsuringType (← `(fun $x => $e)) (← mkArrow ρ ρ)
  Term.synthesizeSyntheticMVarsNoPostponing
  let wrapped ← Meta.mkAppM ``MonadWithReaderOf.withReader #[f, body]
  (← lifter.restoreCont).mkBindUnlessPure wrapped
```

有了这个精化器，{name}`ReaderT` 提供的值可以被本地覆盖，同时仍然允许与周围 {keywordOf Lean.Parser.Term.do}`do` 块相关的效果：
```lean (name := locallyDemo)
abbrev App := ReaderT Nat Id

#eval show Id Nat from do
  Id.run <| (·.run 5) <| show App Nat from do
    let mut total := 0
    total := total + (← read)
    locally r => r + 100 do
      -- Mutates an outer variable
      total := total + (← read)
      if (← read) > 1000 then
        -- Early return from the outer block
        return 999
    return total
```
```leanOutput locallyDemo
110
```
:::

:::example "Locally Violating Invariants"
```imports -show
import Lean.Elab
```
```lean -show
open Lean Elab Do Term Meta
open Lean.Parser.Term (doSeq)
set_option backward.do.legacy false
```
当需要维护可变变量的某些不变量时，使用子类型通常是最方便的。
然而，子类型有一个缺点，即必须_始终_维持不变式；它不能在本地被破坏并重新建立。
虽然可以使用第二个可变变量来实现此目的，但这会使代码变得混乱并且容易出错。
通过对 {keywordOf Lean.Parser.Term.do}`do` 表示法的适当扩展，可以方便地局部破坏和重新建立不变量。

第一步是建立此操作的语法。
{keywordOf openMutPure}`open mut` 将“打开”子类型，将所包含的数据从嵌套块中谓词的限制中释放出来。
区块完成后，用户必须证明或检查不变量是否成立；将 {keywordOf Lean.Parser.Term.do}`do` 块放置在 {keywordOf openMutPure}`invariant` 部分中表示要执行动态检查。
第二个语法定义具有明确的高优先级以避免歧义，这确保只要存在 {keywordOf Lean.Parser.Term.do}`do` 块就使用它。
```lean
syntax (name := openMutPure)
  "open" "mut" ident "do" doSeq "invariant" term : doElem

syntax (name := openMutMon) (priority := high)
  "open" "mut" ident "do" doSeq "invariant" "do" doSeq : doElem
```

这些操作的控制信息处理程序是嵌入式 {name}`doSeq` 语法的函数：
```lean
@[doElem_control_info openMutPure, doElem_control_info openMutMon]
def openMutInfo : ControlInfoHandler := fun
  | `(doElem|open mut $x do $steps invariant do $steps') => do
    let info ← inferControlInfoSeq steps
    let info' ← inferControlInfoSeq steps'
    return info.sequence info'
  | `(doElem|open mut $x do $steps invariant $tm:term) =>
    inferControlInfoSeq steps
  | _ => throwUnsupportedSyntax
```

精化器的主要功能是执行以下操作的助手：
1. 它确保提供的名称实际上引用具有子类型的变量，提取基本类型和谓词。
2. 它从子类型中提取内部值。
3. 它 {keywordOf Lean.Parser.Term.«let»}`let` 绑定内部值，将 {keywordOf Lean.Parser.Term.«let»}`let` 绑定变量建立为别名并安排其可变。
4. 它通过调用所提供的精化器的延续来详细说明主体，该延续“关闭”子类型，重新建立不变量。
```lean
def openMutBody (x : Ident) (seq : TSyntax ``doSeq)
    (mkClose : (p outerTy : Expr) → (base : FVarId) → DoElabM Expr) :
    DoElabM Expr := do
  -- Ensure that it is mutable
  throwUnlessMutVarDeclared x
  -- Ensure that it is a subtype
  let outerDecl ← getLocalDeclFromUserName x.getId
  let ty ← whnf outerDecl.type
  let (``Subtype, #[α, p]) := ty.getAppFnArgs
    | throwError "`open mut`: `{x}` is not a subtype, but is a `{ty}`"

  -- Get the value from the subtype
  let base := outerDecl.fvarId
  let init ← mkAppM ``Subtype.val #[outerDecl.toExpr]

  -- Let-bind and continue
  withLetDecl x.getId α init (nondep := false) fun innerX => do
    addLocalVarInfo x innerX
    pushInfoLeaf <| .ofFVarAliasInfo {
      userName := x.getId, id := innerX.fvarId!, baseId := base
    }
    let bodyCont : DoElemCont := {
      resultName := ← mkFreshUserName `__r, resultType := ← mkPUnit
      k := mkClose p outerDecl.type base
    }
    mkLetFVars #[innerX] (← declareMutVar x do elabDoSeq seq bodyCont)
```

对 {name}`addLocalVarInfo` 的调用会通知语言服务器有关详细的 {keywordOf Lean.Parser.Term.«let»}`let` 绑定变量与源代码中的标识符之间的连接，从而启用悬停时的类型信息等功能。
{name}`pushInfoLeaf` 与 {name}`Info.ofFVarAliasInfo` 组合将 {keywordOf Lean.Parser.Term.«let»}`let` 绑定变量注册为现有绑定的别名。

关闭纯版本包括引入新的 {keywordOf Lean.Parser.Term.«let»}`let` 绑定、对可变变量进行遮蔽和别名，以及更新的值和证明。
```lean
def rebindMut (x : Ident) (outerTy repacked : Expr) (base : FVarId)
    (dec : DoElemCont) : DoElabM Expr :=
  withLetDecl x.getId outerTy repacked (nondep := false) fun newX => do
    addLocalVarInfo x newX
    pushInfoLeaf <| .ofFVarAliasInfo {
      userName := x.getId, id := newX.fvarId!, baseId := base
    }
    mkLetFVars #[newX] (← dec.continueWithUnit)

```

纯净版的精化器连接两部分：
```lean
@[doElem_elab openMutPure]
def elabOpenMutPure : DoElab := fun stx dec => do
  let `(doElem| open mut $x:ident do $seq invariant $prf:term) := stx
    | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt x
  openMutBody x seq fun p outerTy base => do
    let cur ← getFVarFromUserName x.getId
    let proof ← Term.elabTermEnsuringType prf (mkApp p cur)
    rebindMut x outerTy (← mkAppM ``Subtype.mk #[cur, proof]) base dec
```

要实际演示此功能，请采用非零自然数的 {name}`Pos` 类型：
```lean
abbrev Pos := { n : Nat // 0 < n }
```

在 {keywordOf openMutPure}`open` 块内，`x` 的类型为 {name}`Nat`。
它和其他可变变量都可以重新分配：
```lean (name := openDemo)
#eval show Id (Pos × Nat) from do
  let mut other := 100
  let mut x : Pos := ⟨10, by grind⟩
  open mut x do
    x := x * 2
    other := other + x
    x := x + 1
  invariant by grind
  return (x, other)
```
```leanOutput openDemo
(21, 120)
```

同样，内部块可以来自外部 {keywordOf Lean.Parser.Term.do}`do` 块的 {keywordOf Lean.Parser.Term.doReturn}`return`：
```lean (name := openDemo2)
#eval show Id (Nat × Nat) from do
  let mut other := 100
  let mut x : Pos := ⟨10, by grind⟩
  open mut x do
    x := x * 2
    other := other + x
    if other > 0 then return (0, other)
    x := x + 1
  invariant by grind
  return (x.val, other)
```
```leanOutput openDemo2
(0, 120)
```

对于无法证明返回值满足谓词的情况，_检查_它是否满足仍然有用。
单子变体的精化器期望返回 {name}`PLift` 的证明：
```lean
def closeInvariant {α : Type} {P : α → Prop} [Monad m]
    (val : α) (act : m (PLift (P val))) : m (Subtype P) :=
  return ⟨val, (← act).down⟩

@[doElem_elab openMutMon]
def elabOpenMutMon : DoElab := fun stx dec => do
  let `(doElem| open mut $x:ident do $seq invariant do $invSeq) := stx
    | throwUnsupportedSyntax
  let dec ← dec.ensureUnitAt x
  openMutBody x seq fun _p outerTy base => do
    let cur ← getFVarFromUserName x.getId
    let actionStx ←
      ``(closeInvariant $(← Term.exprToSyntax cur) (do $invSeq))
    let action ← elabTermEnsuringType actionStx (← mkMonadApp outerTy)
    let rn ← mkFreshUserName `__repacked
    let closeCont : DoElemCont := {
      resultName := rn, resultType := outerTy
      k := do
        let d ← getLocalDeclFromUserName rn
        rebindMut x outerTy d.toExpr base dec
    }
    closeCont.mkBindUnlessPure action
```

现在，运行时检查可以确保不变式，如果不成立则抛出异常：
```lean
def trySub3 (x : Pos) : IO Pos := do
  let mut x := x
  open mut x do
    x := x - 3
  invariant do
    if h : 0 < x then pure ⟨h⟩
    else throw (IO.userError s!"Not positive: x = {x}")
  return x
```
```lean (name := openMutMon1)
#eval trySub3 ⟨10, by grind⟩
```
```leanOutput openMutMon1
7
```
```lean +error  (name := openMutMon2)
#eval trySub3 ⟨3, by grind⟩
```
```leanOutput openMutMon2
Not positive: x = 0
```

:::
