/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "电子匹配" =>
%%%
file := "E___matching"
tag := "e-matching"
%%%

{deftech}_E-matching_ 是一个使用基本术语有效实例化量化定理陈述的过程。
它广泛应用于 SMT 求解器，{tactic}`grind` 使用它来高效地实例化定理。
与 {tech (key := "congruence closure")}[同余闭包] 结合使用时特别有效，使 {tactic}`grind` 能够自动发现等式和注释定理的非明显后果。

电子匹配根据定理索引向隐喻白板添加新事实。
当白板包含与索引匹配的术语时，电子匹配引擎会实例化相应的定理，并且生成的术语可以为进一步的 {tech (key := "congruence closure")}[同余闭包]、{tech (key := "constraint propagation")}[约束传播] 和特定于理论的求解器提供数据。
通过电子匹配添加到白板的每个事实都称为 {deftech (key := "e-matching instance")}_instance_。
注释电子匹配定理，从而将它们添加到索引中，对于 {tactic}`grind` 有效利用库至关重要。

除了用户指定的定理之外，{tactic}`grind` 使用自动生成的 {keywordOf Lean.Parser.Term.match}`match` 表达式方程作为 E 匹配定理。
在幕后，{tech (key := "Lean elaborator")}[精化器] 生成实现模式匹配的辅助函数，以及指定其行为的方程定理。
将这些方程与 E 匹配结合使用，{tactic}`grind` 能够减少模式匹配的这些实例。


# 图案
%%%
file := "Patterns"
tag := "e-matching-patterns"
%%%

电子匹配索引是一个_patterns_表。
当一个术语与表中的模式之一匹配时，{tactic}`grind` 尝试实例化并应用相应的定理，从而产生更多的事实和等式。
选择适当的模式是有效使用 {tactic}`grind` 的重要组成部分：如果模式限制太多，则可能无法应用有用的定理；如果它们太笼统，性能可能会受到影响。


::::example "E-matching Patterns"
考虑以下函数和定理：
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```

```lean -show
variable {x a b : Nat}
```
定理 {lean}`gf` 断言 {lean}`g (f x) = x` 对于所有自然数{lean}`x`。
属性 {attr}`grind =` 指示 {tactic}`grind` 使用等式左侧 {lean}`g (f x)` 作为通过 E 匹配进行启发式实例化的模式。

此证明目标不包括 {lean}`g (f x)` 的实例，但 {tactic}`grind` 仍然能够解决它：
```lean
example {a b} (h : f b = a) : g a = b := by
  grind
```

尽管 {lean}`g a` 不是模式 {lean}`g (f x)` 的实例，但它会以方程 {lean}`f b = a` 为模。
通过在 {lean}`g a` 中用 {lean}`f b` 替换 {lean}`a`，我们获得术语 {lean}`g (f b)`，它与模式 {lean}`g (f x)` 和赋值 `x := b` 相匹配。
因此，定理 {lean}`gf` 被实例化为 `x := b`，并且断言新的等式 {lean}`g (f b) = b`。
{tactic}`grind` 然后使用同余闭包导出隐含等式 {lean}`g a = g (f b)` 并完成证明。
::::


{keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` 命令可用于手动选择定理的 E 匹配模式。
启用选项 {option}`trace.grind.ematch.instance` 会导致 {tactic}`grind` 为其生成的每个定理实例打印一条跟踪消息，这在确定 E 匹配模式时很有帮助。

:::syntax command (title := "E-matching Pattern Selection")
```grammar
grind_pattern $_ => $_,*
```
将定理与一个或多个模式相关联。
当单个 {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` 命令中提供多个模式时，所有模式都必须与 {tactic}`grind` 尝试实例化定理之前的项匹配。

```grammar
grind_pattern $_ => $_,* where $_
```
可选的 {keywordOf Lean.Parser.Command.grind_pattern}`where` 子句指定在 {tactic}`grind` 尝试实例化定理之前必须满足的约束。
每个约束的形式为 `variable =/= value`，防止在为模式变量分配指定值时实例化。
这对于避免有问题的术语的无限制或过度实例化很有用。
:::

::::example "Selecting Patterns"
{attr}`grind =` 属性使用等式的左侧作为 {lean}`gf` 的 E 匹配模式：
```lean
def f (a : Nat) : Nat :=
  a + 1

def g (a : Nat) : Nat :=
  a - 1

@[grind =]
theorem gf (x : Nat) : g (f x) = x := by
  simp [f, g]
```

例如，模式 `g (f x)` 在以下情况下限制过多：
定理 `gf` 不会被实例化，因为目标甚至没有
包含功能符号 `g`。

在此示例中，{tactic}`grind` 失败，因为模式限制太多：目标不包含函数符号 {lean}`g`。
```lean +error (name := restrictivePattern)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```
```leanOutput restrictivePattern (expandTrace := eqc)
`grind` failed
case grind
b a c : Nat
h₁ : f b = a
h₂ : f c = a
h : ¬b = c
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] b = c
  [eqc] Equivalence classes
    [eqc] {a, f b, f c}
```

仅使用 `f x` 作为模式允许 {tactic}`grind` 自动解决目标：
```lean
grind_pattern gf => f x

example {a b c} (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  grind
```

启用 {option}`trace.grind.ematch.instance` 可以查看通过 E 匹配找到的等式：
```lean (name := ematchInstanceTrace)
example (h₁ : f b = a) (h₂ : f c = a) : b = c := by
  set_option trace.grind.ematch.instance true in
  grind
```
```leanOutput ematchInstanceTrace
[grind.ematch.instance] gf: g (f c) = c
[grind.ematch.instance] gf: g (f b) = b
```

E-匹配后，证明成功，因为同余闭包使 `g (f c)` 与 `g (f b)` 相等，因为 `f b` 和 `f c` 都等于 `a`。
因此，`b` 和 `c` 必须属于同一等价类。

::::

当同时指定多个模式时，在 {tactic}`grind` 尝试实例化定理之前，所有模式都必须在当前上下文中匹配。
这称为 {deftech}_multi-pattern_。
这对于诸如传递性规则之类的引理很有用，其中必须同时存在多个前提才能应用规则。
通过使用 {keywordOf Lean.Parser.Command.grind_pattern}`grind_pattern` 或 {attrs}`@[grind _=_]` 属性的多次调用，单个定理可以与多个单独的模式相关联。
如果这些单独模式中的任何一个匹配，则该定理将被实例化。

::::example "Multi-Patterns"

{lean}`R` 是 {lean}`Int` 上的传递二元关系：
```lean
opaque R : Int → Int → Prop
axiom Rtrans {x y z : Int} : R x y → R y z → R x z
```

要利用 {lean}`R` 具有传递性的事实，{tactic}`grind` 必须已经能够满足两个前提。
这是使用 {tech (key := "multi-pattern")}[多模式] 表示的：
```lean
grind_pattern Rtrans => R x y, R y z

example {a b c d} : R a b → R b c → R c d → R a d := by
  grind
```

```lean -show
variable {x y z a b c d : Int}
```

仅当 {lean}`R x y` 和 {lean}`R y z` 在上下文中可用时，多模式 `R x y, R y z` 才指示 {tactic}`grind` 实例化 {lean}`Rtrans`。
在该示例中，{tactic}`grind` 应用 {lean}`Rtrans` 从 {lean}`R a b` 和 {lean}`R b c` 导出 {lean}`R a c`，然后可以重复相同的推理从 {lean}`R a c` 和 {lean}`R c d` 导出 {lean}`R a d`。
::::

::::example "Pattern Constraints"
某些定理组合可能会导致无限实例化，其中 E 匹配会重复生成越来越长的项。
考虑有关 {name}`List.flatMap` 和 {name}`List.reverse` 的定理。
如果 {name}`List.flatMap_def`、{name}`List.flatMap_reverse` 和 {name}`List.reverse_flatMap` 都用 {attrs}`@[grind =]` 进行注释，则一旦实例化 {name}`List.flatMap_reverse`，就会发生以下实例化链，从而使用 {name}`List.reverse` 创建逐渐更长的函数组合。
这可以使用 `#grind_lint` 命令观察到：
```
attribute [local grind =] List.reverse_flatMap

set_option trace.grind.ematch.instance true in
#grind_lint inspect List.flatMap_reverse
```
跟踪输出显示无界实例化：
```
[grind.ematch.instance] List.flatMap_def: List.flatMap (List.reverse ∘ f) l = (List.map (List.reverse ∘ f) l).flatten
[grind.ematch.instance] List.flatMap_def: List.flatMap f l.reverse = (List.map f l.reverse).flatten
[grind.ematch.instance] List.flatMap_reverse: List.flatMap f l.reverse = (List.flatMap (List.reverse ∘ f) l).reverse
[grind.ematch.instance] List.reverse_flatMap: (List.flatMap (List.reverse ∘ f) l).reverse =
  List.flatMap (List.reverse ∘ List.reverse ∘ f) l.reverse
[grind.ematch.instance] List.flatMap_def: List.flatMap (List.reverse ∘ List.reverse ∘ f) l.reverse =
  (List.map (List.reverse ∘ List.reverse ∘ f) l.reverse).flatten
```

这种模式无限期地持续下去，每次迭代都会向合成中添加另一个 {name}`List.reverse`。
{keywordOf Lean.Parser.Command.grind_pattern}`where` 子句通过排除有问题的实例化来防止这种情况：
```
grind_pattern reverse_flatMap => (l.flatMap f).reverse where
  f =/= List.reverse ∘ _
```
这指示 {tactic}`grind` 使用模式 `(l.flatMap f).reverse`，但仅当 `f` 不是与 {name}`List.reverse` 的组合时，防止无限的实例化链。

您可以使用 `#grind_lint check` 查找有问题的模式，或使用 `#grind_lint check in List` 或 `#grind_lint check in module Std.Data` 在特定命名空间或模块中查找。
::::

{attr}`grind` 属性使用启发式自动生成 E 匹配模式或多模式，而不是使用 {keywordOf Lean.Parser.Command.grindPattern}`grind_pattern` 显式指定模式。
它包括许多选择不同启发式的变体。
{attr}`grind?` 属性显示一条信息消息，显示所选模式 - 这对于调试非常有帮助！

模式是定理陈述的子表达式。
如果子表达式具有可索引常量作为其头部，则该子表达式为 {deftech}_indexable_；如果它修复了参数的值，则称其为 {deftech}_cover_ 定理的参数之一。
可索引常量是除 {name}`Eq`、{name}`HEq`、{name}`Iff`、{name}`And`、{name}`Or` 和 {name}`Not` 之外的所有常量。
模式或多模式覆盖的参数集称为其 {deftech}_coverage_。
某些常量的优先级低于其他常量；特别是，算术运算符 {name}`HAdd.hAdd`、{name}`HSub.hSub`、{name}`HMul.hMul`、{name}`Dvd.dvd`、{name}`HDiv.hDiv` 和 {name}`HMod.hMod` 具有低优先级。
如果不存在其头常量至少具有同样高优先级的更小的可索引子表达式，则可索引子表达式为 {deftech}_minimal_。

:::syntax attr (title := "Grind Patterns")
当 {attr}`grind` 属性添加到定义中时，每当遇到该定义时，它都会导致 `grind` 将该定义展开到其正文。
使用模块系统时，如果定义主体不可见（例如通过 {attrs}`@[expose]`），则忽略 {attr}`grind` 属性。

```grammar
grind $[$_:grindMod]?
```
{attr}`grind` 属性使用由提供的修饰符确定的策略自动生成定理的 E 匹配模式。
如果未提供修饰符，则 {attr}`grind` 会建议合适的修饰符，并显示结果模式。

```grammar
grind! $[$_:grindMod]?
```
{attr}`grind!` 属性使用由提供的修饰符确定的策略自动生成定理的 E 匹配模式。
它还强制执行以下条件：所选模式应该是最小可索引子表达式。

```grammar
grind? $[$_:grindMod]?
```

{attr}`grind?` 显示生成的模式。

```grammar
grind!? $[$_:grindMod]?
```
{attr}`grind!?` 属性与 {attr}`grind!` 等效，只不过它显示结果模式以供检查。


在没有任何修饰符的情况下，{attrs}`@[grind]` 从左到右遍历结论，然后遍历假设，在增加覆盖范围时添加模式，在覆盖所有参数时停止。
可以使用 {keywordOf Lean.Parser.Attr.grindDef}`.` 修饰符显式请求此默认策略。
除了使用默认策略之外，该属性还会检查可以应用哪些其他策略，并显示所有结果模式。
:::

```lean -keep -show
-- This test will start failing if new grind modifiers are added. It's to make sure they're all
-- documented (or at least that a decision has been made to _not_ document one of them).
open Lean Parser Attr
open Lean Elab Command

deriving instance Repr for ParserDescr

def getName : ParserDescr → CommandElabM String
  | .nodeWithAntiquot name .. => pure name
  | other => throwError m!"Expected a {.ofConstName ``nodeWithAntiquot}, got {repr other}"

def getOrElse (descr : ParserDescr) : CommandElabM (Array ParserDescr) := do
  match descr with
  | .binary `orelse x y => return (← getOrElse x) ++ (← getOrElse y)
  | other => return #[other]

def getGrindAlts (descr : ParserDescr) : CommandElabM (Array String) := do
  if let .nodeWithAntiquot "grindMod" ``grindMod d' := descr then
    let cases ← getOrElse d'
    return (← cases.mapM getName).qsort
  else throwError "Expected a {.ofConstName ``nodeWithAntiquot}, got {repr descr}"

/--
info: `grindMod` can be these:
grindBwd
grindCases
grindCasesEager
grindDef
grindEq
grindEqBoth
grindEqBwd
grindEqRhs
grindExt
grindFunCC
grindFwd
grindGen
grindInj
grindIntro
grindLR
grindNorm
grindRL
grindSym
grindUnfold
grindUsr
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let allMods ← getGrindAlts grindMod
  IO.println "`grindMod` can be these:"
  for gmod in allMods do
    IO.println gmod

```

:::syntax Lean.Parser.Attr.grindMod (title := "Default Pattern")
```grammar
.
```
```grammar
·
```
{includeDocstring Lean.Parser.Attr.grindDef}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Equality Rewrites")
```grammar
=
```
{includeDocstring Lean.Parser.Attr.grindEq}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Backward Equality Rewrites")
```grammar
=_
```
{includeDocstring Lean.Parser.Attr.grindEqRhs}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Bidirectional Equality Rewrites")
```grammar
_=_
```
{includeDocstring Lean.Parser.Attr.grindEqBoth}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Forward Reasoning")
```grammar
→
```
{includeDocstring Lean.Parser.Attr.grindFwd}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Backward Reasoning")
```grammar
←
```
{includeDocstring Lean.Parser.Attr.grindBwd}
:::

检查 {attrs}`@[grind]` 属性生成的模式以确保它们与引理的正确部分匹配非常重要。
如果模式太严格，则引理将不会应用于相关的情况，从而导致自动化程度降低。
如果它太笼统，那么性能将会受到影响，因为引理在许多情况下都没有帮助。

还有三个不太常用的引理修饰符：

:::syntax Lean.Parser.Attr.grindMod (title := "Left-to-Right Traversal")
```grammar
=>
```
```grammar
⇒
```
{includeDocstring Lean.Parser.Attr.grindLR}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Right-to-Left Traversal")
```grammar
<=
```
```grammar
⇐
```
{includeDocstring Lean.Parser.Attr.grindRL}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Backward Reasoning on Equality")
```grammar
←=
```
{includeDocstring Lean.Parser.Attr.grindEqBwd}
:::

:::example "The `@[grind ←=]` Attribute"
```lean -show
variable {α} {a b : α} [Inv α]
```
当尝试证明 {lean}`a⁻¹ = b` 时，由于 {attrs}`@[grind ←=]` 注释，{tactic}`grind` 使用 {name}`inv_eq`。
```lean
@[grind ←=]
theorem inv_eq [One α] [Mul α] [Inv α] {a b : α}
    (w : a * b = 1) : a⁻¹ = b :=
  sorry
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Function-Valued Congruence Closure")
```grammar
funCC
```
{includeDocstring Lean.Parser.Attr.grindFunCC}
:::


一些附加修饰符可用于向索引添加其他类型的引理。
这包括外延性定理、函数的单射定理以及将归纳定义的谓词的所有构造函数添加到索引的快捷方式。

:::syntax Lean.Parser.Attr.grindMod (title := "Extensionality")
```grammar
ext
```
{includeDocstring Lean.Parser.Attr.grindExt}

此外，将 {attrs}`@[grind ext]` 添加到结构中会注册其外延性定理。
:::


::::example "The `@[grind ext]` Attribute"

{lean}`Point` 是一个具有两个字段的结构：
```lean
structure Point where
  x : Int
  y : Int
```
默认情况下，{tactic}`grind` 可以解决这样的目标，因为 定义等价 包含产品类型的 {tech (key := "η-equivalence")}[η-equivalence]：
```lean
example (p : Point) : p = ⟨p.x, p.y⟩ := by grind
```
然而，它无法解决像这样需要诉诸命题等价的目标：
```lean +error (name := noExt)
example (p : Point) (a : Int) : a = p.x → p = ⟨a, p.y⟩ := by grind
```
```leanOutput noExt
`grind` failed
case grind
p : Point
a : Int
h : a = p.x
h_1 : ¬p = { x := a, y := p.y }
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
  [eqc] Equivalence classes
```


在证明定理时可能会出现这种目标，例如交换点的字段两次是恒等式的事实：
```lean
def Point.swap (p : Point) : Point := ⟨p.y, p.x⟩
```
```lean +error (name := noExt')
theorem swap_swap_eq_id : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
```leanOutput noExt'
`grind` failed
case grind
h : ¬((fun p => { x := p.y, y := p.x }) ∘ fun p => { x := p.y, y := p.x }) = id
w : Point
h_1 : ¬{ x := w.x, y := w.y } = id w
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [ematch] E-matching patterns

[grind] Diagnostics
```
将 {attrs}`@[grind ext]` 属性添加到 {name}`Point` 使 {tactic}`grind` 能够求解原始示例并证明该定理：
```lean
attribute [grind ext] Point

example (p : Point) (a : Int) : a = p.x → p = ⟨a, p.y⟩ := by
  grind

theorem swap_swap_eq_id' : Point.swap ∘ Point.swap = id := by
  unfold Point.swap
  grind
```
::::

:::syntax Lean.Parser.Attr.grindMod (title := "Injectivity")
```grammar
inj
```
{includeDocstring Lean.Parser.Attr.grindInj}
:::

:::example "Injectivity Patterns"
此函数 {name}`double` 将其参数加倍：
```lean
def double (x : Nat) : Nat := x + x
```
默认情况下，{tactic}`grind` 无法证明以下定理：
```lean +error
theorem A {n k : Nat} :
    double (n + 5) = double (k - 3) →
    n + 8 = k := by
  grind
```
但是，{name}`double` 是单射的，可以使用 {attr}`grind inj` 属性为 {tactic}`grind` 注册这一事实：
```lean
@[grind inj]
theorem double_inj : Function.Injective double := by
  simp only [double, Function.Injective]
  grind
```
这个单射引理足以证明以下定理：
```lean
theorem B {n k : Nat} :
    double (n + 5) = double (k - 3) →
    n + 8 = k := by
  grind
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Constructor Patterns")
```grammar
intro
```
{includeDocstring Lean.Parser.Attr.grindIntro}
:::

:::example "Patterns for Constructors"
谓词 {name}`Decreasing` 声明整数列表中的每个值都小于之前的值，函数 {name}`decreasing` 检查此属性，返回 {name}`Bool`。
```lean
inductive Decreasing : List Int → Prop
  | nil : Decreasing []
  | singleton : Decreasing [x]
  | cons : Decreasing (x :: xs) → y > x → Decreasing (y :: x :: xs)

def decreasing : List Int → Bool
  | [] | [_] => true
  | y :: x :: xs => y > x && decreasing (x :: xs)
```

如果当 {name}`Decreasing` 为其参数成立时，该函数恰好返回 {name}`true`，则该函数是正确的。
尝试使用 {tactic}`fun_induction` 和 {tactic}`grind` 的组合来证明这一事实立即失败，三种情况均未得到证明：
```lean +error (name := decreasingCorrect1)
def decreasingCorrect : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> grind
```
```leanOutput decreasingCorrect1
`grind` failed
case grind
h : True = ¬Decreasing []
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
```
```leanOutput decreasingCorrect1
`grind` failed
case grind
head : Int
h : True = ¬Decreasing [head]
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
```
```leanOutput decreasingCorrect1
`grind` failed
case grind.1
y x : Int
xs : List Int
ih1 : (decreasing (x :: xs) = true) = Decreasing (x :: xs)
h : (-1 * y + x + 1 ≤ 0 ∧ decreasing (x :: xs) = true) = ¬Decreasing (y :: x :: xs)
left : -1 * y + x + 1 ≤ 0
left_1 : decreasing (x :: xs) = true
right_1 : ¬Decreasing (y :: x :: xs)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
  [eqc] False propositions
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
```
将 {attr}`grind intro` 属性添加到 {name}`Decreasing` 会导致为三个构造函数中的每一个添加 E 匹配模式，之后 {tactic}`grind` 可以证明前两个目标，并且只需要对假设进行案例分析即可证明最终目标：
```lean
attribute [grind intro] Decreasing

def decreasingCorrect' : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> try grind
  case case3 y x xs ih =>
    apply propext
    constructor
    . grind
    . intro
      | .cons hDec hLt =>
        grind
```
将 {attr}`grind cases` 添加到 {name}`Decreasing` 可以自动进行案例分析，从而实现全自动证明：
```lean
attribute [grind cases] Decreasing

def decreasingCorrect'' : decreasing xs = Decreasing xs := by
  fun_induction decreasing <;> grind
```
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Unfolding During Preprocessing")
```grammar
unfold
```
{includeDocstring Lean.Parser.Attr.grindUnfold}
:::

:::syntax Lean.Parser.Attr.grindMod (title := "Normalization Rules")
```grammar
norm
```
{includeDocstring Lean.Parser.Attr.grindNorm}
:::

{TODO}[Document `gen` modifier for `grind` patterns]

# 检查模式
%%%
file := "Inspecting-Patterns"
tag := "zh-grind-ematching-h002"
%%%

{attr}`grind?` 属性是 {attr}`grind` 属性的一个版本，它另外显示生成的图案或 {tech (key := "multi-pattern")}[多图案]。
模式和多重模式显示为子表达式列表，每个子表达式都是一个模式；普通模式显示为单例列表。
在这些显示的模式中，定义的常量的名称按原样打印。
当定理的参数出现在模式中时，它们将使用数字而不是名称来显示。
特别地，它们是从右到左编号的，从0开始；该表示被称为 {deftech (key := "de Bruijn indices")}_de Bruijnindexs_。

:::example "Inspecting Patterns" (open := true)
为了使用 {tactic}`grind` 整除性可传递的证明，需要 E 匹配模式：
```lean
theorem div_trans {n k j : Nat} : n ∣ k → k ∣ j → n ∣ j := by
  intro ⟨d₁, p₁⟩ ⟨d₂, p₂⟩
  exact ⟨d₁ * d₂, by rw [p₂, p₁, Nat.mul_assoc]⟩
```
正确使用的属性是 {attrs}`@[grind →]`，因为每个前提都应该有一个模式。
使用 {attrs}`@[grind? →]`，可以查看生成了哪些模式：
```lean (name := grindHuh)
attribute [grind? →] div_trans
```
有两个：
```leanOutput grindHuh
div_trans: [@Dvd.dvd `[Nat] `[Nat.instDvd] #4 #3, @Dvd.dvd `[Nat] `[Nat.instDvd] #3 #2]
```
参数从右到左编号，因此 `#0` 是 `k ∣ j` 的假设，而 `#4` 是 `n`。
因此，这两个模式对应于术语 `n ∣ k` 和 `k ∣ j`。
:::

从假设和结论的子表达式中选择模式的规则是微妙的。
:::TODO
更多文字
:::

:::example "Forward Pattern Generation" (open := true)
```lean
axiom p : Nat → Nat
axiom q : Nat → Nat
```

```lean (name := h1)
@[grind!? →] theorem h₁ (w : p (q x) = 7) : p (x + 1) = q x := sorry
```
```leanOutput h1
h₁: [q #1]
```
图案为 `q x`。
从右数起，参数`#0`是前提`w`，参数`#1`是隐含参数`x`。

为什么是`@[grind! →]`？选择`q #1`？
属性 `@[grind! →]` 通过从左到右遍历假设（即类型为命题的参数）来查找模式。
在本例中，只有一个假设：`p (q x) = 7`。
上述启发式表示，{attr}`grind!` 将搜索最小的 {tech (key := "indexable")}[可索引] 子表达式，其中 {tech (key := "covers")}[覆盖] 先前未覆盖的参数。
只有一个未覆盖的参数，即 `x`。
整个假设 `p (q x) = 7` 无法使用，因为 {tactic}`grind` 不会对相等性进行索引。
右侧 `7` 没有帮助，因为它无法确定 `x` 的值。
`p (q x)` 不适合，因为它不是最小的：它内部有 `q x`，它是可转位的（其头部是常量 `q`），并且它决定了 `x` 的值。
表达式 `q x` 本身是最小的，因为 `x` 不可索引。
因此，选择 `q x` 作为模式。
:::

:::example "Backward Pattern Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```

在此示例中，{keywordOf Lean.Parser.Attr.grindMod}`←` 修饰符指示应在结论中找到该模式：
```lean (name := h2)
set_option trace.grind.debug.ematch.pattern true in
@[grind? ←] theorem h₂ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
使用等式的左侧是因为 {name}`Eq` 不可索引，并且 {name}`HAdd.hAdd` 的优先级低于 {lean}`p`。
```leanOutput h2
h₂: [p (#1 + 1)]
```
:::

:::example "Bidirectional Equality Pattern Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
在此示例中，根据相等结论生成两个单独的 E 匹配模式。
一个匹配左侧，另一个匹配右侧。
```lean (name := h3)
@[grind? _=_] theorem h₃ (w : 7 = p (q x)) : p (x + 1) = q x := sorry
```
```leanOutput h3
h₃: [q #1]
```

使用等式的整个左侧而不是仅使用 `x + 1`，因为 {name}`HAdd.hAdd` 的优先级低于 {lean}`p`。
```leanOutput h3
h₃: [p (#1 + 1)]
```
:::

:::example "Patterns from Conclusion and Hypotheses" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```

在没有任何修饰符的情况下，{attrs}`@[grind]` 通过首先检查结论然后检查前提来生成多重模式：
```lean (name := h4)
@[grind? .] theorem h₄ (w : p x = q y) : p (x + 2) = 7 := sorry
```
这里，参数 `x` 是 `#2`，`y` 是 `#1`，`w` 是 `#0`。
生成的多重模式包含等式的左侧，这是涵盖参数的结论的唯一 {tech}[minimal] {tech}[indexable] 子表达式（即 `x`）。
它还包含 `q y`，它是涵盖附加参数（即 `y`）的假设 `w` 的唯一最小可索引子表达式。
```leanOutput h4
h₄: [p (#2 + 2), q #1]
```
:::

:::example "Failing Backward Pattern Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
在此示例中，模式生成失败，因为定理的结论未提及参数 `y`。
```lean (name := h5) +error
@[grind? ←] theorem h₅ (w : p x = q y) : p (x + 2) = 7 := sorry
```
```leanOutput h5
`@[grind ←] theorem h₅` failed to find patterns in the theorem's conclusion, consider using different options or the `grind_pattern` command
```
:::

:::example "Left-to-Right Generation" (open := true)
```lean -show
axiom p : Nat → Nat
axiom q : Nat → Nat
```
在此示例中，模式是通过从左到右遍历前提生成的，然后得出结论：
```lean (name := h6)
@[grind? =>] theorem h₆
    (_ : q (y + 2) = q y)
    (_ : q (y + 1) = q y) :
    p (x + 2) = 7 :=
  sorry
```
在这些模式中，`y` 是参数 `#3`，`x` 是参数 `#2`，因为在定理语句中 {tech (key := "automatic implicit parameters")}[自动隐式参数] 是从左到右插入的，并且 `y` 出现在 `x` 之前。
前提是参数 `#1` 和 `#0`。
在生成的多重模式中，`y` 由第一个前提的子表达式覆盖，`z` 由结论的子表达式覆盖：
```leanOutput h6
h₆: [q (#3 + 2), p (#2 + 2)]
```
:::


# 资源限制
%%%
file := "Resource-Limits"
tag := "grind-limits"
%%%

电子匹配可以生成无限数量的定理 {tech (key := "e-matching instance")}[实例]。
出于效率和终止的考虑，{tactic}`grind` 使用两种机制限制电子匹配可以运行的次数：

: 生成

  每个项都被分配一个 {deftech (key := "generation")}_生成_，并且 E-matching 产生的项的生成比用于实例化定理的所有项的最大生成大一。
  E-matching 只考虑生成低于可配置阈值的项。
  {tactic}`grind` 的 `gen` 选项控制生成阈值。

: 轮次限制

  E-matching 引擎的每次调用都称为一个 {deftech (key := "round")}_轮次_。
  只执行有限轮次的 E-matching。
  `ematch` 至 {tactic}`grind` 选项控制轮数限制。


:::example "Too Many Instances" (open := true)

电子匹配会生成太多定理 {tech (key := "e-matching instance")}[实例]。
某些模式甚至可能生成无限数量的实例。

在此示例中，{name}`s_eq` 将添加到具有模式 `s x` 的索引中：
```lean (name := ematchUnboundedPat)
def s (x : Nat) := 0

@[grind? =] theorem s_eq (x : Nat) : s x = s (x + 1) :=
  rfl
```
```leanOutput ematchUnboundedPat
s_eq: [s #0]
```

尝试使用该定理会导致许多有关 {lean}`s` 的事实应用于生成的具体值。
特别是，{lean}`s_eq` 在五轮中的每一轮中都用新的 {lean}`Nat` 进行实例化。
首先，{tactic}`grind` 使用 `x := 0` 实例化 {lean}`s_eq`，从而生成项 {lean}`s 1`。
这与模式 `s x` 匹配，因此用于使用 `x := 1` 实例化 {lean}`s_eq`，从而生成术语 {lean}`s 2`，
依此类推，直到达到回合限制。
```lean +error (name := ematchUnbounded)
example : s 0 > 0 := by
  grind
```

```leanOutput ematchUnbounded (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```

由于默认生成限制为 8，将轮数限制增加到 20 会导致电子匹配终止：
```lean +error (name := ematchUnbounded2)
example : s 0 > 0 := by
  grind (ematch := 20)
```
```leanOutput ematchUnbounded2 (expandTrace := limits) (expandTrace := ematch) (expandTrace := facts)
`grind` failed
case grind
h : s 0 = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] s 0 = 0
    [prop] s 0 = s 1
    [prop] s 1 = s 2
    [prop] s 2 = s 3
    [prop] s 3 = s 4
    [prop] s 4 = s 5
    [prop] s 5 = s 6
    [prop] s 6 = s 7
    [prop] s 7 = s 8
  [eqc] Equivalence classes
  [ematch] E-matching patterns
    [thm] s_eq: [s #0]
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
    [limit] maximum term generation has been reached, threshold: `(gen := 8)`

[grind] Diagnostics
```
:::

:::example "Increasing E-matching Limits"


{lean}`iota` 返回严格小于其参数的所有数字的列表，定理 {lean}`iota_succ` 描述了其在 {lean}`Nat.succ` 上的行为：
```lean
def iota : Nat → List Nat
  | 0 => []
  | n + 1 => n :: iota n

@[grind =] theorem iota_succ : iota (n + 1) = n :: iota n :=
  rfl
```

{lean}`(iota 20).length > 10`这一事实可以通过重复实例化{lean}`iota_succ`和{lean}`List.length_cons`来证明。
但是，{tactic}`grind` 没有成功：
```lean +error (name := biggerGrindLimits)
example : (iota 20).length > 10 := by
  grind
```
```leanOutput biggerGrindLimits (expandTrace := limits) (expandTrace := facts)
`grind` failed
case grind
h : (iota 20).length ≤ 10
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] (iota 20).length ≤ 10
    [prop] iota 20 = 19 :: iota 19
    [prop] iota 19 = 18 :: iota 18
    [prop] (19 :: iota 19).length = (iota 19).length + 1
    [prop] iota 18 = 17 :: iota 17
    [prop] (18 :: iota 18).length = (iota 18).length + 1
    [prop] iota 17 = 16 :: iota 16
    [prop] (17 :: iota 17).length = (iota 17).length + 1
    [prop] iota 16 = 15 :: iota 15
    [prop] (16 :: iota 16).length = (iota 16).length + 1
  [eqc] True propositions
  [eqc] Equivalence classes
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints
  [ring] Ring `Lean.Grind.Ring.OfSemiring.Q Nat`
  [limits] Thresholds reached
    [limit] maximum number of E-matching rounds has been reached, threshold: `(ematch := 5)`

[grind] Diagnostics
```

由于电子匹配轮数有限，实例化链尚未完成。
增加这些限制可以使 {tactic}`grind` 成功：

```lean
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```

当选项 {option}`diagnostics` 设置为 {lean}`true` 时，{tactic}`grind` 显示它为每个定理生成的实例数。
这对于检测包含触发过多实例的模式的定理很有用。
在本例中，诊断显示 {name}`iota_succ` 被实例化 12 次：
```lean (name := grindDiagnostics)
set_option diagnostics true in
set_option diagnostics.threshold 10 in
example : (iota 20).length > 10 := by
  grind (gen := 20) (ematch := 20)
```
```leanOutput grindDiagnostics (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] iota_succ ↦ 12
    [thm] List.length_cons ↦ 11
  [app] Applications
  [grind] Simplifier
    [simp] used theorems (max: 15, num: 2):
    [simp] tried theorems (max: 46, num: 1):
    use `set_option diagnostics.threshold <num>` to control threshold for reporting counters
```
:::

默认情况下，{tactic}`grind` 使用自动生成的 {keywordOf Lean.Parser.Term.match}`match` 表达式方程作为 E 匹配定理。
可以通过将 `matchEqs` 标志设置为 {lean}`false` 来禁用此功能。

:::example "E-matching and Pattern Matching"

启用诊断显示 {tactic}`grind` 在 E 匹配期间使用辅助匹配函数的方程之一：
```lean (name := gt1diag)
theorem gt1 (x y : Nat) :
    x = y + 1 →
    0 < match x with
        | 0 => 0
        | _ + 1 => 1 := by
  set_option diagnostics true in
  grind
```
```leanOutput gt1diag (expandTrace := grind) (expandTrace := thm)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] gt1.match_1.congr_eq_2 ↦ 1
  [app] Applications
```
该定理有以下类型：
```lean (name := gt1matchtype)
#check gt1.match_1.congr_eq_2
```
```leanOutput gt1matchtype
gt1.match_1.congr_eq_2.{u_1} (motive : Nat → Sort u_1) (x✝ : Nat) (h_1 : Unit → motive 0)
  (h_2 : (n : Nat) → motive n.succ) (n✝ : Nat) (heq_1 : x✝ = n✝.succ) :
  (match x✝ with
    | 0 => h_1 ()
    | n.succ => h_2 n) ≍
    h_2 n✝
```

禁用匹配器函数方程的使用会导致证明失败：

```lean +error (name := noMatchEqs)
example (x y : Nat)
    : x = y + 1 →
      0 < match x with
          | 0 => 0
          | _+1 => 1 := by
  grind -matchEqs
```
```leanOutput noMatchEqs
`grind` failed
case grind.2
x y : Nat
h : x = y + 1
h_1 : (match x with
  | 0 => 0
  | n.succ => 1) =
  0
n : Nat
h_2 : x = n + 1
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] Equivalence classes
  [cases] Case analyses
  [cutsat] Assignment satisfying linear constraints
  [ring] Rings

[grind] Diagnostics
```
:::

{optionDocs trace.grind.ematch.instance}

:::comment
待定
* 反模式
* 局部属性与全局属性
* `gen` 修改器？
:::
