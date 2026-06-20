/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Lean (Syntax SourceInfo)

open Illuminate in
def coeChainDiagram : Diagram SVG :=
  let spacing := 16
  -- Build from inside out: hcat items spanned by each brace, then vsep brace below
  -- Level 1: Coe* with CoeTC brace
  let level1 := Diagram.braceBelow (mono "Coe*") (mono "CoeTC")
  -- Level 2: add CoeOut* on the left, CoeOTC brace below
  let level2 := Diagram.braceBelow
    (Diagram.hsep spacing [mono "CoeOut*", level1] (align := .top))
    (mono "CoeOTC")
  -- Level 3: add CoeHead? on the left, CoeHTC brace below
  let level3 := Diagram.braceBelow
    (Diagram.hsep spacing [mono "CoeHead?", level2] (align := .top))
    (mono "CoeHTC")
  -- Level 4: add CoeTail? on the right, CoeHTCT brace below (named)
  let level4 := Diagram.braceBelow
    (Diagram.hsep spacing [level3, mono "CoeTail?"] (align := .top))
    (mono "CoeHTCT" |>.padBottom 3 |>.namedWithAnchors `CoeHTCT)
  -- CoeDep at same level as CoeHTCT label (bottom-aligned, named)
  let withCoeDep := Diagram.hsep 30
    [level4, mono "CoeDep" |>.padBottom 3 |>.namedWithAnchors `CoeDep] (align := .bottom)
  -- "or" and CoeT below, named for anchor resolution
  let orLabel : Diagram SVG :=
    Diagram.text "or" { fontSize := 10, italic := true } |>.pad 3 |>.namedWithAnchors `or
  let coeTLabel : Diagram SVG := mono "CoeT" (name := `CoeT)
  let lineStroke : Stroke := .ofWidth 1
  Diagram.vsep 12 [withCoeDep, orLabel, coeTLabel]
    |>.connectL `CoeHTCT.south `or.west (stroke := lineStroke)
    |>.connectL `CoeDep.south `or.east (stroke := lineStroke)
    |>.connectL `or.south `CoeT.north (stroke := lineStroke)
where
  mono (s : String) (name : Option Lean.Name := none) : Diagram SVG :=
    .text s { fontSize := 10, fontFamily := "monospace" } (name := name)


#doc (Manual) "强制" =>
%%%
tag := "coercions"
%%%

```lean -show
section
open Lean (TSyntax Name)
variable {c1 c2 : Name} {α : Type u}
```


当 Lean精化器期望一种类型但生成不同类型的术语时，它会尝试自动插入 {deftech}_coercion_，这是从术语类型到预期类型的​​专门指定函数。
通过强制转换，可以在与需要信息量较少的类型的 API 交互时使用特定类型来表示数据。
它们还允许数学发展遵循“双关语”的通常做法，其中相同的符号用于代表代数结构及其载体集，其精确含义由上下文确定。


:::paragraph
Lean 的标准库和元编程 API 定义了许多强制。
一些例子包括：

 * {name}`Nat` 可以用在需要 {name}`Int` 的地方。
 * {name}`Fin` 可以用在需要 {name}`Nat` 的地方。
 * {lean}`α` 可以用在需要 {lean}`Option α` 的地方。强制将值包装在 {name}`some` 中。
 * {lean}`α` 可以用在需要 {lean}`Thunk α` 的地方。强制将项包装在函数中以延迟其求值。
 * 当一个语法类别 {lean}`c1` 嵌入到另一类别 {lean}`c2` 中时，从 {lean}`TSyntax c1` 到 {lean}`TSyntax c2` 的强制转换将执行任何必要的包装以构造有效的语法树。

使用类型类 {tech}[synthesis] 发现强制转换。
可以通过添加适当类型类的更多实例来扩展强制转换集。
:::

```lean -show
end
```

:::example "Coercions"

以下所有示例都依赖于强制：

```lean
example (n : Nat) : Int := n
example (n : Fin k) : Nat := n
example (x : α) : Option α := x

def th (f : Int → String) (x : Nat) : Thunk String := f x

open Lean in
example (n : Ident) : Term := n
```

对于 {name}`th`，使用 {keywordOf Lean.Parser.Command.print}`#print` 表明函数应用程序的评估被延迟，直到请求 thunk 的值：
```lean (name := thunkEval)
#print th
```
```leanOutput thunkEval
def th : (Int → String) → Nat → Thunk String :=
fun f x => { fn := fun x_1 => f ↑x }
```
:::


```lean -show
section
variable {α : Type u}
```

强制转换不用于解析 {tech (key := "generalized field notation")}[通用字段表示法]：仅考虑术语的推断类型。
但是，{tech}[type ascription] 可用于触发对具有所需广义字段的类型的强制。
强制转换也不用于解析 {name}`OfNat` 实例：即使存在 {lean}`OfNat Nat` 的默认实例，从 {lean}`Nat` 到 {lean}`α` 的强制转换也不允许将自然数文字用于 {lean}`α`。

```lean -show
end
```

```lean -show
-- Test comment about field notation
/-- error: Unknown constant `Nat.bdiv` -/
#check_msgs in
#check Nat.bdiv

/-- info: Int.bdiv (x : Int) (m : Nat) : Int -/
#check_msgs in
#check Int.bdiv

/--
error: Invalid field `bdiv`: The environment does not contain `Nat.bdiv`, so it is not possible to project the field `bdiv` from an expression
  n
of type `Nat`
-/
#check_msgs in
example (n : Nat) := n.bdiv 2

#check_msgs in
example (n : Nat) := (n : Int).bdiv 2
```

:::example "Coercions and Generalized Field Notation"

名称 {lean +error}`Nat.bdiv` 未定义，但 {lean}`Int.bdiv` 存在。
查找字段 `bdiv` 时，不考虑从 {lean}`Nat` 到 {lean}`Int` 的强制转换：

```lean +error (name := natBdiv)
example (n : Nat) := n.bdiv 2
```
```leanOutput natBdiv
Invalid field `bdiv`: The environment does not contain `Nat.bdiv`, so it is not possible to project the field `bdiv` from an expression
  n
of type `Nat`
```

这是因为仅当存在与推断类型不同的预期类型时才会插入强制转换，并且根据点之前术语的推断类型来解析广义字段。
可以通过添加类型归属来触发强制转换，这还会导致整个归属项的推断类型为 {lean}`Int`，从而允许找到函数 {name}`Int.bdiv`。
```lean
example (n : Nat) := (n : Int).bdiv 2
```
:::

::::example "Coercions and `OfNat`"
{lean}`Bin` 是表示二进制数的归纳类型。
```lean
inductive Bin where
  | done
  | zero : Bin → Bin
  | one : Bin → Bin

def Bin.toString : Bin → String
  | .done => ""
  | .one b => b.toString ++ "1"
  | .zero b => b.toString ++ "0"

instance : ToString Bin where
  toString
    | .done => "0"
    | b => Bin.toString b
```

通过重复应用 {lean}`Bin.succ` 可以将二进制数转换为自然数：
```lean
def Bin.succ (b : Bin) : Bin :=
  match b with
  | .done => Bin.done.one
  | .zero b => .one b
  | .one b => .zero b.succ

def Bin.ofNat (n : Nat) : Bin :=
  match n with
  | 0 => .done
  | n + 1 => (Bin.ofNat n).succ
```

```lean -show -keep
--- Internal tests
/-- info: [0, 1, 10, 11, 100, 101, 110, 111, 1000] -/
#check_msgs in
#eval [
  Bin.done,
  Bin.done.succ,
  Bin.done.succ.succ,
  Bin.done.succ.succ.succ,
  Bin.done.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ.succ]
```
```lean -show
def Bin.toNat : Bin → Nat
  | .done => 0
  | .zero b => 2 * b.toNat
  | .one b => 2 * b.toNat + 1

def Bin.double : Bin → Bin
  | .done => .done
  | other => .zero other

theorem Bin.toNat_succ_eq_succ {b : Bin} : b.toNat = n → b.succ.toNat = n + 1 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.succ]

theorem Bin.toNat_double_eq_double {b : Bin} : b.toNat = n → b.double.toNat = n * 2 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.double]

theorem Bin.ofNat_toNat_eq {n : Nat} : (Bin.ofNat n).toNat = n := by
  induction n <;> simp_all [Bin.ofNat, Bin.toNat, Bin.toNat_succ_eq_succ]
```


即使 {lean}`Bin.ofNat` 注册为强制转换，自然数文字也不能用于 {lean}`Bin`：
```lean
attribute [coe] Bin.ofNat

instance : Coe Nat Bin where
  coe := Bin.ofNat
```
``` lean (name := nineFail) +error
#eval (9 : Bin)
```
```leanOutput nineFail
failed to synthesize instance of type class
  OfNat Bin 9
numerals are polymorphic in Lean, but the numeral `9` cannot be used in a context where the expected type is
  Bin
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
这是因为插入强制是为了响应不匹配的类型，但合成 {name}`OfNat` 实例失败并不是类型不匹配。


可以在 {lean}`OfNat Bin` 实例的定义中使用强制转换：
```lean (name := ten)
instance : OfNat Bin n where
  ofNat := n

#eval (10 : Bin)
```
```leanOutput ten
1010
```
::::

大多数新的强制转换可以通过声明 {name}`Coe` {tech}[type class] 的实例并将 {attr}`coe` 属性应用于执行强制转换的函数来定义。
为了更好地控制强制或在更多上下文中启用它们，Lean 提供了可以实现的更多类，如本章其余部分所述。

:::example "Defining Coercions: Decimal Numbers"
十进制数可以定义为数字数组。

```lean
structure Decimal where
  digits : Array (Fin 10)
```

添加强制转换允许它们在期望 {lean}`Nat` 的上下文中使用，而且也可以在期望 {lean}`Nat` 可以强制为任何类型的上下文中使用。

```lean
@[coe]
def Decimal.toNat (d : Decimal) : Nat :=
  d.digits.foldl (init := 0) fun n d => n * 10 + d.val

instance : Coe Decimal Nat where
  coe := Decimal.toNat
```

这可以通过将 {lean}`Decimal` 视为 {lean}`Int` 以及 {lean}`Nat` 来证明：
```lean (name := digival)
def twoHundredThirteen : Decimal where
  digits := #[2, 1, 3]

def one : Decimal where
  digits := #[1]

#eval (one : Int) - (twoHundredThirteen : Nat)
```
```leanOutput digival
-212
```

:::

{docstring Coe}



# 强制插入
%%%
tag := "coercion-insertion"
%%%

:::paragraph
搜索从一种类型到另一种类型的强制转换的过程称为 {deftech (key := "coercion insertion")}_coercion insert_。
在以下可能会发生错误的情况下会尝试强制插入：

 * 术语的预期类型与为该术语找到的类型不同。

 * 需要类型或命题，但该术语的类型不是 {tech}[universe]。

 * 术语的应用就像函数一样，但其类型不是函数类型。

当明确请求时，也会插入强制转换。
可以插入强制转换的每种情况都有一个相应的前缀运算符来触发适当的插入。
:::

```lean -show
section
variable {α : Type u} {α' : Type u'} {β : Type u} [Coe α α'] [Coe α' β] (e : α)
```

由于强制转换是自动插入的，因此嵌套的 {tech}[type ascriptions] 提供了一种精确控制强制转换中涉及的类型的方法。
如果 {lean}`α` 和 {lean}`β` 不是同一类型，{lean}`((e : α) : β)` 会将 {lean}`e` 安排为类型 {lean}`α`，然后插入从 {lean}`α` 到 {lean}`β` 的强制转换。

```lean -show
end
```

当发现强制转换时，用于查找它的实例将展开并从结果项中删除。
在可能的情况下，最终术语中不会发生对 {name}`Coe.coe` 和相关函数的调用。
这个展开过程使术语更具可读性。
更重要的是，这意味着强制可以通过将强制项包装在函数中来控制对强制项的求值。

:::example "Controlling Evaluation with Coercions"

结构 {name}`Later` 表示将来可以通过调用所包含的函数来计算的项。

```lean
structure Later (α : Type u) where
  get : Unit → α
```

从任何值到后面的值的强制转换是通过创建一个包装它的函数来执行的。
```lean
instance : CoeTail α (Later α) where
  coe x := { get := fun () => x }
```

但是，如果强制插入导致应用 {name}`CoeTail.coe`，则此强制在运行时不会产生预期效果，因为将评估强制值，然后将其保存在函数的闭包中。
由于强制实现已展开，因此该实例仍然有用。

```lean
def tomorrow : Later String :=
  (Nat.fold 10000
    (init := "")
    (fun _ _ s => s ++ "tomorrow") : String)
```
打印结果定义表明计算是在函数体内进行的：
```lean (name := tomorrow)
#print tomorrow
```
```leanOutput tomorrow
def tomorrow : Later String :=
{ get := fun x => Nat.fold 10000 (fun x x_1 s => s ++ "tomorrow") "" }
```
:::

```lean -show
section
variable {α : Type u}
```
::::example "Duplicate Evaluation in Coercions"
由于 {lean}`Coe` 实例的内容在强制插入期间展开，因此多次使用其参数的强制应小心确保计算仅发生一次。
这可以通过使用不属于实例的辅助函数来完成，或者使用 {keywordOf Lean.Parser.Term.let}`let` 来评估强制项，然后重用其结果值。

结构 {name}`Twice` 要求两个字段具有相同的值：
```lean
structure Twice (α : Type u) where
  first : α
  second : α
  first_eq_second : first = second
```

定义从 {lean}`α` 到 {lean}`Twice α` 的强制转换的一种方法是使用辅助函数 {name}`twice`。
{attr}`coe` 属性将其标记为强制，以便可以在证明目标和错误消息中正确显示。
```lean
@[coe]
def twice (x : α) : Twice α where
  first := x
  second := x
  first_eq_second := rfl

instance : Coe α (Twice α) := ⟨twice⟩
```
当 {name}`Coe` 实例展开时，对 {name}`twice` 的调用仍然存在，这会导致在执行函数体之前计算其参数。
因此，{keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` 仅包含在结果项中一次：
```lean (name := eval1)
#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
这是用来演示效果的：
```leanOutput eval1
hello
```

将帮助程序内联到 {name}`Coe` 实例中会产生与 {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` 重复的术语：
```lean (name := eval2)
instance : Coe α (Twice α) where
  coe x := ⟨x, x, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval2
hello
hello
```

为评估结果引入中间名称可防止 {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` 的重复：
```lean (name := eval3)
instance : Coe α (Twice α) where
  coe x := let y := x; ⟨y, y, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval3
hello
```

::::
```lean -show
end
```


# 类型之间的强制
%%%
tag := "ordinary-coercion"
%%%

:::paragraph
当 Lean精化器在需要某种其他类型的术语的上下文中成功构造术语并推断其类型时，会插入类型之间的强制转换。
在发出错误信号之前，精化器尝试通过合成 {lean}`CoeT` 的实例来插入从推断类型到预期类型的强制转换。
有两种方法可以成功：
 1. 可能存在通过许多中间类型从推断类型到预期类型的强制转换链。
    这些链式强制转换是根据推断类型和预期类型来选择的，而不是根据被强制转换的术语来选择。
 2. 可能存在从推断类型到预期类型的单一依赖强制转换。
    依赖强制转换考虑了被强制的术语以及推断和预期的类型，但它们不能被链接起来。
:::

定义非依赖强制转换的最简单方法是实现 {name}`Coe` 实例，该实例足以合成 {name}`CoeT` 实例。
该实例参与链接，并且可以应用任意次。
表达式的预期类型（而不是推断类型）用于驱动 {name}`Coe` 实例的合成。
对于最多可以使用一次的实例，或者推断类型应该驱动合成的实例，可能需要其他强制类之一。

:::example "Defining Coercions"
类型 {lean}`Even` 代表偶数自然数。

```lean
structure Even where
  number : Nat
  isEven : number % 2 = 0
```

强制允许在需要自然数的地方使用偶数。
{attr}`coe` 属性将投影标记为强制，以便可以相应地在证明状态和错误消息中显示，如 {ref "coercion-impl"}[有关实现强制的部分]中所述。
```lean
attribute [coe] Even.number

instance : Coe Even Nat where
  coe := Even.number
```
通过这种强制转换，可以在需要自然数的地方使用偶数。
```lean (name := four)
def four : Even := ⟨4, by omega⟩

#eval (four : Nat) + 1
```
```leanOutput four
5
```

由于强制链接，还存在从 {name}`Even` 到 {name}`Int` 的强制，通过将 {inst}`Coe Even Nat` 实例与从 {name}`Nat` 到 {name}`Int` 的现有强制链接链接起来形成：
```lean (name := four')
#eval (four : Int) - 5
```
```leanOutput four'
-1
```
:::

当需要被强制的特定术语时，需要 {deftech}[Dependent coercions]，以便确定是否或如何强制该术语：例如，只有可判定命题可以强制为 {name}`Bool`，因此相关命题必须作为实例类型的一部分出现，以便它可以需要 {name}`Decidable` 实例。
只要推断类型的所有值都可以强制转换为目标类型，就会使用非依赖强制转换。

:::example "Defining Dependent Coercions"
可以使用以下实例声明将字符串 {lean}`"four"` 强制转换为自然数{lean  (type := "Nat")}`4`：
```lean (name := fourCoe)
instance : CoeDep String "four" Nat where
  coe := 4

#eval ("four" : Nat)
```
```leanOutput fourCoe
4
```

其他字符串会产生普通类型错误：
```lean +error (name := threeCoe)
#eval ("three" : Nat)
```
```leanOutput threeCoe
Type mismatch
  "three"
has type
  String
but is expected to have type
  Nat
```

:::


```lean -show
section
variable {α α' α'' β β' «…» γ: Sort _}

macro "…":term => Lean.mkIdentFromRef `«…»

variable [CoeHead α α'] [CoeOut α' …] [CoeOut … α''] [Coe α'' …] [Coe … β'] [CoeTail β' γ]


```

:::paragraph
非依赖强制转换可以是链接的：如果存在从 {lean}`α` 到 {lean}`β` 以及从 {lean}`β` 到 {lean}`γ` 的强制转换，则还存在从 {lean}`α` 到 {lean}`γ` 的强制转换。
{index (subterm:="of coercions")}[链条]
该链的格式应为 {name}`CoeHead`$`?`{name}`CoeOut`$`*`{name}`Coe`$`*`{name}`CoeTail`$`?`，也就是说它可能包含以下内容：

 * {inst}`CoeHead α α'` 的可选实例，后跟
 * 零个或多个 {inst}`CoeOut α' …`, …, {inst}`CoeOut … α''` 实例，后跟
 * 零个或多个 {inst}`Coe α'' …`, …, {inst}`Coe … β'` 实例，后跟
 * {inst}`CoeTail β' γ` 的可选实例

大多数强制可以作为 {name}`Coe` 的实例来实现。
在某些特殊情况下需要 {name}`CoeHead`、{name}`CoeOut` 和 {name}`CoeTail`。

:::



{name}`CoeHead` 和 {name}`CoeOut` 实例从推断类型链接到预期类型。
换句话说，为该术语找到的类型中的信息用于解析实例链。
{name}`Coe` 和 {name}`CoeTail` 实例从预期类型链接到推断类型，因此预期类型中的信息用于解析实例链。
如果这些链在中间相遇，则发现了强制。
这反映在它们的类型签名中：{name}`CoeHead` 和 {name}`CoeOut` 使用 {tech (key := "semi-output parameters")}[半输出参数] 作为强制转换的目标，而 {name}`Coe` 和 {name}`CoeTail` 使用 {tech (key := "semi-output parameters")}[半输出参数] 作为强制转换的源。

当实例为 {tech (key := "semi-output parameter")}[半输出参数] 提供值时，该值将在实例综合期间使用。
然而，如果没有提供值，则合成算法可以分配一个值。
因此，在选择实例时，应为每个半输出参数分配一个类型。
这意味着当强制输出中出现的变量是其输入中的变量的子集时，应使用 {name}`CoeOut`；当输入中的变量是输出中的变量的子集时，应使用 {name}`Coe`。

:::example "`CoeOut` vs `Coe` instances"
{name}`Truthy` 值是与是否应将其视为 true 或 false 的指示配对的值。
{name}`Decision` 是 {name Decision.yes}`yes`、{name Decision.no}`no` 或 {name Decision.maybe}`maybe`，后者包含供考虑的更多数据。

```lean
structure Truthy (α : Type) where
  val : α
  isTrue : Bool

inductive Decision (α : Type) where
  | yes
  | maybe (val : α)
  | no
```

通过忘记包含的值，{noVale "Made-up word for example purposes"}[“Truthy”] 值可以转换为 {name}`Bool`。
通过打折 {name Decision.maybe}`maybe` 外壳，{name}`Bool` 可以转换为 {name}`Decision`。
```lean
@[coe]
def Truthy.toBool : Truthy α → Bool :=
  Truthy.isTrue

@[coe]
def Decision.ofBool : Bool → Decision α
  | true => .yes
  | false => .no
```

{name}`Truthy.toBool` 必须是 {name}`CoeOut` 实例，因为强制转换的目标包含的未知类型变量少于源，而 {name}`Decision.ofBool` 必须是 {name}`Coe` 实例，因为强制转换的源包含的变量少于目标：
```lean
instance : CoeOut (Truthy α) Bool := ⟨Truthy.isTrue⟩

instance : Coe Bool (Decision α) := ⟨Decision.ofBool⟩
```

在这些情况下，强制链接起作用：
```lean (name := chainTruthiness)
#eval ({ val := 1, isTrue := true : Truthy Nat } : Decision String)
```
```leanOutput chainTruthiness
Decision.yes
```

尝试使用错误的类会导致错误：
```lean (name := coeOutErr) +error
instance : Coe (Truthy α) Bool := ⟨Truthy.isTrue⟩
```
```leanOutput coeOutErr
instance does not provide concrete values for (semi-)out-params
  Coe (Truthy ?α) Bool
```

:::


```lean -show
end
```

{docstring CoeHead}

{docstring CoeOut}

{docstring CoeTail}

当存在适当的实例链时，或者当存在单个适用的 {name}`CoeDep` 实例时，可以合成 {name}`CoeT` 的实例。{margin}[从 {lean}`Nat` 强制到另一种类型时，{name}`NatCast` 实例也足够了。]
如果两者都存在，则 {name}`CoeDep` 实例优先。

{docstring CoeT}

```lean -show
section
variable {α β : Sort _} {e : α} [CoeDep α e β]
```

依赖强制不能被链接。
作为强制链的替代方案，可以使用 {inst}`CoeDep α e β` 的实例将类型 {lean}`α` 的术语 {lean}`e` 强制为 {lean}`β`。
依赖强制转换在只能强制强制某些值的情况下很有用；该机制用于将可判定命题强制强制为 {lean}`Bool`。
当值本身出现在强制转换的目标类型中时，它们也很有用。

```lean -show
end
```

{docstring CoeDep}

:::example "Dependent Coercion"
```lean -show
universe u
```

非空列表的类型可以定义为一对列表和证明它不为空的证明。
可以通过应用投影将此类型强制为普通列表：

```lean
structure NonEmptyList (α : Type u) : Type u where
  contents : List α
  non_empty : contents ≠ []

instance : Coe (NonEmptyList α) (List α) where
  coe xs := xs.contents
```

强制按预期工作：
```lean
def oneTwoThree : NonEmptyList Nat := ⟨[1, 2, 3], by simp⟩

#eval (oneTwoThree : List Nat) ++ [4]
```

然而，不能将任意列表强制为非空列表，因为某些任意选择的列表可能确实是空的：

```lean +error (name := coeFail) -keep
instance : Coe (List α) (NonEmptyList α) where
  coe xs := ⟨xs, _⟩
```
```leanOutput coeFail
don't know how to synthesize placeholder for argument `non_empty`
context:
α : Type u_1
xs : List α
⊢ xs ≠ []
```

依赖强制转换可以将强制转换的范围限制为仅不为空的列表：
```lean (name := coeOk)
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := ⟨x :: xs, by simp⟩

#eval ([1, 2, 3] : NonEmptyList Nat)
```
```leanOutput coeOk
{ contents := [1, 2, 3], non_empty := _ }
```


依赖强制插入要求要强制的术语在语法上与实例标头中的术语匹配。
已知非空列表，但在语法上不是 {lean (type := "{α : Type u} → α → List α → List α")}`(· :: ·)` 的语法实例，无法使用此实例进行强制。
```lean +error (name := coeFailDep)
#check
  fun (xs : List Nat) =>
    let ys : List Nat := xs ++ [4]
    (ys : NonEmptyList Nat)
```
强制插入失败时，报原始类型错误：
```leanOutput coeFailDep
Type mismatch
  ys
has type
  List Nat
but is expected to have type
  NonEmptyList Nat
```

:::

:::syntax term (title := "Coercions")
```grammar
↑$_:term
```

可以使用前缀运算符 {keywordOf coeNotation}`↑` 显式放置强制转换。
:::

与使用嵌套 {tech (key := "type ascriptions")}[类型归属] 不同，用于放置强制转换的 {keywordOf coeNotation}`↑` 语法不需要显式编写所涉及的类型。

:::example "Controlling Coercion Insertion"

实例合成和强制插入是相互作用的。
合成实例可以使类型信息已知，随后触发强制插入。
强制的具体位置可能很重要。

在 {lean}`sub` 的定义中，{inst}`Sub Int` 实例是根据函数的返回类型综合的。
该实例要求这两个参数也为{lean}`Int`，但它们是{lean}`Nat`。
强制转换插入到减法运算符的每个参数周围。
这可以在 {keywordOf Lean.Parser.Command.print}`#print` 的输出中看到。

```lean (name := subThenCoe)
def sub (n k : Nat) : Int := n - k

#print sub
```
```leanOutput subThenCoe
def sub : Nat → Nat → Int :=
fun n k => ↑n - ↑k
```

将强制转换运算符放在减法之外会导致精化器尝试推断减法的类型，然后插入强制转换。
由于参数都是 {lean}`Nat`，因此选择 {inst}`Sub Nat` 实例，导致差异为 {lean}`Nat`。
然后将差异强制转换为 {lean}`Int`。
```lean (name:=coeThenSub)
def sub' (n k : Nat) : Int := ↑ (n - k)

#print sub'
```

这两个函数并不等价，因为自然数的减法会截断为零：
```lean (name := subRes)
#eval sub 4 8
```
```leanOutput subRes
-4
```
```lean (name := subMark)
#eval sub' 4 8
```
```leanOutput subMark
0
```

:::


## 实施强制
%%%
tag := "coercion-impl"
%%%

适当的 {name}`CoeHead`、{name}`CoeOut`、{name}`Coe` 或 {name}`CoeTail` 实例足以导致插入所需的强制。
但是，强制的实现应使用 {attr}`coe` 属性注册为强制。
这会导致 Lean 显示 {keywordOf coeNotation}`↑` 运算符的强制转换的使用情况。
它还导致 {tactic}`norm_cast`策略将强制转换视为强制转换，而不是普通函数。

:::syntax attr (title := "Coercion Declarations")
```grammar
coe
```

{includeDocstring Lean.Attr.coe}

:::

:::example "Implementing Coercions"
{tech (key := "enum inductive")}[enum inducing] 类型 {lean}`Weekday` 代表一周中的几天：
```lean
inductive Weekday where
  | mo | tu | we | th | fr | sa | su
```

作为七元素类型，它包含与 {lean}`Fin 7` 相同的信息。
存在双射：
```lean
def Weekday.toFin : Weekday → Fin 7
  | mo => 0
  | tu => 1
  | we => 2
  | th => 3
  | fr => 4
  | sa => 5
  | su => 6

def Weekday.fromFin : Fin 7 → Weekday
  | 0 => mo
  | 1 => tu
  | 2 => we
  | 3 => th
  | 4 => fr
  | 5 => sa
  | 6 => su
```

```lean -show
theorem Weekday.toFin_fromFin_id : Weekday.toFin (Weekday.fromFin n) = n := by
  repeat (cases ‹Fin (_ + 1)› using Fin.cases; case zero => rfl)
  apply Fin.elim0; assumption

theorem Weekday.fromFin_toFin_id : Weekday.fromFin (Weekday.toFin w) = w := by
  cases w <;> rfl
```

每种类型都可以强制转换为另一种：
```lean
instance : Coe Weekday (Fin 7) where
  coe := Weekday.toFin

instance : Coe (Fin 7) Weekday where
  coe := Weekday.fromFin
```

虽然此方法有效，但 Lean 输出中发生的强制实例不会使用强制运算符呈现，而这正是 Lean 用户所期望的。
相反，显式使用名称 {lean}`Weekday.fromFin`：
```lean (name := wednesday)
def wednesday : Weekday := (2 : Fin 7)

#print wednesday
```
```leanOutput wednesday
def wednesday : Weekday :=
Weekday.fromFin 2
```


将 {attr}`coe` 属性添加到强制转换的定义中会导致使用强制转换运算符显示它：
```lean (name := friday)
attribute [coe] Weekday.fromFin
attribute [coe] Weekday.toFin

def friday : Weekday := (5 : Fin 7)

#print friday
```
```leanOutput friday
def friday : Weekday :=
↑5
```

:::

## 来自自然数和整数的强制转换
%%%
tag := "nat-api-cast"
%%%

类型类 {name}`NatCast` 和 {name}`IntCast` 是 {name}`Coe` 的特殊情况，用于定义从 {lean}`Nat` 或 {lean}`Int` 到某种某种意义上规范的其他类型的强制。
它们的存在是为了更好地与大型数学库集成，例如 [Mathlib](https://github.com/leanprover-community/mathlib4)，这些数学库大量使用强制从自然数或整数映射到其他结构（通常是环）。
理想情况下，将自然数或整数强制转换为这些结构是 {tech (key := "simp normal form")}[simp 范式]，因为这是表示它们的便捷方法。

当强制转换应用程序预计为类型的 {tech (key := "simp normal form")}[simp 范式] 时，重要的是在实践中所有此类强制转换都是 {tech (key := "definitional equality")}[定义等价]。
否则，{tech (key := "simp normal form")}[simp范式]将需要选择单个链式强制转换路径，但引理可能会意外地使用不同的路径来陈述。
由于 {tactic}`simp` 的内部索引基于术语的底层结构，而不是其在表面语法中的表示形式，因此这些差异将导致引理无法应用到预期的位置。
另一方面，{lean}`NatCast` 和 {lean}`IntCast` 实例应定义为始终 {tech (key := "definitional equality")}[定义等价]，从而避免出现该问题。
Lean 标准库的实例经过排列，使得在强制插入期间优先选择 {name}`NatCast` 或 {name}`IntCast` 实例而不是强制实例链。
它们还可以用作 {name}`CoeOut` 实例，允许在需要时优雅地回退到强制链接。

{docstring NatCast}

{docstring Nat.cast}

{docstring IntCast}

{docstring Int.cast}


# 强制排序
%%%
tag := "sort-coercion"
%%%

Lean精化器期望类型位于某些位置，但不一定能够提前确定类型的 {tech}[universe]。
例如，定义标题中冒号后面的术语可能是命题或类型。
普通强制转换机制不适用，因为它需要特定的预期类型，并且无法表示预期类型可以是 {name}`Coe` 类中的 _any_ Universe。

当在预期命题或类型的位置详细精化术语，但所精化术语的推断类型不是命题或类型时，Lean 尝试通过合成 {name}`CoeSort` 的实例来从错误中恢复。
如果找到实例，并且结果类型本身就是一种类型，则插入并展开强制转换。

并非精化器需要 Universe 的所有情况都需要 {name}`CoeSort`。
在某些情况下，特定的 Universe 可用作预期类型。
在这些情况下，使用使用 {name}`CoeT` 的普通强制插入。
{lean}`CoeSort` 的实例可用于合成 {lean}`CoeOut` 的实例，因此不需要单独的实例来支持此用例。
一般来说，类型强制应实现为 {name}`CoeSort`。

{docstring CoeSort}


:::syntax term (title := "Explicit Coercion to Sorts")
```grammar
↥ $_:term
```

可以使用 {keyword}`↥` 前缀运算符显式触发排序强制。
:::

::: example "Sort Coercions"

幺半群是一种配备有关联二元运算和单位元素的类型。
虽然幺半群结构可以定义为类型类，但它也可以定义为将结构与类型“捆绑”的结构：
```lean
structure Monoid where
  Carrier : Type u
  op : Carrier → Carrier → Carrier
  id : Carrier
  op_assoc :
    ∀ (x y z : Carrier), op x (op y z) = op (op x y) z
  id_op_identity : ∀ (x : Carrier), op id x = x
  op_id_identity : ∀ (x : Carrier), op x id = x
```

类型 {lean  (type := "Type 1")}`Monoid` 不指示运营商：
```lean
def StringMonoid : Monoid where
  Carrier := String
  op := (· ++ ·)
  id := ""
  op_assoc := by intros; simp [String.append_assoc]
  id_op_identity := by intros; simp
  op_id_identity := by intros; simp
```

但是，当在 Lean 需要类型的位置使用幺半群时，可以实现应用 {name}`Monoid.Carrier` 投影的 {name}`CoeSort` 实例：
```lean
instance : CoeSort Monoid (Type u) where
  coe m := m.Carrier

example : StringMonoid := "hello"
```
:::

:::example "Sort Coercions as Ordinary Coercions"
{tech (key := "inductive type")}[归纳类型] {name}`NatOrBool` 代表类型 {name}`Nat` 和 {name}`Bool`。
它们可以强制转换为实际类型 {name}`Nat` 和 {name}`Bool`：
```lean
inductive NatOrBool where
  | nat | bool

@[coe]
abbrev NatOrBool.asType : NatOrBool → Type
  | .nat => Nat
  | .bool => Bool

instance : CoeSort NatOrBool Type where
  coe := NatOrBool.asType

open NatOrBool
```

当 {lean}`nat` 出现在冒号右侧时，使用 {name}`CoeSort` 实例：
```lean
def x : nat := 5
```

当预期类型可用时，将使用普通的强制插入。
在本例中，{name}`CoeSort` 实例用于合成 {lean}`CoeOut NatOrBool Type` 实例，该实例与 {inst}`Coe Type (Option Type)` 实例链接以从类型错误中恢复。
```lean
def y : Option Type := bool
```
:::

# 强制转换为函数类型
%%%
tag := "fun-coercion"
%%%

预期类型通常不可用的另一种情况是函数应用术语中的函数位置。
依赖函数类型很常见；它们与 {tech (key := "implicit")}[隐式] 参数一起，导致信息从一个参数的精化流向其他参数的精化。
尝试从整个应用程序术语的预期类型和单独推断的参数类型来推断函数所需的类型通常会失败。
在这些情况下，Lean 使用 {name}`CoeFun` 类型类将应用程序位置中的非函数强制为函数。
与 {name}`CoeSort` 一样，{name}`CoeFun` 实例在插入函数强制转换时不会与其他强制转换链接，但它们可以在普通强制插入期间用作 {name}`CoeOut` 实例。

{name}`CoeFun` 的第二个参数是输出参数，用于确定结果函数类型。
此输出参数是根据被强制转换的项计算函数类型的函数，而不是函数类型本身。
与 {name}`CoeDep` 不同，在实例合成期间不考虑该术语本身；但是，它可以用于创建依值类型的强制转换，其中函数类型由术语确定。


{docstring CoeFun}

:::syntax term (title := "Explicit Coercion to Functions")
```grammar
⇑ $_:term
```
:::

```lean -show
section
variable {α : Type u} {β : Type v}
```
:::example "Coercing Decorated Functions to Function Types"
结构 {lean}`NamedFun α β` 将 {lean}`α` 到 {lean}`β` 的函数与名称配对。

```lean
structure NamedFun (α : Type u) (β : Type v) where
  function : α → β
  name : String
```

现有函数可以命名为：
```lean
def succ : NamedFun Nat Nat where
  function n := n + 1
  name := "succ"

def asString [ToString α] : NamedFun α String where
  function := ToString.toString
  name := "asString"

def append : NamedFun (List α) (List α → List α) where
  function := (· ++ ·)
  name := "append"
```

命名函数也可以组成：
```lean
def NamedFun.comp
    (f : NamedFun β γ)
    (g : NamedFun α β) :
    NamedFun α γ where
  function := f.function ∘ g.function
  name := f.name ++ " ∘ " ++ g.name
```


与普通函数不同，命名函数具有合理的字符串表示形式：
```lean
instance : ToString (NamedFun α α'') where
  toString f := s!"#<{f.name}>"
```
```lean (name := compDemo)
#eval asString.comp succ
```
```leanOutput compDemo
#<asString ∘ succ>
```

{name}`CoeFun` 实例允许它们像普通函数一样应用：
```lean
instance : CoeFun (NamedFun α α'') (fun _ => α → α'') where
  coe | ⟨f, _⟩ => f
```
```lean (name := appendDemo)
#eval append [1, 2, 3] [4, 5, 6]
```
```leanOutput appendDemo
[1, 2, 3, 4, 5, 6]
```
:::
```lean -show
end
```

:::example "Dependent Coercion to Functions"
有时，结果函数的类型取决于被强制转换的特定值。
{lean}`Writer` 表示将某个值的表示附加到字符串的方法：
```lean
structure Writer where
  Writes : Type u
  write : Writes → String → String

def natWriter : Writer where
  Writes := Nat
  write n out := out ++ toString n

def stringWriter : Writer where
  Writes := String
  write s out := out ++ s
```

由于内部函数期望的参数类型取决于 {lean}`Writer.Writes` 字段，因此 {name}`CoeFun` 实例提取该字段：
```lean
instance :
    CoeFun Writer (·.Writes → String → String) where
  coe w := w.write
```

在这个实例中，具体的 {name}`Writer` 可以用作函数：
```lean (name := writeTwice)
#eval "" |> natWriter (5 : Nat) |> stringWriter " hello"
```
```leanOutput writeTwice
"5 hello"
```
:::

:::example "Coercing to Function Types"

类型良好的解释器是一种编程语言的解释器，它使用索引族来排除运行时类型错误。
用解释语言编写的函数可以解释为 Lean 函数，但也可以检查其底层源代码。

类型良好的解释器的第一步是选择可以使用的 Lean 类型的子集。
这些类型由代码 {name}`Ty` 的 {tech (key := "inductive type")}[归纳类型] 以及将这些代码映射到实际类型的函数表示。
```lean
inductive Ty where
  | nat
  | arr (dom cod : Ty)

abbrev Ty.interp : Ty → Type
  | .nat => Nat
  | .arr t t' => t.interp → t'.interp
```

语言本身由变量上下文和结果类型上的 {tech (key := "indexed family")}[索引族] 表示。
变量由 [de Bruijn 指数](https://en.wikipedia.org/wiki/De_Bruijn_index) 表示。
```lean
inductive Tm : List Ty → Ty → Type where
  | zero : Tm Γ .nat
  | succ (n : Tm Γ .nat) : Tm Γ .nat
  | rep (n : Tm Γ .nat)
    (start : Tm Γ t)
    (f : Tm Γ (.arr .nat (.arr t t))) :
    Tm Γ t
  | lam (body : Tm (t :: Γ) t') : Tm Γ (.arr t t')
  | app (f : Tm Γ (.arr t t')) (arg : Tm Γ t) : Tm Γ t'
  | var (i : Fin Γ.length) : Tm Γ Γ[i]
deriving Repr
```


由于 {name}`Fin` 的 {name}`OfNat` 实例要求上限非零，因此 {name}`Tm.var` 与数字文字一起使用可能不方便。
在这些情况下，可以使用帮助器 {name}`Tm.v` 来避免类型注释的需要。
```lean
def Tm.v
    (i : Fin (Γ.length + 1)) :
    Tm (t :: Γ) (t :: Γ)[i] :=
  .var (Γ := t :: Γ) i
```

添加两个自然数的函数使用 {name Tm.rep}`rep` 操作来重复应用后继 {name}`Tm.succ`。
```lean
def plus : Tm [] (.arr .nat (.arr .nat .nat)) :=
  .lam <| .lam <| .rep (.v 1) (.v 0) (.lam (.lam (.succ (.v 0))))
```


每个类型上下文都可以解释为一种运行时环境，为上下文中的每个变量提供一个值：
```lean
def Env : List Ty → Type
  | [] => Unit
  | t :: Γ => t.interp × Env Γ

def Env.empty : Env [] := ()

def Env.extend (ρ : Env Γ) (v : t.interp) : Env (t :: Γ) :=
  (v, ρ)

def Env.get (i : Fin Γ.length) (ρ : Env Γ) : Γ[i].interp :=
  match Γ, ρ, i with
  | _::_, (v, _), ⟨0, _⟩ => v
  | _::_, (_, ρ'), ⟨i+1, _⟩ => ρ'.get ⟨i, by simp_all⟩
```

最后，解释器是该术语的递归函数：
```lean
def Tm.interp (ρ : Env α'') : Tm α'' t → t.interp
  | .zero => 0
  | .succ n => n.interp ρ + 1
  | .rep n start f =>
    let f' := f.interp ρ
    (n.interp ρ).fold (fun n _ x => f' n x) (start.interp ρ)
  | .lam body => fun x => body.interp (ρ.extend x)
  | .app f arg => f.interp ρ (arg.interp ρ)
  | .var i => ρ.get i
```

将 {name}`Tm` 强制为函数包括调用解释器。

```lean
instance : CoeFun (Tm [] α'') (fun _ => α''.interp) where
  coe f := f.interp .empty
```

由于函数由一阶归纳类型表示，因此可以检查它们的代码：
```lean (name := evalPlus)
#eval plus
```
```leanOutput evalPlus
Tm.lam (Tm.lam (Tm.rep (Tm.var 1) (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0))))))
```

同时，由于强制，它们可以像本机 Lean 函数一样应用：
```lean (name := eight)
#eval plus 3 5
```
```leanOutput eight
8
```

:::



# 实施细节
%%%
tag := "coercion-impl-details"
%%%


只有普通的强制插入才使用链接。
将强制转换插入 {ref "sort-coercion"}[sort] 或 {ref "fun-coercion"}[function] 使用普通实例合成。
同样，{tech (key := "dependent coercions")}[依赖强制转换]也不是链接的。

## 展开强制
%%%
tag := "coercion-unfold-impl"
%%%

强制插入机制展开了强制的应用，这使得它们能够控制结果项的特定形状。
这对于确保可读的证明目标和控制编译代码中强制术语的评估都很重要。
展开强制转换由 {attr}`coe_decl` 属性控制，该属性应用于每种强制转换方法（例如 {name}`Coe.coe`）。
该属性应被视为强制机制内部的一部分，而不是公共强制 API 的一部分。


## 强制链接
%%%
tag := "coercion-chain-impl"
%%%

:::paragraph

强制链接是通过辅助类型类的集合来实现的。
用户不应直接编写这些类的实例，但在诊断未按预期插入强制转换的原因时，了解其结构可能很有用。
管理链中实例排序的特定规则（即，它应该匹配 {name}`CoeHead`﻿`?`{name}`CoeOut`﻿`*`{name}`Coe`﻿`*`{name}`CoeTail`﻿`?`）由以下类型类：

 * {name}`CoeTC` 是 {name}`Coe` 实例的传递闭包。

 * {name}`CoeOTC` 是链的中间，由 {name}`CoeOut` 实例的传递闭包和后跟的 {name}`CoeTC` 组成。

 * {name}`CoeHTC` 是链的起点，最多由一个 {name}`CoeHead` 实例组成，后跟 {name}`CoeOTC`。

 * {name}`CoeHTCT` 是整个链，由 `CoeHTC` 和最多一个 {name}`CoeTail` 实例组成。或者，它可能是 {name}`NatCast` 实例。

 * {name}`CoeT` 代表整个链：它可以是 {name}`CoeHTCT` 链，也可以是单个 {name}`CoeDep` 实例。

:::

:::figure "Auxiliary Classes for Coercions" (tag := "coe-aux-classes")
```diagram
coeChainDiagram
```
:::

{docstring CoeHTCT}

{docstring CoeHTC}

{docstring CoeOTC}

{docstring CoeTC}
