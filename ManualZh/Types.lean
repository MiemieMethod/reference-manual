/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.Language.Functions
import ManualZh.Language.InductiveTypes
import ManualZh.Quotients

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option maxRecDepth 800

#doc (Manual) "Type 系统" =>
%%%
tag := "type-system"
shortContextTitle := "Type System"
%%%

{deftech}_Terms_，也称为 {deftech}_expressions_，是 Lean 核心语言中意义的基本单位。
它们是由 {tech (key := "Lean elaborator")}[精化器] 根据用户编写的语法生成的。
Lean 的类型系统将术语与其_类型_相关联，这些_类型_本身也是术语。
类型可以被认为表示集合，而术语表示这些集合的各个元素。
如果项具有符合 Lean 的 类型论 规则的类型，则该项是 {deftech}_well-typed_。
只有类型正确的术语才有意义。

术语是依值类型的 λ 演算：它们包括函数抽象、应用程序、变量和 `let` 绑定。
除了绑定变量之外，术语语言中的变量还可以指 {tech}[构造函数]、{tech}[类型构造函数]、{tech}[递归函数]、{deftech}[定义的常量] 或不透明常量。
构造函数、类型构造函数、递归器和不透明常量不能进行替换，而定义的常量可以用它们的定义替换。

{deftech}_derivation_ 通过明确指示所使用的精确推理规则来演示术语的类型正确性。
隐含地，类型良好的术语可以代替证明其类型良好的推导。
Lean 的 类型论 足够明确，可以从类型良好的术语重建推导，这大大减少了存储完整推导所产生的开销，同时仍然具有足够的表现力来表示现代研究数学。
这意味着证明项是定理真实性的充分证据，并且可以进行独立验证。

除了具有类型之外，术语还通过 {deftech}_定义等价_相关。
这是一种可机械检查的关系，在语法上将术语对其计算行为取模。
定义等价 包括 {deftech}[reduction] 的以下形式：

 : {deftech}[β]（测试版）

    通过替换绑定变量将函数抽象应用于参数

 : {deftech}[δ]（增量）

    将出现的 {tech}[已定义常量] 替换为定义的值

 : {deftech}[ι] (iota)

    减少目标是构造函数的递归器（原始递归）

 : {deftech}[z] (zeta)

     用其定义值替换 let 绑定变量

 : 商数减少

   {ref "quotient-model"}[商类型函数提升运算符的归约]应用于商的元素时

已进行所有可能减少的项采用 {deftech}_正常形式_。

::::keepEnv
```lean -show
axiom α : Type
axiom β : Type
axiom f : α → β

structure S where
  f1 : α
  f2 : β

axiom x : S

-- test claims in next para

example : (fun x => f x) = f := by rfl
example : S.mk x.f1 x.f2 = x := by rfl

export S (f1 f2)
```
定义等价 包括函数 {deftech}[η-等价] 和单构造函数归纳类型。
也就是说，如果 {lean}`S` 是具有字段 {lean}`f1` 和 {lean}`f2` 的结构，则 {lean}`fun x => f x` 定义上等于 {lean}`f`，{lean}`S.mk x.f1 x.f2` 定义上等于 {lean}`x`。
它还具有 {deftech}_证明无关性_：同一命题的任何两个证明在定义上都是相等的。
它是自反且对称的，但不具有传递性。
::::

定义等价 通过转换使用：如果两个术语在定义上相等，并且给定术语将其中之一作为其类型，则它也将另一个作为其类型。
由于 定义等价 包含约简，因此类型可以通过数据计算得出。

::::keepEnv
:::Manual.example "Computing types"

当传递自然数时，函数 {lean}`LengthList` 计算一个与列表相对应的类型，其中包含恰好那么多的条目：

```lean
def LengthList (α : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => α × LengthList α n
```

由于 Lean 的元组嵌套在右侧，因此不需要多个嵌套括号：
```lean
example : LengthList Int 0 := ()

example : LengthList String 2 :=
  ("Hello", "there", ())
```

如果长度与条目数不匹配，则计算类型将与该术语不匹配：
```lean +error (name := wrongNum)
example : LengthList String 5 :=
  ("Wrong", "number", ())
```
```leanOutput wrongNum
Application type mismatch: The argument
  ()
has type
  Unit
but is expected to have type
  LengthList String 3
in the application
  ("number", ())
```
:::
::::

Lean 中的基本类型为 {tech}[universes]、{tech}[function] 类型、{name}`Quot` 的商、{tech}[归纳类型] 的 {tech}[类型构造函数]。
{tech}[定义的常量]、{tech}[递归器]的应用、函数应用、{tech}[公理]或 {tech}[不透明常量] 还可以给出类型，就像它们可以产生任何其他类型的项一样。


{include ManualZh.Language.Functions}

# 提案
%%%
tag := "propositions"
%%%

{deftech}[命题] 是接受证据的有意义的陈述。 {index}[提议]
无意义的陈述不是命题，但错误的陈述才是。
所有命题均按 {lean}`Prop` 分类。

命题具有以下属性：

: 定义证明无关性

  同一命题的任何两个证明都是完全可以互换的。

: 运行时无关性

  命题将从编译的代码中删除。

: 必然性

  命题可以量化任何宇宙中的类型。

: 限制性淘汰

  除了 {tech}[subsingletons] 之外，命题不能被消元为非命题类型。

: {deftech (key := "propositional extensionality")}[外延性] {index (subterm := "of propositions")}[外延性]

  任何两个逻辑上等价的命题都可以用 {lean}`propext` 公理证明相等。

{docstring propext}

# 宇宙
%%%
tag := "zh-types-h002"
%%%

类型按 {deftech}_universes_ 进行分类。 {index}[宇宙]{margin}[宇宙也称为 {deftech}_sorts_。]
每个宇宙都有一个 {deftech (key:="universe level")}_level_，{index (subterm := "of universe")}[level] 是自然数。
{lean}`Sort` 运算符从给定级别构造一个 Universe。 {index}[`Sort`]
如果一个宇宙的层次小于另一个宇宙的层次，则称宇宙本身较小。
除了命题（本章稍后描述）之外，给定宇宙中的类型只能对较小宇宙中的类型进行量化。
{lean}`Sort 0` 是命题的类型，而每个 `Sort (u + 1)` 是描述数据的类型。

每个宇宙都是下一个更大宇宙的元素，因此 {lean}`Sort 5` 包括 {lean}`Sort 4`。
这意味着以下示例被接受：
```lean
example : Sort 5 := Sort 4
example : Sort 2 := Sort 1
```

另一方面，{lean}`Sort 3` 不是 {lean}`Sort 5` 的元素：
```lean +error (name := sort3)
example : Sort 5 := Sort 3
```

```leanOutput sort3
Type mismatch
  Type 2
has type
  Type 3
of sort `Type 4` but is expected to have type
  Type 4
of sort `Type 5`
```

同样，由于 {lean}`Unit` 在 {lean}`Sort 1` 中，因此它不在 {lean}`Sort 2` 中：
```lean
example : Sort 1 := Unit
```
```lean +error (name := unit1)
example : Sort 2 := Unit
```

```leanOutput unit1
Type mismatch
  Unit
has type
  Type
of sort `Type 1` but is expected to have type
  Type 1
of sort `Type 2`
```

由于命题和数据的用途不同，受不同的规则管辖，为了方便区分，提供缩写{lean}`Type`和{lean}`Prop`。  {index}[`Type`] {index}[`Prop`]
`Type u` 是 `Sort (u + 1)` 的缩写，因此 {lean}`Type 0` 为 {lean}`Sort 1`，{lean}`Type 3` 为 {lean}`Sort 4`。
{lean}`Type 0` 也可以缩写为 {lean}`Type`，即 `Unit : Type` 和 `Type : Type 1`。
{lean}`Prop` 是 {lean}`Sort 0` 的缩写。

## 预测性
%%%
tag := "zh-types-h003"
%%%

每个宇宙都包含依赖函数类型，这些函数类型还代表全称量化和含义。
函数类型的范围由其参数和返回类型的范围决定。
具体规则取决于函数的返回类型是否是命题。

谓词是返回命题的函数（即，函数的结果是 `Prop` 中的某种类型）可以在任何宇宙中具有参数类型，但函数类型本身仍保留在 `Prop` 中。
换句话说，命题具有 {deftech}[_impredicative_] {index}[impredicative]{index (subterm := "impredicative")}[quantification] 量化的特征，因为命题本身可以是关于所有命题（以及所有其他类型）的陈述。

:::Manual.example "Impredicativity"
证明无关性可以写成一个对所有命题进行量化的命题：
```lean
example : Prop := ∀ (P : Prop) (p1 p2 : P), p1 = p2
```

命题还可以在任何给定级别量化所有类型：
```lean
example : Prop := ∀ (α : Type), ∀ (x : α), x = x
example : Prop := ∀ (α : Type 5), ∀ (x : α), x = x
```
:::

对于 {tech (key := "universe level")}[级别] `1` 及更高级别（即 `Type u` 层次结构）的 Universe，量化为 {deftech}[_predicative_]。 {index}[谓语]{index (subterm := "predicative")}[量化]
对于这些全域，函数类型的全域是参数和返回类型的全域的最小上限。

:::Manual.example "Universe levels of function types"
这两种类型都在 {lean}`Type 2` 中：
```lean
example (α : Type 1) (β : Type 2) : Type 2 := α → β
example (α : Type 2) (β : Type 1) : Type 2 := α → β
```
:::

:::Manual.example "Predicativity of {lean}`Type`"
该示例不被接受，因为 `α` 的级别大于 `1`。换句话说，带注释的 Universe 小于函数类型的 Universe：
```lean +error (name := toosmall)
example (α : Type 2) (β : Type 1) : Type 1 := α → β
```
```leanOutput toosmall
Type mismatch
  α → β
has type
  Type 2
of sort `Type 3` but is expected to have type
  Type 1
of sort `Type 2`
```
:::

Lean 的 Universe 不是 {deftech}[累积]；{index}[累积性] `Type u` 中的类型不会自动出现在 `Type (u + 1)` 中。
每种类型都恰好栖息在同一个宇宙中。

:::Manual.example "No cumulativity"
此示例不被接受，因为带注释的 Universe 大于函数类型的 Universe：
```lean +error (name := toobig)
example (α : Type 2) (β : Type 1) : Type 3 := α → β
```
```leanOutput toobig
Type mismatch
  α → β
has type
  Type 2
of sort `Type 3` but is expected to have type
  Type 3
of sort `Type 4`
```
:::

## 多态性
%%%
tag := "zh-types-h004"
%%%

Lean 支持 {deftech}_universe 多态性_、{index (subterm := "universe")}[多态性] {index}[universe 多态性]，这意味着 Lean 环境中定义的常量可以采用 {deftech}[universe 参数]。
当使用常量时，可以使用 宇宙层级 实例化这些参数。
Universe 参数写在花括号中，常量名称后面紧跟一个点。

:::Manual.example "Universe-polymorphic identity function"
当完全显式时，恒等函数采用全域参数 `u`。它的签名是：
```signature
id.{u} {α : Sort u} (x : α) : α
```
:::

Universe 变量还可能出现在 {ref "level-expressions"}[宇宙层级 表达式] 中，其在定义中提供特定的 宇宙层级。
当用具体级别实例化多态定义时，这些 宇宙层级 表达式也会被评估以产生具体级别。

::::keepEnv
:::Manual.example "Universe level expressions"

在此示例中，{lean}`Codec` 所在的 Universe 比它包含的类型的 Universe 大 1：
```lean
structure Codec.{u} : Type (u + 1) where
  type : Type u
  encode : Array UInt32 → type → Array UInt32
  decode : Array UInt32 → Nat → Option (type × Nat)
```

Lean 自动推断大多数电平参数。
在以下示例中，无需将类型注释为 {lean}`Codec.{0}`，因为 {lean}`Char` 的类型为 {lean}`Type 0`，因此 `u` 必须为 `0`：
```lean
def Codec.char : Codec where
  type := Char
  encode buf ch := buf.push ch.val
  decode buf i := do
    let v ← buf[i]?
    if h : v.isValidChar then
      let ch : Char := ⟨v, h⟩
      return (ch, i + 1)
    else
      failure
```
:::
::::

宇宙多态定义实际上创建了一个可以在各种级别实例化的_示意性定义_，并且宇宙的不同实例化创建了不兼容的值。

::::keepEnv
:::Manual.example "Universe polymorphism and definitional equality"

这可以在以下示例中看到，其中 {lean}`T` 是一个无偿宇宙多态函数，它始终返回 {lean}`true`。
由于它被标记为 {keywordOf Lean.Parser.Command.declaration}`opaque`，因此 Lean 无法通过展开定义来检查相等性。
{lean}`T` 的两个实例都具有相同的参数和类型，但它们不同的 Universe 实例使它们不兼容。
```lean +error (name := uniIncomp)
opaque T.{u} (_ : Nat) : Bool :=
  (fun (α : Sort u) => true) PUnit.{u}

set_option pp.universes true

def test.{u, v} : T.{u} 0 = T.{v} 0 := rfl
```
```leanOutput uniIncomp
Type mismatch
  rfl.{?u.46}
has type
  Eq.{?u.46} ?m.48 ?m.48
but is expected to have type
  Eq.{1} (T.{u} 0) (T.{v} 0)
```
:::
::::

自动绑定的隐式参数尽可能具有全域多态性。
定义恒等函数如下：
```lean
def id' (x : α) := x
```
签名结果：
```signature
id'.{u} {α : Sort u} (x : α) : α
```

:::Manual.example "Universe monomorphism in auto-bound implicit parameters"
另一方面，由于 {name}`Nat` 在全域 {lean}`Type 0` 中，因此该函数自动以 `α` 的具体 宇宙层级 结束，因为 `m` 应用于 {name}`Nat` 和 `α`，因此两者必须具有相同的类型，因此处于相同的类型宇宙：
```lean
partial def count [Monad m] (p : α → Bool) (act : m α) : m Nat := do
  if p (← act) then
    return 1 + (← count p act)
  else
    return 0
```

```lean -show -keep
/-- info: Nat : Type -/
#check_msgs in
#check Nat

/--
info: count.{u_1} {m : Type → Type u_1} {α : Type} [Monad m] (p : α → Bool) (act : m α) : m Nat
-/
#check_msgs in
#check count
```
:::

### 级别表达式
%%%
tag := "level-expressions"
%%%

定义中出现的级别不仅限于变量和常量的添加。
可以使用级别表达式来定义宇宙之间更复杂的关系。

```
Level ::= 0 | 1 | 2 | ...  -- Concrete levels
        | u, v             -- Variables
        | Level + n        -- Addition of constants
        | max Level Level  -- Least upper bound
        | imax Level Level -- Impredicative LUB
```

给定级别变量分配给具体数字，评估这些表达式遵循通常​​的算术规则。
`imax` 操作定义如下：

$$`\mathtt{imax}\ u\ v = \begin{cases}0 & \mathrm{when\ }v = 0\\\mathtt{max}\ u\ v&\mathrm{otherwise}\end{cases}`

`imax` 用于实现 {lean}`Prop` 的 {tech}[指示] 量化。
特别是，如果 `A : Sort u` 和 `B : Sort v`，则 `(x : A) → B : Sort (imax u v)`。
如果是 `B : Prop`，则函数类型本身就是 {lean}`Prop`；否则，功能类型的级别为`u` 和`v` 中的最大值。

### Universe 变量绑定
%%%
tag := "zh-types-h006"
%%%

宇宙多态定义绑定宇宙变量。
这些绑定可以是显式的，也可以是隐式的。
显式 Universe 变量绑定和实例化作为定义名称的后缀出现。
Universe 参数是通过在常量名称后加上句点 (`.`) 后跟大括号之间以逗号分隔的 Universe 变量序列来定义或提供的。

::::keepEnv
:::Manual.example "Universe-polymorphic `map`"
以下 {lean}`map` 声明声明了两个 Universe 参数（`u` 和 `v`），并依次实例化每个多态 {name}`List`：
```lean
def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    List.{u} α → List.{v} β
  | [] => []
  | x :: xs => f x :: map f xs
```
:::
::::

正如 Lean 自动实例化隐式参数一样，它也会自动实例化 Universe 参数。
当启用 {ref "automatic-implicit-parameters"}[自动隐式参数插入]（即 {option}`autoImplicit` 选项设置为 {lean}`true`，这是默认值）时，无需显式绑定 Universe 变量；它们会自动插入。
当它设置为 {lean}`false` 时，必须显式添加它们或使用 `universe` 命令声明它们。 {TODO}[外部参考]

:::Manual.example "Automatic Implicit Parameters and Universe Polymorphism"
当 `autoImplicit` 为 {lean}`true`（这是默认设置）时，即使不绑定其 Universe 参数，也会接受此定义：
```lean -keep
set_option autoImplicit true
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

当 `autoImplicit` 为 {lean}`false` 时，定义将被拒绝，因为 `u` 和 `v` 不在范围内：
```lean +error (name := uv)
set_option autoImplicit false
def map {α : Type u} {β : Type v} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs
```
```leanOutput uv
unknown universe level `u`
```
```leanOutput uv
unknown universe level `v`
```
:::

除了使用 `autoImplicit` 之外，还可以使用 `universe` 命令将特定标识符声明为特定 {tech}[节范围] 中的 Universe 变量。

:::syntax Lean.Parser.Command.universe (title := "Universe Parameter Declarations")
```grammar
universe $x:ident $xs:ident*
```

为当前范围的范围声明一个或多个 Universe 变量。

正如 `variable` 命令导致特定标识符被视为具有特定类型的参数一样，`universe` 命令导致后续标识符在提及它们的声明中隐式量化为 Universe 参数，即使选项 `autoImplicit` 是 {lean}`false`。
:::

:::Manual.example "The `universe` command when `autoImplicit` is `false`"
```lean -keep
set_option autoImplicit false
universe u
def id₃ (α : Type u) (a : α) := a
```
:::

由于自动隐式参数功能仅插入声明的 {tech}[header] 中使用的参数，因此仅出现在定义右侧的 Universe 变量不会作为参数插入，除非已使用 `universe` 声明它们，即使 `autoImplicit` 为 `true` 也是如此。

:::Manual.example "Automatic universe parameters and the `universe` command"

接受带有显式 Universe 参数的定义：
```lean -keep
def L.{u} := List (Type u)
```
即使使用自动隐式参数，此定义也会被拒绝，因为标头中未提及 `u`，该标头位于 `:=` 之前：
```lean +error (name := unknownUni) -keep
set_option autoImplicit true
def L := List (Type u)
```
```leanOutput unknownUni
unknown universe level `u`
```
通过 Universe 声明，即使在右侧，​​`u` 也被接受为参数：
```lean -keep
universe u
def L := List (Type u)
```
`L` 的最终定义是全域多态的，其中 `u` 作为全域参数插入。

如果 `universe` 命令范围内的声明或其他自动插入的参数中未出现 Universe 变量，则该声明不会成为多态。
```lean
universe u
def L := List (Type 0)
#check L
```
:::

### 宇宙统一
%%%
draft := true
%%%

:::planned 99
 * 统一规则、算法属性
 * 缺乏单射性
 * 未注释的归纳类型的宇宙推断
:::

### 宇宙提升
%%%
tag := "zh-types-h008"
%%%

当一种类型的 Universe 小于某些上下文中预期的 Universe 时，{deftech}_universe lift_ 运算符可以弥补这一差距。
这些是给定类型术语的包装器，它们位于比包装类型更大的宇宙中。
起重操作员有两名：
 * {name}`PLift` 可以将任何类型（包括 {tech}[命题]）提升一级。它可用于在数据结构（例如列表）中包含证明。
 * {name}`ULift` 可以将任何非命题类型提升任意数量的级别。

{docstring PLift}

{docstring ULift}

{include 0 ManualZh.Language.InductiveTypes}

{include 0 ManualZh.Quotients}
