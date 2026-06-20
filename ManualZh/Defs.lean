/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import ManualZh.RecursiveDefs

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

set_option maxRecDepth 1500

#doc (Manual) "定义" =>
%%%
tag := "definitions"
%%%


Lean 中的以下命令类似于定义： {TODO}[将命令渲染为其名称（类似于策略索引）]
 * {keyword}`def`
 * {keyword}`abbrev`
 * {keyword}`example`
 * {keyword}`theorem`
 * {keyword}`opaque`

所有这些命令都会导致 Lean 变为 {tech (key := "elaborator") -normalize}[详细精化]基于 {tech}[签名]的术语。
除了 {keywordOf Lean.Parser.Command.example}`example` 会丢弃结果之外，Lean 核心语言中的结果表达式将被保存以供将来在环境中使用。
{keywordOf Lean.Parser.Command.declaration}`instance` 命令在 {ref "instance-declarations"}[有关实例声明的部分]中进行了描述。


# 修饰符
%%%
tag := "declaration-modifiers"
%%%

声明接受一组一致的 {deftech}_modifiers_，所有这些都是可选的。
修饰符改变了声明解释的某些方面；例如，他们可以添加文档或更改其范围。
修饰符的顺序是固定的，但并非每种声明都接受每种修饰符。

:::syntax declModifiers -open (alias:=Lean.Parser.Command.declModifiers) (title := "Declaration Modifiers")
修饰符按顺序由以下各项组成，所有这些都是可选的：
 1. 文档注释，
 2. {tech}[属性] 列表，
 3. 命名空间控制，指定结果名称是 {tech}[private] 还是 {tech}[protected]，
 4. {keyword}`noncomputable` 关键字，使定义免于编译，
 5. {keyword}`unsafe` 关键字，以及
 6. 递归修饰符 {keyword}`partial` 或 {keyword}`nonrec`，禁用终止证明或完全禁止递归。
```grammar
$[$_:docComment]?
$[$_:attributes]?
$[$_]?
$[noncomputable]?
$[unsafe]?
$[$_]?
```
:::

{deftech}_Documentation comments_ 用于为它们修改的声明提供源内 API 文档。
事实上，文档注释不是注释：将文档注释放在不作为文档处理的位置是一个语法错误。
它们也出现在需要某种文本的位置，但字符串转义会很麻烦，例如 {keywordOf Lean.guardMsgsCmd}`#guard_msgs` 命令上所需的消息。

:::syntax docComment -open (title := "Documentation Comments")

文档注释与普通块注释类似，但它们以序列 `/--` 而不是 `/-` 开头；就像普通注释一样，它们以 `-/` 结尾。

```grammar
/--
...
-/
```
:::

属性是将附加信息与声明相关联的修饰符的可扩展集合。
它们在 {ref "attributes"}[专用部分]中进行了描述。

如果声明标记为 {deftech (key := "private")}[{keyword}`private`]，则在定义它的模块外部无法访问该声明。
如果它是 {keyword}`protected`，则打开其命名空间不会将其纳入范围。

标记为 {keyword}`noncomputable` 的函数未编译且无法执行。
如果函数使用不可计算的推理原则（例如选择公理或排除中间）来生成与其返回的答案相关的数据，或者如果它们使用出于效率原因而免于代码生成的 Lean 功能（例如 {tech}[recursors]），则函数必须是不可计算的。
不可计算函数对于规范和推理非常有用，即使它们无法编译和执行。

{keyword}`unsafe` 标记使定义免于内核检查，并使其能够访问可能破坏 Lean 保证的功能。
使用时应非常小心，并且必须彻底了解 Lean 的内部结构。


# 标头和签名
%%%
tag := "signature-syntax"
%%%

定义或声明的 {deftech}[_header_] 由声明或定义的常量（如果相关）及其签名组成。
常量的 {deftech}_signature_ 指定如何使用它。
签名中呈现的信息不仅仅是类型，还包括{tech (key := "universe parameter")}[宇宙层级参数]等信息及其可选参数的默认值。
在Lean中，不同类型的声明中的签名都以一致的格式书写。

## 声明名称
%%%
tag := "zh-defs-h003"
%%%

大多数标头以 {deftech}_declaration name_ 开头，后面跟着正确的签名：其参数和结果类型。
声明名称是可以选择包含 Universe 参数的名称。

:::syntax declId -open (title := "Declaration Names")
不带 Universe 参数的声明名称由标识符组成：
```grammar
$_:ident
```

带有 Universe 参数的声明名称由一个标识符后跟一个句点以及大括号中的一个或多个 Universe 参数名称组成：
```grammar
$_.{$_, $_,*}
```
这些 Universe 参数名称是绑定事件。
:::

示例不包括声明名称，并且实例声明的名称是可选的。

## 参数和类型
%%%
tag := "parameter-syntax"
%%%

名称后面（如果存在）是标头的签名。
签名指定声明的参数和类型。

:::syntax declSig -open (title := "Declaration Signatures")
签名由零个或多个参数组成，后跟冒号和类型。

```grammar
$_* : $_
```
:::

:::syntax optDeclSig -open (title := "Optional Signatures")
签名通常是可选的。
在这些情况下，即使省略类型，也可以提供参数。
```grammar
$_* $[: $_]?
```
:::


参数可以有三种形式：
 * 标识符，命名参数但不提供类型。
   这些参数的类型必须在精化期间推断。
 * 下划线 (`_`)，表示在本地范围内无法通过名称访问的参数。
   这些参数的类型也必须在精化期间推断。
 * 一种带括号的绑定器，它可以指定一个或多个参数的各个方面，包括它们的名称、类型、默认值以及它们是显式的、隐式的、严格隐式的还是实例隐式的。

## 带括号的参数绑定
%%%
tag := "bracketed-parameter-syntax"
%%%


除标识符或下划线之外的参数统称为 {deftech}_bracketed binders_，因为指定它们的每个语法形式都有某种类型的方括号、大括号或圆括号。
所有括号内的绑定程序都指定参数的类型，并且大多数都包含参数名称。
对于实例隐式参数，名称是可选的。
使用下划线 (`_`) 代替参数名称表示匿名参数。


:::syntax bracketedBinder -open (title := "Explicit Parameters")
带括号的参数表示显式参数。
如果提供了多个标识符或下划线，则它们全部成为同一类型的参数。
```grammar
($x $x* : $t)
```
:::

:::syntax bracketedBinder (title := "Optional and Automatic Parameters")
带 `:=` 的括号参数为参数分配默认值。
具有默认值的参数称为 {deftech}_可选参数_。
在调用站点，如果未提供参数，则使用提供的术语来填充它。
签名中的先前参数在默认值范围内，并且它们在调用站点的值将替换为默认值项。

如果提供了 {ref "tactics"}[策略脚本]，则在调用站点执行策略以合成参数值；通过策略填写的参数称为{deftech}_自动参数_。
```grammar
($x $x* : $t := $e)
```
:::

:::syntax bracketedBinder (title := "Implicit Parameters")
大括号中的参数表示 {tech}[隐式] 参数。
除非在调用站点通过名称提供，否则这些参数预计将通过调用站点的统一进行合成。
隐式参数在所有调用站点进行综合。
```grammar
{$x $x* : $t}
```
:::

:::syntax bracketedBinder (title := "Strict Implicit Parameters")
双花括号中的参数表示 {tech}[严格隐式] 参数。
`⦃ … ⦄` 和 `{{ … }}` 等效。
与隐式参数一样，当未按名称提供这些参数时，预计将通过调用站点的统一来合成这些参数。
仅当还提供了签名中的后续参数时，才会在调用站点合成严格的隐式参数。

```grammar
⦃$x $x* : $t⦄
```
```grammar
{{$x $x* : $t}}
```

:::

:::syntax bracketedBinder (title := "Instance Implicit Parameters")
方括号中的参数表示 {tech}[实例隐式] 参数，这些参数是使用 {tech (key := "synthesis")}[实例合成] 在调用站点合成的。
```grammar
[$[$x :]? $t]
```
:::

参数始终位于签名类型的范围内，该类型出现在冒号之后。
它们也在声明主体的范围内，而在类型本身中绑定的名称仅在类型的范围内。
因此，参数名称被使用两次：
 * 作为声明函数类型中的名称，绑定为 {tech (key := "dependent")}[依赖函数类型] 的一部分。
 * 作为声明正文中的名称。
   在函数定义中，它们由 {keywordOf Lean.Parser.Term.fun}`fun` 绑定。

:::example "Parameter Scope"
{lean}`add` 的签名包含一个参数 `n`。
另外，签名的类型是{lean}`(k : Nat) → Nat`，它是包含`k`的函数类型。
参数 `n` 在函数体的范围内，但 `k` 不在。

```lean
def add (n : Nat) : (k : Nat) → Nat
  | 0 => n
  | k' + 1 => 1 + add n k'
```

与 {lean}`add` 一样，{lean}`mustBeEqual` 的签名包含一个参数 `n`。
它在类型中（它出现在命题中）和正文中（它作为消息的一部分出现）都在范围内。
```lean
def mustBeEqual (n : Nat) : (k : Nat) → n = k → String :=
  fun _ =>
    fun
    | rfl => s!"Equal - both are {n}!"

```
:::

{ref "function-application"}[函数应用]部分详细介绍了 {tech (key := "optional parameter")}[可选]、{tech (key := "automatic parameter")}[自动]、{tech}[隐式]和 {tech}[实例隐式]参数的解释。

## 自动隐式参数
%%%
tag := "automatic-implicit-parameters"
%%%


默认情况下，签名中出现的其他未绑定名称会在可能的情况下转换为隐式参数
这些参数称为 {deftech}_自动隐式参数_。
当它们不处于应用程序的功能位置并且签名中有足够的可用信息来推断它们的类型以及它们的任何排序约束时，这是可能的。
迭代此过程：如果新插入的隐式参数的推断类型具有未唯一确定的依赖项，则这些依赖项将替换为进一步的隐式参数。

与签名中写入的名称不对应的隐式参数被分配的名称类似于证明中 {tech}[不可访问] 假设的名称，无法引用。
它们出现在带有匕首的签名中（`'✝'`）。
这可以防止 Lean 任意选择的名称通过用作 {tech}[命名参数] 成为 API 的一部分。

::::leanSection
```lean -show
variable {α : Type u} {β : Type v}
```
:::example "Automatic Implicit Parameters"

在{lean}`map`的这个定义中，{lean}`α`和{lean}`β`没有明确地绑定。
这不是一个错误，而是被转换为隐式参数。
因为它们必须是类型，但没有任何东西限制它们的 Universe，所以还插入了 Universe 参数 `u` 和 `v`。
```lean
def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

{lean}`map`的完整签名为：
```signature
map.{u, v} {α : Type u} {β : Type v}
  (f : α → β) (xs : List α) :
  List β
```
:::
::::

::::example "No Automatic Implicit Parameters"

:::leanSection
```lean -show
universe u v
variable {α : Type u} {β : Type v}
```

在此定义中，{lean}`α` 和 {lean}`β` 没有显式绑定。
由于 {option}`autoImplicit` 已禁用，因此这是一个错误：
:::

:::keepEnv
```lean +error (name := noAuto)
set_option autoImplicit false

def map (f : α → β) : (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

```leanOutput noAuto
Unknown identifier `α`

Note: It is not possible to treat `α` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```
```leanOutput noAuto
Unknown identifier `β`

Note: It is not possible to treat `β` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```
:::


完整的签名允许定义被接受：
```lean -keep
set_option autoImplicit false

def map.{u, v} {α : Type u} {β : Type v}
    (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

对于没有显式类型注释的参数，将自动插入 Universe 参数。
即使 {option}`autoImplicit` 被禁用，也可以推断类型参数的 Universe，并插入适当的 Universe 参数：
```lean -keep
set_option autoImplicit false

def map {α β} (f : α → β) :
    (xs : List α) → List β
  | [] => []
  | x :: xs => f x :: map f xs
```

::::



:::::example "Iterated Automatic Implicit Parameters"

:::leanSection
```lean -show
variable (i : Fin n)
```
给定一个由 {lean}`n` 界定的数字（由类型 `Fin n` 表示），{lean}`AtLeast i` 是一个自然数，并且证明它至少与 `i` 一样大。
:::
```lean
structure AtLeast (i : Fin n) where
  val : Nat
  val_gt_i : val ≥ i.val
```

可以添加这些数字：
```lean
def AtLeast.add (x y : AtLeast i) : AtLeast i :=
  AtLeast.mk (x.val + y.val) <| by
    cases x
    cases y
    dsimp only
    omega
```

::::paragraph
:::leanSection
```lean -show
variable (i : Fin n)
```
{lean}`AtLeast.add`的签名需要多轮自动隐式参数插入。
首先插入{lean}`i`；但其类型取决于 {lean}`Fin n` 的上限 {lean}`n`。
在第二轮中，使用机器选择的名称插入 {lean}`n`。
由于 {lean}`n` 的类型是 {lean}`Nat`，它没有依赖性，因此进程终止。
最终签名可以通过 {keywordOf Lean.Parser.Command.check}`#check` 看到：
:::
```lean (name := checkAdd)
#check AtLeast.add
```
```leanOutput checkAdd
AtLeast.add {n✝ : Nat} {i : Fin n✝} (x y : AtLeast i) : AtLeast i
```
::::

:::::

由于 {tech}[节变量]，在插入参数后会发生自动隐式参数插入。
与节变量相对应的参数具有与相应变量相同的名称，即使它们不与直接写入签名中的名称相对应，并且禁用自动隐式参数不会影响与节变量相对应的参数。
但是，当启用自动隐式参数时，包含其他未绑定变量的节变量声明会接收遵循与隐式参数相同规则的附加节变量。

自动隐式参数插入由两个选项控制。
默认情况下，自动隐式参数插入是_relaxed_，这意味着任何未绑定的标识符都可以是自动插入的候选者。
将选项 {option}`relaxedAutoImplicit` 设置为 {lean}`false` 会禁用宽松模式，并导致仅考虑由单个字符后跟零个或多个数字组成的标识符进行自动插入。

{optionDocs relaxedAutoImplicit}

{optionDocs autoImplicit}


::::example "Relaxed vs Non-Relaxed Automatic Implicit Parameters"

拼写错误的标识符或丢失的导入最终可能会成为不需要的隐式参数，如下例所示：
```lean
inductive Answer where
  | yes
  | maybe
  | no
```
:::keepEnv
```lean  (name := asnwer) +error
def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
生成的错误消息指出参数的类型不是常量，因此点符号不能在模式中使用：
```leanOutput asnwer
Invalid dotted identifier notation: The expected type of `.yes`
  Asnwer
is not of the form `C ...` or `... → C ...` where C is a constant
```
这是因为签名是：
```signature
select.{u_1, u_2}
  {α : Type u_1}
  {Asnwer : Sort u_2}
  (choices : α × α × α) :
  Asnwer → α
```
:::

禁用宽松的自动隐式参数可以使错误更加清晰，同时仍然允许自动插入类型：
:::keepEnv
```lean  (name := asnwer2) +error
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Asnwer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput asnwer2
Unknown identifier `Asnwer`

Note: It is not possible to treat `Asnwer` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `false`.
```
:::

纠正错误可以使定义被接受。
:::keepEnv
```lean
set_option relaxedAutoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
:::

关闭自动隐式参数完全会导致定义被拒绝：
:::keepEnv
```lean +error (name := noauto)
set_option autoImplicit false

def select (choices : α × α × α) : Answer →  α
  | .yes => choices.1
  | .maybe => choices.2.1
  | .no => choices.2.2
```
```leanOutput noauto
Unknown identifier `α`

Note: It is not possible to treat `α` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
```
:::
::::

# 定义
%%%
tag := "zh-defs-h007"
%%%

定义向全局环境添加一个新常量作为代表术语的名称。
作为内核的 定义等价 的一部分，这个新常数可以通过 {tech (key := "δ")}[δ-reduction] 替换为它所代表的术语。
在精化器中，此替换由常数的 {tech}[约简性] 控制。
新常量可能是 {tech (key := "universe polymorphism")}[宇宙多态]，在这种情况下，事件可能会使用不同的 宇宙层级 参数来实例化它。

函数定义可以是递归的。
为了保持 Lean 的类型论作为逻辑的一致性，递归函数必须对内核不透明（例如通过 {ref "partial-functions"}[声明它们 {keyword}`partial`]），或者必须证明它们会终止；可用策略之一见 {ref "recursive-definitions"}[递归定义一节]。

定义的标题和正文一起详细说明。
如果标头未完整指定（例如，参数的类型或密码域丢失），则主体可以为精化器提供足够的信息来重建丢失的部分。
但是，{tech}[实例隐式]参数必须在标头中指定或指定为 {tech}[节变量]。

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.definition) (title := "Definitions")
使用 `:=` 的定义将右侧的术语与常量名称相关联。
该术语包装在每个参数的 {keywordOf Lean.Parser.Term.fun}`fun` 中，并且通过将参数绑定到函数类型中来找到类型。
{keyword}`def` 的定义是 {tech}[半可约]。

```grammar
$_:declModifiers
def $_ $_ := $_
```

定义可以使用模式匹配。
这些定义针对 {keywordOf Lean.Parser.Term.match}`match` 的使用进行了脱糖处理。

```grammar
$_:declModifiers
def $_ $_
  $[| $_ => $_]*
```

结构类型的值或返回它们的函数可以通过为其字段提供值来定义，如下 {keyword}`where`：

```grammar
$_:declModifiers
def $_ $_ where
  $_*
```

在 {tech}[modules] 中，默认情况下不公开使用 {keyword}`def` 定义的定义主体。
:::

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.abbrev) (title := "Abbreviations")
{deftech}[缩写] 与 {keyword}`def` 的定义相同，但它们是 {tech}[可约]。

```grammar
$_:declModifiers
abbrev $_ $_ := $_
```

```grammar
$_:declModifiers
abbrev $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
abbrev $_ $_ where
  $_*
```

在 {tech}[modules] 中，默认情况下会公开使用 {keyword}`abbrev` 定义的定义主体。
:::


{deftech}_不透明常量_是不受内核中的 {tech (key := "δ")}[δ-约简] 影响的已定义常量。
它们对于指定某些函数的存在很有用。
与 {tech}[axioms] 不同，不透明声明只能用于已存在的类型，因此不会有引入不一致的风险。
与公理不同的是，类型的居民在编译代码中使用。
{attr}`implemented_by` 属性可用于指示编译器发出对某些其他函数的调用作为不透明常量的编译。

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.opaque) (title := "Opaque Constants")
右侧的不透明定义与其他定义一样详细说明。
这表明该类型有人居住；居民不再扮演任何角色。
```grammar
$_:declModifiers
opaque $_ $_ := $_
```

不透明常量也可以在没有右侧的情况下指定。
精化器通过合成 {name}`Inhabited` 的实例或 {name}`Nonempty`（如果失败）来填充右侧。
```grammar
$_:declModifiers
opaque $_ $_
```
:::

# 定理
%%%
tag := "zh-defs-h008"
%%%

:::paragraph
由于 {tech}[命题] 是其居民视为证明的类型，因此 {deftech}[定理] 和定义在技术上非常相似。
然而，由于它们的用例截然不同，因此在许多细节上有所不同：

* 定理陈述必须是一个命题。
  定义类型可以存在于任何 {tech}[universe] 中。
* 定理的标题（即定理陈述）在精化正文之前就已完全精化。
  如果节变量（或其依赖项）在标题中提及，则它们仅成为定理的参数。
  这可以防止因无意中改变定理陈述而对证明进行更改。
* 默认定理为 {tech}[不可约]。
  因为同一命题的所有证明都是 {tech (key := "definitional equality")}[定义等价]，所以几乎没有理由展开定理。
:::

定理可以是递归的，遵循与 {ref "recursive-definitions"}[递归函数定义]相同的条件。
但是，更常见的是使用策略，例如 {tactic}`induction` 或 {tactic}`fun_induction`。

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.theorem) (title := "Theorems")
定理的语法类似于定义的语法，除了签名中的共域（即定理陈述）是强制性的。
```grammar
$_:declModifiers
theorem $_ $_ := $_
```

```grammar
$_:declModifiers
theorem $_ $_
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
theorem $_ $_ where
  $_*
```

在 {tech}[modules] 中，默认情况下不公开定理证明。
:::



# 声明示例
%%%
tag := "zh-defs-h009"
%%%

{deftech}[example] 是一个匿名定义，经过详细精化后被丢弃。
示例对于开发过程中的增量测试非常有用，并且可以使文件更容易理解。

:::syntax Lean.Parser.Command.declaration (alias := Lean.Parser.Command.example) (title := "Examples")
```grammar
$_:declModifiers
example $_:optDeclSig := $_
```

```grammar
$_:declModifiers
example $_:optDeclSig
  $[| $_ => $_]*
```

```grammar
$_:declModifiers
example $_:optDeclSig where
  $_*
```
:::



{include 0 ManualZh.RecursiveDefs}
