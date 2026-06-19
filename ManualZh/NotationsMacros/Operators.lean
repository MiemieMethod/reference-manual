/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "自定义运算符" =>
%%%
tag := "operators"
%%%

Lean 支持自定义中缀、前缀和后缀运算符。
任何 Lean 库都可以添加新运算符，并且新运算符与语言中的运算符具有同等地位。
每个新运算符都会被分配一个作为函数的解释，之后运算符的使用将被转换为函数的使用。
运算符到函数调用的翻译称为其 {deftech}_expansion_。
如果此函数是 {tech}[type class] {tech}[method]，则可以通过定义该类的实例来重载生成的运算符。

所有运算符都有 {deftech}_precedence_。
运算符优先级决定了无括号表达式的运算顺序：因为乘法的优先级高于加法，所以 {lean}`2 + 3 * 4` 等效于 {lean}`2 + (3 * 4)`，{lean}`2 * 3 + 4` 等效于 {lean}`(2 * 3) + 4`。
中缀运算符还具有 {deftech}_associativity_ ，它确定具有相同优先级的运算符链的含义：

: {deftech}[左结合]

  这些运算符嵌套在左侧。
  加法是左关联的，因此 {lean}`2 + 3 + 4 + 5` 相当于 {lean}`((2 + 3) + 4) + 5`。

: {deftech}[右结合]

  这些运算符嵌套在右侧。
  产品类型是右关联的，因此 {lean}`Nat × String × Unit × Option Int` 等效于 {lean}`Nat × (String × (Unit × Option Int))`。

: {deftech}[非关联]

  链接这些运算符是一个语法错误。
  需要明确的括号。
  相等是非关联的，因此以下是错误的：

  ```syntaxError eqs (category := term)
  1 + 2 = 3 = 2 + 1
  ```
  解析器错误是：
  ```leanOutput eqs
  <example>:1:10-1:11: expected end of input
  ```
::::keepEnv
:::example "Precedence for Prefix and Infix Operators"
```lean -show
axiom A : Prop
axiom B : Prop
example : (¬A ∧ B = (¬A) ∧ B) = (¬A ∧ ((B = ¬A) ∧ B)) := rfl
example : (¬A ∧ B) = ((¬A) ∧ B) := rfl
```

命题 {lean}`¬A ∧ B` 等效于 {lean}`(¬A) ∧ B`，因为 `¬` 的优先级高于 `∧`。
由于 `∧` 的优先级高于 `=` 并且是右关联的，因此 {lean}`¬A ∧ B = (¬A) ∧ B` 等效于 {lean}`¬A ∧ ((B = ¬A) ∧ B)`。
:::
::::

Lean 提供用于定义新运算符的命令：
:::syntax command (title := "Operator Declarations")
非关联中缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`infix` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

左关联中缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`infixl` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixl:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

右关联中缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`infixr` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind infixr:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

前缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`prefix` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind prefix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```

后缀运算符使用 {keywordOf Lean.Parser.Command.mixfix}`postfix` 定义：
```grammar
$[$_:docComment]?
$[$_:attributes]?
$_:attrKind postfix:$_ $[(name := $x)]? $[(priority := $_:prio)]? $s:str => $t:term
```
:::

每个命令前面可能带有 {tech}[文档注释] 和 {tech}[属性]。
当用户将鼠标悬停在运算符上时会显示文档注释，并且属性可以调用任意元程序，就像任何其他声明一样。
属性 {attr}`inherit_doc` 导致实现该运算符的函数的文档被该运算符本身重用。

运算符与 {tech}[节范围] 的交互方式与属性相同。
默认情况下，运算符可在任何可传递导入在其中建立它们的模块中使用，但可以将它们声明为 `scoped` 或 `local`，以分别将其可用性限制在当前名称空间已打开的上下文或当前 {tech}[节范围] 中。

自定义运算符需要 {ref "precedence"}[优先级] 说明符，后跟冒号。
自定义运算符没有可回退的默认优先级。

操作符可以被明确命名。
该名称表示 Lean 语法的扩展，主要用于元编程。
如果未显式提供名称，则 Lean 根据运算符生成一个名称。
不应依赖此名称分配的细节，因为内部名称分配算法可能会发生变化，而且在上游依赖项中引入类似的运算符可能会导致冲突，在这种情况下，Lean 将修改分配的名称，直到它是唯一的。

::::keepEnv
:::example "Assigned Operator Names"
给定这个中缀运算符：
```lean
infix:90 " ⤴ " => Option.getD
```
内部名称 {name}`«term_⤴_»` 被分配给生成的解析器扩展。
:::
::::

::::keepEnv
:::example "Provided Operator Names"
给定这个中缀运算符：
```lean
infix:90 (name := getDOp) " ⤴ " => Option.getD
```
生成的解析器扩展名为 {name}`getDOp`。
:::
::::

::::keepEnv
:::example "Inheriting Documentation"
给定这个中缀运算符：
```lean
@[inherit_doc]
infix:90 " ⤴ " => Option.getD
```
生成的解析器扩展具有与 {name}`Option.getD` 相同的文档。
:::
::::



当定义多个共享相同语法的运算符时，Lean 的解析器会尝试所有这些运算符。
如果多个规则成功，则选择使用最多输入的规则 - 这称为 {deftech}_本地最长匹配规则_。
在某些情况下，解析多个运算符可能会成功，所有运算符都覆盖相同的输入范围。
在这些情况下，操作员的 {tech}[priority] 用于选择适当的结果。
最后，如果具有相同优先级的多个运算符匹配最长匹配，解析器将保存所有结果，并且精化器依次尝试每个结果，如果精化在其中一个结果上没有成功，则失败。

:::::keepEnv

::::example "Ambiguous Operators and Priorities"

:::keepEnv
将 `+` 的替代实现定义为 {lean}`Or` 仅需要中缀运算符声明。
```lean
infix:65  " + " => Or
```

通过此声明，Lean 尝试使用 {name}`HAdd.hAdd` 的内置语法和 {lean}`Or` 的新语法来详细说明加法：
```lean (name := trueOrFalse1)
#check True + False
```
```leanOutput trueOrFalse1
True + False : Prop
```
```lean (name := twoPlusTwo1)
#check 2 + 2
```
```leanOutput twoPlusTwo1
2 + 2 : Nat
```

但是，由于 new 运算符不具有关联性，因此 {tech}[本地最长匹配规则] 意味着只有 {name}`HAdd.hAdd` 适用于不带括号的三参数版本：
```lean +error (name := trueOrFalseOrTrue1)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue1
failed to synthesize instance of type class
  HAdd Prop Prop ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

:::

:::keepEnv
如果以高优先级声明中缀运算符，则 Lean 在不明确的情况下不会尝试内置 {name}`HAdd.hAdd` 运算符：
```lean
infix:65 (priority := high)  " + " => Or
```

```lean (name := trueOrFalse2)
#check True + False
```
```leanOutput trueOrFalse2
True + False : Prop
```
```lean (name := twoPlusTwo2) +error
#check 2 + 2
```
```leanOutput twoPlusTwo2
failed to synthesize instance of type class
  OfNat Prop 2
numerals are polymorphic in Lean, but the numeral `2` cannot be used in a context where the expected type is
  Prop
due to the absence of the instance above

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

new 运算符不具有关联性，因此 {tech}[本地最长匹配规则] 意味着只有 {name}`HAdd.hAdd` 适用于三参数版本：
```lean +error (name := trueOrFalseOrTrue2)
#check True + False + True
```
```leanOutput trueOrFalseOrTrue2
failed to synthesize instance of type class
  HAdd Prop Prop ?m.3

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
:::

::::
:::::


实际的运算符以字符串文字形式提供。
新的经营者必须满足以下要求：
 * 它必须至少包含一个字符。
 * 第一个字符不能是单引号或双引号（`'` 或 `"`），除非运算符是 `''`。
 * 它不能以反引号 (`` ` ``) 开头，后跟作为带引号名称的有效前缀的字符。
 * 它可能不以数字开头。
 * 它可能不包含内部空格。

运算符字符串文字可以以空格开头或结尾。
这些不是运算符语法的一部分，并且它们的存在不需要在运算符的使用周围有空格。
但是，空格的存在会导致 Lean 在向用户显示操作员时插入空格。
省略它们会导致运算符的参数立即显示在运算符本身旁边。


:::keepEnv
```lean -show
-- Test claim about internal whitespace in preceding paragraph
/-- error: invalid atom -/
#check_msgs in
infix:99 " <<<< >>>> " => Nat.add


--- Test further claims about allowed atoms
/-- error: invalid atom -/
#check_msgs in
infix:9 (name := bogus) "" => Nat.mul


/-- error: invalid atom -/
#check_msgs in
infix:9 (name := alsobogus) " ` " => Nat.mul

-- this one's OK
#check_msgs in
infix:9 (name := nonbogus) " `` " => Nat.mul

/-- error: invalid atom -/
#check_msgs in
infix:9 (name := bogus) "`a" => Nat.mul

```
:::

最后，提供了运算符的含义，与运算符之间用 {keywordOf Lean.Parser.Command.mixfix}`=>` 分隔。
这可以是任何 Lean 术语。
运算符的使用被脱糖到函数应用程序中，并在函数位置中提供术语。
前缀和后缀运算符将术语作为显式参数应用于其单个参数。
中缀运算符按该顺序将该术语应用于左右参数。
除了在每个调用站点接受参数的能力之外，对该术语没有任何具体要求。
运算符可以构造函数，因此该术语可能需要比运算符更多的参数。
隐式参数和 {tech}[实例隐式] 参数在每个应用程序站点解析，这允许通过 {tech}[类型类] {tech}[方法] 定义运算符。

```lean -show -keep
-- Double-check claims about operators above
prefix:max "blah" => Nat.add
#check (blah 5)
```

如果该术语由全局环境中的名称或此类名称对一个或多个参数的应用组成，则 Lean 会自动为运算符生成 {tech}[unexpander]。
这意味着当功能项本来会显示时，运算符将显示在 {tech}[证明状态]、错误消息和 Lean 的其他输出中。
Lean 不会跟踪原始术语中是否使用了该运算符；只要有机会，它就会被插入。

:::::keepEnv
::::example "Custom Operators in Lean's Output"
如果数字不太大，则函数 {lean}`perhapsFactorial` 计算该数字的阶乘。
```lean
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * fact n

def perhapsFactorial (n : Nat) : Option Nat :=
  if n < 8 then some (fact n) else none
```

可以使用后缀 interrobang 运算符来表示它。
```lean
postfix:90 "‽" => perhapsFactorial
```

当尝试证明 {lean}`∀ n, n ≥ 8 → (perhapsFactorial n).isNone` 时，初始证明状态使用 new 运算符，即使所写的定理不会：
```proofState
∀ n, n ≥ 8 → (perhapsFactorial n).isNone := by skip
/--
⊢ ∀ (n : Nat), n ≥ 8 → n‽.isNone = true
-/

```
::::
:::::

:::example "Infix Operators, Defined Functions, and Unexpanders"
当运算符不扩展为 defiend 函数的应用时，不会生成解扩展器。
在这里，后缀 interrobang 扩展为一个匿名函数，如果其参数不太大，则该函数接受阶乘。

```lean
def fact : Nat → Nat
  | 0 => 1
  | n+1 => (n + 1) * fact n

set_option quotPrecheck false in
postfix:90 "‽" => fun (n : Nat) => if n < 8 then some (fact n) else none
```

由于展开中没有命名函数，因此无法生成解展开器：
```lean (name := noUnexp)
#check 7‽
```
```leanOutput noUnexp
(fun n => if n < 8 then some (fact n) else none) 7 : Option Nat
```

使用命名函数会产生一个解展开器，该解展开器用于由 {name}`perhapsFactorial` 的应用程序组成的术语：
```lean
def perhapsFactorial (n : Nat) : Option Nat :=
  if n < 8 then some (fact n) else none

postfix:90 "‽'" => perhapsFactorial

```
```lean (name := withUnexp)
#check 7‽'
```
```leanOutput withUnexp
7‽' : Option Nat
```
:::
