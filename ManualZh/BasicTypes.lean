/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import ManualZh.BasicTypes.Nat
import ManualZh.BasicTypes.Int
import ManualZh.BasicTypes.String
import ManualZh.BasicTypes.Array
import ManualZh.BasicTypes.ByteArray
import ManualZh.BasicTypes.Fin
import ManualZh.BasicTypes.UInt
import ManualZh.BasicTypes.BitVec
import ManualZh.BasicTypes.Float
import ManualZh.BasicTypes.Char
import ManualZh.BasicTypes.Option
import ManualZh.BasicTypes.Empty
import ManualZh.BasicTypes.Products
import ManualZh.BasicTypes.Sum
import ManualZh.BasicTypes.List
import ManualZh.BasicTypes.Maps
import ManualZh.BasicTypes.Subtype
import ManualZh.BasicTypes.Thunk
import ManualZh.BasicTypes.Range

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "基本类型" =>
%%%
tag := "basic-types"
%%%


Lean 包含许多编译器特别支持的内置类型。
有些（例如 {lean}`Nat`）在内核中还具有特殊支持。
其他类型本身没有特殊的编译器支持，但出于性能原因在重要方面依赖于类型的内部表示。

{include 0 ManualZh.BasicTypes.Nat}

{include 0 ManualZh.BasicTypes.Int}

{include 0 ManualZh.BasicTypes.Fin}

{include 0 ManualZh.BasicTypes.UInt}

{include 0 ManualZh.BasicTypes.BitVec}

{include 0 ManualZh.BasicTypes.Float}

{include 0 ManualZh.BasicTypes.Char}


{include 0 ManualZh.BasicTypes.String}

# 单位 Type

单元类型是只有一个元素的规范类型，名为 {name Unit.unit}`unit`，并由空元组 {lean}`()` 表示。
它仅描述一个值，该值由不应用于任何参数的所述构造函数组成。

{lean}`Unit` 类似于源自 C 的语言中的 `void`：尽管 `void` 没有可命名的元素，但它表示从没有附加信息的函数返回控制流。
在函数式编程中，{lean}`Unit` 是“不返回任何内容”的返回类型。
从数学上讲，这由一个完全无信息的值表示，而不是像 {lean}`Empty` 这样表示无法访问的代码的空类型。

:::leanSection
```lean -show
variable {m : Type → Type} [Monad m] {α : Type}
```

当使用 {ref "monads-and-do"}[monads]​​ 进行编程时，{lean}`Unit` 特别有用。
对于任何类型 {lean}`α`，{lean}`m α` 表示具有副作用并返回 {lean}`α` 类型的值的操作。
{lean}`m Unit` 类型表示具有一些副作用但不返回值的操作。

:::



单位类型有两种变体：

 * {lean}`Unit` 是存在于最小非命题 {tech}[宇宙] 中的 {lean}`Type`。

 * {lean}`PUnit` 是 {tech (key := "universe polymorphism")}[宇宙多态]，可用于任何非命题 {tech}[宇宙]。

在幕后，{lean}`Unit` 实际上被定义为 {lean}`PUnit.{1}`。
如果可能，{lean}`Unit` 应优先于 {name}`PUnit`，以避免不必要的 Universe 参数。
如果有疑问，请使用 {lean}`Unit` 直到出现 Universe 错误。

{docstring Unit}

{docstring Unit.unit}

{docstring PUnit}

## 定义等价

{deftech}_Unit-like types_ 是具有单个构造函数的归纳类型，该构造函数不采用非证明参数。
{lean}`PUnit` 就是此类类型之一。
类似单元类型的所有元素都是 {tech (key := "definitional equality")}[定义上等于]所有其他元素。

:::example "Definitional Equality of {lean}`Unit`"
每个 {lean}`Unit` 类型的术语在定义上都等于 {lean}`Unit` 类型的所有其他术语：

```lean
example (e1 e2 : Unit) : e1 = e2 := rfl
```
:::

::::keepEnv
:::example "Definitional Equality of Unit-Like Types"

{lean}`CustomUnit` 和 {lean}`AlsoUnit` 都是类似单元的类型，具有不带参数的单个构造函数。
任一类型的每对术语在定义上都是相等的。

```lean
inductive CustomUnit where
  | customUnit

example (e1 e2 : CustomUnit) : e1 = e2 := rfl

structure AlsoUnit where

example (e1 e2 : AlsoUnit) : e1 = e2 := rfl
```

带参数的类型（例如 {lean}`WithParam`）如果具有不带参数的单个构造函数，那么它们也是类似单元的。

```lean
inductive WithParam (n : Nat) where
  | mk

example (x y : WithParam 3) : x = y := rfl
```

具有非证明参数的构造函数不是类单元的，即使参数都是类单元类型。
```lean
inductive NotUnitLike where
  | mk (u : Unit)
```

```lean +error (name := NotUnitLike)
example (e1 e2 : NotUnitLike) : e1 = e2 := rfl
```
```leanOutput NotUnitLike
Type mismatch
  rfl
has type
  ?m.13 = ?m.13
but is expected to have type
  e1 = e2
```

类单元类型的构造函数可以采用作为证明的参数。
```lean
inductive ProofUnitLike where
  | mk : 2 = 2 → ProofUnitLike

example (e1 e2 : ProofUnitLike) : e1 = e2 := rfl
```
:::
::::

{include 0 ManualZh.BasicTypes.Empty}


# 布尔值

{docstring Bool}

构造函数 {lean}`Bool.true` 和 {lean}`Bool.false` 是从 {lean}`Bool` 命名空间导出的，因此它们可以写成 {lean}`true` 和 {lean}`false`。

## 运行时表示

由于 {lean}`Bool` 是 {tech}[enum inducing] 类型，因此它在编译代码中由单个字节表示。

## 布尔值和命题

{lean}`Bool` 和 {lean}`Prop` 都代表真理的概念。
从纯粹的逻辑角度来看，它们是等价的：{tech}[命题外延性]意味着基本上只有两个命题，即{lean}`True`和{lean}`False`。
但是，存在一个重要的实用差异：{lean}`Bool` 对可以由程序计算的值进行分类，而 {lean}`Prop` 对代码生成没有意义的语句进行分类。
换句话说，{lean}`Bool` 是适用于程序的真与假概念，而 {lean}`Prop` 是适用于数学的概念。
由于校样已从编译的程序中删除，因此保持 {lean}`Bool` 和 {lean}`Prop` 不同可以清楚地表明 Lean 文件的哪些部分用于计算。

```lean -show
section BoolProp

axiom b : Bool

/-- info: b = true : Prop -/
#check_msgs in
#check (b : Prop)

example : (true = true) = True := by simp

#check decide
```

{lean}`Bool` 可以用在任何需要 {lean}`Prop` 的地方。
从每个 {lean}`Bool` {lean}`b` 到命题 {lean}`b = true` 都有一个 {tech}[强制]。
通过 {lean}`propext`，{lean}`true = true` 等于 {lean}`True`，{lean}`false = true` 等于 {lean}`False`。

并非每个命题都可以被程序用来做出运行时决策。
否则，程序可能会根据 Collatz 猜想是真是假而产生分支！
然而，许多命题可以通过算法进行检查。
这些命题称为 {tech}_decidable_ 命题，并且具有 {lean}`Decidable` 类型类的实例。
函数 {name}`Decidable.decide` 将携带证明的 {lean}`Decidable` 结果转换为 {lean}`Bool`。
该函数也是从可判定命题到 {lean}`Bool` 的强制转换，因此 {lean}`(2 = 2 : Bool)` 的计算结果为 {lean}`true`。

```lean -show
/-- info: true -/
#check_msgs in
#eval (2 = 2 : Bool)
end BoolProp
```

## 句法

:::syntax term (title := "Boolean Infix Operators")
中缀运算符 `&&`、`||` 和 `^^` 分别是 {lean}`Bool.and`、{lean}`Bool.or` 和 {lean}`Bool.xor` 的表示法。

```grammar
$_:term && $_:term
```
```grammar
$_:term || $_:term
```
```grammar
$_:term ^^ $_:term
```
:::

:::syntax term (title := "Boolean Negation")
前缀运算符 `!` 是 {lean}`Bool.not` 的表示法。
```grammar
!$_:term
```
:::


## API 参考

### 逻辑运算

```lean -show
section ShortCircuit

axiom BIG_EXPENSIVE_COMPUTATION : Bool
```

功能 {name}`cond`、{name Bool.and}`and` 和 {name Bool.or}`or` 被短路。
换句话说，{lean}`false && BIG_EXPENSIVE_COMPUTATION` 在返回 `false` 之前不需要执行 {lean}`BIG_EXPENSIVE_COMPUTATION`。
这些函数是使用 {attr}`macro_inline` 属性定义的，这会导致编译器在生成代码时用它们的定义替换对它们的调用，并且定义使用嵌套的模式匹配来实现短路行为。

```lean -show
end ShortCircuit
```


{docstring cond}

{docstring Bool.dcond}

{docstring Bool.not}

{docstring Bool.and}

{docstring Bool.or}

{docstring Bool.xor}

### 比较

大多数布尔值比较应使用 {inst}`DecidableEq Bool`、{inst}`LT Bool`、{inst}`LE Bool` 实例执行。

{docstring Bool.decEq}

### 转换

{docstring Bool.toISize}

{docstring Bool.toUInt8}

{docstring Bool.toUInt16}

{docstring Bool.toUInt32}

{docstring Bool.toUInt64}

{docstring Bool.toUSize}

{docstring Bool.toInt8}

{docstring Bool.toInt16}

{docstring Bool.toInt32}

{docstring Bool.toInt64}

{docstring Bool.toNat}

{docstring Bool.toInt}


{include 0 ManualZh.BasicTypes.Option}

{include 0 ManualZh.BasicTypes.Products}

{include 0 ManualZh.BasicTypes.Sum}

{include 0 ManualZh.BasicTypes.List}

{include 0 ManualZh.BasicTypes.Array}

{include 0 ManualZh.BasicTypes.ByteArray}

{include 0 ManualZh.BasicTypes.Range}

{include 0 ManualZh.BasicTypes.Maps}

{include 0 ManualZh.BasicTypes.Subtype}

{include 0 ManualZh.BasicTypes.Thunk}
