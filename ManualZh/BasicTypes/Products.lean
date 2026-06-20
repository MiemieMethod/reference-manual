/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "元组" =>
%%%
file := "Tuples"
tag := "tuples"
%%%



:::paragraph
Lean 标准库包含各种类似元组的类型。
在实践中，它们有四个方面的不同：
 * 第一个投影是类型还是命题
 * 第二个投影是类型还是命题
 * 第二个投影的类型是否取决于第一个投影的值
 * 类型作为一个整体是命题还是类型
:::

:::table +header
* + Type
  + 第一个投影
  + 第二次投影
  + 依赖？
  + 宇宙
* + {name}`Prod`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Type v`
  + ❌️
  + {lean (universes := "u v")}`Type (max u v)`
* + {name}`And`
  + {lean (universes := "u v")}`Prop`
  + {lean (universes := "u v")}`Prop`
  + ❌️
  + {lean (universes := "u v")}`Prop`
* + {name}`Sigma`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Type v`
  + ✔
  + {lean (universes := "u v")}`Type (max u v)`
* + {name}`Subtype`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Prop`
  + ✔
  + {lean (universes := "u v")}`Type u`
* + {name}`Exists`
  + {lean (universes := "u")}`Type u`
  + {lean (universes := "v")}`Prop`
  + ✔
  + {lean (universes := "u v")}`Prop`
:::

:::paragraph
该表中的一些潜在行在库中不存在：

 * 不存在依赖对，其中第一个投影是命题，因为 {tech (key := "proof irrelevance")}[证明无关性] 使这变得毫无意义。

 * 不存在将类型与命题组合在一起的非依赖对，因为这种情况在实践中很少见：将数据与_不相关_证明进行分组并不常见。
:::

这些差异导致了非常不同的用例。
{name}`Prod` 及其变体 {name}`PProd` 和 {name}`MProd` 只是将数据组合在一起 - 它们是产品。
因为它的第二个投影是相关的，所以 {name}`Sigma` 具有求和的特征：对于第一个投影类型的每个元素，第二个投影中可能有不同的类型。
{name}`Subtype` 选择满足谓词的类型的值。
尽管它在语法上类似于一对，但实际上它被视为实际的子集。
{name}`And` 是逻辑连接词，{name}`Exists` 是量词。
本章记录了类似元组的对，即 {name}`Prod` 和 {name}`Sigma`。

# 有序对
%%%
file := "Ordered-Pairs"
tag := "pairs"
%%%

```lean -show
section
variable {α : Type u} {β : Type v} {γ : Type w} {x : α} {y : β} {z : γ}
```

类型 {lean}`α × β` 是 {lean}`Prod α β` 的 {tech (key := "notation")}[符号]，包含有序对，其中第一项是 {lean}`α`，第二项是 {lean}`β`。
这些对写在括号中，并用逗号分隔。
较大的元组表示为嵌套元组，因此 {lean}`α × β × γ` 相当于 {lean}`α × (β × γ)`，{lean}`(x, y, z)` 相当于 {lean}`(x, (y, z))`。

:::syntax term (title := "Product Types")
```grammar
$_ × $_
```
产品 {lean}`Prod α β` 写作 {lean}`α × β`。
:::

:::syntax term (title := "Pairs")
```grammar
($_, $_)
```
:::

{docstring Prod}

```lean -show
section
variable {α : Sort u} {β : Sort v} {γ : Type w}
```

还有 {lean}`α ×' β`（{lean}`PProd α β` 的表示法）和 {lean}`MProd` 的变体，它们在 {tech}[universe] 级别方面有所不同：与 {name}`PSum` 一样，{name}`PProd` 允许 {lean}`α` 或{lean}`β` 是一个命题，而 {lean}`MProd` 要求两者的类型相同 宇宙层级。
一般来说，{name}`PProd`主要用于证明自动化和精化器的实现，因为它容易产生无法解决的宇宙层级统一问题。
另一方面，{lean}`MProd` 可以简化某些高级用例中的 宇宙层级 问题。

```lean -show
end
```

:::syntax term (title := "Products of Arbitrary Sorts")
```grammar
$_ ×' $_
```
乘积 {lean}`PProd α β`（其中两种类型都可以是命题）写作 {lean}`α × β`。
:::


{docstring PProd}

{docstring MProd}

## API 参考
%%%
file := "API-Reference"
tag := "prod-api"
%%%

仅作为一对，{lean}`Prod` 的主 API 由模式匹配以及第一和第二投影 {name}`Prod.fst` 和 {name}`Prod.snd` 提供。

### 转型
%%%
file := "Transformation"
tag := "zh-basictypes-products-h003"
%%%

{docstring Prod.map}

{docstring Prod.swap}

### 自然数范围
%%%
file := "Natural-Number-Ranges"
tag := "zh-basictypes-products-h004"
%%%

{docstring Prod.allI}

{docstring Prod.anyI}

{docstring Prod.foldI}

### 订购
%%%
file := "Ordering"
tag := "zh-basictypes-products-h005"
%%%

{docstring Prod.lexLt}


# 依赖对
%%%
file := "Dependent-Pairs"
tag := "sigma-types"
%%%


{deftech (key := "Dependent pairs")}_Dependentpairs_，也称为 {deftech}_dependent sums_ 或 {deftech}_Σ-types_，{see "Σ-types"}[Sigma types]{index}[Σ-types] 是其中第二项的类型可能取决于第一项的_value_的对。
它们与存在量词 {TODO}[xref] 和 {name}`Subtype` 密切相关。
与存在量化的陈述不同，依赖对位于 {lean}`Type` 宇宙中，并且是计算相关的数据。
与子类型不同，第二项也是计算相关的数据。
与普通对一样，依赖对可以嵌套；这种嵌套是右结合的。

:::syntax term (title := "Dependent Pair Types")

```grammar
($x:ident : $t) × $t
```

```grammar
Σ $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
Σ ($x:ident $[$x:ident]* : $t), $_
```

依赖对类型绑定一个或多个变量，这些变量位于最后一项的范围内。
如果有一个变量，那么它的类型是对中第一个元素的类型，最后一项是对中第二个元素的类型。
如果有多个变量，则类型以右关联方式嵌套。
标识符也可以是`_`。
使用括号时，多个绑定变量可以具有不同的类型，而不带括号的变量则要求所有变量具有相同的类型。
:::

::::example "Nested Dependent Pair Types"

:::paragraph
类型
```leanTerm
Σ n k : Nat, Fin (n * k)
```
相当于
```leanTerm
Σ n : Nat, Σ k : Nat, Fin (n * k)
```
和
```leanTerm
(n : Nat) × (k : Nat) × Fin (n * k)
```
:::

:::paragraph
类型
```leanTerm
Σ (n k : Nat) (i : Fin (n * k)) , Fin i.val
```
相当于
```leanTerm
Σ (n : Nat), Σ (k : Nat), Σ (i : Fin (n * k)) , Fin i.val
```
和
```leanTerm
(n : Nat) × (k : Nat) × (i : Fin (n * k)) × Fin i.val
```
:::

两种注释样式不能在单个 {keywordOf «termΣ_,_»}`Σ` 类型中混合：
```syntaxError mixedNesting (category := term)
Σ n k (i : Fin (n * k)) , Fin i.val
```
```leanOutput mixedNesting
<example>:1:5-1:7: unexpected token '('; expected ','
```
::::

```lean -show
section
variable {α : Type} (x : α)
```
::::paragraph
依赖对通常以以下两种方式之一使用：

 1. 它们可用于将具体类型索引与索引族的值“打包”在一起，在事先未知索引值时使用。
    {lean}`Σ n, Fin n` 类型是一对自然数和一些其他严格较小的数字。
    这是使用依赖对的最常见方法。

 2. :::paragraph
    第一个元素可以被认为是一个“标签”，用于从第二个术语的不同类型中进行选择。
    这类似于选择和类型的构造函数确定构造函数参数的类型的方式。
    例如，类型

    ```leanTerm
    Σ (b : Bool), if b then Unit else α
    ```

    相当于 {lean}`Option α`，其中 {lean  (type := "Option α")}`none` 是 {lean  (type := "Σ (b : Bool), if b then Unit else α")}`⟨true, ()⟩`，{lean  (type := "Option α")}`some x` 是 {lean  (type := "Σ (b : Bool), if b then Unit else α")}`⟨false, x⟩`。
    以这种方式使用依赖对并不常见，因为直接定义特殊用途的 {tech (key := "inductive type")}[归纳类型] 通常要容易得多。
    :::
::::

```lean -show
end
```

{docstring Sigma}

:::::example "Dependent Pairs with Data"

::::ioExample
将已知长度与数组关联的类型 {name}`Vector` 可以与长度本身放置在从属对中。
虽然这在逻辑上相当于仅使用 {name}`Array`，但有时需要这种结构来弥补 API 中的间隙。

```ioLean
def getNLinesRev : (n : Nat) → IO (Vector String n)
  | 0 => pure #v[]
  | n + 1 => do
    let xs ← getNLinesRev n
    return xs.push (← (← IO.getStdin).getLine)

def getNLines (n : Nat) : IO (Vector String n) := do
  return (← getNLinesRev n).reverse

partial def getValues : IO (Σ n, Vector String n) := do
  let stdin ← IO.getStdin

  IO.println "How many lines to read?"
  let howMany ← stdin.getLine

  if let some howMany := howMany.trimAscii.copy.toNat? then
    return ⟨howMany, (← getNLines howMany)⟩
  else
    IO.eprintln "Please enter a number."
    getValues

def main : IO Unit := do
  let values ← getValues
  IO.println s!"Got {values.fst} values. They are:"
  for x in values.snd do
    IO.println x.trimAscii
```
:::paragraph
当用这个标准输入调用程序时：
```stdin
4
Apples
Quince
Plums
Raspberries
```
输出是：
```stdout
How many lines to read?
Got 4 values. They are:
Raspberries
Plums
Quince
Apples
```
:::
::::

:::::

:::example "Dependent Pairs as Sums"
{name}`Sigma` 可用于实现求和类型。
{name}`Sum'` 第一个投影中的 {name}`Bool` 指示第二个投影是从哪种类型绘制的。
```lean
def Sum' (α : Type) (β : Type) : Type :=
  Σ (b : Bool),
    match b with
    | true => α
    | false => β
```

注入将标签 ({name}`Bool`) 与指定类型的值配对。
使用 {attr}`match_pattern` 对它们进行注释允许它们在模式中以及在普通术语中使用。
```lean
variable {α β : Type}

@[match_pattern]
def Sum'.inl (x : α) : Sum' α β := ⟨true, x⟩

@[match_pattern]
def Sum'.inr (x : β) : Sum' α β := ⟨false, x⟩

def Sum'.swap : Sum' α β → Sum' β α
  | .inl x => .inr x
  | .inr y => .inl y
```
:::


正如 {name}`Prod` 具有接受命题和类型的变体 {name}`PProd` 一样，{name}`PSigma` 允许其投影成为命题。
这与 {name}`PProd` 具有相同的缺点：它更有可能导致 宇宙层级 统一失败。
然而，在实现自定义证明自动化或在一些罕见的高级用例中，{name}`PSigma` 可能是必要的。

:::syntax term (title := "Fully-Polymorphic Dependent Pair Types")

```grammar
Σ' $x:ident $[$_:ident]* $[: $t]? , $_
```

```grammar
Σ' ($x:ident $[$x:ident]* : $t), $_
```

嵌套 {keyword}`Σ'` 的规则以及管理其绑定结构的规则与 {keywordOf «termΣ_,_»}`Σ` 的规则相同。
:::

{docstring PSigma}
