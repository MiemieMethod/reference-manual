/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`invalidField`" =>
%%%
shortTitle := "invalidField"
%%%

{errorExplanationHeader lean.invalidField}

此错误表明遇到了包含点后跟标识符的表达式，
并且不可能将标识符理解为一个字段。

Lean 的字段表示法非常强大，但这也会使其变得混乱：表达式
`color.value` 可以是单个 {ref "identifiers-and-resolution"}[标识符]。
它可以是对 {ref "structure-fields"}[结构体字段]的引用，并且它
并且是对值 `color` 调用函数
{ref "generalized-field-notation"}[通用字段表示法]。

# 示例

:::errorExample "Incorrect Field Name"

```broken
#eval (4 + 2).suc
```
```output
Invalid field `suc`: The environment does not contain `Nat.suc`, so it is not possible to project the field `suc` from an expression
  4 + 2
of type `Nat`
```
```fixed
#eval (4 + 1).succ
```

无效字段错误的最简单原因是正在寻找的函数，例如 `Nat.suc`，
不存在。
:::

:::errorExample "Projecting from the Wrong Expression"
```broken
#eval '>'.leftpad 10 ['a', 'b', 'c']
```
```output
Invalid field `leftpad`: The environment does not contain `Char.leftpad`, so it is not possible to project the field `leftpad` from an expression
  '>'
of type `Char`
```
```fixed
#eval ['a', 'b', 'c'].leftpad 10 '>'
```

点之前表达式的类型完全决定了该字段调用的函数
投影。不存在 `Char.leftpad`，并且使用通用调用 `List.leftpad` 的唯一方法
字段表示法是将列表放在点之前。
:::

:::errorExample "Type is Not Specific"
```broken
def double_plus_one {α} [Add α] (x : α) :=
   (x + x).succ
```
```output
Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  x + x
has type `α` which does not have the necessary form.
```
```fixed
def double_plus_one (x : Nat) :=
   (x + x).succ
```

`Add` 类型类足以执行加法 `x + x`，但 `.succ` 字段表示法
如果不了解更多有关 `succ` 所投影的实际类型的信息，则无法进行操作。
:::

:::errorExample "Insufficient Type Information"

```broken
example := fun (n) => n.succ.succ
```
```output
Invalid field notation: Type of
  n
is not known; cannot resolve field `succ`

Hint: Consider replacing the field projection with a call to one of the following:
  • `Fin.succ`
  • `Nat.succ`
  • `Lean.Level.succ`
  • `Std.PRange.succ`
  • `Lean.Level.PP.Result.succ`
  • `Std.Time.Internal.Bounded.LE.succ`
```
```fixed
example := fun (n : Nat) => n.succ.succ
```

仅当可以确定正在使用的类型时才能使用通用字段表示法
预计。可能需要添加 Type 注释才能使通用字段表示法起作用。
:::
