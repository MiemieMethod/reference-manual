/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inductiveParamMismatch`" =>
%%%
shortTitle := "inductiveParamMismatch"
%%%

{errorExplanationHeader lean.inductiveParamMismatch}

当归纳类型的参数在电感中不统一时，会出现此错误
声明。归纳类型的参数（即出现在冒号后面的参数）
{keyword}`inductive` 关键字）在所有出现的定义类型中必须相同
它的构造函数的类型。如果归纳类型的参数必须在构造函数之间变化，则使
通过将参数移动到冒号右侧来将其作为索引。请参阅手册部分
{ref "inductive-types"}[归纳类型] 了解更多详细信息。

请注意，自动隐式嵌入提示始终出现在归纳声明中冒号的左侧
（即作为参数），即使它们实际上是索引。这意味着双击
插入此类参数的嵌入提示可能会导致此错误。如果是这样，请更改插入的
参数到索引。

# 示例
%%%
tag := "zh-errorexplanations-inductiveparammismatch-h001"
%%%

:::errorExample "Vector Length Index as a Parameter"
```broken
inductive Vec (α : Type) (n : Nat) : Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```
```output
Mismatched inductive type parameter in
  Vec α 0
The provided argument
  0
is not definitionally equal to the expected parameter
  n

Note: The value of parameter `n` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```
```fixed
inductive Vec (α : Type) : Nat → Type where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)
```

`Vec`类型构造函数的长度参数`n`被声明为参数，但其他值
此参数出现在 `nil` 和 `cons` 构造函数（即 `0` 和 `n + 1`）中。一个错误
因此出现在此类论证第一次出现时。要纠正此问题，`n` 不能是
归纳声明的参数，并且必须是索引，如更正的示例中所示。开
另一方面，`α` 在声明中所有出现的 `Vec` 中保持不变，因此
是一个有效的参数。
:::
