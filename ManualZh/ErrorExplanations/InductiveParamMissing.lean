/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`inductiveParamMissing`" =>
%%%
shortTitle := "inductiveParamMissing"
%%%

{errorExplanationHeader lean.inductiveParamMissing}

当归纳类型构造函数部分应用于其其中之一的类型时，会发生此错误
构造函数，以便省略该类型的一个或多个参数。精化器要求
归纳类型的所有参数都应在其引用类型的任何地方指定
定义，包括其构造函数的类型。

如果需要允许部分应用类型构造函数，而不指定给定的
类型参数，该参数必须转换为索引。请参阅手册部分
{ref "inductive-types"}[归纳类型] 进一步解释指数之间的差异
和参数。

# 示例
%%%
tag := "zh-errorexplanations-inductiveparammissing-h001"
%%%

:::errorExample "Omitting Parameter in Argument to Higher-Order Predicate"
```broken
inductive List.All {α : Type u} (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

structure RoseTree (α : Type u) where
  val : α
  children : List (RoseTree α)

inductive RoseTree.All (P : α → Prop) (t : RoseTree α) : Prop
  | intro : P t.val → List.All (All P) t.children → All P t
```

```output
Missing parameter(s) in occurrence of inductive type: In the expression
  List.All (All P) t.children
found
  All P
but expected all parameters to be specified:
  All P t

Note: All occurrences of an inductive type in the types of its constructors must specify its fixed parameters. Only indices can be omitted in a partial application of the type constructor.
```

```fixed
inductive List.All {α : Type u} (P : α → Prop) : List α → Prop
  | nil : All P []
  | cons {x xs} : P x → All P xs → All P (x :: xs)

structure RoseTree (α : Type u) where
  val : α
  children : List (RoseTree α)

inductive RoseTree.All (P : α → Prop) : RoseTree α → Prop
  | intro : P t.val → List.All (All P) t.children → All P t
```

因为 `RoseTree.All` 类型构造函数必须部分应用于 `List.All` 的参数中，
未指定的参数 (`t`) 不得是 `RoseTree.All` 谓词的参数。使其成为
`RoseTree.All` 标题中冒号右侧的索引允许此部分应用程序
成功。
:::
