/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean Doc
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`ctorResultingTypeMismatch`" =>
%%%
shortTitle := "ctorResultingTypeMismatch"
%%%

{errorExplanationHeader lean.ctorResultingTypeMismatch}

在归纳声明中，每个构造函数的结果类型必须与正在的类型匹配
宣布；如果不存在，则会引发此错误。也就是说，归纳类型的每个构造函数都必须
返回该类型的值。请参阅 {ref "inductive-types"}[归纳类型] 手册部分了解
额外的细节。请注意，如果以下情况，可以省略构造函数的结果类型：
inductive type being defined has no indices.

# 示例

:::errorExample "Typo in Resulting Type"
```broken
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Treee α
```
```output
Unexpected resulting type for constructor `Tree.node`: Expected an application of
  Tree
but found
  ?m.2
```
```fixed
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α
```
:::

:::errorExample "Missing Resulting Type After Constructor Parameter"
```broken
inductive Credential where
  | pin      : Nat
  | password : String
```
```output
Unexpected resulting type for constructor `Credential.pin`: Expected
  Credential
but found
  Nat
```
```fixed "resulting type"
inductive Credential where
  | pin      : Nat → Credential
  | password : String → Credential
```
```fixed "named parameter"
inductive Credential where
  | pin (num : Nat)
  | password (str : String)
```

如果构造函数的类型被注释，则完整类型（包括结果类型）必须是
提供。或者，可以使用命名绑定器编写构造函数参数；这允许
省略构造函数的结果类型，因为它不包含索引。
:::
