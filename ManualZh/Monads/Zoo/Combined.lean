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

#doc (Manual) "组合错误和状态 Monad" =>
%%%
tag := "zh-monads-zoo-combined-root"
%%%

```lean -show
variable (ε : Type u) (σ σ' : Type u) (α : Type u)
```

{name}`EStateM` monad 具有异常和可变状态。
{lean}`EStateM ε σ α` 在逻辑上等同于 {lean}`ExceptT ε (StateM σ) α`。
{lean}`ExceptT ε (StateM σ)` 计算结果为 {lean}`σ → Except ε α × σ` 类型，而 {lean}`EStateM ε σ α` 计算结果为 {lean}`σ → EStateM.Result ε σ α`。
{name}`EStateM.Result` 是一个归纳类型，它与 {name}`Except` 非常相似，只是两个构造函数都有一个附加的状态字段。
在编译的代码中，这种表示形式从每个单子绑定中删除了一层间接。

```lean -show
/-- info: σ → Except ε α × σ -/
#check_msgs in
#reduce (types := true) ExceptT ε (StateM σ) α

/-- info: σ → EStateM.Result ε σ α -/
#check_msgs in
#reduce (types := true) EStateM ε σ α
```

{docstring EStateM}

{docstring EStateM.Result}

{docstring EStateM.run}

{docstring EStateM.run'}

{docstring EStateM.adaptExcept}

{docstring EStateM.fromStateM +allowMissing}

# 状态回滚
%%%
tag := "zh-monads-zoo-combined-h001"
%%%

以不同顺序组合 {name}`StateT` 和 {name}`ExceptT` 会导致异常与状态的交互方式不同。
在一种顺序中，当捕获异常时，状态更改会回滚；另一方面，他们坚持不懈。
后一个选项与大多数命令式编程语言的语义相匹配，但前者对于基于搜索的问题非常有用。
通常，一些但不是全部状态应该回滚；这可以通过将 {name}`ExceptT`“夹在”{name}`StateT` 的两个单独用途之间来实现。

为了避免通过使用 {lean}`StateT σ (EStateM ε σ') α` 产生另一层间接，{name}`EStateM` 提供了 {name}`EStateM.Backtrackable` {tech (key := "type class")}[类型类别]。
此类指定可以保存和恢复的状态的某些部分。
然后，{name}`EStateM` 安排围绕错误处理进行保存和恢复。

{docstring EStateM.Backtrackable}

有一个普遍适用的 {name EStateM.Backtrackable}`Backtrackable` 实例，既不保存也不恢复任何内容。
由于实例合成首先选择最近的实例，因此只有在没有定义其他实例的情况下才会使用通用实例。

{docstring EStateM.nonBacktrackable}

# 实施
%%%
tag := "zh-monads-zoo-combined-h002"
%%%

这些函数通常不直接调用，而是通过其相应的类型类访问。

{docstring EStateM.map}

{docstring EStateM.pure}

{docstring EStateM.bind}

{docstring EStateM.orElse}

{docstring EStateM.orElse'}

{docstring EStateM.seqRight}

{docstring EStateM.tryCatch}

{docstring EStateM.throw}

{docstring EStateM.get}

{docstring EStateM.set}

{docstring EStateM.modifyGet}
