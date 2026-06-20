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

#doc (Manual) "提升单子" =>
%%%
tag := "lifting-monads"
%%%

::::keepEnv

```lean -show
variable {m m' n : Type u → Type v} [Monad m] [Monad m'] [Monad n] [MonadLift m n]
variable {α β : Type u}
```

当一个 monad 至少与另一个 monad 一样有能力时，则后一个 monad 的操作可以在期望前一个 monad 操作的上下文中使用。
这称为 {deftech (key := "lift")}_lifting_ 从一个单子到另一个单子的动作。
Lean 在电梯可用时自动插入电梯；电梯在 {name}`MonadLift` 类型类别中定义。
在通用 {tech (key := "coercion")}[强制] 机制之前尝试自动 monad 提升。

{docstring MonadLift}

{tech (key := "lift")}[Lifting] 在单子之间是自反和及物的：
 * 任何 monad 都可以运行自己的操作。
 * 从 {lean}`m` 到 {lean}`m'` 以及从 {lean}`m'` 到 {lean}`n` 的提升可以组合起来产生从 {lean}`m` 到 {lean}`n` 的提升。
实用程序类型类 {name}`MonadLiftT` 通过 {name}`MonadLift` 实例的自反和传递闭包构造提升。
用户不应定义 {name}`MonadLiftT` 的新实例，但它可用作需要在某些用户提供的 monad 中从多个 monad 运行操作的多态函数的实例隐式参数。

{docstring MonadLiftT}

```lean -show
section
variable {m : Type → Type u}
```

:::example "Monad Lifts in Function Signatures"
函数 {name}`IO.withStdin` 具有以下签名：
```signature
IO.withStdin.{u} {m : Type → Type u} {α : Type}
  [Monad m] [MonadFinally m] [MonadLiftT BaseIO m]
  (h : IO.FS.Stream) (x : m α) :
  m α
```
因为它不要求其参数精确地位于 {name}`IO` 中，所以它可以在许多 monad 中使用，并且主体不需要将自身限制为 {name}`IO`。
实例隐式参数 {lean}`MonadLiftT BaseIO m` 允许使用 {name}`MonadLift` 的自反传递闭包来组装电梯。
:::

```lean -show
end
```


当需要 {lean}`n β` 类型的术语，但提供的术语具有 {lean}`m α` 类型，并且这两种类型在定义上不相等时，Lean 会在报告错误之前尝试插入提升和强制转换。
有以下几种可能：
 1. 如果{lean}`m`和{lean}`n`可以统一为同一个monad，那么{lean}`α`和{lean}`β`就不相同。
    在这种情况下，不需要 monad 提升，但 monad 中的值必须是 {tech (key := "coercion")}[强制]。
    如果找到适当的强制，则会插入对 {name}`Lean.Internal.coeM` 的调用，该调用具有以下签名：
    ```signature
    Lean.Internal.coeM.{u, v} {m : Type u → Type v} {α β : Type u}
      [(a : α) → CoeT α a β] [Monad m]
      (x : m α) :
      m β
    ```
 2. 如果 {lean}`α` 和 {lean}`β` 可以统一，则 monad 不同。
    在这种情况下，需要使用 monad lift 将类型为 {lean}`m α` 的表达式转换为 {lean}`n α`。
    如果 {lean}`m` 可以提升为 {lean}`n`（即，存在 {lean}`MonadLiftT m n` 的实例），则插入对 {name}`liftM`（{name}`MonadLiftT.monadLift` 的别名）的调用。
    ```signature
    liftM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      [self : MonadLiftT m n] {α : Type u} :
      m α → n α
    ```
 3. 如果 {lean}`m` 和 {lean}`n` 以及 {lean}`α` 和 {lean}`β` 都无法统一，但 {lean}`m` 可以提升为 {lean}`n`，并且 {lean}`α` 可以 {tech (key := "coercion")}[强制] 为{lean}`β`，则可以组合提升和强制。
    这是通过插入对 {name}`Lean.Internal.liftCoeM` 的调用来完成的：
    ```signature
    Lean.Internal.liftCoeM.{u, v, w}
      {m : Type u → Type v} {n : Type u → Type w}
      {α β : Type u}
      [MonadLiftT m n] [(a : α) → CoeT α a β] [Monad n]
      (x : m α) :
      n β
    ```

顾名思义，{name}`Lean.Internal.coeM` 和 {name}`Lean.Internal.liftCoeM` 是实现细节，而不是公共 API 的一部分。
在结果项中，{name}`Lean.Internal.coeM`、{name}`Lean.Internal.liftCoeM` 和强制的出现被展开。

::::

::::keepEnv
:::example "Lifting `IO` Monads"
有一个 {lean}`MonadLift BaseIO IO` 的实例，因此任何 `BaseIO` 操作也可以在 `IO` 中运行：
```lean
def fromBaseIO (act : BaseIO α) : IO α := act
```
在幕后插入 {name}`liftM`：
```lean (name := fromBase)
#check fun {α} (act : BaseIO α) => (act : IO α)
```
```leanOutput fromBase
fun {α} act => liftM act : {α : Type} → BaseIO α → EIO IO.Error α
```
:::
::::

:::::keepEnv
::::example "Lifting Transformed Monads"
大多数标准库的 {tech (key := "monad transformers")}[monad 转换器] 也有 {name}`MonadLift` 的实例，因此基本 monad 操作可以在转换后的 monad 中使用，无需额外工作。
例如，状态 monad 操作可以在读取器和异常转换器之间提升，从而允许兼容的 monad 自由混合：
```lean -keep
def incrBy (n : Nat) : StateM Nat Unit := modify (· + n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
```

禁用提升会导致错误：
```lean (name := noLift) +error
set_option autoLift false

def incrBy (n : Nat) : StateM Nat Unit := modify (. + n)

def incrOrFail : ReaderT Nat (ExceptT String (StateM Nat)) Unit := do
  if (← read) > 5 then throw "Too much!"
  incrBy (← read)
```
```leanOutput noLift
Type mismatch
  incrBy __do_lift✝
has type
  StateM Nat Unit
but is expected to have type
  ReaderT Nat (ExceptT String (StateM Nat)) Unit
```

::::
:::::


通过将 {option}`autoLift` 设置为 {lean}`false` 可以禁用自动提升。

{optionDocs autoLift}

# 倒车升降机
%%%
tag := "zh-monads-lift-h001"
%%%

```lean -show
variable {m n : Type u → Type v} {α ε : Type u}
```

Monad 提升并不总是足以组合 monad。
monad 提供的许多操作都是高阶的，在同一个 monad 中采取操作作为参数。
即使这些操作被提升到一些更强大的 monad，它们的参数仍然仅限于原始 monad。

有两个类型类支持这种“反向提升”：{name}`MonadFunctor` 和 {name}`MonadControl`。
{lean}`MonadFunctor m n` 的实例解释了如何将 {lean}`m` 中的完全多态函数解释为 {lean}`n`。
此多态函数必须适用于所有类型 {lean}`α`：它的类型为 {lean}`{α : Type u} → m α → n α`。
这样的函数可以被认为是一个可能有效果的函数，但不能根据提供的特定值来实现这一点。
{lean}`MonadControl m n` 的实例解释了如何将 {lean}`m` 的任意操作解释为 {lean}`n`，同时提供允许 {lean}`m` 操作运行 {lean}`n` 操作的“反向解释器”。

## 单子函子
%%%
tag := "zh-monads-lift-h002"
%%%

{docstring MonadFunctor}

{docstring MonadFunctorT}

## 使用 `MonadControl` 进行可逆提升
%%%
tag := "zh-monads-lift-h003"
%%%

{docstring MonadControl}

{docstring MonadControlT}

{docstring control}

{docstring controlAt}


::::keepEnv
:::example "Exceptions and Lifting"
{name}`Except.tryCatch` 就是一个示例：
```signature
Except.tryCatch.{u, v} {ε : Type u} {α : Type v}
  (ma : Except ε α) (handle : ε → Except ε α) :
  Except ε α
```
它的两个参数都在{lean}`Except ε`中。
{name}`MonadLift`可以解除处理程序的整个应用程序。
函数 {lean}`getBytes` 使用状态和异常从 {lean}`Nat` 数组中提取单个字节，编写时没有使用 {keywordOf Lean.Parser.Term.do}`do` 表示法或自动提升，以便使其结构明确。
```lean
set_option autoLift false

def getByte (n : Nat) : Except String UInt8 :=
  if n < 256 then
    pure n.toUInt8
  else throw s!"Out of range: {n}"

def getBytes (input : Array Nat) :
    StateT (Array UInt8) (Except String) Unit := do
  input.forM fun i =>
    liftM (Except.tryCatch (some <$> getByte i) fun _ => pure none) >>=
      fun
        | some b => modify (·.push b)
        | none => pure ()
```

```lean (name := getBytesEval1)
#eval getBytes #[1, 58, 255, 300, 2, 1000000] |>.run #[] |>.map (·.2)
```
```leanOutput getBytesEval1
Except.ok #[1, 58, 255, 2]
```
{name}`getBytes` 使用从提升操作返回的 `Option` 来发出所需状态更新的信号。
如果有不止一种方法对内部操作做出反应，例如保存已处理的异常，那么这很快就会变得难以处理。
理想情况下，状态更新将直接在 {name}`tryCatch` 调用中执行。


但是，尝试保存字节并处理异常不起作用，因为 {name}`Except.tryCatch` 的参数具有 {lean}`Except String Unit` 类型：
```lean +error (name := getBytesErr) -keep
def getBytes' (input : Array Nat) :
    StateT (Array String)
      (StateT (Array UInt8)
        (Except String)) Unit := do
  input.forM fun i =>
    liftM
      (Except.tryCatch
        (getByte i >>= fun b =>
         modifyThe (Array UInt8) (·.push b))
        fun e =>
          modifyThe (Array String) (·.push e))
```
```leanOutput getBytesErr
failed to synthesize instance of type class
  MonadStateOf (Array String) (Except String)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

由于 {name}`StateT` 具有 {name}`MonadControl` 实例，因此可以使用 {name}`control` 代替 {name}`liftM`。
它为内部动作提供了外部单子的解释器。
对于 {name}`StateT`，该解释器期望内部 monad 返回一个包含更新状态的元组，并负责提供初始状态并从元组中提取更新状态。

```lean
def getBytes' (input : Array Nat) :
    StateT (Array String)
      (StateT (Array UInt8)
        (Except String)) Unit := do
  input.forM fun i =>
    control fun run =>
      (Except.tryCatch
        (getByte i >>= fun b =>
         run (modifyThe (Array UInt8) (·.push b))))
        fun e =>
          run (modifyThe (Array String) (·.push e))
```

```lean (name := getBytesEval2)
#eval
  getBytes' #[1, 58, 255, 300, 2, 1000000]
  |>.run #[] |>.run #[]
  |>.map (fun (((), bytes), errs) => (bytes, errs))
```
```leanOutput getBytesEval2
Except.ok (#["Out of range: 300", "Out of range: 1000000"], #[1, 58, 255, 2])
```
:::
::::
