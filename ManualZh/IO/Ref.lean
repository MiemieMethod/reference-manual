/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "可变引用" =>
%%%
file := "Mutable-References"
tag := "zh-io-ref-root"
%%%


虽然普通的 {tech (key := "state monads")}[状态单子] 使用跟踪状态内容以及计算值的元组对有状态计算进行编码，但 Lean 的运行时系统还提供始终由可变内存单元支持的可变引用。
可变引用的类型为 {lean}`IO.Ref`，指示单元格是可变的，并且读取和写入必须是显式的。
{lean}`IO.Ref` 是使用 {lean}`ST.Ref` 实现的，因此整个 {ref "mutable-st-references"}[{lean}`ST.Ref` API] 也可以与 {lean}`IO.Ref` 一起使用。

{docstring IO.Ref}

{docstring IO.mkRef}



# 状态转换器
%%%
file := "State-Transformers"
tag := "mutable-st-references"
%%%


可变引用通常在不希望出现任意副作用的情况下很有用。
当 Lean 无法将纯操作优化为突变时，它们可以显着加速，并且某些算法使用可变引用比状态单子更容易表达。
此外，它还有一个其他副作用所没有的属性：如果一段代码使用的所有可变引用都是在其执行期间创建的，并且该代码中没有可变引用逃逸到其他代码，则评估结果是确定性的。

{lean}`ST` monad 是 {lean}`IO` 的受限版本，其中可变状态是唯一的副作用，并且可变引用无法转义。{margin}[{lean}`ST` 首先由 {citehere launchbury94}[] 描述。]
{lean}`ST` 采用从未用于对任何术语进行分类的类型参数。
{lean}`runST` 函数允许从 {lean}`ST` 转义，要求传递给它的 {lean}`ST` 操作可以使用 _any_ 类型实例化此类型参数。
这种未知类型除了作为函数的参数外不存在，这意味着由它“标记”类型的值无法逃脱其作用域。

{docstring ST}

{docstring runST}

与 {lean}`IO` 和 {lean}`EIO` 一样，{lean}`ST` 也有一个变体，它采用自定义错误类型作为参数。
这里，{lean}`ST` 类似于 {lean}`BaseIO` 而不是 {lean}`IO`，因为 {lean}`ST` 不会导致抛出错误。

{docstring EST}

{docstring runEST}

{docstring ST.Ref +hideFields}

{docstring ST.mkRef}

## 阅读和写作
%%%
file := "Reading-and-Writing"
tag := "zh-io-ref-h002"
%%%

{docstring ST.Ref.get}

{docstring ST.Ref.set}

::::example "Data races with {name ST.Ref.get}`get` and {name ST.Ref.set}`set`"
:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      if cost < (← balance.get) then
        IO.sleep (← IO.rand 10 100).toUInt32
        balance.set ((← balance.get) - cost)
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance is negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
```
```stderr
Final balance is negative!
```
:::
::::

{docstring ST.Ref.modify}

::::example "Avoiding data races with {name ST.Ref.modify}`modify`"

该程序启动 100 个线程。
每个线程模拟一次购买尝试：它生成一个随机价格，如果帐户余额足够，则将其减少该价格。
余额检查和新值的计算发生在对 {name}`ST.Ref.modify` 的原子调用中。

:::ioExample
```ioLean
def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)

  let mut orders := #[]
  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      balance.modify fun b =>
        if cost < b then
          b - cost
        else b
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```
```stdout
Sending out orders...
Final balance is zero or positive.
```
```stderr
```
:::
::::

{docstring ST.Ref.modifyGet}

{docstring ST.Ref.swap}

## 比较
%%%
file := "Comparisons"
tag := "zh-io-ref-h003"
%%%

{docstring ST.Ref.ptrEq}

## `ST` 支持的状态 Monad
%%%
file := "___ST___-Backed-State-Monads"
tag := "zh-io-ref-h004"
%%%

{docstring ST.Ref.toMonadStateOf}

# 并发性
%%%
file := "Concurrency"
tag := "ref-locks"
%%%

可变引用可以用作锁定机制。
_获取_引用的内容会导致获取它或从中读取内容的尝试被阻止，直到它再次成为 {name ST.Ref.set}`set`。
这是一个低级功能，可用于实现其他同步机制；如果可能的话，通常最好依赖更高级别的抽象。

{docstring ST.Ref.take}


::::example "Reference Cells as Locks"
该程序启动 100 个线程。
每个线程模拟一次购买尝试：它生成一个随机价格，如果帐户余额足够，则将其减少该价格。
如果余额不足，则不会减少。
因为每个线程 {name ST.Ref.take}`take` 在检查平衡单元之前都会对其进行操作，并且仅在完成时才将其返回，因此单元充当锁的作用。
与使用 {name}`ST.Ref.modify`（使用纯函数以原子方式修改单元格的内容）不同，其他 {name}`IO` 操作可能发生在临界区中
该程序的`main`函数被标记为{keywordOf Lean.Parser.Command.declaration}`unsafe`，因为{name ST.Ref.take}`take`本身是不安全的。

:::ioExample
```ioLean
unsafe def main : IO Unit := do
  let balance ← IO.mkRef (100 : Int)
  let validationUsed ← IO.mkRef false

  let mut orders := #[]

  IO.println "Sending out orders..."
  for _ in [0:100] do
    let o ← IO.asTask (prio := .dedicated) do
      let cost ← IO.rand 1 100
      IO.sleep (← IO.rand 10 100).toUInt32
      let b ← balance.take
      if cost ≤ b then
        balance.set (b - cost)
      else
        balance.set b
        validationUsed.set true
    orders := orders.push o

  -- Wait until all orders are completed
  for o in orders do
    match o.get with
    | .ok () => pure ()
    | .error e => throw e

  if (← validationUsed.get) then
    IO.println "Validation prevented a negative balance."

  if (← balance.get) < 0 then
    IO.eprintln "Final balance negative!"
  else
    IO.println "Final balance is zero or positive."
```

该程序的输出是：
```stdout
Sending out orders...
Validation prevented a negative balance.
Final balance is zero or positive.
```
:::
::::
