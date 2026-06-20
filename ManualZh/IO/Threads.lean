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

#doc (Manual) "任务和线程" =>
%%%
tag := "concurrency"
%%%

:::leanSection
```lean -show
variable {α : Type u}
```

{deftech}_Tasks_ 是编写多线程代码的基本原语。
{lean}`Task α` 表示在某个时刻将 {tech (key := "resolve promise")}_resolve_ 转换为 `α` 类型的值的计算；它可以在单独的线程上计算。
当任务解决后，可以读取其值；尝试在任务解决之前获取任务的值会导致当前线程阻塞，直到任务解决为止。
任务类似于 JavaScript、Rust 中的 `JoinHandle` 和 Scala 中的 `Future` 中的 Promise。

任务可以执行纯计算或 {name}`IO` 操作。
纯任务的 API 类似于 {tech}[thunks]：{name}`Task.spawn` 从 {lean}`Unit → α` 中的函数创建 {lean}`Task α`，{name}`Task.get` 等待直到计算出函数的值，然后返回它。
该值被缓存，因此后续请求不需要重新计算它。
关键区别在于计算发生的时间：虽然 thunk 的值在强制执行之前不会被计算，但任务会在单独的线程中伺机执行。

{name}`IO` 中的任务是使用 {name}`IO.asTask` 创建的。
类似地，{name}`BaseIO.asTask` 和 {name}`EIO.asTask` 在其他 {name}`IO` monad 中创建任务。
这些任务可能有副作用，并且可以与其他任务进行通信。
:::

当对任务的最后一个引用被删除时，它是 {deftech (key := "cancel")}_cancelled_。
使用 {name}`Task.spawn` 创建的纯任务将在取消时终止。
使用 {name}`IO.asTask`、{name}`EIO.asTask` 或 {name}`BaseIO.asTask` 生成的任务继续执行，并且必须使用 {name}`IO.checkCanceled` 显式检查取消。
可以使用 {name}`IO.cancel` 显式取消任务。

Lean 运行时维护一个用于运行任务的线程池。
线程池的大小由环境变量 {envVar +def}`LEAN_NUM_THREADS`（如果已设置）确定，否则由当前计算机上逻辑处理器的数量确定。
线程池的大小不是硬性限制；在某些情况下，可能会超出它以避免死锁。
默认情况下，这些线程用于运行任务；每个任务都有一个 {deftech (key := "task priority")}_priority_ ({name}`Task.Priority`)，高优先级任务优先于低优先级任务。
还可以通过以足够高的优先级生成任务来将任务分配给专用线程。

{docstring Task (label := "type") +hideStructureConstructor +hideFields}

# 创建任务
%%%
tag := "zh-io-threads-h001"
%%%

纯任务通常应使用 {name}`Task.spawn` 创建，因为 {name}`Task.pure` 是已使用提供的值解析的任务。
不纯任务由 {name BaseIO.asTask}`asTask` 操作之一创建。

## 纯任务
%%%
tag := "zh-io-threads-h002"
%%%

纯任务可以在 {name}`IO` monad 系列之外创建。
当对它们的最后一个引用被删除时，它们就会终止。

{docstring Task.spawn}

{docstring Task.pure}

## 不纯的任务
%%%
tag := "zh-io-threads-h003"
%%%

使用 {name IO.asTask}`asTask` 函数之一生成具有副作用的任务时，实际执行生成的 {name}`IO` 操作非常重要。
每次执行结果操作时都会生成一个任务，而不是在调用 {name IO.asTask}`asTask` 时生成。
即使没有对不纯任务的引用，不纯任务也会继续运行，但这确实会导致请求取消。
也可以使用 {name}`IO.cancel` 明确请求取消。
非纯任务必须使用 {name}`IO.checkCanceled` 检查是否取消。

{docstring BaseIO.asTask}

{docstring EIO.asTask}

{docstring IO.asTask}

## 优先事项
%%%
tag := "zh-io-threads-h004"
%%%

线程调度程序使用任务优先级将任务分配给线程。
在优先级范围 {name Task.Priority.default}`default`–{name Task.Priority.max}`max` 内，高优先级任务始终优先于低优先级任务。
以优先级 {name Task.Priority.dedicated}`dedicated` 生成的任务会被分配自己的专用线程，并且不会与线程池中的线程的其他任务竞争。

{docstring Task.Priority}

{docstring Task.Priority.default}

{docstring Task.Priority.max}

{docstring Task.Priority.dedicated}

# 任务结果
%%%
tag := "zh-io-threads-h005"
%%%

{docstring Task.get}

{docstring IO.wait}

{docstring IO.waitAny}

# 排序任务
%%%
tag := "zh-io-threads-h006"
%%%

这些操作员从旧任务创建新任务。
如果可能，最好使用 {name}`Task.map` 或 {name}`Task.bind`，而不是在新任务中手动调用 {name}`Task.get`，因为它们不会暂时增加线程池的大小。

{docstring Task.map}

{docstring Task.bind}

{docstring Task.mapList}

{docstring BaseIO.mapTask}

{docstring EIO.mapTask}

{docstring IO.mapTask}

{docstring BaseIO.mapTasks}

{docstring EIO.mapTasks}

{docstring IO.mapTasks}

{docstring BaseIO.bindTask}

{docstring EIO.bindTask}

{docstring IO.bindTask}

{docstring BaseIO.chainTask}

{docstring EIO.chainTask}

{docstring IO.chainTask}

# 取消和状态
%%%
tag := "zh-io-threads-h007"
%%%

不纯任务应使用 `IO.checkCanceled` 对取消做出反应，取消是由于 `IO.cancel` 的结果或在删除对任务的最后一个引用时发生的。
纯任务在取消时会自动终止。

{docstring IO.cancel}

{docstring IO.checkCanceled}

{docstring IO.hasFinished}

{docstring IO.getTaskState}

{docstring IO.TaskState}

{docstring IO.getTID}

# 承诺
%%%
tag := "zh-io-threads-h008"
%%%

承诺代表未来将提供的价值。
提供该值称为 {deftech (key := "resolve promise")}_resolving_ 承诺。
一旦创建，promise 就可以存储在数据结构中或像任何其他值一样传递，并且尝试读取它会阻塞，直到它被解析。


{docstring IO.Promise}

{docstring IO.Promise.new}

{docstring IO.Promise.isResolved}

{docstring IO.Promise.result?}

{docstring IO.Promise.result!}

{docstring IO.Promise.resultD}

{docstring IO.Promise.resolve}

# 任务之间的通信
%%%
tag := "zh-io-threads-h009"
%%%

除了本节中描述的类型和操作之外，{name}`IO.Ref` 还可以用作锁。
获取引用（使用 {name ST.Ref.take}`take`）会导致其他线程在读取时阻塞，直到引用再次变为 {name ST.Ref.set}`set`。
{ref "ref-locks"}[有关参考单元的部分] 中描述了此模式。

## 渠道
%%%
tag := "zh-io-threads-h010"
%%%

本节中的类型和功能在导入{module}`Std.Sync.Channel`后可用。

{docstring Std.Channel}

{docstring Std.Channel.new}

{docstring Std.Channel.send}

{docstring Std.Channel.recv}


{docstring Std.Channel.forAsync}


{docstring Std.Channel.sync}

{docstring Std.Channel.Sync}


{docstring Std.CloseableChannel}

{docstring Std.CloseableChannel.new}





:::leanSection
```lean -show
variable {m : Type → Type v} {α : Type} [MonadLiftT BaseIO m] [Inhabited α] [Monad m]
```
还可以使用 {keywordOf Lean.Parser.Term.doFor}`for` 循环读取同步通道。
特别是，每个单子 {lean}`m` 和 {inst}`MonadLiftT BaseIO m` 实例以及 {lean}`α` 和 {inst}`Inhabited α` 实例都有一个类型为 {inst}`ForIn m (Std.Channel.Sync α) α` 的实例。
:::
## 互斥体
%%%
tag := "zh-io-threads-h011"
%%%

本节中的类型和功能在导入{module}`Std.Sync.Mutex`后可用。

{docstring Std.Mutex (label := "type") +hideStructureConstructor +hideFields}

{docstring Std.Mutex.new}

{docstring Std.Mutex.atomically}

{docstring Std.Mutex.atomicallyOnce}

{docstring Std.AtomicT}


## 条件变量
%%%
tag := "zh-io-threads-h012"
%%%

本节中的类型和功能在导入{module}`Std.Sync.Mutex`后可用。

{docstring Std.Condvar}

{docstring Std.Condvar.new}

{docstring Std.Condvar.wait}

{docstring Std.Condvar.notifyOne}

{docstring Std.Condvar.notifyAll}

{docstring Std.Condvar.waitUntil}
