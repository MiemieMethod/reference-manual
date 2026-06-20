/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

import ManualZh.IO.Console
import ManualZh.IO.Files
import ManualZh.IO.Threads
import ManualZh.IO.Ref

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "IO" =>
%%%
tag := "io"
%%%



Lean 是一种纯函数式编程语言。
虽然 Lean 代码在运行时严格求值，但类型检查期间（尤其是检查 {tech (key := "definitional equality")}[定义等价] 时）使用的求值顺序在形式上未指定，并且使用了许多启发式方法来提高性能，但可能会发生变化。
这意味着简单地添加执行副作用的操作（例如文件 I/O、异常或可变引用）将导致程序中的效果顺序未指定。
在类型检查期间，甚至带有自由变量的项也会被减少；这将使副作用更加难以预测。
最后，Lean 逻辑的基本原则是函数是将域的每个元素映射到范围的唯一元素的_函数_。
包括控制台 I/O、任意可变状态或随机数生成等副作用将违反此原则。

:::::keepEnv
```lean -show
/-- A type -/
axiom α : Type
```

可能有副作用的程序有一个类型（通常为 {lean}`IO α`）来将它们与纯函数区分开来。
从逻辑上讲，{lean}`IO`描述了副作用的排序和数据依赖性。
从 Lean 逻辑的角度来看，许多基本副作用（例如从文件中读取）都是不透明的常量。
其他的则由逻辑上与运行时版本等效的代码指定。
在运行时，编译器生成普通代码。

:::::

# 逻辑模型
%%%
tag := "zh-io-h001"
%%%

:::::keepEnv
```lean -show
/-- A type -/
axiom α : Type
```
从概念上讲，Lean 将项的评估或减少与副作用的执行区分开来。
期限缩减由 {tech}[β] 和 {tech}[δ] 等规则指定，这些规则可能随时随地发生。
Lean 的逻辑中抽象地描述了必须按正确顺序执行的副作用。
当程序运行时，Lean运行时系统负责实际执行所描述的效果。


{lean}`IO α` 类型是一个进程的描述，通过执行副作用，该进程应该返回 {lean}`α` 类型的值或引发错误。
它可以被认为是一个 {tech (key := "state monad")}[状态单子]，其中状态就是整个世界。
正如 {lean}`StateM Nat Bool` 类型的值计算 {lean}`Bool` 同时能够改变自然数一样，{lean}`IO Bool` 类型的值在计算 {lean}`Bool` 的同时可能会改变世界。
错误处理是通过在其之上分层适当的异常 monad 转换器来完成的。

:::::

由于整个世界无法在内存中表示，因此实际实现使用代表其状态的抽象标记。
Lean 运行时系统负责在程序运行时提供初始令牌，每个原始操作接受一个代表世界的令牌，并在完成时返回另一个令牌。
这确保了效果以正确的顺序发生，并且它清楚地将副作用的执行与 Lean 术语的约简语义分开。



通过一般递归实现的非终止与 {name}`IO` 描述的效果分开处理。
由于无限循环而无法终止的程序必须定义为 {ref "partial-unsafe"}[`partial`] 函数。
从逻辑角度来看，它们被视为任意常数；不需要 {name}`IO`。

{lean}`IO` 的一个非常重要的特性是值无法“逃逸”。
如果不使用几个明确标记的不安全运算符之一，程序就无法从 {lean}`IO Nat` 中提取纯 {lean}`Nat`。
这可以确保保留副作用的正确顺序，并确保具有副作用的程序被明确标记。

## `IO`、`EIO` 和 `BaseIO` Monad
%%%
tag := "io-monad"
%%%

有两个 monad 通常用于与现实世界交互的程序：

 * {lean}`IO` 中的操作可能会引发 {lean}`IO.Error` 类型的异常或修改世界。
 * {lean}`BaseIO` 中的操作不能引发异常，但它们可以修改世界。

这种区别使得可以通过查看操作的类型签名来判断是否可能出现异常。
{lean}`BaseIO` 操作会根据需要自动升级为 {lean}`IO`。

{docstring BaseIO}

{docstring IO}

{lean}`IO` 是 {lean}`EIO` 的一个实例，其中错误类型是一个参数。
特别地，{lean}`IO` 被定义为{lean}`EIO IO.Error`。
在某些情况下，例如绑定到非 Lean 库，可以方便地将 {lean}`EIO` 与自定义错误类型一起使用，这可确保在这些操作与其他 {lean}`IO` 操作之间的边界处处理错误。

```lean -show
-- Check claim in preceding paragraph
example : IO = EIO IO.Error := rfl
```

{docstring EIO}

{docstring IO.lazyPure}

{docstring BaseIO.toIO}

{docstring BaseIO.toEIO}

{docstring EIO.toBaseIO}

{docstring EIO.toIO}

{docstring EIO.toIO'}

{docstring IO.toEIO}

## `IO` 中的错误和错误处理
%%%
tag := "io-monad-errors"
%%%

{lean}`IO` monad 中的错误处理使用与任何其他 {tech (key := "exception monad")}[异常 monad] 相同的设施。
特别是，抛出和捕获异常使用 {name}`MonadExceptOf` {tech}[type class] 的方法。
{lean}`IO` 中引发的异常的类型为 {lean}`IO.Error`。
这种类型的构造函数代表大多数操作系统上发生的低级错误，例如文件不存在。
最常用的构造函数是 {name IO.Error.userError}`userError`，它涵盖所有其他情况并包含描述问题的字符串。

{docstring IO.Error}

{docstring IO.Error.toString}

{docstring IO.ofExcept}

{docstring EIO.catchExceptions}

{docstring IO.userError}

::::example "Throwing and Catching Errors"
:::ioExample
该程序反复要求输入密码，并使用控制流异常。
用于异常的语法在所有异常 monad 中都可用，而不仅仅是 {lean}`IO`。
当提供的密码不正确时，会引发异常，该异常会被重复密码检查的循环捕获。
正确的密码允许控制继续通过检查，终止循环，并重新抛出任何其他异常。

```ioLean
def accessControl : IO Unit := do
  IO.println "What is the password?"
  let password ← (← IO.getStdin).getLine
  if password.trimAscii.copy != "secret" then
    throw (.userError "Incorrect password")
  else return

def repeatAccessControl : IO Unit := do
  repeat
    try
      accessControl
      break
    catch
      | .userError "Incorrect password" =>
        continue
      | other =>
        throw other

def main : IO Unit := do
  repeatAccessControl
  IO.println "Access granted!"
```

使用此输入运行时：
```stdin
publicinfo
secondtry
secret
```

程序发出：
```stdout
What is the password?
What is the password?
What is the password?
Access granted!
```
:::
::::

# 控制结构
%%%
tag := "io-monad-control"
%%%

通常，用 {lean}`IO` 编写的程序使用 {ref "monads-and-do"}[与其他 monad 中编写的控制结构相同]。
有一个特定的 {lean}`IO` 帮助程序。

{docstring IO.iterate}

{include 0 ManualZh.IO.Console}

{include 0 ManualZh.IO.Ref}

{include 0 ManualZh.IO.Files}

# 系统和平台信息
%%%
tag := "platform-info"
%%%

{docstring System.Platform.numBits}

{docstring System.Platform.target}

{docstring System.Platform.isWindows}

{docstring System.Platform.isOSX}

{docstring System.Platform.isEmscripten}


# 环境变量
%%%
tag := "io-monad-getenv"
%%%

{docstring IO.getEnv}

# 定时
%%%
tag := "io-timing"
%%%

{docstring IO.sleep}

{docstring IO.monoNanosNow}

{docstring IO.monoMsNow}

{docstring IO.getNumHeartbeats}

{docstring IO.addHeartbeats}

# 流程
%%%
tag := "io-processes"
%%%

## 当前流程
%%%
tag := "zh-io-h009"
%%%

{docstring IO.Process.getCurrentDir}

{docstring IO.Process.setCurrentDir}

{docstring IO.Process.exit}

{docstring IO.Process.getPID}

## 正在运行的进程
%%%
tag := "zh-io-h010"
%%%

从 Lean 运行其他程序有三种主要方法：

 1. {lean}`IO.Process.run` 同步执行另一个程序，以字符串形式返回其 标准输出。如果进程退出时出现 `0` 以外的错误代码，则会引发错误。
 2. {lean}`IO.Process.output` 同步执行另一个具有空 标准输入 的程序，捕获其 标准输出、标准错误 和退出代码。如果进程终止失败，则不会引发任何错误。
 3. {lean}`IO.Process.spawn` 异步启动另一个程序并返回可用于访问进程的 标准输入、输出和错误流的数据结构。

{docstring IO.Process.run}

::::example "Running a Program"
运行时，该程序使用 Unix 工具 `cat` 将其自己的源代码与自身连接两次。

:::ioExample
```ioLean
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
```

其输出为：
```stdout
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
-- Main.lean begins here
def main : IO Unit := do
  let src2 ← IO.Process.run {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  IO.println src2
-- Main.lean ends here
```
:::
::::

::::example "Running a Program on a File"

该程序使用 Unix 实用程序 `grep` 作为过滤器来查找四位数字回文。
它创建一个包含从 {lean}`0` 到 {lean}`9999` 的所有数字的文件，然后对其调用 `grep`，从其 标准输出 读取结果。

:::ioExample
```ioLean
def main : IO Unit := do
  -- Feed the input to the subprocess
  IO.FS.withFile "numbers.txt" .write fun h =>
    for i in [0:10000] do
      h.putStrLn (toString i)

  let palindromes ← IO.Process.run {
    cmd := "grep",
    args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#, "numbers.txt"]
  }

  let count := palindromes.trimAscii.split "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
```

其输出为：
```stdout
There are 90 four-digit palindromes.
```
:::
::::


{docstring IO.Process.output}

::::example "Checking Exit Codes"
运行时，该程序首先对不存在的文件调用 `cat` 并显示生成的错误代码。
然后，它使用 Unix 工具 `cat` 将自己的源代码与自身连接两次。

:::ioExample
```ioLean
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here
```

其输出为：
```stdout
Exit code from failed process: 1
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here
-- Main.lean begins here
def main : IO UInt32 := do
  let src1 ← IO.Process.output {cmd := "cat", args := #["Nonexistent.lean"]}
  IO.println s!"Exit code from failed process: {src1.exitCode}"

  let src2 ← IO.Process.output {cmd := "cat", args := #["Main.lean", "Main.lean"]}
  if src2.exitCode == 0 then
    IO.println src2.stdout
  else
    IO.eprintln "Concatenation failed"
    return 1

  return 0
-- Main.lean ends here

```
:::
::::


{docstring IO.Process.spawn}

::::example "Asynchronous Subprocesses"

该程序使用 Unix 实用程序 `grep` 作为过滤器来查找四位数字回文。
它将从 {lean}`0` 到 {lean}`9999` 的所有数字提供给 `grep` 进程，然后读取其结果。
仅当 `grep` 足够快并且输出管道足够大以包含所有 90 个四位数字回文时，此代码才是正确的。

:::ioExample
```ioLean
def main : IO Unit := do
  let grep ← IO.Process.spawn {
    cmd := "grep",
    args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#],
    stdin := .piped,
    stdout := .piped,
    stderr := .null
  }

  -- Feed the input to the subprocess
  for i in [0:10000] do
    grep.stdin.putStrLn (toString i)

  -- Consume its output, after waiting 100ms for grep to process the data.
  IO.sleep 100
  let count := (← grep.stdout.readToEnd).trimAscii.split "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
```

其输出为：
```stdout
There are 90 four-digit palindromes.
```
:::
::::

{docstring IO.Process.SpawnArgs}

{docstring IO.Process.StdioConfig}

{docstring IO.Process.Stdio}

{docstring IO.Process.Stdio.toHandleType}

{docstring IO.Process.Child}

{docstring IO.Process.Child.wait}

{docstring IO.Process.Child.tryWait}

{docstring IO.Process.Child.kill}

{docstring IO.Process.Child.takeStdin}

::::example "Closing a Subprocess's Standard Input"

该程序使用 Unix 实用程序 `grep` 作为过滤器来查找四位数回文，确保子进程成功终止。
它将从 {lean}`0` 到 {lean}`9999` 的所有数字提供给 `grep` 进程，然后关闭进程的 标准输入，从而导致其终止。
检查 `grep` 的退出代码后，程序提取其结果。

:::ioExample
```ioLean
def main : IO UInt32 := do
  let grep ← do
    let (stdin, child) ← (← IO.Process.spawn {
      cmd := "grep",
      args := #[r#"^\([0-9]\)\([0-9]\)\2\1$"#],
      stdin := .piped,
      stdout := .piped,
      stderr := .null
    }).takeStdin

    -- Feed the input to the subprocess
    for i in [0:10000] do
      stdin.putStrLn (toString i)

    -- Return the child without its stdin handle.
    -- This closes the handle, because there are
    -- no more references to it.
    pure child

  -- Wait for grep to terminate
  if (← grep.wait) != 0 then
    IO.eprintln s!"grep terminated unsuccessfully"
    return 1

  -- Consume its output
  let count := (← grep.stdout.readToEnd).trimAscii.split "\n" |>.length

  IO.println s!"There are {count} four-digit palindromes."
  return 0
```

其输出为：
```stdout
There are 90 four-digit palindromes.
```
:::
::::

{docstring IO.Process.Output}



# 随机数
%%%
tag := "zh-io-h011"
%%%

{docstring IO.setRandSeed}

{docstring IO.rand}

{docstring randBool}

{docstring randNat}

## 随机生成器
%%%
tag := "zh-io-h012"
%%%

{docstring RandomGen}

{docstring StdGen +hideStructureConstructor +hideFields}

{docstring stdRange}

{docstring stdNext}

{docstring stdSplit}

{docstring mkStdGen}

## 系统随机性
%%%
tag := "zh-io-h013"
%%%

{docstring IO.getRandomBytes}

{include 0 ManualZh.IO.Threads}
