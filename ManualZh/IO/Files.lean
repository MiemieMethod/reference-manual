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

#doc (Manual) "文件、文件句柄和流" =>

Lean 在所有支持的平台上提供一致的文件系统 API。
这些是关键概念：

: {deftech}[文件]

  文件是操作系统提供的一种抽象，它提供对持久存储的数据的随机访问，这些数据按层次结构组织到目录中。

: {deftech}[目录]

  目录，也称为_文件夹_，可能包含文件或其他目录。
  从根本上来说，目录将名称映射到它包含的文件和/或目录。

: {deftech}[文件句柄]

  文件句柄 ({name IO.FS.Handle}`Handle`) 是对已打开以进行读取和/或写入的文件的抽象引用。
  文件句柄维护一种确定是否允许读取和/或写入的模式，以及指向文件中特定位置的光标。
  读取或写入文件句柄会使光标前进。
  文件句柄可能是 {deftech}[buffered]，这意味着从文件句柄读取可能不会返回持久数据的当前内容，并且写入文件句柄可能不会立即修改它们。

: 路径

  文件主要通过 {deftech}_paths_ ({name}`System.FilePath`) 访问。
  路径是目录名的序列，可能以文件名结尾。
  它们由字符串表示，其中分隔符 {margin}[当前平台的分隔符在 {name}`System.FilePath.pathSeparators` 中列出。] 分隔名称。

  路径的详细信息是特定于平台的。
  {deftech}[绝对路径] 从 {deftech}_根目录_ 开始；某些操作系统具有单个根目录，而其他操作系统可能具有多个根目录。
  相对路径不从根目录开始，并且需要将某个其他目录作为起点。
  除了目录之外，路径还可以包含特殊目录名称 `.`（指在其中找到它的目录）和 `..`（指路径中先前的目录）。

  文件名和路径可能以一个或多个标识文件类型的 {deftech}_extensions_ 结尾。
  扩展名由字符 {name}`System.FilePath.extSeparator` 分隔。
  在某些平台上，可执行文件具有特殊扩展名 ({name}`System.FilePath.exeExtension`)。

: {deftech}[流]

  流是对文件的更高级别的抽象，既提供附加功能又隐藏文件的一些细节。
  虽然 {tech}[文件句柄] 本质上是围绕操作系统表示的薄包装器，但流在 Lean 中实现为称为 {lean}`IO.FS.Stream` 的结构。
  由于流是在 Lean 中实现的，因此用户代码可以创建额外的流，这些流可以与标准库中提供的流无缝地一起使用。

# 低级文件 API
%%%
tag := "zh-io-files-h001"
%%%

在最低级别，文件是使用 {name IO.FS.Handle.mk}`Handle.mk` 显式打开的。
当删除对句柄对象的最后一个引用时，文件将被关闭。
除了确保没有对文件句柄的引用之外，没有明确的方法可以关闭文件句柄。


{docstring IO.FS.Handle}

{docstring IO.FS.Handle.mk}

{docstring IO.FS.Mode}

{docstring IO.FS.Handle.read}

{docstring IO.FS.Handle.readToEnd}

{docstring IO.FS.Handle.readBinToEnd}

{docstring IO.FS.Handle.readBinToEndInto}

{docstring IO.FS.Handle.getLine}

{docstring IO.FS.Handle.write}

{docstring IO.FS.Handle.putStr}

{docstring IO.FS.Handle.putStrLn}

{docstring IO.FS.Handle.flush}

{docstring IO.FS.Handle.rewind}

{docstring IO.FS.Handle.truncate}

{docstring IO.FS.Handle.isTty}

{docstring IO.FS.Handle.lock}

{docstring IO.FS.Handle.tryLock}

{docstring IO.FS.Handle.unlock}


::::example "One File, Multiple Handles"
该程序对同一文件有两个句柄。
由于文件 I/O 可能会针对每个句柄独立缓冲，因此当缓冲区需要与文件的实际内容同步时，应调用 {name IO.FS.Handle.flush}`Handle.flush`。
在这里，两个句柄以锁步方式处理文件，其中一个句柄比另一个句柄领先一个字节。
第一个句柄用于计算 `'A'` 出现的次数，而第二个句柄用于将每个 `'A'` 替换为 `'!'`。
第二个句柄在 {name IO.FS.Mode.readWrite}`readWrite` 模式而不是 {name IO.FS.Mode.write}`write` 模式下打开，因为在 {name IO.FS.Mode.write}`write` 模式下打开现有文件会将其替换为空文件。
在这种情况下，在执行期间不需要刷新缓冲区，因为修改仅发生在不会再次读取的文件部分，但应在循环完成后刷新写入句柄。

:::ioExample
```ioLean
open IO.FS (Handle)

def main : IO Unit := do
  IO.println s!"Starting contents: '{(← IO.FS.readFile "data").trimAscii}'"

  let h ← Handle.mk "data" .read
  let h' ← Handle.mk "data" .readWrite
  h'.rewind

  let mut count := 0
  let mut buf : ByteArray ← h.read 1
  while ok : buf.size = 1 do
    if Char.ofUInt8 buf[0] == 'A' then
      count := count + 1
      h'.write (ByteArray.empty.push '!'.toUInt8)
    else
      h'.write buf
    buf ← h.read 1

  h'.flush

  IO.println s!"Count: {count}"
  IO.println s!"Contents: '{(← IO.FS.readFile "data").trimAscii}'"
```

当运行此文件时：
```inputFile "data"
AABAABCDAB
```

程序输出：
```stdout
Starting contents: 'AABAABCDAB'
Count: 5
Contents: '!!B!!BCD!B'
```
```stderr -show
```

之后，该文件包含：
```outputFile "data"
!!B!!BCD!B
```

:::
::::

# 流
%%%
tag := "zh-io-files-h002"
%%%

{docstring IO.FS.Stream}

{docstring IO.FS.Stream.ofBuffer}

{docstring IO.FS.Stream.ofHandle}

{docstring IO.FS.Stream.putStrLn}

{docstring IO.FS.Stream.Buffer}


# 路径
%%%
tag := "zh-io-files-h003"
%%%

路径由字符串表示。
不同的平台对路径有不同的约定：一些使用斜杠（`/`）作为目录分隔符，另一些使用反斜杠（`\`）。
有些区分大小写，有些则不区分大小写。
可以使用不同的 Unicode 编码和正常形式来表示文件名，并且某些平台将文件名视为字节序列而不是字符串。
在一个系统上表示 {tech}[绝对路径] 的字符串在另一系统上甚至可能不是有效路径。

要编写与多个系统尽可能兼容的 Lean 代码，使用 Lean 的路径操作原语而不是原始字符串操作会很有帮助。
{name}`System.FilePath.join` 等帮助程序会考虑绝对路径的特定于平台的规则，{name}`System.FilePath.pathSeparator` 包含当前平台的适当路径分隔符，{name}`System.FilePath.exeExtension` 包含可执行文件的任何必要扩展名。
避免对这些规则进行硬编码。

{name System.FilePath}`FilePath` 有一个 {lean}`Div` 类型类的实例，它允许使用斜杠运算符来连接路径。

{docstring System.FilePath +allowMissing}

{docstring System.mkFilePath}

{docstring System.FilePath.join}

{docstring System.FilePath.normalize}

{docstring System.FilePath.isAbsolute}

{docstring System.FilePath.isRelative}

{docstring System.FilePath.parent}

{docstring System.FilePath.components}

{docstring System.FilePath.fileName}

{docstring System.FilePath.fileStem}

{docstring System.FilePath.extension}

{docstring System.FilePath.addExtension}

{docstring System.FilePath.withExtension}

{docstring System.FilePath.withFileName}

{docstring System.FilePath.pathSeparator}

{docstring System.FilePath.pathSeparators}

{docstring System.FilePath.extSeparator}

{docstring System.FilePath.exeExtension}

# 与文件系统交互
%%%
tag := "zh-io-files-h004"
%%%

路径上的某些操作会参考文件系统。

{docstring IO.FS.Metadata}

{docstring System.FilePath.metadata}

{docstring System.FilePath.symlinkMetadata}

{docstring System.FilePath.pathExists}

{docstring System.FilePath.isDir}

{docstring IO.FS.DirEntry}

{docstring IO.FS.DirEntry.path}

{docstring System.FilePath.readDir}

{docstring System.FilePath.walkDir}

{docstring IO.AccessRight +allowMissing}

{docstring IO.AccessRight.flags}

{docstring IO.FileRight}

{docstring IO.FileRight.flags}

{docstring IO.setAccessRights}

{docstring IO.FS.removeFile}

{docstring IO.FS.rename}

{docstring IO.FS.removeDir}

{docstring IO.FS.lines}

{docstring IO.FS.withTempFile}

{docstring IO.FS.withTempDir}

{docstring IO.FS.createDirAll}

{docstring IO.FS.writeBinFile}

{docstring IO.FS.withFile}

{docstring IO.FS.removeDirAll}

{docstring IO.FS.createTempFile}

{docstring IO.FS.createTempDir}

{docstring IO.FS.readFile}

{docstring IO.FS.realPath}

{docstring IO.FS.writeFile}

{docstring IO.FS.readBinFile}

{docstring IO.FS.createDir}

# 标准输入/输出
%%%
tag := "stdio"
%%%

在源自 Unix 或受 Unix 启发的操作系统上，{deftech}_standard input_、{deftech}_standard output_ 和 {deftech}_standard error_ 是每个进程中可用的三个流的名称。
通常，程序应从 标准输入 读取，将普通输出写入 标准输出，并将错误消息写入 标准错误。
默认情况下，标准输入 接收来自控制台的输入，而 标准输出 和 标准错误 输出到控制台，但这三者通常都重定向到管道或文件或从管道或文件重定向。

Lean 不是提供对操作系统标准 I/O 设施的直接访问，而是将它们包装在 {name IO.FS.Stream}`Stream` 中。
此外，{lean}`IO` monad 包含对替换或本地覆盖它们的特殊支持。
这种额外的间接级别使得可以在 Lean 程序中重定向输入和输出。


{docstring IO.getStdin}

::::example "Reading from Standard Input"
在此示例中，{lean}`IO.getStdin` 和 {lean}`IO.getStdout` 分别用于获取当前 标准输入 和输出。
这些可以读取和写入。

:::ioExample
```ioLean
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "Who is it?"
  let name ← stdin.getLine
  stdout.putStr "Hello, "
  stdout.putStrLn name
```

有了这个 标准输入：
```stdin
Lean user
```
标准输出 是：
```stdout
Who is it?
Hello, Lean user
```
:::
::::

{docstring IO.setStdin}

{docstring IO.withStdin}

{docstring IO.getStdout}

{docstring IO.setStdout}

{docstring IO.withStdout}

{docstring IO.getStderr}

{docstring IO.setStderr}

{docstring IO.withStderr}

{docstring IO.FS.withIsolatedStreams}

::::keepEnv
:::example "Redirecting Standard I/O to Strings"
{lean}`countdown` 函数从指定数字开始倒计时，并将其进度写入 标准输出。
使用 `IO.FS.withIsolatedStreams`，可以将此输出重定向到字符串。

```lean (name := countdown)
def countdown : Nat → IO Unit
  | 0 =>
    IO.println "Blastoff!"
  | n + 1 => do
    IO.println s!"{n + 1}"
    countdown n

def runCountdown : IO String := do
  let (output, ()) ← IO.FS.withIsolatedStreams (countdown 10)
  return output

#eval runCountdown
```

运行 {lean}`countdown` 会生成一个包含输出的字符串：
```leanOutput countdown
"10\n9\n8\n7\n6\n5\n4\n3\n2\n1\nBlastoff!\n"
```
:::
::::

# 文件和目录
%%%
tag := "zh-io-files-h006"
%%%

{docstring IO.currentDir}

{docstring IO.appPath}

{docstring IO.appDir}
