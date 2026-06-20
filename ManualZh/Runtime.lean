/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Manual.Meta
import Manual.Meta.LexedText
import Manual.Papers
import Std.Async.Process

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "运行时代码" =>
%%%
file := "Run-Time-Code"
tag := "runtime"
%%%

已编译的 Lean 代码使用 Lean 运行时提供的服务。
该运行时包含高效的低级原语，可弥合 Lean 语言和支持的平台之间的差距。
这些服务包括：

 : 内存管理

    Lean不需要程序员手动管理内存。
    当需要存储值时会分配空间，而无法再访问（因此不相关）的值将被释放。
    特别是，Lean 使用 {tech (key := "reference count")}[引用计数]，其中每个分配的对象都维护传入引用的计数。
    编译器发出对分配内存和修改引用计数的内存管理例程的调用，这些例程由运行时提供，以及表示编译代码中的 Lean 值的数据结构。

 : 多线程

    {name}`Task` API 提供编写并行和并发代码的能力。
    运行时负责跨操作系统线程调度 Lean 任务。

 : 原语运算符

    许多内置类型（包括 {lean}`Nat`、{lean}`Array`、{lean}`String` 和 固定位宽整数）出于效率原因具有特殊表示。
    运行时提供了这些类型的原始运算符的实现，这些运算符利用了这些优化的表示形式。


有许多原始运算符。
它们在 {ref "basic-types"}[基本类型] 下各自的部分中进行了描述。

# 拳击
%%%
file := "Boxing"
tag := "boxing"
%%%

:::paragraph
Lean 值可以在运行时以两种方式表示：
* {deftech}_Boxed_值可能是指向堆值的指针或需要移位和屏蔽。
* {deftech}_Unboxed_值立即可用。
:::

装箱值可以是指向对象的指针（在这种情况下最低位为 0），也可以是立即值（在这种情况下最低位为 1），并且通过将表示形式向右移动一位来找到该值。

具有未装箱表示的类型（例如 {name}`UInt8` 和 {tech (key := "enum inductive")}[enum inducing] 类型）在编译器可以确定该值具有所述类型的上下文中表示为相应的 C 类型。
在某些情况下，例如 {name}`Array` 等通用容器类型，否则未装箱的值必须在存储之前装箱。
换句话说，使用 {name}`Bool.not` 调用并返回未装箱的 `uint8_t` 值，因为 {tech (key := "enum inductive")}[enum inducing] 类型 {name}`Bool` 具有未装箱的表示形式，但 {lean}`Array Bool` 中的各个 {name}`Bool` 值已装箱。
归纳类型的构造函数中 {lean}`Bool` 类型的字段表示为未装箱，而存储在实例化为 {lean}`Bool` 的多态字段中的 {lean}`Bool` 则为装箱。


# 引用计数
%%%
file := "Reference-Counting"
tag := "reference-counting"
%%%

Lean 使用 {deftech (key := "reference count")}_引用计数_进行内存管理。
每个分配的对象都会维护有多少其他对象引用它的计数。
添加新引用时，计数会增加；删除引用时，计数会递减。
当引用计数达到零时，该对象将不再可访问，并且无法参与程序的进一步执行。
它被释放，并且它对其他对象的所有引用都被删除，这可能会触发进一步的释放。

:::paragraph
引用计数提供了许多好处：

 : 内存的重用

    如果一个对象的引用计数在分配另一个相同大小的对象时降至零，则原始对象的内存可以安全地重新用于新对象。
    因此，当要遍历的数据结构只有一个引用时，许多常见的数据结构遍历（例如 {name}`List.map`）不需要分配内存。

 : 机会性就地更新

    基本类型（例如 {ref "String"}[strings] 和 {ref "Array"}[arrays]）可以提供复制共享数据但就地修改非共享数据的操作。
    只要它们保留对正在修改的值的唯一引用，对这些基本类型的许多操作都会修改它而不是复制它。
    这可以带来显着的性能优势。
    精心编写的 {lean}`Array` 代码避免了不可变数据结构的性能开销，同时保持纯函数提供的推理简易性。

 : 可预测性

    引用计数会在可预测的时间递减。
    因此，引用计数对象可用于管理其他资源，例如文件句柄。
    在 Lean 中，{name IO.FS.Handle}`Handle` 不需要显式关闭，因为当它不再可访问时会立即关闭。

 : 更简单 FFI

    作为回收未使用内存的一部分，不需要重新定位使用引用计数管理的对象。
    这极大地简化了与用其他语言（例如 C）编写的代码的交互。

:::

引用计数的传统缺点包括由于更新引用计数而导致的性能开销以及无法识别和释放循环数据。
通过基于“借用”的分析可以最小化前一个缺点，该分析允许省略许多引用计数更新。
然而，多线程代码需要在线程之间同步引用计数更新，这也会带来很大的开销。
为了减少这种开销，Lean 值被分为可从多个线程访问的值和不可访问的值。
单线程引用计数的更新速度比多线程引用计数快得多，并且许多值只能在单个线程上访问。
这些技术共同大大降低了引用计数的性能开销。
由于 Lean 的可验证片段无法创建循环数据，因此 Lean 运行时没有检测它的技术。
{citet countingBeans}[] 提供有关引用计数在 Lean 中实现的更多详细信息。

## 观察独特性
%%%
file := "Observing-Uniqueness"
tag := "zh-runtime-h003"
%%%

确保数组和字符串被唯一引用是在 Lean 中编写快速代码的关键。
原语 {name}`dbgTraceIfShared` 可用于检查数据结构是否存在别名。
调用时，它返回其参数不变，如果参数的引用计数大于 1，则打印提供的跟踪消息。

{docstring dbgTraceIfShared}

由于 {keywordOf Lean.Parser.Command.eval}`#eval` 实现方式的具体情况，将 {name}`dbgTraceIfShared` 与 {keywordOf Lean.Parser.Command.eval}`#eval` 一起使用可能会产生误导。
相反，它应该在显式编译和运行的代码中使用。

::::example "Observing Uniqueness"
:::ioExample
该程序读取用户输入的一行，并在用空格替换其第一个字符后打印它。
如果字符串不共享并且字符都包含在 Unicode 的 7 位 ASCII 子集中，则替换字符串中的字符将使用就地更新。
{name}`dbgTraceIfShared` 调用不执行任何操作，表明该字符串确实会就地更新而不是复制。

```ioLean
def process (str : String) (h : str.startPos ≠ str.endPos) : IO Unit := do
  IO.println ((dbgTraceIfShared "String update" str).startPos.set ' ' h)

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if h : line.startPos ≠ line.endPos then
    process line h
```

使用此输入运行时：
```stdin
Here is input.
```

程序发出：
```stdout
 ere is input.
```
具有空的 标准错误 输出：
```stderr
```
:::

:::ioExample
该版本的程序保留了对原始字符串的引用，这需要将调用中的字符串复制到 {name}`String.set`。
这一事实在其 标准错误 输出中可见。

```ioLean
def process (str : String) (h : str.startPos ≠ str.endPos) : IO Unit := do
  IO.println ((dbgTraceIfShared "String update" str).startPos.set ' ' h)

def main : IO Unit := do
  let line := (← (← IO.getStdin).getLine).trimAscii.copy
  if h : line.startPos ≠ line.endPos then
    process line h
  IO.println "Original input:"
  IO.println line
```

使用此输入运行时：
```stdin
Here is input.
```

程序发出：
```stdout
 ere is input.
Original input:
Here is input.
```

在其 标准错误 中，传递给 {name}`dbgTraceIfShared` 的消息是可见的。
```stderr
shared RC String update
```
:::
::::

## 编译器IR
%%%
file := "Compiler-IR"
tag := "zh-runtime-h004"
%%%

编译器选项 {option}`trace.compiler.ir.result` 可用于检查函数的编译器中间表示 (IR)。
在此中间表示中，引用计数、分配和重用是明确的：
 * `isShared` 运算符检查引用计数是否为 `1`。
 * `ctor_`$`n` 分配类型的第 $`n` 个构造函数。
 * `proj_`$`n` 从构造函数值中检索 $`n`th 字段。
 * `set `$`x`﻿`[`$`n`﻿`]` 改变 $`x` 中构造函数的 $`n`th 字段。
 * `ret `$`x` 返回 $`x` 中的值。

引用计数操作的细节可能取决于优化过程（例如内联）的结果。
虽然绝大多数 Lean 代码不需要这种关注来实现良好的性能，但在编写性能关键型代码时，了解如何诊断独特的引用问题可能非常重要。

{optionDocs trace.compiler.ir.result}

:::example "Reference Counts in IR"
编译器 IR 可用于观察引用计数何时递增，这有助于诊断预期值具有唯一传入引用但实际上是共享的情况。
这里，{lean}`process`和{lean}`process'`各自以一个字符串作为参数，并用{name}`String.set`修改它，返回一对字符串。
{lean}`process` 返回常量字符串作为该对的第二个元素，而 {lean}`process'` 返回原始字符串。

```lean
set_option trace.compiler.ir.result true
```
```lean (name := p1)
def process (str : String) : String × String :=
  (str.set 0 ' ', "")
```
```lean (name := p2)
def process' (str : String) : String × String:=
  (str.set 0 ' ', str)
```

{lean}`process` 的 IR 不包含 `inc` 或 `dec` 指令。
如果传入的字符串 `x_1` 是唯一引用，那么当传递给 {name}`String.set` 时它仍然是唯一引用，然后可以使用就地修改：
```leanOutput p1 (allowDiff := 5)
[Compiler.IR] [result]
    def process._closed_0 : obj :=
      let x_1 : obj := "";
      ret x_1
    def process (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := process._closed_0;
      let x_6 : obj := ctor_0[Prod.mk] x_4 x_5;
      ret x_6
```

另一方面，{lean}`process'` 的 IR 在调用 {name}`String.set` 之前递增字符串的引用计数。
因此，修改后的字符串 `x_4` 是一个副本，无论对 `x_1` 的原始引用是否唯一：
```leanOutput p2
[Compiler.IR] [result]
    def process' (x_1 : obj) : obj :=
      let x_2 : tagged := 0;
      let x_3 : u32 := 32;
      inc x_1;
      let x_4 : obj := String.set x_1 x_2 x_3;
      let x_5 : obj := ctor_0[Prod.mk] x_4 x_1;
      ret x_5
```
:::

:::example "Memory Reuse in IR"
函数 {lean}`discardElems` 是 {name}`List.map` 的简化版本，它将列表中的每个元素替换为 {lean}`()`。
检查其中间表示表明，当其引用唯一时，它将重用列表的内存。

```lean (name := discardElems)
set_option trace.compiler.ir.result true

def discardElems : List α → List Unit
  | [] => []
  | x :: xs => () :: discardElems xs
```

这会发出以下 IR：

```leanOutput discardElems
[Compiler.IR] [result]
    def discardElems._redArg (x_1 : tobj) : tobj :=
      case x_1 : tobj of
      List.nil →
        let x_2 : tagged := ctor_0[List.nil];
        ret x_2
      List.cons →
        let x_3 : tobj := proj[1] x_1;
        block_4 (x_5 : tobj) (x_6 : u8) :=
          let x_7 : tagged := ctor_0[PUnit.unit];
          let x_8 : tobj := discardElems._redArg x_3;
          block_9 (x_10 : obj) :=
            ret x_10;
          case x_6 : u8 of
          Bool.false →
            set x_5[1] := x_8;
            set x_5[0] := x_7;
            jmp block_9 x_5
          Bool.true →
            let x_11 : obj := ctor_1[List.cons] x_7 x_8;
            jmp block_9 x_11;
        let x_12 : u8 := isShared x_1;
        case x_12 : u8 of
        Bool.false →
          let x_13 : tobj := proj[0] x_1;
          dec x_13;
          jmp block_4 x_1 x_12
        Bool.true →
          inc x_3;
          dec x_1;
          jmp block_4 ◾ x_12
[Compiler.IR] [result]
    def discardElems (x_1 : ◾) (x_2 : tobj) : tobj :=
      let x_3 : tobj := discardElems._redArg x_2;
      ret x_3
```

在 IR 中，{name}`List.cons` 情况显式检查参数值是否共享（即其引用计数是否大于 1）。
如果引用是唯一的，则丢弃的列表元素 `x_5` 的引用计数将递减，并重用构造函数值。
如果共享，则在 `x_11` 中为结果分配一个新的 {name}`List.cons`。
:::


### 更多主题
%%%
file := "More-Topics"
tag := "zh-runtime-h005"
draft := true
%%%

:::planned 208

 * 紧凑区域

 * C 代码何时应增加或减少引用计数？

 * 借用注释（`@&`）的含义是什么？

:::

# 多线程执行
%%%
file := "Multi-Threaded-Execution"
tag := "zh-runtime-h006"
%%%

Lean 包括并行和并发程序的原语，使用 {tech (key := "tasks")}[任务] 进行描述。
Lean 运行时系统包括一个为任务分配硬件资源的任务管理器。
与用于定义任务的 API 一起，{ref "concurrency"}[有关多线程程序的部分]对此进行了详细描述。

# 对外函数接口
%%%
file := "Foreign-Function-Interface"
tag := "ffi"
%%%


*当前接口设计用于 Lean 内部使用，应视为不稳定*。
未来将进一步完善和扩展。

Lean 提供与支持 C ABI 的任何语言的高效互操作性。
但是，此支持目前仅限于传输 Lean 数据类型；特别是，目前还无法通过 Lean 的值传递或返回复合数据结构，例如 C {C}`struct`。

与其他语言互操作有两个主要属性：
  {TODO}[It can also be used with `def` to provide an internal definition, but ensuring consistency of both definitions is up to the user.]
* `@[export sym] def leanSym : ...`

:::syntax attr (title := "External Symbols")
```grammar
extern $s:str
```

将 Lean 声明绑定到指定的外部符号。
:::

:::syntax attr (title := "Exported Symbols")
```grammar
export $x:ident
```
导出具有未修饰符号名称 `sym` 的 Lean 常量。
:::


有关如何从 Lean 调用外部代码以及反之亦然的简单示例，请参阅 Lean 源存储库中的 [FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/ffi) 和 [反向 FFI](https://github.com/leanprover/lean4/tree/master/tests/lake/examples/reverse-ffi) 示例。

## Lean ABI
%%%
file := "The-Lean-ABI"
tag := "zh-runtime-h008"
%%%

:::leanSection
```lean -show
variable {α₁ αₙ β αᵢ}
private axiom «α₂→…→αₙ₋₁».{u} : Type u
local macro "..." : term => ``(«α₂→…→αₙ₋₁»)
```

Lean {deftech (key := "Application Binary Interface")}_应用程序二进制接口_ (ABI) 描述如何在平台本机调用约定中对 Lean 声明的签名进行编码。
它基于标准C ABI和目标平台的调用约定。
可以使用属性 Lean 标记 Lean 声明以与外部函数交互，这会导致编译代码使用 C 声明 {C}`sym` 作为实现，也可以使用属性 {attr}`export sym` 进行标记，这使得声明可作为 {C}`sym` 提供给 C。

在这两种情况下，C 声明的类型均派生自具有属性的声明的 Lean 类型。
令 {lean}`α₁ → ... → αₙ → β` 为声明的 {tech (key := "normal form")}[规范化] 类型。
如果 `n` 为 0，则对应的 C 声明为
```C
extern s sym;
```
其中 {C}`s` 是 {lean}`β` 的 C 翻译，如 {ref "ffi-types"}[下一节]中指定。
对于标记为 {attr}`extern` 的定义，仅保证在调用 Lean 模块的初始化程序或导入模块的初始化程序后初始化符号的值。
关于 {ref "ffi-initialization"}[初始化] 的部分更详细地描述了初始化器。

如果 `n` 大于 0，则相应的 C 声明为
```C
s sym(t₁, ..., tₙ);
```
其中参数类型 `tᵢ` 是类型 {lean}`αᵢ` 的 C 翻译。
对于 {attr}`extern`，首先删除所有 {tech (key := "irrelevant")}[不相关] 类型。
:::

### 将类型从 Lean 转换为 C
%%%
file := "Translating-Types-from-Lean-to-C"
tag := "ffi-types"
%%%

:::leanSection
```lean -show
universe u
variable (p : Prop)
private axiom «...» : Sort u
local macro "..." : term => ``(«...»)
```

在 {tech (key := "application binary interface")}[ABI] 中，Lean 类型转换为 C 类型，如下所示：

* 整数类型 {lean}`UInt8`, …, {lean}`UInt64`, {lean}`USize` 分别由 C 类型 {C}`uint8_t`, ..., {C}`uint64_t`, {C}`size_t` 表示。
  如果它们的 {ref "fixed-int-runtime"}[运行时表示] 需要 {tech (key := "boxed")}[装箱]，则它们会在 FFI 边界处拆箱。
* {lean}`Char` 由 {C}`uint32_t` 表示。
* {lean}`Float` 由 {C}`double` 表示。
* {name}`Nat`和{name}`Int`由{C}`lean_object *`表示。
  它们的运行时值可以是指向不透明 bignum 对象的指针，或者如果“指针”的最低位为 1 ({C}`lean_is_scalar`)，则为编码的自然数或整数 ({C}`lean_box`/{C}`lean_unbox`)。
* Universe {lean}`Sort u`、类型构造函数 {lean}`... → Sort u` 或命题 {lean}`p`​` :`{lean}` Prop` 是 {tech (key := "irrelevant")}[无关]，并且可以静态擦除（参见上文）或表示为具有运行时值的 {C}`lean_object *` {C}`lean_box(0)`
* 对于没有特殊编译器支持的其他归纳类型的 ABI 取决于类型的具体情况。
  它与这些类型的 {ref "run-time-inductives"}[运行时表示]相同。
  其运行时值要么是指向 {C}`lean_object` 子类型的对象的指针（请参阅下面的“归纳类型”部分），要么是归纳类型的第 {C}`cidx` 构造函数的值 {C}`lean_box(cidx)`（如果该构造函数没有任何相关参数）。

:::

```lean -show
variable (u : Unit)
```

:::example "`Unit` in the ABI"
{lean}`u`​` : `{lean}`Unit` 的运行时值始终为 `lean_box(0)`。
:::

### 借款
%%%
file := "Borrowing"
tag := "ffi-borrowing"
%%%

默认情况下，{attr}`extern` 函数的所有 {C}`lean_object *` 参数都被视为 {deftech}_owned_。
外部代码传递一个“虚拟 RC 令牌”，并负责将该令牌传递给另一个消费函数（仅一次）或通过 {C}`lean_dec` 释放它。
为了减少引用计数开销，可以通过在参数类型前添加 {keywordOf Lean.Parser.Term.borrowed}`@&` 来将参数标记为 {deftech}_borrowed_。
借用的对象只能传递给其他非消耗函数（任意频繁）或使用 {C}`lean_inc` 转换为拥有的值。
在`lean.h`中，{C}`lean_object *`别名{C}`lean_obj_arg`和{C}`b_lean_obj_arg`用于在C端标记这种差异。
返回值和 `@[export]` 参数此时始终拥有。

:::syntax term (title := "Borrowed Parameters")
```grammar
@& $_
```
通过在参数类型前加上 {keyword}`@&` 前缀，可以将参数标记为 {tech (key := "borrowed")}[借用]。
:::

## 初始化
%%%
file := "Initialization"
tag := "ffi-initialization"
%%%

当在较大的程序中包含 Lean 代码时，模块在访问其任何声明之前必须是 {deftech (key := "initialize")}_initialized_。
模块初始化需要：
* 所有“常量定义”（空函数）的初始化，包括从其他函数中取出的封闭术语，
* 执行标有 {attr}`init` 属性的所有代码，以及
* 如果已设置模块初始值设定项的 `builtin` 参数，则执行标有 {attr}`builtin_init` 属性的所有代码。

对于从 Lean 代码编译的可执行文件以及使用 `lean --plugin` 加载的“插件”，模块初始化程序会使用 `builtin` 标志自动运行。
对于 `lean` 导入的所有其他模块，初始化程序在没有 `builtin` 的情况下运行。
换句话说，{attr}`init` 函数当且仅当其模块被导入时才会运行，无论它们是否具有可用的本机代码，而 {attr}`builtin_init` 函数仅针对本机可执行文件或插件运行，无论其模块是否已导入。
Lean 编译器使用内置初始化程序来实现诸如注册基本解析器之类的目的，这些解析器即使在不导入其模块的情况下也应该可用，这是引导所必需的。

包 `foo` 中模块 `A.B` 的初始化程序称为 {C}`initialize_foo_A_B`。
对于 Lean内核中的模块（例如 {module}`Init.Prelude`），初始化程序称为 {C}`initialize_Init_Prelude`。
模块初始化程序将自动初始化任何导入的模块。
它们也是幂等的（当使用相同的 `builtin` 标志运行时），但不是线程安全的。

*对于与流程相关的功能很重要*：使用 `libuv` 中的流程相关功能（例如 {name}`Std.IO.Process.getProcessTitle` 和 {name}`Std.IO.Process.setProcessTitle`）的应用程序必须调用 `lean_setup_args(argc, argv)`（它返回可能已修改的 `argv`，必须用来代替原始的）*在*调用 `lean_initialize()` 或`lean_initialize_runtime_module()`。
这可以正确设置进程处理功能，这对于 Lean 运行时可能依赖的某些系统级操作至关重要。

与 Lean 运行时的初始化一起，在访问任何 Lean 声明之前，应运行如下代码一次：
```C
void lean_initialize_runtime_module();
void lean_initialize();
char ** lean_setup_args(int argc, char ** argv);

lean_object * initialize_A_B(uint8_t builtin);
lean_object * initialize_C(uint8_t builtin);
...

argv = lean_setup_args(argc, argv); // if using process-related functionality
lean_initialize_runtime_module();
// necessary (and replaces `lean_initialize_runtime_module`) for code that (indirectly) accesses the `Lean` package:
//lean_initialize();

lean_object * res;
// use same default as for Lean executables
uint8_t builtin = 1;
res = initialize_foo_A_B(builtin);
if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
} else {
    lean_io_result_show_error(res);
    lean_dec(res);
    return ...;  // do not access Lean declarations if initialization failed
}
res = initialize_bar_C(builtin);
if (lean_io_result_is_ok(res)) {
...

//lean_init_task_manager();  // necessary for code that (indirectly) uses `Task`
lean_io_mark_end_initialization();
```

此外，任何其他不是由 Lean 运行时本身生成的线程都必须通过调用来初始化以供 Lean 使用
```C
void lean_initialize_thread();
```
并且应该通过调用来最终确定以释放所有线程本地资源
```C
void lean_finalize_thread();
```

## 解释器中的 `@[extern]`
%%%
file := "_______LSQ_extern_RSQ____-in-the-Interpreter"
tag := "zh-runtime-h012"
%%%

Lean 解释器可以运行 Lean 声明，这些声明的符号在加载的共享库中可用，其中包括标记为 {attr}`extern` 的声明。
要运行此代码（例如使用 {keywordOf Lean.Parser.Command.eval}`#eval`），需要执行以下步骤：
  1. 包含声明及其依赖项的模块必须编译成共享库
  1. 应将此共享库提供给 `lean --load-dynlib=` 以运行导入模块的代码。

加载包含外部符号的外部库是不够的，因为解释器依赖于为每个 {attr}`extern` 声明发出的代码。
因此，无法解释同一文件中的 {attr}`extern` 声明。
Lean 源存储库在 [`tests/compiler/foreign`](https://github.com/leanprover/lean4/tree/master/tests/compiler/foreign/) 中包含此用法的示例。
