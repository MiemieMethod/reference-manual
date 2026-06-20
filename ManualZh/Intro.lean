/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "引言" =>
%%%
htmlSplit := .never
tag := "introduction"
%%%

_Lean 语言参考_ 旨在对 Lean 作出全面而精确的描述。
它是一部供 Lean 用户查阅详细信息的参考著作，而不是面向新用户的教程。
目前，本参考手册仍是公开预览版。
教程和学习材料请见 [Lean 文档页面](https://lean-lang.org/documentation/)。

本文档描述 Lean 版本 {versionString}[]。


# 历史
%%%
tag := "history-of-lean"
%%%

Leonardo de Moura 于 2013 年在微软研究院期间启动了 Lean 项目；Lean 0.1 于 2014 年 6 月 16 日正式发布。
Lean 项目的目标，是将小型、可独立实现的逻辑内核所提供的高可信度，与 SMT 求解器等工具的便利性和自动化能力结合起来，同时能够扩展到大型问题。
这一愿景仍然指导着 Lean 的发展：我们持续改进自动化、性能和易用性；受信任的核心证明检查器仍然保持极小，并且已有独立实现。

Lean 的早期版本主要被配置为 C++ 库，客户代码可以在其中构造可信且可独立检查的证明。
在这些早期年份中，Lean 的设计迅速向传统交互式证明器演化：起初 tactic 用 Lua 编写，后来则具有专门的前端语法。
2017 年 1 月 20 日，Lean 3.0 系列首次发布。
Lean 3 在数学家群体中得到了广泛采用，并开创了自扩展性：tactic、记号和顶层命令都可以在 Lean 自身中定义。
数学社群构建了 Mathlib；到 Lean 3 末期，Mathlib 已有超过一百万行形式化数学，所有证明均由机器检查。
然而，系统本身仍以 C++ 实现，这限制了 Lean 的灵活性，也由于所需技能多样而增加了开发难度。

Lean 4 的开发始于 2018 年，并于 2023 年 9 月 8 日发布 4.0 版。
Lean 4 是一个重要里程碑：自第 4 版起，Lean 已实现自举，约 90% 的 Lean 实现代码本身就是用 Lean 编写的。
Lean 4 丰富的扩展 API 使用户能够按自身需要调整系统，而不必依赖核心开发者添加必要功能。
此外，自举使开发过程快得多，因此可以更快交付新特性和性能改进；Lean 4 比 Lean 3 更快，也能扩展到更大的问题。
在 Lean 开发者支持下，社群于 2023 年成功将 Mathlib 移植到 Lean 4；如今 Mathlib 已增长到超过一百五十万行。
尽管 Mathlib 增长了 50%，Lean 4 检查它的速度仍快于 Lean 3 检查当时较小库的速度。
Lean 4 的开发周期大致等于所有先前版本开发周期之和；我们现在对其设计感到满意，并且不计划再进行重写。

2023 年 7 月，Leonardo de Moura 及其共同创始人 Sebastian Ullrich 在 Convergent Research 旗下创立了非营利的 Lean Focused Research Organization（FRO），并获得 Simons Foundation International、Alfred P. Sloan Foundation 和 Richard Merkin 的慈善支持。
FRO 目前有十余名员工，致力于支持 Lean 以及更广泛 Lean 社群的成长和可扩展性。


# 排版约定
%%%
tag := "typographical-conventions"
%%%

本文档使用若干排版和布局约定，以标示所呈现信息的不同方面。

## Lean 代码
%%%
tag := "code-samples"
%%%


本文档包含许多 Lean 代码示例。
其格式如下：

```lean
def hello : IO Unit := IO.println "Hello, world!"
```

编译器输出（可能是错误、警告，也可能只是信息）既会在代码中显示，也会单独显示：

```lean (name := output) +error
#eval s!"The answer is {2 + 2}"

theorem bogus : False := by sorry

example := Nat.succ "two"
```

信息性输出，例如 {keywordOf Lean.Parser.Command.eval}`#eval` 的结果，显示如下：
```leanOutput output (severity := information)
"The answer is 4"
```

警告显示如下：
```leanOutput output (severity := warning)
declaration uses `sorry`
```

错误消息显示如下：
```leanOutput output (severity := error)
Application type mismatch: The argument
  "two"
has type
  String
but is expected to have type
  Nat
in the application
  Nat.succ "two"
```


tactic 证明状态由小菱形标记表示；点击该标记即可显示证明状态，例如下列 {tactic}`rfl` 之后的标记：
```lean
example : 2 + 2 = 4 := by rfl
```

:::tacticExample
证明状态也可以单独显示。
在试图证明 {goal}`2 + 2 = 4` 时，初始证明状态为：
```pre
⊢ 2 + 2 = 4
```
使用 {tacticStep}`rfl` 后，所得状态为：
```post

```

```setup
skip
```
:::

代码示例中的标识符会超链接到其文档。

含语法错误的代码示例会标出解析错误发生的位置，并附上错误消息：
```syntaxError intro
def f : Option Nat → Type
  | some 0 => Unit
  | => Option (f t)
  | none => Empty
```
```leanOutput intro
<example>:3:3-3:6: unexpected token '=>'; expected term
```

## 示例
%%%
tag := "example-boxes"
%%%


说明性示例置于提示框中，如下所示：

::::keepEnv
:::example "Even Numbers"
这是一个示例的示例。

定义偶数的一种方式是使用归纳谓词：
```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)
```
:::
::::

## 技术术语
%%%
tag := "technical-terms"
%%%


{deftech}_技术术语_ 是指在撰写本参考手册这样的技术材料时，以非常特定的意义使用的词项。
{tech}[技术术语]的用例通常会像此处一样超链接到其定义位置。

## 常量、语法与 tactic 参考
%%%
tag := "reference-boxes"
%%%


定义、归纳类型、语法构造和 tactic 都有专门描述。
这些描述标记如下：

::::keepEnv
```lean
/--
Evenness: a number is even if it can be evenly divided by two.
-/
inductive Even : Nat → Prop where
  | /-- 0 is considered even here -/
    zero : Even 0
  | /-- If `n` is even, then so is `n + 2`. -/
    plusTwo : Even n → Even (n + 2)
```

{docstring Even}

::::

# 如何引用本著作
%%%
tag := "zh-intro-h007"
%%%

在正式引用中，请将本著作引用为 Lean Developers 所著的 _The Lean Language Reference_。
此外，请在引用中注明相应的 Lean 版本，即 {versionString}[]。

# 开源许可证
%%%
tag := "dependency-licenses"
number := false
%%%

{licenseInfo}
