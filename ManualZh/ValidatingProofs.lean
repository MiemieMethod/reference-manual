/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/
import VersoManual

import Manual.Meta

import Verso.Code.External

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option guard_msgs.diff true

open Verso.Code.External (lit)

open Lean (Syntax SourceInfo)

#doc (Manual) "验证 Lean 证明" =>
%%%
file := "ValidatingProofs"
tag := "validating-proofs"
number := false
htmlSplit := .never
%%%

本节讨论如何验证以 Lean 表示的证明。

根据情况，可能会建议采取额外的步骤来排除误导性的证据。
特别是，无论是处理 {tech}[诚实] 证明尝试（仅需要防止良性错误）还是处理可能积极试图误导的 {tech}[恶意] 证明尝试，这一点都非常重要。

特别是，当目标是创建有效证明时，我们使用 {deftech}_honest_。
这允许证明和元代码（策略、属性、命令等）中存在错误和错误，但不允许明显仅用于规避系统的代码（例如使用 {option}`debug.skipKernelTC`）。
请注意，API 函数上的 {keyword}`unsafe` 标记与该 API 是否可以以不诚实的方式使用无关。

相比之下，我们使用 {deftech}_malicious_ 来描述特意欺骗或误导用户、利用错误或危害系统的代码。
这包括未经审查的人工智能生成的证明和程序。

此外，区分“定理是否有有效证明”和“定理陈述的含义是什么”这一问题也很重要。

下面介绍了一系列逐步升级的检查，以及如何执行这些检查的说明、对这些检查所涉及内容的解释以及它们所防范的错误或攻击。

# 蓝色双复选标记
%%%
tag := "validating-blue-check-marks"
%%%

在日常使用 Lean 时，只需检查定理陈述旁边的蓝色双勾标记即可确保定理得到证明。

## 指示
%%%
tag := "zh-validatingproofs-h002"
%%%

当与 Lean 交互工作时，一旦定理被证明，蓝色的双复选标记就会出现在代码左侧的装订线中。

:::figure "A double blue check mark"
![编辑器装订线中出现双蓝色复选标记的定理](/static/screenshots/doublecheckmarks.png)
:::

## 意义
%%%
tag := "zh-validatingproofs-h003"
%%%

蓝色勾号表示根据当前文件及其导入中定义的语法和类型类实例，已成功精化定理陈述，并且 Lean内核已接受从当前文件及其导入中声明的定义、定理和公理得出的定理陈述的证明。

## 相信
%%%
tag := "zh-validatingproofs-h004"
%%%

如果人们相信正式定理陈述与其预期的非正式含义相对应，并相信导入库的作者是 {tech}[诚实]，他们检查了其库中的定理是否表达了其预期的非正式含义，并且没有声明和使用不健全的公理，则此检查是有意义的。

## 保护
%%%
tag := "zh-validatingproofs-h005"
%%%

:::listBullet "🛡️"
这项检查可以防止

* 当前定理的不完整证明（缺少目标，策略错误）
* {lean}`sorry` *在当前定理中*的显式使用
* {tech}[诚实] 元程序和策略中的错误
* 仍在后台检查证据
:::

## 评论
%%%
tag := "zh-validatingproofs-h006"
%%%

在 Visual Studio Code 扩展设置中，可以更改符号。
VS Code 以外的编辑器可能有不同的指示。

运行 {lake}`build`{lit}` +Module`（其中 {lit}`Module` 指的是包含定理的文件），并且观察成功且没有错误消息或警告可提供相同的保证。

# 打印公理
%%%
tag := "validating-printing-axioms"
%%%

即使在定理的依赖关系中明确使用 {lean}`sorry` 或不完整的证明，蓝色双复选标记也会出现。
由于 {lean}`sorry` 和不完整证明都被详细精化为公理，因此可以通过列出证明所依赖的公理来检测它们的存在。

## 指示
%%%
tag := "zh-validatingproofs-h008"
%%%

:::keepEnv
```lean -show
inductive TheoremStatement : Prop where | intro
theorem thmName : TheoremStatement := .intro
```

在定理声明后写入 {leanCommand}`#print axioms thmName`，并将 {lean}`thmName` 替换为定理名称，并检查它是否仅报告内置公理 {name}`propext`、{name}`Classical.choice` 和 {name}`Quot.sound`。

:::

## 意义
%%%
tag := "zh-validatingproofs-h009"
%%%

该命令打印该定理及其所依赖的定理所使用的公理集。
上述三个公理是Lean逻辑的标准公理，并且是良性的。

* 如果报告 {name}`sorryAx`，则该定理或其依赖项之一使用 {lean}`sorry` 或者不完整。
* 如果报告 {name}`Lean.trustCompiler`，则使用本机评估；请参阅下面的讨论。
* 任何其他公理都意味着声明和使用了自定义公理，并且该定理仅相对于这些公理的健全性有效。

## 相信
%%%
tag := "zh-validatingproofs-h010"
%%%

如果人们相信正式定理陈述与其预期的非正式含义相对应，并且相信导入库的作者是 {tech}[诚实]，则此检查是有意义的。

## 保护
%%%
tag := "zh-validatingproofs-h011"
%%%

:::listBullet "🛡️"
（除了上面的列表之外）

* 证明不完整
* 显式使用 {lean}`sorry`
* 自定义公理
:::

# 使用 `lean4checker` 重新检查校样
%%%
tag := "validating-lean4checker"
%%%

有一小类错误和一些不诚实的证明方式，可以通过在构建项目时重新检查存储在 {tech}[`.olean` 文件] 中的证明来捕获。

## 指示
%%%
tag := "zh-validatingproofs-h013"
%%%

使用 {lake}`build` 构建您的项目，在包含感兴趣的定理的模块上运行 `lean4checker --fresh`，并检查是否未报告错误。

## 意义
%%%
tag := "zh-validatingproofs-h014"
%%%

`lean4checker` 工具读取 `lean` 在构建期间存储的声明和证明（{tech}[`.olean` 文件]），并通过内核重播它们。
它相信 {tech}[`.olean` 文件] 结构正确。

## 相信
%%%
tag := "zh-validatingproofs-h015"
%%%

如果人们相信正式定理陈述与其预期的非正式含义相对应，并且相信导入库的作者不是非常狡猾的 {tech}[恶意]，并且既不会损害用户的系统，也不会使用 Lean 的可扩展性来改变定理陈述的解释，则此检查是有意义的。

## 保护
%%%
tag := "zh-validatingproofs-h016"
%%%

:::listBullet "🛡️"
（除了上面的列表之外）

* Lean 对内核状态的核心处理中存在错误（例如，由于并行证明处理或导入处理）
* 元程序或策略故意绕过该状态（例如，使用低级功能添加未经检查的定理）
:::

## 评论
%%%
tag := "zh-validatingproofs-h017"
%%%

由于 `lean4checker` 读取 {tech}[`.olean` 文件] 而不验证其格式，因此此检查很容易导致攻击者制作无效的 `.olean` 文件（例如无效指针、字符串中的无效数据）。

Lean策略和其他元代码在运行时可以执行任意操作。
导入由确定的 {tech}[恶意] 攻击者创建的库并在没有进一步保护的情况下构建它们可能会危及用户的系统，之后无法进行进一步的有意义的检查。

我们建议将 `lean4checker` 作为 CI 的一部分运行，以提供针对 Lean 声明处理中的错误的额外保护，并作为对简单攻击的威慑。
[lean-action](https://github.com/leanprover/lean-action) GitHub 操作通过设置 `lean4checker: true` 提供此功能。

如果没有 `--fresh` 标志，则可以指示该工具仅检查某些模块，并假设其他模块是正确的（例如受信任的库），以加快处理速度。

# 黄金标准：`comparator` 和外部检查器
%%%
tag := "validating-comparator"
%%%

为了防止严重的 {tech}[恶意] 证明损害 Lean 解释定理陈述或用户系统的方式，需要采取额外的步骤。
这应该只适用于高风险场景（证明市场、高奖励证明竞争、不统一的人工智能）。

## 指示
%%%
tag := "zh-validatingproofs-h019"
%%%

在可信环境中，编写定理*陈述*（“挑战”），然后将挑战以及提议的证明提供给 [`comparator`](https://github.com/leanprover/comparator) 工具，并启用外部检查器，如其中所述。

## 意义
%%%
tag := "zh-validatingproofs-h020"
%%%

Comparator 将在沙盒环境中构建证明，以防止构建步骤中的 {tech}[恶意] 代码。
证明项导出为序列化格式。
在沙箱之外并且远离可能的恶意代码，它会验证导出的格式，使用 Lean 的内核和/或外部检查器重放证明，并确保已证明的定理语句与可信挑战文件中的定理语句相匹配。

## 相信
%%%
tag := "zh-validatingproofs-h021"
%%%

如果可信质询文件中的定理语句正确并且用于构建可能的 {tech}[恶意] 代码的沙箱是安全的，则此检查是有意义的。

## 保护
%%%
tag := "zh-validatingproofs-h022"
%%%

:::listBullet "🛡️"
（除了上面的列表之外）

* 主动{tech}[恶意]证明
* 一些（但并非全部）使用的检查器中存在实现错误。
:::

## 评论
%%%
tag := "zh-validatingproofs-h023"
%%%

截至撰写本文时，`comparator` 支持使用官方 Lean内核和独立开发并在 Rust 中实现的外部检查器 [`nanoda`](https://github.com/ammkrn/nanoda_lib)。 [Lean内核Arena](https://arena.lean-lang.org/) 具有更多外部检查器，可以手动使用，以提高信心。

# 剩余问题
%%%
tag := "zh-validatingproofs-h024"
%%%

当遵循使用比较器检查证明的黄金标准时，仍然存在一些假设：

* Lean 逻辑的健全性。
* `comparator` 工具提供的管道是正确的。
* `comparator` 使用的沙箱是安全的。
* 不存在同时影响所有使用的检查器的实现错误。
* 可信质询文件中的定理陈述没有人为错误或误导性表述。

  如果对定理的含义存在疑问，则必须仔细研究其陈述和所有引用的定义，特别是在自定义符号和类型类方面。
  一些外部检查器提供原始的漂亮打印功能，不受源文件中解析器或符号更改的影响。

# 在 `Lean.trustCompiler` 上（最高至 Lean 4.28.0）
%%%
tag := "validating-trustCompiler"
%%%

Lean 支持通过本机评估进行证明。
它由 {tactic}`decide`{keywordOf Lean.Parser.Tactic.decide}` +native`策略或特定策略（特别是 {tactic}`bv_decide`）在内部使用，并生成证明项，调用编译的 Lean 代码来执行计算，然后由内核信任该计算。

{tech}[诚实]策略中包含的特定用途（例如 {tactic}`bv_decide`）通常是值得信赖的。
可信代码库更大（它包括Lean的编译工具链和标准库中的库注释），但仍然是固定的和经过审查的。

当术语的本机评估与内核的评估不一致时，一般使用（{tactic}`decide`{keywordOf Lean.Parser.Tactic.decide}` +native` 或直接使用 {name}`Lean.ofReduceBool`）可用于创建无效证明。
特别是，对于库中的每个 {attr}`implemented_by`/{attr}`extern` 属性，它成为可信代码库的一部分，替换在语义上是等效的。

所有这些用途都在 {keywordOf Lean.Parser.Command.printAxioms}`#print axioms` 中显示为公理 {name}`Lean.trustCompiler`。
外部检查器（`lean4checker`、`comparator`）无法检查此类证明，因为它们无权访问 Lean 编译器。
当需要这种级别的检查时，证明必须避免使用本机评估。

自 Lean 4.29.0 起，{tactic}`decide`{keywordOf Lean.Parser.Tactic.decide}` +native` 和 {tactic}`bv_decide`策略不再使用 {name}`Lean.trustCompiler`，而是为本机计算断言的每个计算引入一个专用公理。 {name}`Lean.trustCompiler` 机器已弃用，最终将被删除。
