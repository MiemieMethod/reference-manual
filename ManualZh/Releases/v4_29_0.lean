/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/

import VersoManual
import Manual.Meta
import Manual.Meta.Markdown

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option linter.typography.quotes false

#doc (Manual) "Lean 4.29.0 (2026-03-27)" =>
%%%
tag := "release-v4.29.0"
file := "v4.29.0"
%%%

此版本有 453 项更改。除了下面列出的 112 项功能添加和 107 项修复之外，还有 30 项重构更改、21 项文档改进、29 项性能改进、26 项测试套件改进和 115 项其他更改。

# 亮点

_Violetta Sim 帮助编写了从 4.16 到 4.29 的发布亮点，Lean 开发人员衷心感谢她的贡献。_


## 性能改进

[#12082](https://github.com/leanprover/lean4/pull/12082) 和
[#12044](https://github.com/leanprover/lean4/pull/12044) 减少
通过直接在二进制文件中存储封闭项来启动时间，其中
可能，并延迟初始化剩余的而不是 at
启动。

[#12406](https://github.com/leanprover/lean4/pull/12406) 显着
减少了 `bv_decide` 中 LRAT 验证检查所消耗的内存。

## 全新可扩展 `do`精化器

[#12459](https://github.com/leanprover/lean4/pull/12459) 添加了一个新的、
可扩展 `do`精化器。用户可以通过以下方式选择新的精化器：
取消设置选项 `backward.do.legacy`。

内置 `doElem` 语法类别的新精化器可以
使用属性 `doElem_elab` 注册。对于新语法，另外
控制信息处理程序必须使用属性注册
`doElem_control_info` 指定是否使用新语法 `return`s
早期，`break`、`continue` 以及它重新分配的 `mut` 变量。

精化器有类型吗
``TS语法 `doElem → DoElemCont → DoElabM Expr``, where `DoElabM` 是
本质上 `TermElabM` 和 `DoElemCont` 代表其余部分如何
`do` 块的结构有待详细说明。请参阅文档字符串了解更多信息
详细信息。

*重大变更：*

- `let pat := rhs | otherwise` 的语法和类似的 now 范围
  超过下面的 `doSeq`。此外，`otherwise` 和
  为了不被窃取，接下来的序列现在是 `doSeqIndented`
  syntax from record syntax.

通过取消设置选择新的 `do`精化器时的*重大更改*
`backward.do.legacy`：

- `do` 表示法现在始终需要 `Pure`。
- `do match` 现在始终是非相关的。有
  `do match (dependent := true)` 扩展为术语匹配
  一些相关用途的解决方法。

## mvcgen：本地上下文中的规范

[#12395](https://github.com/leanprover/lean4/pull/12395) 添加 mvcgen
支持本地环境中的规范。例子：

```
import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

def foo (x : Id Nat → Id Nat) : Id Nat := do
  let r₁ ← x (pure 42)
  let r₂ ← x (pure 26)
  pure (r₁ + r₂)

theorem foo_spec
    (x : Id Nat → Id Nat)
    (x_spec : ∀ (k : Id Nat) (_ : ⦃⌜True⌝⦄ k ⦃⇓r => ⌜r % 2 = 0⌝⦄), ⦃⌜True⌝⦄ x k ⦃⇓r => ⌜r % 2 = 0⌝⦄) :
    ⦃⌜True⌝⦄ foo x ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen [foo, x_spec] <;> grind

def bar (k : Id Nat) : Id Nat := do
  let r ← k
  if r > 30 then return 12 else return r

example : ⦃⌜True⌝⦄ foo bar ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
  mvcgen [foo_spec, bar] -- unfold `bar` and automatically apply the spec for the higher-order argument `k`
```

## grinding：电子匹配中的高阶米勒模式支持

[#12483](https://github.com/leanprover/lean4/pull/12483) 添加支持
用于 `grind` 电子匹配引擎中的高阶米勒模式。
以前，电子匹配模式中的 lambda 参数始终是
被视为 `dontCare`，这意味着它们无法有助于匹配
或绑定模式变量。这是一个重大限制
lambda 参数带有基本结构的定理，例如
`List.foldl`、`List.foldrM` 或任何采用函数的组合器
论点。

通过此更改，当模式参数是 lambda 时，其主体
满足*米勒模式条件* — 即模式变量
仅适用于不同的 lambda 绑定变量 - lambda 是
保存为 `ho[...]` 模式。在实例化时，这些
所有一阶之后，高阶模式通过 `isDefEq` 进行匹配
模式变量已由电子图分配。

*例子*

```
@[grind =] theorem applyFlip_spec (f : Nat → Nat → Nat) (a b : Nat)
    : applyFlip (fun x y => f y x) a b = f b a := sorry
```

模式 `applyFlip ho[fun x => fun y => #2 y x] #1 #0` 捕获
结构上的 lambda 参数：`#2`（`f` 的模式变量）
应用于不同的 lambda 绑定变量 `y` 和 `x`。当
`grind` 遇到 `applyFlip (fun x y => Nat.add y x) 3 4`，它结合
`f := Nat.add` 通过 `isDefEq` 并触发重写。

## 每个本机计算一个公理

[#12217](https://github.com/leanprover/lean4/pull/12217) 实现
RFC [#12216](https://github.com/leanprover/lean4/issues/12216)：本机
计算（{tactic}`native_decide`、{tactic}`bv_decide`）用逻辑表示
作为每次计算的一个公理，断言所获得的相等性
来自本机计算。 `#print axiom` 将不再显示
`Lean.trustCompiler`，而是这些的自动生成的名称
公理（例如，名称中包含 `._native.bv_decide.`）。请参阅
RFC 了解更多信息。

## `inductive`/`structure` 命令中更可靠的 宇宙层级 推理

[#12514](https://github.com/leanprover/lean4/pull/12514) 改进
宇宙层级 `inductive` 和 `structure` 命令的推断
更加可靠并产生更好的错误消息。查看公关
描述以获取更多信息。

*重大更改。* 宇宙层级 元变量仅存在于
构造函数字段不再提升为 宇宙层级
参数：使用显式 宇宙层级 参数。此次促销活动是
不一致的完成取决于归纳类型的宇宙是否
level 有一个元变量，也给用户带来了困惑，
因为这些 宇宙层级 不受类型前者的约束
参数。

*重大更改。*现在递归类型不算“明显的”
`Prop` 候选人”。使用显式 `Prop` 类型前注释
递归归纳谓词。

## 更简单的 `noncomputable` 语义

[#12028](https://github.com/leanprover/lean4/pull/12028) 给出
`noncomputable` 的语义更简单，同时也提高了可预测性
准备将代码生成移动到单独的构建步骤中，而无需
打破错误消息的立即生成。

具体来说，现在每当公理或
另一个 `noncomputable` def 由 def 使用，但以下情况除外
特殊情况：

- 使用内部证明、类型、类型形成器和构造函数参数
  对应于（固定）感应参数被忽略
- 标记为 `@[extern]/@[implemented_by]/@[csimp]` 的函数的用途是
  被忽略
- 对于标记为 `@[macro_inline]` 的功能的应用，
  相反，检查内联的不可计算性

*重大更改*：此更改后，更多 `noncomputable`
可能需要比以前更多的注释来换取改进
未来的稳定。

## 实例和还原性处理的更改

v4.29.0 对还原性设置的处理带来了重大且突破性的变化。
我们解决了一个长期存在的问题：在 v4.29.0 之前，`isDefEq` 算法会影响
透明度级别高达 `.default`（即愿意展开默认透明度定义）
比较隐式参数时。

这是一个严重的问题，导致立即出现不可预测的性能问题
`isDefEq`，并隐藏了下游库中发生定义滥用的许多地方。

为了确保可扩展性并解决这些定义滥用问题，我们有
在 [#12179](https://github.com/leanprover/lean4/pull/12179) 中做出了相当颠覆性的改变，
删除此透明度级别凹凸作为默认路径。

比较隐式参数时透明度凹凸的变化可以通过两种方式控制：
* 可以使用新的 `@[implicit_reducible]` 属性来标记定义。
  这是 `@[reducible]` 和 `@[semireducible]` 之间的中间值（即默认设置），
  因为该定义大多被视为半可简化的，除非正在处理 `isDefEq`
  隐式参数或匹配判别式。
  请参见 [#12247](https://github.com/leanprover/lean4/pull/12247) 和 [#12567](https://github.com/leanprover/lean4/pull/12567)。
* 选项 `set_option backward.isDefEq.respectTransparency false` 恢复 `v4.29.0` 之前的行为
  （等效地，所有半可约定义都被视为 `implicit_reducible`）。
  作为向后兼容选项，这最终可能会被删除，但考虑到这一变化的破坏性，我们预计会在中期保留该选项。


由于透明度处理的这些变化，下游库中现有的定义滥用问题现在在某些地方浮现出来
以前他们没有。为了帮助解决这些问题，主要但不限于：
是由错误实现的类型类实例引起的，我们在 [#12897](https://github.com/leanprover/lean4/pull/12897) 中进行了更改
`inferInstanceAs` 和默认的 `deriving` 处理程序。
这些确保使用它们创建的实例不会泄漏所涉及类型的定义，
当实例以低于半可缩减的透明度缩减时。

`inferInstanceAs α` 合成 `α` 类型的实例，但现在对其进行调整以符合
预期类型 `β`，它必须可以从上下文推断出来。

例子：
```
def D := Nat
instance : Inhabited D := inferInstanceAs (Inhabited Nat)
```

该调整将确保生成的实例在以下情况下不会泄漏 RHS `Nat`：
在低于 `semireducible` 的透明度级别时减少，即 `D` 也不会展开。

更具体地说，给定源类型（参数）和目标类型（预期类型），
`inferInstanceAs` 合成源类型的实例，然后展开并重新包装其
根据需要添加组件（字段、嵌套实例）以使它们与目标类型兼容。的
各个步骤由以下选项表示，这些选项均默认启用并且可以
禁用以帮助移植：

* `backward.inferInstanceAs.wrap`：`inferInstanceAs` 中的实例调整的主开关
  和默认的派生处理程序
* `backward.inferInstanceAs.wrap.reuseSubInstances`：重用目标类型的现有实例
  对于子实例字段以避免非 defeq 实例菱形
* `backward.inferInstanceAs.wrap.instances`：将不可约实例包装在辅助定义中
* `backward.inferInstanceAs.wrap.data`：将数据字段包装在辅助定义中（证明字段是
  总是包裹着）

如果您只需要合成一个实例而不需要在类型之间进行传输，请使用 `inferInstance`
相反，可能带有预期类型的类型注释。

`v4.29.0` 中的第三个重大变化是 `simp` 和 `dsimp` 不再处理类型类实例。
此行为会产生非标准实例，并导致 Mathlib 出现问题。
请参见 [#12244](https://github.com/leanprover/lean4/pull/12244) 和 [#12195](https://github.com/leanprover/lean4/pull/12195)。
可以恢复旧的行为

```
set_option backward.dsimp.instances true
```

或 `simp +instances` 为 `simp`。然而，到目前为止，我们的经验是，这并不经常需要。

最后我们在 [#12172](https://github.com/leanprover/lean4/pull/12172) 中解决了一个问题
我们确定函数参数是否是实例，这对依赖于该分类的多种算法具有后续影响。
这可能会导致潜在的回归：自动化现在可能表现不同
在以前错误识别实例参数的情况下。
例如，`simp` 中的重写规则由于以下原因而未触发
现在可能会触发不正确的索引。

### 迁移指南

任何想要推迟处理透明度级别变化所需的调整的项目都可以
只需使用 `set_option backward.isDefEq.respectTransparency false`。

这可以在 `lakefile.toml` 中的项目范围级别上进行设置：
```
[leanOptions]
backward.isDefEq.respectTransparency = false
```

但是，我们鼓励您在需要它的文件中本地化该选项，
甚至在使用 `set_option backward.isDefEq.respectTransparency false in ...` 的个人声明上。
这使得开始识别代码中定义的滥用问题变得更加容易。

如果您的项目位于 Mathlib 的下游，您可能会发现以下两个脚本很有用：
* `scripts/add_set_option.py`（如果您有 Mathlib 作为依赖项，则可在 `.lake/packages/mathlib/scripts/add_set_option.py` 中使用）
  它尝试编译您的项目，并自动用 `set_option backward.isDefEq.respectTransparency false in ...` 包装任何失败的声明，
  在这种情况下，这样做可以解决失败。
* `scripts/rm_set_option.py`，它编译您的项目并识别所有出现的 `set_option backward.isDefEq.respectTransparency false in ...`，可以将其删除而不会导致失败（在同一声明中）。
  发生这种情况可能是因为之前的更改解决了定义滥用问题。

这些脚本也可以从 Mathlib 中复制出来并在任何项目上运行。

同样，当 Mathlib 下游时，您还可以使用实验性 `#defeq_abuse in ...` 命令，
它试图识别和解释，或者至少提供线索，潜在的定义滥用问题
可以解释为什么声明当前需要 `set_option backward.isDefEq.respectTransparency false in ...`。
我们鼓励用户在 [Zulip](https://leanprover.zulipchat.com/) 上报告此命令的问题，
我们希望，随着此诊断命令的稳定，我们能够将其作为未来 Lean 工具链的一部分提供。

我们鼓励您检查项目中所有默认透明度类型同义词的实例构造。
如果可能，您应该使用 `deriving` 处理程序，或新的 `inferInstanceAs`精化器，
而不是编写需要展开类型同义词才能进行类型检查的术语模式结构。
`inferInstanceAs` 命令现在“需要”预期类型。
如果您遇到错误，其中 `inferInstanceAs` 现在由于未提供预期类型而给出错误，
您可能会发现您应该简单地使用 `inferInstance` 来代替。

## 宇宙层级 作为输出参数

[#12423](https://github.com/leanprover/lean4/pull/12423) 添加
attribute `@[univ_out_params]` for specifying which universe levels
应被视为输出参数。默认情况下，任何 宇宙层级
任何输入参数中都没有出现的被视为输出
参数。

## 图书馆亮点

此版本包括一个新的字符串搜索基础架构，使用
对字符统一工作的多态模式系统，
谓词和字符串。看：

- [#12333](https://github.com/leanprover/lean4/pull/12333) 添加
  将用于验证我们的基本类型类
  字符串搜索基础设施。

- [#12424](https://github.com/leanprover/lean4/pull/12424) 给出
  `Slice` 模式的 `LawfulToForwardSearcherModel` 证明，其中
  等于证明我们实施的KMP是正确的。

该库还添加了各种内容，包括：

- [#11938](https://github.com/leanprover/lean4/pull/11938) 介绍
  投影最小值和最大值，也称为“argmin/argmax”，用于
  列在名称 `List.minOn` 和 `List.maxOn` 下。还介绍了
  `List.minIdxOn` 和 `List.maxIdxOn`，返回索引
  最小或最大元素。

- [#11994](https://github.com/leanprover/lean4/pull/11994) 提供
  更多关于列表/数组/向量之和的引理，尤其是
  `Nat` 或 `Int` 列表/数组/向量。

- [#12363](https://github.com/leanprover/lean4/pull/12363) 介绍
  通过 `Vector.iter` 和 `Vector.iterM` 的向量迭代器
  与通常的引理。

- [#12452](https://github.com/leanprover/lean4/pull/12452) 上游
  `List.scanl`、`List.scanr` 及其引理从电池到
  标准库。

## Lake 的新功能

- [#12203](https://github.com/leanprover/lean4/pull/12203) 更改
  从本地缓存传输工件，优先选择硬链接
  副本，当硬链接失败时（例如，在
  不同的文件系统）。缓存工件现在标记为只读
  防止通过硬链接路径意外损坏。

- [#12444](https://github.com/leanprover/lean4/pull/12444) 添加
  Lake CLI 命令 `lake cache clean`，删除 Lake 缓存
  目录。

- [#12490](https://github.com/leanprover/lean4/pull/12490) 添加一个
  系统范围的 Lake 配置文件并使用它来配置
  `lake cache` 使用的远程缓存服务。

# 语言

* [#11963](https://github.com/leanprover/lean4/pull/11963) 更积极地激活 `getElem?_pos`，由 `c[i]` 触发。

* [#12028](https://github.com/leanprover/lean4/pull/12028) 为 `noncomputable` 提供了更简单的语义，改进了
  可预测性以及准备将代码生成移至单独的
  构建步骤不会中断错误消息的立即生成。

* [#12110](https://github.com/leanprover/lean4/pull/12110) 修复了在 `x86_64` 上对 `(ISize.minValue
  / -1 : ISize)` 求值时的 SIGFPE 崩溃，填补了 #11624 中的遗漏。

* [#12159](https://github.com/leanprover/lean4/pull/12159) 通过扩展到
  `PUnit.unit` 而不是 `()`。

* [#12160](https://github.com/leanprover/lean4/pull/12160) 删除了我们期望在正常情况下传递的对 `check` 的调用
  情况。这可以稍后重新添加，由 `debug` 选项保护。

* [#12164](https://github.com/leanprover/lean4/pull/12164) 在证明一个方向时使用 `.inj` 定理
  `.injEq` 定理。

* [#12179](https://github.com/leanprover/lean4/pull/12179) 确保 `isDefEq` 不会将透明度模式增加到
  `.default` 检查隐式参数是否定义时
  平等。以前的行为造成了可扩展性问题
  Mathlib。也就是说，这是一个非常具有颠覆性的变化。上一个
  可以使用命令恢复行为
  ```
  set_option backward.isDefEq.respectTransparency false
  ```

* [#12184](https://github.com/leanprover/lean4/pull/12184) 确保 `mspec`策略不会分配合成不透明
  MVar 发生在目标中，就像 `apply`策略一样。

* [#12190](https://github.com/leanprover/lean4/pull/12190) 添加了 `introSubstEq` MetaM策略，作为对
  `intro h; subst h`，如果可以的话，避免引入 `h : a = b`
  避免,
  当 `b` 可以在不恢复任何内容的情况下恢复时，就是这种情况
  否则。加速 `injEq` 定理的生成。

* [#12217](https://github.com/leanprover/lean4/pull/12217) 实现 RFC #12216：本机计算 (`native_decide`，
  `bv_decide`) 在逻辑中表示为每次计算一个公理，
  断言从本机计算获得的相等性。
  `#print axiom` 将不再显示 `Lean.trustCompiler`，而是显示
  这些公理的自动生成的名称（例如，
  名称中的 `._native.bv_decide.`）。请参阅 RFC 了解更多信息。

* [#12219](https://github.com/leanprover/lean4/pull/12219) 修复了出现在
  `Lean.Meta.MkIffOfInductiveProp` 的上游机械
  Mathlib。在 `toInductive` 内部，传递了错误的自由变量，
  这使得在某些情况下无法进行统一。

* [#12236](https://github.com/leanprover/lean4/pull/12236) 将 `orElse` 组合器添加到 `Sym.Simp` 的 simprocs 中。

* [#12243](https://github.com/leanprover/lean4/pull/12243) 修复了 #12240，其中 `deriving Ord` 因
  `Unknown identifier a✝` 失败。

* [#12247](https://github.com/leanprover/lean4/pull/12247) 添加新的透明度设置 `@[instance_reducible]`。我们
  用于检查声明是否具有 `instance` 可还原性，方法是使用
  `isInstance` 谓词。然而，这并不是一个可靠的解决方案
  因为：

  - 我们有作用域实例，并且仅当 `isInstance` 返回 `true`
  范围处于活动状态。

* [#12263](https://github.com/leanprover/lean4/pull/12263) 实现#12247 的第二部分。

* [#12269](https://github.com/leanprover/lean4/pull/12269) 通过设置 `isRecursive` 环境扩展来改进 #12106
  添加声明之后，但在处理属性之前，例如
  `macro_inline` 表示想看一下标志。修复#12268。

* [#12283](https://github.com/leanprover/lean4/pull/12283) 引入了允许标记的 `cbv_opaque` 属性
  `cbv`策略不会展开定义。

* [#12285](https://github.com/leanprover/lean4/pull/12285) 为类 宇宙层级 的位置实现缓存
  仅出现在输出参数类型中的参数。

* [#12286](https://github.com/leanprover/lean4/pull/12286) 确保类型解析缓存正确缓存结果
  包含输出参数的类型类。

* [#12324](https://github.com/leanprover/lean4/pull/12324) 将默认 `Inhabited` 实例添加到 `Theorem` 类型。

* [#12325](https://github.com/leanprover/lean4/pull/12325) 向任何不包含该类类型的 `def` 添加警告
  声明适当的还原性。

* [#12329](https://github.com/leanprover/lean4/pull/12329) 添加选项 `doc.verso.module`。如果设置，它控制是否
  模块文档字符串使用 Verso 语法。如果未设置，则默认为该值
  `doc.verso` 选项的。

* [#12338](https://github.com/leanprover/lean4/pull/12338) 实施#12179 的准备工作。它实现了一个新的
  `isDefEq` 中的功能确保它不会增加透明度
  检查隐式的定义等价性时，级别为 `.default`
  论据。 Lean 3 中引入了这种透明度级别凹凸，但它
  不是性能问题，并且正在影响 Mathlib。添加了
  新功能，但默认情况下处于禁用状态。

* [#12339](https://github.com/leanprover/lean4/pull/12339) 修复了 Delta 导出中的钻石问题，其中
  派生实例类型中的实例隐式类参数为
  使用为基础类型而不是别名类型合成的实例。

* [#12340](https://github.com/leanprover/lean4/pull/12340) 实现了对标记为的展开类字段的更好支持
  `reducible`。例如，我们想要标记以下类型的字段
  ```
  MonadControlT.stM : Type u -> Type u
  ```
  动机类似于我们的启发式，类型定义应该
  是缩写。
  现在，假设我们要使用以下内容展开 `stM m (ExceptT ε m) α`
  `.reducible` 透明度设置，我们希望结果为`stM m m
  (MonadControl.stM m (ExceptT ε m) α)` 而不是
  `(instMonadControlTOfMonadControl m m (ExceptT ε m)).1 α`。后者
  将违背将字段标记为可约的意图，因为
  instance `instMonadControlTOfMonadControl` is `[instance_reducible]` and
  使用 `.reducible` 透明度时，结果项将被卡住
  模式。

* [#12353](https://github.com/leanprover/lean4/pull/12353) 通过重定向来恢复死跟踪类 `Elab.resume`
  `Elab.resuming` 不存在。

* [#12355](https://github.com/leanprover/lean4/pull/12355) 将 `isBoolTrueExpr` 和 `isBoolFalseExpr` 功能添加到 `SymM`

* [#12391](https://github.com/leanprover/lean4/pull/12391) 公开 `simpCond`。需要避免代码重复
  在 #12361

* [#12395](https://github.com/leanprover/lean4/pull/12395) 添加了对本地上下文中的规范的 `mvcgen` 支持。
  示例：

  ```
  import Std.Tactic.Do

  open Std.Do

  set_option mvcgen.warning false

  def foo (x : Id Nat → Id Nat) : Id Nat := do
    let r₁ ← x (pure 42)
    let r₂ ← x (pure 26)
    pure (r₁ + r₂)

  theorem foo_spec
      (x : Id Nat → Id Nat)
      (x_spec : ∀ (k : Id Nat) (_ : ⦃⌜True⌝⦄ k ⦃⇓r => ⌜r % 2 = 0⌝⦄), ⦃⌜True⌝⦄ x k ⦃⇓r => ⌜r % 2 = 0⌝⦄) :
      ⦃⌜True⌝⦄ foo x ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
    mvcgen [foo, x_spec] <;> grind

  def bar (k : Id Nat) : Id Nat := do
    let r ← k
    if r > 30 then return 12 else return r

  example : ⦃⌜True⌝⦄ foo bar ⦃⇓r => ⌜r % 2 = 0⌝⦄ := by
    mvcgen [foo_spec, bar] -- unfold `bar` and automatically apply the spec for the higher-order argument `k`
  ```

* [#12407](https://github.com/leanprover/lean4/pull/12407) 与#12403 类似。

* [#12416](https://github.com/leanprover/lean4/pull/12416) 公开 `Sym.Simp.toBetaApp`。这是必要的
  在 #12417 中重构主要 `cbv` simproc。

* [#12425](https://github.com/leanprover/lean4/pull/12425) 修复了 `mvcgen` 中因 `match` 拆分不完整而导致的错误。

* [#12427](https://github.com/leanprover/lean4/pull/12427) 使 `mvcgen` 建议使用 `-trivial`，这样做可以避免
  递归深度错误。

* [#12429](https://github.com/leanprover/lean4/pull/12429) 在生成方程之前设置 `irreducible` 属性
  用于递归定义。这可以防止这些方程被标记为
  `defeq`，这可能导致不键入 `simp` 生成证明
  检查默认透明度。

* [#12451](https://github.com/leanprover/lean4/pull/12451) 为新的 do精化器调用提供必要的挂钩
  进入 let 并匹配精化器。

* [#12459](https://github.com/leanprover/lean4/pull/12459) 添加了新的可扩展 `do`精化器。用户可以选择加入
  通过取消选项 `backward.do.legacy` 来创建新的精化器。

* [#12460](https://github.com/leanprover/lean4/pull/12460) 修复了 `cbv`策略中的 `AppBuilder` 异常
  简化投影函数相关的投影（关闭
  #12457).

* [#12507](https://github.com/leanprover/lean4/pull/12507) 修复了方程定理生成失败的 #12495
  使用类似 Box 的包装器进行结构递归定义
  嵌套归纳法。

* [#12514](https://github.com/leanprover/lean4/pull/12514) 改进了 `inductive` 的 宇宙层级 推理，
  `structure` 命令更可靠并产生更好的错误
  消息。回想一下，归纳类型的主要约束是，如果
  `u` 是类型的 宇宙层级 和 `u > 0`，则每个
  构造函数字段的 宇宙层级 `v` 满足 `v ≤ u`，其中
  *构造函数字段*是一个不是该类型的参数之一
  *参数*（回想一下：类型的参数是
  类型前者和所有构造函数共享的参数）。给定
  对于此约束，`inductive`精化器尝试找到合理的
  对可能存在的元变量的赋值：
  - 对于 宇宙层级 `u`，选择一个分配，使其
  最低级别是合理的，只要它是唯一的。
  - 对于构造函数字段，选择唯一赋值通常是
  合理。
  - 对于类型的参数，将级别元变量提升为新的
  宇宙层级参数合理。

* [#12524](https://github.com/leanprover/lean4/pull/12524) 添加了 `Std.Iter.toHashSet` 和变体。

* [#12525](https://github.com/leanprover/lean4/pull/12525) 将声明名称添加到leanchecker 错误消息中，以使
  当内核拒绝声明时调试更容易。

* [#12530](https://github.com/leanprover/lean4/pull/12530) 改进了 `mvcgen` 无法解析名称时的错误消息
  规范定理。

* [#12538](https://github.com/leanprover/lean4/pull/12538) 为 v4.29 启用 `backward.whnf.reducibleClassField`。

* [#12558](https://github.com/leanprover/lean4/pull/12558) 修复了 `(kernel) declaration has metavariables` 错误
  在从属归纳类型索引中使用 `by`策略时发生
  引用先前的索引：

  ```
  axiom P : Prop
  axiom Q : P → Prop
  -- Previously gave: (kernel) declaration has metavariables 'Foo'
  inductive Foo : (h : P) → (Q (by exact h)) → Prop
  ```

* [#12564](https://github.com/leanprover/lean4/pull/12564) 修复了 `getStuckMVar?` 以通过以下方式检测卡住的元变量
  为钻石继承创建的辅助父投影。这些
  强制转换（例如 `AddMonoid'.toAddZero'`）未注册为常规
  预测，因为它们根据个体构建父值
  字段而不是提取单个字段。此前，
  `getStuckMVar?`遇到他们就会放弃，防止TC
  合成被触发。

* [#12567](https://github.com/leanprover/lean4/pull/12567) 将 `instance_reducible` 重命名为 `implicit_reducible` 并添加
  新的
  `backward.isDefEq.implicitBump` 选项，为治疗所有疾病做好准备
  隐含的
  在 定义等价 检查期间统一参数。

* [#12572](https://github.com/leanprover/lean4/pull/12572) 是 `implicit_reducible` 重构的第 2 部分（第 1 部分：
  #12567）。

* [#12574](https://github.com/leanprover/lean4/pull/12574) 将 `SpecTheorems.add` 重命名为 `SpecTheorems.insert`

* [#12576](https://github.com/leanprover/lean4/pull/12576) 将 `Sym.mkPatternFromDeclWithKey` 添加到 Sym API 中以进行泛化
  并实施`Sym.mkEqPatternFromDecl`。这对于实施很有用
  自定义重写类似策略想要使用 `Pattern`
  判别树查找。

* [#12621](https://github.com/leanprover/lean4/pull/12621) 修复了绕过 `reduceRecMatcher?` 和 `reduceProj?` 的错误
  `@[cbv_opaque]` 属性。这些内核级还原函数
  内部使用 `whnf`，它不知道 `@[cbv_opaque]`。这个
  意味着 `@[cbv_opaque]` 值在匹配时展开
  判别式、递归主前提或投影目标。修复
  引入了 `withCbvOpaqueGuard`，它将这些调用包装为
  `withCanUnfoldPred` 防止 `whnf` 展开 `@[cbv_opaque]`
  定义。

* [#12633](https://github.com/leanprover/lean4/pull/12633) 使 `isDefEqProj` 将透明度提高到 `.instances`（通过
  `withInstanceConfig`) 比较类的结构参数时
  预测。这使得行为与 `isDefEqArgs` 一致，
  它已经对实例隐式参数应用了相同的凹凸
  在比较功能应用程序时。

* [#12639](https://github.com/leanprover/lean4/pull/12639) 修复了之间的交互
  `backward.whnf.reducibleClassField` 和 `isDefEqDelta`
  论证比较启发式。

* [#12650](https://github.com/leanprover/lean4/pull/12650) 修复了通过启用
  `backward.whnf.reducibleClassField`
  (https://github.com/leanprover/lean4/pull/12538)。的
  `ExprDefEq` 中的 `isNonTrivialRegular` 函数是分类类
  在所有透明度级别上的预测都是不平凡的，但额外的
  `.instances` `unfoldDefault` 的减少激发了这一点
  分类仅适用于 `.reducible` 透明度。在较高的
  透明度级别，不平凡的分类导致不必要的
  `isDefEqDelta` 中级联的启发式比较尝试
  BitVec 减少，导致 `Lean.Data.Json.Parser` 的精化
  从 ~3.6G 指令翻倍到 ~7.2G。

* [#12698](https://github.com/leanprover/lean4/pull/12698) 将 `result? : Option TraceResult` 字段添加到 `TraceData` 并
  将其填充到 `withTraceNode` 和 `withTraceNodeBefore` 中，以便
  元程序行走跟踪树可以决定成功/失败
  在结构上而不是表情符号上的字符串匹配。

* [#12699](https://github.com/leanprover/lean4/pull/12699) 给出 `generate` 函数的“将 @Foo 应用到目标”跟踪节点
  他们自己的跟踪子类 `Meta.synthInstance.apply` 而不是共享
  父类 `Meta.synthInstance`。

* [#12701](https://github.com/leanprover/lean4/pull/12701) 修复了如何将 `@[implicit_reducible]` 分配给父级的问题
  结构精化期间的投影。

* [#12719](https://github.com/leanprover/lean4/pull/12719) 将 `levelZero`、`levelOne` 和 `Level.ofNat` 标记为
  `@[implicit_reducible]` 使得 `Level.ofNat 0 =?= Level.zero` 成功时
  定义等价 检查器尊重透明度注释。

* [#12756](https://github.com/leanprover/lean4/pull/12756) 添加 `deriving noncomputable instance` 语法，以便
  增量派生实例可以标记为不可计算。

* [#12789](https://github.com/leanprover/lean4/pull/12789) 在以下情况下跳过 `deriving instance` 中不可计算的预检查
  实例类型为 `Prop`，因为编译器会删除证明并且
  可计算性是无关紧要的。

* [#12778](https://github.com/leanprover/lean4/pull/12778) 修复了 `getStuckMVar?` 中实例的不一致问题
  类投影函数和辅助父投影的参数
  在检查卡住的元变量之前未进行 whnf 标准化。每个
  `getStuckMVar?` 中的其他情况（递归器、商递归器、`.proj`
  节点）在递归之前通过 `whnf` 标准化主要参数 — 类
  投影函数和辅助父投影是例外。

* [#12897](https://github.com/leanprover/lean4/pull/12897) 调整 `inferInstanceAs` 和 `def` `deriving` 的结果
  处理程序以符合最近加强的可还原性限制。
  当派生或推断半可简化类型定义的实例时，
  当实例减少时，定义的 RHS 不再泄漏
  低于半还原透明度。合成实例的组件
  （字段、嵌套实例）根据需要展开和重新包装。

* [#13043](https://github.com/leanprover/lean4/pull/13043) 修复了 `inferInstanceAs` 和默认 `deriving` 的错误
  处理程序，当在 `meta section` 内部使用时，将创建辅助
  未标记为 `meta` 的定义（通过 `normalizeInstance`）。
  这导致编译器拒绝父 `meta` 定义：

  ```
  Invalid `meta` definition `instEmptyCollectionNamePrefixRel`, `instEmptyCollectionNamePrefixRel._aux_1` not marked `meta`
  ```

* [#13059](https://github.com/leanprover/lean4/pull/13059) 切换由以下命令创建的辅助定义的元标记
  `normalizeInstance` 从使用 `isMetaSection` 到 `declName?` 模式，
  修复了元部分中的 `deriving` 由于辅助定义而失败的错误
  被错误地标记为 `meta`，而实例本身则没有。

# 图书馆

* [#11811](https://github.com/leanprover/lean4/pull/11811) 证明擦除Dups 保留了成员身份：一个元素
  存在于重复数据删除列表中，前提是它存在于原始列表中。

* [#11832](https://github.com/leanprover/lean4/pull/11832) 使用 `Array` 而不是 `List` 将子句存储在
  `Std.CNF`。这减少了内存占用和压力
  分配器，导致巨大的 CNF 出现显着的性能变化。

* [#11936](https://github.com/leanprover/lean4/pull/11936) 提供与 `List.min(?)` 类似的 `Array` 操作
  `List.max(?)`。

* [#11938](https://github.com/leanprover/lean4/pull/11938) 引入投影最小值和最大值，也称为
  “argmin/argmax”，对于名称为 `List.minOn` 的列表和
  `List.maxOn`。它还介绍了`List.minIdxOn`和`List.maxIdxOn`，
  返回最小或最大元素的索引。而且，
  有一些带有 `?` 后缀的变体返回 `Option`。改变
  进一步引入了相反顺序的新实例，例如
  `LE.opposite`、`IsLinearOrder.opposite` 等。更改还添加了
  缺少 `Std.lt_irrefl` 引理。

* [#11943](https://github.com/leanprover/lean4/pull/11943) 介绍定理
  `BitVec.sshiftRight_eq_setWidth_extractLsb_signExtend` 定理，证明
  `x.sshiftRight n` 相当于第一次符号扩展 `x`，提取
  适当的最低有效位，然后设置宽度
  至 `w`。

* [#11994](https://github.com/leanprover/lean4/pull/11994) 提供更多关于列表/数组/向量之和的引理，
  特别是 `Nat` 或 `Int` 列表/数组/向量的总和。

* [#12017](https://github.com/leanprover/lean4/pull/12017) 对列表/数组/向量 API 进行了一些小改进：
  * 它修复了 `Init.Core` 中的拼写错误。
  * 它添加了 `List.isSome_min_iff` 和 `List.isSome_max_iff`。
  * 它将 `grind` 和 `simp` 注释添加到以前的各种注释中
  未注释的引理。
  * 它添加了引理，用于用索引 `∃
  (i : Nat), ∃ hi, P (xs[i])` 表征 `∃ x ∈ xs, P x`，以及类似的全称量化引理：
  `exists_mem_iff_exists_getElem` 和 `forall_mem_iff_forall_getElem`。
  * 它添加了 `Vector.toList_zip`。
  * 它为列表/数组/向量添加了 `map_ofFn` 和 `ofFn_getElem`。

* [#12019](https://github.com/leanprover/lean4/pull/12019) 提供 `Nat`/`Int` 引理 `x ≤ y * z ↔ (x + z - 1) / z ≤
  y`, `x ≤ y * z ↔ (x + y - 1) / y ≤ z` and `x / z + y / z ≤ (x + y) / z`。

* [#12108](https://github.com/leanprover/lean4/pull/12108) 添加 `prefix_map_iff_of_injective` 和
  `suffix_map_iff_of_injective` 引理到 Init.Data.List.Nat.Sublist。

* [#12161](https://github.com/leanprover/lean4/pull/12161) 添加 `Option.of_wp_eq` 和 `Except.of_wp_eq`，类似于
  现有 `Except.of_wp`。 `Except.of_wp` 已弃用，因为应用
  需要先进行泛化，此时比较方便
  使用 `Except.of_wp_eq`。

* [#12162](https://github.com/leanprover/lean4/pull/12162) 添加函数 `Std.Iter.first?` 并验证规范
  如果迭代器有效，则引理 `Std.Iter.first?_eq_match_step`。

* [#12170](https://github.com/leanprover/lean4/pull/12170) 调整 List.take/drop 的研磨注释，并添加两个
  定理。

* [#12181](https://github.com/leanprover/lean4/pull/12181) 为 `Int` 添加两个缺失的订单实例。

* [#12193](https://github.com/leanprover/lean4/pull/12193) 为 `Sigma` 和 `PSigma` 添加 `DecidableEq` 实例。

* [#12204](https://github.com/leanprover/lean4/pull/12204) 添加了显示 `find?` 和
  各种索引查找功能。定理建立双向
  查找元素和查找其索引之间的关系。

* [#12212](https://github.com/leanprover/lean4/pull/12212) 添加函数 `Std.Iter.isEmpty` 并证明
  规范引理 `Std.Iter.isEmpty_eq_match_step` 和
  `Std.Iter.isEmpty_toList`（如果迭代器有效）。

* [#12220](https://github.com/leanprover/lean4/pull/12220) 修复了 Windows 和 `IO.Process.spawn` 上的错误，其中设置
  环境变量为空字符串不会设置环境
  variable on the subprocess.

* [#12234](https://github.com/leanprover/lean4/pull/12234) 引入了一个 `Iter.step_eq` 引理，它完全展开了
  `Iter.step` 调用，绕过层层展开。

* [#12249](https://github.com/leanprover/lean4/pull/12249) 添加了一些关于 `sum`、`min` 和 `max` 相互作用的引理
  关于列表中已经存在的数组。

* [#12250](https://github.com/leanprover/lean4/pull/12250) 引入定义等式 `Triple.iff` 并将其用于
  证明而不是依赖 定义等价。还介绍了
  `Triple.iff_conseq` 对于向后推理很有用，并介绍了
  验证条件。类似地，`Triple.entails_wp_*` 定理是
  引入用于向后推理，其中目标是有状态的
  蕴涵而不是三元组。

* [#12258](https://github.com/leanprover/lean4/pull/12258) 添加定理，直接说明 div 和 mod 形成
  单射对：如果 `a / n = b / n` 和 `a % n = b % n` 那么 `a = b`。
  这些补充了现有的 div/mod 引理并且对于扩展很有用
  论据。

* [#12277](https://github.com/leanprover/lean4/pull/12277) 添加 `IO.FS.Metadata.numLinks`，其中包含
  到文件的硬链接。

* [#12281](https://github.com/leanprover/lean4/pull/12281) 将 `Squash` 的定义更改为使用 `Quotient`
  上游
  [`true_equivalence`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#true_equivalence)
  （现为 `equivalence_true`）和
  [`trueSetoid`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html#trueSetoid)
  （现为 `Setoid.trivial`）。新定义相对于旧定义来说是 def-eq，但是
  确保只要 `Quotient` 参数是，就可以使用 `Squash`
  无需显式提供 setoid 即可实现预期效果。

* [#12282](https://github.com/leanprover/lean4/pull/12282) 修复了 `IO.FS.removeFile` 中的平台不一致问题
  无法删除 Windows 上的只读文件。

* [#12290](https://github.com/leanprover/lean4/pull/12290) 将 `PredTrans.apply` 结构字段移动到单独的
  `def`。这样做可以提高内核的还原速度，因为内核是
  与结构域相比，不太可能展开定义
  预测。这会导致 `simp` 正常形式发生微小变化。

* [#12301](https://github.com/leanprover/lean4/pull/12301) 介绍功能 `(String|Slice).posGE` 和
  `(String|Slice).posGT` 将全面验证并弃用
  `Slice.findNextPos` 支持 `Slice.posGT`。

* [#12305](https://github.com/leanprover/lean4/pull/12305) 添加了有关基本类型的各种无趣引理，已提取
  从KMP验证。

* [#12311](https://github.com/leanprover/lean4/pull/12311) 公开链和 `is_sup` 定义，以便其他模块
  可以声明自定义 CCPO 实例。

* [#12312](https://github.com/leanprover/lean4/pull/12312) 颠倒了 `ForwardPattern` 和
  `ToForwardSearcher` 类。

* [#12318](https://github.com/leanprover/lean4/pull/12318) 避免未对齐时 `String.Slice.hash` 中的未定义行为
  子串。
  这可能会在某些 Arm 平台上产生 SIGILL。

* [#12322](https://github.com/leanprover/lean4/pull/12322) 添加了 `String.Slice.Subslice`，它是
  `String.Slice`。

* [#12333](https://github.com/leanprover/lean4/pull/12333) 添加将在验证中使用的基本类型类
  我们的字符串搜索基础设施。

* [#12341](https://github.com/leanprover/lean4/pull/12341) 添加了一些我们之后需要的统一提示
  `backward.isDefEq.respectTransparency` 默认为 `true`。

* [#12346](https://github.com/leanprover/lean4/pull/12346) 显示 `s == t ↔ s.copy = t.copy` 对于 `s t : String.Slice` 和
  将右侧建立为 simpl 范式。

* [#12349](https://github.com/leanprover/lean4/pull/12349) 基于 #12333 构建并证明 `Char` 和 `Char -> Bool`
  模式是合法的。

* [#12352](https://github.com/leanprover/lean4/pull/12352) 使用 `drop`/`take` 操作的引理改进了切片 API
  关于 `Subarray` 以及更多关于 `Std.Slice.fold`、`Std.Slice.foldM` 的引理
  和 `Std.Slice.forIn`。它还更改了 `simp` 和 `grind`
  `Slice` 相关引理的注释。切片之间转换的引理
  不同形状的不再是 `simp`/`grind` 注释，因为它们
  通常引理很复杂并且阻碍了自动化。

* [#12358](https://github.com/leanprover/lean4/pull/12358) 改进了 `simp` 和 `grind` 规则框架
  `PredTrans.apply` 并根据
  公约。

* [#12359](https://github.com/leanprover/lean4/pull/12359) 弃用 `extract_eq_drop_take`，转而使用更正确的方法
  命名为 `extract_eq_take_drop`，这样我们就可以使用旧名称
  对于引理 `xs.extract start stop = (xs.take stop).drop start`。直到
  弃用截止日期已过，这个新引理将被称为
  `extract_eq_drop_take'`。

* [#12360](https://github.com/leanprover/lean4/pull/12360) 为字符串提供 `LawfulForwardPatternModel` 实例
  模式，即，它证明了 `dropPrefix?` 的正确性和
  `startsWith` 用于字符串模式的函数。

* [#12363](https://github.com/leanprover/lean4/pull/12363) 通过 `Vector.iter` 引入向量迭代器，
  `Vector.iterM`，以及通常的引理。

* [#12371](https://github.com/leanprover/lean4/pull/12371) 添加引理以简化涉及 `Bool` 和
  `ite`/`dite`。

* [#12412](https://github.com/leanprover/lean4/pull/12412) 引入 `Rat.abs` 并添加有关 `Int` 的缺失引理和
  `Rat`。

* [#12419](https://github.com/leanprover/lean4/pull/12419) 为 `Nat`、`Int` 和所有添加 `LawfulOrderOrd` 实例
  固定位宽整数 类型（`Int8`、`Int16`、`Int32`、`Int64`、`ISize`、
  `UInt8`、`UInt16`、`UInt32`、`UInt64`、`USize`）。这些实例
  确定这些类型的 `Ord` 实例与
  他们的 `LE` 实例。此外，此 PR 添加了一些缺失的引理
  和 `grind` 图案。

* [#12424](https://github.com/leanprover/lean4/pull/12424) 给出 `LawfulToForwardSearcherModel` 对于 `Slice` 的证明
  模式，这相当于证明我们的 KMP 实施是
  正确。

* [#12426](https://github.com/leanprover/lean4/pull/12426) 添加引理 `Acc.inv_of_transGen`，它是
  `Acc.inv`。虽然 `Acc.inv` 显示 `Acc r x` 暗示 `Acc r y`
  `r y x`，新引理表明，如果 `y` 仅是，则这也成立
  *传递*与 `x` 相关。

* [#12432](https://github.com/leanprover/lean4/pull/12432) 将引理 `isSome_find?` 和 `isSome_findSome?` 添加到 API
  列表、数组和向量。

* [#12437](https://github.com/leanprover/lean4/pull/12437) 通过关联来验证 `String.Slice.splitToSubslice` 函数
  它是基于 `Model.split` 的模型实现
  `ForwardPatternModel`。

* [#12438](https://github.com/leanprover/lean4/pull/12438) 提供 (1) 引理，显示从范围获得的列表具有
  切片上没有重复项和 (2) 关于 `forIn` 和 `foldl` 的引理。

* [#12441](https://github.com/leanprover/lean4/pull/12441) 删除 `Subarray.foldl(M)`、`Subarray.toArray` 和
  `Subarray.size` 支持 `Std.Slice` 命名空间操作。点
  符号将继续起作用。比如说，如果 `Subarray.size` 明确地
  参考后，将显示一条错误，建议使用 `Std.Slice.size`。

* [#12442](https://github.com/leanprover/lean4/pull/12442) 为范围类型派生 `DecidableEq` 实例，例如
  `a...b`（在本例中为 `Std.Rco`）。

* [#12445](https://github.com/leanprover/lean4/pull/12445) 提供表征 `Nat.toDigits`、`Nat.repr` 和
  `ToString Nat`。

* [#12449](https://github.com/leanprover/lean4/pull/12449) 将 `String.toString_eq_singleton` 标记为 `simp` 引理。

* [#12450](https://github.com/leanprover/lean4/pull/12450) 将 `String.Slice`/`String` 迭代器移出到自己的迭代器中
  文件，准备审核。

* [#12452](https://github.com/leanprover/lean4/pull/12452) 上游 `List.scanl`、`List.scanr` 及其引理来自
  电池放入标准库。

* [#12456](https://github.com/leanprover/lean4/pull/12456) 验证除字节之外的所有 `String` 迭代器
  迭代器，将它们与 `String.toList` 相关联。

* [#12504](https://github.com/leanprover/lean4/pull/12504) 生成 `Rat.abs_*` 引理 (`abs_zero`、`abs_nonneg`、
  `abs_of_nonneg`、`abs_of_nonpos`、`abs_neg`、`abs_sub_comm`、
  `abs_eq_zero_iff`、`abs_pos_iff`）受到保护，因此它们不会遮蔽
  在下游打开 `Rat` 命名空间时的常规 `abs_*` 引理
  项目。

* [#12521](https://github.com/leanprover/lean4/pull/12521) 显示 `HashSet.ofList l ~m l.foldl (init := ∅) fun acc a =>
  acc.insert a`（“只是”定义）。

* [#12531](https://github.com/leanprover/lean4/pull/12531) 将一些关于哈希映射的引理捆绑到等价中以便更容易
  重写。

* [#12582](https://github.com/leanprover/lean4/pull/12582) 对 `Name.quickCmp` 使用 `ptrEq` 快速路径。它特别是
  有效加速
  `quickCmp` 调用由 `FVarId` 索引的 `TreeMap`，通常有
  每个 `FVarId` 只有一个指针
  因此，始终会立即检测到相等性，而无需遍历链接
  `Name` 组件列表。

* [#12583](https://github.com/leanprover/lean4/pull/12583) 内联 `Name` 的计算哈希字段的访问器。这个
  确保访问
  值基本上总是只是一次加载，而不是执行完整的加载
  函数调用。

* [#12596](https://github.com/leanprover/lean4/pull/12596) 在字符串上为 `ForIn` 添加 `Std.Do` 规范引理。

* [#12641](https://github.com/leanprover/lean4/pull/12641) 导出字符串位置的线性顺序 (`String.Pos.Raw`，
  `String.Pos`、`String.Slice.Pos`）通过 `Std.LinearOrderPackage`，其中
  确保所有数据承载和命题实例都存在。

* [#12642](https://github.com/leanprover/lean4/pull/12642) 添加了 dsimprocs，用于减少 `String.toList` 和 `String.push`。

* [#12651](https://github.com/leanprover/lean4/pull/12651) 添加了一些关于 `min`、`minOn`、`List.min` 的缺失引理，
  `List.minOn`。

* [#12757](https://github.com/leanprover/lean4/pull/12757) 将 `Id.run` 标记为 `[implicit_reducible]` 以确保
  `Id.instMonadLiftTOfPure` 和 `instMonadLiftT Id` 定义为
  使用 `.implicitReducible` 透明度设置时相同。

* [#12821](https://github.com/leanprover/lean4/pull/12821) 从以下位置删除 `@[grind →]` 属性
  `List.getElem_of_getElem?` 和 `Vector.getElem_of_getElem?`。这些是
  在 Mathlib 中被确定为有问题
  https://github.com/leanprover/lean4/issues/12805.

# 策略

* [#11744](https://github.com/leanprover/lean4/pull/11744) 修复了 `lia` 错误地解决涉及以下目标的错误
  它不应该处理像 `Rat` 这样的有序类型。 `lia`策略是
  仅用于线性整数算术。

* [#12152](https://github.com/leanprover/lean4/pull/12152) 添加了 `simpArrowTelescope`，这是一个简化望远镜的 simproc
  非相关箭头 (p₁ → p2 → ... → q)，同时避免二次
  证明增长。

* [#12153](https://github.com/leanprover/lean4/pull/12153) 改进了 `simpArrowTelescope` simproc，简化了
  非依赖箭式望远镜：`p₁ → p₂ → ... → q`。

* [#12154](https://github.com/leanprover/lean4/pull/12154) 添加了 `simpTelescope`，这是一个简化望远镜的 simproc
  结合剂（`have`-表达值和箭头假设），但不是
  最终的身体。这对于在引入之前简化目标很有用
  假设。

* [#12168](https://github.com/leanprover/lean4/pull/12168) 在 `SymM` 中添加了对 eta 缩减的支持。

* [#12172](https://github.com/leanprover/lean4/pull/12172) 修复了我们如何确定函数参数是否为
  实例。
  以前，我们依赖活页夹注释（例如，`[Ring A]` 与 `{_ ：
  环A}`)
  做出这个决定。这是不可靠的，因为用户
  合法使用
  当实例已经可用时，`{..}` 类类型的绑定器
  来自
  上下文。例如：
  ```
  structure OrdSet (α : Type) [Hashable α] [BEq α] where
    ...

  def OrdSet.insert {_ : Hashable α} {_ : BEq α} (s : OrdSet α) (a : α) : OrdSet α :=
    ...
  ```

  这里，`Hashable` 和 `BEq` 是类，但 `{..}` 绑定器是故意的，
  实例来自`OrdSet`的参数，因此类型类解析是不必要的。

  该修复使用 `isClass?` 而不是其语法来检查参数的*类型*，并且
  将此信息缓存在 `FunInfo` 中。这会影响多个子系统：
  判别树、同余引理生成和 `grind` 规范化器。

* [#12176](https://github.com/leanprover/lean4/pull/12176) 修复了延迟 E-match 定理实例可能导致的错误
  实例跟踪映射中的 uniqueId 冲突。

* [#12195](https://github.com/leanprover/lean4/pull/12195) 确保 `dsimp` 默认情况下不会“简化”实例。的
  可以通过使用来检索旧行为
  ```
  set_option backward.dsimp.instances true
  ```
  将 `dsimp` 应用于实例会创建非标准实例，这
  在 Mathlib 中产生各种问题。
  这个修改类似于
  ```
  set_option backward.dsimp.proofs true
  ```

* [#12205](https://github.com/leanprover/lean4/pull/12205) 添加 `mkBackwardRuleFromExpr` 以创建向后规则
  表达式，补充了现有的 `mkBackwardRuleFromDecl`
  仅适用于声明名称。

* [#12224](https://github.com/leanprover/lean4/pull/12224) 修复了 `grind?` 建议不包含的错误
  使用局部变量点表示法的参数（例如，
  `cs.getD_rightInvSeq`，其中 `cs` 是局部变量）。这些参数
  被错误地过滤掉，因为代码假定了所有 ident 参数
  决心全球声明。事实上，局部变量点表示法
  生成需要在重播期间加载原始术语的锚点，
  因此它们必须保留在建议中。

* [#12226](https://github.com/leanprover/lean4/pull/12226) 修复了当定理 `foo` 有时 `grind [foo]` 失败的错误
  与目标不同的 Universe 变量名称，即使 Universe
  多态性应该允许宇宙统一。

* [#12244](https://github.com/leanprover/lean4/pull/12244) 确保 `simp` 默认情况下不会“简化”实例。旧的
  可以使用 `simp +instances` 检索行为。是相似的
  到 #12195，但对于 `dsimp`。
  `dsimp` 的向后兼容性标志也会停用此新功能
  功能。

* [#12259](https://github.com/leanprover/lean4/pull/12259) 确保我们将 `unfold_definition` 定义的结果缓存在
  内核类型检查器。我们曾经将这些信息缓存在线程中
  本地存储，但在 Lean 3 到 Lean 4 期间被删除
  过渡。

* [#12260](https://github.com/leanprover/lean4/pull/12260) 修复了 `Sym` 中函数 `instantiateRangeS'` 的错误
  框架。

* [#12279](https://github.com/leanprover/lean4/pull/12279) 添加了一个实验性的 `cbv`策略，可以从
  `conv` 模式。策略不适合生产用途，并且
  显示适当的警告。

* [#12280](https://github.com/leanprover/lean4/pull/12280) 添加了基于 Xavier Leroy 编译器验证的基准测试
  测试按值调用策略的课程。

* [#12287](https://github.com/leanprover/lean4/pull/12287) 修复了 `attribute [local simp]` 错误的问题
  私人导入的定理被拒绝

* [#12296](https://github.com/leanprover/lean4/pull/12296) 添加了 `cbv_eval` 属性，允许计算以下函数
  `cbv`策略使用预先注册的定理。

* [#12319](https://github.com/leanprover/lean4/pull/12319) 利用 `grind` 中表达式类型正确的事实
  外延定理的结论的形式为`?a = ?b`。

* [#12345](https://github.com/leanprover/lean4/pull/12345) 添加了两个基准（Eratosthenes 筛选、删除重复项
  从列表中）和一个测试（具有次线性复杂度的函数
  通过良基递归定义，对大天然物进行评估，最多
  到 `60` 数字）。

* [#12361](https://github.com/leanprover/lean4/pull/12361) 开发自定义 simprocs 来处理 `ite`/`dite`
  `cbv`策略中的表达式，基于来自的等效 simproc
  `Sym.simp`，区别在于如果条件不简化为
  `True`/`False`，我们利用可判定实例并计算
  条件减少到什么程度。

* [#12370](https://github.com/leanprover/lean4/pull/12370) 修复了 `Sym.simp` 中的证明构造错误。

* [#12399](https://github.com/leanprover/lean4/pull/12399) 添加自定义 simproc 来处理 `Decidable.rec`，我们强制
  `Decidable` 类型的参数中的重写，通常是
  由于是子单例而没有重写。

* [#12406](https://github.com/leanprover/lean4/pull/12406) 对 `bv_decide` 中的 LRAT 检查进行了两项更改：
  1. LRAT 修剪器以前用于删除删除指令，因为我们
  没有以有意义的方式对它们采取行动（如2中所述）。现在它
  找出最早可以删除条款的时间点
  修剪后的 LRAT 证明并在那里插入删除内容。
  2. LRAT 检查器接收 `Array IntAction` 并将其分解为
  `Array DefaultClauseAction`，然后将其传递到检查循环。
  与相比，`DefaultClauseAction` 具有更大的内存占用量
  `IntAction`。因此将整个证明具体化为
  `DefaultClauseAction` 前期消耗大量内存。在改编的
  LRAT 检查器我们采用 `Array IntAction` 并且只转换
  我们目前正在研究 `DefaultClauseAction`。在
  结合我们现在插入删除指令的事实
  可以大大减少内存消耗。

* [#12408](https://github.com/leanprover/lean4/pull/12408) 添加了一个面向 `cbv`策略的用户，该用户可以在外部使用
  `conv` 模式。

* [#12411](https://github.com/leanprover/lean4/pull/12411) 添加了整理 `decide_cbv`策略，适用
  `of_decide_eq_true` 然后尝试使用以下方法释放剩余目标
  `cbv`。

* [#12415](https://github.com/leanprover/lean4/pull/12415) 改进了对 `grind` 模式中 eta 扩展项的支持。

* [#12417](https://github.com/leanprover/lean4/pull/12417) 重构了 `cbv`策略的主循环。而不是使用
  多个 simproc，引入了中央预 simproc。此外，让
  由于性能原因，表达式不再立即 zeta 缩减
  基准之一 (`leroy.lean`)。

* [#12423](https://github.com/leanprover/lean4/pull/12423) 添加属性 `@[univ_out_params]` 用于指定
  宇宙层级 应被视为输出参数。默认情况下，任何
  考虑任何输入参数中未出现的 宇宙层级
  一个输出参数。

* [#12467](https://github.com/leanprover/lean4/pull/12467) 添加了用于评估 `cbv`策略的基准
  `Decidable.decide` 用于 `Decidable` 实例的检查问题
  如果一个数不是素数幂。

* [#12473](https://github.com/leanprover/lean4/pull/12473) 修复了 #12246 报告的 `grind` 中的断言冲突
  在包含异质等式的示例中，断言失败
  附加到不同类型的元素（例如，`Fin n` 和 `Fin m`）
  相同的理论求解器。

* [#12474](https://github.com/leanprover/lean4/pull/12474) 修复了 `grind` 中 `sreifyCore?` 可能遇到的恐慌
  嵌套期间尚未在 E 图中内化的幂子项
  传播。环形强化器（`reifyCore?`）已经具有防御性
  `alreadyInternalized` 创建变量之前检查，但半环
  reifier (`sreifyCore?`) 缺少此守卫。当`propagatePower`
  将 `a ^ (b₁ + b₂)` 分解为 `a^b₁ * a^b₂` 以及所得项
  触发进一步传播，可以调用半环放大器
  子项尚未出现在 E 图中，导致 `markTerm` 失败。

* [#12475](https://github.com/leanprover/lean4/pull/12475) 修复了假设包含元变量时 `grind` 失败的问题
  （例如，在 `refine` 之后）。根本原因是 `abstractMVars` 在
  `withProtectedMCtx` 仅抽象目标中的元变量，而不是
  假设，在grind的电子图中造成了脱节。

* [#12476](https://github.com/leanprover/lean4/pull/12476) 修复了 #12245，其中 `grind` 在 `Fin n` 上工作，但在 `Fin (n
  + 1）`。

* [#12477](https://github.com/leanprover/lean4/pull/12477) 修复了调用 `mkEqProof` 时的内部 `grind` 错误
  具有不同类型的术语。当等价类包含
  异构等式（例如，`0 : Fin 3` 和 `0 : Fin 2` 通过合并
  `HEq`), `closeGoalWithValuesEq` 会调用 `mkEqProof`
  不兼容的类型，触发内部错误。

* [#12480](https://github.com/leanprover/lean4/pull/12480) 在 AIG 到 CNF 转换期间跳过重新标记步骤，从而减少
  内存压力。

* [#12483](https://github.com/leanprover/lean4/pull/12483) 在 `grind` 中添加了对高阶米勒模式的支持
  电子匹配引擎。

* [#12486](https://github.com/leanprover/lean4/pull/12486) 将 `isDefEqI` 结果缓存在 `Sym` 中。符号计算期间
  （例如，VC 生成器），我们一遍又一遍地找到相同的实例。

* [#12500](https://github.com/leanprover/lean4/pull/12500) 改进了 `decide_cbv`策略生成的错误消息
  通过仅减少引入的等式的左侧
  `of_decide_eq_true`，而不是尝试通过
  `cbvGoal`。

* [#12506](https://github.com/leanprover/lean4/pull/12506) 添加了使用 `cbv_eval` 注册定理的功能
  attribute in the reverse direction using the `←` modifier, mirroring the
  现有的 `simp` 属性行为。当使用`@[cbv_eval ←]`时，
  方程 `lhs = rhs` 反转为 `rhs = lhs`，允许 `cbv`
  将出现的 `rhs` 重写为 `lhs`。

* [#12562](https://github.com/leanprover/lean4/pull/12562) 修复了 #12554，其中 `cbv`策略抛出“意外的内核”
  重写时结构 定义等价" 期间的投影项
  定理的模式包含一个 lambda 并且匹配的表达式有
  相应位置处的 `.proj`（内核投影）。

* [#12568](https://github.com/leanprover/lean4/pull/12568) 从中删除 `tryMatchEquations` 和 `tryMatcher`
  `Lean.Meta.Tactic.Cbv.Main`，因为两者都已在中定义和使用
  `Lean.Meta.Tactic.Cbv.ControlFlow`。 `Main.lean` 中的副本是
  无法访问的死代码。

* [#12585](https://github.com/leanprover/lean4/pull/12585) 删除 `ite` 和 `dite` 中不必要的 `trySynthInstance `
  `cbv` 使用的 simprocs 以前贡献了太多
  策略进行不必要的展开。

* [#12588](https://github.com/leanprover/lean4/pull/12588) 为 `cbv`策略添加了一个基准，其中涉及评估
  `List.mergeSort` 位于自然数的反向列表上。

* [#12601](https://github.com/leanprover/lean4/pull/12601) 在策略模式下使用 `cbv` 或 `decide_cbv` 时添加警告，
  与转换模式下的现有警告相匹配
  (`src/Lean/Elab/Tactic/Conv/Cbv.lean`)。该警告告知用户
  这些策略处于实验阶段，仍在开发中。它可以是
  使用 `set_option cbv.warning false` 禁用。

* [#12612](https://github.com/leanprover/lean4/pull/12612) 修复了 `cbv`策略的 `handleProj` simproc 中的崩溃问题
  处理依赖投影（例如 `Sigma.snd`），其结构为
  通过 `@[cbv_eval]` 重写为非定义等价项
  无法进一步减少。

* [#12615](https://github.com/leanprover/lean4/pull/12615) 修复了 `handleConst` 中阻止 `cbv` 的翻转条件
  从展开无效（非函数）常量定义，例如
  `def myVal : Nat := 42`。支票 `unless eType matches .forallE` 是
  旨在跳过裸函数常量（其展开定理期望
  参数），而是跳过值常量。该修复更改了
  保护到 `if eType matches .forallE`，匹配中使用的逻辑
  标准 `simp` 地面评估器。

* [#12622](https://github.com/leanprover/lean4/pull/12622) 修复了 `simp` 在类别投影上没有进展的错误
  当 `backward.whnf.reducibleClassField` 为 `true` 时减少。

* [#12627](https://github.com/leanprover/lean4/pull/12627) 恢复#12615，这意外地破坏了 Leroy 的编译器
  验证课程基准。

* [#12646](https://github.com/leanprover/lean4/pull/12646) 使 `cbv`策略能够展开 nullary（无功能）
  常数
  定义如 `def myNat : Nat := 42`，允许地面术语
  评价
  （例如 `evalEq`、`evalLT`）将它们的值识别为文字。

* [#12782](https://github.com/leanprover/lean4/pull/12782) 为研磨中的 `OfSemiring.Q` 实例添加高优先级
  环形信封。导入 Mathlib 时，类型的实例合成
  像 `OfSemiring.Q Nat` 变得非常昂贵，因为求解器
  在找到正确的实例之前探索许多不相关的路径。由
  将这些实例标记为高优先级并添加快捷方式实例
  用于基本操作（`Add`、`Sub`、`Mul`、`Neg`、`OfNat`、`NatCast`、
  `IntCast`、`HPow`），实例合成快速解析。

# 编译器

* [#12044](https://github.com/leanprover/lean4/pull/12044) 实现封闭项的延迟初始化。以前的工作
  已经确保约 70% 的封闭术语出现在核心中
  可以从二进制文件静态初始化。这样剩下的
  它们是延迟初始化的，而不是在启动时初始化的。

* [#12052](https://github.com/leanprover/lean4/pull/12052) 避免了 Lean 程序关闭时可能出现的死锁
  池线程数已暂时推至高于
  限制。

* [#12060](https://github.com/leanprover/lean4/pull/12060) 从 Linux 上的 libleanshared.so 中删除不需要的符号名称。它
  似乎在其他平台上我们感兴趣的符号名称
  这里已经被链接器删除了。

* [#12082](https://github.com/leanprover/lean4/pull/12082) 使编译器生成静态初始化的 C 代码
  尽可能接近条款。此更改减少了启动时间，因为条款
  直接存储在二进制文件中，而不是在
  启动。

* [#12117](https://github.com/leanprover/lean4/pull/12117) 升级 Lean 的内部工具链以使用 C++20 作为准备
  步骤#12044。

* [#12214](https://github.com/leanprover/lean4/pull/12214) 向 LCNF IR 引入相分离。这是一个
  为合并做准备
  旧的 `Lean.Compiler.IR` 和新的 `Lean.Compiler.LCNF` 框架。

* [#12239](https://github.com/leanprover/lean4/pull/12239) 恢复#8308 中所做的大量更改。我们实际上
  遇到过这样的情况：
  ```
  fun y (z) :=
    let x := inst
    mkInst x z
  f y
  ```
  实例拉取器将其变成：
  ```
  let x := inst
  fun y (z) :=
    mkInst x z
  f y
  ```
  当前的启发式现在发现 `x` 在调用站点的范围内
  `f` 的并在 `y` 的活页夹下使用，从而阻止拉入
  `x` 到专业化，对实例进行抽象。

* [#12272](https://github.com/leanprover/lean4/pull/12272) 将 LCNF mono 到 lambda pure 的转换转移到
  LCNF 不纯相。这是为即将进行的重构做的准备工作
  IR转化为不纯的LCNF。

* [#12284](https://github.com/leanprover/lean4/pull/12284) 更改了对过度应用案例表达式的处理
  `ToLCNF` 以避免生成被调用的函数声明
  立即。例如，`ToLCNF` 之前生成了这个：
  ```
  set_option trace.Compiler.init true
  /--
  trace: [Compiler.init] size: 4
      def test x y : Bool :=
        fun _y.1 _y.2 : Bool :=
          cases x : Bool
          | PUnit.unit =>
            fun _f.3 a : Bool :=
              return a;
            let _x.4 := _f.3 _y.2;
            return _x.4;
        let _x.5 := _y.1 y;
        return _x.5
  -/
  #guard_msgs in
  def test (x : Unit) (y : Bool) : Bool :=
    x.casesOn (fun a => a) y
  ```
  现在简化为
  ```
  set_option trace.Compiler.init true
  /--
  trace: [Compiler.init] size: 3
      def test x y : Bool :=
        cases x : Bool
        | PUnit.unit =>
          let a := y;
          return a
  -/
  #guard_msgs in
  def test (x : Unit) (y : Bool) : Bool :=
    x.casesOn (fun a => a) y
  ```
  This is especially relevant for #8309 because there `dite` is defined as
  an over-applied `Bool.casesOn`.

* [#12294](https://github.com/leanprover/lean4/pull/12294) ports the `push_proj` pass from IR to LCNF. Notably it cannot
  delete it from IR yet as the pass is still used later on.

* [#12315](https://github.com/leanprover/lean4/pull/12315) migrates the IR ResetReuse pass to LCNF.

* [#12344](https://github.com/leanprover/lean4/pull/12344) changes the semantics of `inline` annotations in the compiler.
  The behavior of the original `@[inline]` attribute remains the same but
  the function `inline` now comes with a restriction that it can only use
  declarations that are local to the current module. This comes as a
  preparation to pulling the compiler out into a separate process.

* [#12356](https://github.com/leanprover/lean4/pull/12356) moves the IR `elim_dead_vars` pass to LCNF. It cannot delete the
  pass yet as it is still used
  in later IR passes.

* [#12384](https://github.com/leanprover/lean4/pull/12384) ports the IR SimpCase pass to LCNF.

* [#12387](https://github.com/leanprover/lean4/pull/12387) fixes an issue in LCNF simp where it would attempt to act on
  type incorrect `cases`
  statements and look for a branch, otherwise panic. This issue did not
  yet manifest in production as
  various other invariants upheld by LCNF simp help mask it but will start
  to become an issue with the
  upcoming changes.

* [#12413](https://github.com/leanprover/lean4/pull/12413) ports the IR borrow pass to LCNF.

* [#12434](https://github.com/leanprover/lean4/pull/12434) removes the uses of `shared_timed_mutex` that were introduced
  because we were stuck on C++14
  with the `shared_mutex` available from C++17 and above.

* [#12446](https://github.com/leanprover/lean4/pull/12446) adds a simplification rule for `Task.get (Task.pure x) = x` into
  the LCNF simplifier. This
  ensures that we avoid touching the runtime for a `Task` that instantly
  gets destructed anyways.

* [#12458](https://github.com/leanprover/lean4/pull/12458) ports the IR pass for box/unbox insertion to LCNF.

* [#12465](https://github.com/leanprover/lean4/pull/12465) changes the boxed type of `uint64` from `tobject` to `object` to
  allow for more precise reference counting.

* [#12466](https://github.com/leanprover/lean4/pull/12466) handles zero-sized reads on handles correctly by returning an
  empty array before the syscall
  is even attempted.

* [#12472](https://github.com/leanprover/lean4/pull/12472) inlines `mix_hash` from C++ which provides general speedups for
  hash functions.

* [#12548](https://github.com/leanprover/lean4/pull/12548) ports the RC insertion from IR to LCNF.

* [#12580](https://github.com/leanprover/lean4/pull/12580) makes `computed_field` respect the inline attributes on the
  function for computing the
  field. This means we can inline the accessor for the field, allowing
  quicker access.

* [#12604](https://github.com/leanprover/lean4/pull/12604) makes the derived value analysis in RC insertion recognize
  `Array.uget` as another kind of
  "projection-like" operation. This allows it to reduce reference count
  pressure on elements accessed
  through uget.

* [#12625](https://github.com/leanprover/lean4/pull/12625) ensures that failure in initial compilation marks the relevant
  definitions as `noncomputable`, inside and outside `noncomputable
  section`, so that follow-up errors/noncomputable markings are detected
  in initial compilation as well instead of somewhere down the pipeline.

* [#12644](https://github.com/leanprover/lean4/pull/12644) ports the toposorting pass from IR to LCNF.

* [#12759](https://github.com/leanprover/lean4/pull/12759) replaces the `isImplicitReducible` check with `Meta.isInstance`
  in the `shouldInline` function within `inlineCandidate?`.

# Pretty Printing

* [#12688](https://github.com/leanprover/lean4/pull/12688) adds the `pp.fvars.anonymous` option (default `true`) that
  controls the display of loose free variables (fvars not in the local
  context). When `false`, they display as `_fvar._` instead of their internal
  name. This is useful for stabilizing output in `#guard_msgs`.
  [#12745](https://github.com/leanprover/lean4/pull/12745) fixes the
  behavior when the option is set to `false`.

# Documentation

* [#12157](https://github.com/leanprover/lean4/pull/12157) updates #12137 with a link to the Lean reference manual.

* [#12174](https://github.com/leanprover/lean4/pull/12174) fixes a typo in `ExtractLetsConfig.merge` doc comment.

* [#12253](https://github.com/leanprover/lean4/pull/12253) adds a "Stabilizing output" section to the `#guard_msgs`
  docstring, explaining how to use `pp.mvars.anonymous` and `pp.mvars`
  options to stabilize output containing autogenerated metavariable names
  like `?m.47`.

* [#12271](https://github.com/leanprover/lean4/pull/12271) adds and updates docstrings for syntax (and one for ranges).

* [#12439](https://github.com/leanprover/lean4/pull/12439) improves docstrings for `cbv` and `decide_cbv` tactics

* [#12487](https://github.com/leanprover/lean4/pull/12487) expands the docstring for `@[univ_out_params]` to explain:

  - How universe output parameters affect the typeclass resolution cache
  (they are erased from cache keys, so queries differing only in output
  universes share entries)
  - When a universe parameter should be considered an output (determined
  by inputs) vs. not (part of the question being asked)

* [#12616](https://github.com/leanprover/lean4/pull/12616) adds documentation to the Cbv evaluator files under
  `Meta/Tactic/Cbv/`. Module docstrings describe the evaluation strategy,
  limitations, attributes, and unfolding order. Function docstrings cover
  the public API and key internal simprocs.

* [#13115](https://github.com/leanprover/lean4/pull/13115) updates the `inferInstanceAs` docstring to reflect current
  behavior: it requires an
  expected type from context and should not be used as a simple
  `inferInstance` synonym. The
  old example (`#check inferInstanceAs (Inhabited Nat)`) no longer works,
  so it's replaced
  with one demonstrating the intended transport use case.

# Server

* [#12197](https://github.com/leanprover/lean4/pull/12197) fixes a bug in `System.Uri.fileUriToPath?` where it wouldn't use
  the default Windows path separator in the path it produces.

* [#12332](https://github.com/leanprover/lean4/pull/12332) fixes an issue on new NeoVim versions that would cause the
  language server to display an error when using certain code actions.

* [#12553](https://github.com/leanprover/lean4/pull/12553) fixes an issue where commands that do not support incrementality
  did not have their elaboration interrupted when a relevant edit is made
  by the user. As all built-in variants of def/theorem share a common
  incremental elaborator, this likely had negligible impact on standard
  Lean files but could affect other use cases heavily relying on custom
  commands such as Verso.

# Lake

* [#12113](https://github.com/leanprover/lean4/pull/12113) changes the alters the file format of outputs stored in the
  local Lake cache to include an identifier indicating the service (if
  any) the output came from. This will be used to enable lazily
  downloading artifacts on-demand during builds.

* [#12178](https://github.com/leanprover/lean4/pull/12178) scopes the `simp` attribute on `FamilyOut.fam_eq` to the `Lake`
  namespace. The lemma has a very permissive discrimination tree key
  (`_`), so when `Lake.Util.Family` is transitively imported into
  downstream projects, it causes `simp` to attempt this lemma on every
  goal, leading to timeouts.

* [#12203](https://github.com/leanprover/lean4/pull/12203) changes the way artifacts are transferred from the local Lake
  cache to a local build path. Now, Lake will first attempt to hard link
  the local build path to artifact in the cache. If this fails (e.g.,
  because the cache is on a different file system or drive), it will
  fallback to pre-existing approach of copying the artifact. Lake also now
  marks cache artifacts as read-only to avoid corrupting the cache by
  writing to a hard linked artifact.

* [#12261](https://github.com/leanprover/lean4/pull/12261) fixes a bug in Lake where the facet names printed in unknown
  facet errors would contain the internal facet kind.

* [#12300](https://github.com/leanprover/lean4/pull/12300) makes disabling the artifact cache (e.g., via
  `LAKE_ARTIFACT_CACHE=false` or `enableArtifactCache = false`) now stop
  Lake from fetching from the cache (whereas it previously only stopped
  writing to it).

* [#12377](https://github.com/leanprover/lean4/pull/12377) adds identifying information about a module available to `lean`
  (e.g., its name and package identifier) to the module's dependency
  trace. This ensures modules with different identification have different
  input hashes even if their source files and imports are identical.

* [#12444](https://github.com/leanprover/lean4/pull/12444) adds the Lake CLI command `lake cache clean`, which deletes the
  Lake cache directory.

* [#12461](https://github.com/leanprover/lean4/pull/12461) adds support for manually re-releasing nightlies when a build
  issue or critical fix requires it. When a `workflow_dispatch` triggers
  the nightly release job and a `nightly-YYYY-MM-DD` tag already exists,
  the CI now creates `nightly-YYYY-MM-DD-rev1` (then `-rev2`, etc.)
  instead of silently skipping.

* [#12490](https://github.com/leanprover/lean4/pull/12490) adds a system-wide Lake configuration file and uses it to
  configure the remote cache services used by `lake cache`.

* [#12532](https://github.com/leanprover/lean4/pull/12532) fixes a bug with `cache clean` where it would fail if the cache
  directory does not exist.

* [#12537](https://github.com/leanprover/lean4/pull/12537) fixes a bug where Lake recached artifacts already present within
  the cache. As a result, Lake would attempt to overwrite the read-only
  artifacts, causing a permission denied error.

* [#12835](https://github.com/leanprover/lean4/pull/12835) changes Lake to only emit `.nobuild` traces (introduced in
  #12076) if the normal trace file already exists. This fixes an issue
  where a `lake build --no-build` would create the build directory and
  thereby prevent a cloud release fetch in a future build.

* [#13141](https://github.com/leanprover/lean4/pull/13141) changes Lake to run `git clean -xf` when updating dependency
  repositories, ensuring stale untracked files (such as `.hash` files) in the
  source tree are removed. Stale `.hash` files could cause incorrect trace
  computation and break builds.

# Other

* [#12351](https://github.com/leanprover/lean4/pull/12351) extends the `@[csimp]` attribute to be correctly tracked by
  `lake shake`

* [#12375](https://github.com/leanprover/lean4/pull/12375) extends shake with tracking of attribute names passed to
  `simp`/`grind`.

* [#12463](https://github.com/leanprover/lean4/pull/12463) fixes two issues discovered during the first test of the revised
  nightly release workflow
  (https://github.com/leanprover/lean4/pull/12461):

  *1. Date logic:* The `workflow_dispatch` path used `date -u +%F`
  (current UTC date) to find the base nightly to revise. If the most
  recent nightly was from yesterday (e.g. `nightly-2026-02-12`) but UTC
  has rolled over to Feb 13, the code would look for `nightly-2026-02-13`,
  not find it, and create a fresh nightly instead of a revision. Now finds
  the latest `nightly-*` tag via `sort -rV` and creates a revision of
  that.

* [#12517](https://github.com/leanprover/lean4/pull/12517) adds tooling for profiling Lean programs with human-readable
  function names in Firefox Profiler:

  - *`script/lean_profile.sh`* — One-command pipeline: record with
  samply, symbolicate, demangle, and open in Firefox Profiler
  - *`script/profiler/lean_demangle.py`* — Faithful port of
  `Name.demangleAux` from `NameMangling.lean`, with a postprocessor that
  folds compiler suffixes into compact annotations (`[λ, arity↓]`, `spec
  at context[flags]`)
  - *`script/profiler/symbolicate_profile.py`* — Resolves raw addresses
  via samply's symbolication API
  - *`script/profiler/serve_profile.py`* — Serves demangled profiles to
  Firefox Profiler without re-symbolication
  - *`PROFILER_README.md`* — Documentation including a guide to reading
  demangled names

* [#12533](https://github.com/leanprover/lean4/pull/12533) adds human-friendly demangling of Lean symbol names in runtime
  backtraces. When a Lean program panics, stack traces now show readable
  names instead of mangled C identifiers.
