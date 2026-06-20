/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "简化者" =>
%%%
file := "The-Simplifier"
tag := "the-simplifier"
%%%

简化器是 Lean 最常用的功能之一。
它基于简化规则数据库对术语进行由内而外的重写。
该简化器具有高度可配置性，许多策略以不同的方式使用它。

# 调用简化器
%%%
file := "Invoking-the-Simplifier"
tag := "simp-tactic-naming"
%%%


Lean 的简化器可以通过多种方式调用。
最常见的模式在一组策略中捕获。
{ref "simp-tactics"}[策略参考]包含简化策略的完整列表。

简化策略名称中均包含 `simp`。
除此之外，它们是根据描述其功能的前缀和后缀系统命名的：

: `-!`后缀

  将 {name Lean.Meta.Simp.Config.autoUnfold}`autoUnfold` 配置选项设置为 `true`，使简化器展开所有定义

: `-?`后缀

  使简化器跟踪简化过程中使用的规则，并建议最小的 {tech}[simp set] 作为对策略脚本的编辑

: `-_arith`后缀

  允许使用线性算术简化规则

: `d-` 前缀

  导致简化器仅通过定义保留的重写来简化

: `-_all`后缀

  使简化器反复简化所有假设和目标结论，考虑尽可能多的假设，直到不可能进一步简化

还有两个进一步的简化策略、{tactic}`simpa` 和 {tactic}`simpa!`，用于在实现目标之前同时简化目标和证明项或假设。
这种同时简化使得证明对于 {tech}[simp set] 中的变化更加稳健。

## 参数
%%%
file := "Parameters"
tag := "simp-tactic-params"
%%%

简化策略具有以下语法：

:::syntax tactic (title := "Simplification Tactics")
```grammar
simp $_:optConfig $[only]? $[ [ $[$e],* ] ]? $[at $[$h]*]?
```
:::

换句话说，简化策略的调用按顺序采用以下修饰符，所有这些修饰符都是可选的：
 * 一组 {ref "tactic-config"}[配置选项]，其中应包括 {name}`Lean.Meta.Simp.Config` 或 {name}`Lean.Meta.DSimp.Config` 字段，具体取决于所调用的简化器是 {tactic}`simp` 版本还是 {tactic}`dsimp` 版本。
 * {keywordOf Lean.Parser.Tactic.simp}`only` 修饰符不包括默认的 simp 集，而是以空的{margin}[从技术上讲，simp 集始终包含 {name}`eq_self` 和 {name}`iff_self`，以便释放自反情况。] simp 集开始。
 * 引理列表在 simp 集中添加或删除引理。可以通过三种方式在引理列表中指定引理：
   * `*`，将证明状态中的所有假设添加到 simp 集中
   * `-` 后跟引理，从 simpl 集中删除引理
   * 引理说明符，按顺序包含以下内容：
      * 可选的 `↓` 或 `↑`，分别导致在输入子项之前或之后应用引理（`↑` 是默认值）。简化者通常会在尝试简化父项之前先简化子项，因为简化的参数通常会使更多规则适用； `↓` 导致使用子项简化之前的规则来简化父项。
      * 可选的 `←`，它导致等式引理从右到左而不是从左到右使用。
      * 强制引理，可以是 simp 集名称、引理名称或术语。术语被视为就像用新名称命名的引理一样。
 * 位置说明符，前面带有 {keywordOf Lean.Parser.Tactic.simp}`at`，由位置序列组成。地点可能是：

   - 假设的名称，表明其类型应简化
   - 星号`*`，表示所有假设和结论都应该简化
   - 一个转门`⊢`，说明结论应该简化

  默认情况下，仅对结论进行简化。

::::example "Location specifiers for {tactic}`simp`"
:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```

在这种证明状态下，
```pre
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

策略{tacticStep}`simp +arith` 仅简化了目标：

```post
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (x + 7)
```
:::

:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre -show
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

调用 {tacticStep}`simp +arith at h` 会产生一个目标，其中假设 `h` 已被简化：

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (6 + x + 1)
```
:::

:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre -show
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

结论还可以通过添加`⊢`来进一步简化，即{tacticStep}`simp +arith at h ⊢`：

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (x + 7)
```
:::

:::tacticExample
{goal -show}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre -show
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

使用 {tacticStep}`simp +arith at *` 简化了所有假设以及结论：

```post
p : Nat → Prop
x : Nat
h : p (x + 7)
h' : p (x + 12)
⊢ p (x + 7)
```
:::
::::


# 重写规则
%%%
file := "Rewrite-Rules"
tag := "simp-rewrites"
%%%

简化器具有三种重写规则：

: 待展开的宣言

  默认情况下，简化器只会展开 {tech}[reducible] 定义。
  但是，可以为任何 {tech (key := "semireducible")}[半可约] 或 {tech (key := "irreducible")}[不可约] 定义添加重写规则，这也会导致简化器展开它。
  当简化器在定义模式（{tactic}`dsimp` 及其变体）下运行时，定义展开仅用其值替换定义的名称；否则，它还使用方程编译器生成的方程引理。

: 方程引理

  简化器可以将等式证明视为重写规则，在这种情况下等式的左侧将被右侧替换。这些等式引理可以具有任意数量的参数。简化器实例化参数以使等式的左侧与目标匹配，并执行证明搜索以实例化任何其他参数。

: 简化程序

  该简化器支持称为 {deftech}_simprocs_ 的简化过程，该过程使用 Lean 元编程来执行无法使用方程有效指定的重写。 Lean 包括用于内置类型上最重要操作的 simprocs。

:::keepEnv
```lean -show
-- Validate the above description of reducibility

@[irreducible]
def foo (x : α) := x

set_option allowUnsafeReducibility true in
@[semireducible]
def foo' (x : α) := x

@[reducible]
def foo'' (x : α) := x

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo (x, y) = (y, x) := by
  simp [foo]

/-- error: `simp` made no progress -/
#check_msgs in
example : foo (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo' (x, y) = (y, x) := by
  simp [foo']

/-- error: `simp` made no progress -/
#check_msgs in
example : foo' (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo'' (x, y) = (y, x) := by
  simp [foo'']

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#check_msgs in
example : foo'' (x, y) = (y, x) := by
  simp

```
:::

由于 {tech (key := "propositional extensionality")}[命题外延性]，等式引理可以将命题重写为更简单、逻辑上等价的命题。
当简化器将证明目标重写为 {lean}`True` 时，它会自动关闭它。
作为等式引理的特例，等式以外的命题可以被标记为重写规则
它们被预处理成规则，将命题重写为 {lean}`True`。

:::::example "Rewriting Propositions"
::::tacticExample

{goal -show}`∀(α β : Type) (w y : α) (x z : β), (w, x) = (y, z)`
```setup
intro α β w y x z
```

当被要求简化对等式时：
```pre
α β : Type
w y : α
x z : β
⊢ (w, x) = (y, z)
```

{tacticStep}`simp` 产生等式的合取：

```post
α β : Type
w y : α
x z : β
⊢ w = y ∧ x = z
```

默认的 simp 集包含 {lean}`Prod.mk.injEq`，这显示了两个语句的等价性：

```signature
Prod.mk.injEq.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) :
  ∀ (fst_1 : α) (snd_1 : β),
    ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
```
::::
:::::

除了重写规则之外，{tactic}`simp` 还有许多内置的缩减规则，{ref "simp-config"}[由 `config` 参数控制]。
即使 simp 集为空，{tactic}`simp` 也可以用其值替换 `let` 绑定变量，减少 {tech (key := "match discriminant")}[判别式] 是构造函数应用的 {keywordOf Lean.Parser.Term.match}`match` 表达式，减少应用于构造函数的结构投影，或将 lambda 应用于其参数。

# 简单套装
%%%
file := "Simp-sets"
tag := "simp-sets"
%%%

简化器使用的规则集合称为 {deftech}_simp set_。
simp 集是根据 {deftech}_default simp set_ 的修改来指定的。
这些修改可以包括添加规则、删除规则或添加一组规则。
`only` 对 {tactic}`simp`策略的修饰符会导致它以空的 simp 集（而不是默认的）开始。
使用 {attr}`simp` 属性将规则添加到默认 simp 集。


:::syntax attr (alias := Lean.Meta.simpExtension) (title := "Registering {keyword}`simp` Lemmas")
{attr}`simp` 属性向默认 simp 集添加声明。
如果声明是定义，则将定义标记为展开；如果它是一个定理，则该定理被注册为重写规则。

```grammar
simp
```


```grammar
simp ↑ $p?
```

```grammar
simp ↓ $p?
```

```grammar
simp $p:prio
```

```lean -show
-- Check above claim about default priority
/-- info: 1000 -/
#check_msgs in
#eval eval_prio default
```
:::

{deftech (key := "Custom simp sets")}_自定义 simp 集_ 使用 {name Lean.Meta.registerSimpAttr}`registerSimpAttr` 创建，必须在 {tech (key := "initialization")}[初始化] 期间通过将其放置在 {keywordOf Lean.Parser.Command.initialize}`initialize` 块中来运行。
作为副作用，它会创建一个与 {attr}`simp` 具有相同接口的新属性，该属性将规则添加到自定义 simp 集。
返回的值是 {name Lean.Meta.SimpExtension}`SimpExtension`，可用于以编程方式访问自定义 simp 集的内容。
通过将其属性名称包含在规则列表中，可以指示 {tactic}`simp`策略使用新的 simp 集。

{docstring Lean.Meta.registerSimpAttr}

{docstring Lean.Meta.SimpExtension}


# 简单范式
%%%
file := "Simp-Normal-Forms"
tag := "simp-normal-forms"
%%%


默认的 {tech}[simp set] 包含用 {attr}`simp` 属性标记的所有定理和简化过程。
表达式的 {deftech (key := "simp normal form")}_simp 范式_ 是通过 {tactic}`simp`策略应用默认 simp 集的结果，直到无法应用更多规则。
当表达式采用 simp 范式时，它会根据默认的 simp 集尽可能地简化，通常使其更容易在证明中使用。

{tactic}`simp`策略*不保证汇合*，这意味着表达式的 simp 范式可能取决于应用默认 simp 集的元素的顺序。
在设置 {attr}`simp` 属性时，可以通过分配优先级来更改应用规则的顺序。

设计 Lean 库时，重要的是要考虑适合库运算符的各种组合的简单范式。
这可以作为选择库应添加到默认 simp 集中的规则的指南。
特别是，simpl 引理的右侧应该是 simpl 范式；这有助于确保简化终止。
此外，库中的每个概念都应该通过一种 simpl 范式来表达，即使有多种等效的方式来表达它。
如果一个概念在不同的 simpl 引理中以两种不同的方式陈述，那么某些所需的简化可能不会发生，因为简化器没有连接它们。

尽管简化不需要汇合，但努力汇合是有帮助的，因为它使库更具可预测性，并且往往会揭示丢失或选择不当的简化引理。
默认 simp 集与其导出的常量的类型签名一样，都是库接口的一部分。

库不应向默认 simp 集添加未提及库中至少定义的一个常量的规则。
否则，导入库可能会更改某些不相关库的 {tactic}`simp` 的行为。
如果库依赖其他库的定义或声明的附加简化规则，请创建自定义简化集并指导用户使用它或提供专用的策略。


# 终端头寸与非终端头寸
%%%
file := "Terminal-vs-Non-Terminal-Positions"
tag := "terminal-simp"
%%%

要编写可维护的证明，请避免使用不带 {keywordOf Lean.Parser.Tactic.simp}`only` 的 {tactic}`simp`，除非它关闭了目标。
不关闭目标的 {tactic}`simp` 的此类使用称为 {deftech}_non-terminal simps_。
这是因为对默认 simp 集的添加可能会使 {tactic}`simp` 更强大，或者只是导致它选择不同的重写序列并达到不同的 simp 范式。
当指定 {keywordOf Lean.Parser.Tactic.simp}`only` 时，其他引理将不会影响策略的调用。
实际上，{tactic}`simp` 的终端使用不太可能因添加新的 simpl 引理而被破坏，并且当它们被破坏时，更容易理解问题并修复它。

在非终端位置工作时，{tactic}`simp?`（或名称中带有 `?` 的其他简化策略之一）可用于生成 {keywordOf Lean.Parser.Tactic.simp}`only` 的适当调用。
正如 {tactic}`apply?` 或 {tactic}`rw?` 建议使用相关引理一样，{tactic}`simp?` 建议使用用于达到规范形式的最小 simp 集来调用 {tactic}`simp`。

:::example "Using {tactic}`simp?`"

此证明中的非终结符 {tactic}`simp?` 建议使用更小的 {tactic}`simp` 和 {keywordOf Lean.Parser.Tactic.simp}`only`：
```lean (name:=simpHuhDemo)
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp?
  assumption
```
建议的重写是：
```leanOutput simpHuhDemo
Try this:
  [apply] simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
```
这导致了更易于维护的证明：
```lean
example (xs : Array Unit) : xs.size = 2 → xs = #[(), ()] := by
  intros
  ext
  simp only [
    List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd
  ]
  assumption
```

:::


# 配置简化
%%%
file := "Configuring-Simplification"
tag := "simp-config"
%%%

{tactic}`simp` 主要通过配置参数进行配置，作为名为 `config` 的命名参数传递。

{docstring Lean.Meta.Simp.Config}

{docstring Lean.Meta.Simp.neutralConfig}

{docstring Lean.Meta.DSimp.Config}

## 选项
%%%
file := "Options"
tag := "simp-options"
%%%

一些全局选项影响 {tactic}`simp`：

{optionDocs simprocs}

{optionDocs tactic.simp.trace}

{optionDocs linter.unnecessarySimpa}

{optionDocs trace.Meta.Tactic.simp.rewrite}

{optionDocs trace.Meta.Tactic.simp.discharge}

# 简化与重写
%%%
file := "Simplification-vs-Rewriting"
tag := "simp-vs-rw"
%%%


{tactic}`simp` 和 {tactic}`rw`/{tactic}`rewrite` 都使用等式引理将部分术语替换为等效替代项。
然而，它们的预期用途和重写策略有所不同。
{tactic}`simp` 系列中的策略主要用于以标准化方式重新表述问题，使其更易于人类理解和进一步自动化。
特别是，简化决不应该使本来可以证明的目标变得不可能。
{tactic}`rw` 系列中的策略主要用于应用手动选择的转换，这些转换并不总是保留可证明性，也不以标准化形式放置术语。
这些不同的侧重点体现在策略的两个家族之间的行为差异上。

{tactic}`simp`策略主要是从内到外重写。
首先简化尽可能小的表达式，以便它们可以为周围的表达式释放进一步简化的机会。
{tactic}`rw`策略选择与模式匹配的最左边最外层的子项，并重写它一次。
策略都允许覆盖其策略：将引理添加到 simp 集中时，`↓` 修饰符会使其在子项简化之前应用，并且 {tactic}`rw` 配置参数的 {name Lean.Meta.Rewrite.Config.occs}`occs` 字段允许通过白名单或黑名单选择不同的出现。
