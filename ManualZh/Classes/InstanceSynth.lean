/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "实例合成" =>
%%%
tag := "instance-synth"
%%%


实例合成是一种递归搜索过程，要么找到给定类型类的实例，要么失败。
换句话说，给定一个注册为类型类的类型，实例合成尝试用所述类型构造一个术语。
它遵循 {tech}[可约性]：{tech}[半可约] 或 {tech}[不可约] 定义不会展开，因此定义的实例不会自动视为其展开的实例，除非它是 {tech}[可约]。
给定类可能有多个可能的实例；在这种情况下，声明的优先级和声明顺序将按此顺序用作决胜局，较新的实例优先于具有相同优先级的较早实例。

该搜索过程在存在菱形的情况下是有效的，并且在存在循环时不会无限循环。
{deftech}_Diamonds_ 发生在存在多条路线到达给定目标的情况下，而 {deftech}_cycles_ 是指如果解决了另一个实例则可以解决两个实例的情况。
在实践中，当使用类型类对数学概念进行编码时，菱形经常出现，并且 Lean 的强制转换功能 {TODO}[link] 自然会导致循环，例如有限集和有限多重集之间。

可以使用 {keywordOf Lean.Parser.Command.synth}`#synth` 命令测试实例综合。
此外，{name}`inferInstance` 和 {name}`inferInstanceAs` 可用于在需要实例本身的位置合成实例。
带类型注释的 {name}`inferInstance` 和 {name}`inferInstanceAs` 不等效； {name}`inferInstanceAs` {ref "instance-wrapping"}[预处理合成实例]以防止实现细节无意泄漏到接口中。

{docstring inferInstance}

{docstring inferInstanceAs}

# 实例搜索摘要

一般来说，实例合成是一种递归搜索过程，通常可以任意回溯。
对于实例术语，综合可能会_成功_，如果找不到这样的术语，则可能_失败_，或者如果信息不足，则_陷入困境_。
{citet tabledRes}[] 中提供了实例合成算法的详细描述。
实例搜索问题由应用于具体参数的类型类给出；这些参数值可能已知，也可能未知。
实例搜索按优先级和定义的顺序尝试每个类型为类的本地绑定变量以及每个注册实例。
当候选实例本身具有实例隐式参数时，它们会施加进一步的综合任务。

仅当类型类的所有输入参数已知时才尝试解决问题。
当一个问题还不能尝试时，该分支就被卡住了；其他子问题的进展可能会导致问题变得可以解决。
输出或半输出参数在实例搜索开始时可能是已知的或未知的。
检查实例是否与问题匹配时忽略输出参数，而考虑半输出参数。

给定问题的每个候选解决方案都保存在一个表中；这可以防止循环情况下的无限回归以及钻石存在时的指数搜索开销（即可以实现相同目标的多条路径）。
当发生以下任一情况时，搜索分支将失败：
 * 所有潜在的实例都已尝试过，并且搜索空间已耗尽。
 * 已达到选项 {option}`synthInstance.maxSize` 指定的实例大小限制。
 * 输出参数的合成值与搜索问题中的指定值不匹配。
失败的分支不会重试。

如果搜索失败或卡住，搜索进程会尝试按优先级顺序使用匹配的 {tech}[默认实例]。
对于默认实例，输入参数不需要完全已知，并且可以通过实例参数值来实例化。
默认实例可能采用实例隐式参数，这会引发进一步的递归搜索。

问题完全已知的成功分支（即，其中不存在未解决的元变量）将被修剪，并且不会尝试进一步的潜在成功实例，因为后面的实例不会导致先前成功的分支失败。

# 实例搜索问题
%%%
tag := "instance-search"
%%%

实例搜索发生在（可能为空）函数应用程序的精化期间。
一些隐式参数的值是由其他参数强制的；例如，可以使用显式提供的后续值参数的类型来解决隐式类型参数。
隐式参数也可以使用程序中该点的预期类型的信息来解决。
对实例隐式参数的搜索可以利用已找到的隐式参数值，并且还可以解决其他问题。

实例综合从实例隐式参数的类型开始。
该类型必须是类型类对零个或多个参数的应用；当搜索开始时，这些参数值可能是已知的或未知的。
如果类的参数未知，搜索过程将不会实例化它，除非相应的参数是 {ref "class-output-parameters"}[标记为输出参数]，明确使其成为实例综合例程的输出。

搜索可能成功、失败或陷入困境；当已知未知参数值可能会取得进展时，可能会发生卡住搜索。
当精化器发现先前未知的隐式参数之一时，可能会重新调用卡住的搜索。
如果不发生这种情况，卡住的搜索就会失败。

::::example "Tracing Instance Search"

将 {option}`trace.Meta.synthInstance` 选项设置为 {lean}`true` 会导致 Lean 发出合成类型类实例的过程跟踪。
此跟踪可用于了解实例合成如何成功以及失败的原因。

:::paragraph
在这里，我们可以看到 Lean 所采取的步骤来得出存在 {lean}`(Nat ⊕ Empty)` 类型的元素（特别是元素 {lean}`Sum.inl 0`）的结论：
单击 `▶` 符号可展开跟踪的该分支，单击 `▼` 可折叠展开的分支。

```lean -show
-- Hide Lake details that are intruding here
attribute [-instance] Lake.inhabitedOfNilTrace Lake.inhabitedOfMonadCycle
```

```lean (name := trace)
set_option pp.explicit true in
set_option trace.Meta.synthInstance true in
#synth Nonempty (Nat ⊕ Empty)
```

```comment
IF THE LEAN OUTPUT BELOW CHANGES, IT MAY ALSO BE NECESSARY TO UPDATE THE NARRATIVE VERSION OF THIS STORY THAT FOLLOWS
```
```leanOutput trace (expandTrace := Meta.synthInstance) (expandTrace := Meta.synthInstance.apply) (expandTrace := Meta.synthInstance.resume)
[Meta.synthInstance] ✅️ Nonempty (Sum Nat Empty)
  [Meta.synthInstance] ✅️ new goal Nonempty (Sum Nat Empty)
    [Meta.synthInstance.instances] #[@instNonemptyOfInhabited, @instNonemptyOfMonad, @Sum.nonemptyLeft, @Sum.nonemptyRight]
  [Meta.synthInstance.apply] ✅️ apply @Sum.nonemptyRight to Nonempty (Sum Nat Empty)
    [Meta.synthInstance.tryResolve] ✅️ Nonempty (Sum Nat Empty) ≟ Nonempty (Sum Nat Empty)
    [Meta.synthInstance] ✅️ new goal Nonempty Empty
      [Meta.synthInstance.instances] #[@instNonemptyOfInhabited, @instNonemptyOfMonad]
  [Meta.synthInstance.apply] ❌️ apply @instNonemptyOfMonad to Nonempty Empty
    [Meta.synthInstance.tryResolve] ❌️ Nonempty Empty ≟ Nonempty (?m.5 ?m.6)
  [Meta.synthInstance.apply] ✅️ apply @instNonemptyOfInhabited to Nonempty Empty
    [Meta.synthInstance.tryResolve] ✅️ Nonempty Empty ≟ Nonempty Empty
    [Meta.synthInstance] ✅️ new goal Inhabited Empty
      [Meta.synthInstance.instances] #[@instInhabitedOfMonad]
  [Meta.synthInstance.apply] ❌️ apply @instInhabitedOfMonad to Inhabited Empty
    [Meta.synthInstance.tryResolve] ❌️ Inhabited Empty ≟ Inhabited (?m.8 ?m.7)
  [Meta.synthInstance.apply] ✅️ apply @Sum.nonemptyLeft to Nonempty (Sum Nat Empty)
    [Meta.synthInstance.tryResolve] ✅️ Nonempty (Sum Nat Empty) ≟ Nonempty (Sum Nat Empty)
    [Meta.synthInstance] ✅️ new goal Nonempty Nat
      [Meta.synthInstance.instances] #[@instNonemptyOfInhabited, @instNonemptyOfMonad]
  [Meta.synthInstance.apply] ❌️ apply @instNonemptyOfMonad to Nonempty Nat
    [Meta.synthInstance.tryResolve] ❌️ Nonempty Nat ≟ Nonempty (?m.5 ?m.6)
  [Meta.synthInstance.apply] ✅️ apply @instNonemptyOfInhabited to Nonempty Nat
    [Meta.synthInstance.tryResolve] ✅️ Nonempty Nat ≟ Nonempty Nat
    [Meta.synthInstance] ✅️ new goal Inhabited Nat
      [Meta.synthInstance.instances] #[@instInhabitedOfMonad, instInhabitedNat]
  [Meta.synthInstance.apply] ✅️ apply instInhabitedNat to Inhabited Nat
    [Meta.synthInstance.tryResolve] ✅️ Inhabited Nat ≟ Inhabited Nat
    [Meta.synthInstance.answer] ✅️ Inhabited Nat
  [Meta.synthInstance.resume] ✅️ propagating Inhabited Nat to subgoal Inhabited Nat of Nonempty Nat
    [Meta.synthInstance.resume] size: 1
    [Meta.synthInstance.answer] ✅️ Nonempty Nat
  [Meta.synthInstance.resume] ✅️ propagating Nonempty Nat to subgoal Nonempty Nat of Nonempty (Sum Nat Empty)
    [Meta.synthInstance.resume] size: 2
    [Meta.synthInstance.answer] ✅️ Nonempty (Sum Nat Empty)
  [Meta.synthInstance] result @Sum.nonemptyLeft Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
:::

:::paragraph
通过探索跟踪，可以遵循 Lean 用于类型类实例搜索的深度优先回溯搜索。
这可能需要一些练习才能习惯！
在上面的示例中，Lean 遵循以下步骤：

* Lean 考虑第一个目标 {lean}`Nonempty (Sum Nat Empty)`。 Lean 认为有四种可能实现这一目标的方法：
  - {name}`Sum.nonemptyRight` 实例，它将创建子目标 {lean}`Nonempty Empty`。
  - {name}`Sum.nonemptyLeft` 实例，它将创建子目标 {lean}`Nonempty Nat`。
  - {name}`instNonemptyOfMonad` 实例，它将创建两个子目标 {lean}`Monad (Sum Nat)` 和 {lean}`Nonempty Nat`。
  - {name}`instNonemptyOfInhabited` 实例，它将创建子目标 {lean}`Inhabited (Sum Nat Empty)`。
* 它应用了 {name}`Sum.nonemptyRight`，成功了，留下了一个新目标：{lean}`Nonempty Empty`。
* 考虑第一个子目标 {lean}`Nonempty Empty`。 Lean 认为有两种可能实现此目标的方法：
  - {name}`instNonemptyOfMonad` 实例，被拒绝。
    它无法使用，因为类型 {lean}`Empty` 不是 monad 对类型的应用。
  - {name}`instNonemptyOfInhabited` 实例，它将创建子目标 {lean}`Inhabited Empty`。
* 考虑新生成的子目标 {lean}`Inhabited Empty`。
  Lean 仅看到一种可能满足此目标的方法，即 {name}`instInhabitedOfMonad`，该方法被拒绝。
  和以前一样，这是因为类型 {lean}`Empty` 不是 monad 对类型的应用。
* 此时，没有剩余的选项可以实现最初的第一个子目标。
  使用实例 {name}`Sum.nonemptyLeft` 进行搜索回溯，这需要 {lean}`Nonempty Nat` 的实例。
  此搜索最终通过 {inst}`Inhabited Nat` 实例成功。
:::

第三和第四个原始候选人从未被考虑过。
一旦搜索 {lean}`Nonempty Nat` 成功，{keywordOf Lean.Parser.Command.synth}`#synth` 命令就会完成并输出解决方案：
```leanOutput trace
@Sum.nonemptyLeft Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
::::

# 候选实例

实例合成在其搜索中使用本地实例和全局实例。
{deftech}_本地实例_是本地上下文中可用的实例；它们可以是函数的参数，也可以是使用 `let` 本地定义的。 {TODO}[`let` 的文档参考]
本地实例无需特别注明；任何类型为类型类的局部变量都是实例综合的候选者。
{deftech}_全局实例_是全局环境中可用的实例；每个全局实例都是应用了 {attr}`instance` 属性的定义名称。{margin}[{keywordOf Lean.Parser.Command.declaration}`instance` 声明自动应用 {attr}`instance` 属性。]

::::keepEnv
:::example "Local Instances"
在此示例中，{lean}`addPairs` 包含 {lean}`Add NatPair` 的本地定义实例：
```lean
structure NatPair where
  x : Nat
  y : Nat

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun ⟨x1, y1⟩ ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩⟩
  p1 + p2
```
本地实例用于添加，已通过实例合成找到。
:::
::::

::::keepEnv
:::example "Local Instances Have Priority"
此处，{lean}`addPairs` 包含 {lean}`Add NatPair` 的本地定义实例，即使存在全局实例：
```lean
structure NatPair where
  x : Nat
  y : Nat

instance : Add NatPair where
  add
    | ⟨x1, y1⟩, ⟨x2, y2⟩ => ⟨x1 + x2, y1 + y2⟩

def addPairs (p1 p2 : NatPair) : NatPair :=
  let _ : Add NatPair :=
    ⟨fun _ _ => ⟨0, 0⟩⟩
  p1 + p2
```
选择本地实例而不是全局实例：
```lean (name:=addPairsOut)
#eval addPairs ⟨1, 2⟩ ⟨5, 2⟩
```
```leanOutput addPairsOut
{ x := 0, y := 0 }
```
:::
::::

# 实例参数和综合
%%%
tag := "instance-synth-parameters"
%%%

实例的搜索过程很大程度上由类参数控制。
Type 类采用一定数量的参数，并且当实例的参数选择与要为其合成实例的类类型中的参数“兼容”时，就会在搜索过程中尝试实例。

实例本身也可以带参数，但是实例参数在实例合成中的作用非常不同。
实例的参数表示可以通过实例综合实例化的变量或在使用实例之前要完成的进一步综合工作。
特别地，实例的参数可以是显式的、隐式的或实例隐式的。
如果它们是实例隐式的，那么它们会引起进一步的递归实例搜索，而显式或隐式参数必须通过统一来解决。

::::keepEnv
:::example "Implicit and Explicit Parameters to Instances"
虽然实例通常隐式地或实例隐式地采用参数，但可以填写显式参数，就好像它们在实例合成期间是隐式的一样。
在此示例中，{name}`aNonemptySumInstance` 是通过综合找到的，并显式应用于 {lean}`Nat`，这是使其类型正确所需的。
```lean
instance aNonemptySumInstance
    (α : Type) {β : Type} [inst : Nonempty α] :
    Nonempty (α ⊕ β) :=
  let ⟨x⟩ := inst
  ⟨.inl x⟩
```

```lean (name := instSearch)
set_option pp.explicit true in
#synth Nonempty (Nat ⊕ Empty)
```
在输出中，显式参数 {lean}`Nat` 和隐式参数 {lean}`Empty` 都是通过与搜索目标统一找到的，而 {lean}`Nonempty Nat` 实例是通过递归实例合成找到的。
```leanOutput instSearch
@aNonemptySumInstance Nat Empty (@instNonemptyOfInhabited Nat instInhabitedNat)
```
:::
::::

# 输出参数
%%%
tag := "class-output-parameters"
%%%

默认情况下，类型类的参数被视为搜索过程的_输入_。
如果参数未知，那么搜索过程就会陷入困境，因为选择实例需要参数具有与实例中的值相匹配的值，而这不能根据不完整的信息来确定。
在大多数情况下，猜测实例会使实例合成变得不可预测。

然而，在某些情况下，选择一个参数会导致自动选择另一个参数。
例如，重载成员谓词类型类 {name}`Membership` 将数据结构的元素类型视为输出，以便可以通过使用站点处的数据结构的类型来确定元素的类型，而不是要求在开始实例合成之前有足够的类型注释来确定两种类型。
{lean}`List Nat` 的元素可以简单地根据其在列表中的成员资格来推断为 {lean}`Nat`。

```signature -show
-- Test the above claim
Membership.{u, v} (α : outParam (Type u)) (γ : Type v) : Type (max u v)
```

Type 类参数可以通过将其类型包装在 {name}`outParam` {tech}[gadget] 中来声明为输出。
当类参数是 {deftech}_输出参数_时，实例合成将不需要它是已知的；事实上，任何现有的价值都被完全忽略。
选择与输入参数匹配的第一个实例，并且该实例对输出参数的分配将成为其值。
如果存在预先存在的值，则综合完成后将其与赋值进行比较，如果不匹配则出错。

{docstring outParam}

::::example "Output Parameters and Stuck Search"
:::keepEnv
该序列化框架提供了一种将值转换为某种底层存储类型的方法：
```lean
class Serialize (input output : Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```

在此示例中，输出类型未知。
```lean +error (name := noOutputType)
example := ser (2, 3)
```
实例综合无法选择 {lean}`Serialize Nat String` 实例，因此无法选择 {lean}`Append String` 实例，因为这需要将输出类型实例化为 {lean}`String`，因此搜索会陷入困境：
```leanOutput noOutputType
typeclass instance problem is stuck
  Serialize (Nat × Nat) ?m.5

Note: Lean will not try to resolve this typeclass instance problem because the second type argument to `Serialize` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
```
正如消息所示，解决该问题的一种方法是提供预期的类型：
```lean
example : String := ser (2, 3)
```
:::
:::keepEnv
另一种是将输出类型做成输出参数：
```lean
class Serialize (input : Type) (output : outParam Type) where
  ser : input → output
export Serialize (ser)

instance : Serialize Nat String where
  ser n := toString n

instance [Serialize α γ] [Serialize β γ] [Append γ] :
    Serialize (α × β) γ where
  ser
    | (x, y) => ser x ++ ser y
```
现在，实例合成可以自由选择{lean}`Serialize Nat String`实例，这就解决了{name}`ser`的未知隐式`output`参数：
```lean
example := ser (2, 3)
```
:::
::::

::::keepEnv
:::example "Output Parameters with Pre-Existing Values"
类 {name}`OneSmaller` 表示一种将类型的非最大元素转换为少一个元素的类型的元素的方法。
有两个单独的实例可以匹配输入类型 {lean}`Option Bool`，并具有不同的输出：
```lean
class OneSmaller (α : Type) (β : outParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```
由于实例合成选择的是最近定义的实例，因此以下代码是错误的：
```lean +error (name := nosmaller)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller
failed to synthesize instance of type class
  OneSmaller (Option Bool) Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
{lean}`OneSmaller (Option Bool) (Option Unit)` 实例是在实例合成期间选择的，而不考虑 `β` 的提供值。
:::
::::

{deftech}_半输出参数_类似于输出参数，因为在合成开始之前不需要知道它们；与输出参数不同，在选择实例时会考虑它们的值。

{docstring semiOutParam}

半输出参数对实例提出了要求：具有半输出参数的类的每个实例都应确定其半输出参数的值。
:::TODO
如果他们不能，会出现什么问题？
:::

::::keepEnv
:::example "Semi-Output Parameters with Pre-Existing Values"
类 {name}`OneSmaller` 表示一种将类型的非最大元素转换为少一个元素的类型的元素的方法。
它有两个单独的实例，可以匹配输入类型 {lean}`Option Bool`，并具有不同的输出：
```lean
class OneSmaller (α : Type) (β : semiOutParam Type) where
  biggest : α
  shrink : (x : α) → x ≠ biggest → β

instance : OneSmaller (Option α) α where
  biggest := none
  shrink
    | some x, _ => x

instance : OneSmaller (Option Bool) (Option Unit) where
  biggest := some true
  shrink
    | none, _ => none
    | some false, _ => some ()

instance : OneSmaller Bool Unit where
  biggest := true
  shrink
    | false, _ => ()
```

由于实例综合在选择实例时考虑了半输出参数，因此由于 `β` 提供的值，{lean}`OneSmaller (Option Bool) (Option Unit)` 实例将被传递：
```lean (name := nosmaller2)
#check OneSmaller.shrink (β := Bool) (some false) sorry
```
```leanOutput nosmaller2
OneSmaller.shrink (some false) ⋯ : Bool
```
:::
::::

# 默认实例
%%%
tag := "default-instance-synth"
%%%

当实例合成失败时，如果未选择实例，则按优先级顺序尝试使用 {attr}`default_instance` 属性指定的 {deftech}_default 实例_。
当优先级相同时，会先选择最近定义的默认实例，然后再选择较早定义的默认实例。
选择导致搜索成功的第一个默认实例。

如果默认实例本身具有实例隐式参数，则默认实例可能会引发进一步的递归实例搜索。
如果递归搜索失败，搜索过程将回溯并尝试下一个默认实例。

# “道德规范”实例

在实例合成期间，如果目标完全已知（即不包含元变量）并且搜索成功，则不会为同一目标尝试更多实例。
换句话说，当以无法通过随后的信息增加来反驳的方式成功搜索某个目标时，即使存在可能已使用的其他实例，也不会再次尝试该目标。
这种优化可以防止实例综合搜索的后续分支中的失败导致虚假回溯，从而用对大状态空间的缓慢探索来替换来自较早分支的快速解决方案。

优化依赖于实例是 {deftech}_morally canonical_ 的假设。
即使给定类型类的重载操作有不止一种潜在实现，或者由于钻石而合成实例的方法不止一种，_任何发现的实例都应该被认为与任何其他实例一样好_。
换句话说，只要保证其中一个实例能够正常工作，就无需考虑_所有_潜在实例。
可以使用向后兼容选项 {option}`backward.synthInstance.canonInstances` 禁用优化，该选项可能会在 Lean 的未来版本中删除。

使用实例隐式参数的代码应准备好将所有实例视为等效的。
换句话说，面对合成实例的差异，它应该是鲁棒的。
当代码依赖于实例_事实上_是等效的时，它应该显式地操作实例（例如，通过本地定义，通过将它们保存在结构字段中，或者让结构从适当的类继承），或者应该在类型中明确这种依赖关系，以便实例的不同选择导致不兼容的类型。

# 包装合成实例
%%%
tag := "instance-wrapping"
%%%

{name}`inferInstanceAs` 或默认 {keywordOf Lean.Parser.Command.declaration}`deriving` 处理程序合成实例后，将处理实例主体以确保其类型及其字段类型与 {name Lean.Meta.TransparencyMode.instances}`instances` 透明度下的预期类型匹配，这仅展开 {tech}[可约] 和 {tech}[隐式可约] 定义。
当实例减少到低于 {tech}[半可缩减]透明度时，此处理可防止实例定义的内部泄漏，泄漏可能会导致代码库的不同部分之间产生意外的依赖关系。

如果预期类型是一个命题，则该实例被包装在辅助定理中。
否则，合成的实例会在 {name Lean.Meta.TransparencyMode.instances}`instances` 透明度下还原为弱头部范式。
如果结果是构造函数应用程序，则处理每个字段：
* 当找到子实例字段时，子实例字段将被替换为其类型的新合成实例。
  这可确保该实例与合成该实例的客户端代码找到的实例相同，从而避免出现以下情况：实例的多个路径（称为 _diamonds_）产生彼此不 {tech (key := "definitional equality")}[定义等价]的实例。
  当综合找不到实例时，将使用此过程递归地包装该字段。
* 其类型在定义上不等于预期类型的证明字段被包装在隐藏类型差异的辅助定理中。
* 类型与预期类型不匹配的数据字段将包装在具有适当可简化性的辅助定义中。

如果实例未简化为构造函数应用程序并且其类型与预期类型不匹配，则将其包装在具有适当可简化性的辅助定义中。

# 选项

{optionDocs backward.synthInstance.canonInstances}

{optionDocs synthInstance.maxHeartbeats}

{optionDocs synthInstance.maxSize}

{optionDocs backward.inferInstanceAs.wrap}

{optionDocs backward.inferInstanceAs.wrap.reuseSubInstances}

{optionDocs backward.inferInstanceAs.wrap.instances}

{optionDocs backward.inferInstanceAs.wrap.data}
