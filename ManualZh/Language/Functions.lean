/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "功能" =>
%%%
tag := "functions"
%%%


函数类型是 Lean 的内置功能。
{deftech}[Functions] 将一种类型 ({deftech}_domain_) 的值映射到另一种类型 ({deftech}_codomain_) 的值，{deftech}_function types_ 指定函数的域和余域。

函数类型有两种：

 : {deftech (key := "Dependent")}[依赖]

   依赖函数类型显式命名参数，并且函数的共域可以显式引用该名称。
   由于类型可以根据值计算，因此依赖函数可以返回任意数量的不同类型的值，具体取决于其参数。{margin}[依赖函数有时称为 {deftech}_dependent products_，因为它们对应于集合的索引乘积。]

 : {deftech (key := "Non-Dependent")}[非相关]

   非依赖函数类型不包含参数名称，并且陪域不会根据提供的特定参数而变化。


::::keepEnv
:::example "Dependent Function Types"

函数 {lean}`two` 返回不同类型的值，具体取决于使用哪个参数调用它：

```lean
def two : (b : Bool) → if b then Unit × Unit else String :=
  fun b =>
    match b with
    | true => ((), ())
    | false => "two"
```

函数体不能用 `if...then...else...` 编写，因为它不像 {keywordOf Lean.Parser.Term.match}`match` 那样细化类型。
:::
::::

在Lean的核心语言中，所有函数类型都是相关的：非相关函数类型是参数名称不出现在{tech}[codomain]中的相关函数类型。
此外，如果重命名参数使它们相等，则具有不同参数名称的两个从属函数类型在定义上可能相等。
但是，Lean精化器不会引入非相关函数参数的本地绑定。

:::example "Definitional Equality of Dependent and Non-Dependent Functions"
{lean}`(x : Nat) → String` 和 {lean}`Nat → String` 类型在定义上是相等的：
```lean
example : ((x : Nat) → String) = (Nat → String) :=
  rfl
```
同样，类型 {lean}`(n : Nat) → n + 1 = 1 + n` 和 {lean}`(k : Nat) → k + 1 = 1 + k` 在定义上是相等的：
```lean
example : ((n : Nat) → n + 1 = 1 + n) = ((k : Nat) → k + 1 = 1 + k) :=
  rfl
```
:::

:::::keepEnv
::::example "Non-Dependent Functions Don't Bind Variables"

:::keepEnv
以下语句中需要依赖函数来保证数组的所有元素均非零：
```lean
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (lt : i < xs.size) → xs[i] ≠ 0
```
:::

:::keepEnv
这是因为用于数组访问的精化器需要证明索引在边界内。
该语句的非依赖版本没有引入此假设：
```lean +error (name := nondepOops)
def AllNonZero (xs : Array Nat) : Prop :=
  (i : Nat) → (i < xs.size) → xs[i] ≠ 0
```
```leanOutput nondepOops
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array Nat
i : Nat
⊢ i < xs.size
```
:::
::::
:::::

虽然核心 类型论 不具有 {tech (key := "implicit")}[隐式] 参数，但函数类型确实包含参数是否隐式的指示。
该信息由 Lean精化器使用，但它不会影响核心理论中的类型检查或 定义等价，并且在仅考虑核心 类型论 时可以忽略。

:::example "Definitional Equality of Implicit and Explicit Function Types"
类型 {lean}`{α : Type} → (x : α) → α` 和 {lean}`(α : Type) → (x : α) → α` 在定义上是相等的，即使第一个参数在一个参数中是隐式的，而在另一个参数中是显式的。
```lean
example :
    ({α : Type} → (x : α) → α)
    =
    ((α : Type) → (x : α) → α)
  := rfl
```

:::

# 函数抽象
%%%
tag := "zh-language-functions-h001"
%%%

在 Lean 的 类型论 中，函数是使用绑定变量的 {deftech (key := "function abstractions")}_函数抽象_ 创建的。
{margin}[在各个社区中，函数抽象也称为 _lambdas_，因为 Alonzo Church 对它们的表示法，或者称为_匿名函数_，因为它们不需要在全局环境中使用名称来定义。]
应用该函数时，通过 {tech (key := "β")}[β-reduction] 找到结果：用参数替换绑定变量。
在编译的代码中，这种情况严格发生：参数必须已经是一个值。
类型检查时，没有这样的限制； 定义等价 的方程理论允许任意项进行 β 约简。

在Lean的{ref "function-terms"}[术语语言]中，函数抽象可以采用多个参数或使用模式匹配。
这些功能被转换为核心语言中更简单的操作，其中所有函数抽象都只采用一个参数。
并非所有函数都源自抽象：{tech (key := "type constructors")}[类型构造函数]、{tech (key := "constructors")}[构造函数] 和 {tech (key := "recursors")}[递归函数] 可能具有函数类型，但不能单独使用函数抽象来定义它们。


# 柯里化
%%%
tag := "currying"
%%%


在 Lean 的核心 类型论 中，每个函数将 {tech}[domain] 的每个元素映射到 {tech}[codomain] 的单个元素。
换句话说，每个函数都只需要一个参数。
多参数函数是通过定义高阶函数来实现的，当提供第一个参数时，该函数将返回一个需要其余参数的新函数。
这种编码称为 {deftech}_currying_，由 Haskell B. Curry 推广并命名。
Lean 用于定义函数、指定其类型并应用它们的语法会产生多参数函数的错觉，但精化的结果仅包含单参数函数。



# 外延性
%%%
tag := "function-extensionality"
%%%


Lean 中的函数 定义等价 是 {deftech}_intensional_。
这意味着 定义等价 是按语法定义的，对绑定变量和 {tech (key := "reduction")}[约简] 进行模重命名。
对于第一个近似，这意味着如果两个函数实现相同的算法，则它们在定义上是相等的，而不是通常的数学相等概念，即如果它们将 {tech}[domain] 的相等元素映射到 {tech}[codomain] 的相等元素，则两个函数相等。


定义等价 由类型检查器使用，因此它的可预测性非常重要。
内涵相等的句法特征意味着检查它的算法是可以确定的。
检查外延相等性涉及证明关于函数相等性的本质上任意定理，并且没有明确的规范来检查它的算法。
这使得扩展相等对于类型检查器来说是一个糟糕的选择。
相反，函数外延性作为推理原理提供，在证明 {tech (key := "proposition")}[命题] 两个函数相等时可以调用该推理原理。


::::keepEnv
```lean -show
axiom α : Type
axiom β : α → Type
axiom f : (x : α) → β x

-- test claims in next para
example : (fun x => f x) = f := by rfl
```

除了绑定变量的缩减和重命名之外，定义等价 还支持一种有限形式的外延性，称为 {tech}_η-equivalence_，其中函数等于其主体将其应用于参数的抽象。
给定类型为 {lean}`(x : α) → β x` 的 {lean}`f`，{lean}`f` 定义上等于 {lean}`fun x => f x`。
::::

在推理函数时，定理 {lean}`funext`{margin}[与某些内涵类型理论不同，{lean}`funext` 是 Lean 中的定理。可以证明 {ref "quotient-funext"}[使用商类型].] 或相应的策略{tactic}`funext` 或 {tactic}`ext` 可用于证明两个函数相等，如果它们将相等的输入映射到相等的输出。

{docstring funext}

# 整体性和终止性
%%%
tag := "totality"
%%%


可以使用 {keywordOf Lean.Parser.Command.declaration}`def` 递归定义函数。
从 Lean 的逻辑角度来看，所有函数都是 {deftech}_total_，这意味着它们在有限时间内将 {tech}[domain] 的每个元素映射到 {tech}[codomain] 的元素。{margin}[有些编程语言社群以另一种含义使用 _total_ 一词：若函数不会因未处理的情形而崩溃，则认为它是全函数，而忽略非终止。]
Total 函数的值是为所有类型正确的参数定义的，并且它们不会由于模式匹配中缺少大小写而无法终止或崩溃。

虽然Lean的逻辑模型认为所有功能都是完整的，但Lean也是一种实用的编程语言，提供了某些“逃生舱口”。
尚未证明可以终止的函数仍然可以在 Lean 的逻辑中使用，只要它们的 {tech}[codomain] 被证明为非空。
这些函数被 Lean 的逻辑视为未解释的函数，并且它们的计算行为被忽略。
在编译代码中，这些函数的处理方式与其他函数一样。
其他功能可能被标记为不安全；这些功能对于 Lean 的逻辑根本不可用。
关于 {ref "partial-unsafe"}[部分和不安全函数定义] 的部分包含有关使用递归函数进行编程的更多详细信息。

同样，在编译代码中应在运行时失败的操作（例如对数组的越界访问）只能在已知结果类型存在时使用。
这些操作会导致在 Lean 逻辑中任意选择该类型的居民（具体来说，是在类型的 {name}`Inhabited` 实例中指定的居民）。

:::example "Panic"
函数 {name}`thirdChar` 提取数组的第三个元素，或者如果数组有两个或更少的元素，则会出现混乱：
```lean
def thirdChar (xs : Array Char) : Char := xs[2]!
```
{lean}`#['!']` 和 {lean}`#['-', 'x']` 的（不存在的）第三个元素是相等的，因为它们产生相同的任意选择的字符：
```lean
example : thirdChar #['!'] = thirdChar #['-', 'x'] := rfl
```
事实上，两者都等于 {lean}`'A'`，这恰好是 {lean}`Char` 的默认后备：
```lean
example : thirdChar #['!'] = 'A' := rfl
example : thirdChar #['-', 'x'] = 'A' := rfl
```
:::

# API 参考
%%%
tag := "function-api"
%%%

`Function` 命名空间包含用于处理函数的通用帮助程序。

{docstring Function.comp}

{docstring Function.const}

{docstring Function.curry}

{docstring Function.uncurry}

## 特性
%%%
tag := "function-api-properties"
%%%

{docstring Function.Injective}

{docstring Function.Surjective}

{docstring Function.LeftInverse}

{docstring Function.HasLeftInverse}

{docstring Function.RightInverse}

{docstring Function.HasRightInverse}
