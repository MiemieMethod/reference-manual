/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers


open Manual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "基本建设" =>
%%%
tag := "basic-props"
%%%

除了蕴涵和全称量化之外，逻辑连接词和量词在 {lean}`Prop` 域中实现为 {tech (key := "inductive types")}[归纳类型]。
从某种意义上说，本章中描述的连接词并不特殊——任何用户都可以实现它们。
然而，这些基本连接词在标准库和内置证明自动化工具中广泛使用。



# 真相
%%%
tag := "true-false"
%%%

基本上，Lean 中只有两个命题：{lean}`True` 和 {lean}`False`。
命题外延性公理 ({name}`propext`) 允许命题在逻辑上等价时被视为相等，并且每个真命题在逻辑上等价于 {lean}`True`。
类似地，每个假命题在逻辑上都等价于{lean}`False`。

{lean}`True` 是一个归纳定义的命题，具有不带参数的单个构造函数。
总是可以证明 {lean}`True`。
另一方面，{lean}`False` 是一个没有构造函数的归纳定义命题。
证明它需要找到当前上下文中的不一致之处。

{lean}`True` 和 {lean}`False` 都是 {ref "subsingleton-elimination"}[子单例]；这意味着它们可以用来计算非命题类型的居民。
对于 {lean}`True`，这相当于忽略证明，该证明没有提供任何信息。
对于 {lean}`False`，这相当于证明当前代码无法访问并且不需要完成。

{docstring True}

{docstring False}

{docstring False.elim}

:::example "Dead Code and Subsingleton Elimination"


{lean}`f` 定义中的第四个分支无法访问，因此不需要提供具体的 {lean}`String` 值：
```lean
def f (n : Nat) : String :=
  if h1 : n < 11 then
    "Small"
  else if h2 : n > 13 then
    "Large"
  else if h3 : n % 2 = 1 then
    "Odd"
  else if h4 : n ≠ 12 then
    False.elim (by omega)
  else "Twelve"
```
在此示例中，{name}`False.elim` 向 Lean 指示当前本地上下文在逻辑上不一致：证明 {name}`False` 足以放弃该分支。

类似地，{name}`g` 的定义似乎有可能是非终止的。
但是，递归调用发生在程序中无法到达的路径上。
用于生成终止证明的证明自动化可以检测到局部假设是否不一致。
```lean
def g (n : Nat) : String :=
  if n < 11 then
    "Small"
  else if n > 13 then
    "Large"
  else if n % 2 = 1 then
    "Odd"
  else if n ≠ 12 then
    g (n + 1)
  else "Twelve"
termination_by n
```
:::

# 逻辑连接词
%%%
tag := "zh-basicprops-h002"
%%%

连词被实现为归纳定义的命题 {name}`And`。
构造函数 {name}`And.intro` 表示合取的引入规则：要证明一个合取，只需证明两个合取即可。
类似地，{name}`And.elim` 表示消除规则：给定一个合取的证明和一个假设两个合取的其他陈述的证明，另一个陈述可以被证明。
由于 {name}`And` 是 {tech}[subsingleton]，因此 {name}`And.elim` 也可以用作计算数据的一部分。
但是，不应将其与 {name}`PProd` 混淆：使用不可计算的推理原理（例如选择公理）来定义数据（包括 {lean}`Prod`）会导致 Lean 无法编译和运行生成的程序，而在命题证明中使用它们则不会导致此类问题。

在 {ref "tactics"}[策略] 证明中，可以通过 {tactic}`apply` 显式使用 {name}`And.intro` 来证明合取，但 {tactic}`constructor` 更常见。
当多个连词嵌套在证明目标中时，{tactic}`and_intros` 可用于在每个相关位置应用 {name}`And.intro`。
可以使用 {tactic}`cases`、模式匹配与 {tactic}`let` 或 {tactic (show := "match")}`Lean.Parser.Tactic.match` 或 {tactic}`rcases` 来简化上下文中连词的假设。

{docstring And}

{docstring And.elim}

析取作为归纳定义的命题 {name}`Or` 来实现。
它有两个构造函数，每个引入规则都有一个：任一析取的证明都足以证明该析取。
虽然 {lean}`Or` 的定义与 {lean}`Sum` 的定义类似，但在实践中却有很大不同。
由于 {lean}`Sum` 是一种类型，因此可以检查使用哪个构造函数来创建任何给定值。
另一方面，{lean}`Or` 形成命题：证明析取的项不能被询问来检查哪个析取是正确的。
换句话说，由于 {lean}`Or` 不是 {tech}[subsingleton]，因此它的证明不能用作计算的一部分。

在 {ref "tactics"}[策略] 证明中，可以通过 {tactic}`apply` 使用任一构造函数（{name}`Or.inl` 或 {name}`Or.inr`）显式证明析取。
可以使用 {tactic}`cases`、模式匹配与 {tactic (show := "match")}`Lean.Parser.Tactic.match` 或 {tactic}`rcases` 来简化上下文中的析取假设。

{docstring Or}

当任一析取为 {tech (key := "decidable")}[可判定] 时，就可以使用 {lean}`Or` 来计算数据。
这是因为决策过程的结果提供了合适的分支条件。

{docstring Or.by_cases}

{docstring Or.by_cases'}


```lean -show
section
variable {P : Prop}
```
{lean}`¬P` 不是将否定编码为归纳类型，而是定义为表示 {lean}`P → False`。
换句话说，为了证明一个否定，只需假设否定的陈述并导出矛盾即可。
这也意味着 {lean}`False` 可以立即从命题及其否定的证明中导出，然后用于证明任何命题或栖息于任何类型。
```lean -show
end
```


{docstring Not}

{docstring absurd}

{docstring Not.elim}




```lean -show
section
variable {A B : Prop}
```
使用 {tech (key := "universe")}[命题] 的 {tech (key := "propositions")}[宇宙] 中的 {ref "function-types"}[函数类型] 表示蕴涵。
为了证明{lean}`A → B`，在假设{lean}`A`之后证明{lean}`B`就足够了。
这对应于 {keywordOf Lean.Parser.Term.fun}`fun` 的键入规则。
类似地，函数应用的类型规则对应于{deftech}_modus ponens_：给定{lean}`A → B`的证明和{lean}`A`的证明，可以证明{lean}`B`。

:::example "Truth-Functional Implication"
将蕴涵表示为命题域中的函数相当于传统定义，其中 {lean}`A → B` 被定义为 {lean}`(¬A) ∨ B`。
这可以使用 {tech (key := "propositional extensionality")}[命题外延性] 和排中律来证明：
```lean
theorem truth_functional_imp {A B : Prop} :
    ((¬ A) ∨ B) = (A → B) := by
  apply propext
  constructor
  . rintro (h | h) a <;> trivial
  . intro h
    by_cases A
    . apply Or.inr; solve_by_elim
    . apply Or.inl; trivial
```
:::

```lean -show
end
```


逻辑等价，或“当且仅当”，使用相当于蕴涵两个方向的合取的结构来表示。

{docstring Iff}

{docstring Iff.elim}

:::syntax term (title := "Propositional Connectives")
除蕴涵之外的逻辑连接词通常使用专用语法来引用，而不是通过其定义的名称：
```grammar
$_ ∧ $_
```
```grammar
$_ ∨ $_
```
```grammar
¬ $_
```
```grammar
$_ ↔ $_
```
:::


# 量词
%%%
tag := "zh-basicprops-h003"
%%%

正如蕴涵在 {lean}`Prop` 中实现为普通函数类型一样，全称量化在 {lean}`Prop` 中实现为依赖函数类型。
由于 {lean}`Prop` 是 {tech (key := "impredicative")}[必然]，因此 {tech}[codomain] 是 {lean}`Prop` 的任何函数类型本身也是 {lean}`Prop`，即使 {tech}[domain] 是 {lean}`Type` 也是如此。
依赖函数的类型规则与全称量化的引入和消除规则精确匹配：如果谓词对于任意选择的类型元素成立，那么它就全称成立。
如果一个谓词普遍成立，那么它可以实例化为任何个体的证明。

:::syntax term (title := "Universal Quantification")

```grammar
∀ $x:ident $[$_:ident]* $[: $t]?, $_
```
```grammar
forall $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
∀ $_ $[$_]*, $_
```

```grammar
forall $_ $[$_]*, $_
```

通用量词绑定一个或多个变量，这些变量随后位于最终术语的范围内。
标识符也可以是`_`。
使用带括号的类型注释，多个绑定变量可以具有不同的类型，而不带括号的变体则要求所有变量具有相同的类型。
:::

尽管全称量词由函数表示，但它们的证明不应被视为计算。
由于证明无关性和命题的消除限制，无法使用这些证明来实际计算数据。
因此，他们可以自由地使用不易计算的推理原理，例如经典的选择公理。


存在量化被实现为类似于 {name}`Subtype` 和 {name}`Sigma` 的结构：它包含 {deftech}_witness_，它是满足谓词的值，以及见证人实际上满足谓词的证明。
换句话说，它是依赖对类型的一种形式。
与 {name}`Subtype` 和 {name}`Sigma` 不同，它是一个 {tech (key := "proposition")}[命题]；这意味着程序通常不能使用存在语句的证明来获取满足谓词的值。

编写证明时，{tactic}`exists`策略允许为（可能嵌套的）存在性陈述指定一个（或多个）证人。
另一方面，{tactic}`constructor`策略为见证人创建一个 {tech (key := "metavariable")}[元变量]；提供谓词的证明也可以解决元变量。
存在假设的组成部分可以通过模式匹配与 {tactic}`let` 或 {tactic (show := "match")}`Lean.Parser.Tactic.match` 以及使用 {tactic}`cases` 或 {tactic}`rcases` 单独提供。

:::example "Proving Existential Statements"

当证明存在一些自然数是 4 和 5 之和时，{tactic}`exists`策略期望提供总和，使用 {tactic}`trivial` 构造相等证明：

```lean
theorem ex_four_plus_five : ∃ n, 4 + 5 = n := by
  exists 9
```

另一方面，{tactic}`constructor`策略需要一个证明。
{tactic}`rfl`策略导致总和被确定为检查 定义等价 的副作用。

```lean
theorem ex_four_plus_five' : ∃ n, 4 + 5 = n := by
  constructor
  rfl
```


:::

{docstring Exists}

:::syntax term (title := "Existential Quantification")

```grammar
∃ $x:ident $[$_:ident]* $[: $t]?, $_
```
```grammar
exists $x:ident $[$_:ident]* $[: $t]?, $_
```

```grammar
∃ $_ $[$_]*, $_
```

```grammar
exists $_ $[$_]*, $_
```

存在量词绑定一个或多个变量，这些变量在最后一项的范围内。
标识符也可以是`_`。
使用带括号的类型注释，多个绑定变量可以具有不同的类型，而不带括号的变体则要求所有变量具有相同的类型。
如果绑定多个变量，则结果是 {name}`Exists` 的多个实例，嵌套在右侧。
:::

{docstring Exists.choose}

# 命题等价
%%%
tag := "propositional-equality"
%%%

{deftech (key := "Propositional equality")}_命题等价_是允许将两个项的相等性表述为命题的运算符。
必要时会自动检查 {tech (key := "Definitional equality")}[定义等价]。
因此，为了保持检查它的算法快速且易于理解，它的表达能力受到限制。
另一方面，命题等价 必须显式证明并显式使用 - Lean 检查证明的有效性，而不是确定陈述是否正确。
作为交换，它更具表现力：许多术语在命题上相等，但在定义上并不相等。

命题等价 定义为归纳类型。
它的唯一构造函数 {name}`Eq.refl` 要求两个相等的值相同；这隐含地呼吁 {tech (key := "definitional equality")}[定义等价]。
命题等价 也可以被认为是模 定义等价 的最小自反关系。
除了 {name}`Eq.refl` 之外，等式证明还由 {name}`propext` 和 {name}`Quot.sound` 公理生成。


{docstring Eq}

:::syntax term (title := "Propositional Equality")
```grammar
$_ = $_
```
命题等价 通常由中缀 `=` 运算符表示。
:::

{docstring rfl}

{docstring Eq.symm}

{docstring Eq.trans}

{docstring Eq.subst}

{docstring cast}

{docstring congr}

{docstring congrFun}

{docstring congrArg}

{docstring Eq.mp}

{docstring Eq.mpr}

:::syntax term (title := "Casting")
```grammar
$_ ▸ $_
```
当项的类型包含等式的一侧作为子项时，可以使用 `▸` 运算符重写它。
如果等式的两边都出现在项的类型中，则左侧将被重写为右侧。
:::

## 平等证明的唯一性
%%%
tag := "UIP"
%%%

:::keepEnv

由于定义证明无关，命题等价 证明是唯一的：两个数学对象不能以不同的方式相等。

```lean
theorem Eq.unique {α : Sort u}
    (x y : α)
    (p1 p2 : x = y) :
    p1 = p2 := by
  rfl
```

Streicher 的公理 K{citep streicher1993}[] 也是定义证明无关性的结果，其计算规则也是如此。
Axiom K 是逻辑上等同于 {name}`Eq.unique` 的原理，作为 命题等价 的替代 {tech (key := "recursor")}[递归器] 实现。
```lean
def K {α : Sort u}
    {motive : {x : α} → x = x → Sort v}
    (d : {x : α} → motive (Eq.refl x))
    (x : α) (z : x = x) :
    motive z :=
  d

example {α : Sort u} {a : α}
    {motive : {x : α} → x = x → Sort u}
    {d : {x : α} → motive (Eq.refl x)}
    {v : motive (Eq.refl a)} :
    K (motive := motive) d a rfl = d := by
  rfl
```

:::

## 异质平等
%%%
tag := "HEq"
%%%

{deftech}_Heterogeneous equality_ is a version of {tech (key := "propositional equality")}[命题等价] that does not require that the two equated terms have the same type.
然而，使用 {name}`rfl` 的版本_证明_这些项是相等的需要类型和项在定义上是相等的。
换句话说，它允许制定更多的陈述。

异构相等在实践中通常不如普通的 命题等价 方便。
由于不要求等式两边都具有相同的类型而提供了更大的灵活性，这意味着它具有更少的有用属性。
由于依赖模式匹配，经常会遇到这种情况：当准确反映相应控制流所需的普通等式假设类型不正确时，{tactic}`split`、策略和函数归纳 {TODO}[xref] 将异构等式假设添加到上下文中。
在这些情况下，内置自动化别无选择，只能使用异构平等。


{docstring HEq}

:::syntax term (title := "Heterogeneous Equality")
```grammar
$_ ≍ $_
```

```lean -show
section
variable (x : α) (y : β)
```
异构相等{lean}`HEq x y`可以写成{lean}`x ≍ y`。
```lean -show
end
```

:::

{docstring HEq.rfl}


:::::leanSection
::::example "Heterogeneous Equality"
```lean -show
variable {α : Type u} {n k l₁ l₂ l₃ : Nat}
```

{lean}`Vector α n` 类型是 {lean}`Array α` 的包装，其中包括数组大小为 {lean}`n` 的证明。
附加 {name}`Vector` 是关联的，但不能使用普通的 命题等价 直接说明这一事实：
```lean
variable
  {xs : Vector α l₁} {ys : Vector α l₂} {zs : Vector α l₃}
set_option linter.unusedVariables false
```
```lean (name := assocFail) +error -keep
theorem Vector.append_associative :
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by sorry
```
问题是自然数的加法结合性在命题上成立，但在定义上不成立：
```leanOutput assocFail
Type mismatch
  xs ++ ys ++ zs
has type
  Vector α (l₁ + l₂ + l₃)
but is expected to have type
  Vector α (l₁ + (l₂ + l₃))
```

:::paragraph
解决此问题的一种方法是在语句中使用自然数加法的结合律：
```lean
theorem Vector.append_associative' :
    xs ++ (ys ++ zs) =
    Nat.add_assoc _ _ _ ▸ ((xs ++ ys) ++ zs) := by
  sorry
```
然而，在某些情况下，此类证明陈述可能很难使用。
:::

:::paragraph
另一种是使用异构平等：
```lean -keep
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by sorry
```
:::

在这种情况下，{ref "the-simplifier"}[简化器]可以重写方程两边，而不必保留它们的类型。
然而，证明该定理确实需要最终证明长度仍然匹配。
```lean -keep
theorem Vector.append_associative :
    HEq (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs) := by
  cases xs; cases ys; cases zs
  simp
  congr 1
  . omega
  . apply heq_of_eqRec_eq
    . rfl
    . apply propext
      constructor <;> intro h <;> simp_all +arith
```
::::
:::::

{docstring HEq.elim}

{docstring HEq.ndrec}

{docstring HEq.ndrecOn}

{docstring HEq.subst}

{docstring eq_of_heq}

{docstring heq_of_eq}

{docstring heq_of_eqRec_eq}

{docstring eqRec_heq}

{docstring cast_heq}

{docstring heq_of_heq_of_eq}

{docstring type_eq_of_heq}
