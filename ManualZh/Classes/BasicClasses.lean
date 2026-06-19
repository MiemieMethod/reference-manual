/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option maxHeartbeats 250000

#doc (Manual) "基础课程" =>
%%%
tag := "basic-classes"
%%%

许多 Lean 类型类的存在是为了允许重载内置符号（例如加法或数组索引）。

# 布尔相等测试

通过定义 {name}`BEq` 的实例来重载布尔相等运算符 `==`。
伴随类 {name}`Hashable` 指定类型的哈希过程。
当类型同时具有 {name}`BEq` 和 {name}`Hashable` 实例时，计算的哈希值应遵循 {name}`BEq` 实例：由 {name}`BEq.beq` 等同的两个值应始终具有相同的哈希值。

{docstring BEq}

{docstring Hashable}

{docstring mixHash}

{docstring LawfulBEq}

{docstring ReflBEq}

{docstring EquivBEq}

{docstring LawfulHashable}

{docstring hash_eq}

# 订购

对类型的值进行排序有两种主要方法：
 * {name}`Ord` 类型类提供三向比较运算符 {name}`compare`，它可以指示一个值小于、等于或大于另一个值。它返回 {name}`Ordering`。
 * {name}`LT` 和 {name}`LE` 类为不需要可判定的类型提供规范的 {lean}`Prop` 值排序关系。这些关系用于重载 `<` 和 `≤` 运算符。

{docstring Ord}

{name}`compare` 方法已导出，因此不需要显式 `Ord` 命名空间即可使用它。

{docstring compareOn}

{docstring Ord.opposite}

{docstring Ordering}

{docstring Ordering.swap}

{docstring Ordering.then}

{docstring Ordering.isLT}

{docstring Ordering.isLE}

{docstring Ordering.isEq}

{docstring Ordering.isNe}

{docstring Ordering.isGE}

{docstring Ordering.isGT}

{docstring compareOfLessAndEq}

{docstring compareOfLessAndBEq}

{docstring compareLex}

:::syntax term (title := "Ordering Operators")

小于运算符在 {name}`LT` 类中重载：

```grammar
$_ < $_
```

小于或等于运算符在 {name}`LE` 类中重载：

```grammar
$_ ≤ $_
```

大于和大于或等于运算符与小于和小于或等于运算符相反，并且不能独立重载：

```grammar
$_ > $_
```

```grammar
$_ ≥ $_
```

:::

{docstring LT}

{docstring LE}

{name}`Ord` 可用于通过以下帮助程序构造 {name}`BEq`、{name}`LT` 和 {name}`LE` 实例。
它们不会自动成为实例，因为许多类型可以通过自定义关系更好地服务。

{docstring ltOfOrd}

{docstring leOfOrd}

{docstring Ord.toBEq}

{docstring Ord.toLE}

{docstring Ord.toLT}

:::example "Using `Ord` Instances for `LT` and `LE` Instances"

Lean 可以自动派生 {name}`Ord` 实例。
在本例中，{inst}`Ord Vegetable` 实例按字典顺序比较蔬菜：
```lean
structure Vegetable where
  color : String
  size : Fin 5
deriving Ord
```

```lean
def broccoli : Vegetable where
  color := "green"
  size := 2

def sweetPotato : Vegetable where
  color := "orange"
  size := 3
```


使用帮助程序 {name}`ltOfOrd` 和 {name}`leOfOrd`，可以定义 {inst}`LT Vegetable` 和 {inst}`LE Vegetable` 实例。
这些实例使用 {name}`compare` 比较蔬菜，并逻辑断言结果符合预期。
```lean
instance : LT Vegetable := ltOfOrd
instance : LE Vegetable := leOfOrd
```

结果关系是可判定的，因为对于 {lean}`Ordering` 相等性是可判定的：

```lean (name := brLtSw)
#eval broccoli < sweetPotato
```
```leanOutput brLtSw
true
```
```lean (name := brLeSw)
#eval broccoli ≤ sweetPotato
```
```leanOutput brLeSw
true
```
```lean (name := brLtBr)
#eval broccoli < broccoli
```
```leanOutput brLtBr
false
```
```lean (name := brLeBr)
#eval broccoli ≤ broccoli
```
```leanOutput brLeBr
true
```
:::

## 实例构建

{docstring Ord.lex}

{docstring Ord.lex'}

{docstring Ord.on}

# 最小值和最大值

类 `Max` 和 `Min` 提供重载运算符来选择两个值中的较大或较小值。
这些应该与 `Ord`、`LT` 和 `LE` 实例（如果存在）一致，但没有机制强制执行这一点。

{docstring Min}

{docstring Max}

:::leanSection

```lean -show
variable {α : Type u} [LE α]
```

给定 {name}`LE.le` 可判定的 {inst}`LE α` 实例，助手 {name}`minOfLe` 和 {name}`maxOfLe` 可用于创建合适的 {lean}`Min α` 和 {lean}`Max α` 实例。
它们可以用作 {keywordOf Lean.Parser.Command.declaration}`instance` 声明的右侧。

{docstring minOfLe}

{docstring maxOfLe}

:::

# 可判定性
%%%
tag := "decidable-propositions"
%%%

如果可以通过算法检查，则命题为 {deftech}_decidable_。{index}[decidable]{index (subterm := "decidable")}[proposition]
排除中间定律意味着每个命题都是真或假，但它没有提供方法来检查这两种情况中哪一个成立，这通常是有用的。
默认情况下，只有可以生成代码的算法 {lean}`Decidable` 实例才在范围内；打开 `Classical` 命名空间使每个命题都可判定。

{docstring Decidable}

{docstring DecidablePred}

{docstring DecidableRel}

{docstring DecidableEq}

{docstring DecidableLT}

{docstring DecidableLE}

{docstring Decidable.decide}

{docstring Decidable.byCases}

::::keepEnv
:::example "Excluded Middle and {lean}`Decidable`"
从 {lean}`Nat` 到 {lean}`Nat` 的函数相等不可判定：
```lean +error (name := NatFunNotDecEq)
example (f g : Nat → Nat) : Decidable (f = g) := inferInstance
```
```leanOutput NatFunNotDecEq
failed to synthesize instance of type class
  Decidable (f = g)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

打开 `Classical` 使得每个命题都是可判定的；但是，使用此事实的声明和示例必须标记为 {keywordOf Lean.Parser.Command.declaration}`noncomputable` 以指示不应为它们生成代码。
```lean
open Classical
noncomputable example (f g : Nat → Nat) : Decidable (f = g) :=
  inferInstance
```

:::
::::


# 居住类型

{docstring Inhabited}

{docstring Nonempty}

# 子单例类型

{docstring Subsingleton}

{docstring Subsingleton.elim}

{docstring Subsingleton.helim}

# 可见的表示
%%%
draft := true
%%%

:::planned 135
 * 转字符串
 * 外部参考 Repr 部分
 * 何时使用 {name}`Repr` 与 {name}`ToString`
:::


{docstring ToString +allowMissing}

# 算术和位运算符

{docstring Zero}

{docstring NeZero}

{docstring HAdd}

{docstring Add}

{docstring HSub}

{docstring Sub}

{docstring HMul}

{docstring SMul}

{docstring Mul}

{docstring HDiv}

{docstring Div}

{docstring Dvd}

{docstring HMod}

{docstring Mod}

{docstring HPow}

{docstring Pow}

{docstring NatPow}

{docstring HomogeneousPow}

{docstring HShiftLeft}

{docstring ShiftLeft}

{docstring HShiftRight}

{docstring ShiftRight}

{docstring Neg}

{docstring HAnd}

{docstring AndOp}

{docstring HOr}

{docstring OrOp}

{docstring HXor}

{docstring XorOp}

# 附加

{docstring HAppend}

{docstring Append}

# 数据查找

{docstring GetElem}

{docstring GetElem?}

{docstring LawfulGetElem}
