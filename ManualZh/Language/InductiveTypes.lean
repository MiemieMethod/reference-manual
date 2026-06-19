/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Meta.LexedText
import ManualZh.Language.InductiveTypes.LogicalModel
import ManualZh.Language.InductiveTypes.Structures
import ManualZh.Language.InductiveTypes.Nested

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option maxRecDepth 800

#doc (Manual) "归纳类型" =>
%%%
tag := "inductive-types"
%%%


{deftech}_感应类型_是向Lean引入新类型的主要手段。
虽然 {tech}[universes]、{tech}[functions] 和 {tech}[quotient types] 是用户无法添加的内置原语，但 Lean 中的所有其他类型要么是归纳类型，要么是根据 Universe、函数和归纳类型定义的。
归纳类型由其 {deftech}_type 构造函数_ {index}[类型构造函数] 及其 {deftech}_constructors_ 指定； {index}[构造函数]它们的其他属性都是从这些派生的。
每个归纳类型都有一个类型构造函数，它可以同时采用 {tech}[全域参数] 和普通参数。
归纳类型可以有任意数量的构造函数；这些构造函数引入了新值，其类型以归纳类型的类型构造函数为首。

基于类型构造函数和归纳类型的构造函数，Lean 派生 {deftech}_recursor_{index}[recursor]{see "recursor"}[eliminator]。
逻辑上，递归代表归纳原则或消除规则；在计算上，它们代表原始的递归计算。
递归函数的终止是通过将它们转换为递归器的使用来证明的，因此 Lean 的内核只需要执行递归应用程序的类型检查，而不需要包括单独的终止分析。
Lean 另外还生成许多基于递归器的辅助构造，{margin}[始终使用术语_recursor_，即使对于非递归类型也是如此。]它们在系统的其他地方使用。


_结构_ 是归纳类型的一种特殊情况，只有一个构造函数。
声明结构时，Lean 会生成帮助程序，使其他语言功能能够与新结构一起使用。

本节介绍用于指定归纳类型和结构的语法的具体细节、环境中由归纳类型声明产生的新常量和定义，以及编译代码中归纳类型' 值的运行时表示。

# 归纳类型声明
%%%
tag := "inductive-declarations"
%%%

:::syntax command (alias := «inductive») (title := "Inductive Type Declarations")
```grammar
$_:declModifiers
inductive $d:declId $_:optDeclSig where
  $[| $_ $c:ident $_]*
$[deriving $[$x:ident],*]?
```

声明新的归纳类型。
{syntaxKind}`declModifiers` 的含义如 {ref "declaration-modifiers"}[关于声明修饰符] 部分所述。
:::

声明归纳类型后，其类型构造函数、构造函数和递归器将出现在环境中。
新的归纳类型扩展了 Lean 的核心逻辑 - 它们不由其他一些已存在的数据编码或表示。
归纳类型声明必须满足 {ref "well-formed-inductives"}[许多格式良好的要求]，以确保逻辑保持一致。

声明的第一行，从 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`inductive` 到 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`，指定新的 {tech}[类型构造函数] 的名称和类型。
如果提供了类型构造函数的类型签名，则其结果类型必须是 {tech}[universe]，但参数不需要是类型。
如果未提供签名，则 Lean 将尝试推断一个刚好足以包含结果类型的 Universe。
在某些情况下，此过程可能无法找到最小宇宙或根本找不到最小宇宙，因此需要注释。

构造器规范遵循{keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`where`。
构造函数不是强制性的，因为无构造函数的归纳类型（例如 {lean}`False` 和 {lean}`Empty`）是完全合理的。
每个构造函数规范均以竖线（`'|'`、Unicode `'VERTICAL BAR' (U+007c)`）、声明修饰符和名称开头。
该名称是 {tech}[原始标识符]。
名称后面有声明签名。
签名可以指定任何参数，以归纳类型声明的格式良好性要求为模，但签名中的返回类型必须是指定的归纳类型的类型构造函数的饱和应用程序。
如果未提供签名，则通过插入足够的隐式参数来构造格式正确的返回类型来推断构造函数的类型。

新归纳类型的名称在 {tech}[当前命名空间] 中定义。
每个构造函数的名称位于归纳类型的命名空间中。{index (subterm := "of inductive type")}[命名空间]

## 参数及指标
%%%
tag := "inductive-datatypes-parameters-and-indices"
%%%

Type 构造函数可以采用两种参数： {deftech}_parameters_ {index (subterm := "of inductive type")}[parameter] 和 {deftech (key := "index")}_indices_.{index (subterm := "of inductive type")}[index]
整个定义中参数的使用必须一致；声明中每个构造函数中所有出现的类型构造函数都必须采用完全相同的参数。
索引可能因类型构造函数的出现而异。
所有参数必须位于类型构造函数签名中的所有索引之前。

类型构造函数签名中冒号 (`':'`) 之前出现的参数被视为整个归纳类型声明的参数。
它们始终是在整个类型定义中必须保持一致的参数。
一般来说，出现在冒号之后的参数是在整个类型定义中可能变化的索引。
然而，如果选项 {option}`inductive.autoPromoteIndices` 是 {lean}`true`，则本来可以是参数的语法索引将变成参数。
如果索引的所有类型依赖项本身都是参数，并且在所有构造函数中出现的归纳类型类型构造函数中统一用作未实例化的变量，则索引可能是参数。

{optionDocs inductive.autoPromoteIndices}

索引可以被视为定义类型的_family_。
每个索引选择都会从该族中选择一个类型，该族有自己的一组可用构造函数。
据说带有索引的 Type 构造函数指定类型的 {deftech}_indexed family_ {index (subterm := "of types")}[indexed family]。

## 示例归纳类型
%%%
tag := "example-inductive-types"
%%%

:::example "A constructorless type"
{lean}`Vacant` 是一个空的归纳类型，相当于 Lean 的 {lean}`Empty` 类型：
```lean
inductive Vacant : Type where
```

空的归纳类型并不是没有用；它们可用于指示无法访问的代码。
:::

:::example "A constructorless proposition"
{lean}`No` 是一个假 {tech}[命题]，等价于 Lean 的 {lean}`False`：
```lean
inductive No : Prop where
```

```lean -show -keep
theorem no_is_false : No = False := by
  apply propext
  constructor <;> intro h <;> cases h
```
:::

:::example "A unit type" (keep := true)
{lean}`Solo` 相当于 Lean 的 {lean}`Unit` 类型：
```lean
inductive Solo where
  | solo
```
这是归纳类型的示例，其中类型构造函数和构造函数的签名均被省略。
Lean 将 {lean}`Solo` 分配给 {lean}`Type`：
```lean (name := OneTy)
#check Solo
```
```leanOutput OneTy
Solo : Type
```
该构造函数被命名为 {lean}`Solo.solo`，因为构造函数名称是类型构造函数的命名空间。
由于 {lean}`Solo` 不需要任何参数，因此为 {lean}`Solo.solo` 推断的签名为：
```lean (name := oneTy)
#check Solo.solo
```
```leanOutput oneTy
Solo.solo : Solo
```
:::


:::example "A true proposition"
{lean}`Yes` 等价于 Lean 的 {lean}`True` 命题：

```lean
inductive Yes : Prop where
  | intro
```
与 {lean}`One` 不同，新的归纳类型{lean}`Yes` 被指定位于 {lean}`Prop` Universe 中。
```lean (name := YesTy)
#check Yes
```
```leanOutput YesTy
Yes : Prop
```
{lean}`Yes.intro` 推断的签名是：
```lean (name := yesTy)
#check Yes.intro
```
```leanOutput yesTy
Yes.intro : Yes
```

```lean -show -keep
theorem yes_is_true : Yes = True := by
  apply propext
  constructor <;> intros <;> constructor
```
:::

::::example "A type with parameter and index" (keep := true)

:::keepEnv
```lean -show
universe u
axiom α : Type u
axiom b : Bool
```

{lean}`EvenOddList α b` 是一个列表，其中 {lean}`α` 是列表中存储的数据类型，当条目数为偶数时，{lean}`b` 是 {lean}`true`：
:::

```lean
inductive EvenOddList (α : Type u) : Bool → Type u where
  | nil : EvenOddList α true
  | cons : α → EvenOddList α isEven → EvenOddList α (not isEven)
```

此示例的类型正确，因为列表中有两个条目：
```lean
example : EvenOddList String true :=
  .cons "a" (.cons "b" .nil)
```

此示例的类型不正确，因为列表中有三个条目：
```lean +error (name := evenOddOops)
example : EvenOddList String true :=
  .cons "a" (.cons "b" (.cons "c" .nil))
```
```leanOutput evenOddOops
Type mismatch
  EvenOddList.cons "a" (EvenOddList.cons "b" (EvenOddList.cons "c" EvenOddList.nil))
has type
  EvenOddList String !!!true
but is expected to have type
  EvenOddList String true
```

:::keepEnv
```lean -show
universe u
axiom α : Type u
axiom b : Bool
```

在此声明中，{lean}`α` 是 {tech}[参数]，因为它在所有出现的 {name}`EvenOddList` 中一致使用。
{lean}`b` 是 {tech}[索引]，因为它在不同的情况下使用不同的 {lean}`Bool` 值。
:::


```lean -show -keep
def EvenOddList.length : EvenOddList α b → Nat
  | .nil => 0
  | .cons _ xs => xs.length + 1

theorem EvenOddList.length_matches_evenness (xs : EvenOddList α b) : b = (xs.length % 2 = 0) := by
  induction xs
  . simp [length]
  next b' _ xs ih =>
    simp [length]
    cases b' <;> simp only [Bool.true_eq_false, false_iff, true_iff] <;> simp at ih <;> omega
```
::::

:::::keepEnv
::::example "Parameters before and after the colon"

在此示例中，两个参数均在 {name}`Either` 签名中的冒号之前指定。

```lean
inductive Either (α : Type u) (β : Type v) : Type (max u v) where
  | left : α → Either α β
  | right : β → Either α β
```

在此版本中，有两种名为 `α` 的类型可能不相同：
```lean (name := Either') +error
inductive Either' (α : Type u) (β : Type v) : Type (max u v) where
  | left : {α : Type u} → {β : Type v} → α → Either' α β
  | right : β → Either' α β
```
```leanOutput Either'
Mismatched inductive type parameter in
  Either' α β
The provided argument
  α
is not definitionally equal to the expected parameter
  α✝

Note: The value of parameter `α✝` must be fixed throughout the inductive declaration. Consider making this parameter an index if it must vary.
```

将参数放在冒号后面会产生可由构造函数实例化的参数：
```lean (name := Either'')
inductive Either'' : Type u → Type v → Type (max u v + 1) where
  | left : {α : Type u} → {β : Type v} → α → Either'' α β
  | right : β → Either'' α β
```
此类型需要更大的 Universe，因为 {ref "inductive-type-universe-levels"}[构造函数参数必须位于比归纳类型的 Universe 小的 Universe 中]。
{name}`Either''.right` 的类型参数是通过 Lean 的 {tech}[自动隐式参数] 的普通规则发现的。
::::
:::::


## 匿名构造函数语法
%%%
tag := "anonymous-constructor-syntax"
%%%

如果归纳类型只有一个构造函数，则该构造函数符合 {deftech}_匿名构造函数语法_。
可以将显式参数括在尖括号（`'⟨'` 和 `'⟩'`、Unicode `MATHEMATICAL LEFT ANGLE BRACKET	(U+0x27e8)` 和 `MATHEMATICAL RIGHT ANGLE BRACKET	(U+0x27e9)`）中并用逗号分隔，而不是将构造函数的名称写入其参数。
这在模式和表达式上下文中都有效。
按名称提供参数或使用 `@` 将所有隐式参数转换为显式参数需要使用普通构造函数语法。

:::syntax term (title := "Anonymous Constructors")
可以通过将构造函数的显式参数括在尖括号中并用逗号分隔来匿名调用。
```grammar
⟨ $_,* ⟩
```
:::

::::example "Anonymous constructors"

:::keepEnv
```lean -show
axiom α : Type
```
{lean}`AtLeastOne α` 类型与 `List α` 类似，只不过始终至少存在一个元素：
:::

```lean
inductive AtLeastOne (α : Type u) : Type u where
  | mk : α → Option (AtLeastOne α) → AtLeastOne α
```

可以使用匿名构造函数语法来构造它们：
```lean
def oneTwoThree : AtLeastOne Nat :=
  ⟨1, some ⟨2, some ⟨3, none⟩⟩⟩
```
并与他们匹配：
```lean
def AtLeastOne.head : AtLeastOne α → α
  | ⟨x, _⟩ => x
```

同样，可以使用传统的构造函数语法：
```lean
def oneTwoThree' : AtLeastOne Nat :=
  .mk 1 (some (.mk 2 (some (.mk 3 none))))

def AtLeastOne.head' : AtLeastOne α → α
  | .mk x _ => x
```
::::


## 派生实例
%%%
tag := "inductive-declarations-deriving-instances"
%%%

归纳类型声明的可选 {keywordOf Lean.Parser.Command.declaration (parser:=«inductive»)}`deriving` 子句可用于派生类型类的实例。
更多信息请参考{ref "deriving-instances"}[实例派生部分]。


{include 0 ManualZh.Language.InductiveTypes.Structures}

{include 0 ManualZh.Language.InductiveTypes.LogicalModel}

# 运行时表示
%%%
tag := "run-time-inductives"
%%%

归纳类型的运行时表示取决于它有多少个构造函数、每个构造函数采用多少个参数以及这些参数是否是 {tech}[相关]。

## 例外情况
%%%
tag := "inductive-types-runtime-special-support"
%%%

并非每个归纳类型都按此处所示表示 - 某些归纳类型具有 Lean 编译器的特殊支持：
:::keepEnv
```lean -show
axiom α : Prop
```

 * 固定位宽整数 类型 {lean}`UInt8`、...、{lean}`UInt64`、{lean}`Int8`、...、{lean}`Int64` 和 {lean}`USize` 的表示形式取决于代码是针对 32 位架构还是针对 64 位架构进行编译。
  它们的表示被描述为 {ref "fixed-int-runtime"}[在专门的部分中]。

 * {lean}`Char` 由 `uint32_t` 表示。由于 {lean}`Char` 值不需要超过 21 位，因此它们始终未装箱。

 * {lean}`Float` 由指向包含“double”的 Lean 对象的指针表示。

 * {deftech}_enum inducing_ 类型至少为 2，最多为 $`2^{32}` constructors, each of which has no parameters, is represented by the first type of {C}`uint8_t`、{C}`uint16_t`、{C}`uint32_t`，足以为每个构造函数分配唯一值。例如，类型 {lean}`Bool` 由 {C}`uint8_t` 表示，其中值 {C}`0` 代表 {lean}`false`，{C}`1` 代表 {lean}`true`。 {TODO}[看看这是否应该说“无相关参数”]

 * {lean}`Decidable α` 的表示方式与 `Bool` {TODO} 相同[Decidable 和 Bool 不是简单构造函数和无关性规则的特殊情况吗？]

 * {lean}`Nat` 和 {lean}`Int` 由 {C}`lean_object *` 表示。
  它们的表示在 {ref "nat-runtime"}[关于自然数的部分]和 {ref "int-runtime"}[关于整数的部分]中有更详细的描述。

:::

## 关联
%%%
tag := "inductive-types-runtime-relevance"
%%%


类型和证明没有运行时表示。
也就是说，如果归纳类型是 `Prop`，则其值会在编译之前被擦除。
同样，所有定理陈述和类型都被删除。
具有运行时表示的类型称为 {deftech}_relevant_，而没有运行时表示的类型称为 {deftech}_irrelevant_。

:::example "Types are irrelevant"
尽管 {name}`List.cons` 具有以下签名，它指示三个参数：
```signature
List.cons.{u} {α : Type u} : α → List α → List α
```
它的运行时表示只有两个，因为类型参数与运行时无关。
:::

:::example "Proofs are irrelevant"
尽管 {name}`Fin.mk` 具有以下签名，它指示三个参数：
```signature
Fin.mk {n : Nat} (val : Nat) : val < n → Fin n
```
它的运行时表示只有两个，因为证明被删除了。
:::

在大多数情况下，不相关的值会从编译的代码中消失。
但是，在需要某种表示的情况下（例如当它们是多态构造函数的参数时），它们由一个简单的值表示。

## 简单的包装器
%%%
tag := "inductive-types-trivial-wrappers"
%%%

如果归纳类型恰好具有一个构造函数，并且该构造函数恰好具有一个运行时相关参数，则归纳类型的表示方式与其参数相同。

:::example "Zero-Overhead Subtypes"
结构 {name}`Subtype` 将某种类型的元素与其满足谓词的证明捆绑在一起。
它的构造函数有四个参数，但其中三个是不相关的：
```signature
Subtype.mk.{u} {α : Sort u} {p : α → Prop}
  (val : α) (property : p val) : Subtype p
```
因此，子类型不会在编译代码中产生运行时开销，并且与 {name Subtype.val}`val` 字段的类型相同地表示。
:::

:::example "Signed Integers"
有符号整数类型 {lean}`Int8`、...、{lean}`Int64`、{lean}`ISize` 是具有单个字段的结构，该字段包装相应的无符号整数类型。
它们分别由无符号 C 类型 {C}`uint8_t`、...、{C}`uint64_t`、{C}`size_t` 表示，因为它们具有简单的结构。
:::

## 其他归纳类型
%%%
tag := "inductive-types-standard-representation"
%%%


如果归纳类型不属于上述类别之一，则其表示由其构造函数确定。
没有相关参数的构造函数由它们在构造函数列表中的索引表示，作为未装箱的无符号机器整数（标量）。
具有相关参数的构造函数表示为一个对象，该对象具有标头、构造函数的索引、指向其他对象的指针数组，然后是按其类型排序的标量字段数组。
标头跟踪对象的引用计数和其他必要的簿记。

递归函数按照大多数编程语言的方式进行编译，而不是使用归纳类型的递归器。
将递归函数细化为递归器可以提供可靠的终止证据，而不是可执行代码。

### FFI
%%%
tag := "inductive-types-ffi"
%%%

从C的角度来看，这些其他的归纳类型都用{C}`lean_object *`来表示。
每个构造函数都存储为 {C}`lean_ctor_object`，并且 {C}`lean_is_ctor` 将返回 true。
{C}`lean_ctor_object` 将构造函数索引存储在其标头中，字段存储在对象的 {C}`m_objs` 部分中。
Lean 假设 {C}`sizeof(size_t) == sizeof(void*)` — 虽然 C 不保证这一点，但 Lean 运行时系统包含一个断言，如果情况并非如此，该断言将失败。


字段的内存顺序源自声明中字段的类型和顺序。它们的顺序如下：

* 非标量字段存储为 {C}`lean_object *`
* {lean}`USize` 类型的字段
* 其他标量场，按大小降序排列

在每个组中，字段按声明顺序排序。 *警告*：为此目的，普通包装类型被视为其基础包装类型。

* 要访问第一种字段，请使用 {C}`lean_ctor_get(val, i)` 获取第 `i` 个非标量字段。
* 要访问 {lean}`USize` 字段，请使用 {C}`lean_ctor_get_usize(val, n+i)` 获取第 {C}`i` `USize` 字段，{C}`n` 是第一类字段的总数。
* 要访问其他标量字段，请根据需要使用 {C}`lean_ctor_get_uintN(val, off)` 或 {C}`lean_ctor_get_usize(val, off)`。这里 `off` 是结构体中字段的字节偏移量，从 {C}`n*sizeof(void*)` 开始，其中 `n` 是前两种字段的数量。

::::keepEnv

例如，如下结构
```lean
structure S where
  ptr_1 : Array Nat
  usize_1 : USize
  sc64_1 : UInt64
   -- Wrappers of scalars count as scalars:
  sc64_2 : { x : UInt64 // x > 0 }
  sc64_3 : Float -- `Float` is 64 bit
  sc8_1 : Bool
  sc16_1 : UInt16
  sc8_2 : UInt8
  sc64_4 : UInt64
  usize_2 : USize
  -- Trivial wrapper around `UInt32`
  sc32_1 : Char
  sc32_2 : UInt32
  sc16_2 : UInt16
```
将被重新排序为以下内存顺序：

* {name}`S.ptr_1`: {C}`lean_ctor_get(val, 0)`
* {name}`S.usize_1`: {C}`lean_ctor_get_usize(val, 1)`
* {name}`S.usize_2`: {C}`lean_ctor_get_usize(val, 2)`
* {name}`S.sc64_1`: {C}`lean_ctor_get_uint64(val, sizeof(void*)*3)`
* {name}`S.sc64_2`: {C}`lean_ctor_get_uint64(val, sizeof(void*)*3 + 8)`
* {name}`S.sc64_3`: {C}`lean_ctor_get_float(val, sizeof(void*)*3 + 16)`
* {name}`S.sc64_4`: {C}`lean_ctor_get_uint64(val, sizeof(void*)*3 + 24)`
* {name}`S.sc32_1`: {C}`lean_ctor_get_uint32(val, sizeof(void*)*3 + 32)`
* {name}`S.sc32_2`: {C}`lean_ctor_get_uint32(val, sizeof(void*)*3 + 36)`
* {name}`S.sc16_1`: {C}`lean_ctor_get_uint16(val, sizeof(void*)*3 + 40)`
* {name}`S.sc16_2`: {C}`lean_ctor_get_uint16(val, sizeof(void*)*3 + 42)`
* {name}`S.sc8_1`: {C}`lean_ctor_get_uint8(val, sizeof(void*)*3 + 44)`
* {name}`S.sc8_2`: {C}`lean_ctor_get_uint8(val, sizeof(void*)*3 + 45)`

::::

::: TODO
弄清楚如何测试/验证/CI 这些语句
:::


# 相互归纳类型
%%%
tag := "mutual-inductive-types"
%%%


归纳类型可以相互递归。
归纳类型的相互递归定义是通过定义 `mutual ... end` 块中的类型来指定的。

:::example "Mutually Defined Inductive Types"
前面示例中的类型 {name}`EvenOddList` 使用布尔索引来选择所讨论的列表是否应具有偶数或奇数个元素。
这种区别也可以通过选择两个相互归纳类型{name}`EvenList` 和 {name}`OddList` 之一来表达：

```lean
mutual
  inductive EvenList (α : Type u) : Type u where
    | nil : EvenList α
    | cons : α → OddList α → EvenList α
  inductive OddList (α : Type u) : Type u where
    | cons : α → EvenList α → OddList α
end

example : EvenList String := .cons "x" (.cons "y" .nil)
example : OddList String := .cons "x" (.cons "y" (.cons "z" .nil))
```
```lean +error (name := evenOddMut)
example : OddList String := .cons "x" (.cons "y" .nil)
```
```leanOutput evenOddMut
Unknown constant `OddList.nil`

Note: Inferred this name from the expected resulting type of `.nil`:
  OddList String
```
:::

## 要求
%%%
tag := "mutual-inductive-types-requirements"
%%%


`mutual` 块中声明的归纳类型被视为一个组；它们必须共同满足非互递归归纳类型的格式良好标准的广义版本。
即使可以在没有 `mutual` 块的情况下定义它们，情况也是如此，因为它们实际上不是相互递归的。

### 相互依赖
%%%
tag := "mutual-inductive-types-dependencies"
%%%

每个类型构造函数的签名必须能够在不引用 `mutual` 组中的其他归纳类型的情况下进行详细说明。
换句话说，`mutual`组中的归纳类型不能互相作为参数。
每个归纳类型的构造函数可以在其参数类型中提及组中的其他类型构造函数，其限制是非互归纳类型中递归出现的限制。

:::example "Mutual inductive type constructors may not mention each other"
Lean 不接受这些归纳类型：
```lean +error (name := mutualNoMention)
mutual
  inductive FreshList (α : Type) (r : α → α → Prop) : Type where
    | nil : FreshList α r
    | cons (x : α) (xs : FreshList α r) (fresh : Fresh r x xs)
  inductive Fresh
      (r : α → FreshList α → Prop) :
      α → FreshList α r → Prop where
    | nil : Fresh r x .nil
    | cons : r x y → (f : Fresh r x ys) → Fresh r x (.cons y ys f)
end
```

类型构造函数可能不引用 `mutual` 组中的其他类型构造函数，因此 `FreshList` 不在 `Fresh` 的类型构造函数的范围内：
```leanOutput mutualNoMention
Unknown identifier `FreshList`
```
:::


### 参数必须匹配
%%%
tag := "mutual-inductive-types-same-parameters"
%%%

`mutual` 组中的所有归纳类型必须具有相同的 {tech}[参数]。
它们的指数可能不同。

::::keepEnv
::: example "Differing numbers of parameters"
尽管 `Both` 和 `OneOf` 不是相互递归的，但它们是在同一 `mutual` 块中声明的，因此必须具有相同的参数：
```lean (name := bothOptional) +error
mutual
  inductive Both (α : Type u) (β : Type v) where
    | mk : α → β → Both α β
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput bothOptional
Invalid mutually inductive types: `Optional` has 1 parameter(s), but the preceding type `Both` has 2

Note: All inductive types declared in the same `mutual` block must have the same parameters
```
:::
::::

::::keepEnv
::: example "Differing parameter types"
尽管 `Many` 和 `OneOf` 不是相互递归的，但它们是在同一 `mutual` 块中声明的，因此必须具有相同的参数。
它们都只有一个参数，但 `Many` 的参数不一定与 `Optional` 的参数位于同一宇宙中：
```lean (name := manyOptional) +error
mutual
  inductive Many (α : Type) : Type u where
    | nil : Many α
    | cons : α → Many α → Many α
  inductive Optional (α : Type u) where
    | none
    | some : α → Optional α
end
```
```leanOutput manyOptional
Invalid mutually inductive types: Parameter `α` has type
  Type u
of sort `Type (u + 1)` but is expected to have type
  Type
of sort `Type 1`
```
:::
::::

### 宇宙层级
%%%
tag := "mutual-inductive-types-same-universe"
%%%

相互组中每个归纳类型的 宇宙层级 必须遵守与非相互递归归纳类型相同的要求。
此外，共同组中的所有归纳类型必须位于同一宇宙中，这意味着它们的构造函数在其参数的宇宙方面同样受到限制。

::::example "Universe mismatch"
:::keepEnv
这些相互归纳类型是表示列表的游程长度编码的一种有点复杂的方法：
```lean
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run (x : α) (n : Nat) :
    n ≠ 0 → PrefixRunOf n x xs ys → RLE ys → RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Type where
  | zero
    (noMore : ¬∃zs, xs = x :: zs := by simp) :
    PrefixRunOf 0 x xs xs
  | succ :
    PrefixRunOf n x xs ys →
    PrefixRunOf (n + 1) x (x :: xs) ys
end

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] :=
  .run 1 2 (by decide) (.succ (.succ .zero)) <|
  .run 2 2 (by decide) (.succ (.succ .zero)) <|
  .run 3 1 (by decide) (.succ .zero) <|
  .run 1 3 (by decide) (.succ (.succ (.succ (.zero)))) <|
  .nil
```

将 {name}`PrefixRunOf` 指定为 {lean}`Prop` 是明智的，但这是不可能的，因为这些类型将位于不同的 Universe 中：
:::

:::keepEnv
```lean +error (name := rleBad)
mutual
  inductive RLE : List α → Type where
  | nil : RLE []
  | run
    (x : α) (n : Nat) :
    n ≠ 0 → PrefixRunOf n x xs ys → RLE ys →
    RLE xs

  inductive PrefixRunOf : Nat → α → List α → List α → Prop where
  | zero
    (noMore : ¬∃zs, xs = x :: zs := by simp) :
    PrefixRunOf 0 x xs xs
  | succ :
    PrefixRunOf n x xs ys →
    PrefixRunOf (n + 1) x (x :: xs) ys
end
```
```leanOutput rleBad
Invalid mutually inductive types: The resulting type of this declaration
  Prop
differs from a preceding one
  Type

Note: All inductive types declared in the same `mutual` block must belong to the same type universe
```
:::

:::keepEnv
这个特殊的属性可以通过单独定义格式良好条件并使用子类型来表达：
```lean
def RunLengths α := List (α × Nat)
def NoRepeats : RunLengths α → Prop
  | [] => True
  | [_] => True
  | (x, _) :: ((y, n) :: xs) =>
    x ≠ y ∧ NoRepeats ((y, n) :: xs)
def RunsMatch : RunLengths α → List α → Prop
  | [], [] => True
  | (x, n) :: xs, ys =>
    ys.take n = List.replicate n x ∧
    RunsMatch xs (ys.drop n)
  | _, _ => False
def NonZero : RunLengths α → Prop
  | [] => True
  | (_, n) :: xs => n ≠ 0 ∧ NonZero xs
structure RLE (xs : List α) where
  rle : RunLengths α
  noRepeats : NoRepeats rle
  runsMatch : RunsMatch rle xs
  nonZero : NonZero rle

example : RLE [1, 1, 2, 2, 3, 1, 1, 1] where
  rle := [(1, 2), (2, 2), (3, 1), (1, 3)]
  noRepeats := by simp [NoRepeats]
  runsMatch := by simp [RunsMatch]
  nonZero := by simp [NonZero]
```
:::
::::


### 积极性
%%%
tag := "mutual-inductive-types-positivity"
%%%

`mutual` 组中定义的每个归纳类型只能严格正向出现在该组中所有类型的构造函数的参数类型中。
换句话说，在该组的所有类型中每个构造函数的每个参数的类型中，该组中的任何类型构造函数都不会出现在任何箭头的左侧，并且它们都不会出现在参数位置，除非它们是归纳类型的类型构造函数的参数。

::: example "Mutual strict positivity"
在以下共同组中，`Tm` 出现在 `Binding.scope` 参数中的负位置：
```lean +error (name := mutualHoas)
mutual
  inductive Tm where
    | app : Tm → Tm → Tm
    | lam : Binding → Tm
  inductive Binding where
    | scope : (Tm → Tm) → Binding
end
```
由于 `Tm` 是同一共同组的一部分，因此它只能严格正数出现在 `Binding` 构造函数的参数中。
然而，它的发生却是消极的：
```leanOutput mutualHoas
(kernel) arg #1 of 'Binding.scope' has a non positive occurrence of the datatypes being declared
```
:::

::: example "Nested positions"
{name}`LocatedStx` 和 {name}`Stx` 的定义满足正性条件，因为递归出现不在任何箭头的左侧，并且当它们是参数时，它们是归纳类型构造函数的参数。

```lean
mutual
  inductive LocatedStx where
    | mk (line col : Nat) (val : Stx)
  inductive Stx where
    | atom (str : String)
    | node (kind : String) (args : List LocatedStx)
end
```
:::

## 递归器
%%%
tag := "mutual-inductive-types-recursors"
%%%

相互的归纳类型提供有原始递归器，就像非相互定义的归纳类型一样。
这些递归器考虑到它们必须处理组中的其他类型，因此每个归纳类型都有一个动机。
由于 `mutual` 组中的所有归纳类型都需要具有相同的参数，因此递归器仍然首先采用参数，将它们抽象到动机和递归器的其余部分。
此外，由于递归程序必须处理组的其他类型，因此需要为组中每种类型的每个构造函数提供案例。
不考虑类型之间的实际依赖结构；即使由于相互依赖性较少而实际上并不需要额外的动机或构造函数，生成的递归器仍然需要它们。

::::keepEnv
::: example "Even and odd"
```lean
mutual
  inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : Odd n → Even (n + 1)
  inductive Odd : Nat → Prop where
    | succ : Even n → Odd (n + 1)
end
```

```signature
Even.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : {n : Nat} → (a : Odd n) → motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) →
  ∀ {a : Nat} (t : Even a), motive_1 a t
```

```signature
Odd.rec
  {motive_1 : (a : Nat) → Even a → Prop}
  {motive_2 : (a : Nat) → Odd a → Prop}
  (zero : motive_1 0 Even.zero)
  (succ : ∀ {n : Nat} (a : Odd n), motive_2 n a → motive_1 (n + 1) (Even.succ a)) :
  (∀ {n : Nat} (a : Even n), motive_1 n a → motive_2 (n + 1) (Odd.succ a)) → ∀ {a : Nat} (t : Odd a), motive_2 a t
```

:::
::::

::::keepEnv
:::example "Spuriously mutual types"
类型 {name}`Two` 和 {name}`Three` 在共同块中定义，即使它们不互相引用：
```lean
mutual
  inductive Two (α : Type) where
    | mk : α → α → Two α
  inductive Three (α : Type) where
    | mk : α → α → α → Three α
end
```
尽管如此，{name}`Two` 的递归器 {name}`Two.rec` 仍然需要 {name}`Three` 的动机和案例：
```signature
Two.rec.{u} {α : Type}
  {motive_1 : Two α → Sort u}
  {motive_2 : Three α → Sort u}
  (mk : (a a_1 : α) → motive_1 (Two.mk a a_1)) :
  ((a a_1 a_2 : α) → motive_2 (Three.mk a a_1 a_2)) → (t : Two α) → motive_1 t
```

:::
::::

## 运行时表示
%%%
tag := "mutual-inductive-types-run-time"
%%%

相互归纳类型在编译代码和运行时中的表示方式与 {ref "run-time-inductives"}[非相互归纳类型] 相同。
对相互归纳类型的限制的存在是为了确保 Lean 作为逻辑的一致性，并且不影响编译的代码。

{include 2 ManualZh.Language.InductiveTypes.Nested}

## 格理论归纳和共归纳谓词

归纳类型声明的语法可用于指定归纳谓词和共归纳谓词。
这些不是 Lean 类型系统的内置功能，而是精心设计成合适的编码。
它们在 {ref "coinductive-predicates"}[专用部分]中进行了描述。
