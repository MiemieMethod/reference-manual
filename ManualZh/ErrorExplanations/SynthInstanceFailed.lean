/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`synthInstanceFailed`" =>
%%%
file := "About___-___synthInstanceFailed___"
tag := "zh-errorexplanations-synthinstancefailed-root"
shortTitle := "synthInstanceFailed"
%%%

{errorExplanationHeader lean.synthInstanceFailed}

```lean -show
variable {t : Type} (x y : Int)
```

{ref "type-classes"}[Type 类] 是 Lean 和许多其他
编程语言用于处理重载操作。处理特定的代码
重载操作是一个类型类的{tech}_instance_；决定对于给定的情况使用哪个实例
重载操作称为_合成_实例。

例如，当 Lean 遇到表达式 {lean}`x + y` 时，其中 {lean}`x` 和 {lean}`y` 都
有类型 {name}`Int`，有必要查找它应该如何添加两个整数并查找
结果类型是什么。这被描述为合成类型类的实例
{lean}`HAdd Int Int t` 对于某些类型 `t`。

许多合成类型类实例失败的原因是使用了错误的二进制文件
操作。成功和失败并不总是那么简单，因为有些情况是
根据其他实例定义，并且 Lean 必须递归搜索以找到适当的实例。
可以 {ref "instance-search"}[检查 Lean 的实例合成]，并且这个
有助于诊断类型类实例合成的棘手故障。

# 示例
%%%
file := "Examples"
tag := "zh-errorexplanations-synthinstancefailed-h001"
%%%

:::errorExample "Using the Wrong Binary Operation"

```broken
#eval "A" + "3"
```
```output
failed to synthesize instance of type class
  HAdd String String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```fixed
#eval "A" ++ "3"
```

二元运算`+`与{name}`HAdd`类型类相关联，无法添加
两个字符串。与 {name}`HAppend` 类型类关联的二元运算 `++` 是
附加字符串的正确方法。
:::

:::errorExample "Arguments Have the Wrong Type"

```broken
def x : Int := 3
#eval x ++ "meters"
```
```output
failed to synthesize instance of type class
  HAppend Int String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```fixed
def x : Int := 3
#eval ToString.toString x ++ "meters"
```

Lean 不允许直接将整数和字符串相加。功能
{name}`ToString.toString` 使用类型类重载将值转换为字符串；通过成功
搜索 {lean}`ToString Int` 的实例，第二个示例将成功。
:::

:::errorExample "Missing Type Class Instance"

```broken
inductive MyColor where
  | chartreuse | sienna | thistle

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```output
failed to synthesize instance of type class
  Inhabited MyColor

Hint: Adding the command `deriving instance Inhabited for MyColor` may allow Lean to derive the missing instance.
```
```fixed "derive instance when defining type"
inductive MyColor where
  | chartreuse | sienna | thistle
deriving Inhabited

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```fixed "derive instance separately"
inductive MyColor where
  | chartreuse | sienna | thistle

deriving instance Inhabited for MyColor

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```fixed "define instance"
inductive MyColor where
  | chartreuse | sienna | thistle

instance : Inhabited MyColor where
  default := .sienna

def forceColor (oc : Option MyColor) :=
  oc.get!
```

Type 类综合可能会失败，因为只需要提供类型类的实例。
对于 {name}`Repr`、{name}`BEq`、{name}`ToJson` 等类型类，通常会发生这种情况
{name}`Inhabited`。 Lean 通常可以 {ref "deriving-instances"}[自动生成
带有 `deriving` 关键字的类型类] 在定义类型时或使用独立类型时
{keywordOf Lean.Parser.Command.deriving}`deriving` 命令。
:::
