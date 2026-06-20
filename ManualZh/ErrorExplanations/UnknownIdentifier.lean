/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "关于：`unknownIdentifier`" =>
%%%
shortTitle := "unknownIdentifier"
%%%

{errorExplanationHeader lean.unknownIdentifier}

此错误意味着 Lean 无法找到与给定名称匹配的变量或常量。更多
准确地说，这意味着无法*解析*该名称，如手册部分中所述
{ref "identifiers-and-resolution"}[标识符]：不将输入解释为
局部变量或节变量的名称（如果适用）、先前声明的全局常量或
前述任何一项的预测都是有效的。 （“如果适用”是指在某些情况下
案例 - 例如，{keywordOf Lean.Parser.Command.print}`#print` 命令的参数 - 名称已解析
仅适用于全局常量。）

请注意，此错误消息将仅显示标识符的一种可能的解析，但
出现此错误表示它可能引用的*所有*可能的名称均失败。对于
例如，如果在命名空间 `A` 和 `B` 打开的情况下输入标识符 `x`，则错误
消息“未知标识符 \`x\`”表示找不到 `x`、`A.x` 或 `B.x` 中的任何一个（或
`A.x` 或 `B.x`（如果存在）是受保护的声明）。

导致此错误的常见原因包括忘记导入定义常量的模块，
当命名空间未打开时省略常量的命名空间，或尝试引用本地变量
variable that is not in scope.

为了帮助解决其中一些常见问题，此错误消息附带了一个代码操作，该操作
建议与所提供的名称类似的常量名称。这些包括环境中的常数
以及可以从其他模块导入的内容。请注意，这些建议可用
仅通过受支持的代码编辑器的内置代码操作机制，而不是作为错误中的提示
消息本身。

# 示例
%%%
tag := "zh-errorexplanations-unknownidentifier-h001"
%%%

:::errorExample "Variable Not in Scope"
```broken
example (s : IO.FS.Stream) := do
  IO.withStdout s do
    let text := "Hello"
    IO.println text
  IO.println s!"Wrote '{text}' to stream"
```
```output
Unknown identifier `text`
```
```fixed
example (s : IO.FS.Stream) := do
  let text := "Hello"
  IO.withStdout s do
    IO.println text
  IO.println s!"Wrote '{text}' to stream"
```
此示例的最后一行出现未知标识符错误，因为变量 `text` 是
不在范围内。第三行的 {keywordOf Lean.Parser.Term.let}`let` 绑定的范围是
内部 {keywordOf Lean.Parser.Term.do}`do` 块，不能
在外部 {keywordOf Lean.Parser.Term.do}`do` 块中访问。将此绑定移动到外部
{keywordOf Lean.Parser.Term.do}`do` 块——它仍然存在
也在内部块的范围内——解决了这个问题。
:::

:::errorExample "Missing Namespace"
```broken
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

def red : Color :=
  rgb 255 0 0
```
```output
Unknown identifier `rgb`
```
```fixed "qualified name"
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

def red : Color :=
  Color.rgb 255 0 0
```
```fixed "open namespace"
inductive Color where
  | rgb (r g b : Nat)
  | grayscale (k : Nat)

open Color in
def red : Color :=
  rgb 255 0 0
```

在此示例中，最后一行的标识符 `rgb` 不会解析为 `Color` 构造函数
那个名字的。这是因为构造函数的名称实际上是 `Color.rgb`：
inductive type have names in that type's namespace. Because the `Color` namespace is not open, the
如果没有命名空间前缀，则无法使用标识符 `rgb`。

解决此错误的一种方法是提供完全限定的构造函数名称 `Color.rgb`；的
也可以使用点标识符符号 `.rgb`，因为 `.rgb 255 0 0` 的预期类型是
`Color`。或者，可以打开 `Color` 命名空间并继续省略 `Color` 前缀
来自标识符。
:::

:::errorExample "Protected Constant Name Without Namespace Prefix"

```broken
protected def A.x := ()

open A

example := x
```
```output
Unknown identifier `x`
```
```fixed "qualified name"
protected def A.x := ()

open A

example := A.x
```
```fixed "restricted open"
protected def A.x := ()

open A (x)

example := x
```

在此示例中，由于常量 `A.x` 为 {keyword}`protected`，因此不能通过后缀引用它
`x` 即使命名空间 `A` 打开。因此，标识符 `x` 无法解析。相反，要
引用 {keyword}`protected` 常量时，必须至少包含其最内部的命名空间 - 在此
案例，`A`。或者，*限制打开*语法 - 在第二个更正的示例中演示
示例—允许通过其非限定名称引用 {keyword}`protected` 常量，而无需打开
它发生的命名空间的其余部分（请参阅手册部分
{ref "namespaces-sections"}[命名空间和部分]了解详细信息）。
:::

:::errorExample "Unresolvable Name Inferred by Dotted-Identifier Notation"

```broken
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  .toNat (b₁ || b₂)
```
```output
Unknown constant `Nat.toNat`

Note: Inferred this name from the expected resulting type of `.toNat`:
  Nat
```
```fixed "generalized field notation"
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  (b₁ || b₂).toNat
```
```fixed "qualified name"
def disjoinToNat (b₁ b₂ : Bool) : Nat :=
  Bool.toNat (b₁ || b₂)
```

在此示例中，点标识符符号 `.toNat` 导致 Lean 推断出无法解析的
名称 (`Nat.toNat`)。点标识符表示法使用的命名空间总是从
它出现的表达式的预期类型，由于类型注释
`disjoinToNat`—在此示例中为 `Nat`。使用参数类型的命名空间——作为作者
这段代码似乎是有意的——使用*通用字段表示法*，如第一个更正的代码所示
示例。或者，可以通过编写完整的名称空间来明确指定正确的名称空间
限定函数名称。
:::

:::errorExample "Auto-bound variables"

```broken
set_option relaxedAutoImplicit false in
def thisBreaks (x : α₁) (y : size₁) := ()

set_option autoImplicit false in
def thisAlsoBreaks (x : α₂) (y : size₂) := ()
```
```output
Unknown identifier `size₁`

Note: It is not possible to treat `size₁` as an implicitly bound variable here because it has multiple characters while the `relaxedAutoImplicit` option is set to `false`.
```
```fixed "modifying options"
set_option relaxedAutoImplicit true in
def thisWorks (x : α₁) (y : size₁) := ()

set_option autoImplicit true in
def thisAlsoWorks (x : α₂) (y : size₂) := ()
```
```fixed "add implicit bindings for the unknown identifiers"
set_option relaxedAutoImplicit false in
def thisWorks {size₁} (x : α₁) (y : size₁) := ()

set_option autoImplicit false in
def thisAlsoWorks {α₂ size₂} (x : α₂) (y : size₂) := ()
```

Lean 的默认行为，当它遇到无法在 a 类型中识别的标识符时
定义，就是添加{ref "automatic-implicit-parameters"}[自动隐式参数]
对于那些未知的标识符。然而，许多文件或项目通过设置禁用此功能
{option}`autoImplicit` 或 {option}`relaxedAutoImplicit` 选项至 {name}`false`。

无需重新启用 {option}`autoImplicit` 或 {option}`relaxedAutoImplicit` 选项，最简单的方法
修复此错误的方法是将未知标识符添加为
{ref "implicit-functions"}[普通隐式参数]如上例所示。
:::
