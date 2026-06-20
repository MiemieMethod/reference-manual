/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
-- set_option trace.SubVerso.Highlighting.Code true

set_option guard_msgs.diff true

#doc (Manual) "句法" =>
%%%
tag := "zh-monads-syntax-root"
%%%

Lean 支持通过特殊语法使用函子、应用函子和 monad 进行编程：
 * 中缀运算符适用于最常见的操作。
 * 一种名为 {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation] 的嵌入式语言允许在 monad 中编写程序时使用命令式语法。

# 中缀运算符
%%%
tag := "zh-monads-syntax-h001"
%%%

中缀运算符主要在较小的表达式中或没有 {lean}`Monad` 实例时有用。

## 函子
%%%
tag := "zh-monads-syntax-h002"
%%%

```lean -show
section FOps
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {x : f α}
```
{name}`Functor.map` 有两个中缀运算符。

:::syntax term (title := "Functor Operators")
{lean}`g <$> x` 是 {lean}`Functor.map g x` 的缩写。
```grammar
$_ <$> $_
```

{lean}`x <&> g` 是 {lean}`Functor.map g x` 的缩写。
```grammar
$_ <&> $_
```
:::

```lean -show
example : g <$> x = Functor.map g x := by rfl
example : x <&> g = Functor.map g x := by rfl
end FOps
```

## 应用函子
%%%
tag := "zh-monads-syntax-h003"
%%%

```lean -show
section AOps
variable {f : Type u → Type v} [Applicative f] [Alternative f] {α β : Type u} {g : f (α → β)} {x e1 e e' : f α} {e2 : f β}
```

:::syntax term (title := "Applicative Operators")
{lean}`g <*> x` 是 {lean}`Seq.seq g (fun () => x)` 的缩写。
插入该函数是为了延迟计算，因为控制可能无法到达参数。
```grammar
$_ <*> $_
```

{lean}`e1 *> e2` 是 {lean}`SeqRight.seqRight e1 (fun () => e2)` 的缩写。
```grammar
$_ *> $_
```

{lean}`e1 <* e2` 是 {lean}`SeqLeft.seqLeft e1 (fun () => e2)` 的缩写。
```grammar
$_ <* $_
```
:::

许多应用函子还通过 {name}`Alternative` 类型类支持故障和恢复。
此类还有一个中缀运算符。

:::syntax term (title := "Alternative Operators")
{lean}`e <|> e'` 是 {lean}`OrElse.orElse e (fun () => e')` 的缩写。
插入该函数是为了延迟计算，因为控制可能无法到达参数。
```grammar
$_ <|> $_
```
:::


```lean -show
example : g <*> x = Seq.seq g (fun () => x) := by rfl
example : e1 *> e2 = SeqRight.seqRight e1 (fun () => e2) := by rfl
example : e1 <* e2 = SeqLeft.seqLeft e1 (fun () => e2) := by rfl
example : (e <|> e') = (OrElse.orElse e (fun () => e')) := by rfl
end AOps
```

:::::keepEnv
```lean
structure User where
  name : String
  favoriteNat : Nat
def main : IO Unit := pure ()
```
::::example "Infix `Functor` and `Applicative` Operators"
常见的函数式编程习惯是在某些上下文中通过 {name}`Functor.map` 和 {name}`Seq.seq` 应用纯函数来产生效果。
该函数使用 `<$>` 应用于其参数序列，并且参数由 `<*>` 分隔。

在此示例中，构造函数 {name}`User.mk` 通过 {lean}`main` 主体中的此习惯用法进行应用。
:::ioExample
```ioLean
def getName : IO String := do
  IO.println "What is your name?"
  return (← (← IO.getStdin).getLine).trimAsciiEnd.copy

partial def getFavoriteNat : IO Nat := do
  IO.println "What is your favorite natural number?"
  let line ← (← IO.getStdin).getLine
  if let some n := line.trimAscii.copy.toNat? then
    return n
  else
    IO.println "Let's try again."
    getFavoriteNat

structure User where
  name : String
  favoriteNat : Nat
deriving Repr

def main : IO Unit := do
  let user ← User.mk <$> getName <*> getFavoriteNat
  IO.println (repr user)
```
使用此输入运行时：
```stdin
A. Lean User
None
42
```
它产生这样的输出：
```stdout
What is your name?
What is your favorite natural number?
Let's try again.
What is your favorite natural number?
{ name := "A. Lean User", favoriteNat := 42 }
```
:::

::::
:::::

## 单子
%%%
tag := "zh-monads-syntax-h004"
%%%

Monad 主要通过 {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation] 使用。
然而，有时通过运算符描述一元计算会很方便。

```lean -show
section MOps
variable {m : Type u → Type v} [Monad m] {α β : Type u} {act : m α} {f : α → m β} {g : β → m γ}
```

:::syntax term (title := "Monad Operators")

{lean}`act >>= f` 是 {lean}`Bind.bind act f` 的语法。
```grammar
$_ >>= $_
```

类似地，反转运算符 {lean}`f =<< act` 是 {lean}`Bind.bind act f` 的语法。
```grammar
$_ =<< $_
```

Kleisli 组合运算符 {name}`Bind.kleisliRight` 和 {name}`Bind.kleisliLeft` 也有中缀运算符。
```grammar
$_ >=> $_
```
```grammar
$_ <=< $_
```

:::

```lean -show
example : act >>= f = Bind.bind act f := by rfl
example : f =<< act = Bind.bind act f := rfl
example : f >=> g = Bind.kleisliRight f g := by rfl
example : g <=< f = Bind.kleisliLeft g f := by rfl
end MOps
```


# `do`-符号
%%%
tag := "do-notation"
%%%

Monad 主要通过 {deftech}[{keywordOf Lean.Parser.Term.do}`do`-notation] 使用，这是一种用于命令式编程的嵌入式语言。
它提供了熟悉的语法来排序有效的操作、提前返回、局部可变变量、循环和异常处理。
所有这些功能都转换为 {lean}`Monad` 类型类的操作，其中一些功能需要添加指定容器迭代的类实例，例如 {lean}`ForIn`。
有关 {keywordOf Lean.Parser.Term.do}`do` 表示法设计的更多详细信息，请参阅 {citet doUnchained}[]。

{keywordOf Lean.Parser.Term.do}`do` 项由关键字 {keywordOf Lean.Parser.Term.do}`do` 后跟 {deftech}_{keywordOf Lean.Parser.Term.do}`do` elements_ 序列组成。

:::syntax term (title := "`do`-Notation")
```grammar
do $stmt*
```
{keywordOf Lean.Parser.Term.do}`do` 中的元素可以用分号分隔；否则，每个都应该在自己的行上，并且它们应该具有相同的缩进。
:::

```lean -show
section
variable {m : Type → Type} [Monad m] {α β γ: Type} {e1 : m Unit} {e : β} {es : m α}
```

## 顺序计算
%%%
tag := "zh-monads-syntax-h006"
%%%

{tech}[{keywordOf Lean.Parser.Term.do}`do`-element] 的一种形式是术语。

:::syntax Lean.Parser.Term.doSeqItem (title := "Terms in `do`-Notation")
```grammar
$e:term
```
:::


后跟元素序列的术语被翻译为 {name}`bind` 的使用；特别是，{lean}`do e1; es` 被转换为 {lean}`e1 >>= fun () => do es`。


:::table +header
*
  * {keywordOf Lean.Parser.Term.do}`do` 元件
  * 脱糖
*
  * ```leanTerm
    do
    e1
    es
    ```
  * ```leanTerm
    e1 >>= fun () => do es
    ```
:::

```lean -show -keep
def ex1a := do e1; es
def ex1b := e1 >>= fun () => do es
example : @ex1a = @ex1b := by rfl
```

该项的计算结果也可以被命名，以便在后续步骤中使用它。
这是使用 {keywordOf Lean.Parser.Term.doLet}`let` 完成的。

```lean -show
section
variable {e1 : m β} {e1? : m (Option β)} {fallback : m α} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}
```

:::syntax Lean.Parser.Term.doSeqItem (title := "Data Dependence in `do`-Notation")
{keywordOf Lean.Parser.Term.do}`do` 块中有两种形式的一元 {keywordOf Lean.Parser.Term.doLet}`let` 绑定。
第一个将标识符绑定到结果，并带有可选的类型注释：
```grammar
let $x:ident$[:$e]? ← $e:term
```
第二个将模式绑定到结果。
以 `|` 开头的后备子句指定模式与结果不匹配时的行为。
```grammar
let $x:term ← $e:term
  $[| $e]?
```
:::
此语法也被转换为 {name}`bind` 的使用。
{lean}`do let x ← e1; es` 转换为 {lean}`e1 >>= fun x => do es`，后备子句转换为默认模式匹配。
{keywordOf Lean.Parser.Term.doLet}`let` 也可以与标准定义语法 `:=` 一起使用，而不是与 `←` 一起使用。
这表明这是一个纯粹的定义，而不是一元的定义：
:::syntax Lean.Parser.Term.doSeqItem (title := "Local Definitions in `do`-Notation")
```grammar
let $v := $e:term
```
:::
{lean}`do let x := e; es` 转换为 {lean}`let x := e; do es`。

:::table +header
*
  * {keywordOf Lean.Parser.Term.do}`do` 元件
  * 脱糖
*
  * ```leanTerm
    do
    let x ← e1
    es
    ```
  * ```leanTerm
    e1 >>= fun x =>
      do es
    ```
*
  * ```leanTerm
    do
    let some x ← e1?
      | fallback
    es
    ```
  * ```leanTerm
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
    ```
*
  * ```leanTerm
    do
    let x := e
    es
    ```
  * ```leanTerm
    let x := e
    do es
    ```
:::

```lean -show -keep
-- Test desugarings
def ex1a := do
    let x ← e1
    es
def ex1b :=
    e1 >>= fun x =>
      do es
example : @ex1a = @ex1b := by rfl


def ex2a :=
    do
    let some x ← e1?
      | fallback
    es

def ex2b :=
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
example : @ex2a = @ex2b := by rfl

def ex3a :=
    do
    let x := e
    es
def ex3b :=
    let x := e
    do es
example : @ex3a = @ex3b := by rfl
```
在 {keywordOf Lean.Parser.Term.do}`do` 块内，`←` 可以用作前缀运算符。
应用它的表达式将替换为新变量，该变量在当前步骤之前使用 {name}`bind` 进行绑定。
这允许在原本可能期望纯值的位置使用单子效果，同时仍然保持_描述_有效计算和实际_执行_其效果之间的区别。
多次出现的 `←` 按从左到右、从内到外的顺序进行处理。

::::figure "Example Nested Action Desugarings"
:::table +header
*
  * 示例 {keywordOf Lean.Parser.Term.do}`do` 元素
  * 脱糖
*
  * ```leanTerm
    do
    f (← e1) (← e2)
    es
    ```
  * ```leanTerm
    do
    let x ← e1
    let y ← e2
    f x y
    es
    ```
*
  * ```leanTerm
    do
    let x := g (← h (← e1))
    es
    ```
  * ```leanTerm
    do
    let y ← e1
    let z ← h y
    let x := g z
    es
    ```
:::
::::

```lean -show -keep
-- Test desugarings
def ex1a := do
  f (← e1) (← e2)
  es
def ex1b := do
  let x ← e1
  let y ← e2
  f x y
  es
example : @ex1a = @ex1b := by rfl
def ex2a := do
  let x := g (← h (← e1))
  es
def ex2b := do
  let y ← e1
  let z ← h y
  let x := g z
  es
example : @ex2a = @ex2b := by rfl
```

除了方便地支持具有数据依赖性的顺序计算之外，{keywordOf Lean.Parser.Term.do}`do`-notation 还支持本地添加各种效果，包括提前返回、本地可变状态和提前终止的循环。
这些效果是通过整个 {keywordOf Lean.Parser.Term.do}`do` 块以类似于 {tech (key := "monad transformers")}[monad 转换器] 的方式进行转换来实现的，而不是通过局部脱糖来实现。

## 提前返回
%%%
tag := "early-return"
%%%

提前返回会立即终止给定值的计算。
该值是从最接近的包含 {keywordOf Lean.Parser.Term.do}`do` 的块返回的；但是，这可能不是最接近的 `do` 关键字。
{ref "closest-do-block"}[在其自己的部分]中描述了确定 {keywordOf Lean.Parser.Term.do}`do` 块范围的规则。

:::syntax Lean.Parser.Term.doSeqItem (title := "Early Return")
```grammar
return $e
```

```grammar
return
```
:::

并非所有 monad 都包含提前返回。
因此，当{keywordOf Lean.Parser.Term.do}`do`块包含{keywordOf Lean.Parser.Term.doReturn}`return`时，需要重写代码来模拟效果。
使用早期返回来计算单子 {lean}`m` 中类型 {lean}`α` 的值的程序可以被视为单子 {lean}`ExceptT α m α` 中的程序：早期返回值采用异常路径，而普通返回则不采用异常路径。
然后，外部处理程序可以从任一代码路径返回值。
在内部，{keywordOf Lean.Parser.Term.do}`do`精化器执行的转换与此非常相似。

就其本身而言，{keywordOf Lean.Parser.Term.doReturn}`return` 是 {keywordOf Lean.Parser.Term.doReturn}`return`​` `​{lean}`()` 的缩写。

## 局部可变状态
%%%
tag := "let-mut"
%%%

本地可变状态是无法转义定义它的 {keywordOf Lean.Parser.Term.do}`do` 块的可变状态。
{keywordOf Lean.Parser.Term.doLet}`let mut` 绑定器引入了本地可变绑定。
:::syntax Lean.Parser.Term.doSeqItem (title := "Local Mutability")
可变绑定可以通过纯计算或一元计算来初始化：
```grammar
let mut $x := $e
```
```grammar
let mut $x ← $e
```

类似地，它们可以用纯值或 monad 计算的结果进行变异：
```grammar (of := Lean.Parser.Term.doReassign)
$x:ident$[: $_]?  := $e:term
```
```grammar (of := Lean.Parser.Term.doReassign)
$x:term$[: $_]? := $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:ident$[: $_]? ← $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:term ← $e:term
  $[| $e]?
```
:::

这些本地可变的绑定不如 {tech}[state monad] 强大，因为它们在词法范围之外是不可变的；这也让他们更容易推理。
当 {keywordOf Lean.Parser.Term.do}`do` 块包含可变绑定时，{keywordOf Lean.Parser.Term.do}`do`精化器会以类似于 {lean}`StateT` 的方式转换表达式，构造一个新的 monad 并使用正确的值对其进行初始化。

## 控制结构
%%%
tag := "do-control-structures"
%%%

有一些 {keywordOf Lean.Parser.Term.do}`do` 元素对应于大多数 Lean 的术语级控制结构。
当它们作为 {keywordOf Lean.Parser.Term.do}`do` 块中的步骤出现时，它们被解释为 {keywordOf Lean.Parser.Term.do}`do` 元素而不是术语。
控制结构的每个分支都是 {keywordOf Lean.Parser.Term.do}`do` 元素的序列，而不是术语，其中一些分支在语法上比相应的术语更灵活。

:::syntax Lean.Parser.Term.doSeqItem (title := "Conditionals")
在 {keywordOf Lean.Parser.Term.do}`do` 块中，{keywordOf Lean.Parser.Term.doIf}`if` 语句可以省略其 {keywordOf Lean.Parser.Term.doIf}`else` 分支。
省略 {keywordOf Lean.Parser.Term.doIf}`else` 分支相当于使用 {name}`pure`{lean}` ()` 作为分支的内容。
```grammar
if $[$h :]? $e then
  $e*
$[else
  $_*]?
```
:::

从语法上讲，{keywordOf Lean.Parser.Term.doIf}`then` 分支不能省略。
对于这些情况，{keywordOf Lean.Parser.Term.doUnless}`unless` 仅在条件为 false 时执行其主体。
{keywordOf Lean.Parser.Term.doUnless}`unless` 中的 {keywordOf Lean.Parser.Term.do}`do` 是其语法的一部分，不会产生嵌套的 {keywordOf Lean.Parser.Term.do}`do` 块。
:::syntax Lean.Parser.Term.doSeqItem (title := "Reverse Conditionals")
```grammar
unless $e do
  $e*
```
:::


当 {keywordOf Lean.Parser.Term.doMatch}`match` 用于 {keywordOf Lean.Parser.Term.do}`do` 块时，每个分支都被视为同一块的一部分。
否则，它相当于 {keywordOf Lean.Parser.Term.match}`match` 项。
:::syntax Lean.Parser.Term.doSeqItem (title := "Pattern Matching")
```grammar
match $[$[$h :]? $e],* with
  $[| $t,* => $e*]*
```
:::


## 迭代
%%%
tag := "monad-iteration-syntax"
%%%

在 {keywordOf Lean.Parser.Term.do}`do` 块内，{keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` 循环允许对数据结构进行迭代。
循环体是包含 {keywordOf Lean.Parser.Term.do}`do` 块的一部分，因此可以使用局部效果，例如提前返回和可变变量。

:::syntax Lean.Parser.Term.doSeqItem (title := "Iteration over Collections")
```grammar
for $[$[$h :]? $x in $y],* do
  $e*
```
:::

{keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` 循环至少需要一个子句来指定要执行的迭代，该子句由一个可选的成员资格证明名称后跟一个冒号 (`:`)、一个要绑定的模式、关键字 {keywordOf Lean.Parser.Term.doFor}`in` 和一个集合术语组成。
该模式可能只是 {tech}[identifier]，必须与集合中的任何元素匹配；此位置的模式不能用作隐式过滤器。
可以通过用逗号分隔来提供进一步的子句。
每个集合都会同时迭代，当任何一个集合用完元素时，迭代就会停止。

:::example "Iteration Over Multiple Collections"
迭代多个集合时，当任何集合用完元素时，迭代就会停止。
```lean (name := earlyStop)
#eval Id.run do
  let mut v := #[]
  for x in [0:43], y in ['a', 'b'] do
    v := v.push (x, y)
  return v
```
```leanOutput earlyStop
#[(0, 'a'), (1, 'b')]
```
:::

::::keepEnv
:::example "Iteration over Array Indices with {keywordOf Lean.Parser.Term.doFor}`for`"

当使用 {keywordOf Lean.Parser.Term.doFor}`for` 迭代数组的有效索引时，命名成员资格证明允许策略成功搜索数组索引在界限内的证明。
```lean -keep
def satisfyingIndices
    (p : α → Prop) [DecidablePred p]
    (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```

省略假设名称会导致数组查找失败，因为在上下文中无法证明迭代变量在指定范围内。

```lean -keep -show
-- test it
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
m : Type → Type
inst✝¹ : Monad m
α β γ : Type
e1✝ : m Unit
e : β
es : m α
e1 : m β
e1? : m (Option β)
fallback : m α
e2 : m γ
f : β → γ → m Unit
g : γ → α
h : β → m γ
p : α → Prop
inst✝ : DecidablePred p
xs : Array α
out✝ : Array Nat := #[]
i : Nat
r✝ : Array Nat
out : Array Nat := r✝
⊢ i < xs.size
-/
#check_msgs in
def satisfyingIndices (p : α → Prop) [DecidablePred p] (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```
:::
::::

:::::keepEnv
::::leanSection

`for` 循环的迭代被转化为 `ForIn.forIn` 的使用，它是 `ForM.forM` 的类似物，增加了对局部突变和提前终止的支持。
{name}`ForIn.forIn` 接收本地可变状态的初始值和一元操作作为参数，以及迭代的集合。
传递给 {name}`ForIn.forIn` 的单子操作将当前状态作为参数，并在单子 {lean}`m` 中执行操作后，返回 {name}`ForInStep.yield` 以指示迭代应使用一组更新的本地可变值继续，或者返回 {name}`ForInStep.done` 以指示 {keywordOf Lean.Parser.Term.doBreak}`break` 或 {keywordOf Lean.Parser.Term.doReturn}`return`被执行。
迭代完成后，{name}`ForIn.forIn` 返回局部可变值的最终值。

循环的具体脱糖取决于循环体中如何使用状态和提前终止。
以下是一些示例：
```lean -show
axiom «<B>» : Type u
axiom «<b>» : β
variable [Monad m] (xs : Coll) [ForIn m Coll α] [instMem : Membership α Coll] [ForIn' m Coll α instMem]
variable (f : α → β → m β) (f' : (x : α) → x ∈ xs → β → m β)

macro "…" : term => `((«<b>» : β))
```

:::table +header
*
  * {keywordOf Lean.Parser.Term.do}`do` 元件
  * 脱糖
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.yield b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
      break
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.done b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.yield b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
      break
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.done b
    es
    ```
:::
::::
:::::


当条件保持为真时，{keywordOf Lean.doElemWhile_Do_}`while` 循环的主体会重复。
可以在未标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数中使用它们编写无限循环。
这是因为 {keywordOf Lean.Parser.Command.declaration}`partial` 修饰符仅适用于由正在定义的函数引起的非终止或无限回归，而不是由它调用的函数引起的。
{keywordOf Lean.doElemWhile_Do_}`while` 循环的翻译依赖于单独的帮助程序。

:::syntax Lean.Parser.Term.doSeqItem (title := "Conditional Loops")
```grammar
while $e do
  $e*
```
```grammar
while $h : $e do
  $e*
```
:::

{keywordOf Lean.doElemRepeat__Until_}`repeat`-{keywordOf Lean.doElemRepeat__Until_}`until` 循环体始终至少执行一次。
每次迭代后，都会检查条件，并在条件为“假”时重复循环。
当条件成立时，迭代停止。

:::syntax Lean.Parser.Term.doSeqItem (title := "Post-Tested Loops")
```grammar
repeat
  $e*
until $_
```
:::


重复 {keywordOf Lean.doElemRepeat_}`repeat` 循环体，直到执行 {keywordOf Lean.Parser.Term.doBreak}`break` 语句为止。
就像 {keywordOf Lean.doElemWhile_Do_}`while` 循环一样，这些循环可以在未标记为 {keywordOf Lean.Parser.Command.declaration}`partial` 的函数中使用。

:::syntax Lean.Parser.Term.doSeqItem (title := "Unconditional Loops")
```grammar
repeat
  $e*
```
:::

{keywordOf Lean.Parser.Term.doContinue}`continue` 语句跳过最接近的封闭 {keywordOf Lean.doElemRepeat_}`repeat`、{keywordOf Lean.doElemWhile_Do_}`while` 或 {keywordOf Lean.Parser.Term.doFor}`for` 循环体的其余部分，继续进行下一次迭代。
{keywordOf Lean.Parser.Term.doBreak}`break` 语句终止最接近的封闭 {keywordOf Lean.doElemRepeat_}`repeat`、{keywordOf Lean.doElemWhile_Do_}`while` 或 {keywordOf Lean.Parser.Term.doFor}`for` 循环，从而停止迭代。

:::syntax Lean.Parser.Term.doSeqItem (title := "Loop Control Statements")
```grammar
continue
```
```grammar
break
```
:::

除了 {keywordOf Lean.Parser.Term.doBreak}`break` 之外，循环始终可以通过当前 monad 中的效果来终止。
从循环中抛出异常会终止循环。

:::example "Terminating Loops in the {lean}`Option` Monad"
{name}`Alternative` 类中的 {name}`failure` 方法可用于终止 {name}`Option` monad 中原本无限的循环。

```lean (name := natBreak)
#eval show Option Nat from do
  let mut i := 0
  repeat
    if i > 1000 then failure
    else i := 2 * (i + 1)
  return i
```
```leanOutput natBreak
none
```
:::

## 识别 `do` 块
%%%
tag := "closest-do-block"
%%%

{keywordOf Lean.Parser.Term.do}`do` 表示法的许多功能都会对 {deftech (key := "current do block")}[当前 {keywordOf Lean.Parser.Term.do}`do` 块]产生影响。
特别是，提前返回会中止当前块，导致其计算返回值，并且可变绑定只能在定义它们的块中进行更改。
理解这些特征需要精确定义“同一”块的含义。

根据经验，这可以使用 Lean 语言服务器进行检查。
当光标位于 {keywordOf Lean.Parser.Term.doReturn}`return` 语句上时，相应的 {keywordOf Lean.Parser.Term.do}`do` 关键字会突出显示。
尝试改变同一 {keywordOf Lean.Parser.Term.do}`do` 块之外的可变绑定会导致错误消息。

:::figure "Highlighting {keywordOf Lean.Parser.Term.do}`do`"

![从 return 中突出显示 do](/static/screenshots/do-return-hl-1.png)

![突出显示带有错误的返回 do](/static/screenshots/do-return-hl-2.png)
:::

规则如下：
 * 立即嵌套在开始块的 {keywordOf Lean.Parser.Term.do}`do` 关键字下的每个元素都属于该块。
 * 直接嵌套在 {keywordOf Lean.Parser.Term.do}`do` 关键字下的每个元素（包含 {keywordOf Lean.Parser.Term.do}`do` 块中的元素）都属于外部块。
 * {keywordOf Lean.Parser.Term.doIf}`if`、{keywordOf Lean.Parser.Term.doMatch}`match` 或 {keywordOf Lean.Parser.Term.doUnless}`unless` 元素的分支中的元素与包含它们的控制结构属于同一 {keywordOf Lean.Parser.Term.do}`do` 块。作为 {keywordOf Lean.Parser.Term.doUnless}`unless` 语法一部分的 {keywordOf Lean.Parser.Term.doUnless}`do` 关键字不会引入新的 {keywordOf Lean.Parser.Term.do}`do` 块。
 * {keywordOf Lean.doElemRepeat_}`repeat`、{keywordOf Lean.doElemWhile_Do_}`while` 和 {keywordOf Lean.Parser.Term.doFor}`for` 主体中的元素与包含它们的循环属于同一 {keywordOf Lean.Parser.Term.do}`do` 块。作为 {keywordOf Lean.doElemWhile_Do_}`while` 和 {keywordOf Lean.Parser.Term.doFor}`for` 语法一部分的 {keywordOf Lean.Parser.Term.doFor}`do` 关键字不会引入新的 {keywordOf Lean.Parser.Term.do}`do` 块。

```lean -show
-- Test nested `do` rules

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return

/-- error: must be last element in a `do` sequence -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return
  set 7
  return

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  if true then
    set 6
    do return
  set 7
  return
```

::::keepEnv
:::example "Nested `do` and Branches"
以下示例输出 {lean}`6` 而不是 {lean}`7`：
```lean (name := nestedDo)
def test : StateM Nat Unit := do
  set 5
  if true then
    set 6
    do return
  set 7
  return

#eval test.run 0
```
```leanOutput nestedDo
((), 6)
```

这是因为 {keywordOf Lean.Parser.Term.doIf}`if` 下的 {keywordOf Lean.Parser.Term.doReturn}`return` 语句与其直接父级属于同一 {keywordOf Lean.Parser.Term.do}`do`，而该父级本身又与 {keywordOf Lean.Parser.Term.doIf}`if` 属于同一 {keywordOf Lean.Parser.Term.do}`do`。
如果作为其他 {keywordOf Lean.Parser.Term.do}`do` 块中的元素出现的 {keywordOf Lean.Parser.Term.do}`do` 块改为创建新块，则该示例将输出 {lean}`7`。
:::
::::

```lean -show
end
```

```lean -show
-- tests for this section
set_option pp.all true

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α e1 fun (x : PUnit.{1}) => es : m α
-/
#check_msgs in
#check do e1; es

section
variable {e1 : m β}
/-- info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (x : β) => es : m α -/
#check_msgs in
#check do let x ← e1; es
end

/--
info: let x : β := e;
es : m α
-/
#check_msgs in
#check do let x := e; es

variable {e1 : m β} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α e2 fun (__do_lift_1 : γ) =>
    @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α (f __do_lift __do_lift_1) fun (x : PUnit.{1}) => es : m α
-/
#check_msgs in
#check do f (← e1) (← e2); es

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α (h __do_lift) fun (__do_lift : γ) =>
    let x : α := g __do_lift;
    es : m α
-/
#check_msgs in
#check do let x := g (← h (← e1)); es

end


```

## Type 用于迭代的类
%%%
tag := "zh-monads-syntax-h012"
%%%

要与没有成员资格证明的 {keywordOf Lean.Parser.Term.doFor}`for` 循环一起使用，集合必须实现 {name}`ForIn` 类型类。
实现 {lean}`ForIn'` 还允许使用具有成员资格证明的 {keywordOf Lean.Parser.Term.doFor}`for` 循环。

{docstring ForIn}

{docstring ForIn'}

{docstring ForInStep}

{docstring ForInStep.value}

{docstring ForM}

{docstring ForM.forIn}
