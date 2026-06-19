/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import ManualZh.Monads.Zoo.State
import ManualZh.Monads.Zoo.Reader
import ManualZh.Monads.Zoo.Except
import ManualZh.Monads.Zoo.Combined
import ManualZh.Monads.Zoo.Id
import ManualZh.Monads.Zoo.Option

/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
-- set_option trace.SubVerso.Highlighting.Code true

#doc (Manual) "单子的种类" =>
%%%
tag := "monad-varieties"
%%%

{lean}`IO` monad 有很多很多的效果，用于编写需要与世界交互的程序。
它在 {ref "io"}[它自己的部分]中进行了描述。
使用 {lean}`IO` 的程序本质上是黑匣子：它们通常不太适合验证。

许多算法最容易用更少的效果来表达。
这些效果通常可以被模拟；例如，可以通过传递包含程序值和状态的元组来模拟可变状态。
这些模拟效果更容易正式推理，因为它们是使用普通代码而不是新语言原语定义的。

标准库提供了处理常用效果的抽象。
许多常用效果分为以下几类：

: {deftech}[状态单子] 具有可变状态

  可以访问可能被计算的其他部分修改的某些数据的计算使用_可变状态_。
  状态可以通过多种方式实现，在 {ref "state-monads"}[状态 monads] 部分中进行了描述，并在 {name}`MonadState` 类型类中捕获。

: {deftech}[Reader monads]​​ 是参数化计算

  大多数编程语言中都存在可以读取上下文提供的某些参数值的计算，但是许多将状态和异常作为第一类功能的语言没有用于定义新参数化计算的内置设施。
  通常，这些计算在调用时会提供一个参数值，有时它们可以在本地覆盖它。
  参数值具有_动态范围_：调用堆栈中最近提供的值是使用的值。
  可以通过一系列函数调用传递一个不变的值来模拟它们；但是，这种技术可能会使代码更难阅读，并带来可能将值错误地传递给进一步调用的风险。
  它们还可以使用可变状态进行模拟，并围绕状态的修改进行仔细的训练。
  维护参数的 Monad，可能允许它在调用堆栈的一部分中被覆盖，称为 _reader monads_。
  读取器单子在 {lean}`MonadReader` 类型类中捕获。
  此外，允许本地覆盖参数值的读取器单子在 {lean}`MonadWithReader` 类型类中捕获。

: {deftech}[Exception monads]​​ 有异常

  可能因异常值而提前终止的计算使用 _exceptions_。
  它们通常使用 sum 类型进行建模，该 sum 类型具有用于普通终止的构造函数和用于提前终止错误的构造函数。
  异常单子在 {ref "exception-monads"}[异常单子] 部分中进行了描述，并在 {name}`MonadExcept` 类型类中捕获。


# Monad Type 类

使用 {lean}`MonadState` 和 {lean}`MonadExcept` 等类型类允许客户端代码相对于 monad 是多态的。
与自动提升一起，这使得程序可以在许多不同的 monad 中重用，并使它们更适合重构。

重要的是要意识到单子中的效果可能不仅仅以一种方式相互作用。
例如，具有状态和异常的 monad 在抛出异常时可能会也可能不会回滚状态更改。
如果这对于函数的正确性很重要，那么它应该使用更具体的签名。

::::keepEnv
:::example "Effect Ordering"
函数 {name}`sumNonFives` 使用状态单子添加列表的内容，如果遇到 {lean}`5` 则提前终止。
```lean
def sumNonFives {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Unit := do
  for x in xs do
    if x == 5 then
      throw "Five was encountered"
    else
      modify (· + x)
```

在一个 monad 中运行它会返回遇到 {lean}`5` 时的状态：
```lean (name := exSt)
#eval
  sumNonFives (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run 0
```
```leanOutput exSt
(Except.error "Five was encountered", 10)
```

在另一个例子中，状态被丢弃：
```lean (name := stEx)
#eval
  sumNonFives (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run 0
```
```leanOutput stEx
Except.error "Five was encountered"
```

在第二种情况下，异常处理程序会将状态回滚到 {keywordOf Lean.Parser.Term.termTry}`try` 开头处的值。
因此以下函数是不正确的：
```lean
/-- Computes the sum of the non-5 prefix of a list. -/
def sumUntilFive {m}
    [Monad m] [MonadState Nat m] [MonadExcept String m]
    (xs : List Nat) :
    m Nat := do
  MonadState.set 0
  try
    sumNonFives xs
  catch _ =>
    pure ()
  get
```

在一个 monad 中，答案是正确的：
```lean (name := exSt2)
#eval
  sumUntilFive (m := ExceptT String (StateM Nat))
    [1, 2, 3, 4, 5, 6] |>.run |>.run' 0
```
```leanOutput exSt2
Except.ok 10
```

另一方面，它不是：
```lean (name := stEx2)
#eval
  sumUntilFive (m := StateT Nat (Except String))
    [1, 2, 3, 4, 5, 6] |>.run' 0
```
```leanOutput stEx2
Except.ok 0
```
:::
::::

单个 monad 可以支持相同效果的多个版本。
例如，可能存在可变的 {lean}`Nat` 和可变的 {lean}`String` 或两个单独的读取器参数。
只要它们有不同的类型，就应该可以方便地访问两者。
在典型使用中，类型类中重载的一些一元操作具有可用于 {tech (key := "synthesis")}[实例综合]的类型信息，而其他操作则没有。
例如，传递给 {name MonadState.set}`set` 的参数确定要使用的状态类型，而 {name MonadState.get}`get` 不采用此类参数。
当有多个状态可用时，{name MonadState.set}`set` 应用程序中存在的类型信息可用于选择正确的实例，这表明可变状态的类型应该是输入参数或 {tech}[半输出参数]，以便可用于选择实例。
另一方面，{name MonadState.get}`get` 的使用中缺乏类型信息，这表明可变状态的类型应该是 {lean}`MonadState` 中的 {tech}[输出参数]，因此类型类综合从 monad 本身确定状态的类型。

这种二分法可以通过许多效果类型类的两个版本来解决。
带有半输出参数的版本具有后缀`-Of`，其操作根据需要显式采用类型。
示例包括 {name}`MonadStateOf`、{name}`MonadReaderOf` 和 {name}`MonadExceptOf`。
具有显式类型参数的操作的名称以 `-The` 结尾，例如 {name}`getThe`、{name}`readThe` 和 {name}`tryCatchThe`。
带有输出参数的版本名称未修饰。
标准库根据典型用例中具有良好推理行为的内容，导出 `-Of` 和每个类型类的未修饰版本的操作组合。

:::table +header
  *
   * 操作
   * 来自班级
   * 注释
  *
   * {name}`get`
   * {name}`MonadState`
   * 输出参数改进了类型推断
  *
   * {name}`set`
   * {name}`MonadStateOf`
   * 半输出参数使用来自 {name}`set` 参数的类型信息
  *
   * {name}`modify`
   * {name}`MonadState`
   * 需要输出参数来允许没有注释的函数
  *
   * {name}`modifyGet`
   * {name}`MonadState`
   * 需要输出参数来允许没有注释的函数
  *
   * {name}`read`
   * {name}`MonadReader`
   * 由于缺少参数的类型信息，因此需要输出参数
  *
   * {name}`readThe`
   * {name}`MonadReaderOf`
   * 半输出参数使用提供的类型来指导合成
  *
   * {name}`withReader`
   * {name}`MonadWithReader`
   * 输出参数避免了函数上类型注释的需要
  *
   * {name}`withTheReader`
   * {name}`MonadWithReaderOf`
   * 半输出参数使用提供的类型来指导合成
  *
   * {name}`throw`
   * {name}`MonadExcept`
   * 输出参数允许对异常使用构造函数点表示法
  *
   * {name}`throwThe`
   * {name}`MonadExceptOf`
   * 半输出参数使用提供的类型来指导合成
  *
   * {name}`tryCatch`
   * {name}`MonadExcept`
   * 输出参数允许对异常使用构造函数点表示法
  *
   * {name}`tryCatchThe`
   * {name}`MonadExceptOf`
   * 半输出参数使用提供的类型来指导合成
:::

```lean -show
example : @get = @MonadState.get := by rfl
example : @set = @MonadStateOf.set := by rfl
example {inst} (f : σ → σ) : @modify σ m inst f = @MonadState.modifyGet σ m inst PUnit fun (s : σ) => (PUnit.unit, f s) := by rfl
example : @modifyGet = @MonadState.modifyGet := by rfl
example : @read = @MonadReader.read := by rfl
example : @readThe = @MonadReaderOf.read := by rfl
example : @withReader = @MonadWithReader.withReader := by rfl
example : @withTheReader = @MonadWithReaderOf.withReader := by rfl
example : @throw = @MonadExcept.throw := by rfl
example : @throwThe = @MonadExceptOf.throw := by rfl
example : @tryCatch = @MonadExcept.tryCatch := by rfl
example : @tryCatchThe = @MonadExceptOf.tryCatch := by rfl
```

:::example "State Types"
状态单子 {name}`M` 有两个单独的状态：{lean}`Nat` 和 {lean}`String`。
```lean
abbrev M := StateT Nat (StateM String)
```

由于 {name}`get` 是 {name}`MonadState.get` 的别名，因此状态类型是输出参数。
这意味着 Lean 自动选择一种状态类型，在本例中是来自最外层 monad 转换器的状态类型：
```lean (name := getM)
#check (get : M _)
```
```leanOutput getM
get : M Nat
```

只能使用最外层，因为状态的类型是输出参数。
```lean (name := getMStr) +error
#check (get : M String)
```
```leanOutput getMStr
failed to synthesize instance of type class
  MonadState String M

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```

使用 {name}`MonadStateOf` 中的 {name}`getThe` 显式提供状态类型允许读取两种状态。
```lean (name := getTheM)
#check ((getThe String, getThe Nat) : M String × M Nat)
```
```leanOutput getTheM
(getThe String, getThe Nat) : M String × M Nat
```

设置状态适用于任一类型，因为状态类型是 {name}`MonadStateOf` 上的 {tech}[半输出参数]。
```lean (name := setNat)
#check (set 4 : M Unit)
```
```leanOutput setNat
set 4 : M PUnit
```

```lean (name := setStr)
#check (set "Four" : M Unit)
```
```leanOutput setStr
set "Four" : M PUnit
```

:::


# 莫纳德变形金刚
%%%
tag := "monad-transformers"
%%%

{deftech}_monad Transformer_ 是一个函数，当提供一个 monad 时，它会返回一个新的 monad。
通常，这个新的 monad 具有原始 monad 的所有效果以及一些附加效果。

```lean -show
variable {α : Type u} (T : (Type u → Type v) → Type u → Type w) (m : Type u → Type v)

```
一个 Monad 转换器由以下部分组成：
 * 从现有 monad 构造新 monad 类型的函数 {lean}`T`
 * `run` 函数，将 {lean}`T m α` 改编为 {lean}`m` 的某些变体，通常需要附加参数并在 {lean}`m` 下返回更具体的类型
 * {lean}`[Monad m] → Monad (T m)` 的实例，允许将转换后的 monad 用作 monad
 * {lean}`MonadLift` 的实例，允许在转换后的 monad 中使用原始 monad 的代码
 * 如果可能，{lean}`MonadControl m (T m)` 的实例允许在原始 monad 中使用转换后的 monad 中的操作

通常，monad 转换器还提供一个或多个类型类的实例来描述它引入的效果。
转换器的 {name}`Monad` 和 {name}`MonadLift` 实例使得在转换后的 monad 中编写代码变得实用，而类型类实例允许将转换后的 monad 与多态函数一起使用。

::::keepEnv
```lean -show
universe u v
variable {m : Type u → Type v} {α : Type u}
```
:::example "The Identity Monad Transformer "
身份 monad 转换器既不会添加也不会删除转换后的 monad 的功能。
它的定义是恒等函数，经过适当专门化：
```lean
def IdT (m : Type u → Type v) : Type u → Type v := m
```
同样，{name IdT.run}`run` 函数不需要额外的参数，只返回 {lean}`m α`：
```lean
def IdT.run (act : IdT m α) : m α := act
```

monad 实例依赖于转换后的 monad 的 monad 实例，通过 {tech}[type ascriptions] 选择它：
```lean
instance [Monad m] : Monad (IdT m) where
  pure x := (pure x : m _)
  bind x f := (x >>= f : m _)
```

由于 {lean}`IdT m` 在定义上等于 {lean}`m`，因此 {lean}`MonadLift m (IdT m)` 实例不需要修改正在解除的操作：
```lean
instance : MonadLift m (IdT m) where
  monadLift x := x
```

{lean}`MonadControl` 实例同样简单。
```lean
instance [Monad m] : MonadControl m (IdT m) where
  stM α := α
  liftWith f := f (fun x => Id.run <| pure x)
  restoreM v := v
```

:::
::::

Lean 标准库提供许多不同 monad 的转换器版本，包括 {name}`ReaderT`、{name}`ExceptT` 和 {name}`StateT`，以及使用其他表示形式的变体，例如 {name}`StateCpsT`、{name StateRefT'}`StateRefT` 和 {name}`ExceptCpsT`。
此外，{name}`EStateM` monad 相当于 {name}`ExceptT` 和 {name}`StateT` 的组合，但它可以使用更专门的表示来提高性能。

{include 0 ManualZh.Monads.Zoo.Id}

{include 0 ManualZh.Monads.Zoo.State}

{include 0 ManualZh.Monads.Zoo.Reader}

{include 0 ManualZh.Monads.Zoo.Option}

{include 0 ManualZh.Monads.Zoo.Except}

{include 0 ManualZh.Monads.Zoo.Combined}
