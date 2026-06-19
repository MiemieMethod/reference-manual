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

#doc (Manual) "优先级" =>
%%%
tag := "precedence"
%%%

Lean 的中缀运算符、符号和其他语法扩展使用显式 {tech}[优先级] 注释。
虽然 Lean 中的优先级从技术上讲可以是任何自然数，但按照惯例，它们的范围是从 {evalPrec}`min` 到 {evalPrec}`max`，分别表示为 `min` 和 `max`。{TODO}[修复 keywordsOf 运算符并在此处使用它]
函数应用程序具有最高优先级。

:::syntax prec -open (title := "Parser Precedences")
大多数运算符优先级由显式数字组成。
指定的优先级表示范围的外边缘，接近最小值或最大值，通常由更多涉及的语法扩展使用。
```grammar
$n:num
```

优先级也可以表示为优先级的和或差；这些通常用于分配与指定优先级之一相关的优先级。
```grammar
$p + $p
```
```grammar
$p - $p
```
```grammar
($p)
```

最大优先级用于解析出现在函数位置的术语。
运算符通常不应使用此级别，因为它可能会干扰用户对函数应用程序比任何其他运算符绑定更紧密的期望，但它在涉及更多的语法扩展中很有用，可以指示其他构造如何与函数应用程序交互。
```grammar
max
```

参数优先级比最大优先级低一。
此级别对于定义应被视为函数参数的语法非常有用，例如 {keywordOf Lean.Parser.Term.fun}`fun` 或 {keywordOf Lean.Parser.Term.do}`do`。
```grammar
arg
```

前导优先级低于参数优先级，并且应用于不应作为函数参数出现的自定义语法，例如 {keywordOf Lean.Parser.Term.let}`let`。
```grammar
lead
```

最小优先级可用于确保某个运算符的绑定不如所有其他运算符紧密。
```grammar
min
```
:::
