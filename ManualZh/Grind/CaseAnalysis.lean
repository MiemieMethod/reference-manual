/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "案例分析" =>
%%%
tag := "grind-split"
%%%

除了同余闭包和约束传播之外，{tactic}`grind` 还执行案例分析。
在案例分析期间，{tactic}`grind` 以类似于 {tactic}`cases` 和 {tactic}`split`策略的方式考虑构建项的每种可能方式，或特定项的每个可能值。
此案例分析并不详尽：{tactic}`grind` 仅递归地将案例分割到配置的深度限制，并且配置选项和注释控制哪些术语是分割的候选者。


# 选择启发法

{tactic}`grind` 通过组合三个信号源来决定分割哪个子项：

: 结构标志

  这些配置标志确定 {tactic}`grind` 是否执行某些情况拆分：

  : `splitIte`（默认{lean}`true`）

    每个 {keywordOf Lean.Parser.Term.ite}`if` 项都应该被拆分，就像被 {tactic}`split`策略一样。

  : `splitMatch`（默认{lean}`true`）

    每个 {keywordOf Lean.Parser.Term.match}`match` 项都应该被拆分，就像被 {tactic}`split`策略一样。

  :  `splitImp`（默认{lean}`false`）

    :::leanSection
    ```lean -show
    variable {A : Prop} {B : Sort u}
    ```
    {lean}`A → B` 形式的假设（其先行词 {lean}`A` 是“命题”）通过考虑 {lean}`A` 的所有可能性来拆分。
    算术先行词是特殊情况：如果 {lean}`A` 是算术文字（即由 `≤`、`=`、`¬`、{lean}`Dvd` 等运算符形成的命题），则 {tactic}`grind` 将在以下情况下拆分 _even： `splitImp := false`_ 因此整数求解器可以传播事实。
    :::

: 全球限制

  {tactic}`grind` 选项 `splits := n` 限制搜索树的深度。
  一旦分支执行 `n` 拆分，{tactic}`grind` 就会停止在该分支中进一步拆分；如果无法关闭分支，则报告已达到拆分阈值。

: 手动注释

  归纳谓词或结构可以用 {attr}`grind cases` 属性进行标记。
  {tactic}`grind` 将该谓词的每个实例视为拆分的候选者。


:::syntax attr (title := "Case Analysis")
```grammar
grind cases
```
{includeDocstring Lean.Parser.Attr.grindCases}
:::

:::syntax attr (title := "Eager Case Analysis")
```grammar
grind cases eager
```
{includeDocstring Lean.Parser.Attr.grindCasesEager}
:::


:::example "Splitting Conditional Expressions"
在此示例中，{tactic}`grind` 通过考虑条件的两种情况来证明该定理：
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind
```

禁用 `splitIte` 会导致证明失败：
```lean +error (name := noSplitIte)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind -splitIte
```
特别是，在发现条件表达式等于 {lean}`0` 后就无法进行：
```leanOutput noSplitIte (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] others
      [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
```

禁止所有大小写拆分会导致证明因同样的原因而失败：
```lean +error (name := noSplitsAtAll)
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 0)
```
```leanOutput noSplitsAtAll (expandTrace := eqc)
`grind` failed
case grind
c : Bool
x y : Nat
h : (if c = true then x else y) = 0
left : ¬x = 0
right : ¬y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] False propositions
    [prop] x = 0
    [prop] y = 0
  [eqc] Equivalence classes
    [eqc] others
      [eqc] {0, if c = true then x else y}
  [cutsat] Assignment satisfying linear constraints
  [limits] Thresholds reached
```

仅允许一次拆分就足够了：
```lean
example (c : Bool) (x y : Nat)
    (h : (if c then x else y) = 0) :
    x = 0 ∨ y = 0 := by
  grind (splits := 1)
```
:::

:::example "Splitting Pattern Matching"
在此示例中，禁用模式匹配的大小写分割会导致 {tactic}`grind` 失败：
```lean +error (name := noSplitMatch)
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind -splitMatch
```
```leanOutput noSplitMatch (expandTrace := eqc)
`grind` failed
case grind
y x : Nat
h : y =
  match x with
  | 0 => 1
  | x => 2
h_1 : y = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] (x = 0 → False) →
          (match x with
            | 0 => 1
            | x => 2) =
            2
  [eqc] Equivalence classes
    [eqc] {y, 0}
      [eqc] {match x with
          | 0 => 1
          | x => 2}
    [eqc] {x = 0 → False, (fun x_0 => x_0 = 0 → False) x, x = 0 → False}
  [ematch] E-matching patterns
  [cutsat] Assignment satisfying linear constraints

[grind] Diagnostics
```
启用该选项会使证明成功：
```lean
example (h : y = match x with | 0 => 1 | _ => 2) :
    y > 0 := by
  grind
```
:::

:::example "Splitting Predicates"
{lean}`Not30` 是一种有点冗长的方式来声明数字不是 {lean}`30`：
```lean
inductive Not30 : Nat → Prop where
  | gt : x > 30 → Not30 x
  | lt : x < 30 → Not30 x
```

默认情况下，{tactic}`grind` 无法表明 {lean}`Not30` 暗示数字实际上不是 {lean}`30`：
```lean +error (name := not30fail)
example : Not30 n → n ≠ 30 := by grind
```
这是因为 {tactic}`grind` 没有考虑 {lean}`Not30` 的两种情况
```leanOutput not30fail (expandTrace := eqc)
`grind` failed
case grind
n : Nat
h : Not30 n
h_1 : n = 30
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
  [eqc] True propositions
    [prop] Not30 n
  [eqc] Equivalence classes
    [eqc] {n, 30}
  [cutsat] Assignment satisfying linear constraints
```

将 {attr}`grind cases` 属性添加到 {lean}`Not30` 可以使证明成功：
```lean
attribute [grind cases] Not30

example : Not30 n → n ≠ 30 := by grind
```

同样，{lean}`Even` 上的 {attr}`grind cases` 属性允许 {tactic}`grind` 执行大小写拆分：
```lean (name := blah)
@[grind cases]
inductive Even : Nat → Prop
  | zero : Even 0
  | step : Even n → Even (n + 2)

attribute [grind cases] Even

example (h : Even 5) : False := by
  grind

set_option trace.grind.split true in
example (h : Even (n + 2)) : Even n := by
  grind
```

:::

# 表现

案例分析功能强大，但计算成本昂贵：每个级别的案例分割都会使搜索空间成倍增加。
重要的是要明智，不要进行不必要的分割。
特别是：
* *仅*当目标确实需要更深的分支时才增加 `splits` ；每增加一层，搜索空间就会成倍增加。
* 当大型模式匹配定义爆炸树时禁用 `splitMatch`；这可以通过设置 {option}`trace.grind.split` 来观察。
* 标志可以组合，例如`by grind -splitMatch (splits := 10) +splitImp`。
* {attr}`grind cases` 属性是 {ref "scoped-attributes"}_scoped_。
  修饰符 {keywordOf Lean.Parser.Term.attrKind}`local` 和 {keywordOf Lean.Parser.Term.attrKind}`scoped` 限制对节或命名空间的额外拆分。

{optionDocs trace.grind.split}
