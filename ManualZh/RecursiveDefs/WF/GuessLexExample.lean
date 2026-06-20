/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta

/-!
This is extracted into its own file because line numbers show up in the error message, and we don't
want to update it over and over again as we edit the large file.
-/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "终止失败（包含在其他地方）" =>
%%%
file := "Termination-failure-_LPAR_for-inclusion-elsewhere_RPAR_"
tag := "zh-recursivedefs-wf-guesslexexample-root"
%%%

:::example "Termination failure"

如果没有 {keywordOf Lean.Parser.Command.declaration}`termination_by` 子句，Lean 会尝试推断良基递归的度量。
如果失败，则会打印上述表格。
在此示例中，{keywordOf Lean.Parser.Command.declaration}`decreasing_by` 子句只是阻止 Lean 尝试结构递归；这使错误消息保持特定。

```lean +error -keep (name := badwf)
def f : (n m l : Nat) → Nat
  | n+1, m+1, l+1 => [
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by all_goals decreasing_tactic
```
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n m l
1) 35:6-25 = = =
2) 36:6-23 = < _
3) 37:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
```

这三个递归调用由它们的源位置来标识。
该消息传达了以下事实：

* 在第一次递归调用中，所有参数（可证明）等于参数
* 在第二个递归调用中，第一个参数等于第一个参数，并且第二个参数可证明小于第二个参数。
  对于此递归调用，没有检查第三个参数，因为没有必要确定不存在合适的终止参数。
* 在第三次递归调用中，第一个参数严格递减，其他参数不进行检查。

当终止证明以这种方式失败时，发现问题的一个好方法是使用 {keywordOf Lean.Parser.Command.declaration}`termination_by` 显式指示预期的终止参数。
这将显示来自失败的策略的消息。

:::
