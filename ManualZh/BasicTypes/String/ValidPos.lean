/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "职位" =>
%%%
file := "Positions"
tag := "string-api-valid-pos"
%%%


{docstring String.ValidPos}

# 在字符串中
%%%
file := "In-Strings"
tag := "zh-basictypes-string-validpos-h001"
%%%

{docstring String.startValidPos}

{docstring String.endValidPos}

{docstring String.pos}

{docstring String.pos?}

{docstring String.pos!}

# 查找
%%%
file := "Lookups"
tag := "zh-basictypes-string-validpos-h002"
%%%

{docstring String.ValidPos.get}

{docstring String.ValidPos.get!}

{docstring String.ValidPos.get?}

{docstring String.ValidPos.set}

{docstring String.ValidPos.extract +allowMissing}

# 修改
%%%
file := "Modifications"
tag := "zh-basictypes-string-validpos-h003"
%%%

{docstring String.ValidPos.modify}

{docstring String.ValidPos.byte}

# 调整
%%%
file := "Adjustment"
tag := "zh-basictypes-string-validpos-h004"
%%%

{docstring String.ValidPos.prev}

{docstring String.ValidPos.prev!}

{docstring String.ValidPos.prev?}

{docstring String.ValidPos.next}

{docstring String.ValidPos.next!}

{docstring String.ValidPos.next?}

# 其他琴弦
%%%
file := "Other-Strings"
tag := "zh-basictypes-string-validpos-h005"
%%%

{docstring String.ValidPos.cast}

{docstring String.ValidPos.ofCopy}

{docstring String.ValidPos.setOfLE}

{docstring String.ValidPos.modifyOfLE}

{docstring String.ValidPos.toSlice}
