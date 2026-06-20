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

#doc (Manual) "原始头寸" =>
%%%
file := "Raw-Positions"
tag := "string-api-pos"
%%%


{docstring String.Pos.Raw}

# 有效性
%%%
file := "Validity"
tag := "zh-basictypes-string-rawpos-h001"
%%%

{docstring String.Pos.Raw.isValid}

{docstring String.Pos.Raw.isValidForSlice}

# 边界
%%%
file := "Boundaries"
tag := "zh-basictypes-string-rawpos-h002"
%%%

{docstring String.endPos}

{docstring String.Pos.Raw.atEnd}

# 比较
%%%
file := "Comparisons"
tag := "zh-basictypes-string-rawpos-h003"
%%%

{docstring String.Pos.Raw.min}

{docstring String.Pos.Raw.byteDistance}

{docstring String.Pos.Raw.substrEq}

# 调整
%%%
file := "Adjustment"
tag := "zh-basictypes-string-rawpos-h004"
%%%

{docstring String.Pos.Raw.prev}

{docstring String.Pos.Raw.next}

{docstring String.Pos.Raw.next'}

{docstring String.Pos.Raw.nextUntil}

{docstring String.Pos.Raw.nextWhile}

{docstring String.Pos.Raw.inc}

{docstring String.Pos.Raw.increaseBy}

{docstring String.Pos.Raw.offsetBy}

{docstring String.Pos.Raw.dec}

{docstring String.Pos.Raw.decreaseBy}

{docstring String.Pos.Raw.unoffsetBy}

# 字符串查找
%%%
file := "String-Lookups"
tag := "zh-basictypes-string-rawpos-h005"
%%%

{docstring String.Pos.Raw.extract}

{docstring String.Pos.Raw.get}

{docstring String.Pos.Raw.get!}

{docstring String.Pos.Raw.get'}

{docstring String.Pos.Raw.get?}

# 字符串修改
%%%
file := "String-Modifications"
tag := "zh-basictypes-string-rawpos-h006"
%%%

{docstring String.Pos.Raw.set}

{docstring String.Pos.Raw.modify}
