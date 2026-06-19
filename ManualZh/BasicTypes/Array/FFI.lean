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


#doc (Manual) "FFI" =>
%%%
tag := "array-ffi"
%%%

:::ffi "lean_string_object" (kind := type)
```
typedef struct {
    lean_object   m_header;
    size_t        m_size;
    size_t        m_capacity;
    lean_object * m_data[];
} lean_array_object;
```
C 中数组的表示。更多详细信息请参见 {ref "array-runtime"}[运行时 {name}`Array`s 的描述]。
:::

:::ffi "lean_is_array"
```
bool lean_is_array(lean_object * o)
```

如果 `o` 是数组，则返回 `true`，否则返回 `false`。
:::

:::ffi "lean_to_array"
```
lean_array_object * lean_to_array(lean_object * o)
```
执行运行时检查 `o` 确实是一个数组。如果 `o` 不是数组，则断言失败。
:::

::::draft
:::planned 158
 * {lean}`Array` 的完整 C API
:::
::::
