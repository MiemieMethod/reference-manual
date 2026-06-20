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
file := "FFI"
tag := "string-ffi"
%%%


:::ffi "lean_string_object" (kind := type)
```
typedef struct {
    lean_object m_header;
    /* byte length including '\0' terminator */
    size_t      m_size;
    size_t      m_capacity;
    /* UTF8 length */
    size_t      m_length;
    char        m_data[0];
} lean_string_object;
```
C 中字符串的表示。更多详细信息请参见 {ref "string-runtime"}[运行时 {name}`String`s 的描述]。
:::

:::ffi "lean_is_string"
```
bool lean_is_string(lean_object * o)
```

如果 `o` 是字符串，则返回 `true`，否则返回 `false`。
:::

:::ffi "lean_to_string"
```
lean_string_object * lean_to_string(lean_object * o)
```
执行运行时检查 `o` 确实是一个字符串。如果 `o` 不是字符串，则断言失败。
:::

::::draft
:::planned 158
 * {lean}`String` 的完整 C API
:::
::::
