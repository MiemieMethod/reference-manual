/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "调用计算" =>
%%%
tag := "Thunk"
%%%

{deftech}_thunk_ 延迟值的计算。
特别是，{name}`Thunk` 类型用于延迟编译代码中值的计算，直到明确请求该值为止 - 该请求称为 {deftech (key := "force")}_forcing_ thunk。
计算出的值会被保存，因此后续请求不会导致重新计算。
当明确请求时，最多计算一次值称为 {deftech (key := "lazy evaluation")}_lazyvaluation_.{index}[call-by-need]
此缓存对于 Lean 的逻辑是不可见的，其中 {name}`Thunk` 相当于 {name}`Unit` 中的函数。


# 逻辑模型
%%%
tag := "Thunk-model"
%%%

thunk 被建模为包含 {lean}`Unit` 中的函数的单字段结构。
该结构体的字段是私有的，因此不能直接访问该函数本身。
相反，应使用 {name}`Thunk.get`。
从逻辑上看，它们是等价的； {name}`Thunk.get` 的存在将在编译器中被实现惰性求值的平台原语覆盖。

{docstring Thunk}

# 运行时表示
%%%
tag := "Thunk-runtime"
%%%

:::figure "Memory layout of thunks" (tag := "thunkffi")
```diagram
open Illuminate in
open Manual.Diagram in
layoutDiagram [
  ("m_header", .header, txt "Lean object header"),
  ("m_value", .object, twoLine "Saved value" "lean_object *"),
  ("m_closure", .object, twoLine "Closure" "lean_object *")
]
```
:::

Thunk 是 Lean 运行时支持的原始对象类型之一。
对象头包含一个特定的标记，指示对象是一个 thunk。

:::paragraph
Thunk 有两个字段：
 * `m_value` 是指向已保存值的指针，如果尚未计算该值，则该指针为空指针。
 * `m_closure` 是一个闭包，在计算值时将调用它。

运行时系统维护闭包或保存的值是空指针的不变量。
如果两者都是空指针，则 thunk 被强制作用在另一个线程上。
:::

当 thunk 为 {tech (key := "force")}[forced] 时，运行时系统首先检查保存的值是否已经计算过，如果是则返回。
否则，它会尝试通过原子地将闭包与空指针交换来获取闭包上的锁。
如果获取了锁，则调用它来计算值；计算出的值存储在保存的值字段中，并且对闭包的引用被删除。
如果没有，则另一个线程已经在计算该值；系统会等待直到计算完毕。

# 强制
%%%
tag := "Thunk-coercions"
%%%

:::leanSection
```lean -show
variable {α : Type u} {e : α}
```
存在从任何类型 {lean}`α` 到 {lean}`Thunk α` 的强制转换，将术语 {lean}`e` 转换为 {lean}`Thunk.mk fun () => e`。
由于精化器{ref "coercion-insertion"}[展开强制]，原始项 {lean}`e` 的求值被延迟；强制转换不等于 {name}`Thunk.pure`。
:::

:::example "Lazy Lists"

惰性列表是可能包含 thunk 的列表。
{name LazyList.delayed}`delayed` 构造函数导致根据需要计算列表的一部分。
```lean
inductive LazyList (α : Type u) where
  | nil
  | cons : α → LazyList α → LazyList α
  | delayed : Thunk (LazyList α) → LazyList α
deriving Inhabited
```

通过强制所有嵌入的 thunk，可以将惰性列表转换为普通列表。
```lean
def LazyList.toList : LazyList α → List α
  | .nil => []
  | .cons x xs => x :: xs.toList
  | .delayed xs => xs.get.toList
```

惰性列表上的许多操作可以在不强制嵌入 thunk 的情况下实现，而是构建更多的 thunk。
由于强制转换，{name LazyList.delayed}`delayed` 的主体不需要是对 {name}`Thunk.mk` 的显式调用。
```lean
def LazyList.take : Nat → LazyList α → LazyList α
  | 0, _ => .nil
  | _, .nil => .nil
  | n + 1, .cons x xs => .cons x <| .delayed <| take n xs
  | n + 1, .delayed xs => .delayed <| take (n + 1) xs.get

def LazyList.ofFn (f : Fin n → α) : LazyList α :=
  Fin.foldr n (init := .nil) fun i xs =>
    .delayed <| LazyList.cons (f i) xs

def LazyList.append (xs ys : LazyList α) : LazyList α :=
  .delayed <|
    match xs with
    | .nil => ys
    | .cons x xs' => LazyList.cons x (append xs' ys)
    | .delayed xs' => append xs'.get ys
```

Lean 程序通常看不到惰性：无法检查 thunk 是否已被强制。
但是，{keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` 可用于深入了解 thunk 评估。
```lean
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val
```

惰性列表 {lean}`xs` 和 {lean}`ys` 在求值时会发出痕迹。
```lean
def xs := LazyList.ofFn (n := 3) (observe "xs")
def ys := LazyList.ofFn (n := 3) (observe "ys")
```

将 {lean}`xs` 转换为普通列表会强制所有嵌入的 thunk：
```lean (name := lazy1)
#eval xs.toList
```
```leanOutput lazy1
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy1
[0, 1, 2]
```

同样，将 {lean}`xs.append ys` 转换为普通列表会强制嵌入 thunk：
```lean (name := lazy2)
#eval xs.append ys |>.toList
```
```leanOutput lazy2
xs: 0
xs: 1
xs: 2
ys: 0
ys: 1
ys: 2
```
```leanOutput lazy2
[0, 1, 2, 0, 1, 2]
```

在强制 thunk 之前将 {lean}`xs` 附加到自身会产生一组跟踪，因为每个 thunk 的代码仅计算一次：
```lean (name := lazy3)
#eval xs.append xs |>.toList
```
```leanOutput lazy3
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy3
[0, 1, 2, 0, 1, 2]
```

最后，采用 {lean}`xs.append ys` 前缀会导致仅评估 {lean}`ys` 中的部分 thunk：
```lean (name := lazy4)
#eval xs.append ys |>.take 4 |>.toList
```
```leanOutput lazy4
xs: 0
xs: 1
xs: 2
ys: 0
```
```leanOutput lazy4
[0, 1, 2, 0]
```
:::


# API 参考
%%%
tag := "Thunk-api"
%%%

{docstring Thunk.get}

{docstring Thunk.map}

{docstring Thunk.pure}

{docstring Thunk.bind}
