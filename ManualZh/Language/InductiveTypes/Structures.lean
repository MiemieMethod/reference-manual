/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Lean.Parser.Command («inductive» «structure» declValEqns computedField)

set_option guard_msgs.diff true

#doc (Manual) "结构声明" =>
%%%
tag := "structures"
%%%

:::syntax command (title := "Structure Declarations")
```grammar
$_:declModifiers
structure $d:declId $_:bracketedBinder* $[: $_]?
  $[extends $[$[$_ : ]?$_],*]?
  where
  $[$_:declModifiers $_ ::]?
  $_
$[deriving $[$_],*]?
```

声明一个新的结构类型。
:::

{deftech}[结构] 是仅具有单个构造函数且没有索引的归纳类型。
作为这些限制的交换，Lean 为结构生成代码，提供了许多便利：为每个字段生成投影函数，可以使用基于字段名称而不是位置参数的附加构造函数语法，可以使用类似的语法来替换某些命名字段的值，并且结构可以扩展其他结构。
就像其他归纳类型一样，结构可以是递归的；他们在严格积极性方面受到同样的限制。
结构不会给Lean增加任何表现力；它们的所有功能都是通过代码生成来实现的。

```lean -show
-- Test claim about recursive above

/--
error: (kernel) arg #1 of 'RecStruct.mk' has a non positive occurrence of the datatypes being declared
-/
#check_msgs in
structure RecStruct where
  next : RecStruct → RecStruct

```

# 结构参数
%%%
tag := "structure-params"
%%%

就像普通的归纳类型声明一样，结构声明的标头包含一个可以指定参数和结果 Universe 的签名。
结构不能定义 {tech}[索引族]。

# 领域
%%%
tag := "structure-fields"
%%%

结构声明的每个字段对应于构造函数的一个参数。

::::example "Inferring Universes"

{lean}`MyProd` 的结构与 {lean}`Prod` 相同。
```lean
structure MyProd (α β : Type _) where
  fst : α
  snd : β
```
这两个参数和两个字段是构造函数参数：
```signature
MyProd.mk.{u, v}
  {α : Type u}
  {β : Type v}
  (fst : α)
  (snd : β)
  : MyProd.{u, v} α β
```
另外，构造函数为{tech (key := "universe polymorphism")}[universe polymorphic]；类型构造函数 {name}`MyProd` 采用两个 Universe 参数：
```signature
MyProd.{u, v} (α : Type u) (β : Type v) : Type (max u v)
```

```lean -show
universe u v
```
每个字段的每种类型的宇宙层级必须小于或等于结构体的宇宙层级。
Lean 推断 {lean}`Type (max u v)` 是可以容纳 {lean}`Type u` 和 {lean}`Type v` 的最小宇宙。

::::

自动隐式参数会单独插入到每个字段中，即使它们的名称相同，并且这些字段会成为对类型进行量化的构造函数参数。

::::example "Auto-Implicit Parameters in Structure Fields"

结构 {lean}`MyStructure` 包含其类型具有自动隐式参数的字段：

```lean
structure MyStructure where
  field1 : Fin n
  field2 : Fin n
```
```lean -show
variable {n : Nat}
```
构造函数 {name}`MyStructure.mk` 中的每个字段都有自己的隐式参数 {lean}`n`，其类型为 {lean}`Nat`：
```signature
MyStructure.mk
  (field1 : {n : Nat} → Fin n)
  (field2 : {n : Nat} → Fin n)
  : MyStructure
```
类型构造函数 {name}`MyStructure` 不采用 Universe 参数，结果类型位于 `Type` 中，
这是 {name}`Nat` 和 {lean}`Fin n` 的宇宙：
```signature
MyStructure : Type
```
::::


对于每个字段，都会生成一个 {deftech}[投影函数]，用于从基础类型的构造函数中提取字段的值。
该函数位于结构名称的命名空间中。
结构字段投影由精化器专门处理（如 {ref "structure-inheritance"}[有关结构继承的部分]中所述），它执行查找命名空间之外的额外步骤。
当字段类型依赖于先前字段时，依赖投影函数的类型根据早期投影来编写，而不是显式的模式匹配。


:::: example "Dependent projection types"

结构体 {lean}`ArraySized` 包含一个字段，其类型取决于结构体参数和之前的字段：
```lean
structure ArraySized (α : Type u) (length : Nat)  where
  array : Array α
  size_eq_length : array.size = length
```

投影函数 {name ArraySized.size_eq_length}`size_eq_length` 的签名将结构类型的参数作为隐式参数，并使用相应的投影引用先前的字段：
```signature
ArraySized.size_eq_length.{u}
  {α : Type u} {length : Nat}
  (self : ArraySized α length)
  : self.array.size = length
```

::::

结构字段可能有默认值，用 `:=` 指定。
如果未提供明确的值，则使用这些值。


::: example "Default values"

图的邻接列表表示可以表示为 {lean}`Nat` 列表的数组。
数组的大小表示顶点的数量，每个顶点的出边都存储在数组中顶点的索引处。
由于为字段 {name Graph.adjacency}`adjacency` 提供了默认值 {lean}`#[]`，因此可以在不提供任何字段值的情况下构造空图 {lean}`Graph.empty`。
```lean
structure Graph where
  adjacency : Array (List Nat) := #[]

def Graph.empty : Graph := {}
```
:::


结构字段还可以使用点表示法通过其索引进行访问。
字段编号以 `1` 开头。


# 结构构造函数
%%%
tag := "structure-constructors"
%%%


可以通过在字段之前提供构造函数名称和 `::` 来显式命名结构构造函数。
如果未显式提供名称，则构造函数在结构类型的命名空间中命名为 `mk`。
{ref "declaration-modifiers"}[声明修饰符] 还可以与显式构造函数名称一起提供。

::: example "Non-default constructor name"
结构体 {lean}`Palindrome` 包含一个字符串和一个字符串反转后相同的证明：

```lean
structure Palindrome where
  ofString ::
  text : String
  is_palindrome : text.data.reverse = text.data
```

其构造函数名为 {name}`Palindrome.ofString`，而不是 `Palindrome.mk`。

:::

::: example "Modifiers on structure constructor"
```imports -show
import Std
```
结构 {lean}`NatStringBimap` 保持自然数和字符串之间的有限双射。
它由一对映射组成，每个键都作为值在另一个映射中仅出现一次。
由于构造函数是私有的，因此定义模块外部的代码无法构造新实例，并且必须使用提供的 API，它维护类型的不变量。
此外，显式提供默认构造函数名称可以将 {tech}[文档注释] 附加到构造函数。

```lean
structure NatStringBimap where
  /--
  Build a finite bijection between some
  natural numbers and strings
  -/
  private mk ::
  natToString : Std.HashMap Nat String
  stringToNat : Std.HashMap String Nat

def NatStringBimap.empty : NatStringBimap := ⟨{}, {}⟩

def NatStringBimap.insert
    (nat : Nat) (string : String)
    (map : NatStringBimap) :
    Option NatStringBimap :=
  if map.natToString.contains nat ||
      map.stringToNat.contains string then
    none
  else
    some <|
      NatStringBimap.mk
        (map.natToString.insert nat string)
        (map.stringToNat.insert string nat)
```
:::

由于结构由单构造函数归纳类型表示，因此可以使用 {tech}[匿名构造函数语法] 调用或匹配其构造函数。
此外，可以使用 {deftech}_结构实例_表示法来构造或匹配结构，其中包括字段的名称及其值。

::::syntax term (title := "Structure Instances")

```grammar
{ $_,*
  $[: $ty:term]? }
```

构造一个构造函数类型的值，给定命名字段的值。
字段说明符可以采用两种形式：
```grammar (of := Lean.Parser.Term.structInstField)
$x := $[private]? $y
```

```grammar (of := Lean.Parser.Term.structInstField)
$f:ident
```

{syntaxKind}`structInstLVal` 是字段名称（标识符）、字段索引（自然数）或方括号中的术语，后跟零个或多个子字段的序列。
子字段可以是前面带有点的字段名称或索引，也可以是方括号中的术语。

该语法针对结构构造函数的应用进行了详细精化。
为字段提供的值是按名称提供的，并且可以按任何顺序提供。
为子字段提供的值用于初始化结构构造函数的字段，这些结构本身在字段中找到。
构造结构时不允许使用方括号中的术语；它们用于结构更新。

不包含 `:=` 的字段说明符是字段缩写。
在本文中，标识符`f`是`f := f`的缩写；即用当前作用域中`f`的值来初始化字段`f`。

必须提供每个没有默认值的字段。
如果将策略指定为默认参数，则它将在精化时间运行以构造参数的值。

在模式上下文中，字段名称映射到与相应投影匹配的模式，并且字段缩写绑定作为字段名称的模式变量。
默认参数仍然存在于模式中；如果模式没有为具有默认值的字段指定值，则该模式仅与默认值匹配。

当字段定义包含 {keywordOf Lean.Parser.Term.stuctInstField}`private` 修饰符时，该值将放置在当前模块的 {tech}[私有范围] 中，即使结构值本身位于公共范围中也是如此。
该值包含在公共但未公开的帮助器定义中。
这对于类型类的实例特别有用，因为默认情况下，类型类的公共 {tech}[实例] 中 {tech}[方法] 的实现是 {tech}[暴露]。
此修饰符允许将它们设为私有。

可选的类型注释允许在未另行确定的上下文中指定结构类型。
::::

::::example "Patterns and default values"
结构 {name}`AugmentedIntList` 包含一个列表以及一些额外信息，如果省略则为空：
```lean
structure AugmentedIntList where
  list : List Int
  augmentation : String := ""
```

当测试列表是否为空时，函数 {name AugmentedIntList.isEmpty}`isEmpty` 必须显式匹配 {name AugmentedIntList.augmentation}`augmentation` 字段，即使它有默认值：
```lean (name := isEmptyDefaults)
def AugmentedIntList.isEmpty : AugmentedIntList → Bool
  | {list := [], augmentation := ""} => true
  | _ => false

#eval {list := [], augmentation := "extra" : AugmentedIntList}.isEmpty
```
```leanOutput isEmptyDefaults
false
```
::::

::::example "Private Field Values"
:::leanModules
即使结构的定义为 {tech}[exposeed]，也可以使用字段级 {keywordOf Lean.Parser.Term.stuctInstField}`private` 修饰符隐藏各个字段。
在此模块中，{name}`x` 的公开公共定义可以使用私有定义 {name}`secret`，因为 {name}`imaginary` 字段的值未公开：
```leanModule (moduleName := Main)
module

public structure Complex where
  real : Float
  imaginary : Float

private def secret := 2.3

@[expose]
public def x : Complex := {
  real := 5.0
  imaginary := private 2 * secret
}
```
:::
::::

::::example "Private Methods"
:::leanModules +error
在此模块中，{name}`State` 结构的存在是公共的，但其构造函数和字段是私有的。
函数 {name}`State.toString` 也是私有的，旨在通过 {name}`ToString` 实例进行访问。
但是，由于 {tech}[methods] 的实现是针对公共实例公开的，因此不允许这样做：
```leanModule (moduleName := Main) (name := tooExposed)
module

public structure State where
  private mk ::
  private count : Nat

private def State.toString (s : State) : String :=
  s!"⟨{s.count}⟩"

public instance : ToString State where
  toString s := s.toString
```
```leanOutput tooExposed
Invalid field `toString`: The environment does not contain `State.toString`, so it is not possible to project the field `toString` from an expression
  s
of type `State`

Note: A private declaration `State.toString` (from the current module) exists but would need to be public to access here.
```
:::
:::leanModules
将 {name}`toString` 的实现标记为 {keyword}`private` 会将其从模块的 {tech}[公共范围] 中删除，从而使其能够访问私有函数：
```leanModule (moduleName := Main) (name := tooExposed)
module

public structure State where
  private mk ::
  private count : Nat

private def State.toString (s : State) : String :=
  s!"⟨{s.count}⟩"

public instance : ToString State where
  toString s := private s.toString
```
:::
::::

:::syntax term (title := "Structure Updates")
```grammar
{$e:term with
  $_,*
  $[: $ty:term]?}
```
更新构造函数类型的值。
{keywordOf Lean.Parser.Term.structInst}`with` 子句之前的术语应具有结构类型；这是正在更新的值。
创建结构的新实例，其中未指定的每个字段都是从正在更新的值复制的，并且指定的字段将替换为其新值。
更新结构时，还可以通过将要更新的索引包含在方括号中来替换数组值。
此更新不要求索引表达式位于数组的范围内，并且超出范围的更新将被丢弃。
:::

::::example "Updating arrays"
:::keepEnv
更新结构可以使用数组索引以及投影名称。
超出范围的索引更新将被忽略：

```lean (name := arrayUpdate)
structure AugmentedIntArray where
  array : Array Int
  augmentation : String := ""
deriving Repr

def one : AugmentedIntArray := {array := #[1]}
def two : AugmentedIntArray := {one with array := #[1, 2]}
def two' : AugmentedIntArray := {two with array[0] := 2}
def two'' : AugmentedIntArray := {two with array[99] := 3}
#eval (one, two, two', two'')
```
```leanOutput arrayUpdate
({ array := #[1], augmentation := "" },
 { array := #[1, 2], augmentation := "" },
 { array := #[2, 2], augmentation := "" },
 { array := #[1, 2], augmentation := "" })
```
:::
::::

结构类型的值也可以使用 {keywordOf Lean.Parser.Command.declaration (parser:=declValEqns)}`where` 声明，后跟每个字段的定义。
这只能用作定义的一部分，不能在表达式上下文中使用。

::::example "`where` for structures"
:::keepEnv
Lean 中的产品类型是名为 {name}`Prod` 的结构。
产品可以使用它们的投影来定义：
```lean
def location : Float × Float where
  fst := 22.807
  snd := -13.923
```
:::
::::

# 结构继承
%%%
tag := "structure-inheritance"
%%%

可以使用可选的 {keywordOf Lean.Parser.Command.declaration (parser:=«structure»)}`extends` 子句将结构声明为扩展其他结构。
生成的结构类型具有所有父结构类型的所有字段。
如果父结构类型具有重叠的字段名称，则所有重叠的字段名称必须具有相同的类型。

生成的结构具有影响字段值的 {deftech}_字段解析顺序_。
如果可能，此解析顺序是结构父级的 [C3 线性化](https://en.wikipedia.org/wiki/C3_linearization)。
本质上，字段解析顺序应该是整个父集的总排序，以便每个 {keywordOf Lean.Parser.Command.declaration (parser:=«structure»)}`extends` 列表都是有序的。
当没有 C3 线性化时，仍然会使用启发式来查找阶数。
每个结构类型都按照其自己的字段解析顺序排列在第一位。

字段解析顺序用于计算可选字段的默认值。
当未指定字段值时，将使用解析顺序中定义的第一个默认值。
对默认值中字段的引用也使用字段解析顺序；这意味着覆盖父构造函数默认字段的子结构也可能会更改父字段的计算默认值。
由于子结构是其自身解析顺序的第一个元素，因此子结构中的默认值优先于父结构中的默认值。

```lean -show -keep
-- If the overlapping fields have different default values, then the default value from the first
-- parent structure in the resolution order that includes the field is used.
structure Q where
  x : Nat := 0
deriving Repr
structure Q' where
  x : Nat := 3
deriving Repr
structure Q'' extends Q, Q'
deriving Repr
structure Q''' extends Q', Q
deriving Repr

/--
info: structure Q'' : Type
number of parameters: 0
parents:
  Q''.toQ : Q
  Q''.toQ' : Q'
fields:
  Q.x : Nat :=
    0
constructor:
  Q''.mk (toQ : Q) : Q''
field notation resolution order:
  Q'', Q, Q'
-/
#check_msgs in
#print Q''

/-- info: 0 -/
#check_msgs in
#eval ({} : Q'').x

/--
info: structure Q''' : Type
number of parameters: 0
parents:
  Q'''.toQ' : Q'
  Q'''.toQ : Q
fields:
  Q'.x : Nat :=
    3
constructor:
  Q'''.mk (toQ' : Q') : Q'''
field notation resolution order:
  Q''', Q', Q
-/
#check_msgs in
#print Q'''

/-- info: 3 -/
#check_msgs in
#eval ({} : Q''').x

-- Defaults use local values
structure A where
  n : Nat := 0
deriving Repr
structure B extends A where
  k : Nat := n
deriving Repr
structure C extends A where
  n := 5
deriving Repr
structure C' extends A where
  n := 3
deriving Repr

structure D extends B, C, C'
deriving Repr
structure D' extends B, C', C
deriving Repr

#eval ({} : D).k

#eval ({} : D').k

```

当新结构扩展现有结构时，新结构的构造函数将现有结构的信息作为附加参数。
通常，这采用每个父结构类型的构造函数参数的形式。
该父值包含父级的所有字段。
然而，如果父级的字段重叠，则包括来自一个或多个父级的非重叠字段的子集，而不是父级结构的整个值，以防止重复字段信息。

父结构类型与其子结构类型之间不存在子类型关系。
即使结构体 `B` 扩展结构体 `A`，需要 `A` 的函数也不会接受 `B`。
但是，会生成将结构转换为其每个父结构的转换函数。
这些转换函数称为 {deftech}_parentprojections_。
父投影位于子结构的命名空间中，其名称是父结构的名称，前面带有 `to`。

::: example "Structure type inheritance with overlapping fields"
在此示例中，{lean}`Textbook` 是 {lean}`Book`，同时也是 {lean}`AcademicWork`：

```lean
structure Book where
  title : String
  author : String

structure AcademicWork where
  author : String
  discipline : String

structure Textbook extends Book, AcademicWork

#check Textbook.toBook
```

由于字段 `author` 出现在 {lean}`Book` 和 {lean}`AcademicWork` 中，因此构造函数 {name}`Textbook.mk` 不会将两个父项都作为参数。
它的签名是：
```signature
Textbook.mk (toBook : Book) (discipline : String) : Textbook
```

转换函数为：
```signature
Textbook.toBook (self : Textbook) : Book
```
```signature
Textbook.toAcademicWork (self : Textbook) : AcademicWork
```

后者将包含的 {lean}`Book` 的 `author` 字段与非捆绑的 `Discipline` 字段组合在一起，相当于：
```lean
def toAcademicWork (self : Textbook) : AcademicWork :=
  let .mk book discipline := self
  let .mk _title author := book
  .mk author discipline
```
```lean -show
-- check claim of equivalence
example : toAcademicWork = Textbook.toAcademicWork := by
  funext b
  cases b
  dsimp [toAcademicWork]
```

:::

可以使用生成的结构的投影，就好像它的字段只是父字段的并集一样。
当使用字段时，Lean精化器自动生成适当的投影。
同样，基于字段的初始化和结构更新符号隐藏了继承编码的细节。
但是，当使用构造函数的名称、使用 {tech}[匿名构造函数语法] 或通过索引而不是名称引用字段时，编码是可见的。

:::: example "Field Indices and Structure Inheritance"

```lean
structure Pair (α : Type u) where
  fst : α
  snd : α
deriving Repr

structure Triple (α : Type u) extends Pair α where
  thd : α
deriving Repr

def coords : Triple Nat := {fst := 17, snd := 2, thd := 95}
```

计算 {name}`coords` 的第一个字段索引会生成基础 {name}`Pair`，而不是字段 `fst` 的内容：
```lean (name := coords1)
#eval coords.1
```
```leanOutput coords1
{ fst := 17, snd := 2 }
```

精化器将 {lean}`coords.fst` 转换为 {lean}`coords.toPair.fst`。

```lean -show -keep
example (t : Triple α) : t.fst = t.toPair.fst := rfl
```
::::

:::: example "No structure subtyping"
:::keepEnv
给出偶数、偶素数和具体偶素数的定义：
```lean
structure EvenNumber where
  val : Nat
  isEven : 2 ∣ val := by decide

structure EvenPrime extends EvenNumber where
  notOne : val ≠ 1 := by decide
  isPrime : ∀ n, n ≤ val → n ∣ val  → n = 1 ∨ n = val

def two : EvenPrime where
  val := 2
  isPrime := by
    intros
    repeat' (cases ‹Nat.le _ _›)
    all_goals omega

def printEven (num : EvenNumber) : IO Unit :=
  IO.print num.val
```
将 {name}`printEven` 直接应用于 {name}`two` 是类型错误：
```lean +error (name := printTwo)
#check printEven two
```
```leanOutput printTwo
Application type mismatch: The argument
  two
has type
  EvenPrime
but is expected to have type
  EvenNumber
in the application
  printEven two
```
因为 {name}`EvenPrime` 类型的值并不是 {name}`EvenNumber` 类型的值。
:::
::::


```lean -show -keep
structure A where
  x : Nat
  y : Int
structure A' where
  x : Int
structure B where
  foo : Nat
structure C extends A where
  z : String
/-- info: C.mk (toA : A) (z : String) : _root_.C -/
#check_msgs in
#check C.mk

def someC : C where
  x := 1
  y := 2
  z := ""

/--
error: Type mismatch
  someC
has type
  _root_.C
but is expected to have type
  A
-/
#check_msgs in
#check (someC : A)

structure D extends A, B where
  z : String
/-- info: D.mk (toA : A) (toB : B) (z : String) : D -/
#check_msgs in
#check D.mk
structure E extends A, B where
  x := 44
  z : String
/-- info: E.mk (toA : A) (toB : B) (z : String) : E -/
#check_msgs in
#check E.mk
/--
error: Field type mismatch: Field `x` from parent `A'` has type
  Int
but is expected to have type
  Nat
-/
#check_msgs in
structure F extends A, A' where

```


{keywordOf Lean.Parser.Command.print}`#print` 命令显示有关结构类型的最重要信息，包括 {tech}[父投影]、所有字段及其默认值、构造函数和 {tech}[字段解析顺序]。
当处理包含继承菱形的深层层次结构时，此信息可能非常有用。

::: example "{keyword}`#print` and Structure Types"

该结构类型集合模拟了各种自行车，包括电动自行车和非电动自行车，以及普通尺寸和大型家庭自行车。
最终结构类型 {lean}`ElectricFamilyBike` 在其继承图中包含菱形，因为 {lean}`FamilyBike` 和 {lean}`ElectricBike` 都扩展了 {lean}`Bicycle`。

```lean
structure Vehicle where
  wheels : Nat

structure Bicycle extends Vehicle where
  wheels := 2

structure ElectricVehicle extends Vehicle where
  batteries : Nat := 1

structure FamilyBike extends Bicycle where
  wheels := 3

structure ElectricBike extends Bicycle, ElectricVehicle

structure ElectricFamilyBike
    extends FamilyBike, ElectricBike where
  batteries := 2
```

{keywordOf Lean.Parser.Command.print}`#print` 命令显示有关每种结构类型的重要信息：
```lean (name := el)
#print ElectricBike
```
```leanOutput el
structure ElectricBike : Type
number of parameters: 0
parents:
  ElectricBike.toBicycle : Bicycle
  ElectricBike.toElectricVehicle : ElectricVehicle
fields:
  Vehicle.wheels : Nat :=
    2
  ElectricVehicle.batteries : Nat :=
    1
constructor:
  ElectricBike.mk (toBicycle : Bicycle) (batteries : Nat) : ElectricBike
field notation resolution order:
  ElectricBike, Bicycle, ElectricVehicle, Vehicle
```

{lean}`ElectricFamilyBike` 默认情况下具有三个轮子，因为 {lean}`FamilyBike` 的分辨率顺序先于 {lean}`Bicycle`：
```lean  (name := elFam)
#print ElectricFamilyBike
```
```leanOutput elFam
structure ElectricFamilyBike : Type
number of parameters: 0
parents:
  ElectricFamilyBike.toFamilyBike : FamilyBike
  ElectricFamilyBike.toElectricBike : ElectricBike
fields:
  Vehicle.wheels : Nat :=
    3
  ElectricVehicle.batteries : Nat :=
    2
constructor:
  ElectricFamilyBike.mk (toFamilyBike : FamilyBike) (batteries : Nat) : ElectricFamilyBike
field notation resolution order:
  ElectricFamilyBike, FamilyBike, ElectricBike, Bicycle, ElectricVehicle, Vehicle
```

:::
