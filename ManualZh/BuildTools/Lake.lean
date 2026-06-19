/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.Build.Package
import Lake.Build.Library
import Lake.Build.Module


import Manual.Meta
import ManualZh.BuildTools.Lake.CLI
import ManualZh.BuildTools.Lake.Config

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Lake" =>
%%%
tag := "lake"
%%%

Lake 是标准 Lean 构建工具。
它负责：
 * 配置构建并构建 Lean 代码
 * 获取和构建外部依赖项
 * 与 Reservoir 集成，Lean 软件包服务器
 * 运行测试、linter 和其他开发工作流程

Lake 是可扩展的。
它提供了丰富的 API，可用于定义未在 Lean 中编写的软件工件的增量构建任务、自动执行管理任务以及与外部工作流程集成。
对于不需要这些功能的构建配置，Lake 提供了一种声明性配置语言，可以用 TOML 或 Lean 文件编写。

本节介绍 Lake 的 {ref "lake-cli"}[命令行界面]、{ref "lake-config"}[配置文件]和 {ref "lake-api"}[内部 API]。
这三个共享一组概念和术语。


# 概念和术语
%%%
tag := "lake-vocab"
%%%

{deftech}_package_是Lean代码分发的基本单位。
单个包可能包含多个库或可执行程序。
包由一个目录组成，其中包含 {tech}[包配置] 文件和源代码。
软件包可能 {deftech}_require_ 其他软件包，在这种情况下，这些软件包的代码（更具体地说，它们的 {tech}[目标]）可用。
包的 {deftech}_direct dependency_ 是它需要的依赖项，{deftech}_transitive dependency_ 是包的直接依赖项及其传递依赖项。
包可以从 [Reservoir](https://reservoir.lean-lang.org/){TODO}[参考章节]、Lean 包存储库或从手动指定的位置获取。
{deftech}_Git dependency_ 由 Git 存储库 URL 以及修订（分支、标签或哈希）指定，并且必须在构建之前在本地克隆，而本地 {deftech}_path dependency_ 由相对于包目录的路径指定。

:::paragraph
{deftech}_workspace_ 是磁盘上的一个目录，其中包含 {tech}[package] 源代码的工作副本以及所有未指定为本地路径的 {tech}[transitive dependency] 的源代码。
为其创建工作区的包是 {deftech}_root package_。
该工作区还包含该包的任何构建的 {tech}[工件]，从而启用 {tech}[增量构建]。
不需要存在依赖关系和工件即可将目录视为工作空间；如果 {lake}`update` 和 {lake}`build` 等命令丢失，则会生成它们。
Lake 通常用于工作区。{margin}[创建工作区的 {lake}`init` 和 {lake}`new` 是例外。]
工作空间通常具有以下布局：

 * `lean-toolchain`：{tech}[工具链文件]。
 * `lakefile.toml` 或 `lakefile.lean`：根包的 {tech}[包配置] 文件。
 * `lake-manifest.json`：根包的 {tech}[清单]。
 * `.lake/`：由Lake管理的中间状态，例如构建的{tech}[artifacts]和依赖源代码。
   * `.lake/lakefile.olean`：根包的配置，已缓存。
   * `.lake/packages/`：工作区的 {deftech}_package 目录_，其中包含根包的所有非本地传递依赖项的副本，其构建的工件位于其自己的 `.lake` 目录中。
   * `.lake/build/`：{deftech}_build 目录_，其中包含根包的构建工件：
     * `.lake/build/bin`：包的 {deftech}_binary 目录_，其中包含构建的可执行文件。
     * `.lake/build/lib`：包的_库目录_，其中包含构建的库和 {tech}[`.olean` 文件]。
     * `.lake/build/ir`：包的中间结果目录，其中包含生成的中间工件，主要是 C 代码。
:::

:::figure "Workspace Layout" (tag :="workspace-layout")
```diagram
open Illuminate in
  let txt (s : String) (size : Float := 10) : Diagram SVG :=
    .text s { fontSize := size, anchor := TextAnchor.start }
  let bold (s : String) (size : Float := 11) : Diagram SVG :=
    .text s { fontSize := size, bold := true, anchor := TextAnchor.start }
  let mono (s : String) (size : Float := 10) : Diagram SVG :=
    .text s { fontSize := size, fontFamily := "monospace", anchor := TextAnchor.start }
  let items (ss : List String) (size : Float := 10) : Diagram SVG :=
    Diagram.vsep 3 (ss.map fun s => txt s size) (align := .left)
  let borderedBox (title : String) (content : Diagram SVG)
      (titleSize : Float := 11) (pad : Float := 8) : Diagram SVG :=
    Diagram.vsep 4 [bold title titleSize, content] (align := .left)
      |>.pad pad |>.frame (padding := 2) (cornerRadius := 4)

  let toolchain := mono "lean-toolchain"
  let rootPkg := borderedBox "Root package" <|
    items [
      "Package configuration file (lakefile.lean)",
      "Libraries",
      "Executables",
      "Manifest (lake-manifest.json)"
    ]
  let depItems := items ["Package configuration file", "Libraries", "Executables", "Artifacts"] 8
  let dep1 := borderedBox "Dependency 1" depItems 9 6
  let dep2 := borderedBox "Dependency 2" depItems 9 6
  let dots : Diagram SVG := .text "⋯" { fontSize := 14 }
  let packages := borderedBox "Packages" <|
    Diagram.vsep 8 [Diagram.hsep 12 [dep1, dep2], dots] (align := .left)
  let artifacts := borderedBox "Artifacts" <|
    items ["Built libraries", "Built executables"]
  let lakeDir := borderedBox "Lake Directory (.lake)" <|
    Diagram.vsep 10 [packages, artifacts] (align := .left)
  borderedBox "Workspace" <|
    Diagram.vsep 10 [toolchain, rootPkg, lakeDir] (align := .left)


```
:::

:::paragraph
{deftech}_package 配置_ 文件指定包的依赖项、设置和目标。
包可以指定适用于其包含的所有目标的配置选项。
它们可以写成两种格式：
 * {ref "lake-config-toml"}[TOML 格式] (`lakefile.toml`) 用于完全声明性包配置。
 * {ref "lake-config-lean"}[Lean 格式] (`lakefile.lean`) 另外支持使用 Lean 代码以声明性选项不支持的方式配置包。
:::

{deftech}_manifest_ 跟踪包中使用的其他包的特定版本。
清单和 {tech}[程序包配置] 文件一起为程序包指定一组唯一的传递依赖项。
在构建之前，Lake 会将每个依赖项的本地副本与清单中指定的版本同步。
如果没有可用的清单，Lake 会获取每个依赖项的最新匹配版本并创建一个清单。
如果清单中列出的包名称与包使用的名称不匹配，则会出现错误；在构建之前必须使用 {lake}`update` 更新清单。
清单应被视为包代码的一部分，并且通常应检查到源代码管理中。

:::paragraph
{deftech}_target_表示用户可以请求的输出。
持久构建输出（例如目标代码、可执行二进制文件或 {tech}[`.olean` 文件]）称为 {deftech}_artifact_。
在生成工件的过程中，Lake可能需要生成更多工件；例如，将 Lean 程序编译为可执行文件需要将其及其依赖项编译为目标文件，这些目标文件本身是从 C 源文件生成的，而 C 源文件是通过详细说明 Lean 源文件并生成 {tech}[`.olean` 文件] 产生的。
该链中的每个链接都是一个目标，Lake 安排每个链接依次构建。
链的开头是 {deftech}_初始目标_：
 * {tech}_Packages_ 是作为一个单元分发的 Lean 代码单元。
 * {deftech}_Libraries_ 是 Lean {tech}[模块] 的集合，在一个或多个 {deftech}_module root_ 下分层组织。
 * {deftech}_Executables_ 由定义 `main` 的_单个_模块组成。
 * {deftech}_外部库_ 是非 Lean *静态* 库，它们将链接到包及其依赖项的二进制文件，包括它们的共享库和可执行文件。
 * {deftech}_自定义目标_包含运行构建的任意代码，使用 Lake 的内部 API 编写。

除了 Lean 代码之外，包、库和可执行文件还包含影响后续构建步骤的配置设置。
包可以指定一组 {deftech}_default 目标_。
默认目标是包中的初始目标，这些目标将在指定了包但未指定特定目标的上下文中构建。
:::

:::paragraph
{deftech}_log_ 包含构建期间生成的信息。
日志被保存，以便可以在 {tech}[增量构建]期间重播。
日志中的消息有四个级别，按严重性排序：

 1. _跟踪消息_ 包含通常特定于运行构建的计算机的内部构建详细信息，包括 Lean 的特定调用以及传递到 shell 的其他工具。
 2. _信息性消息_包含一般信息输出，预计不会指示代码问题，例如 {keywordOf Lean.Parser.Command.eval}`#eval` 命令的结果。
 3. _警告_表示潜在的问题，例如未使用的变量绑定。
 4. _错误_解释为什么解析和精化无法完成。

默认情况下，跟踪消息是隐藏的，而其他消息是显示的。
可以使用 {lakeOpt}`--log-level` 选项、{lakeOpt}`--verbose` 标志或 {lakeOpt}`--quiet` 标志来调整阈值。
:::

## 包覆盖
%%%
tag := "package-overrides"
%%%

{tech}[程序包配置] 和 {tech}[清单] 一起描述了 Lake 期望获取依赖项的确切方式。
通常，这涉及通过网络制作远程 Git 存储库的本地副本。
如果无法访问远程存储库，Lake 将终止并出现错误。
由于依赖关系的来源是可预测的，因此构建可以跨系统重现；在所有机器上以相同的方式从相同的源检索包。

尽管如此，在某些情况下，无法像原始开发人员那样获取包依赖项。
例如，一些公司要求在使用之前对所有依赖项进行审核，并且并非每个人在工作时始终可以访问互联网。
在这些情况下，有必要通过其他方式获取包。

Lake 的 {deftech}_package overrides_ 允许将包依赖项从一个源重定向到另一个源，而无需修改任何 {tech}[包配置] 或 {tech}[清单]。
它们不允许向 {tech}[工作区] 添加或删除包。
工作区中的所有传递依赖项都遵循重定向。
包覆盖文件是一个 JSON 文件，其中包含包条目的备用列表。
这些条目将优先于包的 {tech}[manifest] 中的条目。
该文件可以通过 {lakeOpt}`--packages` 选项或将其放置在 Lake 工作区中的固定路径中提供给 Lake：`.lake/package-overrides.json`。

包中包条目的语法会覆盖镜像 {tech}[manifest] 的文件。
因此，可以将清单中的条目复制到包覆盖文件中（反之亦然）。
确定包条目必要语法的一种方法是将临时依赖项添加到与所需配置匹配的 {tech}[包配置]，运行 {lake}`update` 以生成具有该依赖项的清单，然后将条目从清单复制到包覆盖文件中。

:::example "Making Remote Dependencies Local"

考虑一个用例，其中程序是在无法访问网络的受限环境中开发的（例如，出于安全原因）。
该团队希望编译一个用 Lean 编写的小工具，该工具依赖于 [`@leanprover/Cli`](https://reservoir.lean-lang.org/@leanprover/Cli) 库来提供简单的命令行界面。
该工具的 {tech}[manifest] 看起来像这样：

```lakeManifest
{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [{
    "url": "https://github.com/leanprover/lean4-cli",
    "type": "git",
    "subDir": null,
    "scope": "leanprover",
    "rev": "0000000000000000000000000000000000000000",
    "name": "Cli",
    "manifestFile": "lake-manifest.json",
    "inputRev": null,
    "inherited": false,
    "configFile": "lakefile.toml"
  }],
  "name": "myTool",
  "lakeDir": ".lake",
  "fixedToolchain": false
}
```

构建此工具时，此清单将指示 Lake 从指定的 GitHub URL 下载 `Cli` 包。
但是，受限环境没有网络访问权限，因此除非 Lake 使用本地副本，否则构建将会失败。
这可以通过以下 {tech}[package overrides] 文件来完成：

```lakePackageOverrides
{
  "version": "1.2.0",
  "packages": [{
    "type": "path",
    "dir": "/etc/lean-packages/Cli",
    "name": "Cli",
    "manifestFile": "lake-manifest.json",
    "inherited": false,
    "configFile": "lakefile.toml"
  }]
}
```

这样，Lake 将改为解析 `Cli` 对位于路径 `/etc/lean-packages/Cli` 的本地包的依赖关系。

:::

## 构建

:::paragraph
生成所需的 {tech}[工件]，例如 {tech}[`.olean` 文件] 或可执行二进制文件，称为 {deftech}_build_。
构建由 {lake}`build` 命令或需要存在工件的其他命令（例如 {lake}`exe`）触发。
构建由以下步骤组成：

: {deftech (key := "configure package")}[配置]包

  如果 {tech}[程序包配置] 文件比缓存的配置文件 `lakefile.olean` 新，则重新详细说明程序包配置。
  当缓存文件丢失或提供 {lakeOpt}`--reconfigure` 或 {lakeOpt}`-R` 标志时，也会发生这种情况。
  使用 {lakeOpt}`-K` 更改选项不会触发配置文件的重新精化；在这些情况下 {lakeOpt}`-R` 是必要的。

: 计算依赖关系

  确定产生所需输出所需的工件集，以及产生它们的 {tech}[目标] 和 {tech}[方面]。
  这个过程是递归的，结果是依赖关系图。
  此图中的依赖关系与为包声明的依赖关系不同：包依赖于其他包，而构建目标依赖于其他构建目标，这些构建目标可能位于同一包中，也可能位于不同的包中。
  给定目标的一个方面可能取决于同一目标的其他方面。
  Lake 自动分析 Lean 模块的导入以发现其依赖关系，并且 {tomlField Lake.LeanLibConfig}`extraDepTargets` 字段可用于向目标添加其他依赖关系。

: 重放痕迹

  Lake 使用保存的 {deftech}_trace 文件_ 来确定需要构建哪些工件，而不是从头开始重建依赖关系图中的所有内容。
  在构建期间，Lake 记录用于生成每个工件的源文件或其他工件，保存每个输入的哈希值；这些 {deftech}_traces_ 保存在 {tech}[构建目录]中。{margin}[更具体地说，每个工件的跟踪文件包含其输入哈希的 Merkle 树哈希混合。]
  如果输入全部未修改，则不会重建相应的工件。
  跟踪文件还记录每个构建任务的 {tech}[log]；这些输出会被重播，就好像工件是重新构建的一样。
  尽可能重用以前的构建产品称为 {deftech}_增量构建_。

: 建筑文物

  当依赖关系图中所有未修改的依赖关系都已从其跟踪文件重播后，Lake 继续构建每个工件。
  这涉及在输入文件上运行适当的构建工具并保存工件及其跟踪文件，如相应方面中指定的那样。
:::

Lake 使用两种单独的哈希算法。
文本文件在规范化换行符后进行哈希处理，以便仅因特定于平台的换行符约定而不同的文件进行相同的哈希处理。
其他文件在没有任何标准化的情况下进行哈希处理。

Lean 与跟踪文件一起缓存输入哈希值。
每当构建一个工件时，它的哈希值都会保存在一个单独的文件中，可以重新读取该文件，而不是从头开始计算哈希值。
这是一个性能优化。
可以使用 {lakeOpt}`--rehash` 命令行选项禁用此功能，从而导致从其输入重新计算所有哈希值。

:::paragraph
在构建过程中，将向底层构建工具提供以下目录：
 * {deftech}_source 目录_包含可导入的 Lean 源代码。
 * {deftech}_library 目录_包含 {tech}[`.olean` 文件] 以及可用于链接的共享库和静态库；它通常由 {tech}[根包] 的库目录（在 `.lake/build/lib` 中找到）、工作区中其他包的库目录、当前 Lean 工具链的库目录和系统库目录组成。
 * {deftech}_Lake home_ 是 Lake 的安装目录，包括二进制文件、源代码和库。
   Lake 主目录中的库需要详细说明 Lake 配置文件，这些文件可以访问 Lean 的全部功能。
:::

## 刻面
%%%
tag := "lake-facets"
%%%

{deftech}_facet_ 描述了另一个目标的生成。
从概念上讲，任何目标都可能有多个方面。
但是，可执行文件、外部库和自定义目标仅提供一个隐式方面。
包、库和模块具有多个方面，在调用 {lake}`build` 时可以通过名称请求以选择相应的目标。

当未显式请求构面但指定了初始目标时，{lake}`build` 会生成初始目标的 {deftech}_default facet_。
每种类型的初始目标都有相应的默认方面（例如，从可执行目标生成可执行二进制文件或构建包的 {tech}[默认目标]）；其他方面可以在 {tech}[软件包配置] 中或通过 Lake 的 {ref "lake-cli"}[命令行接口] 显式请求。
Lake 的内部 API 可用于编写自定义构面。


```lakeHelp "build"
Build targets

USAGE:
  lake build [<targets>...] [-o <mappings>]

A target is specified with a string of the form:

  [@[<package>]/][<target>|[+]<module>][:<facet>]

You can also use the source path of a module as a target. For example,

  lake build Foo/Bar.lean:o

will build the Lean module (within the workspace) whose source file is
`Foo/Bar.lean` and compile the generated C file into a native object file.

The `@` and `+` markers can be used to disambiguate packages and modules
from file paths or other kinds of targets (e.g., executables or libraries).

LIBRARY FACETS:         build the library's ...
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
  static                static artifact (*.a file)
  shared                shared artifact (*.so, *.dll, or *.dylib file)

MODULE FACETS:          build the module's ...
  deps                  dependencies (e.g., imports, shared libraries, etc.)
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
  olean                 OLean (binary blob of Lean data for importers)
  ilean                 ILean (binary blob of metadata for the Lean LSP server)
  c                     compiled C file
  bc                    compiled LLVM bitcode file
  c.o                   compiled object file (of its C file)
  bc.o                  compiled object file (of its LLVM bitcode file)
  o                     compiled object file (of its configured backend)
  dynlib                shared library (e.g., for `--load-dynlib`)

TARGET EXAMPLES:        build the ...
  a                     default facet(s) of target `a`
  @a                    default target(s) of package `a`
  +A                    default facet(s) of module `A`
  @/a                   default facet(s) of target `a` of the root package
  @a/b                  default facet(s) of target `b` of package `a`
  @a/+A:c               C file of module `A` of package `a`
  :foo                  facet `foo` of the root package

A bare `lake build` command will build the default target(s) of the root
package. Package dependencies are not updated during a build.

With the Lake cache enabled, the `-o` option will cause Lake to track the
input-to-outputs mappings of targets in the root package touched during the
build and write them to the specified file at the end of the build. These
mappings can then be used to upload build artifacts to a remote cache with
`lake cache put`.
```


::::paragraph

可用于包的方面有：

```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: #[`package.barrel, `package.cache, `package.deps, `package.extraDep, `package.optBarrel, `package.optCache,
  `package.optRelease, `package.release, `package.transDeps]
-/
#guard_msgs in
#eval Lake.initPackageFacetConfigs.toList.map (·.1) |>.toArray |>.qsort (·.toString < ·.toString)
```
: `extraDep`

  包的额外依赖项目标的默认方面，在 {tomlField Lake.PackageConfig}`extraDepTargets` 字段中指定。

: `deps`

  该包的 {tech}[直接依赖项]。

: `transDeps`

  包的 {tech}[传递依赖项]，按拓扑排序。


: `optCache`

  包的可选缓存构建存档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取存档，将 *不会* 导致整个构建失败。

: `cache`

  包的缓存构建存档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取存档，将导致整个构建失败。

: `optBarrel`

  包的可选缓存构建存档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取存档，将 *不会* 导致整个构建失败。

: `barrel`

  包的缓存构建存档（例如，来自 Reservoir 或 GitHub）。
  如果无法获取存档，将导致整个构建失败。

: `optRelease`

  GitHub 版本中软件包的可选构建存档。
  如果无法获取版本，*不会* 导致整个构建失败。

: `release`

  GitHub 版本中的程序包构建存档。
  如果无法获取存档，将导致整个构建失败。


::::

```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: [`lean_lib.extraDep, `lean_lib.leanArts, `lean_lib.static.export, `lean_lib.shared, `lean_lib.modules, `lean_lib.static,
  `lean_lib.default]
-/
#guard_msgs in
#eval Lake.initLibraryFacetConfigs.toList.map (·.1)
```

:::paragraph

图书馆可用的方面有：

: `leanArts`

  Lean 编译器为库或可执行文件（{tech (key := ".olean files")}`*.olean`、`*.ilean` 和 `*.c` 文件）生成的工件。

: `static`

  C 编译器从 `leanArts`（即 `*.a` 文件）生成的静态库。

: `static.export`

  C 编译器从 `leanArts`（即 `*.a` 文件）生成的静态库，带有导出的符号。

: `shared`

  C 编译器从 `leanArts`（即 `*.so`、`*.dll` 或 `*.dylib` 文件，具体取决于平台）生成的共享库。

: `extraDep`

  Lean 库的 {tomlField Lake.LeanLibConfig}`extraDepTargets` 及其包的 {tomlField Lake.LeanLibConfig}`extraDepTargets` 。

:::

:::paragraph

可执行文件具有由可执行二进制文件组成的单个 `exe` 方面。

:::

```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: module.bc
module.bc.o
module.c
module.c.o
module.c.o.export
module.c.o.noexport
module.deps
module.dynlib
module.exportInfo
module.header
module.ilean
module.importAllArts
module.importArts
module.importInfo
module.imports
module.input
module.ir
module.lean
module.leanArts
module.ltar
module.o
module.o.export
module.o.noexport
module.olean
module.olean.private
module.olean.server
module.precompileImports
module.setup
module.transImports
-/
#guard_msgs in
#eval Lake.initModuleFacetConfigs.toList.toArray.map (·.1) |>.qsort (·.toString < ·.toString) |>.forM (IO.println)
```

:::paragraph
模块可用的方面有：

: `lean`

  模块的 Lean 源文件。

: `leanArts`（默认）

 模块的 Lean 工件（`*.olean`、`*.ilean`、`*.c` 文件）。

: `deps`

  模块的依赖项（例如导入或共享库）。

: `olean`

 模块的 {tech}[`.olean` 文件]。 {TODO}[模块系统完全落地后，添加`olean.private`和`olean.server`的文档]

: `ilean`

 该模块的 `.ilean` 文件，它是 Lean 语言服务器使用的元数据。

: `header`

  模块源文件的已解析模块头。

: `input`

  模块处理后的Lean源文件。将跟踪文件与解析其标头相结合。

: `imports`

  Lean 模块的直接导入，但不是全套传递导入。 {TODO}[模块系统完全落地后，请在此处添加 `module.importAllArts`、`module.importArts` 的文档]

: `precompileImports`

  Lean 模块的传递导入，编译为目标代码。

: `transImports`

  Lean 模块的传递导入，如 {tech}[`.olean` 文件]。

: `allImports`

  Lean 模块的直接导入和传递导入。

: `setup`

  模块的所有依赖项：传递本地导入和要使用 `--load-dynlib` 加载的共享库。
  返回要加载的共享库列表及其搜索路径。

: `ir`

  由 `lean` 生成的 `.ir` 文件（启用 {ref "module-structure"}[实验模块系统]）。

: `c`

 Lean 编译器生成的 C 文件。

: `bc`

 LLVM 位码文件，由 Lean 编译器生成。

: `c.o`

 从 C 文件生成的编译目标文件。在 Windows 上，这相当于 `.c.o.noexport`，而在其他平台上相当于 `.c.o.export`。

: `c.o.export`

 编译后的目标文件，由 C 文件生成，并导出 Lean 符号。

: `c.o.noexport`

 编译后的目标文件，由 C 文件生成，并导出 Lean 符号。

: `bc.o`

 编译后的目标文件，由 LLVM 位码文件生成。

: `o`

 配置后端的编译目标文件。

: `dynlib`

  共享库（例如，对于 Lean 选项 `--load-dynlib`）{TODO}[文档 Lean 命令行选项，以及此处的交叉引用]。

: `ltar`

  模块构建工件的压缩存档（通过 `leantar` 生成）。 {TODO}[手册中的文档`leantar`]

:::


## 脚本
%%%
tag := "lake-scripts"
%%%

Lake {tech}[包配置]文件可能包含 {deftech}_Lake 脚本_，它们是可以从命令行执行的嵌入式程序。
脚本旨在用于 Lake 的其他功能尚未很好地满足的特定于项目的任务。
普通可执行程序在 {name}`IO` {tech}[monad] 中运行，而脚本在 {name Lake.ScriptM}`ScriptM` 中运行，它使用有关工作空间的信息扩展了 {name}`IO`。
由于它们是 Lean 定义，因此 Lake 脚本只能以 Lean 配置格式定义。

:::::TODO

一旦我们可以导入足够的 Lake 来详细说明，请恢复以下内容

````
```lean -show
section
open Lake DSL
```

:::example "Listing Dependencies"

This Lake script lists all the transitive dependencies of the root package, along with their Git URLs, in alphabetical order.
Similar scripts could be used to check declared licenses, discover which dependencies have test drivers configured, or compute metrics about the transitive dependency set over time.

```lean
script "list-deps" := do
  let mut results := #[]
  for p in (← getWorkspace).packages do
    if p.name ≠ (← getWorkspace).root.name then
      results := results.push (p.name.toString, p.remoteUrl)
  results := results.qsort (·.1 < ·.1)
  IO.println "Dependencies:"
  for (name, url) in results do
    IO.println s!"{name}:\t{url}"
  return 0
```
:::

```lean -show
end
```
````

:::::

## 测试和 Lint 驱动程序
%%%
tag := "test-lint-drivers"
%%%

{deftech}_测试驱动程序_运行包的测试。
它可以是可执行目标、{tech}[Lake 脚本] 或库。
Lake 本身不是测试框架：{lake}`test` 命令只是定位配置的目标，构建它，然后（对于可执行文件和脚本）运行它。
库驱动程序纯粹由精化执行，因此它们不会作为单独的步骤运行。
断言、测试发现和报告取决于目标本身，无论是第三方测试库还是手写检查。

对于可执行文件和脚本，Lake 将非零退出代码视为测试失败。
对于库，任何精化错误都算作测试失败，包括 {keyword}`#guard` 样式命令的失败。

{deftech}_lint 驱动程序_ 与之类似，但它由 {lake}`lint` 运行，并检查包是否存在风格问题和其他并非错误、但表明可能存在问题的问题。
Lint 驱动程序只能是可执行文件或脚本，不能是库。

### 配置测试驱动程序
%%%
tag := "lake-test-driver-config"
%%%

在 `lakefile.toml` 中，将 {tomlField Lake.PackageConfig}`testDriver` 设置为同一配置中定义的可执行目标、库目标或脚本的名称：

:::::example "Test Driver (`lakefile.toml`)"

::::lakeToml Lake.PackageConfig _root_
```toml
name = "my-package"
testDriver = "my-package-tests"

[[lean_exe]]
name = "my-package-tests"
root = "Tests"
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := `«my-package»,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "my-package-tests",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := `«my-package»,
            name := `«my-package-tests»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[] },
                srcDir := FilePath.mk ".",
                root := `Tests,
                exeName := "my-package-tests",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-tests» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«my-package»,
                  name := `«my-package-tests»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[] },
                      srcDir := FilePath.mk ".",
                      root := `Tests,
                      exeName := "my-package-tests",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "my-package-tests",
  lintDriver := ""}
```
::::
:::::

在 `lakefile.lean` 中，可以在 {keyword}`package` 声明上设置 {name Lake.Package.testDriver}`testDriver` 字段（如上所述），或者使用 {attr}`test_driver` 属性标记脚本、可执行文件或库声明。
属性形式通常很方便，因为它将标记放置在目标旁边。

:::::example "Test Driver (`lakefile.lean`)"

::::lakeLean
```lean
import Lake
open Lake DSL

package «my-package» where
  testDriver := "my-package-tests"

lean_exe «my-package-tests» where
  root := `Tests
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := Lean.Name.mkNum `«my-package» 0,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "my-package-tests",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile.lean",
  relConfigFile := FilePath.mk "lakefile.lean",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := Lean.Name.mkNum `«my-package» 0,
            name := `«my-package-tests»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[] },
                srcDir := FilePath.mk ".",
                root := `Tests,
                exeName := "my-package-tests",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-tests» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := Lean.Name.mkNum `«my-package» 0,
                  name := `«my-package-tests»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[] },
                      srcDir := FilePath.mk ".",
                      root := `Tests,
                      exeName := "my-package-tests",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "my-package-tests",
  lintDriver := ""}
```
::::
:::::

每个包裹只能有一份声明带有 {attr}`test_driver` 标签。
在同一 Lake 配置文件中同时使用 {attr}`test_driver` 属性和非空 {name Lake.Package.testDriver}`testDriver` 字段是错误的。

测试驱动程序也可能是传递性 {tech (key:="require")}[必需] 的包依赖项中的目标。
要使用其他包中的目标，请使用 `<pkg>/<name>` 作为 `testDriver` 的值，其中 `<pkg>` 是在其中找到目标的包的名称。

### 运行测试
%%%
tag := "lake-test-running"
%%%

{lake}`test` 命令仅运行为 {tech}[root package] 配置的驱动程序。
不运行依赖项的测试驱动程序。

:::paragraph
如果测试驱动程序是可执行文件或脚本，Lake 首先传递来自 {tomlField Lake.PackageConfig}`testDriverArgs` 的参数，然后传递命令行上 `--` 之后的任何内容。
例如，

```
lake test -- --filter Foo --verbose
```

在配置完 {tomlField Lake.PackageConfig}`testDriverArgs` 后，将 `--filter Foo --verbose` 传递给驱动程序。
Lake 在运行可执行驱动程序之前构建它们。
:::

如果测试驱动程序是库，则不接受参数。
如果 {tomlField Lake.PackageConfig}`testDriverArgs` 非空或者 `--` 后面有任何参数，则 Lake 报告错误。
要运行测试，该库只是 {tech (key:="Lean elaborator")}[详细]。

如果为根包配置了测试驱动程序，{lake}`check-test` 将以退出代码 0 终止（即成功）。
它不会检查指定的目标是否确实存在。

### Lint 驱动程序
%%%
tag := "lake-lint-drivers"
%%%

Lint 驱动程序的配置和运行与 {ref "lake-test-driver-config"}[测试驱动程序]类似。
Lake 配置文件指定充当 lint 驱动程序的目标，{lake}`lint` 运行它。
该目标必须是可执行文件或脚本；与测试驱动程序不同，lint 驱动程序可能不是库。

在 TOML 格式的 Lake 配置文件中，包级字段 {tomlField Lake.PackageConfig}`lintDriver` 指定 lint 驱动程序目标的名称。

:::::example "Lint Driver (`lakefile.toml`)"
这个最小的 `lakefile.toml` 配置了一个 lint 驱动程序：

::::lakeToml Lake.PackageConfig _root_
```toml
name = "my-package"
lintDriver = "my-package-lint"

[[lean_exe]]
name = "my-package-lint"
root = "Lint"
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := `«my-package»,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "my-package-lint",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := `«my-package»,
            name := `«my-package-lint»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[] },
                srcDir := FilePath.mk ".",
                root := `Lint,
                exeName := "my-package-lint",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-lint» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«my-package»,
                  name := `«my-package-lint»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[] },
                      srcDir := FilePath.mk ".",
                      root := `Lint,
                      exeName := "my-package-lint",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := "my-package-lint"}
```
::::
:::::


在 `lakefile.lean` 中，在 {keyword}`package` 声明上设置 {name Lake.Package.lintDriver}`lintDriver` 字段，或者使用 {attr}`lint_driver` 属性标记脚本或可执行文件声明。
属性形式通常很方便，因为它将标记放置在目标旁边。

:::::example "Lint Driver (`lakefile.lean`)"

::::lakeLean
```lean
import Lake
open Lake DSL

package «my-package» where
  lintDriver := "my-package-lint"

lean_exe «my-package-lint» where
  root := `Lint
```
```expected
{wsIdx := 0,
  baseName := `«my-package»,
  keyName := Lean.Name.mkNum `«my-package» 0,
  origName := `«my-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      bootstrap := false,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "my-package-lint",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true,
      enableArtifactCache? := none,
      restoreAllArtifacts? := none,
      libPrefixOnWindows := false,
      allowImportAll := false,
      builtinLint? := none,
      fixedToolchain := false},
  configFile := FilePath.mk "lakefile.lean",
  relConfigFile := FilePath.mk "lakefile.lean",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  depIdxs := #[],
  depPkgs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := Lean.Name.mkNum `«my-package» 0,
            name := `«my-package-lint»,
            kind := `lean_exe,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[] },
                srcDir := FilePath.mk ".",
                root := `Lint,
                exeName := "my-package-lint",
                needs := #[],
                extraDepTargets := #[],
                supportInterpreter := false,
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`«my-package-lint» ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := Lean.Name.mkNum `«my-package» 0,
                  name := `«my-package-lint»,
                  kind := `lean_exe,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[] },
                      srcDir := FilePath.mk ".",
                      root := `Lint,
                      exeName := "my-package-lint",
                      needs := #[],
                      extraDepTargets := #[],
                      supportInterpreter := false,
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := "my-package-lint"}
```
::::
:::::

每个包裹只能有一份声明带有 {attr}`lint_driver` 标签。
在同一 Lake 配置文件中同时使用 {attr}`lint_driver` 属性和非空 {name Lake.Package.lintDriver}`lintDriver` 字段是错误的。

:::lakeSession -show
```lean +lakefile
import Lake
open Lake DSL
package p

@[lint_driver]
lean_exe Foo where

@[lint_driver]
lean_exe Bar where
```
```lakeCmd "lake build" +error
error: p: only one script or executable can be tagged @[lint_driver]
```
:::

可以使用用于测试驱动程序的相同 `<pkg>/<name>` 语法来引用依赖项包中的 lint 驱动程序。

{lake}`lint` 运行配置的驱动程序，首先传递 {tomlField Lake.PackageConfig}`lintDriverArgs`，然后在命令行上传递 `--` 之后的任何内容：

```
lake lint -- --warnings-as-errors
```

Lake 还具有单独的 {deftech}_builtin linter_，它直接在 Lean 模块上运行，独立于任何配置的驱动程序。
内置 linting 通过 `--builtin-lint` 和相关标志（请参阅 {lake}`lint`）或通过在封装配置中将 {tomlField Lake.PackageConfig}`builtinLint` 设置为 `true` 来启用。
当内置 linting 处于活动状态时，`--` 之前的位置 `MODULE` 参数选择要 lint 的模块，并且它们不会传递到配置的驱动程序。
因此，`lake lint Mathlib` 触发 `Mathlib` 上的内置 linting，而 `lake lint -- Mathlib` 将 `Mathlib` 传递给驱动程序。
这两种机制是独立的，并且可以一起运行：当两者都应用时，Lake 首先运行内置 linter，然后运行驱动程序。

如果为根包配置了 lint 驱动程序或者在其配置中将 {tomlField Lake.PackageConfig}`builtinLint` 设置为 `true`，则 {lake}`check-lint` 将以代码 0 退出（即成功）。


## GitHub 发布版本
%%%
tag := "lake-github"
%%%

Lake 支持向 GitHub 版本的包上传和下载构建工件（即存档的构建目录）。
这使得最终用户能够从云中获取预构建的工件，而无需自己从源重建包。
{envVar}`LAKE_NO_CACHE` 环境变量可用于禁用此功能。

### 正在下载

要下载工件，应配置包选项 `releaseRepo` 和 `buildArchive` 以指向托管该版本的 GitHub 存储库以及其中的正确工件名称（如果默认值不够）。
然后，设置 `preferReleaseBuild := true` 以告诉 Lake 将其作为额外的包依赖项进行获取和解包。

如果需要它的包是依赖项，Lake 将仅获取发布版本作为其标准构建过程的一部分（因为根包预计会被修改，因此通常与此方案不兼容）。
但是，如果希望获取根包的版本（例如，在克隆版本源之后但在编辑之前），可以通过 `lake build :release` 手动执行此操作。

Lake 在内部使用 `curl` 下载版本，并使用 `tar` 对其进行解压，因此最终用户必须安装这两个工具才能使用此功能。
如果 Lake 由于任何原因无法获取版本，它将继续从源构建。
此机制在技术上并不限于 GitHub：任何使用相同 URL 方案的 Git 主机都可以工作。

### 上传中

要将构建的包作为工件上传到 GitHub 版本，Lake 提供了 {lake}`upload` 命令作为方便的简写。
此命令使用 `tar` 将程序包的构建目录打包到存档中，并使用 `gh release upload` 将其附加到指定标记的预先存在的 GitHub 版本。
因此，为了使用它，包上传程序（而不是下载程序）需要安装 `gh`、GitHub CLI 并位于 `PATH` 中。

## 工件缓存
%%%
tag := "lake-cache"
%%%

*这是一项仍在开发中的实验性功能。*

Lake 支持 {deftech (key := "local cache")}_本地工件缓存_，用于存储各个构建产品，跟踪产生它们的完整输入集。
每个 {tech}[工具链] 都有自己的缓存，因为中间构建产品在工具链版本之间不兼容。
但是，工具链的缓存在使用它的所有本地 {tech}[工作空间] 之间共享，因此不需要重建公共依赖项。
如果具有相同工具链的两个独立工作区依赖于同一个包，那么它们可以共享彼此的构建产品。

由于这是一项实验性功能，因此默认情况下禁用本地缓存。
仅当 {envVar}`LAKE_ARTIFACT_CACHE` 环境变量设置为 `true` 或 {ref "lake-config"}[配置文件] 中的 {TODO}[ref] `enableArtifactCache` 字段设置为 `true` 时才启用。


### 远程工件缓存
%%%
tag := "lake-cache-remote"
%%%

可以从远程缓存服务器检索构建产品并将其放入本地缓存中。
这使得完全避免本地构建成为可能。
{lake}`cache get` 命令用于将工件下载到本地缓存中。

与 {ref "lake-github"}[GitHub 发行版本]相比，远程工件缓存更加细粒度。
它在各个源文件、{tech}[`.olean` 文件] 和目标代码级别（而不是整个包级别）跟踪构建产品。

### 映射

当传递 `-o` 选项时，{lake}`build` 跟踪用于生成每个构建产品的输入。
这些以 JSON 行格式存储到 {deftech}_mappings file_ 中，其中文件的每一行必须是有效的 JSON 对象。
映射文件跟踪单个构建，并包括工作区的 {tech}[根包] 的所有中间和最终构建产品，但不包括其依赖项。
这包括已经是最新且未重新生成的构建产品。
{lake}`cache put` 命令将映射文件中的构建产品从本地缓存上传到远程缓存。

### 配置

:::paragraph
远程工件缓存是使用以下环境变量配置的：
 * {envVar}`LAKE_CACHE_KEY`
 * {envVar}`LAKE_CACHE_ARTIFACT_ENDPOINT`
 * {envVar}`LAKE_CACHE_REVISION_ENDPOINT`
:::

{include 0 ManualZh.BuildTools.Lake.CLI}

{include 0 ManualZh.BuildTools.Lake.Config}

# 脚本 API 参考
%%%
tag := "lake-api"
%%%

除了普通的 {lean}`IO` 效果之外，Lake 脚本还可以访问 Lake 环境（提供有关当前工具链的信息，例如 Lean 编译器的位置）和当前工作区。
{name Lake.ScriptM}`ScriptM` 中提供了此访问权限。

{docstring Lake.ScriptM}

## 访问环境

提供对有关当前 Lake 环境的信息（例如 Lean、Lake 和其他工具的位置）的访问的 Monad 具有 {name Lake.MonadLakeEnv}`MonadLakeEnv` 实例。
对于 Lake API 中的所有单子（包括 {name Lake.ScriptM}`ScriptM`）都是如此。

{docstring Lake.MonadLakeEnv}

{docstring Lake.getLakeEnv}

{docstring Lake.getNoCache}

{docstring Lake.getTryCache}

{docstring Lake.getPkgUrlMap}

{docstring Lake.getElanToolchain}

### 搜索路径助手

{docstring Lake.getEnvLeanPath}

{docstring Lake.getEnvLeanSrcPath}

{docstring Lake.getEnvSharedLibPath}

### Elan 安装助手

{docstring Lake.getElanInstall?}

{docstring Lake.getElanHome?}

{docstring Lake.getElan?}

### Lean 安装助手

{docstring Lake.getLeanInstall}

{docstring Lake.getLeanSysroot}

{docstring Lake.getLeanSrcDir}

{docstring Lake.getLeanLibDir}

{docstring Lake.getLeanIncludeDir}

{docstring Lake.getLeanSystemLibDir}

{docstring Lake.getLean}

{docstring Lake.getLeanc}

{docstring Lake.getLeanSharedLib}

{docstring Lake.getLeanAr}

{docstring Lake.getLeanCc}

{docstring Lake.getLeanCc?}

### Lake 安装助手

{docstring Lake.getLakeInstall}

{docstring Lake.getLakeHome}

{docstring Lake.getLakeSrcDir}

{docstring Lake.getLakeLibDir}

{docstring Lake.getLake}

## 访问工作区

提供对有关当前 Lake 工作空间的信息的访问的 Monad 具有 {name Lake.MonadWorkspace}`MonadWorkspace` 实例。
特别是，存在 {name Lake.ScriptM}`ScriptM` 和 {name Lake.LakeM}`LakeM` 的实例。

```lean -show
section
open Lake
#synth MonadWorkspace ScriptM

end
```

{docstring Lake.MonadWorkspace}

{docstring Lake.getRootPackage}

{docstring Lake.findPackageByName?}

{docstring Lake.findPackageByKey?}

{docstring Lake.findModule?}

{docstring Lake.findLeanExe?}

{docstring Lake.findLeanLib?}

{docstring Lake.findExternLib?}

{docstring Lake.getLeanPath}

{docstring Lake.getLeanSrcPath}

{docstring Lake.getSharedLibPath}

{docstring Lake.getAugmentedLeanPath}

{docstring Lake.getAugmentedLeanSrcPath }

{docstring Lake.getAugmentedSharedLibPath}

{docstring Lake.getAugmentedEnv}
