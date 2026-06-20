/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External (lit)


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "命令行界面" =>
%%%
file := "Command-Line-Interface"
tag := "lake-cli"
%%%


```lakeHelp
USAGE:
  lake [OPTIONS] <COMMAND>

COMMANDS:
  new <name> <temp>     create a Lean package in a new directory
  init <name> <temp>    create a Lean package in the current directory
  build <targets>...    build targets
  query <targets>...    build targets and output results
  exe <exe> <args>...   build an exe and run it in Lake's environment
  check-build           check if any default build targets are configured
  test                  test the package using the configured test driver
  check-test            check if there is a properly configured test driver
  lint                  lint the package
  check-lint            check if there is a properly configured lint driver
  clean                 remove build outputs
  shake                 minimize imports in source files
  env <cmd> <args>...   execute a command in Lake's environment
  lean <file>           elaborate a Lean file in Lake's context
  update                update dependencies and save them to the manifest
  pack                  pack build artifacts into an archive for distribution
  unpack                unpack build artifacts from an distributed archive
  upload <tag>          upload build artifacts to a GitHub release
  cache                 manage the Lake cache
  script                manage and run workspace scripts
  scripts               shorthand for `lake script list`
  run <script>          shorthand for `lake script run`
  translate-config      change language of the package configuration
  serve                 start the Lean language server

BASIC OPTIONS:
  --version             print version and exit
  --help, -h            print help of the program or a command and exit
  --dir, -d=file        use the package configuration in a specific directory
  --file, -f=file       use a specific file for the package configuration
  -K key[=value]        set the configuration file option named key
  --old                 only rebuild modified modules (ignore transitive deps)
  --rehash, -H          hash all files for traces (do not trust `.hash` files)
  --update              update dependencies on load (e.g., before a build)
  --packages=file       JSON file of package entries that override the manifest
  --reconfigure, -R     elaborate configuration files instead of using OLeans
  --keep-toolchain      do not update toolchain on workspace update
  --allow-empty         accept bare builds with no default targets configured
  --no-build            exit immediately if a build target is not up-to-date
  --no-cache            build packages locally; do not download build caches
  --try-cache           attempt to download build caches for supported packages
  --json, -J            output JSON-formatted results (in `lake query`)
  --text                output results as plain text (in `lake query`)

OUTPUT OPTIONS:
  --quiet, -q           hide informational logs and the progress indicator
  --verbose, -v         show trace logs (command invocations) and built targets
  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output
  --log-level=lv        minimum log level to output on success
                        (levels: trace, info, warning, error)
  --fail-level=lv       minimum log level to fail a build (default: error)
  --iofail              fail build if any I/O or other info is logged
                        (same as --fail-level=info)
  --wfail               fail build if warnings are logged
                        (same as --fail-level=warning)


See `lake help <command>` for more information on a specific command.
```

Lake 的命令行界面由一系列子命令组成。
所有子命令都具有通过某些环境变量和全局命令行选项进行配置的能力。
每个子命令都应该被理解为一个独立的实用程序，具有自己所需的参数语法和文档。

:::paragraph
Lake 的某些命令委托给 Lean 发行版中未包含的其他命令行实用程序。
这些实用程序必须在 `PATH` 上可用才能使用相应的功能：

 * 需要 `git` 才能访问 Git 依赖项。
 * 创建或提取云构建档案需要 `tar`，并且需要 `curl` 来获取它们。
 * 需要 `gh` 才能将构建工件上传到 GitHub 版本。

Lean 发行版包括 C 编译器工具链。
:::

# 环境变量
%%%
file := "Environment-Variables"
tag := "lake-environment"
%%%

```lakeHelp "env"
Execute a command in Lake's environment

USAGE:
  lake env [<cmd>] [<args>...]

Spawns a new process executing `cmd` with the given `args` and with
the environment set based on the detected Lean/Lake installations and
the workspace configuration (if it exists).

Specifically, this command sets the following environment variables:

  LAKE                  set to the detected Lake executable
  LAKE_HOME             set to the detected Lake home
  LEAN_SYSROOT          set to the detected Lean toolchain directory
  LEAN_AR               set to the detected Lean `ar` binary
  LEAN_CC               set to the detected `cc` (if not using the bundled one)
  LEAN_PATH             adds Lake's and the workspace's Lean library dirs
  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs
  PATH                  adds Lean's, Lake's, and the workspace's binary dirs
  PATH                  adds Lean's and the workspace's library dirs (Windows)
  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)
  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)

A bare `lake env` will print out the variables set and their values,
using the form NAME=VALUE like the POSIX `env` command.
```


当调用Lean编译器或其他工具时，Lake设置或修改多个环境变量。{index}[环境变量]
这些值取决于系统。
在不带任何参数的情况下调用 {lake}`env` 会显示环境变量及其值。
否则，将在 Lake 的环境中调用所提供的命令。

::::paragraph
设置以下变量，覆盖以前的值：
:::table (align := left) -header
*
  * {envVar +def}`LAKE`
  * 检测到的 Lake 可执行文件
*
  * {envVar}`LAKE_HOME`
  * 检测到{tech (key := "Lake home")}[Lake首页]
*
  * {envVar}`LEAN_SYSROOT`
  * 检测到Lean {tech}[toolchain]目录
*
 * {envVar}`LEAN_AR`
 * 检测到 Lean `ar` 二进制
*
  * {envVar}`LEAN_CC`
  * 检测到的 C 编译器（如果不使用捆绑的编译器）
:::
::::

::::paragraph
以下变量增加了附加信息：
:::table (align := left) -header
*
  * {envVar}`LEAN_PATH`
  * 添加 Lake 和 {tech (key := "workspace")}[工作空间] 的 Lean {tech (key := "library directories")}[库目录]。
*
  * {envVar}`LEAN_SRC_PATH`
  * 添加了 Lake 和 {tech (key := "workspace")}[工作空间] 的 {tech (key := "source directories")}[源目录]。
*
  * {envVar}`PATH`
  * 添加 Lean、Lake 和 {tech (key := "workspace")}[工作空间] 的 {tech (key := "binary directories")}[二进制目录]。
    在 Windows 上，还添加了 Lean 和 {tech (key := "workspace")}[工作空间] 的 {tech (key := "library directories")}[库目录]。
*
  * {envVar}`DYLD_LIBRARY_PATH`
  * 在 macOS 上，添加 Lean 和 {tech (key := "workspace")}[工作空间] 的 {tech (key := "library directories")}[库目录]。
*
  * {envVar}`LD_LIBRARY_PATH`
  * 在 Windows 和 macOS 以外的平台上，添加 Lean 和 {tech (key := "workspace")}[工作空间] 的 {tech (key := "library directories")}[库目录]。
:::
::::

::::paragraph
Lake本身可以配置以下环境变量：
:::table (align := left) -header
*
  * {envVar +def}`ELAN_HOME`
  * {ref "elan"}[Elan] 安装的位置，用于 {ref "automatic-toolchain-updates"}[自动工具链更新]。

*
  * {envVar +def}`ELAN`
  * `elan` 二进制文件的位置，用于 {ref "automatic-toolchain-updates"}[自动工具链更新]。
    如果未设置，则 `elan` 必须存在于 {envVar}`PATH` 上。

*
  * {envVar +def}`LAKE_HOME`
  * Lake 安装的位置。
    仅当 Lake 无法从当前运行的 `lake` 可执行文件的位置确定其安装路径时，才会参考此环境变量。
*
  * {envVar +def}`LEAN_SYSROOT`
  * Lean 安装的位置，用于查找 Lean 编译器、标准库和其他捆绑工具。
    Lake 首先检查其二进制文件是否与 Lean 安装位于同一位置，如果是，则使用该安装。
    如果不是，或者如果 {envVar +def}`LAKE_OVERRIDE_LEAN` 为真，则 Lake 查阅 {envVar}`LEAN_SYSROOT`。
    如果未设置，Lake 将查阅 {envVar +def}`LEAN` 环境变量来查找 Lean 编译器，并尝试查找与编译器相关的 Lean 安装。
    如果 {envVar}`LEAN` 设置但为空，则 Lake 认为 Lean 已禁用。
    如果未设置 {envVar}`LEAN_SYSROOT` 和 {envVar}`LEAN`，则使用 {envVar}`PATH` 上第一次出现的 `lean` 来查找安装。
*
  * {envVar +def}`LEAN_CC` 和 {envVar +def}`LEAN_AR`
  * 如果设置了 {envVar}`LEAN_CC` 和/或 {envVar}`LEAN_AR`，则在构建库时，其值将用作 C 编译器或 `ar` 命令。
    如果没有，Lake 将回退到 Lean 安装中的捆绑工具。
    如果未找到捆绑工具，则使用 {envVar +def}`CC` 或 {envVar +def}`AR` 的值，后跟 {envVar}`PATH` 上的 `cc` 或 `ar`。
*
  * {envVar +def}`LAKE_NO_CACHE`
  * 如果为 true，则 Lake 不使用 [Reservoir](https://reservoir.lean-lang.org/) 或 {ref "lake-github"}[GitHub] 的缓存版本。
    可以使用 {lakeOpt}`--try-cache` 命令行选项覆盖此环境变量。

*
  * {envVar +def}`LAKE_ARTIFACT_CACHE`
  * 如果为 true，则 Lake 使用工件缓存。
    这是一个实验性功能。

*
  * {envVar +def}`LAKE_CACHE_KEY`
  * 定义 {ref "lake-cache-remote"}[远程工件缓存] 的身份验证密钥。

*
  * {envVar +def}`LAKE_CACHE_ARTIFACT_ENDPOINT`
  * 用于工件上传的 {ref "lake-cache-remote"}[远程工件缓存] 的基本 URL。
    如果设置，则还必须设置 {envVar}`LAKE_CACHE_REVISION_ENDPOINT`。
    如果两者均未设置，Lake 将使用 Reservoir 代替。

*
  * {envVar +def}`LAKE_CACHE_REVISION_ENDPOINT`
  * {ref "lake-cache-remote"}[远程工件缓存]的基本 URL，用于上传每个工件的 {tech (key := "mappings file")}[输入/输出映射]。
    如果设置，则还必须设置 {envVar}`LAKE_CACHE_ARTIFACT_ENDPOINT`。
    如果两者均未设置，Lake 将使用 Reservoir 代替。

:::
::::

当环境变量的值为 `y`、`yes`、`t`、`true`、`on` 或 `1`（不区分大小写）时，Lake 认为环境变量为 true。
当变量的值为 `n`、`no`、`f`、`false`、`off` 或 `0`（不区分大小写）时，它认为变量为 false。
如果变量未设置，或其值既不是 true 也不是 false，则使用默认值。

```lean -show
-- Test the claim above
/--
info: def Lake.envToBool? : String → Option Bool :=
fun o =>
  if ["y", "yes", "t", "true", "on", "1"].contains o.toLower = true then some true
  else if ["n", "no", "f", "false", "off", "0"].contains o.toLower = true then some false else none
-/
#guard_msgs in
#print Lake.envToBool?
```

# 选项
%%%
file := "Options"
tag := "zh-buildtools-lake-cli-h002"
%%%

Lake 的命令行界面提供了许多全局选项以及执行重要任务的子命令。
单字符标志不能组合； `-HR` 不等同于 `-H -R`。

: {lakeOptDef flag}`--version`

  Lake 输出其版本并退出，不执行任何其他操作。

: {lakeOptDef flag}`--help` 或 {lakeOptDef flag}`-h`

  Lake 输出其版本以及使用信息并退出而不执行任何其他操作。
  子命令可以与 {lakeOpt}`--help` 一起使用，在这种情况下，会输出子命令的使用信息。

: {lakeOptDef option}`--dir DIR` 或 {lakeOptDef option}`-d=DIR`

  使用提供的目录作为包的位置，而不是当前工作目录。
  这并不总是等同于首先更改目录，因为将使用当前目录的 {tech (key := "toolchain file")}[工具链文件] 指示的 `lake` 版本，而不是 `DIR` 的版本。

: {lakeOptDef option}`--file FILE` 或 {lakeOptDef option}`-f=FILE`

  使用指定的 {tech (key := "package configuration")}[包配置] 文件而不是默认文件。

: {lakeOptDef flag}`--old`

  仅重建修改过的模块，忽略传递依赖。
  导入修改后的模块的模块将不会被重建。
  为了实现这一点，使用文件修改时间而不是哈希值来确定模块是否已更改。

: {lakeOptDef flag}`--rehash` 或 {lakeOptDef flag}`-H`

  忽略缓存的文件哈希值，重新计算它们。
  Lake 使用依赖项的哈希来确定是否重建工件。
  每当构建模块时，这些哈希值都会缓存在磁盘上。
  为了节省构建期间的时间，除非指定了 {lakeOpt}`--rehash`，否则将使用这些缓存的哈希值而不是重新计算每个哈希值。

: {lakeOptDef flag}`--allow-empty`

  接受在未配置 {tech (key := "default targets")}[默认目标] 时不产生输出的构建。

: {lakeOptDef flag}`--update`

  在加载 {tech (key := "package configuration")}[包配置] 之后但在执行其他任务（例如构建）之前更新依赖项。
  这相当于在所选命令之前运行 `lake update`，但由于不必加载配置两次，因此可能会更快。

: {lakeOptDef option}`--packages=FILE`

  使用指定的 {tech (key := "package overrides")}[包覆盖] 文件。
  可以多次指定以添加更多覆盖（以后的覆盖优先）。
  完整的包覆盖集还将包括来自 `.lake/package-overrides.json` 的包覆盖（如果有）。
  但是，此选项提供的选项优先。

:  {lakeOptDef flag}`--reconfigure` 或 {lakeOptDef flag}`-R`

  通常，首次配置包时，{tech (key := "package configuration")}[包配置] 文件为 {tech (key := "elaborator") -normalize}[详细]，结果缓存到 {tech (key := ".olean file")}[`.olean` 文件]，用于将来的调用，直到包配置为止
  提供此标志会导致重新详细说明配置文件。

: {lakeOptDef flag}`--keep-toolchain`

  默认情况下，Lake 尝试更新本地 {tech (key := "workspace")}[工作空间] 的 {tech (key := "toolchain file")}[工具链文件]。
  提供此标志会禁用 {ref "automatic-toolchain-updates"}[自动工具链更新]。

: {lakeOptDef flag}`--no-build`

  如果构建目标不是最新的，Lake 会立即退出，并返回非零退出代码。

: {lakeOptDef flag}`--no-cache`

  不要使用可用的云构建缓存，而是在本地构建所有包。
  不下载构建缓存。

: {lakeOptDef flag}`--try-cache`

  尝试下载支持的包的构建缓存

# 控制输出
%%%
file := "Controlling-Output"
tag := "zh-buildtools-lake-cli-h003"
%%%

这些选项允许控制构建时生成的 {tech}[log]。
除了显示或隐藏消息之外，当发出警告甚至信息时，构建也可能失败；这可用于强制执行不允许在构建期间输出的样式指南。

: {lakeOptDef flag}`--quiet`、{lakeOptDef flag}`-q`

  隐藏信息日志和进度指示器。

: {lakeOptDef flag}`--verbose`、{lakeOptDef flag}`-v`

  显示跟踪日志（通常是命令调用）和构建的 {tech (key := "targets")}[目标]。

:  {lakeOptDef flag}`--ansi`、{lakeOptDef flag}`--no-ansi`

  启用或禁用使用 [ANSI 转义码](https://en.wikipedia.org/wiki/ANSI_escape_code) 向 Lake 的输出添加颜色和动画。

:  {lakeOptDef option}`--log-level=LV`

  设置构建成功时显示的 {tech}[logs] 的最低级别。
  `LV` 可能是 `trace`、`info`、`warning` 或 `error`（不区分大小写）。
  当构建失败时，会显示所有级别。
  默认日志级别为 `info`。

:  {lakeOptDef option}`--fail-level=LV`

  设置 {tech}[log] 中的消息导致构建被视为失败的阈值。
  如果向日志发出的消息的级别大于或等于阈值，则构建失败。
  `LV` 可能是 `trace`、`info`、`warning` 或 `error`（不区分大小写）；默认为`error`。


: {lakeOptDef flag}`--iofail`

  如果记录任何 I/O 或其他信息，则会导致构建失败。
  这相当于 {lakeOpt}`--fail-level=info`。

: {lakeOptDef flag}`--wfail`

  如果记录任何警告，则会导致构建失败。
  这相当于 {lakeOpt}`--fail-level=warning`。

# 自动工具链更新
%%%
file := "Automatic-Toolchain-Updates"
tag := "automatic-toolchain-updates"
%%%

{lake}`update` 命令检查依赖项的更改，获取其源并相应地更新 {tech}[manifest]。
默认情况下，当新版本的依赖项指定更新的工具链时，{lake}`update` 还会尝试更新 {tech (key := "root package")}[根包] 的 {tech (key := "toolchain file")}[工具链文件]。
可以使用 {lakeOpt}`--keep-toolchain` 标志禁用此行为。

:::paragraph
如果多个依赖项指定较新的工具链，Lake 将选择最新的兼容工具链（如果存在）。
为了确定最新的兼容工具链，Lake 将包的 `lean-toolchain` 文件中列出的工具链解析为四类：

 * 版本，按版本号进行比较（例如，`v4.4.0` < `v4.8.0` 和 `v4.6.0-rc1` < `v4.6.0`）
 * 每晚构建，按日期进行比较（例如，`nightly-2024-01-10` < `nightly-2024-10-01`）
 * 根据对 Lean 编译器的拉取请求进行构建，这是无与伦比的
 * 其他版本，也是无法比拟的

多个类别的工具链版本是无法比较的。
如果没有最新的工具链，Lake 将打印警告并继续更新而不更改工具链。
:::

如果 Lake 确实找到新工具链，则会相应更新 {tech (key := "workspace")}[工作空间] 的 `lean-toolchain` 文件，并使用新工具链的 Lake 重新启​​动 {lake}`update`。
如果检测到 {ref "elan"}[Elan]，它将通过 `elan run` 生成新的 Lake 进程，其参数与最初运行 Lake 时使用的参数相同。
如果Elan缺失，会提示用户手动重启Lake，并退出并返回特殊错误代码（即`4`）。
Lake 使用的 Elan 可执行文件可以使用 {envVar}`ELAN` 环境变量进行配置。


# 创建包
%%%
file := "Creating-Packages"
tag := "zh-buildtools-lake-cli-h005"
%%%

```lakeHelp "new"
Create a Lean package in a new directory

USAGE:
  lake [+<lean-version>] new <name> [<template>][.<language>]

If you are using Lake through Elan (which is standard), you can create a
package with a specific Lean version via the `+` option.

The initial configuration and starter files are based on the template:

  std                   library and executable; default
  exe                   executable only
  lib                   library only
  math-lax              library only with a Mathlib dependency
  math                  library with Mathlib standards for linting and workflows

Templates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML
version of the configuration file, respectively. The default is TOML.
```

:::lake new "name [template][\".\"language]"

运行 {lake}`new` 会在新目录中创建初始 Lean 包。
该命令相当于创建一个名为 {lakeMeta}`name` 的目录，然后运行 {lake}`init`

:::

:::lake init "name [template][\".\"language]"

运行 {lake}`init` 会在当前目录中创建初始 Lean 包。
该包的内容基于模板，其中 {tech}[package]、其 {tech}[targets] 及其 {tech (key := "module roots")}[module root] 的名称源自当前目录的名称。

{lakeMeta}`template` 可能是：

: `std`（默认）

  创建包含库和可执行文件的包。

: `exe`

  创建仅包含可执行文件的包。

: `lib`

  创建仅包含库的包。

: `math`

  创建一个包，其中包含依赖于 [Mathlib](https://github.com/leanprover-community/mathlib4) 的库。

{lakeMeta}`language` 选择用于 {tech (key := "package configuration")}[包配置] 文件的文件格式，可以是 `lean`（默认值）或 `toml`。
:::

:::TODO
`lake init` 或 `lake new` 示例
:::

# 构建和运行
%%%
file := "Building-and-Running"
tag := "zh-buildtools-lake-cli-h006"
%%%

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

::::lake build "[targets...] [\"-o\" mappings]"

构建指定目标的指定事实。

每个 {lakeMeta}`targets` 由以下形式的字符串指定：

{lakeArgs}`[["@"]package["/"]][target|["+"]module][":"facet]`

可选的 {keyword}`@` 和 {keyword}`+` 标记可用于消除文件路径以及可执行文件和库中的包和模块的歧义，这些文件通过名称指定为 {lakeMeta}`target`。
如果未提供，{lakeMeta}`package` 默认为 {tech (key := "workspace")}[工作空间] 的 {tech (key := "root package")}[根包]。
如果工作区中的多个包中存在相同的目标名称，则选择在包依赖关系图的拓扑排序中找到的目标名称的第一个匹配项。
模块目标也可以通过其文件名来指定，冒号后面有一个可选的方面。

可用的 {tech}[facets] 取决于是否要构建包、库、可执行文件或模块。
它们列在 {ref "lake-facets"}[有关方面的部分]中。

使用 {ref "lake-cache"}[本地工件缓存] 时，{lakeOptDef option}`-o` 选项会保存 {tech (key := "mappings file")}[映射文件]，用于跟踪构建中每个步骤的输入和输出。
此文件可与 {lake}`cache get` 和 {lake}`cache put` 一起使用来与远程缓存交互。
映射文件采用 JSON 行格式，每行有一个有效的 JSON 对象，其文件扩展名通常为 `.jsonl`。
::::

::::example "Target and Facet Specifications"

:::table
*
  - `a`
  - 目标 `a` 的 {tech (key := "default facet")}[默认构面]
*
  - `@a`
  - {tech (key := "default targets")}[封装] `a` 的 {tech (key := "package")}[默认目标]
*
  - `+A`
  -  模块 `A` 的 Lean 工件（因为模块的默认方面是 `leanArts`）
*
  - `@a/b`
  - 包 `a` 的目标 `b` 的默认方面
*
  - `@a/+A:c`
  - 从 `a` 包的模块 `A` 编译的 C 文件
*
  - `:foo`
  - {tech (key := "root package")}[根包]的方面 `foo`
*
  - `A/B/C.lean:o`
  - 文件 `A/B/C.lean` 中模块的已编译目标代码
:::
::::

```lakeHelp "check-build"
Check if any default build targets are configured

USAGE:
  lake check-build

Exits with code 0 if the workspace's root package has any
default targets configured. Errors (with code 1) otherwise.

Does NOT verify that the configured default targets are valid.
It merely verifies that some are specified.

```

:::lake «check-build»
如果 {tech (key := "workspace")}[工作空间] 的 {tech (key := "root package")}[根包] 配置了任何 {tech (key := "default targets")}[默认目标]，则退出并显示代码 0。
否则出错（退出代码为 1）。

{lake}`check-build` *不*验证配置的默认目标是否有效。
它仅验证至少指定了一个。
:::

```lakeHelp "exe"
Build an executable target and run it in Lake's environment

USAGE:
  lake exe <exe-target> [<args>...]

ALIAS: lake exec

Looks for the executable target in the workspace (see `lake help build` to
learn how to specify targets), builds it if it is out of date, and then runs
it with the given `args` in Lake's environment (see `lake help env` for how
the environment is set up).
```

```lakeHelp "query"
Build targets and output results

USAGE:
  lake query [<targets>...]

Builds a set of targets, reporting progress on standard error and outputting
the results on standard out. Target results are output in the same order they
are listed and end with a newline. If `--json` is set, results are formatted as
JSON. Otherwise, they are printed as raw strings. Targets which do not have
output configured will be printed as an empty string or `null`.

See `lake help build` for information on and examples of targets.
```

:::lake query "[targets...]"
构建一组目标，报告 标准错误 的进度并在标准输出上输出结果。
目标结果按照列出的顺序输出，并以换行符结尾。
如果设置了 `--json`，则结果格式为 JSON。
否则，它们将被打印为原始字符串。

未配置输出的目标将打印为空字符串或 `null`。
对于可执行目标，输出是构建的可执行文件的路径。

使用与 {lake}`build` 中相同的语法指定目标。
:::

:::lake exe "«exe-target» [args...]" (alias := exec)

在工作区中查找可执行目标{lakeMeta}`exe-target`，如果过期则构建它，然后运行
它与 Lake 环境中给定的 {lakeMeta}`args` 一起使用。

有关目标规范的语法，请参阅 {lake}`build`；有关如何设置环境的说明，请参阅 {lake}`env`。

:::

```lakeHelp "clean"
Remove build outputs

USAGE:
  lake clean [<package>...]

If no package is specified, deletes the build directories of every package in
the workspace. Otherwise, just deletes those of the specified packages.
```

:::lake clean "[packages...]"

如果未指定包，则删除工作区中每个包的 {tech (key := "build directories")}[构建目录]。
否则，它只删除指定的 {lakeMeta}`packages` 的那些。

:::

```lakeHelp "env"
Execute a command in Lake's environment

USAGE:
  lake env [<cmd>] [<args>...]

Spawns a new process executing `cmd` with the given `args` and with
the environment set based on the detected Lean/Lake installations and
the workspace configuration (if it exists).

Specifically, this command sets the following environment variables:

  LAKE                  set to the detected Lake executable
  LAKE_HOME             set to the detected Lake home
  LEAN_SYSROOT          set to the detected Lean toolchain directory
  LEAN_AR               set to the detected Lean `ar` binary
  LEAN_CC               set to the detected `cc` (if not using the bundled one)
  LEAN_PATH             adds Lake's and the workspace's Lean library dirs
  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs
  PATH                  adds Lean's, Lake's, and the workspace's binary dirs
  PATH                  adds Lean's and the workspace's library dirs (Windows)
  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)
  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)

A bare `lake env` will print out the variables set and their values,
using the form NAME=VALUE like the POSIX `env` command.
```

::::lake env "[cmd [args...]]"

当提供 {lakeMeta}`cmd` 时，它将在 {ref "lake-environment"}[Lake 环境]中使用参数 {lakeMeta}`args` 执行。

如果未提供 {lakeMeta}`cmd`，Lake 将打印其运行工具的环境。
该环境是特定于系统的。
::::

```lakeHelp "lean"
Elaborate a Lean file in the context of the Lake workspace

USAGE:
  lake lean <file> [-- <args>...]

Build the imports of the given file and then runs `lean` on it using
the workspace's root package's additional Lean arguments and the given args
(in that order). The `lean` process is executed in Lake's environment like
`lake env lean` (see `lake help env` for how the environment is set up).
```

:::lake lean "file [\"--\" args...]"

构建给定 {lakeMeta}`file` 的导入，然后按顺序使用 {tech (key := "workspace")}[工作空间] 的 {tech (key := "root package")}[根包] 的附加 Lean 参数和给定的 {lakeMeta}`args` 在其上运行 `lean`。
`lean`进程在{ref "lake-environment"}[Lake的环境]中执行。
:::

# 模块导入
%%%
file := "Module-Imports"
tag := "zh-buildtools-lake-cli-h007"
%%%

```lakeHelp shake
Minimize imports in Lean source files

USAGE:
  lake shake [OPTIONS] [<MODULE>...]

Checks the current project for unused imports by analyzing generated `.olean`
files to deduce required imports and ensuring that every import contributes
some constant or other elaboration dependency.

ARGUMENTS:
  <MODULE>              A module path like `Mathlib`. All files transitively
                        reachable from the provided module(s) will be checked.
                        If not specified, uses the package's default targets.

OPTIONS:
  --force               Skip the `lake build --no-build` sanity check
  --keep-implied        Preserve imports implied by other imports
  --keep-prefix         Prefer parent module imports over specific submodules
  --keep-public         Preserve all `public` imports for API stability
  --add-public          Add new imports as `public` if they were in the
                        original public closure
  --explain             Show which constants require each import
  --fix                 Apply suggested fixes directly to source files
  --gh-style            Output in GitHub problem matcher format

ANNOTATIONS:
  Source files can contain special comments to control shake behavior:

  * `module -- shake: keep-downstream`
    Preserves this module in all downstream modules

  * `module -- shake: keep-all`
    Preserves all existing imports in this module

  * `import X -- shake: keep`
    Preserves this specific import
```

::::lake shake "[options...] [module ...]"

通过分析生成的 {tech (key := ".olean files")}[`.olean` 文件] 来推断所需的导入，检查当前项目是否有未使用的导入，确保每个导入都贡献一些常量或其他精化依赖项。

如果指定了 {lakeMeta}`module`，则会检查它以及可从它传递访问的所有文件。否则，将检查包的 {tech (key := "default targets")}[默认目标]。

:::paragraph
源文件可以包含特殊注释来控制 {lake}`shake` 的行为：

: `module -- shake: keep-downstream`

  在所有下游模块中保留此模块。

: `module -- shake: keep-all`

  保留此模块中的所有现有导入。

: `import X -- shake: keep`

  保留此特定导入。
:::

:::paragraph
{lakeMeta}`options` 可能是：

: `--force`

  跳过 `lake build --no-build` 健全性检查

: `--keep-implied`

  保留其他导入所隐含的导入

: `--keep-prefix`

  优先选择父模块导入而不是特定子模块

: `--keep-public`

  保留所有 `public` 导入，以确保 API 稳定性

: `--add-public`

  如果新导入在原始公开关闭中，则将其添加为 `public`

: `--explain`

  显示每次导入需要哪些常量

: `--fix`

  将建议的修复直接应用到源文件

: `--gh-style`

  以 GitHub 问题匹配器格式输出
:::

::::

# 开发工具
%%%
file := "Development-Tools"
tag := "zh-buildtools-lake-cli-h008"
%%%

Lake 包括对指定标准开发工具和工作流程的支持。
在命令行上，可以使用适当的 `lake` 子命令调用这些工具。

## 测试和检查
%%%
file := "Tests-and-Linters"
tag := "zh-buildtools-lake-cli-h009"
%%%

```lakeHelp test
Test the workspace's root package using its configured test driver

USAGE:
  lake test [-- <args>...]

A test driver can be configured by either setting the 'testDriver'
package configuration option or by tagging a script, executable, or library
`@[test_driver]`. A definition in a dependency can be used as a test driver
by using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.

A script test driver will be run with the  package configuration's
`testDriverArgs` plus the CLI `args`. An executable test driver will be
built and then run like a script. A library test driver will just be built.

```

:::lake test " [\"--\" args...]"
使用配置的 {tech (key := "test driver")}[测试驱动程序] 测试工作区的根包。

将构建一个可执行的测试驱动程序，然后使用包配置的 `testDriverArgs` 加上 CLI {lakeMeta}`args` 运行。
{tech (key := "Lake script")}[Lake 脚本] 测试驱动程序使用与可执行测试驱动程序相同的参数运行。
将刚刚构建一个库测试驱动程序；预计实施测试时，失败会导致构建因精化时间错误而失败。
:::

```lakeHelp lint
Lint the workspace's root package

USAGE:
  lake lint [OPTIONS] [<MODULE>...] [-- <args>...]

By default, runs the package's configured lint driver. If `builtinLint` is
set to `true` in the package configuration, builtin lints also run.

Builtin linting (`--builtin-lint`, `--builtin-only`, `--extra`, `--lint-all`,
`--lint-only`, or `builtinLint = true` in the package configuration) drives a
build of the targeted modules with the requested linter options enabled.
The lint driver path on its own does not trigger a build.

Positional `MODULE` arguments narrow only the builtin lints; if omitted,
the workspace's default target roots are used. The lint driver is invoked
with `lintDriverArgs` from the package config plus any arguments after
`--`; the `MODULE` list is not passed to it.

OPTIONS:
  --builtin-lint        run builtin environment and text linters
  --builtin-only        run only builtin linters, skip the lint driver
  --extra               run default builtin linters together with the
                        non-default (extra) ones
  --lint-all            run all registered linters, including defaults, extras,
                        and any other disabled-by-default linters
  --lint-only <name>    run only the specified linter (repeatable)

A lint driver can be configured by either setting the `lintDriver` package
configuration option or by tagging a script or executable `@[lint_driver]`.
A definition in a dependency can be used as a lint driver by using the
`<pkg>/<name>` syntax for the 'lintDriver' configuration option.

A script lint driver will be run with the package configuration's
`lintDriverArgs` plus the CLI `args`. An executable lint driver will be
built and then run like a script.

```

:::lake lint "[options...] [module...] [\"--\" args...]"

默认情况下，使用其配置的 lint 驱动程序对工作区的根包进行 lint 处理。
如果在包配置中将 `builtinLint` 设置为 {name}`true`，则也会运行内置 lint。

位置 {lakeMeta}`module` 参数仅缩小内置 lint；如果省略，
使用工作区的默认目标根。调用 lint 驱动程序
使用包配置中的 `lintDriverArgs` 以及之后的任何参数
`--`； {lakeMeta}`module` 列表不会传递给它。

脚本 lint 驱动程序将使用包配置运行
`lintDriverArgs` 加上 CLI `args`。可执行的 lint 驱动程序将是
构建然后像脚本一样运行。

内置 linter 是一组可以作为构建的一部分运行的 linter。其中一些是默认运行的；这些 linter 在指定 `--builtin-lint` 时运行。其他的 linter 是额外的 linter；仅当指定 `--extra` 时才运行这些 linter。

{lakeMeta}`options` 可能是：

: `--builtin-lint`

  运行默认的内置环境和文本 linter

: `--builtin-only`

  仅运行默认的内置 linter，跳过 lint 驱动程序

: `--extra`

  仅运行非默认（额外）内置 linter

: `--lint-all`

  运行所有已注册的 linter，包括默认值、额外值、
  以及任何其他默认禁用的 linter

: `--lint-only` `<name>`

  仅运行指定的 linter（可重复）。



可以通过设置 `lintDriver` 包来配置 lint 驱动程序
配置选项或通过标记脚本或可执行文件 `@[lint_driver]`。
依赖项中的定义可以用作 lint 驱动程序，方法是使用
“lintDriver”配置选项的 `<pkg>/<name>` 语法。

脚本 lint 驱动程序将使用包配置运行
`lintDriverArgs` 加上 CLI `args`。可执行的 lint 驱动程序将是
构建然后像脚本一样运行。
:::

```lakeHelp "check-test"
Check if there is a properly configured test driver

USAGE:
  lake check-test

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured test driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

```

:::lake «check-test»

检查是否有正确配置的测试驱动程序

如果工作区的根包具有正确的路径，则以代码 0 退出
配置的 lint 驱动程序。否则错误（代码为 1）。

不验证配置的测试驱动程序是否确实存在于
包或其依赖项。它仅验证是否已指定。

这对于区分失败的测试和错误配置的包很有用。
:::

```lakeHelp "check-lint"
Check if there is a properly configured lint driver

USAGE:
  lake check-lint

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured lint driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

```

:::lake «check-lint»
检查是否有正确配置的 lint 驱动程序

如果工作区的根包具有正确的路径，则以代码 0 退出
配置的 lint 驱动程序。否则错误（代码为 1）。

不验证配置的 lint 驱动程序是否确实存在于
包或其依赖项。它仅验证是否已指定。

这对于区分失败的 lint 和错误配置的包很有用。
:::


## 脚本
%%%
file := "Scripts"
tag := "zh-buildtools-lake-cli-h010"
%%%

```lakeHelp script
Manage Lake scripts

USAGE:
  lake script <COMMAND>

COMMANDS:
  list                  list available scripts
  run <script>          run a script
  doc <script>          print the docstring of a given script

See `lake script help <command>` for more information on a specific command.
```

```lakeHelp scripts
List available scripts

USAGE:
  lake script list

ALIAS: lake scripts

This command prints the list of all available scripts in the workspace.
```

:::lake script list (alias := scripts)
列出工作区中可用的 {ref "lake-scripts"}[脚本]。
:::

```lakeHelp run
Run a script

USAGE:
  lake script run [[<package>/]<script>] [<args>...]

ALIAS: lake run

This command runs the `script` of the workspace (or the specific `package`),
passing `args` to it.

A bare `lake run` command will run the default script(s) of the root package
(with no arguments).
```

:::lake script run "[[package\"/\"]script [args...]]" (alias := run)
此命令运行工作区的 {lakeMeta}`script`（或指定的 {lakeMeta}`package`），
将 {lakeMeta}`args` 传递给它。

裸 {lake}`run` 命令将运行根包的默认脚本（不带参数）。
:::

:::lake script doc "script"
打印 {lakeMeta}`script` 的文档注释。
:::



## 语言服务器
%%%
file := "Language-Server"
tag := "zh-buildtools-lake-cli-h011"
%%%

```lakeHelp serve
Start the Lean language server

USAGE:
  lake serve [-- <args>...]

Run the language server of the Lean installation (i.e., via `lean --server`)
with the package configuration's `moreServerArgs` field and `args`.

```

:::lake serve "[\"--\" args...]"
使用 {tech (key := "package configuration")}[包配置] 的 `moreServerArgs` 字段和 {lakeMeta}`args` 在工作区的根项目中运行 Lean 语言服务器。

此命令通常由编辑器或其他工具调用，而不是手动调用。
:::

# 依赖管理
%%%
file := "Dependency-Management"
tag := "zh-buildtools-lake-cli-h012"
%%%

```lakeHelp update
Update dependencies and save them to the manifest

USAGE:
  lake update [<package>...]

ALIAS: lake upgrade

Updates the Lake package manifest (i.e., `lake-manifest.json`),
downloading and upgrading packages as needed. For each new (transitive) git
dependency, the appropriate commit is cloned into a subdirectory of
`packagesDir`. No copy is made of local dependencies.

If a set of packages are specified, said dependencies are upgraded to
the latest version compatible with the package's configuration (or removed if
removed from the configuration). If there are dependencies on multiple versions
of the same package, the version materialized is undefined.

A bare `lake update` will upgrade all dependencies.
```

:::lake update "[packages...]"
更新 Lake 软件包 {tech}[manifest]（即 `lake-manifest.json`），根据需要下载和升级软件包。
对于每个新的（可传递的）{tech (key := "Git dependency")}[Git 依赖项]，相应的提交将被克隆到工作区的 {tech (key := "package directory")}[包目录] 的子目录中。
没有本地依赖项的副本。

如果指定了一组包 {lakeMeta}`packages`，则这些依赖项将升级到与包的配置兼容的最新版本（如果从配置中删除，则将其删除）。
如果同一包的多个版本存在依赖关系，则选择任意版本。

裸露的 {lake}`update` 将升级所有依赖项。
:::

# 包装和分销
%%%
file := "Packaging-and-Distribution"
tag := "zh-buildtools-lake-cli-h013"
%%%

```lakeHelp "upload"
Upload build artifacts to a GitHub release

USAGE:
  lake upload <tag>

Packs the root package's `buildDir` into a `tar.gz` archive using `tar` and
then uploads the asset to the pre-existing GitHub release `tag` using `gh`.
```

:::lake upload "tag"
使用 `tar` 将根包的 `buildDir` 打包到 `tar.gz` 存档中，然后使用以下命令将资源上传到预先存在的 [GitHub](https://github.com) 版本 {lakeMeta}`tag` [`gh`](https://cli.github.com/)。
尚不支持其他主机。
:::

## 缓存云构建
%%%
file := "Cached-Cloud-Builds"
tag := "zh-buildtools-lake-cli-h014"
%%%

*这些命令仍处于实验阶段。*
根据用户反馈，它们可能会在 Lake 的未来版本中发生更改。
使用 Reservoir 云构建存档的软件包应启用 {tomlField Lake.PackageConfig}`platformIndependent` 设置。

```lakeHelp "pack"
Pack build artifacts into an archive for distribution

USAGE:
  lake pack [<file.tgz>]

Packs the root package's `buildDir` into a gzip tar archive using `tar`.
If a path for the archive is not specified, creates an archive in the package's
Lake directory (`.lake`) named according to its `buildArchive` setting.

Does NOT build any artifacts. It just packs the existing ones.
```

:::lake pack "[archive.tar.gz]"
使用 `tar` 将根包的 {tech (key := "build directory")}[构建目录] 打包到 gzip 压缩的 tar 存档中。
如果未指定存档的路径，则存档位于程序包的 Lake 目录 (`.lake`) 中，并根据其 `buildArchive` 设置进行命名。
此命令不会构建任何工件：它只归档现有的内容。
用户应确保在运行此命令之前存在所需的工件。
:::

```lakeHelp "unpack"
Unpack build artifacts from a distributed archive

USAGE:
  lake unpack [<file.tgz>]

Unpack build artifacts from the gzip tar archive `file.tgz` into the root
package's `buildDir`. If a path for the archive is not specified, uses the
the package's `buildArchive` in its Lake directory (`.lake`).
```

:::lake unpack "[archive.tar.gz]"
将 gzip 压缩的 tar 存档 {lakeMeta}`archive.tgz` 的内容解压到根包的 {tech (key := "build directory")}[构建目录] 中。
如果未指定 {lakeMeta}`archive.tgz`，则使用包的 `buildArchive` 设置来确定文件名，并且该文件应位于包的 Lake 目录 (`.lake`) 中。
:::


# 本地缓存
%%%
file := "Local-Caches"
tag := "zh-buildtools-lake-cli-h015"
%%%

{lake}`cache get`、{lake}`cache put` 和 {lake}`cache add` 用于与远程缓存服务器交互。
这些命令是*实验性的*，并且仅在启用 {ref "lake-cache"}[本地缓存] 时才有用。

这些命令可以配置为使用 {deftech (key := "cache scope")}[缓存范围]，它是包的一组构建输出的服务器特定标识符。
在 Reservoir 上，范围目前与 GitHub 存储库相同，但将来可能包括工具链和平台信息。
其他远程缓存可以使用它们想要的任何范围方案。
缓存范围是使用 {lakeOptDef option}`--scope=` 选项指定的。
缓存范围与用于要求 Reservoir 中的包的范围不同。

```lakeCacheHelp
Manage the Lake cache

USAGE:
  lake cache <COMMAND>

COMMANDS:
  get [<mappings>]      download build outputs into the local Lake cache
  put <mappings>        upload build outputs to a remote cache
  add <mappings>        add input-to-output mappings to the Lake cache
  clean                 removes ALL from the local Lake cache
  services              print configured remote cache services

STAGING COMMANDS:
  stage <map> <dir>     copy build outputs from the cache to a directory
  unstage <dir>         cache build outputs from a staging directory
  put-staged <dir>      upload build outputs from a staging directory

See `lake cache help <command>` for more information on a specific command.
```

```lakeCacheHelp get
Download build outputs from a remote service into the Lake cache

USAGE:
  lake cache get [<mappings>]

OPTIONS:
  --max-revs=<n>                  backtrack up to n revisions (default: 100)
  --rev=<commit-hash>             uses this exact revision to lookup artifacts
  --service=<name>                cache service to fetch from
  --repo=<github-repo>            GitHub repository of the package or a fork
  --platform=<target-triple>      with Reservoir or --repo, sets the platform
  --toolchain=<name>              with Reservoir or --repo, sets the toolchain
  --scope=<remote-scope>          scope for a custom endpoint
  --mappings-only                 only download mappings, delay artifacts
  --force-download                redownload existing files

Downloads build outputs for packages in the workspace from a remote cache
service. The cache service used can be specified via the `--service` option.
Otherwise, Lake will the system default, or, if none is configured, Reservoir.
See `lake cache services` for more information on how to configure services.

If an input-to-outputs mappings file, `--scope`, or `--repo` is provided,
Lake will download build outputs for the root package. Otherwise, it will use
Reservoir to download outputs for each dependency in the workspace (in order).
Non-Reservoir dependencies will be skipped.

To determine what to download, Lake searches for input-to-output mappings for
a given build of the package via the cache service. This mapping is identified
by a Git revision and prefixed with a scope derived from the package's name,
GitHub repository, Lean toolchain, and current platform. The exact configuration
can be customized using options.

For Reservoir, setting `--repo` will cause Lake to lookup outputs for the root
package by a repository name, rather than the package's. This can be used to
download outputs for a fork of the Reservoir package (if such artifacts are
available). The `--platform` and `--toolchain` options can be used to download
artifacts for a different platform/toolchain configuration than Lake detects.
For a custom endpoint, the full prefix Lake uses can be set via  `--scope`.

If `--rev` is not set, Lake uses the package's current revision to lookup
artifacts. If no mappings are found, Lake will backtrack the Git history up to
`--max-revs`, looking for a revision with mappings. If `--max-revs` is 0, Lake
will search the repository's entire history (or as far as Git will allow).

By default, Lake will download both the input-to-output mappings and the
output artifacts for a package. By using `--mappings-onlys`, Lake will only
download the mappings and delay downloading artifacts until they are needed.

If a download for an artifact fails or the download process for a whole
package fails, Lake will report this and continue on to the next. Once done,
if any download failed, Lake will exit with a nonzero status code.
```

:::lake cache get "[mappings] [\"--max-revs=\" cn] [\"--rev=\" «commit-hash»] [\"--service=\" «name»] [\"--repo=\" «github-repo»] [\"--platform=\" «target-triple»] [\"--toolchain=\"«name»] [\"--scope=\" «remote-scope»] [\"--mappings-only\"] [\"--force-download\"]"
将工作区中包的构建输出从远程缓存服务下载到本地 Lake {tech (key:="local cache")}[工件缓存]。
使用的缓存服务可以通过 {lakeOpt}`--service` 选项指定。
否则，Lake 将使用系统默认值，或者，如果未配置，则使用 Reservoir。
有关如何配置服务的更多信息，请参阅 {lake}`cache services`。

如果提供了输入到输出 {lakeMeta}`mappings` 文件、{lakeMeta}`remote-scope` 或 {lakeMeta}`github-repo`，Lake 将下载根包的构建输出。
否则，它将按顺序下载根依赖树中每个包的输出（使用 Reservoir）。
将跳过非 Reservoir 依赖项。

对于 Reservoir，设置 {lakeOpt}`--repo` 将导致 Lake 按存储库名称（而不是包的名称）查找根包的输出。
这可用于下载 Reservoir 包的分支的输出（如果此类工件可用）。
{lakeOpt}`--platform` 和 {lakeOpt}`--toolchain` 选项可用于下载 Lake 检测到的不同平台/工具链配置的工件。
对于自定义端点，Lake 使用的完整前缀可以通过 {lakeOpt}`--scope` 设置。

如果未设置 `--rev`，Lake 将使用包的当前版本来查找工件。
Lake 将下载具有可用映射的最新提交的工件。
它将回溯到 {lakeOptDef option}`--max-revs`，默认为 100。
如果设置为 0，Lake 将搜索存储库的整个历史记录，或者尽可能早地搜索 Git 允许的历史记录。

默认情况下，Lake 将下载包的输入到输出映射和输出工件。
使用 {lakeOptDef option}`--mappings-only` 将导致 Lake 仅下载映射并延迟下载工件，直到需要它们为止。
使用 {lakeOptDef option}`--force-download` 将重新下载现有文件。

下载时，如果工件下载失败或整个包的下载过程失败，Lake 将继续。
但是，在这种情况下，它将报告此情况并以非零状态代码退出。
:::


```lakeCacheHelp put
Upload build outputs from the Lake cache to a remote service

USAGE:
  lake cache put <mappings> <scope-option>

Uploads the input-to-output mappings contained in the specified file along
with the corresponding output artifacts to a remote cache. The cache service
used can be specified via the `--service` option. If not specified, Lake will use
the system default, or error if none is configured. See the help page of
`lake cache services` for more information on how to configure services.

Files are uploaded using the AWS Signature Version 4 authentication protocol
via `curl`. Thus, the service should generally be an S3-compatible bucket. The
authentication key is set via the `LAKE_CACHE_KEY` environment variable.

Since Lake does not currently use cryptographically secure hashes for
artifacts and outputs, uploads to the cache are prefixed with a scope to avoid
clashes. This scope is configured with the following options:

  --scope=<remote-scope>          sets a fixed scope
  --repo=<github-repo>            uses the repository + toolchain & platform
  --toolchain=<name>              with --repo, sets the toolchain
  --platform=<target-triple>      with --repo, sets the platform

At least one of `--scope` or `--repo` must be set. If `--repo` is used, Lake
will produce a scope by augmenting the repository with toolchain and platform
information as it deems necessary. If `--scope` is set, Lake will use the
specified scope verbatim.

Artifacts are uploaded to the artifact endpoint with a file name derived
from their Lake content hash (and prefixed by the repository or scope).
The mappings file is uploaded to the revision endpoint with a file name
derived from the package's current Git revision (and prefixed by the
full scope). As such, the command will warn if the work tree currently
has changes.
```

::::lake cache put "mappings «scope-option»"
将指定文件中包含的输入到输出映射以及相应的输出工件上传到远程缓存。
使用的缓存服务可以通过 {lakeOpt}`--service` 选项指定。
如果未指定，Lake 将使用系统默认值，如果未配置则出错。
有关如何配置服务的更多信息，请参阅 {lake}`cache services`。

文件通过 `curl` 使用 AWS 签名版本 4 身份验证协议上传。
因此，服务通常应该是 S3 兼容的存储桶。
身份验证密钥通过 {envVar}`LAKE_CACHE_KEY` 环境变量设置。

由于 Lake 当前不使用加密安全哈希值
工件和输出，上传到缓存都以范围为前缀以避免
冲突。此范围配置有以下选项：

:::table -header
*
  * {lakeOpt}`--scope`{lit}`=`{lakeMeta}`<remote-scope>`
  * 设置固定范围
*
  * {lakeOptDef option}`--repo`{lit}`=`{lakeMeta}`<github-repo>`
  * 使用存储库+工具链和平台
*
  * {lakeOptDef option}`--toolchain`{lit}`=`{lakeMeta}`<name>`
  * 使用 {lakeOpt}`--repo`，设置工具链
*
  * {lakeOptDef option}`--platform`{lit}`=`{lakeMeta}`<target-triple>`
  * 用{lakeOpt}`--repo`，设置平台
:::

必须至少设置 {lakeOpt}`--scope` 或 {lakeOpt}`--repo` 之一。
如果使用 {lakeOpt}`--repo`，Lake 将根据需要使用工具链和平台信息扩充存储库来生成范围。
如果设置了 {lakeOpt}`--scope`，Lake 将逐字使用指定的范围。

工件上传到工件端点，文件名源自其 Lake 内容哈希（并以存储库或范围为前缀）。
映射文件上传到修订端点，其文件名源自包的当前 Git 修订（并以完整范围为前缀）。
因此，如果工作树当前发生更改，该命令将发出警告。
::::

```lakeCacheHelp add
Add input-to-output mappings to the Lake cache

USAGE:
  lake cache add <mappings>

OPTIONS:
  --service=<name>                cache service to fetch from on demand
  --scope=<remote-scope>          the prefix of artifacts within the service
  --repo=<github-repo>            for Reservoir, a GitHub repository scope

Reads a list of input-to-output mappings from the provided file and adds
them to the local Lake cache. If `--service` is provided, the output artifacts
can then be fetched lazily from that service during a Lake build. The service
must either be `reservoir` or  be configured through the Lake system
configuration (see the help page of `lake cache services` for details).

Since Lake does not currently use cryptographically secure hashes for
artifacts and outputs, artifacts in a cache service are prefixed with a scope
to avoid clashes. For Reservoir, this scope can either be a package (set via
`--scope`) or a repository (set via `--repo`). For S3 services, both options
are synonymous.
```

::::lake cache add "mappings [\"--service=\" «name»] [\"--scope=\" «remote-scope»] [\"--repo=\" «github-repo»]"
从提供的文件中读取输入到输出映射的列表，并将其添加到本地 Lake 缓存中。
如果提供了 {lakeOpt}`--service`，则可以在 Lake 构建期间从该服务延迟获取输出工件。
该服务必须是 `reservoir` 或通过 Lake 系统配置进行配置（有关详细信息，请参阅 {lake}`cache services`）。

由于 Lake 当前不使用加密安全哈希来处理工件和输出，因此缓存服务中的工件都以范围为前缀以避免冲突。
对于 Reservoir，此范围可以是包（通过 {lakeOpt}`--scope` 设置）或存储库（通过 {lakeOpt}`--repo` 设置）。
对于 S3 服务，这两个选项是同义词。
::::

```lakeCacheHelp clean
Removes ALL files from the local Lake cache

USAGE:
  lake cache clean

Deletes the configured Lake cache directory. If a workspace configuration
exists, this will delete the cache directory it uses. Otherwise, it will
delete the default Lake cache directory for the system.
```

:::lake cache clean
删除配置的 Lake {tech (key:="local cache")}[工件缓存] 目录。
如果工作区配置存在，这将删除它使用的缓存目录。
否则，它将删除系统默认的Lake缓存目录。
:::

```lakeCacheHelp services
Print configured remote cache services

USAGE:
  lake cache services

Prints the name of each configured remote cache services (one per line).
Additional services can be added by modifying the system Lake configuration.
The exact location of the this configuration file is system dependent and can
be set by `LAKE_CONFIG`, but it is usually located at `~/.lake/config.toml`.

The configuration of the system cache could look something like the following:

  cache.defaultService = "my-s3"
  cache.defaultUploadService = "my-s3"

  [[cache.service]]
  name = "my-s3"
  kind = "s3"
  artifactEndpoint = "https://my-s3.com/a0"
  revisionEndpoint = "https://my-s3.com/r0"

If no `cache.defaultService` is configured, Lake will use Reservoir by default.
```

::::lake cache services
打印每个配置的远程缓存服务的名称（每行一个）。
可以通过修改系统 Lake 配置文件来添加其他服务，该文件通常位于 `~/.lake/config.toml`，但可以通过 {envVar}`LAKE_CONFIG` 环境变量进行设置。

:::paragraph
系统缓存的配置可能如下所示：
```toml -link
cache.defaultService = "my-s3"
cache.defaultUploadService = "my-s3"

[[cache.service]]
name = "my-s3"
kind = "s3"
artifactEndpoint = "https://my-s3.com/a0"
revisionEndpoint = "https://my-s3.com/r0"
```
如果未配置 `cache.defaultService`，则 Lake 将默认使用 Reservoir。
:::
::::

```lakeCacheHelp stage
Copy build outputs from the cache to a staging directory

USAGE:
  lake cache stage <mappings> <staging-directory>

Creates the staging directory and copies the mappings file to it. Then, it
copies all artifacts described within the mappings file from the cache to the
staging directory. Errors if any of the artifacts described cannot be found in
the cache.
```

::::lake cache stage "mappings «staging-directory»"
创建 {lakeMeta}`staging-directory` 并将 {lakeMeta}`mappings` 文件复制到其中。
此后，它将映射文件中描述的所有工件从缓存复制到
暂存目录。
如果在缓存中找不到所描述的任何工件，则这是一个错误。
::::

```lakeCacheHelp unstage
Cache build outputs from a staging directory

USAGE:
  lake cache unstage <staging-directory>

Copies the mappings and artifacts stored in staging directory (e.g., via
`lake cache stage`) back into the cache.

Reads the mappings file located at `outputs.jsonl` within the staging
directory and writes the mappings to the Lake cache. Then, it copies the
described artifacts from the staging directory into the cache.
```

::::lake cache unstage "«staging-directory»"

将存储在 {lakeMeta}`staging-directory`（例如，通过 {lake}`cache stage`）中的映射和工件复制回缓存中。

读取暂存中位于 `outputs.jsonl` 的映射文件
目录并将映射写入 Lake 缓存。然后，它复制
将描述的工件从暂存目录放入缓存中。
::::


```lakeCacheHelp "put-stage"
Manage the Lake cache

USAGE:
  lake cache <COMMAND>

COMMANDS:
  get [<mappings>]      download build outputs into the local Lake cache
  put <mappings>        upload build outputs to a remote cache
  add <mappings>        add input-to-output mappings to the Lake cache
  clean                 removes ALL from the local Lake cache
  services              print configured remote cache services

STAGING COMMANDS:
  stage <map> <dir>     copy build outputs from the cache to a directory
  unstage <dir>         cache build outputs from a staging directory
  put-staged <dir>      upload build outputs from a staging directory

See `lake cache help <command>` for more information on a specific command.
```


# 配置文件
%%%
file := "Configuration-Files"
tag := "zh-buildtools-lake-cli-h016"
%%%


```lakeHelp "translate-config"
Translate a Lake configuration file into a different language

USAGE:
  lake translate-config <lang> [<out-file>]

Translates the loaded package's configuration into another of
Lake's supported configuration languages (i.e., either `lean` or `toml`).
The produced file is written to `out-file` or, if not provided, the path of
the configuration file with the new language's extension. If the output file
already exists, Lake will error.

Translation is lossy. It does not preserve comments or formatting and
non-declarative configuration will be discarded.
```

:::lake «translate-config» "lang [«out-file»]"
将加载的包的配置转换为 Lake 支持的另一种配置语言（即 `lean` 或 `toml`）。
生成的文件将写入 `out-file`，或者如果未提供，则写入具有新语言扩展名的配置文件的路径。
如果输出文件已存在，Lake 将出错。

翻译是有损的。
它不保留注释或格式，并且丢弃非声明性配置。
:::
