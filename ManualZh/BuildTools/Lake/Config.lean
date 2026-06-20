/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.Config.Monad
import Lake.DSL

import Manual.Meta
import ManualZh.BuildTools.Lake.CLI


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lake.DSL

#doc (Manual) "配置文件格式" =>
%%%
file := "Configuration-File-Format"
tag := "lake-config"
%%%

:::paragraph
Lake 为 {tech (key := "package configuration")}[包配置] 文件提供两种格式：

: TOML

  TOML 配置格式是完全声明性的。
  不包含自定义目标、构面或脚本的项目可以使用 TOML 格式。
  由于 TOML 解析器可用于多种语言，因此使用此格式有助于与非 Lean 编写的工具集成。

: Lean

  Lean 配置格式更加灵活，允许自定义目标、方面和脚本。
  它具有嵌入式特定于域的语言，用于描述 TOML 格式中提供的配置选项的声明性子集。
  此外，Lake API 可用于表达声明性选项可能性之外的构建配置。

命令 {lake}`translate-config` 可用于在两种格式之间自动转换。
:::

这两种格式都由 Lake 进行类似的处理，它以内部结构类型的形式从配置文件中提取 {tech (key := "package configuration")}[包配置]。
当包为 {tech (key := "configure package")}[已配置] 时，生成的数据结构将写入 {tech (key := "build directory")}[构建目录] 中的 `lakefile.olean`。


# 声明性 TOML 格式
%%%
file := "Declarative-TOML-Format"
tag := "lake-config-toml"
%%%


TOML{margin}[[_Tom 显而易见的最小语言_](https://toml.io/en/) 是配置文件的标准化格式。] 配置文件描述 Lake {tech (key := "package configuration")}[包配置] 文件最常用的声明性子集。
TOML 文件表示_tables_，它将键映射到值。
值可能由字符串、数字、值数组或其他表格组成。
由于 TOML 在文件结构方面具有相当大的灵活性，因此本参考文档记录了预期的值，而不是用于生成它们的特定语法。

{configFile}`lakefile.toml` 的内容应表示描述 Lean 包的 TOML 表。
此配置由描述整个包的标量字段以及包含其他表数组的以下字段组成：
 * `require`
 * `lean_lib`
 * `lean_exe`

目前，不属于此处描述的配置表一部分的字段将被忽略。
为了减少拼写错误的风险，这种情况将来可能会改变。
Lake 未使用的字段名称不应用于存储要由其他工具处理的元数据。


## 封装配置
%%%
file := "Package-Configuration"
tag := "zh-buildtools-lake-config-h002"
%%%

`lakefile.toml` 的顶级内容指定适用于包本身的选项，包括名称和版本等元数据、{tech (key := "workspace")}[工作空间]中文件的位置、用于所有 {tech (key := "targets")}[目标] 的编译器标志，以及
唯一的必填字段是 `name`，它声明包的名称。

:::::tomlTableDocs root "Package Configuration" Lake.PackageConfig (skip := backend) (skip := releaseRepo?) (skip := buildArchive?) (skip := manifestFile) (skip := moreServerArgs) (skip := dynlibs) (skip := plugins)

::::tomlFieldCategory "Metadata" name version versionTags description keywords homepage license licenseFiles readmeFile reservoir
这些选项描述了包。
[Reservoir](https://reservoir.lean-lang.org/) 使用它们来索引和显示包。
如果省略某个字段，Reservoir 可以使用包的 GitHub 存储库中的信息来填写详细信息。

:::tomlField Lake.PackageConfig name "The package name" "Package names" String
包的名称。
:::
::::

:::tomlFieldCategory "Layout" packagesDir srcDir buildDir leanLibDr nativeLibDir binDir irDir
这些选项控制包的顶级目录布局及其构建目录。
包内的库、可执行文件和目标指定的其他路径与这些目录相关。
:::

:::tomlFieldCategory "Building and Running" defaultTargets leanLibDir platformIndependent precompileModules moreServerOptions moreGlobalServerArgs buildType leanOptions moreLeanArgs weakLeanArgs moreLeancArgs weakLeancArgs moreLinkArgs weakLinkArgs extraDepTargets

这些选项配置代码在包中的构建和运行方式。
包中的库、可执行文件和其他 {tech (key := "targets")}[目标] 可以进一步添加到此配置的部分。

:::

:::tomlFieldCategory "Testing and Linting" testDriver testDriverArgs lintDriver lintDriverArgs builtinLint

CLI 命令 {lake}`test` 和 {lake}`lint` 使用由 {tech (key := "workspace")}[工作空间] 的 {tech (key := "root package")}[根包] 配置的定义来执行测试和 linting。
运行以执行测试和 linting 的代码称为测试或 lint 驱动程序。
在 Lean 配置文件中，可以通过将 `@[test_driver]` 或 `@[lint_driver]` 属性应用于 {tech (key := "Lake script")}[Lake 脚本] 或可执行文件或库目标来指定这些文件。
在 Lean 和 TOML 配置文件中，也可以通过设置这些选项来配置它们。
可以使用字符串 `"PKG/TGT"` 将依赖项 `PKG` 中的目标或脚本 `TGT` 指定为测试或 lint 驱动程序

:::

:::tomlFieldCategory "Cloud Releases" releaseRepo buildArchive preferReleaseBuild

这些选项定义包的云版本，如 {ref "lake-github"}[GitHub 版本版本] 部分中所述。

:::

:::tomlField Lake.PackageConfig defaultTargets "default targets' names (array)" "default targets' names (array)" String (sort := 2)

{includeDocstring Lake.Package.defaultTargets -elab}

:::

:::::

:::::example "Minimal TOML Package Configuration"
Lean {tech}[package] 的最小 TOML 配置仅设置包的名称，使用所有其他字段的默认值。
该软件包不包含 {tech}[targets]，因此无需构建代码。

::::lakeToml Lake.PackageConfig _root_
```toml
name = "example-package"
```
```expected
{wsIdx := 0,
  baseName := `«example-package»,
  keyName := `«example-package»,
  origName := `«example-package»,
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
  targetDecls := #[],
  targetDeclMap := {},
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := ""}
```
::::
:::::

:::::example "Library TOML Package Configuration"
Lean {tech}[package] 的最小 TOML 配置设置包的名称并定义库目标。
该库名为 `Sorting`，其模块预计位于 `Sorting.*` 层次结构下。
::::lakeToml Lake.PackageConfig _root_
```toml
name = "example-package"
defaultTargets = ["Sorting"]

[[lean_lib]]
name = "Sorting"
```
```expected
{wsIdx := 0,
  baseName := `«example-package»,
  keyName := `«example-package»,
  origName := `«example-package»,
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
          {pkg := `«example-package»,
            name := `Sorting,
            kind := `lean_lib,
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
                roots := #[`Sorting],
                globs := #[Lake.Glob.one `Sorting],
                libName := "",
                libPrefixOnWindows := false,
                needs := #[],
                extraDepTargets := #[],
                precompileModules := false,
                defaultFacets := #[`lean_lib.leanArts],
                nativeFacets := #<fun>,
                allowImportAll := false},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`Sorting ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«example-package»,
                  name := `Sorting,
                  kind := `lean_lib,
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
                      roots := #[`Sorting],
                      globs := #[Lake.Glob.one `Sorting],
                      libName := "",
                      libPrefixOnWindows := false,
                      needs := #[],
                      extraDepTargets := #[],
                      precompileModules := false,
                      defaultFacets := #[`lean_lib.leanArts],
                      nativeFacets := #<fun>,
                      allowImportAll := false},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[`Sorting],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := ""}
```
::::
:::::

## 依赖关系
%%%
file := "Dependencies"
tag := "zh-buildtools-lake-config-h003"
%%%

依赖关系在包配置的 {toml}`[[require]]` 字段数组中指定，该数组指定每个包的名称和源。
来源有以下三种：
 * [Reservoir](https://reservoir.lean-lang.org/)，或替代包注册表
 * Git 存储库，可能是本地路径或 URL
 * 本地路径

::::tomlTableDocs "require" "Requiring Packages" Lake.Dependency (skip := src?) (skip := opts) (skip := subdir) (skip := version?)

{tomlField Lake.Dependency}`path` 和 {tomlField Lake.Dependency}`git` 字段指定依赖项的显式源。
如果两者均未提供，则从 [Reservoir](https://reservoir.lean-lang.org/) 或备用注册表（如果已配置）中获取依赖项。
从 Reservoir 获取包时需要 {tomlField Lake.Dependency}`scope` 字段。

:::tomlField Lake.Dependency path "Path" "Paths" System.FilePath
对本地文件系统的依赖，由其路径指定。
:::

:::tomlField Lake.Dependency git "Git specification" "Git specifications" Lake.DependencySrc
Git 存储库中的依赖项，通过其 URL 作为字符串或通过带有键的表指定：
 * `url`：存储库 URL
 * `subDir`：包含包源代码的 Git 存储库的子目录
:::

:::tomlField Lake.Dependency rev "Git revision" "Git revisions" String
对于 Git 或 Reservoir 依赖项，此字段指定 Git 修订版本，可以是分支名称、标签名称或特定哈希。
在 Reservoir 上，`version` 字段优先于该字段。
:::

:::tomlField Lake.Dependency source "Package Source" "Package Sources" Lake.DependencySrc
依赖项源，指定为独立表，当 `git` 和 `path` 密钥都不存在时使用。
密钥 `type` 应该是字符串 `"git"` 或字符串 `"path"`。
如果类型为 `"path"`，则必须还有另一个键 `"path"`，其值是提供包在磁盘上的位置的字符串。
如果类型为 `"git"`，则应存在以下键：
 * `url`：存储库 URL
 * `rev`：Git 修订版，可以是分支名称、标签名称或特定哈希（可选）
 * `subDir`：包含包源代码的 Git 存储库的子目录
:::

:::tomlField Lake.Dependency version "version as string" "versions as strings" String

{includeDocstring Lake.Dependency.version?}

:::

::::

:::::example "Requiring Packages from Reservoir"
使用此 TOML 配置，可以从 Reservoir 获取软件包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
version = "2.12"
scope = "exampleDev"
```
```expected
#[{name := `example, scope := "exampleDev", version? := some "2.12", src? := none, opts := {}}]
```
::::
:::::

:::::example "Requiring Packages from Git"
可以使用以下 TOML 配置从 Git 存储库中获取包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
git = "https://git.example.com/example.git"
rev = "main"
version = "2.12"
```
```expected
#[{name := `example,
    scope := "",
    version? := some "2.12",
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "main") none),
    opts := {}}]
```
::::

特别是，将从 `main` 分支检出软件包，并且软件包的 {tech (key := "package configuration")}[configuration] 中指定的版本号应与 `2.12` 匹配。
:::::

:::::example "Requiring Packages from a Git tag"
使用此 TOML 配置，可以从 Git 存储库中的标签 `v2.12` 获取包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
git = "https://git.example.com/example.git"
rev = "v2.12"
```
```expected
#[{name := `example,
    scope := "",
    version? := none,
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "v2.12") none),
    opts := {}}]
```
::::
未使用包的 {tech (key := "package configuration")}[configuration] 中指定的版本号。
:::::

:::::example "Requiring Reservoir Packages from a Git tag"
使用 Reservoir 找到的包 `example` 可以使用以下 TOML 配置从其 Git 存储库中的标签 `v2.12` 获取：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
rev = "v2.12"
scope = "exampleDev"
```
```expected
#[{name := `example, scope := "exampleDev", version? := some "git#v2.12", src? := none, opts := {}}]
```
::::
未使用包的 {tech (key := "package configuration")}[configuration] 中指定的版本号。
:::::

:::::example "Requiring Packages from Paths"
使用此 TOML 配置，可以从本地路径 `../example` 获取包 `example`：
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
path = "../example"
```
```expected
#[{name := `example,
    scope := "",
    version? := none,
    src? := some (Lake.DependencySrc.path (FilePath.mk "../example")),
    opts := {}}]
```
::::
当在单个存储库中开发多个包时，或者在测试对依赖项的更改是否修复了下游包中的错误时，对本地路径的依赖关系非常有用。
:::::

:::::example "Sources as Tables"
包来源的信息可以写在一个显式的表中。
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
source = {type = "git", url = "https://example.com/example.git"}
```
```expected
#[{name := `example,
    scope := "",
    version? := none,
    src? := some (Lake.DependencySrc.git "https://example.com/example.git" none none),
    opts := {}}]
```
::::
:::::

## 库目标
%%%
file := "Library-Targets"
tag := "zh-buildtools-lake-config-h004"
%%%

库目标预计位于 `lean_lib` 表数组中。

::::tomlTableDocs "lean_lib" "Library Targets" Lake.LeanLibConfig (skip := backend) (skip := globs) (skip := nativeFacets)
:::tomlField Lake.LeanLibConfig name "The library name" "Library names" String
库的名称，通常与其单个模块根相同。
:::

::::

:::::example "Minimal Library Target"
该库声明仅提供一个名称：
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
```
```expected
#[{ name := TacticTools,
    val := {toLeanConfig :=
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
      roots := #[`TacticTools],
      globs := #[Lake.Glob.one `TacticTools],
      libName := "",
      libPrefixOnWindows := false,
      needs := #[],
      extraDepTargets := #[],
      precompileModules := false,
      defaultFacets := #[`lean_lib.leanArts],
      nativeFacets := #<fun>,
      allowImportAll := false}}]
```
::::
该库的源代码位于包的默认源目录中，位于以 `TacticTools` 为根的模块层次结构中。
:::::

:::::example "Configured Library Target"
该库声明提供了更多选项：
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
srcDir = "src"
precompileModules = true
```
```expected
#[{ name := TacticTools,
    val := {toLeanConfig :=
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
      srcDir := FilePath.mk "src",
      roots := #[`TacticTools],
      globs := #[Lake.Glob.one `TacticTools],
      libName := "",
      libPrefixOnWindows := false,
      needs := #[],
      extraDepTargets := #[],
      precompileModules := true,
      defaultFacets := #[`lean_lib.leanArts],
      nativeFacets := #<fun>,
      allowImportAll := false}}]
```
::::
该库的源代码位于目录 `src` 中，位于以 `TacticTools` 为根的模块层次结构中。
如果在精化时间访问其模块，它们将被编译为本机代码并链接，而不是在解释器中运行。
:::::

## 可执行目标
%%%
file := "Executable-Targets"
tag := "zh-buildtools-lake-config-h005"
%%%

:::: tomlTableDocs "lean_exe" "Executable Targets" Lake.LeanExeConfig (skip := backend) (skip := globs) (skip := nativeFacets)
:::tomlField Lake.LeanExeConfig name "The executable's name" "Executable names" String
可执行文件的名称。
:::

::::

:::::example "Minimal Executable Target"
此可执行声明仅提供一个名称：
::::lakeToml Lake.LeanExeConfig lean_exe
```toml
[[lean_exe]]
name = "trustworthytool"
```
```expected
#[{ name := trustworthytool,
    val := {toLeanConfig :=
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
      root := `trustworthytool,
      exeName := "trustworthytool",
      needs := #[],
      extraDepTargets := #[],
      supportInterpreter := false,
      nativeFacets := #<fun>}}]
```
::::

```lean -show
def main : List String → IO UInt32 := fun _ => pure 0
```

可执行文件的 {lean}`main` 函数应位于包的默认源文件路径中名为 `trustworthytool.lean` 的模块中。
生成的可执行文件名为 `trustworthytool`。
:::::

:::::example "Configured Executable Target"
由于破折号 (`-`)，名称 `trustworthy-tool` 不是有效的 Lean 名称。
要将此名称用于可执行目标，必须提供显式模块根。
尽管 `trustworthy-tool` 是可执行文件的完全可接受的名称，但目标还指定编译和链接的结果应命名为 `tt`。

::::lakeToml Lake.LeanExeConfig lean_exe
```toml
[[lean_exe]]
name = "trustworthy-tool"
root = "TrustworthyTool"
exeName = "tt"
```
```expected
#[{ name := «trustworthy-tool»,
    val := {toLeanConfig :=
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
      root := `TrustworthyTool,
      exeName := "tt",
      needs := #[],
      extraDepTargets := #[],
      supportInterpreter := false,
      nativeFacets := #<fun>}}]
```
::::

```lean -show
def main : List String → IO UInt32 := fun _ => pure 0
```

可执行文件的 {lean}`main` 函数应位于包的默认源文件路径中名为 `TrustworthyTool.lean` 的模块中。
:::::

# Lean 格式
%%%
file := "Lean-Format"
tag := "lake-config-lean"
%%%


Lake {tech (key := "package configuration")}[包配置] 文件的 Lean 格式为 TOML 格式中支持的声明性功能提供域特定语言。
此外，它还提供了编写 Lean 代码的能力，以实现任何无法以声明方式表达的必要构建逻辑。
Lean 配置文件名为 {configFile}`lakefile.lean`。

由于 Lean 格式是 Lean 源文件，因此可以使用 Lean 语言服务器的所有功能对其进行编辑。
此外，Lean 的元编程框架允许使用精化时间副作用来实现当前平台上有条件的配置步骤等功能。
然而，Lean 配置格式是 Lean 文件的结果是，使用本身不是在 Lean 中编写的工具来处理此类文件是不可行的。

```lean -show
section
open Lake DSL
open Lean (NameMap)
```

## 声明字段
%%%
file := "Declarative-Fields"
tag := "zh-buildtools-lake-config-h007"
%%%

Lean 配置格式的声明性子集使用声明字段序列来指定配置选项。

:::syntax Lake.DSL.declField (title := "Declarative Fields") -open

{includeDocstring Lake.DSL.declField}

```grammar
$_ := $_
```
:::

## 套餐
%%%
file := "Packages"
tag := "zh-buildtools-lake-config-h008"
%%%
::::syntax command (title := "Package Configuration")
```grammar
$[$_:docComment]?
$[@[ $_,* ]]?
package $name:identOrStr
```

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package $name where
  $item*
```

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```

每个 Lake 配置文件只能有一个 {keywordOf Lake.DSL.packageCommand}`package` 声明。
定义的封装配置将作为 `_package` 可供参考。

::::

::::syntax command (title := "Post-Update Hooks")
```grammar
post_update $[$name]? $v
```

{includeDocstring Lake.DSL.postUpdateDecl}

::::


## 依赖关系
%%%
file := "Dependencies"
tag := "zh-buildtools-lake-config-h009"
%%%

使用 {keywordOf Lake.DSL.requireDecl}`require` 声明指定依赖关系。

:::syntax command (title := "Requiring Packages")
```grammar
$doc:docComment
require $name:depName $[@ $[git]? $_:term]? $[$_:fromClause]? $[with $_:term]?
```

`@` 子句指定包版本，在需要 [Reservoir](https://reservoir.lean-lang.org/) 中的包时使用。
版本可以是指定包的 {name Lake.PackageConfig.version}`version` 字段中声明的版本的字符串，也可以是特定的 Git 修订版。
Git 修订版可以是分支名称、标签名称或提交哈希值。

可选的 {syntaxKind}`fromClause` 指定除 Reservoir 之外的包源，它可以是 Git 存储库或本地路径。

{keywordOf Lake.DSL.requireDecl}`with` 子句指定将用于配置依赖性的 Lake 选项的 {lean}`NameMap String`。
这相当于在命令行上构建依赖项时将 {lakeOpt}`-K` 选项传递给 {lake}`build`。
:::

:::syntax fromClause -open (title := "Package Sources")

{includeDocstring Lake.DSL.fromClause}

```grammar
from $t:term
```

```grammar
from git $t $[@ $t]? $[/ $t]?
```

:::


## 目标
%%%
file := "Targets"
tag := "zh-buildtools-lake-config-h010"
%%%



{tech (key := "Targets")}[目标] 通常通过应用 `default_target` 属性而不是显式列出它们来添加到默认目标集中。
:::TODO
修复上面的 `default_target` — 它不适用于 CI，但可以在本地使用 `attr` 角色。
:::

:::syntax attr (title := "Specifying Default Targets") (label := "attribute") (namespace := Lake.DSL)

```grammar
default_target
```
将目标标记为默认目标，在未指定其他目标时构建。
:::

### 图书馆
%%%
file := "Libraries"
tag := "zh-buildtools-lake-config-h011"
%%%


:::syntax command (title := "Library Targets")

要定义一个库，其中所有可配置字段都具有默认值，请使用 {keywordOf Lake.DSL.leanLibCommand}`lean_lib`，不带其他字段。

```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr
```

可以通过提供新值来修改默认配置。

```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr where
  $field*
```


```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

{keywordOf Lake.DSL.leanLibCommand}`lean_lib` 的字段是 {name Lake.LeanLibConfig}`LeanLibConfig` 结构的字段。

{docstring Lake.LeanLibConfig}

### 可执行文件
%%%
file := "Executables"
tag := "zh-buildtools-lake-config-h012"
%%%

:::syntax command (title := "Executable Targets")

要定义其中所有可配置字段均具有默认值的可执行文件，请使用不带其他字段的 {keywordOf Lake.DSL.leanExeCommand}`lean_exe`。

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr
```

可以通过提供新值来修改默认配置。

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr where
  $field*
```

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

{keywordOf Lake.DSL.leanExeCommand}`lean_exe` 的字段是 {name Lake.LeanExeConfig}`LeanExeConfig` 结构的字段。

{docstring Lake.LeanExeConfig}

### 外部库
%%%
file := "External-Libraries"
tag := "zh-buildtools-lake-config-h013"
%%%

由于外部库可以用任何语言编写并且需要任意构建步骤，因此它们被定义为用 {name Lake.FetchM}`FetchM` monad 编写的程序，生成 {name Lake.Job}`Job`。
外部库目标应该生成一个构建作业来执行构建，然后返回生成的静态库的位置。
为了使外部库在 {name Lake.PackageConfig.precompileModules}`precompileModules` 打开时正确链接，{keyword}`extern_lib` 目标生成的静态库必须遵循平台的库命名约定（即，在 Windows 上命名为 foo.a，在类 Unix 系统上命名为 libfoo.a）。
实用程序函数 {name}`Lake.nameToStaticLib` 将库名称转换为当前平台的正确文件名。

:::syntax command (title := "External Library Targets")

```grammar
$[$_:docComment]?
$[$_:attributes]?
extern_lib $_:identOrStr $_? := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.externLibCommand}

:::

### 自定义目标
%%%
file := "Custom-Targets"
tag := "zh-buildtools-lake-config-h014"
%%%

自定义目标可用于使用 Lake API 定义任何增量构建的工件。

:::syntax command (title := "Custom Targets")

```grammar
$[$_:docComment]?
$[$_:attributes]?
target $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.externLibCommand}

:::

### 自定义方面
%%%
file := "Custom-Facets"
tag := "zh-buildtools-lake-config-h015"
%%%

自定义方面允许从模块、库或包增量构建其他工件。


:::syntax command (title := "Custom Package Facets")

包方面允许从整个包生成一个工件或一组工件。
Lake API 可以查询包的库；因此，包构面的一个常见用途是构建每个库的给定构面。

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.packageFacetDecl}

:::

:::syntax command (title := "Custom Library Facets")

库方面允许从库中生成一个工件或一组工件。
Lake API 可以查询库的模块；因此，库构面的一个常见用途是构建每个模块的给定构面。

```grammar
$[$_:docComment]?
$[@[$_,*]]?
library_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.libraryFacetDecl}

:::

:::syntax command (title := "Custom Module Facets")

模块方面允许从模块生成一个工件或一组工件，通常通过调用命令行工具来实现。

```grammar
$[$_:docComment]?
$[@[$_,*]]?
module_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.moduleFacetDecl}

:::

## 配置值类型
%%%
file := "Configuration-Value-Types"
tag := "zh-buildtools-lake-config-h016"
%%%

{docstring Lake.BuildType}

在 Lake 的 DSL 中，{deftech}_globs_ 是匹配模块名称集的模式。
存在从名称到与所讨论的名称匹配的全局变量的强制，并且有两个后缀运算符用于构造更多全局变量。

```lean -show
section
example : Lake.Glob := `n

/-- info: instCoeNameGlob -/
#check_msgs in
#synth Coe Lean.Name Lake.Glob

open Lake DSL

/-- info: Lake.Glob.andSubmodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.*

/-- info: Lake.Glob.submodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.+

end
```
:::freeSyntax term (title := "Glob Syntax")

glob 模式 `N.*` 与 `N` 或以 `N` 为前缀的任何子模块匹配。

```grammar
$_:name".*"
```

全局模式 `N.+` 与任何以 `N` 为严格前缀的子模块匹配，但不与 `N` 本身匹配。

```grammar
$_:name".+"
```

名称和 `.*` 或 `.+` 之间不允许有空格。

:::

{docstring Lake.Glob}



{docstring Lake.LeanOption}

{docstring Lake.Backend}

## 脚本
%%%
file := "Scripts"
tag := "zh-buildtools-lake-config-h017"
%%%

Lake 脚本用于自动执行需要访问包配置但不参与代码工件增量构建的任务。
脚本在 {name Lake.ScriptM}`ScriptM` monad 中运行，即 {name}`IO` 以及附加的 {tech}[reader monad] {tech (key := "monad transformer")}[transformer]，提供对包配置的访问。
特别是，脚本的类型应为 {lean}`List String → ScriptM UInt32`。
脚本中的工作空间信息主要通过 {inst}`MonadWorkspace ScriptM` 实例访问。


```lean -show
example : ScriptFn = (List String → ScriptM UInt32) := rfl
```

:::syntax command (title := "Script Declarations")
```grammar
$[$_:docComment]?
$[@[$_,*]]?
script $_:identOrStr $_? :=
  $_:term
$[where
  $_*]?
```

{includeDocstring Lake.DSL.scriptDecl}

:::

{docstring Lake.ScriptM}


:::syntax attr (label := "attribute") (title := "Default Scripts")
```grammar
default_script
```

将 {tech (key := "Lake script")}[Lake 脚本] 标记为 {tech}[package] 的默认值。

:::



## 公用事业
%%%
file := "Utilities"
tag := "zh-buildtools-lake-config-h018"
%%%

:::syntax term (title := "The Current Directory")
```grammar
__dir__
```

{includeDocstring Lake.DSL.dirConst}

:::

:::syntax term (title := "Configuration Options")
```grammar
get_config? $t
```

{includeDocstring Lake.DSL.getConfig}

:::

:::syntax command (title := "Compile-Time Conditionals")

```grammar
meta if $_ then
  $_
$[else $_]?
```

{includeDocstring Lake.DSL.metaIf}

:::

:::syntax cmdDo (title := "Command Sequences")

```grammar
  $_:command
```

```grammar
do
  $_:command
  $[$_:command]*
```

{includeDocstring Lake.DSL.cmdDo}

:::

:::syntax term (title := "Compile-Time Side Effects")
```grammar
run_io $t
```

{includeDocstring Lake.DSL.runIO}

:::
