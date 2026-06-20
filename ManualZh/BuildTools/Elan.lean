/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Meta.ElanCheck
import Manual.Meta.ElanCmd
import Manual.Meta.ElanOpt

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "使用Elan管理工具链" =>
%%%
tag := "elan"
shortContextTitle := "Elan"
%%%

Elan 是 Lean 工具链经理。
它负责安装 {tech (key := "toolchains")}[工具链] 并运行其组成程序。
Elan 可以无缝地处理各种项目，每个项目都设计为使用特定版本的 Lean 构建，而无需手动安装和选择工具链版本。
每个项目通常配置为使用特定版本，该版本根据需要透明安装，并自动跟踪对 Lean 版本的更改。

# 选择工具链
%%%
tag := "elan-toolchain-versions"
%%%

使用Elan时，{envVar}`PATH`上每个工具的版本是调用正确版本的代理。
代理确定当前上下文的适当工具链版本，确保其已安装，然后调用适当工具链安装中的底层工具。
可以通过将特定版本作为前缀为 `+` 的参数传递来指示这些代理使用特定版本，以便 `lake +4.0.0` 在安装后调用 `lake` 版本 `4.0.0`（如有必要）。


## 工具链标识符
%%%
tag := "elan-channels"
%%%

工具链是通过提供工具链标识符来指定的，该标识符可以是 {deftech}_channel_（标识特定类型的 Lean 版本），也可以选择来源，也可以是由 {elan}`toolchain link` 建立的 {deftech (key := "custom toolchain name")}_自定义工具链名称_。
渠道可能是：

 : `stable`

  最新稳定版 Lean 版本。 Elan 自动跟踪稳定版本，并在新版本发布时提供升级。

 : `beta`

  最新的候选版本。候选版本是 Lean 的构建，旨在成为下一个稳定版本。它们可用于广泛的用户测试。

 : `nightly`

   最新的夜间构建。每晚构建对于试验新的 Lean 功能以向开发人员提供反馈非常有用。

 : 版本号或特定的夜间版本

    每个 Lean 版本号标识仅包含该版本的通道。
    版本号可以选择在前面加上 `v`，因此 `v4.17.0` 和 `4.17.0` 是等效的。
    同样，`nightly-YYYY-MM-DD` 指定从指定日期起每晚发布。
    项目的 {tech (key := "toolchain file")}[工具链文件] 通常应包含 Lean 的特定版本，而不是通用通道，以便更轻松地在开发人员之间进行协调以及构建和测试项目的旧版本。
    维护 Lean 版本和夜间构建的存档。

 : 自定义本地工具链

    命令 {elan}`toolchain link` 可用于在 Elan 中为 Lean 的本地构建建立自定义工具链名称。
    这在处理 Lean 编译器本身时特别有用。

指定 {deftech}_origin_ 指示 Elan 从特定源安装 Lean 工具链。
默认情况下，这是 GitHub 上的官方项目存储库，标识为 [`leanprover/lean4`](https://github.com/leanprover/lean4/releases)。
如果指定，则原点应在通道之前并带有冒号，因此 `stable` 相当于 `leanprover/lean4:stable`。
安装夜间版本时，`-nightly` 会附加到源，因此 `leanprover/lean4:nightly-2025-03-25` 会查阅 [`leanprover/lean4-nightly`](https://github.com/leanprover/lean4-nightly/releases) 存储库来下载版本。
起源不用于自定义工具链名称。

## 确定当前工具链
%%%
tag := "elan-toolchain-config"
%%%

Elan 将工具链与目录关联起来，并使用当前工作目录的最新父目录的工具链，该目录已配置工具链。
目录的工具链可能来自工具链文件或使用 {ref "elan-override"}[`elan override`] 配置的覆盖。

当前工具链的确定方法是：首先搜索当前目录的已配置工具链，遍历父目录，直到找到工具链版本或不再有父目录。
如果目录已配置 {tech (key := "toolchain override")}[工具链覆盖] 或者包含 `lean-toolchain` 文件，则目录具有已配置的工具链。
最近的父级优先于其祖先，如果目录同时具有覆盖和工具链文件，则覆盖优先。
如果未找到目录工具链，则使用 Elan 配置的 {deftech}_default toolchain_ 作为后备。

配置 Lean 工具链的最常见方法是使用 {deftech}_toolchain file_。
工具链文件是一个名为 `lean-toolchain` 的文本文件，其中包含带有有效 {ref "elan-channels"}[工具链标识符] 的单行。
该文件通常位于项目的根目录中，并通过代码签入版本控制，以确保参与该项目的每个人都使用相同的版本。
更新到新的 Lean 工具链只需编辑此文件，新版本会在下次打开或构建 Lean 文件时自动下载并运行。

在某些需要更大灵活性的高级用例中，可以配置 {deftech}_toolchain override_。
与工具链文件一样，覆盖将工具链版本与目录及其子目录相关联。
与工具链文件不同，覆盖存储在 Elan 的配置中而不是本地文件中。
它们通常在需要特定的本地配置且对其他开发人员来说没有意义时使用，例如使用本地构建的 Lean 编译器测试项目。

# 工具链位置
%%%
tag := "elan-dir"
%%%

默认情况下，Elan 将安装的工具链存储在用户主目录的 `.elan/toolchains` 中，其代理保存在 `.elan/bin` 中，该代理在安装 Elan 时添加到路径中。
环境变量 {envVar +def}`ELAN_HOME` 可用于更改此位置。
应在安装 Elan 之前和使用 Lean 的所有会话中进行设置，以确保找到 Elan 的文件。

# 命令行界面
%%%
tag := "elan-cli"
%%%

除了自动选择、安装和调用正确版本的 Lean 工具的代理之外，Elan 还提供命令行界面来查询和配置其设置。
该工具称为 `elan`。
与 {ref "lake"}[Lake] 一样，其命令行界面也是围绕子命令构建的。

可以使用以下标志调用 Elan：

 : {elanOptDef flag}`--help` 或 {elanOptDef flag}`-h`

  详细描述当前子命令。

 : {elanOptDef flag}`--verbose` 或 {elanOptDef flag}`-v`

  启用详细输出。

 : {elanOptDef flag}`--version` 或 {elanOptDef flag}`-V`

  显示 Elan 版本。



```elanHelp
The Lean toolchain installer

USAGE:
    elan [FLAGS] <SUBCOMMAND>

FLAGS:
    -v, --verbose    Enable verbose output
    -h, --help       Prints help information
    -V, --version    Prints version information

SUBCOMMANDS:
    show           Show the active and installed toolchains
    default        Set the default toolchain
    toolchain      Modify or query the installed toolchains
    override       Modify directory toolchain overrides
    run            Run a command with an environment configured for a given toolchain
    which          Display which binary will be run for a given command
    self           Modify the elan installation
    completions    Generate completion scripts for your shell
    help           Prints this message or the help of the given subcommand(s)

DISCUSSION:
    elan manages your installations of the Lean theorem prover.
    It places `lean` and `lake` binaries in your `PATH` that automatically
    select and, if necessary, download the Lean version described in your
    project's `lean-toolchain` file. You can also install, select, run,
    and uninstall Lean versions manually using the commands of the `elan`
    executable.
```

## 查询工具链
%%%
tag := "elan-show"
%%%

{elan}`show` 命令显示当前工具链（由当前目录确定）并列出所有已安装的工具链。


```elanHelp "show"
elan-show
Show the active and installed toolchains

USAGE:
    elan show

FLAGS:
    -h, --help    Prints help information

DISCUSSION:
    Shows the name of the active toolchain and the version of `lean`.

    If there are multiple toolchains installed then all installed
    toolchains are listed as well.
```

:::elan show
显示活动工具链的名称和 `lean` 的版本。

如果安装了多个工具链，则会列出它们。
:::

以下是具有 `lean-toolchain` 文件的项目中 {elan}`show` 的典型输出：
```
installed toolchains
--------------------

leanprover/lean4:nightly-2025-03-25
leanprover/lean4:v4.17.0  (resolved from default 'stable')
leanprover/lean4:v4.16.0
leanprover/lean4:v4.9.0

active toolchain
----------------

leanprover/lean4:v4.9.0 (overridden by '/PATH/TO/PROJECT/lean-toolchain')
Lean (version 4.9.0, arm64-apple-darwin23.5.0, commit 8f9843a4a5fe, Release)
```
`installed toolchains` 部分列出了系统上当前可用的所有工具链。
`active toolchain` 部分标识当前工具链并描述如何选择它。
在本例中，由于 `lean-toolchain` 文件而选择了工具链。


## 设置默认工具链
%%%
tag := "elan-default"
%%%

Elan 的配置文件指定当当前目录没有 `lean-toolchain` 文件或 {tech (key := "default toolchain")}[工具链覆盖] 时要使用的 {tech (key := "toolchain override")}[默认工具链]。
通常使用 {elan}`default` 命令更改此值，而不是手动编辑文件。

```elanHelp "default"
elan-default
Set the default toolchain

USAGE:
    elan default <toolchain>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see `elan
                   help toolchain`

DISCUSSION:
    Sets the default toolchain to the one specified.
```

:::elan default "toolchain"
将默认工具链设置为 {elanMeta}`toolchain`，它应该是 {ref "elan-channels"}[有效工具链标识符]，例如 `stable`、`nightly` 或 `4.17.0`。
:::

## 管理已安装的工具链
%%%
tag := "elan-toolchain"
%%%

`elan toolchain` 系列子命令用于管理已安装的工具链。
工具链存储在Elan的{ref "elan-dir"}[工具链目录]中。

安装的工具链可能会占用大量磁盘空间。
Elan 跟踪调用它的 Lean 项目，并保存列表。
此项目列表可用于确定哪些工具链正在使用中，并使用 {elan}`toolchain gc` 自动删除未使用的工具链版本。

```elanHelp "toolchain"
elan-toolchain
Modify or query the installed toolchains

USAGE:
    elan toolchain <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    list         List installed toolchains
    install      Install a given toolchain
    uninstall    Uninstall a toolchain
    link         Create a custom toolchain by symlinking to a directory
    gc           Garbage-collect toolchains not used by any known project
    help         Prints this message or the help of the given subcommand(s)

DISCUSSION:
    Many `elan` commands deal with *toolchains*, a single
    installation of the Lean theorem prover. `elan` supports multiple
    types of toolchains. The most basic track the official release
    channels: 'stable', 'beta', and 'nightly'; but `elan` can also
    install toolchains from the official archives and from local builds.

    Standard release channel toolchain names have the following form:

        [<origin>:]<channel>[-<date>]

        <channel>       = stable|beta|nightly|<version>
        <date>          = YYYY-MM-DD

    'channel' is either a named release channel or an explicit version
    number, such as '4.0.0'. Channel names can be optionally appended
    with an archive date, as in 'nightly-2023-06-27', in which case
    the toolchain is downloaded from the archive for that date.
    'origin' can be used to refer to custom forks of Lean on Github;
    the default is 'leanprover/lean4'. For nightly versions, '-nightly'
    is appended to the value of 'origin'.

    elan can also manage symlinked local toolchain builds, which are
    often used to for developing Lean itself. For more information see
    `elan toolchain help link`.
```

```elanHelp "toolchain" "list"
elan-toolchain-list
List installed toolchains

USAGE:
    elan toolchain list

FLAGS:
    -h, --help    Prints help information
```

:::elan toolchain list
列出当前安装的工具链。这是 {elan}`show` 输出的子集。
:::

```elanHelp "toolchain" "install"
elan-toolchain-install
Install a given toolchain

USAGE:
    elan toolchain install <toolchain>...

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>...    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see
                      `elan help toolchain`
```

:::elan toolchain install "toolchain"
安装指示的 {elanMeta}`toolchain`。
工具链的名称应为 {ref "elan-channels"}[适合包含在 `lean-toolchain` 文件中的标识符]。
:::


```elanHelp "toolchain" "uninstall"
elan-toolchain-uninstall
Uninstall a toolchain

USAGE:
    elan toolchain uninstall <toolchain>...

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>...    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see
                      `elan help toolchain`
```

:::elan toolchain uninstall "toolchain"
卸载指示的 {elanMeta}`toolchain`。
工具链的名称应该是已安装工具链的名称。
使用 {elan}`toolchain list` 查看已安装的工具链及其名称。
:::

```elanHelp "toolchain" "link"
elan-toolchain-link
Create a custom toolchain by symlinking to a directory

USAGE:
    elan toolchain link <toolchain> <path>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <toolchain>    Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see `elan
                   help toolchain`
    <path>

DISCUSSION:
    'toolchain' is the custom name to be assigned to the new toolchain.

    'path' specifies the directory where the binaries and libraries for
    the custom toolchain can be found. For example, when used for
    development of Lean itself, toolchains can be linked directly out of
    the Lean root directory. After building, you can test out different
    compiler versions as follows:

        $ elan toolchain link master <path/to/lean/root>
        $ elan override set master

    If you now compile a package in the current directory, the custom
    toolchain 'master' will be used.
```


:::elan toolchain link "«local-name» path"

使用 {elanMeta}`path` 中找到的 Lean 工具链创建一个名为 {elanMeta}`local-name` 的新本地工具链。

:::


```elanHelp "toolchain" "gc"
elan-toolchain-gc
Garbage-collect toolchains not used by any known project

USAGE:
    elan toolchain gc [FLAGS]

FLAGS:
        --delete    Delete collected toolchains instead of only reporting them
    -h, --help      Prints help information
        --json      Format output as JSON

DISCUSSION:
    Experimental. A toolchain is classified as 'in use' if
    * it is the default toolchain,
    * it is registered as an override, or
    * there is a directory with a `lean-toolchain` file referencing the
      toolchain and elan has been used in the directory before.

    For safety reasons, the command currently requires passing `--delete`
    to actually remove toolchains but this may be relaxed in the future
    when the implementation is deemed stable.
```

:::elan toolchain gc "[\"--delete\"] [\"--json\"]"

该命令仍被认为是实验性的。

确定哪些已安装的工具链正在使用，并提出删除那些未使用的工具链。
列出了所有已安装的工具链，分为正在使用的工具链和未使用的工具链。

如果满足以下条件，工具链将被归类为“正在使用”：
 * 它是默认的工具链，
 * 它被注册为覆盖，或者
 * 有一个目录，其中包含引用工具链的 `lean-toolchain` 文件，并且 elan 之前已在该目录中使用过。

出于安全原因，{elan}`toolchain gc` 实际上不会删除任何工具链，除非传递了 {elanOptDef flag}`--delete` 标志。
当未来认为实施足够成熟时，这一点可能会放宽。
{elanOptDef flag}`--json` 标志导致 {elan}`toolchain gc` 以适合其他工具的 JSON 格式发出已使用和未使用的工具链列表。
:::

## 管理目录覆盖
%%%
tag := "elan-override"
%%%

特定于目录的 {tech (key := "toolchain overrides")}[工具链覆盖] 是优先于 `lean-toolchain` 文件的本地配置。
`elan override` 命令管理覆盖。

```elanHelp "override"
elan-override
Modify directory toolchain overrides

USAGE:
    elan override <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    list     List directory toolchain overrides
    set      Set the override toolchain for a directory
    unset    Remove the override toolchain for a directory
    help     Prints this message or the help of the given subcommand(s)

DISCUSSION:
    Overrides configure elan to use a specific toolchain when
    running in a specific directory.

    elan will automatically select the Lean toolchain specified in
    the `lean-toolchain` file when inside a Lean package, but
    directories can also be assigned their own Lean toolchain manually
    with `elan override`. When a directory has an override then any
    time `lean` or `lake` is run inside that directory, or one of
    its child directories, the override toolchain will be invoked.

    To pin to a specific nightly:

        $ elan override set nightly-2023-09-06

    Or a specific stable release:

        $ elan override set 4.0.0

    To see the active toolchain use `elan show`. To remove the
    override and use the default toolchain again, `elan override
    unset`.
```



:::elan override list
在两列中列出所有当前配置的目录覆盖。
左列包含 Lean 版本被覆盖的目录，右列列出了工具链版本。
:::


:::elan override set "toolchain"
将 {elanMeta}`toolchain` 设置为当前目录的覆盖。
:::




:::elan override unset "[\"--nonexistent\"] [\"--path\" path]"
如果提供了 {elanOptDef flag}`--nonexistent` 标志，则删除为当前不存在的目录配置的所有覆盖。
如果提供了 {elanOptDef option}`--path`，则删除为 {elanMeta}`path` 设置的覆盖。
否则，当前目录的覆盖将被删除。
:::

## 运行工具和命令
%%%
tag := "elan-run"
%%%

本节中的命令提供了在特定工具链中运行命令以及从磁盘上的特定工具链中查找工具的能力。
这在尝试不同的 Lean 版本、跨版本测试以及将 Elan 与其他工具集成时非常有用。

```elanHelp "run"
elan-run
Run a command with an environment configured for a given toolchain

USAGE:
    elan run [FLAGS] <toolchain> <command>...

FLAGS:
    -h, --help       Prints help information
        --install    Install the requested toolchain if needed

ARGS:
    <toolchain>     Toolchain name, such as 'stable', 'beta', 'nightly', or '4.3.0'. For more information see `elan
                    help toolchain`
    <command>...

DISCUSSION:
    Configures an environment to use the given toolchain and then runs
    the specified program. The command may be any program, not just
    lean or lake. This can be used for testing arbitrary toolchains
    without setting an override.

    Commands explicitly proxied by `elan` (such as `lean` and
    `lake`) also have a shorthand for this available. The toolchain
    can be set by using `+toolchain` as the first argument. These are
    equivalent:

        $ lake +nightly build

        $ elan run --install nightly lake build
```

:::elan run "[\"--install\"] toolchain command ..."
配置环境以使用给定的工具链，然后运行指定的程序。
如果提供了 {elanOptDef flag}`--install` 标志，则将安装工具链。
该命令可以是任何程序；它不需要是属于工具链一部分的命令，例如 `lean` 或 `lake`。
这可用于测试任意工具链而无需设置覆盖。
:::

```elanHelp "which"
elan-which
Display which binary will be run for a given command

USAGE:
    elan which <command>

FLAGS:
    -h, --help    Prints help information

ARGS:
    <command>
```

:::elan which "command"
显示 {elanMeta}`command` 的工具链特定二进制文件的完整路径。
:::

## 管理义隆
%%%
tag := "elan-self"
%%%

Elan 可以管理自己的安装。
它可以自我升级、自我删除，并帮助为许多流行的 shell 配置制表符完成。

```elanHelp "self"
elan-self
Modify the elan installation

USAGE:
    elan self <SUBCOMMAND>

FLAGS:
    -h, --help    Prints help information

SUBCOMMANDS:
    update       Download and install updates to elan
    uninstall    Uninstall elan.
    help         Prints this message or the help of the given subcommand(s)
```


```elanHelp "self" "update"
elan-self-update
Download and install updates to elan

USAGE:
    elan self update

FLAGS:
    -h, --help    Prints help information
```
:::elan self update
下载并安装 Elan 本身的更新。
:::

:::elan self uninstall
卸载 Elan。
:::

```elanHelp "completions"
elan-completions
Generate completion scripts for your shell

USAGE:
    elan completions [shell]

FLAGS:
    -h, --help    Prints help information

ARGS:
    <shell>     [possible values: zsh, bash, fish, powershell, elvish]

DISCUSSION:
    One can generate a completion script for `elan` that is
    compatible with a given shell. The script is output on `stdout`
    allowing one to re-direct the output to the file of their
    choosing. Where you place the file will depend on which shell, and
    which operating system you are using. Your particular
    configuration may also determine where these scripts need to be
    placed.

    Here are some common set ups for the three supported shells under
    Unix and similar operating systems (such as GNU/Linux).

    BASH:

    Completion files are commonly stored in `/etc/bash_completion.d/`.
    Run the command:

        $ elan completions bash > /etc/bash_completion.d/elan.bash-completion

    This installs the completion script. You may have to log out and
    log back in to your shell session for the changes to take affect.

    BASH (macOS/Homebrew):

    Homebrew stores bash completion files within the Homebrew directory.
    With the `bash-completion` brew formula installed, run the command:

        $ elan completions bash > $(brew --prefix)/etc/bash_completion.d/elan.bash-completion

    FISH:

    Fish completion files are commonly stored in
    `$HOME/.config/fish/completions`. Run the command:

        $ elan completions fish > ~/.config/fish/completions/elan.fish

    This installs the completion script. You may have to log out and
    log back in to your shell session for the changes to take affect.

    ZSH:

    ZSH completions are commonly stored in any directory listed in
    your `$fpath` variable. To use these completions, you must either
    add the generated script to one of those directories, or add your
    own to this list.

    Adding a custom directory is often the safest bet if you are
    unsure of which directory to use. First create the directory; for
    this example we'll create a hidden directory inside our `$HOME`
    directory:

        $ mkdir ~/.zfunc

    Then add the following lines to your `.zshrc` just before
    `compinit`:

        fpath+=~/.zfunc

    Now you can install the completions script using the following
    command:

        $ elan completions zsh > ~/.zfunc/_elan

    You must then either log out and log back in, or simply run

        $ exec zsh

    for the new completions to take affect.

    CUSTOM LOCATIONS:

    Alternatively, you could save these files to the place of your
    choosing, such as a custom directory inside your $HOME. Doing so
    will require you to add the proper directives, such as `source`ing
    inside your login script. Consult your shells documentation for
    how to add such directives.

    POWERSHELL:

    The powershell completion scripts require PowerShell v5.0+ (which
    comes Windows 10, but can be downloaded separately for windows 7
    or 8.1).

    First, check if a profile has already been set

        PS C:\> Test-Path $profile

    If the above command returns `False` run the following

        PS C:\> New-Item -path $profile -type file -force

    Now open the file provided by `$profile` (if you used the
    `New-Item` command it will be
    `%USERPROFILE%\Documents\WindowsPowerShell\Microsoft.PowerShell_profile.ps1`

    Next, we either save the completions file into our profile, or
    into a separate file and source it inside our profile. To save the
    completions into our profile simply use

        PS C:\> elan completions powershell >>
%USERPROFILE%\Documents\WindowsPowerShell\Microsoft.PowerShell_profile.ps1
```

:::elan completions "shell"
为 Elan 生成 shell 完成脚本，从而在各种 shell 中为 Elan 命令启用制表符完成。
有关如何安装它们的说明，请参阅 `elan help completions` 的输出。
:::
