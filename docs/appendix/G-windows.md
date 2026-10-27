# 附录 G　Windows 故障排查

本附录按「症状 → 原因 → 处理」列出在 Windows 11 上使用本书仓库时会遇到的问题，不少是作者写这本书时真实
碰到的，其余是预防性的说明。它针对锁定的 Lean `v4.35.0` + Mathlib `v4.35.0`（commit `56a0058`）与 VS Code 扩展
`leanprover.lean4` 0.0.240；换了版本，命令与报错文字可能不同。安装步骤见第 1 章第 2、3 节，这里不重复，只处理
装好之后出的问题。

**依据的写法。** 每行最后一列注明依据：

- 「第 1 章 §N」：`Lean4Learn/Part1/Ch01_Setup.lean` 第 N 节（该节自己标「未验证」的，这里照样标「未实测」）。
- 「README」：仓库根目录的 `README.md`。
- 「源码」：本地文件，路径相对仓库根目录或扩展目录（如 `.lake/packages/mathlib/Cache/IO.lean`、
  Lake 的 `Lake/CLI/Help.lean`、扩展的 `manual/manual.md` 与 `package.json`）。Lake 源码在 elan 工具链目录的
  `src/lean/lake/Lake/CLI/Help.lean`（作者机器上是
  `…\toolchains\leanprover--lean4---v4.35.0\src\lean\lake\Lake\CLI\Help.lean`）；扩展文件在
  `%USERPROFILE%\.vscode\extensions\leanprover.lean4-0.0.240\` 下。
- 「手册」：Lean 参考手册 4.35.0 <https://lean-lang.org/doc/reference/4.35.0/>。
- 「笔记 §x」「构建记录」：作者的调研笔记 `_research/10-tooling-ecosystem-windows.md` 与构建日志
  `_research/build-part1c.log`、`_research/build-part1d.log`、`_research/HANDOFF.md`。`_research/` 不随仓库
  分发（见 `.gitignore`），列在这里只为说明出处。
- 「未实测」：推断或别人的说法，作者没有在本机复现。

## 1. 速查表

| 症状 | 原因 | 处理 | 依据 |
|---|---|---|---|
| 打开文件后很久没有结果，`lake build` 开始编译成百上千个 Mathlib 文件 | 没有取预编译缓存，或缓存失配：缓存键由 `lakefile.lean`、`lean-toolchain`、`lake-manifest.json`、编译器版本与文件内容共同决定 | `lake exe cache get`；仍然失配时 `lake exe cache get!` 强制重新下载。不要改 `.lake/packages/mathlib` 下的文件 | 第 1 章 §2；源码 `Cache/README.md`（*Quick Start*、*File Hashing*） |
| C 盘空间不够 | 缓存压缩包默认放在 `C:\Users\<你>\.cache\mathlib`；解压后的产物在项目的 `.lake/` 里（作者机器上约 7 GB） | 把项目放在别的盘；设用户环境变量 `MATHLIB_CACHE_DIR` 把压缩包也移走（**未实测**） | 第 1 章 §2、§3；源码 `Cache/IO.lean` 第 62–75 行、`Cache/README.md` *Environment Variables* |
| `cache` 打印 ``Warning: recommended `curl` version ≥7.84``，或下载失败 | `curl.exe` 版本低（低于 7.75 不能并行下载），或网络需要代理 | `curl.exe --version` 检查；有代理时确认 `HTTPS_PROXY`（代理一项**未实测**）；新的下载端点出问题时可临时设 `MATHLIB_CACHE_DEBUG_USE_LEGACY=1` | 第 1 章 §2；源码 `Cache/IO.lean` 第 262–289 行、`Cache/README.md` *Troubleshooting* |
| `leantar not found in Lean sysroot. This toolchain may predate nightly-2026-03-09.` | 当前工具链里没有 `leantar.exe`；报错本身指向工具链过旧 | 在仓库根目录确认 `lean --version` 是 4.35.0（`lean-toolchain` 决定，elan 自动下载）（处理**未实测**） | 源码 `Cache/IO.lean` 第 134 行；笔记 §1.4 |
| `lake build` 报 `error: <文件>:1:0: failed to read file '…\Mathlib\Tactic\Simps\Basic.olean'`，失败的也可能是 `.olean.private`、`.ir` 文件；每次失败的文件不同 | 内存不足时 Lake 并行编译出错（原因是推断，**未实测**） | 逐个模块构建：`lake build +Lean4Learn.Part1.Ch01_Setup`，依次构建各章，最后再 `lake build Lean4Learn` | 构建记录（`build-part1c.log` 一次失败 7 个模块；`build-part1d.log` 逐个构建全部通过，随后 `lake build Lean4Learn` 退出码 0） |
| 机器卡死，一个文件编译要二十分钟以上 | 内存约 1 GB 空闲时同时跑两个 `lean` 进程（例如 VS Code 正在处理文件，终端里又在构建） | 一次只跑一个：命令行构建时关掉正在处理的 Lean 文件，或执行 *Stop Server*；自己的文件里不要 `import Mathlib` | 构建记录（`HANDOFF.md`，作者机器上的观察，**未系统计时**）；第 1 章 §8（`import Mathlib` 约 20 分钟，未系统计时）；*Stop Server* 命令见笔记 §1.2 |
| 命令行 `lake env lean` 与 `lake build` 结果不一样，例如漏绑的变量没有报错、`fun` 显示成 `=>` | `lake env lean` 不应用 `lakefile.toml` 的 `[leanOptions]` | 手工加 `-DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true`；或用 `lake lean <文件>`，它先构建导入，再带上根包的附加参数运行 `lean` | README「使用建议」；第 1 章 §3（该节注明未单独实测）；源码 Lake `CLI/Help.lean` 的 `helpLean` |
| PowerShell 7 里 `-Dpp.unicode.fun=true` 报错或不生效 | PowerShell 从第一个点处把没加引号的参数切成 `-Dpp` 与 `.unicode.fun=true` | 给每个 `-D` 参数加单引号：`'-Dpp.unicode.fun=true'` | 第 1 章 §3（实测） |
| 运行 `lake update` 之后 `lean-toolchain`、`lake-manifest.json` 变了，缓存全部失配 | `lake update` 改写 manifest，默认还会在依赖指定了新工具链时改写根包的 `lean-toolchain` | 不要在本仓库运行它；已经运行了，用 `git checkout -- lean-toolchain lake-manifest.json` 恢复，再 `lake exe cache get`（恢复步骤**未实测**） | 第 1 章 §10；手册 §25.1.5.4（`--keep-toolchain` 可关掉改写） |
| `lake clean` 之后又要重新编译或下载整个 Mathlib | 不带包名的 `lake clean` 删除工作区里**每个**包的构建目录，包括 Mathlib | 之后重新 `lake exe cache get`；只想清本书的产物时写包名 `lake clean lean4-learn`（两条处理都**未实测**） | 源码 Lake `CLI/Help.lean` 的 `helpClean`；笔记 §1.3 |
| 改了一个被导入的文件，导入它的文件还是旧结果；或打开文件时报依赖需要重建、文件不再往下处理 | 扩展默认不自动重建依赖（设置 `lean4.automaticallyBuildDependencies` 默认 `false`） | 保存后在导入者里执行 *Restart File*（`Ctrl+Shift+X`）；也可打开上述设置 | 第 1 章 §4；源码扩展 `manual/manual.md` *File restarting*、`package.json` |
| infoview（信息视图）不更新、状态混乱 | 语言服务器出错 | 先 *Restart File*；不行再 *Restart Server*（完全重启 Lean）；扩展本身出错时重启 VS Code | 第 1 章 §4；源码扩展 `manual/manual.md` *Restarting Lean* |
| `error: object file '….olean' of module Lean4Learn.Part1.Ch02_Calculation does not exist` | 导入了还没编译的模块 | `lake build Lean4Learn.Part1.Ch02_Calculation`，再对导入它的文件 *Restart File* | 第 1 章 §12（作者机器上试过） |
| `error: unknown module prefix 'Foo'`，后接 `No directory 'Foo' or file 'Foo.olean' in the search path entries:` | 包名拼错，或 `lakefile.toml` 没有把这个包列为依赖 | 检查 `import` 的拼写与依赖列表 | 第 1 章 §12（作者机器上试过） |
| 文件开头位置 `1:0` 报 `error: expected token` | 文件是 UTF-16：PowerShell 5.1 的 `>` 与 `Out-File` 写出带 BOM 的 UTF-16LE | 在 PowerShell 7 里生成文件，或在 VS Code 里以 UTF-8 重新保存（重新保存一项**未实测**） | 第 1 章 §2、§12（实测） |
| 注释里的汉字在编辑器里是乱码，但文件照常编译 | 文件被 `Set-Content` 按系统代码页（GBK，936）写出 | 同上，改用 UTF-8 | 第 1 章 §2、§12（实测） |
| 终端里 `⊢`、`∀`、`ℝ` 显示成乱码 | 控制台代码页是 936，Lean 输出 UTF-8 | `chcp 65001`，或在 PowerShell 里设 `[Console]::OutputEncoding = [System.Text.Encoding]::UTF8`（**未实测**） | 笔记 §0（代码页 936 实测）、§1.7（处理为推断） |
| 准备把仓库放在很深的目录下（预防） | 未开启长路径时 Windows 路径上限 259 个字符；`.lake` 里最长的相对路径 153 个字符 | 项目根至多约 105 个字符，建议 `E:\lean4-learn` 这样的短路径；或以管理员身份把 `LongPathsEnabled` 设为 1（**未实测**） | 第 1 章 §2（长度为实测，开长路径一项该节标未验证） |
| 想升级 Scoop 装的 elan | Scoop 管理 `elan.exe` | 用 `scoop update elan`，不用 `elan self update`（**未实测**） | README；笔记 §1.1（推断） |
| 用户目录下的工具链越积越多 | 每个用过的 Lean 版本都留一份 | `elan toolchain gc` 列出可删的，`elan toolchain gc --delete` 删除；帮助文字说它是实验性的（**未实测**） | 笔记 §1.1（帮助文字已核对） |

## 2. 内存不够时怎么编译

本书是在空闲内存约 1 GB 的笔记本上写成的（作者的观察，见 `_research/HANDOFF.md`）。这类机器上：

1. **一次只有一个 `lean` 进程。** VS Code 打开一个 Lean 文件就会启动语言服务器处理它；终端里再跑
   `lake build` 或 `lake env lean`，两个进程抢内存，编译会严重变慢（作者的观察，未系统计时）。
2. **整体构建失败就逐个构建。** `lake build Lean4Learn` 会并行编译多个模块。作者遇到过一次 7 个模块同时
   以 `failed to read file` 失败（失败的文件每次不同，像是读文件时资源不足，而不是文件真的坏了；这是推断）。
   改为对每章执行 `lake build +Lean4Learn.Part1.ChNN_…`，全部通过，之后整体 `lake build Lean4Learn` 也通过
   （`_research/build-part1d.log`）。`+模块名` 表示只构建这一个模块及其依赖（笔记 §1.3，据 Lake 的用法说明）。
3. **窄导入。** 每章只导入用到的 Mathlib 模块（第 1 章 §8）；导入越多，加载的 olean 文件越多。

## 3. `lake env lean`、`lake lean` 与 `lake build`

`lakefile.toml` 的 `[leanOptions]` 写着 `autoImplicit = false`、`relaxedAutoImplicit = false`、
`pp.unicode.fun = true`（第 1 章 §9）。`lake build` 与 `lake lean <文件>` 构建时会带上包的设置；
`lake env lean <文件>` 只是在 Lake 设好的环境变量里直接运行 `lean`，不读这些选项（README；第 1 章 §3 注明这一点
据 Lake 源码与作者经验，未单独实测）。所以用 `lake env lean` 检查单个文件时，要像第 1 章 §3 那样手工加三个
`-D` 参数，否则 `autoImplicit` 回到 Lean 的默认值，签名的含义可能不同（第 1 章 §9）。另外 `lake env lean`
不会先构建被导入的模块；导入了未编译的模块就会得到上表里的 `object file … does not exist`。

## 4. 版本锁定

`lean-toolchain`、`lakefile.toml` 的 `rev = "v4.35.0"` 与 `lake-manifest.json` 三者一起固定版本（第 1 章 §10）。
日常只用 `lake build` 与 `lake exe cache get`；**不要运行 `lake update`**（README；第 1 章 §10）。Mathlib 在
`lakefile.lean` 里声明 `fixedToolchain := true`（`.lake/packages/mathlib/lakefile.lean` 第 64 行）：一个 Mathlib
版本只配它发布时的 Lean 版本，所以单独改 `lean-toolchain` 或单独改 `rev` 都会失配。真要升级，见第 1 章 §10 的步骤。
