module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.ExtractGoal
public import Mathlib.Tactic.NormNum.Basic

/-!
# 第 1 章　环境、工作流与第一份文件

本章带你在 Windows 11 上把这本书的仓库跑起来：装好 elan（管理 Lean 版本的工具）、VS Code 和 Lean 4
扩展，打开仓库，读懂 infoview（信息视图），学会输入 Unicode 的 notation（记号），并逐行读懂每个文件开头的
固定样板。
读完后你能自己编译、修改任何一章的 exercise（练习），并在遇到问题时写出一个别人愿意回答的最小可复现例子。

## 学习目标
- 在 Windows 11 上用 Scoop 装好 elan、VS Code 与 Lean 4 扩展，打开本仓库并确认能编译。
- 区分 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json`、`.lake/`，知道为什么不能 `lake update`。
- 读懂 infoview 里的 proof state（证明状态）：`⊢`、hypothesis（假设）、`case` 标签、`✝`。
- 用反斜杠缩写加 `Tab` 输入 Unicode 记号；用 `#check`、`#eval`、`#print`、`#guard_msgs` 与 Lean 交互。
- 逐行解释每个文件的开头（`module`、`public import`、`@[expose] public section`）与 `autoImplicit = false`。
- 知道练习与 solution（答案）如何对应，会写 MWE（minimal working example，最小可复现例子）并在 Zulip 提问。

## 前置知识
没有数学上的前置章节，只假定你玩过 Natural Number Game，见过 goal（目标）与 tactic（策略）的样子。
环境上需要：Windows 11、已装好 Scoop（<https://scoop.sh>），会在终端里敲命令；推荐 PowerShell 7（第 2 节装）。
-/

@[expose] public section

namespace Lean4Learn.Ch01

/-!
## 1. 这本书怎么用

本书是一个 Lake 项目（Lake 是 Lean 的构建工具）。**你正在读的这个文件本身就是第 1 章**：正文写在
module docstring（模块文档注释）里，代码可以运行，运行结果由编译器核对。装好环境之前，用任何文本编辑器
读第 1 至 3 节即可；装好之后在 VS Code 里重新打开本文件，对照 infoview 读第 4 节起的内容。
仓库里最重要的文件：本章 `Lean4Learn/Part1/Ch01_Setup.lean`、答案 `Solutions/Part1/Ch01_Setup.lean`，
以及固定版本、配置构建的 `lean-toolchain`、`lakefile.toml`、`lake-manifest.json`（第 9、10 节）。

练习是名为 `ex_<章>_<序号>` 的 `theorem`，证明体是 `by sorry`。`sorry` 是占位：Lean 接受它，
但会发出一条警告。你的任务是把 `sorry` 换成真正的证明。答案在 `Solutions/` 的同名文件里：
陈述（包括 docstring（文档注释））与练习逐字相同，但没有 `sorry`。先自己做，再对照。

先看一个最小的例子。`#guard_msgs` 把紧随其后的命令所发出的消息与它前面的文档注释比对，不一致就报错
（第 6 节细讲）；这里它断言下面这条命令恰好发出一条警告。`example` 是不起名字的声明，只检查、不保存，
`:=` 之后是证明。只要没有别的错误，含 `sorry` 的声明就会产生警告：
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example : 1 + 1 = 2 := sorry

/-!
> **撞词提示。** "目标"指证明里的目标（goal，`⊢` 之后的东西）；Lake 的 target（如 `lake build Solutions`
> 里的 `Solutions`）永远写作"构建目标"。"节"是本书的章节，`section` 命令叫"区段"；"选项"指 `set_option`
> 设置的选项，不是 `Option` 类型；"记号"指 notation（`∑`、`∣` 这样的写法），"符号"指 symbol（一个 Unicode 字符）。
-/

/-!
## 2. 在 Windows 11 上安装

本节装 PowerShell 7、elan、VS Code 加 Lean 4 扩展、Mathlib 的预编译产物，并检查几处容易出问题的设置。带数字的
结果是 2026-10-16 在作者的 Windows 11 上的一次测量；标"未验证"的做法没有在干净的机器上试过，换了机器请自己核对。

**第一步：PowerShell 7、Git、elan 与 ripgrep。** Windows 自带的是 PowerShell 5.1（命令 `powershell`），PowerShell 7
的命令是 `pwsh`，本章的命令都在它里面运行。Lake 用 Git 取依赖；elan 按项目要求下载并切换 toolchain（工具链，
即某个确定版本的 Lean 及其附带程序）；ripgrep（命令 `rg`）是命令行搜索工具，第 11 节用它在 Mathlib 源码里找名字。

```powershell
scoop install pwsh git elan ripgrep   # elan 在 Scoop 的 main bucket 里
pwsh                                  # 进入 PowerShell 7，后面的命令都在这里运行
$PSVersionTable.PSVersion             # 主版本号应是 7
```

**第二步：VS Code 与 Lean 4 扩展。** 官方安装包或 Scoop 的 extras bucket（`scoop bucket add extras`，
然后 `scoop install vscode`）均可；扩展用 `code --install-extension leanprover.lean4` 安装。

**第三步：取得仓库，下载 Mathlib 的预编译产物。** 尖括号处换成你拿到本书时给的仓库地址。Mathlib 从头编译代价
极高，所以它提供预编译好的 olean（`.olean` 文件，Lean 的编译产物）下载；`.lake/` 不进 Git，克隆之后要先取缓存。
第一次运行 `lake` 时 elan 会按 `lean-toolchain` 下载对应版本的 Lean，要等一阵：

```powershell
git clone <本仓库地址> E:\lean4-learn
cd E:\lean4-learn
lake exe cache get
```

`cache` 是 Mathlib 自带的程序，依赖系统的 `curl.exe`，压缩包放在 `C:\Users\<你>\.cache\mathlib`（`Cache/IO.lean`）。
改动 `.lake/packages/mathlib` 下的文件或换了工具链会让缓存失配；误删 `.lake` 后要重新运行。这一步未验证：
作者没有在全新克隆上完整走过。

**第四步：打开仓库。** 用 `code E:\lean4-learn` 打开**文件夹**，而不是单个 `.lean` 文件（扩展手册建议用
*File: Open Folder…* 打开项目目录）。处理文件时编辑器里会出现橙色进度条；它消失之后，infoview 才有完整内容。

**几处容易出问题的设置：**

- curl：`curl.exe --version`。缓存程序建议 7.84 或更高（低于 7.75 不能并行下载，见 `Cache/IO.lean` 的
  `validateCurl`）；作者机器上系统自带的是 8.21.0（Schannel），够用。
- 长路径：`Get-ItemProperty HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem LongPathsEnabled`，0 表示没开，
  路径上限 259 个字符。`.lake` 里最长的相对路径是 153 个字符；作者自己的项目根 `E:\gitclone\lean4-learn` 是 23 个
  字符，全路径 23 + 1（反斜杠）+ 153 = 177。所以项目根至多约 105 个字符才安全，建议放在 `E:\lean4-learn` 这样的
  短路径下。路径太长时可以以管理员身份把该项设为 1（未验证：没有试过 Lake 与 Lean 在长路径下是否正常）。
- 代理：作者实测 curl 遵守 `HTTPS_PROXY`，缓存的下载地址是 https，所以下载失败时先检查这个变量（未验证：
  没有在代理环境下实际下载过）。
- 编码：PowerShell 5.1 的 `>` 与 `Out-File` 写出带 BOM 的 UTF-16LE，`Set-Content` 写系统 ANSI 代码页（作者的机器上
  是 936，即 GBK），PowerShell 7 默认写不带 BOM 的 UTF-8。Lean 要求源文件是 UTF-8，所以**不要在 5.1 里用 `>` 或
  `Set-Content` 生成 `.lean` 文件**（出错时的样子见第 12 节）。
-/

/-!
## 3. 打开仓库，第一次编译

要检查环境是否就绪，在仓库根目录运行（行尾的反引号是 PowerShell 的续行）：

```powershell
lake env lean '-DautoImplicit=false' '-DrelaxedAutoImplicit=false' '-Dpp.unicode.fun=true' `
  Lean4Learn/Part1/Ch01_Setup.lean
```

三个 `-D` 参数手工模拟 `lakefile.toml` 里的 `leanOptions`（第 9 节）：`lake env lean` 不会替你应用它们，
`lake lean <文件>` 与 `lake build` 会（据 Lake 源码与作者的编译脚本经验，未单独实测）。含点号的
`'-Dpp.unicode.fun=true'` 必须加引号：PowerShell 7 会从第一个点处把没加引号的它切成 `-Dpp` 与
`.unicode.fun=true`（实测）；另两个加引号只是为了统一。

预期：恰好 13 条 ``declaration uses `sorry` `` 警告（每道练习一条），没有错误：这是你的自检标准。

`.lake/packages/` 存放 Mathlib 及其依赖（作者机器上整个 `.lake` 约 7 GB），`.lake/build/` 存放本书两个 library
（库，即 Lake 构建的一组模块）`Lean4Learn` 与 `Solutions` 的编译结果；`lean-toolchain`、`lakefile.toml`、
`lake-manifest.json` 由 Git 跟踪，由作者固定，你不用改它们。编译有三条路：编辑器里边写边编译（日常写证明用）；
命令行检查单个文件（上面的命令）；`lake build`（可加 `Lean4Learn`、`Solutions` 或具体 module（模块）名）整体检查，
提交前用。`lake build` 只构建聚合文件（`Lean4Learn.lean`、`Solutions.lean`）里 import（导入）了的章节；
全局选项 `--wfail` 把任何警告当作失败，所以只有 `Solutions` 能这样检查：`lake build Solutions --wfail`。
-/

/-!
## 4. 读 infoview

infoview 显示光标处的证明状态：上半部分是 context（上下文），即局部变量和假设，形如 `名字 : T`，
其中 `T` 是 type（类型），同类型的相邻变量合并成一行（如 `a b : ℕ`）；`⊢`（读作"目标是"）之后是待证的
目标。消息（`error`、`warning`、`info`）显示在 Messages 一栏，也以波浪线标在编辑器里。下面用 `trace_state`
把 infoview 会显示的文字打印成一条消息，并用 `#guard_msgs` 固定下来（`rw` 见第 2 章，`intro`、
`constructor` 见第 4 章，`rfl` 见第 5 章）：
-/

/--
trace: a b : ℕ
h : a = b
⊢ b = a
-/
#guard_msgs in
example (a b : ℕ) (h : a = b) : b = a := by
  trace_state
  rw [h]

/-!
`rw [h]` 把目标里的 `a` 换成 `b`，目标变成 `b = b`，`rw` 随后自动用 `rfl` 关闭它。infoview 显示的是光标
位置的证明状态（扩展手册 *InfoView* 一节）。读源码常用三个操作：悬停在标识符上看类型与
文档；光标放在标识符上按 `F12`（Go to Definition）跳到定义；输入名字的前几个字母后按 `Ctrl+Space` 补全。

一个目标变成两个时，infoview 用 `case` 标签区分它们，目标之间隔一个空行。下面 `constructor` 把
`A ∧ B` 这样的目标拆成名为 `left` 与 `right` 的两个目标（第 4 章细讲），`·` 逐个处理它们：
-/

/--
trace: case left
⊢ 1 + 1 = 2

case right
⊢ 2 + 2 = 4
-/
#guard_msgs in
example : 1 + 1 = 2 ∧ 2 + 2 = 4 := by
  constructor
  trace_state
  · rfl
  · rfl

/-!
`intro` 不给名字时，新变量没有可访问的名字，infoview 用 `✝` 标出这种"不可访问"的名字。你在后面经常
会遇到它；写成 `intro n` 就得到可以引用的名字：
-/

/--
trace: n✝ : ℕ
⊢ n✝ = n✝
-/
#guard_msgs in
example : ∀ n : ℕ, n = n := by
  intro
  trace_state
  rfl

/-!
VS Code 的 Lean 4 扩展（本书核对的是 0.0.240 版）的命令在命令面板（`Ctrl+Shift+P`）里按标题的一部分搜索；
面板里的完整名前面带分类，例如 `Lean 4: Troubleshooting: Show Setup Information`（生成一段 Markdown，
提问时贴给别人）。另有 Toggle InfoView（`Ctrl+Shift+Enter`）和 Restart Server（卡死或状态混乱时的总重置）。

> **最要记住的一条：Restart File**（在 Lean 文件里默认是 `Ctrl+Shift+X`）。编辑器**不会**悄悄重建被导入的文件：改了一个
> 被别的文件导入的模块后，先保存，再对导入它的文件执行 Restart File。

## 5. 输入 Unicode 记号

Lean 与 Mathlib 大量使用 Unicode。在 VS Code 里输入反斜杠 `\` 加缩写。当以已输入内容开头的所有缩写都指向
同一个符号时，自动替换（设置 *Eager Replacement*，默认开启）：`\eps` 立即变成 `ε`，因为更长的 `\epsilon` 也是
`ε`；否则按 `Tab` 或接着输入下一个字符，如 `\to`（还有以它开头的更长缩写）与 `\N`（还有 `\Nat`、`\Nu`）。把鼠标
悬停在任意符号上，会列出它的所有缩写。本书用到的常见记号：

| 记号 | 缩写 | 记号 | 缩写 | 记号 | 缩写 |
|---|---|---|---|---|---|
| `→` | `\to` | `↦` | `\mapsto` | `↔` | `\iff` |
| `∀` | `\forall` | `∃` | `\exists` | `¬` | `\not` |
| `∧` | `\and` | `∨` | `\or` | `≠` | `\ne` |
| `≤` | `\le` | `≥` | `\ge` | `∈` | `\in` |
| `ℕ` | `\N` | `ℤ` | `\Z` | `ℝ` | `\R` |
| `⟨ ⟩` | `\<` `\>` | `∣` | `\mid` | `∑` | `\sum` |
| `α` | `\alpha` | `ε` | `\eps` | | |

以下几处容易踩坑（核对自扩展 0.0.240 的缩写表）：`\int` 得到 `ℤ`，不是积分号 `∫`（积分号是 `\integral`）；
`\l` 得到 `←`；整除号 `∣` 是 `\mid`，与键盘上的竖线 `|` 是不同的字符；`\varepsilon` 不是缩写，用 `\eps`。
要找一个符号的缩写，用命令 "Lean 4: Input: Find Unicode Symbol…"（按符号或按名字搜）。

ASCII 写法大多也被接受，例如 `->`、`<=`、`fun x => …`；但 Mathlib 的风格是 Unicode，本书也一律用
`fun x ↦ …`，源码里不写 `λ`。ASCII 与 Unicode 只是同一个记号的两种拼写，得到同一个 term（项）：下面用第 6 节
要讲的 `#check` 看一眼，输入的 `<=` 被显示成 `≤`：
-/

/-- info: 3 ≤ 4 : Prop -/
#guard_msgs in
#check (3 <= 4)

/-!
## 6. 与 Lean 对话：`#check`、`#eval`、`#print` 与 `#guard_msgs`

读证明之外，你要经常问 Lean 问题，再把答案固定下来。四个最常用的命令：`#check e` 给出 `e` 的类型（对
常量还显示签名），`#eval e` 计算并打印结果，`#print x` 打印声明 `x` 的定义，`#guard_msgs in cmd` 运行
`cmd` 并把它发出的消息与文档注释逐一比对。
-/

/-- info: Nat.add_comm (n m : ℕ) : n + m = m + n -/
#guard_msgs in
#check Nat.add_comm

/-- info: 42 -/
#guard_msgs in
#eval 6 * 7

def double (n : ℕ) : ℕ := 2 * n

/--
info: @[expose] def Lean4Learn.Ch01.double : ℕ → ℕ :=
fun n ↦ 2 * n
-/
#guard_msgs in
set_option pp.unicode.fun true in
#print double

/-!
`def` 定义一个函数（或别的数据），`set_option … in` 只在紧随其后的一条命令里改变选项（第 9 节有例子）；
这里它让 `#print` 用 `↦` 显示函数。输出里的 `@[expose]` 来自文件头，见第 8 节。

**本书为什么到处用 `#guard_msgs`。** 教材里写"这条命令会输出 42"，几个月后升级可能悄悄变错；把输出
写进文档注释，输出一变，编译就失败。所以凡是"Lean 会这样回答"的断言，只要能在文件内部捕获，后面都有一个
`#guard_msgs` 守着（文件头的消息捕获不了，见第 12 节）。

工作流程（你自己写时也这样）：

1. 写 `#guard_msgs in`，文档注释留空。
2. 编译一次。不一致时 Lean 报出 error message（错误信息），并打印真实消息。报告是一份 diff（差异）：每行
   开头有两个字符的前缀，`- `（你写的）、`+ `（Lean 真正发出的）或两个空格（两边相同的行）。
3. 把 `+ ` 行和空格开头的行去掉前缀，原样抄进 `/-- … -/`（VS Code 里也可以点灯泡，用代码操作自动
   替换），再编译，没有输出就通过。

不一致时的报告长什么样，可以故意写错一次来看：内层 `#guard_msgs` 故意写错，外层把它报的错固定下来。外层
注释分三段：内层命令原本发出的 `info`（比对失败时 `#guard_msgs` 会把原消息照样再发一遍）；分隔线 `---`
（只是分隔线，不是语法，一条命令发出多条消息时都这样隔开）；比对失败的 error，其中 `-`、`+` 开头的行就是
上面说的 diff：
-/

/--
info: Nat.add_comm (n m : ℕ) : n + m = m + n
---
error: ❌️ Docstring on `#guard_msgs` does not match generated message:

- info: wrong
+ info: Nat.add_comm (n m : ℕ) : n + m = m + n
-/
#guard_msgs in
/-- info: wrong -/
#guard_msgs in
#check Nat.add_comm

/-!
比对时先去掉首尾空白，再把每个换行换成一个空格，所以长行可以折行，但**缩进里的空格与空行都要原样**
（第 9、12 节里带空行的消息就是例子）。`info:`、`warning:`、`error:` 是消息的严重程度前缀。终端里错误
常常印成 `error(lean.xxx): …`，括号里的错误名在 `#guard_msgs` 里**不出现**，注释里只写 `error: …`。
Lean 对未知名字有两种措辞，`Unknown constant`（第 12 节）与 `Unknown identifier`（第 9 节），读到任一种
都先检查拼写；如果那个名字是你自己引入的变量，再检查它有没有绑定（第 9 节）。
-/

/-!
## 7. 练习要用的几个策略

练习主要用下面几个策略。它们在后面的章节细讲（`norm_num`、`omega`、`exact?` 第 2 章，`exact` 第 4 章，`rfl`、
`decide` 第 5 章），这里只要求会读、会敲；注释写出每个策略面对的目标和它做了什么：
-/

example : (2 : ℕ) + 3 = 5 := by rfl                   -- ⊢ 2 + 3 = 5：两边求值后相同（定义相等），关闭
example : (12 : ℕ) ∣ 60 := by decide                  -- ⊢ 12 ∣ 60：decidable（可判定）命题，求值得 true，关闭
example : (4 : ℤ) - 9 = -5 := by norm_num             -- ⊢ 4 - 9 = -5：简化数值表达式，得到 True，关闭
example (x : ℕ) (h : 2 * x = 6) : x = 3 := by omega   -- h : 2 * x = 6 ⊢ x = 3：由 h 做线性算术推理
example (a b : ℕ) (h : a = b) : a = b := by exact h   -- h : a = b ⊢ a = b：用现成的项 h 收尾

-- 最后是 `exact?`：它在库里搜索能关闭当前目标的 lemma（引理），以一条 `Try this` 消息告诉你结果；
-- 你再把 `exact?` 换成它给出的写法（`[apply]` 只是建议类型的标签，抄 `exact …` 之后的部分）。
/--
info: Try this:
  [apply] exact Nat.add_comm a b
-/
#guard_msgs in
example (a b : ℕ) : a + b = b + a := by exact?

-- `exact?` 不是万能的：下面这个目标它就证不出来（练习 1.9 用到这一点）。
/-- error: `exact?` could not close the goal. Try `apply?` to see partial suggestions. -/
#guard_msgs in
example (x y z : ℕ) (h₁ : x ≤ y) (h₂ : y < z) : x < z + 1 := by exact?

/-!
## 8. 文件头逐行解释

本书每个文件都以同一段样板开头和结尾（这个文件的头在最上面，结尾在最下面）：

```
module                           -- ① 声明本文件是一个模块
public import Mathlib.…          -- ② 导入，并向导入本文件的人重新导出
（模块文档注释）                  -- ③ 感叹号形式的块注释，本书的正文
@[expose] public section         -- ④ 开一个 section（区段）：名字 public（公开），定义体 expose（暴露）
namespace Lean4Learn.Ch01        -- ⑤ 本章的 namespace（命名空间）
…
end Lean4Learn.Ch01
end                              -- ⑥ 关闭第 ④ 行打开的区段
```

这是 Mathlib v4.35.0 的主流写法：Mathlib 的 8624 个源文件全部以 `module` 开头，其中 4933 个用
`@[expose] public section`（在本地 Mathlib 里用 `rg` 统计），细节见第 28 章。一个文件演示不了跨文件的
可见性，所以 ①② 的规则按 Lean 参考手册第 5 章概述，没有示例；④ 的"暴露"能用 Mathlib 的定义验证。

① **`module`**：该文件属于 Lean 的 module system（模块系统）。在模块里，声明默认是 **private（私有）**
的；只有写了 `public`（公开），或位于 `public section` 之内的声明，才对导入它的文件可见。模块只能导入
别的模块，而 Mathlib 的每个文件都是模块。

② **`import` 与 `public import`**：普通 `import M` 让 `M` 的公开名字只在本文件的私有 scope（作用域）
里可见，导入本文件的人看不到；`public import M`（公开导入）会把它们再导出一层。经验规则（由参考手册第 5 章
关于导入层级与未知常量错误的说明推出，不是手册原话）：公开声明的签名里用到的名字（类型、常量、记号）所在
的模块要用 `public import`，只在证明里用到的，普通 `import` 就够。本书统一写 `public import`，一行一个，
按字母排序，这样不必逐个判断；只导入用到的窄模块，**绝不 `import Mathlib`**：窄导入让编译的代价看得见
（作者的机器内存紧张，曾测到 `import Mathlib` 使一个文件的编译约需 20 分钟，没有系统计时）。

③ **模块文档注释** `/-! … -/`：紧跟在导入之后，本书的所有讲解都写在这里。

④ **`@[expose] public section`**：区段里的声明默认公开，`@[expose]` 还让其中所有普通 `def` 的定义体对
导入者暴露，即可见，从而下游文件能 `simp [f]`、`decide`、用 `rfl` 展开它。theorem（定理）的证明默认
不暴露（参考手册第 5 章），其余情形见第 28 章。没有 `@[expose]` 的 `public section` 里，普通 `def`
只公开名字和类型，定义体私有（下面验证）。

⑤ **命名空间**：每章一个，名字不与别的章、Mathlib 冲突（第 6 节的 `double` 全名是 `Lean4Learn.Ch01.double`）。
⑥ **末尾的 `end`** 关闭 ④ 的区段；Mathlib 里常省略它，本书保留，使结构对称。

再看"暴露"。Mathlib 的 `Nat.factorial` 定义在 `@[expose] public section` 里，你在自己的文件中就能展开它：
`simp [f]` 需要看到 `f` 的定义体，`decide` 与 `rfl` 需要把定义体算出来，所以它们都要求定义体可见：
-/

example : Nat.factorial 4 = 24 := by simp [Nat.factorial]
example : Nat.factorial 4 = 24 := by decide
example : Nat.factorial 4 = 24 := rfl

/-!
而 `pentagonal`（广义五边形数；选它只是因为 Mathlib 里它恰好没有暴露定义体，不必理解它的数学含义，本章
为此多导入了它所在的模块）定义在没有 `@[expose]` 的 `public section` 里：名字可见，定义体不可见，
所以 `simp [pentagonal]` 与 `decide` 都失败：
-/

/--
error: Invalid simp theorem `pentagonal`: Expected a definition with an exposed body
---
error: `simp` made no progress
-/
#guard_msgs in
example : pentagonal 1 = 1 := by simp [pentagonal]

/--
error: Tactic `decide` failed to reduce
  @decide (pentagonal 1 = 1) (instDecidableEqNat (pentagonal 1) 1)
to `true` or `false`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at
  (pentagonal 1).beq 1
-/
#guard_msgs in
example : pentagonal 1 = 1 := by decide

/-!
Mathlib 没有暴露 `pentagonal` 的定义体，而是提供了定义引理 `pentagonal_def`：下游文件用它改写，定义体
就"露"了出来。Mathlib 里常有 `xxx_def` 这样的定义引理。`pentagonal` 的参数是整数，所以下面的
`1` 是 `ℤ` 里的 `1`：
-/

example : pentagonal 1 = 1 := by
  rw [pentagonal_def]
  -- ⊢ (1 * (3 * 1 - 1) / 2).toNat = 1
  rfl

/-!
## 9. `lakefile.toml` 节选，以及 `autoImplicit = false`

这个文件决定每个文件编译时的选项，其中一项（`autoImplicit`）会改变你写的签名的含义，所以先读它。下面是
仓库根目录 `lakefile.toml` 的节选；你只需读懂它，不要修改（版本与依赖由作者固定）：

```toml
name = "lean4-learn"                       # package（包）名

[leanOptions]                              # 对 Lake 构建的每个文件生效的选项
pp.unicode.fun = true                      # 把 fun x => … 显示成 fun x ↦ …
autoImplicit = false                       # 关闭 auto-bound implicit（自动绑定隐式参数）
relaxedAutoImplicit = false                # 只在 autoImplicit 为 true 时有意义（见下）
[[require]]                                # 依赖
name = "mathlib"
scope = "leanprover-community"             # Reservoir（Lake 的包索引）里的作用域
rev = "v4.35.0"                            # Git 标签：固定版本
[[lean_lib]]                               # 一个 library（库）；根模块 Lean4Learn
name = "Lean4Learn"                        # （另有同样写法的一个库 Solutions）
```

每个 `lean_lib` 的名字就是根模块：`Lean4Learn` 对应 `Lean4Learn.lean` 与目录 `Lean4Learn/`。Lake 只构建
从根模块出发"可达"的模块，所以新增一章要在聚合文件里加一行 `public import`，`lake build` 才会检查它。

**`pp.unicode.fun`** 决定 `fun` 的显示。为了不依赖构建命令，下面显式设置选项来验证：
-/

/-- info: fun x ↦ x + 1 : ℕ → ℕ -/
#guard_msgs in
set_option pp.unicode.fun true in
#check fun (x : ℕ) ↦ x + 1

/-!
**自动绑定隐式参数**由选项 `autoImplicit` 控制：打开时，签名里没有绑定的标识符会被悄悄当作新的隐式
参数。`relaxedAutoImplicit` 为 `true`（核心库的默认值）时，任何原子标识符都可以这样绑定；为 `false` 时，
只有单个字符后面至多跟数字、下标之类（如 `P`、`α`、`n₁`）的标识符可以。于是拼错变量名不会立刻报错，而是得到一个意想不到的
陈述。下面把本想写的 `n + 0 = n` 误写成 `n + 0 = m`，并显式打开 `autoImplicit`：
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
set_option autoImplicit true in
theorem typoDemo (n : ℕ) : n + 0 = m := sorry

/-- info: @typoDemo : ∀ {m : ℕ} (n : ℕ), n + 0 = m -/
#guard_msgs in
#check @typoDemo

/-!
Lean 没有抱怨：`m` 成了一个新的隐式参数，定理变成"对任意 `m`，`n + 0 = m`"，一个假命题；它是用 `sorry`
"证"出来的，所以只有 `sorry` 的警告。再显式关闭 `autoImplicit`，同一个签名就在 `m` 处立刻报错
（练习 1.5）：
-/

/--
error: Unknown identifier `m`

Note: It is not possible to treat `m` as an implicitly bound variable here because the
`autoImplicit` option is set to `false`.
-/
#guard_msgs in
set_option autoImplicit false in
theorem typoDemo' (n : ℕ) : n + 0 = m := sorry

/-!
## 10. 版本锁定与 `lake update` 的危险

Lean 与 Mathlib 每月都在变，本书的输出只在一个确定的版本组合下成立。三个文件共同固定它：

- `lean-toolchain`：内容是 `leanprover/lean4:v4.35.0`。在项目目录里，`lean`、`lake` 的启动器读它，
  **覆盖** `elan default` 设的全局默认版本（那是没有项目文件时才用的版本）；该版本没有安装就自动下载。
- `lakefile.toml` 的 `rev = "v4.35.0"`：要 Mathlib 的哪个标签。
- `lake-manifest.json`：Lake 解析后记下的确切 Git 提交（Mathlib 为 `56a0058…`），由 Git 跟踪。

下面的断言钉住当前运行的 Lean 版本，工具链一变，本章就编译失败：
-/

/-- info: "4.35.0" -/
#guard_msgs in
#eval Lean.versionString

/-!
**除非有意升级，不要运行 `lake update`。** 它改写 `lake-manifest.json`；按 Lean 参考手册 Lake 一节
（§25.1.5.4），它默认还会在依赖指定了新工具链时改写你的 `lean-toolchain`（`--keep-toolchain` 可以关掉）。
对固定在标签上的 Mathlib，它通常只是重新解析同一个标签；真正的危险是一次误操作，比如把 `rev` 改成
`master`，让 Lean 与 Mathlib 一起跳到新版本，缓存和本书的示例随之失效。Mathlib 的 `lakefile.lean`
（`.lake/packages/mathlib/lakefile.lean` 第 64 行）声明了 `fixedToolchain`：一个 Mathlib 版本只支持与它
一起发布的那个 Lean 版本。要升级，必须同时改 `lean-toolchain` 与 `rev`，再运行
`lake update` 与 `lake exe cache get`。日常学习只用 `lake build` 和 `lake exe cache get`。
-/

/-!
## 11. 求助：最小可复现例子（MWE）与 Zulip

Lean 社区的交流集中在 Zulip（leanprover.zulipchat.com）。想得到回答，先做三件事：

1. **自己先查。** 读错误信息，查 `#check`，用 `exact?`，用 `rg "模式" 目录` 在 Mathlib 源码里搜（每个命中
   显示文件、行号与那一行；例如在仓库根目录运行 `rg "theorem pentagonal_def" .lake/packages/mathlib/Mathlib`，
   找到第 8 节那条引理）。
2. **做一个 MWE**：一段能在空文件里直接复制运行的最小代码，包含全部 `import`、`open`、`variable`，
   删掉无关的一切，用 `sorry` 缩短证明，并在出问题的位置写一行 `-- HERE` 之类的标记。在 Zulip 上
   `import Mathlib` 是可以的（本书的文件里不行）；新手可以先在 `new members` channel（频道）提问。
3. **说明版本。** 用命令 "Lean 4: Troubleshooting: Show Setup Information"（扩展手册 *Collecting setup
   information* 一节），它的输出是为贴到 Zulip 准备的 Markdown。

一个合格的 MWE 大致是这个样子（取第 12 节里 `rfl` 失败的例子；真实的提问还要写你期望什么、得到什么）：

```lean
import Mathlib
example (n : Nat) : n + 0 = 0 + n := by
  rfl   -- HERE：我以为这能证出来
```

代码要放在三个反引号之间；可先在 live.lean-lang.org 里验证它能复现。社区准则值得一读：
据作者读该页时的记录（未逐字复核），它把没有具体问题的"请看我的项目"、未声明的大量 AI 生成内容列为违规
行为，并要求不要用大模型写 Zulip 或 GitHub 上的评论。

缩小的办法：用 Mathlib 的 `extract_goal`（第 13 章细讲）把当前目标连同上下文变成一个独立定理，把与问题
无关的步骤换成 `sorry`，其余全部删掉。它给出的定理名带着本章的命名空间（下面是
`Lean4Learn.Ch01._example.extracted_1`），贴出去之前改成 `foo` 这样的短名字，去掉只有你的项目里才有的前缀：
-/

/--
info: theorem Lean4Learn.Ch01._example.extracted_1 (a b : ℕ) (h : a ≤ b) : a < b + 1 := sorry
-/
#guard_msgs in
example (a b : ℕ) (h : a ≤ b) : a < b + 1 := by
  extract_goal
  omega

/-!
## 12. 常见错误

下面是新手常遇到的几类错误，消息都是真实的（`unsolved goals`、`type mismatch` 留到第 13 章）。
**拼错名字**最常见，Lean 不会猜你的意思。补救：输入 `Nat.add_` 后按 `Ctrl+Space` 看补全，或
`#check Nat.add_comm`，或用 `exact?` 搜索。
-/

/-- error: Unknown constant `Nat.add_com` -/
#guard_msgs in
example (a b : ℕ) : a + b = b + a := Nat.add_com a b

/-!
**对假命题用 `decide`。** `decide` 计算一个可判定命题的真假；命题为假时，它不只是失败，
还告诉你"它是假的"。补救：回头检查陈述；想证它的否定，写 `¬ (2 + 2 = 5)` 再 `decide`（练习 1.7）。
-/

/--
error: Tactic `decide` proved that the proposition
  2 + 2 = 5
is false
-/
#guard_msgs in
example : 2 + 2 = 5 := by decide

/-!
**用 `rfl` 证一个成立、但不是定义相等的等式。** 错误信息列出两边，并指出它们不是定义相等（第 5 章）：
`n + 0` 能直接算成 `n`，`0 + n` 对变量 `n` 却不行。补救：改用 `omega`、`simp`，或库里的引理（如
`Nat.zero_add`）。
-/

/--
error: Tactic `rfl` failed: The left-hand side
  n + 0
is not definitionally equal to the right-hand side
  0 + n

n : ℕ
⊢ n + 0 = 0 + n
-/
#guard_msgs in
example (n : ℕ) : n + 0 = 0 + n := by rfl

/-!
**Windows 上的几类环境错误**发生在文件头，`#guard_msgs` 接不住，只给终端里的样子（均在作者的机器上试过）：

- `error: unknown module prefix 'Foo'`，后接 `No directory 'Foo' or file 'Foo.olean' in the search path
  entries:` 与搜索路径：包名拼错，或 `lakefile.toml` 没有把这个包列为依赖。
- `error: object file '….olean' of module Lean4Learn.Part1.Ch02_Calculation does not exist`：导入了还没
  编译的模块。先 `lake build Lean4Learn.Part1.Ch02_Calculation`，再对导入它的文件执行 Restart File。
- UTF-16 文件（第 2 节）：位置 `1:0` 报 `error: expected token`。GBK 文件反而不报错：只在注释里含 GBK 汉字
  的文件照常编译通过，汉字在编辑器里却是乱码，更隐蔽。
-/

/-!
## 练习

先把光标放到每个 `sorry` 上，看 infoview 里的目标，再动手。需要的策略都在第 7 节见过，或在题目里点名。
本章是第一章，没有前章可复习，练习都面向本章内容；也不设 ★★★。
-/

/-- 练习 1.1（★）：把 `sorry` 换成 `rfl`；再依次试 `decide` 与 `norm_num`，三者都应通过。 -/
theorem ex_1_1 : (6 : ℕ) * 7 = 42 := by sorry

/-- 练习 1.2（★）：用 `decide` 证明。先在草稿里自己用 `\mid` 敲出 `∣`，确认它与键盘上的竖线 `|` 不是
同一个字符。 -/
theorem ex_1_2 : (7 : ℕ) ∣ 91 := by sorry

/-- 练习 1.3 要用的函数：把一个自然数乘以 `3`。 -/
def triple (n : ℕ) : ℕ := 3 * n

/-- 练习 1.3（★）：先用 `#print triple`（第 6 节）看定义，用 `#eval triple 4` 算一次。因为文件头的
`@[expose]`（第 8 节），`triple` 的定义体对下游文件也是暴露的。本文件里 `decide`、`rfl` 与 `simp [triple]`
三种证法都应通过。 -/
theorem ex_1_3 : triple 4 = 12 := by sorry

/-- 练习 1.4（★）：先在草稿里为 `#check Nat.succ_le_of_lt` 配一个留空的 `#guard_msgs in`，把真实消息
抄进去直到通过（第 6 节），再删掉草稿；比较它的签名与本题的陈述（几乎相同），然后用 `omega` 证明本题。 -/
theorem ex_1_4 (a b : ℕ) (h : a < b) : a + 1 ≤ b := by sorry

/-- 练习 1.5（★）：用 `exact hq` 证明。再在整条声明前加一行 `set_option autoImplicit true in` 并删掉
`(P Q : Prop)`：声明仍然通过，`P`、`Q` 成了自动绑定的隐式参数（第 9 节）。去掉那行 `set_option` 之后，
同一份签名报 `Unknown identifier`（项目已全局关闭 `autoImplicit`）。最后恢复原样。 -/
theorem ex_1_5 (P Q : Prop) (_hp : P) (hq : Q) : Q := by sorry

/-- 练习 1.6（★）：用 `constructor` 拆开目标，用 `trace_state` 看两个 `case`（第 4 节），再用 `·` 分别
`exact`。 -/
theorem ex_1_6 (A B : Prop) (ha : A) (hb : B) : A ∧ B := by sorry

/-- 练习 1.7（★）：先在草稿里试 `example : (2 : ℕ) + 2 = 5 := by decide`，读第 12 节那样的消息，
再删掉草稿；然后用 `decide` 证明本题。否定号 `¬` 用 `\not` 输入。 -/
theorem ex_1_7 : ¬ ((2 : ℕ) + 2 = 5) := by sorry

/-- 练习 1.8（★）：把 `sorry` 换成 `exact?`，让 Lean 找出一个引理；再把 `exact?` 换成它给出的
`Try this` 里的内容。答案不止一个，你得到的引理可能与 `Solutions/` 里的不同。 -/
theorem ex_1_8 (a b c : ℕ) : a * (b + c) = a * b + a * c := by sorry

/-- 练习 1.9（★★）：先用 `omega` 证明。再试 `exact?`（第 7 节的例子就是这个形状，它会失败）；然后用
`Nat.lt_add_one_of_le`（输入 `Nat.lt_add_one` 按 `Ctrl+Space` 找到它，用 `#check` 看签名），配合
`Nat.le_trans` 与 `Nat.le_of_lt` 再证一遍，任选一种留在文件里。 -/
theorem ex_1_9 (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b < c) : a < c + 1 := by sorry

/-- 练习 1.10（★）：`simp [pentagonal]` 在这里不可用（第 8 节）。改用 `pentagonal_def`，
再用 `rfl` 收尾；注意参数 `3` 是整数。 -/
theorem ex_1_10 : pentagonal 3 = 12 := by sorry

/-- 练习 1.11（★）：`Nat.factorial` 的定义体是暴露的（第 8 节）。分别用 `simp [Nat.factorial]`、`decide`
与 `rfl` 证明，三者都应通过。 -/
theorem ex_1_11 : Nat.factorial 6 = 720 := by sorry

/-- 练习 1.12（★）：用 `intro n` 引入有名字的变量（第 4 节），用 `trace_state` 看它。先试 `rfl`，它会
失败，原因见第 12 节；再改用 `Nat.zero_add n`（配合 `exact`）或 `omega`。 -/
theorem ex_1_12 : ∀ n : ℕ, 0 + n = n := by sorry

/-- 练习 1.13（★）：在 `omega` 之前加一行 `extract_goal`，读它打印的定理（第 11 节）；再在草稿里按第 11 节
把这个目标写成一份 MWE（完整的 `import`，用 `-- HERE` 标出疑问），然后删掉草稿；用 `omega` 证明。 -/
theorem ex_1_13 (x y : ℕ) (h₁ : x + y = 10) (h₂ : x = 4) : y = 6 := by sorry

/-!
## 小结

| 主题 | 命令或语法 | 何时用 |
|---|---|---|
| 取 Mathlib 缓存 | `lake exe cache get` | 克隆之后、`.lake` 丢失之后；不要 `lake update`（第 2、10 节） |
| 编译 | `lake build`、`lake env lean '-D…'`（第 3 节） | 提交前整体检查、命令行检查单个文件 |
| 读 infoview | `⊢`、`case`、`✝`、`trace_state` | 看目标与假设（第 4 节） |
| 重启文件 | Restart File（`Ctrl+Shift+X`） | 改了被导入的模块之后（第 4 节） |
| 输入记号 | `\` 加缩写，`Tab` | `∀`（`\forall`）、`ℕ`（`\N`）、`∣`（`\mid`） |
| 交互命令 | `#check`、`#eval`、`#print`、`#guard_msgs` | 查类型、算值、看定义、固定输出（第 6 节） |
| 找引理 | `exact?`、`Ctrl+Space`、`rg` | 不知道名字时（第 7、11、12 节） |
| 文件头 | `module`、`public import`、`@[expose] public section` | 每个文件，结构相同（第 8 节；机制见第 28 章） |
| 选项 | `set_option … in`、`autoImplicit` | 局部改变行为；本书关闭自动绑定（第 9 节） |
| 版本 | `lean-toolchain`、`lake-manifest.json` | 固定 Lean 与 Mathlib，不要随意改（第 10 节） |
| 提问 | MWE、`extract_goal`、Show Setup Information | 在 Zulip 求助之前（第 11 节） |
-/

/-!
## 延伸阅读

- Lean 参考手册 4.35.0（<https://lean-lang.org/doc/reference/4.35.0/>）。注意写 `4.35.0`，不要写 `latest`，
  后者已是更新的版本。第 5 章 *Source Files and Modules*：模块系统、`public`、`@[expose]`；第 3.6 节：
  `#guard_msgs`；第 25 章 *Build Tools and Distribution*：25.1 节 Lake（含 `lake update`），25.2 节 Elan。
  中文读者可对照社区译本 Lean-zh《Lean 语言参考手册》（章节编号以译本为准）。
- VS Code 扩展手册 `vscode-lean4/manual/manual.md`（<https://github.com/leanprover/vscode-lean4>）：
  *InfoView*、*File restarting*、*Troubleshooting*。
- Mathlib 缓存说明：`.lake/packages/mathlib/Cache/README.md`；Zulip 的 MWE 页面
  <https://leanprover-community.github.io/mwe.html>，社区准则
  <https://leanprover-community.github.io/community_guidelines.html>。
- 入门教材（未逐页核对具体小节）：*Theorem Proving in Lean 4*（<https://lean-lang.org/theorem_proving_in_lean4/>）
  的 *Dependent Type Theory* 一章；*Mathematics in Lean* 的 *Introduction* 一章里的 Getting Started
  （<https://leanprover-community.github.io/mathematics_in_lean/>）。
-/

end Lean4Learn.Ch01

end
