# Lean 4 系统学习（中文教材）

面向数学专业读者的 Lean 4 + Mathlib 系统教材：从完成 Natural Number Game 之后起步，目标是能用 Mathlib 独立形式化研究级引理（概率、随机图、大偏差方向），并理解 Lean 的元编程与内部机制。

- 讲解用中文，代码、标识符与引理名用英文；术语见 [docs/glossary.md](docs/glossary.md)。
- 每章是一个可编译的 `.lean` 文件：在 VS Code 里边读边改边看 infoview。练习留 `sorry`，答案在 `Solutions/`。
- 所有代码锁定 **Lean `v4.35.0` + Mathlib `v4.35.0`**（commit `56a0058`），并通过 `lake build`。每条关于 Lean/Mathlib 行为的断言都有同文件内的编译示例作证，真实错误信息用 `#guard_msgs` 固定。

## 目录与进度

完整大纲（28 章，五部分）见 [docs/outline.md](docs/outline.md)。

| 部分 | 章 | 状态 |
|---|---|---|
| I 语言与证明的基础 | 1–8 | **已完成**（`Lean4Learn/Part1/`，114 道练习，答案齐全） |
| II 证明工程 | 9–15 | **已完成**（`Lean4Learn/Part2/`，105 道练习，答案齐全） |
| III 测度、概率与图 | 16–19 | 待写 |
| IV 研究方向 capstone | 20–23 | 待写（20–22 章的核心定理已有编译通过的原型） |
| V 元编程、内部机制与编程 | 24–28 | 写作中 |

第 I 部分各章：

1. [环境、工作流与第一份文件](Lean4Learn/Part1/Ch01_Setup.lean)
2. [从 NNG 到 Mathlib：计算与重写](Lean4Learn/Part1/Ch02_Calculation.lean)
3. [类型、项与命题](Lean4Learn/Part1/Ch03_TypesTermsProps.lean)
4. [策略即构造项：逻辑与量词](Lean4Learn/Part1/Ch04_Tactics.lean)
5. [等式、simp 与证明的骨架](Lean4Learn/Part1/Ch05_EqualitySimp.lean)
6. [归纳类型、结构体与递归](Lean4Learn/Part1/Ch06_InductiveTypes.lean)
7. [集合、函数与子类型](Lean4Learn/Part1/Ch07_SetsFunctions.lean)
8. [类型类与代数结构（使用者视角）](Lean4Learn/Part1/Ch08_TypeClasses.lean)

第 II 部分各章：

9. [在 Mathlib 中找到你要的引理](Lean4Learn/Part2/Ch09_FindingLemmas.lean)
10. [自动化策略全景与选择](Lean4Learn/Part2/Ch10_Automation.lean)
11. [不等式与实数](Lean4Learn/Part2/Ch11_Inequalities.lean)
12. [有限和、计数与组合](Lean4Learn/Part2/Ch12_Finsets.lean)
13. [证明的组织、调试与风格](Lean4Learn/Part2/Ch13_ProofEngineering.lean)
14. [滤子与极限：Mathlib 的分析语言](Lean4Learn/Part2/Ch14_Filters.lean)
15. [构造结构与层次结构（设计者视角）](Lean4Learn/Part2/Ch15_Hierarchies.lean)

## 环境准备（Windows）

详细步骤在第 1 章。概要：

```bash
scoop install elan          # Lean 版本管理器；其他平台见 https://lean-lang.org/install/
code --install-extension leanprover.lean4
git clone <本仓库> && cd lean4-learn
lake exe cache get          # 下载预编译的 Mathlib（约 5–7 GB，放在 .lake/）
lake build                  # 编译全书（含练习的 sorry 警告属正常）
```

然后用 VS Code 打开仓库文件夹（File → Open Folder），打开 `Lean4Learn/Part1/Ch01_Setup.lean` 开始。

## 使用建议

- 按章顺序读；每章末尾有「小结」速查表与「延伸阅读」。
- 练习命名 `ex_<章>_<序号>`，难度 ★/★★/★★★；先自己做，再对照 `Solutions/`（陈述逐字相同）。
- 单独检查一个文件：`lake env lean Lean4Learn/Part1/Ch02_Calculation.lean`（注意 `lake env lean` 不读取 `lakefile.toml` 的 `leanOptions`，需要时加 `-DautoImplicit=false -Dpp.unicode.fun=true`）。
- 不要运行 `lake update`：它会解除 Mathlib 的版本锁定。

## 仓库结构

```
Lean4Learn/PartN/ChNN_*.lean   正文章节（可编译；练习含 sorry）
Solutions/PartN/ChNN_*.lean    练习答案（无 sorry；lake build Solutions --wfail 通过）
docs/outline.md                全书大纲与各章规格
docs/style.md                  作者规范（文件头、断言须有示例、练习镜像等）
docs/glossary.md               中英术语表与记号读法
lakefile.toml, lean-toolchain  版本锁定
```

## 许可

待定。
