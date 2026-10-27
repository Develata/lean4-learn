# 附录 D　Lean 3→4 与 2024–2026 常见更名表

旧教程、旧项目与大模型的输出里常出现已经改名、弃用或删除的写法。本附录把读者最可能遇到的几类列成「旧写法 →
锁定版本里的写法」对照，并给出证据：本书演示它的章节，或源码里的 `@[deprecated (since := …)]` 等标记（文件:行）；「本书」一栏的「12 §3」即第 12 章 §3。
内容对应 Lean `v4.35.0` + Mathlib `v4.35.0`（commit `56a0058`）。路径 `Mathlib/…` 指
`.lake/packages/mathlib/Mathlib/…`，`Init/…`、`Lean/…`、`Std/…` 指 Lean 核心源码 `src/lean/` 下的文件。

**读法。**

- 「弃用自」一栏只填源码里写明的日期；源码没有日期而本书正文给出版本或日期时，注明「据第 N 章」；什么都没有就写「—」。
- Mathlib 的政策是弃用的别名约 6 个月后可以删除（第 9 章 §13）。所以「已删除」的名字只会报 `Unknown identifier` /
  `Unknown constant`，不会告诉你新名字；遇到这类报错先怀疑改名，按第 9 章 §8 的流程找新名字。
- Lean 3 的旧语法在 4.35 是**解析错误**。`#guard_msgs` 捕获不到解析错误（第 2 章 §2），本书也没有编译这些写法，
  所以 §1 里标「未实测」的行只是对照，报错的具体措辞以你自己机器上的输出为准。

## 1. Lean 3 语法

| 旧写法 | 现行写法 | 证据 | 本书 |
|---|---|---|---|
| `begin … end` | `by` 加缩进的策略块，策略之间不用逗号 | 未实测 | 全书写法 |
| `λ x, f x` | `fun x ↦ f x`（或 `fun x => f x`） | `λ x => …` 仍能解析，但 Mathlib 的 `linter.style.lambdaSyntax` 警告（`Mathlib/Tactic/Linter/Style.lean:300`）；带逗号的 Lean 3 形式未实测 | 13 §8.1 演示警告；3 §2 |
| `assume h,` | `intro h` | 未实测 | 4 §2 |
| `cases h with a b` | `obtain ⟨a, b⟩ := h`、`rcases h with ⟨a, b⟩`，或 `cases h with \| intro a b => …` | 解析错误，未实测；Mathlib 的 `cases'` 仍在，但被 `linter.style.cases` 标出（`Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean:63`、`:205`） | 4 §3、§4 |
| `induction n with d hd` | `induction n with \| zero => … \| succ d hd => …` | 解析错误 `lean.inductionWithNoAlts`（第 2 章 §2 的说明，未编译）；`induction'` 被 `linter.style.induction` 标出（同上 `:206`） | 2 §2 |
| `refine ⟨_, _⟩`（`_` 变成新目标） | `refine ⟨?_, ?_⟩` | 4 §10 ① 演示报错 `don't know how to synthesize placeholder`；`refine'` 被 `linter.style.refine` 标出（同上 `:53`、`:204`） | 4 §10 ① |
| `∑ x in s, f x` | `∑ x ∈ s, f x` | 约束子语法里没有 `in`（`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:108`、`:180`）；报错未实测 | 12 §3 |
| `dec_trivial`、`decide!` | `decide`、`decide +kernel` | 核心、Batteries、Mathlib 源码里没有这两个语法（`rg` 无结果）；报错未实测 | 5 §3；25 §5 |
| `library_search` | `exact?`（还有 `apply?`、`rw?`、`hint`） | 同上，源码里没有该语法；报错未实测 | 2 §12；9 §9 |
| `structure S :=` 换行 `a : ℕ`（Lean 4 早期写法） | `structure S where` 换行 `a : ℕ` | 4.35 里是弃用警告（据第 6 章，4.14 起弃用；源码无 `since`）；Lean 3 的 `structure S := (a : ℕ)` 未实测 | 6 §11 第 4 条 |

## 2. 策略、语法与选项

| 旧写法 | 现行写法 | 弃用自 / 状态 | 证据 | 本书 |
|---|---|---|---|---|
| `push_neg` | `push Not` | 2026-03-29，警告 | 日期只写在注释里，不是 `@[deprecated]` 属性：`Mathlib/Tactic/Push.lean:283`–`284` | 4 §7 |
| `simp_arith` | `simp +arith` | 据第 2 章：v4.18（2025-04）；4.35 里直接**报错** | `Lean/Elab/Tactic/SimpArith.lean:42`（`throwError`，无 `since`） | 2 §14 第 4 条；5 §7 |
| `cutsat` | `lia` | 据第 10 章：v4.27.0（2026-01-24）改名；警告 | `Lean/Elab/Tactic/Grind/Main.lean:466`（`logWarning`，无 `since`） | 10 §9 ① |
| `polyrith` | 自己写 `linear_combination`，或 `grobner` | 外部服务关闭，调用即报错；无日期 | `Mathlib/Tactic/Polyrith.lean` | 10 §9 ② |
| `peel` | `gconvert` 或 `congr!` | 2026-08-03 | `Mathlib/Tactic/Peel.lean:93`（`deprecated_syntax`） | 10 §9 ③ |
| `mvcgen` | `vcgen`（实验性，`set_option experimental.vcgen true`） | 2026-08-21 | `Std/Tactic/Do/Syntax.lean:440`（`deprecated_syntax`） | 25 §10 |
| `rwa [h] at h₁ h₂`、`rwa … at *` | `rw [h] at … <;> assumption`；`rwa` 只作用于一个位置 | 2026-08-27 | `Init/Tactics.lean:663`（`deprecated_syntax rwaAtLegacyLocation`） | 本书未涉及 |
| 对 `Or` 用 `constructor` | `left` / `right`（或 `constructor!`） | 4.35 起警告 | 演示于 4 §4 | 4 §4 |
| `refine'`、`cases'`、`induction'`、`admit` | `refine`、`obtain`/`rcases`/`cases`、`induction`、`sorry` | 不是弃用属性，而是 Mathlib 的一个 linter（代码检查器）把它们标为过时语法 | `Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean:204`–`207` | 本书未涉及（`refine ⟨_, _⟩` 见 §1） |
| `set_option linter.style.nativeDecide` | `linter.style.native` | 2026-08-28 | `Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean:97` | 25 §5 |
| `for i in [0:n]` | `for i in 0...n`（半开），`0...=n`（闭） | 旧写法在核心源码里仍保留，本书未实测 | — | 24 §4 |

## 3. Mathlib 引理与定义

前两类是机械的整族改名：`setOf` → `ofPred`/`setOfPred`（2026-07-09）、`diff` → `sdiff`（2026-06-03）、
`finset_sum` → `finsetSum`（2026-04-08）。看到旧名，先按规则改一次再 `#check`。

| 旧名 | 新名 | 弃用自 | 证据 | 本书 |
|---|---|---|---|---|
| `setOf` | `Set.ofPred`（记号 `{x \| p x}` 不变） | 2026-07-09 | `Mathlib/Data/Set/Defs.lean:68` | 7 §1 |
| `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` | 2026-07-09 | `Mathlib/Data/Set/Operations.lean:80` | 7 §11 第 1 条；9 §13 |
| `Set.eq_mem_setOf` | `Set.eq_mem_ofPred` | 2026-07-09 | `Mathlib/Data/Set/Operations.lean:89` | 9 练习 9.12 |
| `measurableSet_setOf` | `measurableSet_setOfPred` | 2026-07-09 | `Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean:876` | 16 §1 |
| `Set.mem_diff` | `Set.mem_sdiff` | 2026-06-03 | `Mathlib/Data/Set/Operations.lean:125` | 7 §3、§11 第 1 条 |
| `integral_finset_sum` | `integral_finsetSum` | 2026-04-08 | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:253` | 16 §7；20 §6（只用新名） |
| `integrable_finset_sum` | `integrable_finsetSum` | 2026-04-08 | `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:452` | 20 §6（只用新名） |
| `memLp_finset_sum` | `memLp_finsetSum` | 2026-04-08 | `Mathlib/MeasureTheory/Function/LpSeminorm/TriangleInequality.lean:190` | 17 §9（只用新名） |
| `PMF.bernoulli` | `ProbabilityTheory.bernoulliMeasure`（记号 `Ber`；类型也变了） | 2026-04-07 | `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:298` | 17 §7；17「常见错误」3 |
| `PMF.binomial` | `ProbabilityTheory.binomial`（记号 `Bin`） | 2026-04-07 | `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean:28` | 17 §7 |
| `PMF.uniformOfFintype` | `MeasureTheory.Measure.uniformOfFinset` | 2026-10-04 | `Mathlib/Probability/Distributions/Uniform.lean:272` | 17 §7（本书在有限空间上用 `uniformOn Set.univ`，19 §4） |
| `Memℒp` | `MemLp` | 已删除 | 17「常见错误」3 演示 `Unknown identifier` | 17「常见错误」3 |
| `div_le_iff`（根命名空间） | `div_le_iff₀` | 已删除 | 9 §15 ① 演示；新名在 `Mathlib/Algebra/Order/GroupWithZero/Basic.lean:1132` | 9 §15 ① |
| `pow_le_pow_left` | `pow_le_pow_left₀` | 已删除 | 11 §11 第 2 条演示；新名在同上文件 `:513` | 11 §11 第 2 条 |
| `one_div_le_one_div_iff` | `one_div_le_one_div` | 已不存在 | Mathlib 源码中无此名（`rg` 无结果）；新名在 `Mathlib/Algebra/Order/Field/Basic.lean:93` | 11 §11 第 2 条（文字） |
| `Finset.card_le_of_subset` | `Finset.card_le_card` | 已删除，无别名 | 12 §12 第 1 条演示；`Mathlib/Data/Finset/Card.lean:66` | 12 §12 第 1 条 |
| `Finset.card_insert_of_not_mem` | `Finset.card_insert_of_notMem` | 已不存在 | Mathlib 源码中无旧名（`rg` 无结果）；新名在 `Mathlib/Data/Finset/Card.lean:104` | 12 §5（文字） |
| `Filter.eventually_of_forall` | `Filter.Eventually.of_forall` | 已删除 | 14「常见错误」2 演示；`Mathlib/Order/Filter/Basic.lean:663` | 14 §3 |
| `LinearOrderedField K` | `[Field K] [LinearOrder K] [IsStrictOrderedRing K]` | 类已不存在 | Mathlib 源码里没有 `LinearOrderedField` 的声明，只剩区段名与注释（`rg`）；`IsStrictOrderedRing` 在 `Mathlib/Algebra/Order/Ring/Defs.lean:74` | 8 §5 |
| `List.Sorted (· ≤ ·) l` | `l.Pairwise (· ≤ ·)` | 已删除 | 25 §9 演示 `Unknown constant` | 25 §9 |
| `Sym2.mk (a, b)` | `Sym2.mk a b`，即 `s(a, b)` | 签名改了 | 18 §16 第 1 条演示类型错误 | 18 §3 |
| `SimpleGraph` 的 `symm := fun a b h ↦ …` | `symm` 是结构体 `Std.Symm Adj`，写 `symm.symm := …` | 签名改了 | 18 §16 第 2 条 | 18 §1 |
| `if_pos`、`if_neg`、`dif_pos` | `ite_eq_left`、`ite_eq_right`、`dite_eq_left` | 2026-07-21 | `Init/Core.lean:1184`（`if_pos`；其余在附近） | 本书未涉及 |

**同名不同义。** 有的旧名字仍然存在，意思却变了，报的是类型错误而不是未知标识符。第 9 章 §15 ② 与第 11 章
§11 第 1 条演示了 `mul_le_mul_left`：它现在要求 `MulRightMono`，`ℝ` 没有这个实例；`ℝ` 上用
`mul_le_mul_of_nonneg_left`。`open Nat` 之后核心的 `Nat.mul_le_mul_left` 与它同时候选，参数顺序相反（9 §15 ③）。

## 4. 模块路径与核心库 API

| 旧写法 | 现行写法 | 弃用自 | 证据 | 本书 |
|---|---|---|---|---|
| `import Mathlib.Data.Real.Basic` | `Mathlib.Basic.Real.Basic` | 2026-08-27 | `Mathlib/Data/Real/Basic.lean:5`（`deprecated_module`） | 9 §13 |
| `Mathlib.Data.ENNReal.Basic` | `Mathlib.Basic.ENNReal.Basic` | 2026-08-27 | `Mathlib/Data/ENNReal/Basic.lean:5` | 16「延伸阅读」 |
| `Mathlib.Combinatorics.SimpleGraph.Coloring` | `…SimpleGraph.Coloring.Vertex` | 2026-04-02 | `Mathlib/Combinatorics/SimpleGraph/Coloring.lean:5` | 18「延伸阅读」 |
| `Mathlib.Combinatorics.SimpleGraph.Walks.Basic` | `…SimpleGraph.Walk.Basic` | 2026-04-01 | `Mathlib/Combinatorics/SimpleGraph/Walks/Basic.lean:5` | 18「延伸阅读」 |
| `s.trim`（`String.trim`） | `s.trimAscii.copy` | 已不存在 | 24 §2 演示 `Invalid field trim` | 24 §2 |
| `s.drop n : String` | 4.27 起返回 `String.Slice`，要 `String` 时 `.copy` | — | 24 §2；24 §12 第 1 条 | 24 §2 |
| `(μ s).toReal` | 仍然合法；现代引理多写 `μ.real s`（`measureReal_def`），不是改名 | — | 16 §4 | 16 §4 |

写法改变的完整对照见第 9 章 §13（怎样读弃用警告与 `since` 日期）；具体某个名字是否还在，以本地 `#check`
或 `rg` 锁定版本的源码为准，不以网上文档为准（第 9 章 §10）。
