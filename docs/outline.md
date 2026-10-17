# 《Lean 4 系统学习》教材大纲（v0.2，2026-10-17）

> 目标读者：数学本科/研究生，已完成 Natural Number Game，熟悉 C，无函数式编程与依值类型论背景。
> 学习终点：能用 Mathlib 独立形式化研究级引理（概率、随机图、大偏差方向），读懂 Mathlib 源码，并具备向 Mathlib 贡献的工作流；额外覆盖元编程与 Lean 内部机制。
> 版本锁定：Lean `v4.35.0` + Mathlib `v4.35.0`（commit `56a0058`）。所有代码在此版本下通过 `lake build`。参考手册引用版本固定页：<https://lean-lang.org/doc/reference/4.35.0/>。

## 载体与约定

- Repo 是一个 Lake 项目。每章一个可编译的 `.lean` 文件：`Lean4Learn/PartN/ChNN_Name.lean`；答案在 `Solutions/PartN/ChNN_Name.lean`。
- 中文讲解写在 `/-! ... -/` 文档注释里；代码、标识符、引理名、以及短注释用英文。术语按 `docs/glossary.md`。
- 每章结构：学习目标 → 核心概念（带可运行示例，注释里写出 infoview 应显示的目标）→ 常见错误（用 `#guard_msgs` 捕获真实错误信息）→ 练习（★ 基础 / ★★ 综合 / ★★★ 挑战，含前几章内容的复习）→ 小结速查表 → 延伸阅读（带版本/链接定位）。
- 练习以 `sorry` 留空，命名 `ex_<章>_<序号>`；`Solutions/` 中逐字复述同一陈述并给出完整证明，无 `sorry`。
- 每个文件只做窄 import（绝不 `import Mathlib`），文件头统一为当前 Mathlib 规范：`module` / `public import …` / `@[expose] public section … end`（元编程章用 `public meta import` / `public meta section`）。
- 时间预算：约 110–150 小时（正文 28 章 + 附录）。

## 第 I 部分　语言与证明的基础（Core Lean）

| 章 | 标题 | 学习目标 / 核心内容 | 依赖 |
|---|---|---|---|
| 1 | 环境、工作流与第一份文件 | Windows 上 elan（Scoop）/VS Code/Lean 4 扩展；打开本 repo；infoview 读法；Unicode 输入；`lake build`/`lake env lean`；文件头逐行解释（`module`、`public import`、`@[expose] public section`、`autoImplicit=false`）；`#check`/`#eval`/`#print`；MWE 与提问礼仪；版本锁定与 `lake update` 的危险；PowerShell 5.1 编码陷阱 | — |
| 2 | 从 NNG 到 Mathlib：计算与重写 | NNG 之后的第一课，先会"算"：`example`/`theorem` 的写法；在 `ℕ ℤ ℚ ℝ` 上用 `rw`/`calc`/`ring`/`norm_num`/`omega`/`linarith`/`positivity`/`simp` 做代数与不等式计算；`exact?` 初体验；读目标状态；`Nat` 减法/除法截断等"垃圾值"约定；`ℕ→ℝ` 的 `↑` 初识 | 1 |
| 3 | 类型、项与命题 | 一切皆有类型；`fun`、函数应用、柯里化；`Prop` vs `Type`；命题即类型、证明即项（Curry–Howard）；`theorem` 就是 `def`；隐式参数 `{}` 与 `@`；`Type*`、宇宙的最小必要知识；项模式证明 `→ ∧ ∨ ↔ ¬ ∀ ∃`（`⟨⟩`、`.1/.2`、`Or.inl`、`absurd`、`fun h ↦`） | 2 |
| 4 | 策略即构造项：逻辑与量词 | `by` 块与目标状态；`intro/exact/apply/refine ?_/constructor/left/right/rcases/obtain/rintro/exfalso/contradiction`；同一证明的项模式与策略模式对照；`·` 聚焦、`<;>`、`case`；`have/show/suffices`；经典逻辑：`by_contra`、`by_cases`、`push Not`（`push_neg` 已弃用）、`contrapose!`、`tauto`；`∃` 的 `use`/`obtain`；`∃!`；`constructor` 对 `Or` 的歧义警告 | 3 |
| 5 | 等式、simp 与证明的骨架 | `Eq` 与 `rfl`；定义相等 vs 命题相等（`0 + n` 不是 defeq）；`rw` 细节（`←`、`at`、不能进 binder、motive 错误与 `rw!`）；`simp` 机制（simp 集、`@[simp]`、`simp only`、`simp?`、`simpa`、`simp at`、`+arith` 配置语法、simp 正规形：`ne_eq`、`n+1`）；`calc` 完整语法；`congr`/`congrArg`/`subst`/`ext`/`funext`；`decide` 的边界 | 4 |
| 6 | 归纳类型、结构体与递归 | `inductive`、构造子、`match`；`cases`/`induction … with`（`0`/`n+1` 形式）；`Nat`/`List`/`Option` 的归纳本质；`structure`（4.18 新语法）、投影、匿名构造子、`deriving`；结构递归；`termination_by`/`decreasing_by` 初识、良基递归默认不可约；自定义函数的证明：`simp [f]`、`f.eq_1`、`unfold`、`fun_induction`；`Decidable`（4.35 新定义）与 `decide` | 5 |
| 7 | 集合、函数与子类型 | `Set α := α → Prop`，`{x \| p x}` 即 `Set.ofPred`，`Set.mem_ofPred_eq`（`mem_setOf_eq` 已弃用）；`∈ ⊆ ∩ ∪ ᶜ \`、`Set.ext`；`Function.Injective/Surjective/Bijective`、`Set.image/preimage`；`Subtype`、`↥`；`choose` 策略、`Classical.choose`；`Nonempty/Inhabited`；`Equiv` 初识；第一次真正使用 Mathlib 引理 | 6 |
| 8 | 类型类与代数结构（使用者视角） | `[Group G]`、实例、`inferInstance`、`#synth`；`Monoid/Group/Ring/Field` 与序的 mixin（`[Field K] [LinearOrder K] [IsStrictOrderedRing K]`，无 `LinearOrderedField`）；`ℕ ℤ ℚ ℝ` 从哪来；强制转换 `↑` 与 `norm_cast/push_cast/exact_mod_cast`、`Nat.cast_*`；`^` 的 `rightact%` 规则；`Decidable`、`DecidableEq`、`classical` 策略 vs `open Classical`、`noncomputable`、`ℝ` 不可计算 | 7 |

## 第 II 部分　证明工程（Proof engineering with Mathlib）

| 章 | 标题 | 学习目标 / 核心内容 | 依赖 |
|---|---|---|---|
| 9 | 在 Mathlib 中找到你要的引理 | 命名规范解码（snake_case/UpperCamelCase、`_of_`、`_iff_`、`pos/nonneg`、`₀`、`'`、`_left/_right`、点记号、`mul_le_mul_left` 的实际方向）；`exact?/apply?/rw?/simp?/hint/try?`；`#loogle`、`#leansearch`、Loogle 语法；文档站与源码阅读法（文档站/Loogle 领先于锁定版本，以本地源码为准）；弃用警告的读法、6 个月删除策略；`#min_imports`；Zulip 搜索 | 8 |
| 10 | 自动化策略全景与选择 | `simp` 深入（`simp_all`、`simp_rw`、discharger、循环与 no progress）；`ring/ring_nf/field_simp/field/linear_combination`（`polyrith` 已死）；`linarith/nlinarith/positivity/gcongr/bound/order`；`omega/lia/decide/norm_num` 的边界；`aesop`、`grind`（2026 主流收尾策略）、`tauto`、`abel`、`fun_prop`、`measurability`、`finiteness`、`continuity`；策略选择决策表 | 9 |
| 11 | 不等式与实数 | `ℝ` 基础、`abs`、`Real.sqrt`、`Real.exp/log` 常用引理；`le_trans` 链与 `calc + gcongr`；`div_le_iff₀` 族、`pow_le_pow_left₀` 族；`min/max`；`Finset.sum_le_sum`；Cauchy–Schwarz、AM–GM、Jensen（`ConvexOn.map_sum_le`）在 Mathlib 中的形态；`nlinarith` 提示技巧 | 10 |
| 12 | 有限和、计数与组合 | `Finset`、`∑ x ∈ s, f x`（`∑ x in s` 已不合法）、`Finset.sum_*`；`#s`、`filter`、`card_filter`、`sum_boole`；双计数；`Fintype`、`Fin n`、`Fin.sum_univ_succ`；`Nat.choose`、`powersetCard`；鸽巢；小情形 `decide`；`Finset.induction_on`（case 名）；`Nat.card/Set.ncard/Fintype.card/Finset.card` 的换算 | 11 |
| 13 | 证明的组织、调试与风格 | 自顶向下 `sorry` 分解；`have/suffices/obtain/set/wlog/generalize`；`induction … generalizing`、强归纳（本书统一用 `induction n using Nat.strong_induction_on with \| _ n ih`）、`Nat.le_induction`；`fin_cases/interval_cases`；`convert/congr!`；`extract_goal`；读懂错误信息；`maxHeartbeats`、`set_option trace`；`conv`；Mathlib 风格指南与 linter | 12 |
| 14 | 滤子与极限：Mathlib 的分析语言 | `Filter`、`Tendsto`、`atTop`、`𝓝`、`∀ᶠ`、`filter_upwards`；ε–N 与滤子互译（`Metric.tendsto_atTop`）；极限的代数、夹逼、`Tendsto.comp`；常用序列极限引理（`tendsto_const_div_atTop_nhds_zero_nat` 等）；`limsup/liminf`、`Summable/tsum`、`IsBigO` 速览；`IsOpen/Continuous/Metric.ball` 最小集 | 13 |
| 15 | 构造结构与层次结构（设计者视角） | `structure/class/extends`、实例设计与优先级、`outParam`；真实的类链（`Semigroup → MulOne → Monoid → … → Group`）；`SetLike` 与子结构；态射与 bundled maps（`→+*`、`⇑`、`FunLike`）；商（`Setoid/Quotient/QuotientGroup`）；`variable` 语义（4.11 后）、`include/omit`；`@[to_additive]` 的使用；案例：自定义加权图结构并为其写实例 | 14 |

## 第 III 部分　测度、概率与图（Mathlib for probability and graphs）

| 章 | 标题 | 学习目标 / 核心内容 | 依赖 |
|---|---|---|---|
| 16 | 测度论基础 | `MeasurableSpace/MeasurableSet/Measure/volume`；`ae` 与 `∀ᵐ`；`μ.real` 与 ENNReal 的处理（`finiteness`、`ENNReal.toReal_*`）；`Measurable`、`measurability`/`fun_prop`；`∫⁻` 与 `∫`、`Integrable`、`MemLp`；垃圾值（`Measure.map` 非可测时为 dirac）；有限测度空间：`uniformOn`、`Measure.count`、`integral_fintype`；案例：`Fin n → Bool` 上的抛硬币 | 15 |
| 17 | 概率论基础 | `IsProbabilityMeasure`；随机变量、`μ[X]`/`𝔼[X]`；`IdentDistrib`、`HasLaw`；独立性 `IndepFun/iIndepFun`；`variance`/`Var[X; μ]`；Markov（`mul_meas_ge_le_integral_of_nonneg`）、Chebyshev（`meas_ge_le_variance_div_sq`）、`IndepFun.variance_sum`；分布 `Ber/Bin`（`PMF.*` 已弃用）、`gaussianReal`；`exists_iid`、乘积测度 `Measure.pi/infinitePi`；案例：Chebyshev ⇒ 弱大数律 | 16 |
| 18 | 图论 | `SimpleGraph`（`Std.Symm/Std.Irrefl` 字段）、`Adj`、`edgeSet/edgeFinset`、`degree`、握手引理；`Walk/Path/Reachable/Connected`、`IsTree`；团与独立集、着色；`Subgraph`；可判定性实例的处理；`aesop_graph`、小图 `decide`；Turán/正则性引理/Hall 的导览；案例：三角形计数的 `is3Clique_triple_iff` | 12 |
| 19 | 有限概率空间与概率方法 | `uniformOn` 与 `Finset.expect`（`𝔼 i ∈ s, f i`）；期望线性性；一阶矩原理 `exists_le_of_le_expect`；联合界 `measure_biUnion_finset_le`；`setBer` 随机子集；案例：Ramsey 下界 R(k,k) > 2^{k/2}（有限均匀模型） | 17, 18 |

## 第 IV 部分　研究方向 capstone

| 章 | 标题 | 学习目标 / 核心内容 | 依赖 |
|---|---|---|---|
| 20 | 随机图 G(n,p) 与一阶矩方法 | Mathlib 的 `SimpleGraph.binomialRandom`（`G(V, p)`，`p : unitInterval`）定义链；边的边缘分布 P(e ∈ G) = p；E[#edges] = C(n,2)p；E[#triangles] = C(n,3)p³；Markov ⇒ P(有三角形) ≤ C(n,3)p³；阈值上界：np → 0 ⇒ 以高概率无三角形。以 guided project 形式（分步 `sorry` + 答案） | 19 |
| 21 | 集中不等式：Chernoff 与 Hoeffding | `mgf/cgf`、`measure_ge_le_exp_mul_mgf`、`iIndepFun.mgf_sum`；`HasSubgaussianMGF`、Hoeffding 引理与不等式（Mathlib 现成）；应用：二项分布尾界、G(n,p) 中度的集中 | 17 |
| 22 | 大偏差入门：Cramér 型上界 | 手工定义 Λ(t)=cgf、Λ*(a)=sup_{t≥0}(ta−Λ(t))（`iSup`/`BddAbove`）；证明 P(S_n ≥ na) ≤ exp(−nΛ*(a))（iid 有界）；Bernoulli 情形的速率函数与相对熵（`klDiv` 无离散闭式，需手工）；Mathlib 缺什么（Cramér 定理、Sanov、LDP）与如何规划一个形式化项目 | 21, 14 |
| 23 | 从练习到研究：形式化项目方法论与贡献 Mathlib | blueprint 工作流；先写陈述后分解；API 设计（设计先于代码）；读 Mathlib PR；向 Mathlib 贡献（fork 流程、`lake exe lint-style`、弃用策略、AI 使用政策）；Zulip 礼仪与 MWE；项目卫生（版本锁定）；证明验证阶梯（`#print axioms`、`lake check`）；负责任地使用 AI 助手 | 20–22 |

## 第 V 部分　元编程、内部机制与编程

| 章 | 标题 | 学习目标 / 核心内容 | 依赖 |
|---|---|---|---|
| 24 | Lean 作为函数式编程语言 | 模式匹配、`List/Array/Option/String`（4.27 后 `String.Slice`）、`Std.HashMap`；`do` 记号（4.32 新 elaborator）；单子（`Option/Except/StateM/IO`）；`main` 与 `#eval`；`deriving`；`partial`、`termination_by`；随机数 `StdGen/randNat`；案例：模拟 G(n,p) 并统计度数 | 6 |
| 25 | 程序验证 | 递归函数性质证明、`fun_induction`、方程引理；`decide`/`decide +kernel`/`native_decide`（每次使用添加专属公理；Mathlib 禁止）；`Array` 下标与 `Fin`；`plausible` 找反例；`#guard`；`vcgen`（4.35，实验性）速览；案例：验证插入排序变体或 GCD | 24 |
| 26 | 记号、宏与语法扩展 | `notation/infix/prefix`（自动 unexpander）、`scoped/local`；`syntax + macro_rules`、`macro`、`declare_syntax_cat`；引用与反引用、卫生；策略宏；模块系统下的 `meta`（`public meta section`、辅助函数需 `meta def`）；案例：小型 DSL | 24 |
| 27 | 元编程：Expr、MetaM 与策略编写 | `Expr`、`MetaM`（`whnf/isDefEq/inferType/mkAppM`）、`TermElabM`、`elab`；`TacticM`、`getMainGoal`、`MVarId` 操作、`liftMetaTactic`；`Qq` 速览；`simproc`、`@[norm_num]/@[positivity]/@[aesop]` 扩展；`to_additive` 原理；`@[app_delab]`；Mathlib 策略文件解剖；案例：写一个真正的策略 | 26 |
| 28 | 类型论与内核机制 | 依值类型（Π/Σ）、宇宙多态、`Sort u`、`Prop` 非直谓、无累积性、证明无关与子单元消去；归纳类型与递归子、非递归结构体的 eta、`Quot`；公理（`propext/Classical.choice/Quot.sound`、`#print axioms`）；定义相等与六级透明度、`whnf`、内核加速的 `Nat` 运算；精译器 vs 内核；合一与实例合成（tabled、优先级、`outParam`）；强制转换机制；模块系统内部（三种 olean、`@[expose]`、meta 阶段）；heartbeats；证明验证阶梯与 2026 内核修复 | 27 |

## 附录

- A 策略速查表（中英）　B 术语表（`docs/glossary.md`）　C 记号 → 所需 `open` 对照表　D Lean 3→4 与 2024–2026 常见更名表　E Unicode 输入表　F 延伸阅读（含 Lean-zh 中文译本）　G Windows 故障排查

## 设计原则（给作者与审稿者）

1. 一切行为性断言都要有同文件内的编译示例作证（含用 `#guard_msgs` 固定的错误信息）。
2. 计算先行（第 2 章），理论就近引入：类型论概念只在首次需要时讲，讲透一次，后续引用。
3. 项模式与策略模式双视角贯穿第 3–6 章，直到读者能把任何策略证明"翻译"成项。
4. 第 9 章之后所有示例使用真实 Mathlib 名字与真实数学对象（`ℝ`、`Finset`、`Measure`），不再用玩具类型。
5. 每章练习至少三分之一复习前几章内容；capstone 章用 guided project（陈述给定、步骤留空）。
6. 主动标注 2024–2026 的更名与弃用（`push Not`、`Set.ofPred`、`field`、`integral_finsetSum`、`uniformOn` 取代 `PMF.uniformOfFintype`、`ite_eq_left` 取代 `if_pos` 等），并教读者自己读弃用警告。
7. 所有引理名以本地 Mathlib 源码为准（文档站与 Loogle 领先于锁定版本）。
