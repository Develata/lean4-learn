module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Notation
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.StrongLaw
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 17 章　概率论基础

在 Mathlib 里，probability space（概率空间）不是单独的一个类：它是一个 measurable space（可测空间）
`Ω`、其上的 measure（测度）`μ`，再加上 probability measure（概率测度）的类型类假设
`[IsProbabilityMeasure μ]`。random variable（随机变量）是 `Ω` 上的函数，expectation（期望）是它的积分，
independence（独立）与 identically distributed（同分布）是关于 `μ` 的谓词，variance（方差）是
中心化平方的期望。本章把第 16 章的测度论语言翻译成概率语言，终点是用 Chebyshev's inequality
（切比雪夫不等式）完整证明 weak law of large numbers（弱大数定律）；strong law of large numbers
（强大数定律）只读陈述，central limit theorem（中心极限定理）只给源码位置（延伸阅读）。

## 学习目标
- 会写 `(μ : Measure Ω) [IsProbabilityMeasure μ]` 并做基本计算；知道 `ℙ` 就是 `volume`。
- 会读 `μ[X]`、`𝔼[X]`（`open ProbabilityTheory` 或 `open scoped ProbabilityTheory`），知道它们
  展开成什么积分，知道不可积时期望取 junk value（垃圾值）`0`。
- 会用 `HasLaw X ν μ` 与 `IdentDistrib X Y μ ν` 搬运期望、方差与概率；会写 `X ⟂ᵢ[μ] Y`、
  `iIndepFun X μ`，并说明省略 `μ` 时 `by volume_tac` 会悄悄取 `volume`。
- 会读 `Var[X; μ]`，用 `variance_eq_sub`、`IndepFun.variance_sum`（带 `Set.Pairwise` 与
  `MemLp X 2 μ`）；知道有限测度下 `X` almost everywhere（几乎处处）强可测而不属于 L² 时方差是 `0`。
- 会用 Markov's inequality（马尔可夫不等式）与切比雪夫不等式，并把后者改写成 `μ.real` 值。
- 认识 `Ber`、`Bin`、`gaussianReal`、`Measure.pi`、`Measure.infinitePi` 与 `exists_iid`。
- 会完整证明 pairwise independent（两两独立）、同分布的 L² 随机变量的弱大数定律。

## 前置知识
第 4、5 章（量词与 `calc`）；第 6 章（结构体）；第 7 章（`Subtype`、`⁻¹'`）；第 9 章（找引理）；
第 10 章（`positivity`、`fun_prop`）；第 11 章（`div_le_iff₀`）；第 12 章（`∑ i ∈ s`）；第 14 章
（`Tendsto`、`atTop`）；第 15 章（`omit … in`）；第 16 章（`Measure`、`μ.real`、`ae`、`Measure.map`、
`Integrable`、`MemLp`、积分的线性性、`Set.indicator`；本章不再重讲）。
-/

@[expose] public section

namespace Lean4Learn.Ch17

section Main

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
## 1. 概率空间与概率测度

数学上，概率空间是三元组 `(Ω, 𝓕, ℙ)`，`ℙ(Ω) = 1`。在 Mathlib 里 `𝓕` 是类型类 `MeasurableSpace Ω`，
`ℙ` 是普通的 `Measure Ω`，条件 `ℙ(Ω) = 1` 是只含一个字段 `measure_univ` 的类
`IsProbabilityMeasure μ`；做成类型类，需要「有限测度」的引理就能自动获得实例。
-/

section Space

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

example [IsProbabilityMeasure μ] : μ Set.univ = 1 := measure_univ
example [IsProbabilityMeasure μ] (s : Set Ω) : μ s ≤ 1 := prob_le_one

-- 实数值版本：`μ.real s = (μ s).toReal`（第 16 章）
example [IsProbabilityMeasure μ] (s : Set Ω) : μ.real s ≤ 1 := measureReal_le_one
example [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s) : μ.real s + μ.real sᶜ = 1 :=
  probReal_add_probReal_compl hs

-- 补集公式 `μ sᶜ = 1 - μ s` 靠可加性 `μ s + μ sᶜ = 1`，所以需要 `s` 可测
example [IsProbabilityMeasure μ] (s : Set Ω) (hs : MeasurableSet s) : μ sᶜ = 1 - μ s :=
  prob_compl_eq_one_sub hs

-- 概率测度自动是有限测度，故 `μ s ≠ ∞`
example [IsProbabilityMeasure μ] (s : Set Ω) : μ s ≠ ∞ := measure_ne_top μ s

/-!
不是所有测度都是概率测度。`ℝ` 上的 `volume`（Lebesgue measure（勒贝格测度））把整条实轴测成 `∞`，
所以它不是：
-/

example : ¬ IsProbabilityMeasure (volume : Measure ℝ) := by
  intro h
  have h1 : (volume : Measure ℝ) Set.univ = 1 := measure_univ
  rw [Real.volume_univ] at h1
  exact ENNReal.top_ne_one h1

end Space

/-!
另一种写法是用 `MeasureSpace Ω`：它自带一个默认测度 `volume`，记号 `ℙ` 就是 `volume`（本章的
概率记号靠 `open ProbabilityTheory` 或 `open scoped ProbabilityTheory` 启用，见「常见错误」第 1 条）。
此时「概率空间」就是 `[MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]`。
本章的定理大多取显式的 `μ`，这样同一个 `Ω` 上可以同时处理几个不同的测度（原测度、像测度）。
-/

example {Ω : Type*} [MeasureSpace Ω] : (ℙ : Measure Ω) = volume := rfl

/-!
## 2. 随机变量与期望

数学上随机变量是可测函数；在 Lean 里它只是函数 `X : Ω → ℝ`，可测性（常常只要几乎处处可测）
作为单独的假设出现。期望是第 16 章的 Bochner 积分。记号 `μ[X]` 是 `ProbabilityTheory` 里的 `scoped`
宏，要 `open ProbabilityTheory` 或 `open scoped ProbabilityTheory` 才能用（「常见错误」第 1 条），
展开成 `∫ x, ↑(X x) ∂μ`（`X` 取值于 `ℝ` 时 `↑` 是恒等，下面的 `rfl` 成立）；`𝔼[X]` 是对 `volume`
的期望。第 16 章 §7 的积分引理（`integral_add`、`integral_const_mul`、`integral_undef`）原样适用：
-/

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

example : μ[X] = ∫ ω, X ω ∂μ := rfl
example {Ω' : Type*} [MeasureSpace Ω'] (X : Ω' → ℝ) : 𝔼[X] = ∫ ω, X ω ∂ℙ := rfl
example (h : ¬ Integrable X μ) : μ[X] = 0 := integral_undef h

-- 常数的期望（概率测度下 `μ.real univ = 1`）
example [IsProbabilityMeasure μ] (c : ℝ) : μ[fun _ ↦ c] = c := by simp

-- 概率是 indicator function（指示函数）的期望：`P(A) = 𝔼[1_A]`（`integral_indicator_one`）
example {s : Set Ω} (hs : MeasurableSet s) : μ[s.indicator (1 : Ω → ℝ)] = μ.real s :=
  integral_indicator_one hs

end Expectation

/-!
## 3. 分布：`HasLaw` 与 `IdentDistrib`

随机变量 `X : Ω → E` 的 distribution（分布）是前推测度 `μ.map X`（第 16 章）。「`X` 在 `μ` 下的
分布是 `ν`」写成结构体 `HasLaw X ν μ`，两个字段：`X` 几乎处处可测，以及 `μ.map X = ν`。注意
**参数次序**：分布 `ν` 在前，底测度 `μ` 在后（`μ` 有默认值 `by volume_tac`，见 §4 的陷阱）。
同分布 `IdentDistrib X Y μ μ'` 是两者（可在不同空间上）都几乎处处可测且像测度相等。
-/

section Law

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}
  {μ' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ} {ν : Measure ℝ}
example (hX : HasLaw X ν μ) : μ.map X = ν := hX.map_eq

-- 事件概率搬到分布上：`P(X ≤ 3) = ν((-∞, 3])`
example (hX : HasLaw X ν μ) : μ.real {ω | X ω ≤ 3} = ν.real {x | x ≤ 3} :=
  hX.measureReal_eq (p := fun x ↦ x ≤ 3) (measurableSet_Iic (a := (3 : ℝ)))

-- 分布相同 ⇒ 同分布；同分布 ⇒ 期望、事件概率相同（方差见 §5）
example (hX : HasLaw X ν μ) (hY : HasLaw Y ν μ') : IdentDistrib X Y μ μ' := hX.identDistrib hY
example (h : IdentDistrib X Y μ μ') : μ[X] = μ'[Y] := h.integral_eq
example (h : IdentDistrib X Y μ μ') {s : Set ℝ} (hs : MeasurableSet s) :
    μ (X ⁻¹' s) = μ' (Y ⁻¹' s) := h.measure_mem_eq hs

end Law

/-!
## 4. 独立性

`X ⟂ᵢ[μ] Y`（`IndepFun X Y μ`）表示 `X`、`Y` 生成的 σ-代数独立，展开就是乘积公式
（`indepFun_iff_measure_inter_preimage_eq_mul`）。`iIndepFun X μ` 表示整族 mutually independent
（相互独立），两两独立是 `Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j`。相互独立蕴含两两独立
（`iIndepFun.indepFun`）；反方向不成立（经典反例：两个独立的公平比特与其异或，本书不形式化）。
-/

section Independence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ} {ι : Type*}
  {Z : ι → Ω → ℝ}
example (h : IndepFun X Y μ) : X ⟂ᵢ[μ] Y := h
example (h : X ⟂ᵢ[μ] Y) {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (X ⁻¹' s ∩ Y ⁻¹' t) = μ (X ⁻¹' s) * μ (Y ⁻¹' t) :=
  indepFun_iff_measure_inter_preimage_eq_mul.1 h s t hs ht
example (h : iIndepFun Z μ) {i j : ι} (hij : i ≠ j) : Z i ⟂ᵢ[μ] Z j := h.indepFun hij

-- 一个独立族自动迫使 `μ` 是概率测度：`iIndepFun` 里包含了 `μ univ = 1`
example (h : iIndepFun Z μ) : IsProbabilityMeasure μ := h.isProbabilityMeasure

-- 独立 ⇒ 乘积的期望等于期望的乘积。这条引理不要可积，只要几乎处处强可测：不可积的情形由
-- 积分的垃圾值约定（`integral_undef`）处理；数学上有意义的情形仍要可积。
example (h : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    μ[X * Y] = μ[X] * μ[Y] := h.integral_mul_eq_mul_integral hX hY

-- 独立性沿可测函数保持
example (h : X ⟂ᵢ[μ] Y) : (fun ω ↦ 2 * X ω) ⟂ᵢ[μ] (fun ω ↦ 3 * Y ω) :=
  h.comp (by fun_prop : Measurable fun x : ℝ ↦ 2 * x) (by fun_prop : Measurable fun x : ℝ ↦ 3 * x)

end Independence

/-!
### 陷阱：省略 `μ` 时悄悄取 `volume`

`IndepFun`、`iIndepFun`、`HasLaw`、`IdentDistrib`、`Integrable`、`MemLp` 的测度参数都带默认值
`(μ : Measure Ω := by volume_tac)`：省略时 Lean 找 `MeasureSpace Ω` 实例并取其 `volume`。有这样的
实例时**不会报错**，你证明的是关于 `volume` 的陈述（下面各举一例）；没有时报错（「常见错误」第 2 条）：
-/

section VolumeTrap

variable {Ω : Type*} [MeasureSpace Ω] (ν : Measure Ω) (U V : Ω → ℝ)

-- 省略 `μ`：悄悄成了 `volume`
example (h : IndepFun U V) : IndepFun U V volume := h
example {ι : Type*} (Z : ι → Ω → ℝ) (h : iIndepFun Z) : iIndepFun Z volume := h
example (κ : Measure ℝ) (h : HasLaw U κ) : HasLaw U κ volume := h
example (h : IdentDistrib U V) : IdentDistrib U V volume volume := h
example (h₁ : Integrable U) (h₂ : MemLp U 2) : Integrable U volume ∧ MemLp U 2 volume := ⟨h₁, h₂⟩

-- 想要的是 `ν`，但假设里漏写了 `ν`
/--
error: Type mismatch
  h
has type
  U ⟂ᵢ V
but is expected to have type
  U ⟂ᵢ[ν] V
-/
#guard_msgs in
example (h : IndepFun U V) : IndepFun U V ν := h

end VolumeTrap

/-!
## 5. 方差

`variance X μ`（记号 `Var[X; μ]`，打开方式同 `μ[X]`）定义为
`(evariance X μ).toReal`，其中 `evariance` 是 `ℝ≥0∞` 值的 `∫⁻ ‖X - μ[X]‖ₑ ^ 2 ∂μ`。用 `ℝ≥0∞`
是为了让「方差为无穷」有意义；转成 `ℝ` 之后无穷变成垃圾值 `0`。哪些方差等式要
`MemLp X 2 μ`（`X` 属于 L²，即平方可积）？只涉及定义本身或纯缩放的不要：下面的
`variance_eq_integral` 只要几乎处处可测，`variance_const_mul` 什么都不要。**经过 `𝔼[X²]` 或可加性的
要**：`variance_eq_sub`、`variance_add`、`IndepFun.variance_sum`。在有限测度下，若 `X` 几乎处处
强可测（`AEStronglyMeasurable`）却不属于 L²，方差被垃圾值 `0` 取代（`variance_of_not_memLp`，
下面第二个例子），这些等式可能变假，所以引理带了 L² 假设。
-/

section Variance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ}

example : Var[X; μ] = (evariance X μ).toReal := rfl

-- 有限测度 + 几乎处处强可测 + 不属于 L² ⇒ 方差是垃圾值 `0`
example [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) (h : ¬ MemLp X 2 μ) :
    Var[X; μ] = 0 := variance_of_not_memLp hX h

-- 定义：`Var X = 𝔼[(X - 𝔼 X)²]`
example (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ :=
  variance_eq_integral hX

-- 计算公式：`Var X = 𝔼[X²] - (𝔼 X)²`
example [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) : Var[X; μ] = μ[X ^ 2] - μ[X] ^ 2 :=
  variance_eq_sub hX

-- 同分布 ⇒ 方差相同（`IdentDistrib` 见 §3）
example {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} {Y' : Ω' → ℝ}
    (h : IdentDistrib X Y' μ μ') : Var[X; μ] = Var[Y'; μ'] := h.variance_eq

-- 常数倍
example (c : ℝ) : Var[fun ω ↦ c * X ω; μ] = c ^ 2 * Var[X; μ] := variance_const_mul c X μ
-- 独立 ⇒ 方差可加
example [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) :
    Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] := h.variance_add hX hY

/-!
有限和的版本 `IndepFun.variance_sum` 有两个值得细看的假设。(1) 独立性的形式是
`Set.Pairwise ↑s fun i j ↦ Z i ⟂ᵢ[μ] Z j`：只要求 `s` 里的两两独立。(2) 每个 `Z i` 属于 L²。
结论里的和是函数的和 `∑ i ∈ s, Z i`（`Pi` 上的加法），不是 `fun ω ↦ ∑ i ∈ s, Z i ω`；两者用
`Finset.sum_apply` 互换（下面最后一个例子）。
-/

example {ι : Type*} (Z : ι → Ω → ℝ) (s : Finset ι) (hZ : ∀ i ∈ s, MemLp (Z i) 2 μ)
    (h : Set.Pairwise (↑s) fun i j ↦ Z i ⟂ᵢ[μ] Z j) :
    Var[∑ i ∈ s, Z i; μ] = ∑ i ∈ s, Var[Z i; μ] := IndepFun.variance_sum hZ h

-- 逐点和与函数和的互换
example {ι : Type*} (Z : ι → Ω → ℝ) (s : Finset ι) :
    (fun ω ↦ ∑ i ∈ s, Z i ω) = ∑ i ∈ s, Z i := by
  funext ω
  simp [Finset.sum_apply]

end Variance

/-!
## 6. 马尔可夫不等式与切比雪夫不等式

Mathlib 的马尔可夫不等式叫 `mul_meas_ge_le_integral_of_nonneg`（「乘以测度的 `ge` 集 ≤ 积分，
对非负函数」）：对几乎处处非负的可积 `f`，`ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ`。
-/

section Inequalities

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

example {f : Ω → ℝ} (hf : 0 ≤ᵐ[μ] f) (hi : Integrable f μ) (ε : ℝ) :
    ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ := mul_meas_ge_le_integral_of_nonneg hf hi ε

/-- 马尔可夫不等式的常用形状 `P(X ≥ a) ≤ 𝔼[X] / a`：用 `le_div_iff₀` 改写上面的引理。 -/
theorem markov_real {X : Ω → ℝ} (hX0 : 0 ≤ᵐ[μ] X) (hXi : Integrable X μ) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ X ω} ≤ μ[X] / a := by
  have h := mul_meas_ge_le_integral_of_nonneg hX0 hXi a
  rw [le_div_iff₀ ha, mul_comm]
  -- ⊢ a * μ.real {ω | a ≤ X ω} ≤ ∫ (x : Ω), X x ∂μ
  exact h

/-!
切比雪夫不等式 `meas_ge_le_variance_div_sq` 的左边是 `ℝ≥0∞`：
`μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2)`，假设 `MemLp X 2 μ` 与 `0 < c`。
下面把它改写成 `μ.real`（证明里的 `h` 就是上面的陈述）：`measureReal_def` 展开，
`ENNReal.toReal_mono`（需要右端 `≠ ∞`）把 `toReal` 推进不等式，`toReal_ofReal` 消去 `ofReal`
（需要被消去的量非负，由 `variance_nonneg` 与 `positivity` 提供）。
-/

/-- 切比雪夫不等式的实数值形式：`P(|X - 𝔼X| ≥ c) ≤ Var X / c²`。 -/
theorem chebyshev_real [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω - μ[X]|} ≤ Var[X; μ] / c ^ 2 := by
  have h : μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2) :=
    meas_ge_le_variance_div_sq hX hc
  have hv : 0 ≤ Var[X; μ] / c ^ 2 := by
    have := variance_nonneg X μ
    positivity
  calc μ.real {ω | c ≤ |X ω - μ[X]|}
      = (μ {ω | c ≤ |X ω - μ[X]|}).toReal := measureReal_def μ _
    _ ≤ (ENNReal.ofReal (Var[X; μ] / c ^ 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = Var[X; μ] / c ^ 2 := ENNReal.toReal_ofReal hv

end Inequalities

/-!
## 7. 具名分布：`Ber`、`Bin`、`gaussianReal`

旧的 `PMF.bernoulli` 已被弃用（警告见「常见错误」第 3 条）；新的写法是**测度**。源码里
`PMF.binomial`、`PMF.uniformOfFintype` 也带 `deprecated` 属性（弃用日期见该属性的 `since` 字段，
`Mathlib/Probability/ProbabilityMassFunction/Binomial.lean`、`.../Distributions/Uniform.lean`）。
下面三个都是真正的 `Measure`，且都有 `IsProbabilityMeasure` 实例。
- `Ber(x, y, p)`（`bernoulliMeasure x y p`，Bernoulli distribution（伯努利分布））：以概率 `p` 取 `x`、
  以 `1 - p` 取 `y`，其中 `p : unitInterval`（即 `[0, 1]` 里的点，不是 `ℝ`）。
- `Bin(n, p)`：`ℕ` 上的 binomial distribution（二项分布）；`Bin(ℝ, n, p)` 是它沿 `Nat.cast` 的前推。
- `gaussianReal m v`：均值 `m`、方差 `v : ℝ≥0` 的 normal distribution（正态分布）；`v = 0` 时是
  Dirac measure（狄拉克测度）。
-/

section Distributions

open unitInterval

example (p : unitInterval) : IsProbabilityMeasure Ber(true, false, p) := inferInstance
example (n : ℕ) (p : unitInterval) : IsProbabilityMeasure Bin(n, p) := inferInstance
example (m : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianReal m v) := inferInstance

/-!
`unitInterval`（记号 `I`，需要 `open unitInterval`）是子类型 `{x : ℝ // x ∈ Set.Icc 0 1}`（第 7 章）。
同一个 `p : unitInterval` 下面有三种读法：强制转换 `(p : ℝ)`（就是 `p.val`）、`toNNReal p : ℝ≥0`，
以及后者在 `ℝ≥0∞` 里的像 `(toNNReal p : ℝ≥0∞)`（`Ber` 的测度值取在 `ℝ≥0∞` 里）。前两种读法相等：
-/

example (p : unitInterval) : (p : ℝ) = p.val := rfl
example (p : unitInterval) : ((toNNReal p : ℝ≥0) : ℝ) = p := rfl

-- 伯努利：`Ber(1, 0, p)` 的期望是 `p`
example (p : unitInterval) : ∫ x, x ∂Ber((1 : ℝ), 0, p) = p := by
  simp [integral_bernoulliMeasure]

-- 伯努利：取 `x` 的概率是 `p`（`x ∈ s`、`y ∉ s`）
example (p : unitInterval) : Ber(true, false, p).real {true} = p :=
  bernoulliMeasure_real_apply_of_mem_of_notMem p MeasurableSet.of_discrete (by simp) (by simp)

-- 二项分布的期望：`X ~ Bin(n, p)` ⇒ `𝔼 X = n p`
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {n : ℕ} {p : unitInterval}
    (hX : HasLaw X Bin(ℝ, n, p) P) : P[X] = p.val * n := integral_of_hasLaw_binomial hX

-- Gaussian：均值、方差，以及 `v = 0` 时退化
example (m : ℝ) (v : ℝ≥0) : ∫ x, x ∂gaussianReal m v = m := integral_id_gaussianReal
example (m : ℝ) (v : ℝ≥0) : Var[id; gaussianReal m v] = v := variance_id_gaussianReal
example (m : ℝ) : gaussianReal m 0 = Measure.dirac m := gaussianReal_zero_var m

end Distributions

/-!
名字按命名规则解码（第 9 章）：`integral_of_hasLaw_binomial` 是「`HasLaw` 于 `binomial` 时的
`integral`」。找法：在 `Mathlib/Probability/` 下 `rg "theorem .*bernoulliMeasure"`，或 `exact?`。
-/

/-!
## 8. 积测度与独立同分布序列的存在性

「抛 `n` 次硬币」的模型是 `Bool^n` 上的 product measure（积测度）：第 16 章 §8 用 `uniformOn`
处理 `p = 1/2`，这里 `p` 任意。有限积 `Measure.pi μ` 的核心
公式是 `Measure.pi_pi`（长方体测度是各边测度之积；因子须 σ-有限，概率测度自动满足），概率意义是
`iIndepFun_pi`：坐标在积测度下相互独立。无穷积 `Measure.infinitePi` 见本节末尾。
-/

section Product

open unitInterval

example (n : ℕ) (p : unitInterval) (s : Fin n → Set Bool) :
    Measure.pi (fun _ : Fin n ↦ Ber(true, false, p)) (Set.pi Set.univ s)
      = ∏ i, Ber(true, false, p) (s i) :=
  Measure.pi_pi _ s

/-- `n` 次独立抛币：`Fin n → Bool` 上的积测度，每个坐标是 `Ber(true, false, p)`。 -/
noncomputable def coins (n : ℕ) (p : unitInterval) : Measure (Fin n → Bool) :=
  Measure.pi fun _ ↦ Ber(true, false, p)

instance (n : ℕ) (p : unitInterval) : IsProbabilityMeasure (coins n p) := by
  unfold coins
  infer_instance

variable (n : ℕ) (p : unitInterval)

/-- 每个坐标朝上的概率是 `p`：坐标函数的分布是 `Ber`（`measurePreserving_eval`）。 -/
theorem coins_marginal (i : Fin n) : (coins n p).real {ω | ω i = true} = p := by
  have h : HasLaw (Function.eval i) Ber(true, false, p) (coins n p) :=
    (measurePreserving_eval (fun _ : Fin n ↦ Ber(true, false, p)) i).hasLaw
  have h2 := h.measureReal_eq (p := fun b : Bool ↦ b = true) MeasurableSet.of_discrete
  have h3 : (coins n p).real {ω | ω i = true} = Ber(true, false, p).real {x | x = true} := h2
  rw [h3]
  exact bernoulliMeasure_real_apply_of_mem_of_notMem p MeasurableSet.of_discrete (by simp)
    (by simp)

/-- 不同坐标独立：`iIndepFun_pi` 对恒等函数的应用，再取出两个下标。 -/
theorem coins_indep (i j : Fin n) (hij : i ≠ j) :
    (fun ω : Fin n → Bool ↦ ω i) ⟂ᵢ[coins n p] (fun ω ↦ ω j) :=
  (iIndepFun_pi (μ := fun _ : Fin n ↦ Ber(true, false, p)) (X := fun _ ↦ (id : Bool → Bool))
    (fun _ ↦ aemeasurable_id)).indepFun hij

/-- 两个不同坐标同时朝上的概率是 `p * p`。独立性给出集合形式的乘积公式，
再用 `coins_marginal` 算每个边缘。 -/
theorem coins_two (i j : Fin n) (hij : i ≠ j) :
    (coins n p).real {ω | ω i = true ∧ ω j = true} = p * p := by
  have h := indepFun_iff_measure_inter_preimage_eq_mul.1 (coins_indep n p i j hij)
    {true} {true} MeasurableSet.of_discrete MeasurableSet.of_discrete
  have e : {ω : Fin n → Bool | ω i = true ∧ ω j = true}
      = (fun ω : Fin n → Bool ↦ ω i) ⁻¹' {true} ∩ (fun ω : Fin n → Bool ↦ ω j) ⁻¹' {true} := by
    ext ω; simp
  have ei : (fun ω : Fin n → Bool ↦ ω i) ⁻¹' {true} = {ω | ω i = true} := by ext ω; simp
  have ej : (fun ω : Fin n → Bool ↦ ω j) ⁻¹' {true} = {ω | ω j = true} := by ext ω; simp
  -- `e` 把集合写成交，`measureReal_def` 展开 `real`，`h` 换成乘积，`toReal_mul` 拆开，
  -- 两次 `← measureReal_def` 折回，`ei`、`ej` 还原集合，`coins_marginal` 把边缘换成 `p`
  rw [e, measureReal_def, h, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ei, ej,
    coins_marginal, coins_marginal]

-- 坐标在 `infinitePi` 下相互独立
example (p : unitInterval) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → Bool) ↦ id (ω i))
      (Measure.infinitePi fun _ : ℕ ↦ Ber(true, false, p)) :=
  iIndepFun_infinitePi (X := fun _ ↦ (id : Bool → Bool)) (fun _ ↦ measurable_id)

/-!
`infinitePi` 的定义是一个 `if`（`Mathlib/Probability/ProductMeasure.lean`）：每个因子都是概率测度时
才是真正的积，否则取 `0`。例如 `ℝ` 上的 `volume` 不是概率测度（§1），它的无穷乘积就是 `0`：
-/

example : Measure.infinitePi (fun _ : ℕ ↦ (volume : Measure ℝ)) = 0 := by
  rw [Measure.infinitePi, dite_eq_right]
  intro h
  have h1 : (volume : Measure ℝ) Set.univ = 1 := (h 0).measure_univ
  rw [Real.volume_univ] at h1
  exact ENNReal.top_ne_one h1

/-!
`exists_iid`：对任何概率测度 `ν`，存在概率空间 `(Ω, P)` 和序列 `X : ι → Ω → 𝓧`，每个 `X i`
可测、分布为 `ν`，整族相互独立（证明取 `Ω = ι → 𝓧` 与 `infinitePi`，见 `HasLawExists.lean`）。
结论依次是 `Ω`、`MeasurableSpace`、`P`、`X`、可测性、分布、`iIndepFun X P`、`IsProbabilityMeasure P`；
下面的 `obtain` 按此拆开（`-` 丢掉可测性），得到一列 i.i.d.（独立同分布）抛币并算出期望：
-/

example (p : unitInterval) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ (∀ i, HasLaw (X i) Ber((1 : ℝ), 0, p) P) ∧
        ∀ i, P[X i] = (p : ℝ) := by
  obtain ⟨Ω, mΩ, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (Ber((1 : ℝ), 0, p))
  refine ⟨Ω, mΩ, P, X, hP, hind, hlaw, fun i ↦ ?_⟩
  rw [(hlaw i).integral_eq]
  simp [integral_bernoulliMeasure]

end Product

/-!
## 9. 案例：弱大数定律

设 `X₀, X₁, …` 是同分布、两两独立、属于 L² 的实随机变量，记样本均值
`S̄ₙ = (X₀ + ⋯ + X_{n-1}) / n`。弱大数定律说：对每个 `ε > 0`，`P(|S̄ₙ − 𝔼X₀| ≥ ε) → 0`。
证明用本章的概率引理，加上积分与极限引理（`integral_finsetSum`、`memLp_finsetSum`、
`squeeze_zero'`、`tendsto_const_div_atTop_nhds_zero_nat` 等，用到处点出）：

1. `𝔼 S̄ₙ = 𝔼 X₀`（积分的线性性与同分布，`n ≠ 0`）；
2. `Var S̄ₙ = Var X₀ / n`（`IndepFun.variance_sum`、`variance_const_mul`、同分布的方差相等）；
3. 切比雪夫：`P(|S̄ₙ − 𝔼X₀| ≥ ε) ≤ Var X₀ / (n ε²)`；
4. 右端趋于 `0`（用 `Tendsto … atTop (𝓝 0)` 陈述，第 14 章），夹逼。
-/

section Wlln

open Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}

/-- 样本均值 `S̄ₙ(ω) = (X₀ ω + ⋯ + X_{n-1} ω) / n`（`n = 0` 时是垃圾值 `0`）。 -/
noncomputable def sampleMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.range n, X i ω) / n

example : sampleMean X 0 = fun _ ↦ 0 := by
  funext ω; simp [sampleMean]

/-- 步骤 1：同分布 + 属于 L² ⇒ 样本均值的期望等于 `𝔼 X₀`（`n ≠ 0`；L² 只用来得到可积）。 -/
theorem integral_sampleMean (hX : MemLp (X 0) 2 μ) (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {n : ℕ} (hn : n ≠ 0) : μ[sampleMean X n] = μ[X 0] := by
  have hint : ∀ i, Integrable (X i) μ := fun i ↦
    (hid i).integrable_iff.2 (hX.integrable one_le_two)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have e : μ[sampleMean X n] = (∑ i ∈ Finset.range n, ∫ ω, X i ω ∂μ) / n := by
    change ∫ ω, (∑ i ∈ Finset.range n, X i ω) / n ∂μ = _
    rw [integral_div, integral_finsetSum _ (fun i _ ↦ hint i)]
  -- 同分布把每个 `∫ X i` 换成 `∫ X 0`，和变成 `n * 𝔼 X₀`，再用 `n ≠ 0` 约分
  rw [e, Finset.sum_congr rfl (fun i _ ↦ (hid i).integral_eq), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  field_simp

-- `omit … in`（第 15 章）：这条定理用不到 section 变量里的 `[IsProbabilityMeasure μ]`
omit [IsProbabilityMeasure μ] in
/-- 步骤 2：两两独立 + 同分布 ⇒ `Var S̄ₙ = Var X₀ / n`。这里 `n = 0` 也成立（两边都是 `0`）。 -/
theorem variance_sampleMean (hX : MemLp (X 0) 2 μ) (hind : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    Var[sampleMean X n; μ] = Var[X 0; μ] / n := by
  have hmem : ∀ i, MemLp (X i) 2 μ := fun i ↦ (hid i).memLp_iff.2 hX
  have h1 : Var[∑ i ∈ Finset.range n, X i; μ] = n * Var[X 0; μ] := by
    rw [IndepFun.variance_sum (fun i _ ↦ hmem i) (fun _ _ _ _ hij ↦ hind hij),
      Finset.sum_congr rfl (fun i _ ↦ (hid i).variance_eq), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have h2 : sampleMean X n = fun ω ↦ (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, X i) ω := by
    funext ω
    simp [sampleMean, Finset.sum_apply, div_eq_inv_mul]
  rw [h2, variance_const_mul, h1]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by positivity
    field_simp

/-- 步骤 3：切比雪夫不等式给出定量版本：`n ≥ 1` 时 `P(|S̄ₙ − 𝔼X₀| ≥ ε) ≤ Var X₀ / (n ε²)`。 -/
theorem wlln_bound (hX : MemLp (X 0) 2 μ) (hind : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 0 < n) :
    μ.real {ω | ε ≤ |sampleMean X n ω - μ[X 0]|} ≤ Var[X 0; μ] / (n * ε ^ 2) := by
  have hmem : ∀ i, MemLp (X i) 2 μ := fun i ↦ (hid i).memLp_iff.2 hX
  have hS : MemLp (sampleMean X n) 2 μ := by
    have h := (memLp_finsetSum (Finset.range n) (fun i _ ↦ hmem i)).const_mul (n : ℝ)⁻¹
    have e : sampleMean X n = fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω := by
      funext ω; simp [sampleMean, div_eq_inv_mul]
    rw [e]; exact h
  have h := chebyshev_real hS hε
  rw [integral_sampleMean hX hid hn.ne', variance_sampleMean hX hind hid n] at h
  calc μ.real {ω | ε ≤ |sampleMean X n ω - μ[X 0]|} ≤ Var[X 0; μ] / n / ε ^ 2 := h
    _ = Var[X 0; μ] / (n * ε ^ 2) := by rw [div_div]

/-- **弱大数定律**：同分布、两两独立（相互独立蕴含两两独立，§4）、属于 L² 的 `X₀, X₁, …`，
对每个 `ε > 0`，`P(|S̄ₙ − 𝔼X₀| ≥ ε) → 0`。夹逼的上界是 `wlln_bound` 的右端；`n = 0` 时右端按约定为 `0`，
界可能不成立，所以只要求沿 `atTop` 最终成立（`eventually_gt_atTop`）。 -/
theorem wlln (hX : MemLp (X 0) 2 μ) (hind : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |sampleMean X n ω - μ[X 0]|}) atTop (𝓝 0) := by
  have hv : Tendsto (fun n : ℕ ↦ Var[X 0; μ] / (n * ε ^ 2)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (Var[X 0; μ] / ε ^ 2)
    refine h.congr (fun n ↦ ?_)
    ring
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ hv
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact wlln_bound hX hind hid hε hn

end Wlln

/-!
## 10. 强大数定律（只读陈述）

强大数定律把「坏事件的概率趋于 `0`」加强为 almost surely（几乎必然）收敛（`∀ᵐ ω ∂μ`，第 16 章
§5）。`strong_law_ae_real` 只要 `X 0` 可积（比 L² 弱）、两两独立、同分布；与 `wlln` 并排看：这里是
「对几乎每个 `ω`，数列收敛」，那里是「概率的数列收敛」。中心极限定理见「延伸阅读」。
-/

section Limit

open Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

example (hint : Integrable (X 0) μ) (hind : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ sampleMean X n ω) atTop (𝓝 μ[X 0]) :=
  strong_law_ae_real X hint hind hid

end Limit

end Main

/-!
## 常见错误

**1. 忘了打开 `ProbabilityTheory`。** `μ[X]` 是 `ProbabilityTheory` 里限定作用域（`scoped`）的宏。
这一节在 `section Main` 之外，没有任何 `open`；此时 `μ[X]` 被当成下标取值 `getElem`：
-/

set_option pp.mvars false in
/--
error: failed to synthesize instance of type class
  GetElem (MeasureTheory.Measure Ω) (Ω → ℝ) ?_ ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (X : Ω → ℝ) :
    μ[X] = ∫ ω, X ω ∂μ := rfl

/-!
补救：`open ProbabilityTheory`，或只激活记号而不打开名字的 `open scoped ProbabilityTheory`
（`Probability/Notation.lean` 的文档也写了这两种）。下面只用 `open scoped … in`，本章用到的七个
概率记号 `μ[X]`、`𝔼[X]`、`ℙ`、`Var[X; μ]`、`X ⟂ᵢ[μ] Y`、`Ber(…)`、`Bin(…)` 都能用：
-/

open scoped ProbabilityTheory in
example {Ω : Type*} [MeasureTheory.MeasureSpace Ω] (μ : MeasureTheory.Measure Ω) (X Y : Ω → ℝ)
    (p : unitInterval) (h : X ⟂ᵢ[μ] Y) :
    μ[X] = ∫ ω, X ω ∂μ ∧ 𝔼[X] = ∫ ω, X ω ∧ (ℙ : MeasureTheory.Measure Ω) = MeasureTheory.volume ∧
      Var[X; μ] = ProbabilityTheory.variance X μ ∧ ProbabilityTheory.IndepFun X Y μ ∧
      MeasureTheory.IsProbabilityMeasure Ber(true, false, p) ∧
      MeasureTheory.IsProbabilityMeasure Bin(3, p) :=
  ⟨rfl, rfl, rfl, rfl, h, inferInstance, inferInstance⟩

/-!
**2. 省略测度，Ω 上没有 `MeasureSpace`。** §4 陷阱的另一半：没有 `volume` 可取，`by volume_tac`
失败。补救：显式写出测度（`IndepFun X Y μ`），或给 `Ω` 一个 `MeasureSpace` 实例并接受 `volume`：
-/

/--
error: could not synthesize default value for parameter 'μ' using tactics
---
error: failed to synthesize instance of type class
  MeasureTheory.MeasureSpace Ω

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (X Y : Ω → ℝ) (h : ProbabilityTheory.IndepFun X Y) :
    True := trivial

/-!
**3. 旧名字。** `PMF.bernoulli` 仍可用但已弃用，警告里给出替代名；
`Memℒp` 已不存在（`MemLp` 是新名）：
-/

/--
warning: `PMF.bernoulli` has been deprecated: Use `ProbabilityTheory.bernoulliMeasure` instead

Note: The updated constant has a different type:
  {X : Type u_1} → [inst : MeasurableSpace X] → X → X → ↑unitInterval → MeasureTheory.Measure X
instead of
  (p : NNReal) → p ≤ 1 → PMF Bool

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.bernoulli` to `ProbabilityTheory.bernoulliMeasure x`).
-/
#guard_msgs in
example : PMF Bool := PMF.bernoulli 0 (zero_le_one)

/-- error: Unknown identifier `MeasureTheory.Memℒp` -/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (X : Ω → ℝ) :
    MeasureTheory.Memℒp X 2 μ → True := fun _ ↦ trivial

/-!
## 练习

17.3、17.4 回到第 11 章（`le_div_iff₀`、`gcongr`），17.10、17.11 回到第 14 章（`Tendsto`），
17.12 回到第 12 章（`Finset.sum_congr`）。引理名在本章出现过或由题面给出；陈述不用本章自定义的定理。
-/

section Exercises

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology unitInterval

/-- 练习 17.1（★）：概率测度下补集的实数概率是 `1 - P(A)`；用 `probReal_add_probReal_compl`
再 `linarith`。 -/
theorem ex_17_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) : μ.real sᶜ = 1 - μ.real s := by
  sorry

/-- 练习 17.2（★）：期望的线性性。`𝔼[2X + 3] = 2𝔼[X] + 3`；用 `integral_add`、
`Integrable.const_mul`、`integrable_const`、`integral_const_mul`，常数的积分用 `simp`。 -/
theorem ex_17_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) : μ[fun ω ↦ 2 * X ω + 3] = 2 * μ[X] + 3 := by
  sorry

/-- 练习 17.3（★★）：对 `|X|` 用马尔可夫不等式。若 `X` 可积且 `c > 0`，则
`P(|X| ≥ c) ≤ 𝔼|X| / c`；用 `mul_meas_ge_le_integral_of_nonneg`（取 `f = fun ω ↦ |X ω|`，
非负用 `Filter.Eventually.of_forall`，可积用 `Integrable.abs`）与 `le_div_iff₀`。 -/
theorem ex_17_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Integrable X μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω|} ≤ (∫ ω, |X ω| ∂μ) / c := by
  sorry

/-- 练习 17.4（★★）：切比雪夫不等式的方差上界版。若 `Var[X; μ] ≤ v` 且 `c > 0`，则
`P(|X − 𝔼X| ≥ c) ≤ v / c²`（`ℝ≥0∞` 值）；用 `meas_ge_le_variance_div_sq`，再用
`ENNReal.ofReal_le_ofReal` 与 `gcongr`（第 11 章）比较两个分式。 -/
theorem ex_17_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) {v c : ℝ} (hv : Var[X; μ] ≤ v) (hc : 0 < c) :
    μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (v / c ^ 2) := by
  sorry

/-- 练习 17.5（★★）：缩放和的方差。`X`、`Y` 独立且属于 L²，则
`Var[2X + 3Y] = 4 Var[X] + 9 Var[Y]`；先用 `IndepFun.comp` 得到 `2X` 与 `3Y` 独立，
再用 `IndepFun.variance_fun_add`、`MemLp.const_mul` 与 `variance_const_mul`。 -/
theorem ex_17_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) :
    Var[fun ω ↦ 2 * X ω + 3 * Y ω; μ] = 4 * Var[X; μ] + 9 * Var[Y; μ] := by
  sorry

/-- 练习 17.6（★）：方差不超过二阶矩。`Var[X] ≤ 𝔼[X²]`；用 `variance_eq_sub`
（需要 `MemLp X 2 μ`）与 `sq_nonneg`，最后 `linarith`。 -/
theorem ex_17_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) : Var[X; μ] ≤ μ[X ^ 2] := by
  sorry

/-- 练习 17.7（★）：同分布的随机变量，同一事件的实数概率相同；用
`IdentDistrib.measure_mem_eq`（取 `s = Set.Iic 1`）与 `measureReal_def`。 -/
theorem ex_17_7 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
    (μ' : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) (h : IdentDistrib X Y μ μ') :
    μ.real {ω | X ω ≤ 1} = μ'.real {ω | Y ω ≤ 1} := by
  sorry

/-- 练习 17.8（★★）：`Fin n → Bool` 上的独立计算。在 `n` 次独立抛币的模型
`Measure.pi fun _ ↦ Ber(true, false, p)` 下，两个不同的位置 `i ≠ j` 同时朝下的概率是
`(1 - p) * (1 - p)`。模仿 §8 的 `coins_two`，只是把 `true` 换成 `false`：`iIndepFun_pi` 给出独立性，
`measurePreserving_eval` 给出边缘分布；`Ber` 取 `false` 的概率要用
`bernoulliMeasure_real_apply_of_notMem_of_mem`（§7 用过的 `…_of_mem_of_notMem` 的孪生，条件是
`x ∉ s`、`y ∈ s`；在 `Distributions/Bernoulli.lean` 里按名字搜）。 -/
theorem ex_17_8 (n : ℕ) (p : unitInterval) (i j : Fin n) (hij : i ≠ j) :
    (Measure.pi fun _ : Fin n ↦ Ber(true, false, p)).real {ω | ω i = false ∧ ω j = false}
      = (1 - p) * (1 - p) := by
  sorry

/-- 练习 17.9（★★）：伯努利变量之和的期望。若每个 `X i` 的分布都是 `Ber(1, 0, p)`，则
`𝔼[X₀ + ⋯ + X_{n-1}] = n p`；用 `integral_finsetSum`（可积性来自
`HasLaw.integrable`，其中 `f` 取 `id`，再用 `integrable_bernoulliMeasure`）、`HasLaw.integral_eq` 与
`integral_bernoulliMeasure`。 -/
theorem ex_17_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : unitInterval) (hX : ∀ i, HasLaw (X i) Ber((1 : ℝ), 0, p) P) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, X i ω] = (n : ℝ) * p := by
  sorry

/-- 练习 17.10（★）：切比雪夫界的极限（弱大数定律的最后一步）。对任意实数 `v`、`ε`，
`v / (n ε²) → 0`；用 `tendsto_const_div_atTop_nhds_zero_nat` 加 `Tendsto.congr`，逐点相等用
`ring`（`ring` 不需要 `ε ≠ 0`）。 -/
theorem ex_17_10 (v ε : ℝ) : Tendsto (fun n : ℕ ↦ v / (n * ε ^ 2)) atTop (𝓝 0) := by
  sorry

/-- 练习 17.11（★★★）：弱大数定律的补事件形式。若对每个 `ε > 0`，`P(|Sₙ − m| ≥ ε) → 0`，
则 `P(|Sₙ − m| < ε) → 1`。事件 `{|Sₙ − m| < ε}` 是 `{ε ≤ |Sₙ − m|}` 的补集；
用 `measureReal_compl`（需要可测性，用 `measurableSet_le` 与 `fun_prop`）、`probReal_univ`，
极限用 `tendsto_const_nhds`、`Tendsto.sub` 与 `sub_zero`。 -/
theorem ex_17_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → ℝ) (m : ℝ) (hS : ∀ n, Measurable (S n))
    (h : ∀ ε > 0, Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |S n ω - m|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | |S n ω - m| < ε}) atTop (𝓝 1) := by
  sorry

/-- 练习 17.12（★★）：同方差两两独立变量之和的方差。若 `X i` 两两独立、属于 L²、
方差都是 `v`，则 `Var[X₀ + ⋯ + X_{n-1}] = n v`；用 `IndepFun.variance_sum`、
`Finset.sum_congr`、`Finset.sum_const`、`Finset.card_range`。 -/
theorem ex_17_12 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hind : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j)
    (v : ℝ) (hv : ∀ i, Var[X i; μ] = v) (n : ℕ) :
    Var[∑ i ∈ Finset.range n, X i; μ] = n * v := by
  sorry

/-- 练习 17.13（★★）：用 `exists_iid` 造一列抛币。对每个 `p`，存在概率空间和一列相互独立的
随机变量 `X i`，满足 `P(X i = 1) = p`；用 `exists_iid ℕ Ber(1, 0, p)`、`HasLaw.measureReal_eq`
（集合 `{1}` 的可测性是 `measurableSet_singleton`）与 `bernoulliMeasure_real_apply_of_mem_of_notMem`。 -/
theorem ex_17_13 (p : unitInterval) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ ∀ i, P.real {ω | X i ω = 1} = p := by
  sorry

/-- 练习 17.14（★★）：从相互独立得到强大数定律。i.i.d. 的可积 `X i` 的样本均值几乎必然收敛到
`𝔼[X 0]`；用 `strong_law_ae_real`，两两独立由 `iIndepFun.indepFun` 得到（包一层
`fun _ _ hij ↦ …`）。 -/
theorem ex_17_14 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 μ[X 0]) := by
  sorry

/-- 练习 17.15（★★）：二项分布的期望。`X ~ Bin(n, p)` 时 `𝔼[2X] = 2 (p n)`；
用 `integral_const_mul` 与 `integral_of_hasLaw_binomial`。 -/
theorem ex_17_15 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {n : ℕ}
    {p : unitInterval} (hX : HasLaw X Bin(ℝ, n, p) P) :
    P[fun ω ↦ 2 * X ω] = 2 * (p.val * n) := by
  sorry

end Exercises

/-!
## 小结

| 概念 | 语法 / 名字 | 何时用 |
|---|---|---|
| 概率空间 | `(μ : Measure Ω) [IsProbabilityMeasure μ]`、`measure_univ`、`prob_le_one` | 起点 |
| 记号 | `μ[X]`、`𝔼[X]`、`Var[X; μ]`、`⟂ᵢ[μ]`、`Ber`、`Bin` | `open` 或 `open scoped` `ProbabilityTheory` |
| 期望 | `μ[X]` = `∫ ω, X ω ∂μ`、`integral_indicator_one`、`integral_undef` | 不可积时为 `0` |
| 分布 | `HasLaw X ν μ`（`μ.map X = ν`）、`.measureReal_eq`、`.integral_eq` | 事件概率搬到像空间 |
| 同分布 | `IdentDistrib X Y μ ν`、`.integral_eq`、`.variance_eq`、`.measure_mem_eq` | 互换期望、方差 |
| 独立 | `X ⟂ᵢ[μ] Y`、`iIndepFun X μ`、`iIndepFun.indepFun`、`IndepFun.comp` | 省略 `μ` 会取 `volume` |
| 方差 | `variance_eq_integral`、`variance_eq_sub`、`IndepFun.variance_sum` | 后两条要 `MemLp X 2 μ` |
| 方差的垃圾值 | `variance_of_not_memLp` | 有限测度、几乎处处强可测、非 L² |
| 马尔可夫 | `mul_meas_ge_le_integral_of_nonneg` | 非负可积 |
| 切比雪夫 | `meas_ge_le_variance_div_sq`（`ℝ≥0∞` 值） | 用 `toReal_mono` 转实数 |
| 具名分布 | `Ber(x, y, p)`、`Bin(n, p)`、`Bin(ℝ, n, p)`、`gaussianReal m v` | 取代弃用的 `PMF.*` |
| 积测度 | `Measure.pi`、`iIndepFun_pi`、`Measure.infinitePi`、`exists_iid` | 独立抛币；i.i.d. 序列 |
| 极限定理 | 本章的 `wlln`；`strong_law_ae_real` | 弱定律自证，强定律引用 |
-/

/-!
## 延伸阅读

- 记号与定义：`Mathlib/Probability/Notation.lean`（`μ[X]`、`𝔼[X]`、`ℙ`）、
  `Mathlib/Probability/HasLaw.lean`、`Mathlib/Probability/IdentDistrib.lean`。
- 独立性：`Mathlib/Probability/Independence/Basic.lean`（定义、`iIndepFun_pi`）、
  `.../Independence/Integration.lean`、`.../Independence/InfinitePi.lean`。
- 方差与不等式：`Mathlib/Probability/Moments/Variance.lean`；马尔可夫不等式在
  `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`（`mul_meas_ge_le_integral_of_nonneg`）。
- 分布与存在性：`Mathlib/Probability/Distributions/{Bernoulli,Binomial}.lean`、
  `.../Distributions/Gaussian/Real.lean`、`Mathlib/Probability/ProductMeasure.lean`、
  `Mathlib/Probability/HasLawExists.lean`（`exists_iid`）。
- 极限定理：`Mathlib/Probability/StrongLaw.lean`（`strong_law_ae_real`、`strong_law_Lp`）；
  中心极限定理 `tendstoInDistribution_inv_sqrt_mul_sum_sub` 在 `.../CentralLimitTheorem.lean`。
- 本书第 16 章（测度论）、第 19 章（概率方法）、第 21 章（Chernoff 与 Hoeffding：切比雪夫的指数版本）。
-/

end Lean4Learn.Ch17

end
