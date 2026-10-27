module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 21 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part4/Ch21_Concentration.lean` 逐字相同，只是证明体已补全。
练习的陈述只用 Mathlib 的名字，所以答案文件不需要重证章节里的引理；唯一的辅助引理是
`unit_exponent`（`[0, 1]` 值变量的次高斯参数 `((‖1 - 0‖₊ / 2) ^ 2 : ℝ≥0)` 换成实数后，
尾界的指数化成 `-2 ε²`），供练习 21.10、21.11 共用；练习 21.15 直接调用本文件里的 `ex_21_10`。
-/

@[expose] public section

namespace Solutions.Ch21

open MeasureTheory ProbabilityTheory
open scoped NNReal unitInterval

/-- `[0, 1]` 值变量的次高斯参数换成实数后，尾界的指数是 `-2 ε²`。 -/
theorem unit_exponent (ε : ℝ) :
    -ε ^ 2 / (2 * (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)) = -2 * ε ^ 2 := by
  have hc : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / 4 := by
    push_cast
    rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 - 0)]
    norm_num
  rw [hc]
  ring

section Exercises

open Filter
open scoped Topology

/-- 练习 21.1（★）：累积量母函数的缩放。`cgf (a X) t = cgf X (a t)`；`cgf` 展开成 `log (mgf …)`，
再用 `mgf_const_mul`。 -/
theorem ex_21_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (a t : ℝ) :
    cgf (fun ω ↦ a * X ω) μ t = cgf X μ (a * t) := by
  simp only [cgf, mgf_const_mul]

/-- 练习 21.2（★）：中心化的矩母函数。`mgf (X - m) t = mgf X t * exp (-(t m))`；
用 `mgf_add_const`（取 `a = -m`），再用 `sub_eq_add_neg`、`mul_neg` 把 `X ω + -m`、`t * -m` 改写成
陈述里的形状（`simpa [sub_eq_add_neg]` 一步完成）。这是 Hoeffding 装配里「中心化」一步的矩母函数版本。 -/
theorem ex_21_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (m t : ℝ) :
    mgf (fun ω ↦ X ω - m) μ t = mgf X μ t * Real.exp (-(t * m)) := by
  have h := mgf_add_const (μ := μ) (X := X) (t := t) (-m)
  simpa [sub_eq_add_neg] using h

/-- 练习 21.3（★）：下尾的 Chernoff 界，参数写成 `s ≥ 0`。`P(X ≤ ε) ≤ exp (s ε) * mgf X (-s)`；
用 `measure_le_le_exp_mul_mgf`（取 `t = -s`），再用 `neg_neg` 把 `- -s * ε` 化成 `s * ε`。 -/
theorem ex_21_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    {s : ℝ} (hs : 0 ≤ s) (h_int : Integrable (fun ω ↦ Real.exp (-s * X ω)) μ) (ε : ℝ) :
    μ.real {ω | X ω ≤ ε} ≤ Real.exp (s * ε) * mgf X μ (-s) := by
  have h := measure_le_le_exp_mul_mgf ε (neg_nonpos.2 hs) h_int
  rwa [neg_neg] at h

/-- 练习 21.4（★）：`t = ε / c` 确实最优。对 `c > 0` 与任意 `t`，
`-ε² / (2c) ≤ -(t ε) + c t² / 2`；先用 `div_le_iff₀` 去分母，再用 `nlinarith [sq_nonneg (c * t - ε)]`
（右边减左边乘 `2c` 恰是 `(c t - ε)²`）。 -/
theorem ex_21_4 {c : ℝ} (hc : 0 < c) (ε t : ℝ) :
    -ε ^ 2 / (2 * c) ≤ -(t * ε) + c * t ^ 2 / 2 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (c * t - ε)]

/-- 练习 21.5（★）：次高斯变量的下尾。`P(X ≤ -ε) ≤ exp (-ε² / (2c))`；用 `HasSubgaussianMGF.neg`、
`HasSubgaussianMGF.measure_ge_le`，以及集合相等 `{ω | X ω ≤ -ε} = {ω | ε ≤ (-X) ω}`
（`Set.mem_ofPred_eq`、`Pi.neg_apply`、`linarith`）。 -/
theorem ex_21_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | X ω ≤ -ε} ≤ Real.exp (-ε ^ 2 / (2 * c)) := by
  have h' := h.neg.measure_ge_le hε
  have hset : {ω | X ω ≤ -ε} = {ω | ε ≤ (-X) ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact h'

/-- 练习 21.6（★）：次高斯参数可以放大。若 `X` 具有参数 `c` 的次高斯矩母函数且 `c ≤ c'`，则它也具有
参数 `c'` 的；用匿名构造子，可积性取 `h.integrable_exp_mul`，不等式用 `h.mgf_le`、`Real.exp_le_exp`
或 `gcongr`（先把 `c ≤ c'` 转成 `(c : ℝ) ≤ c'`，用 `exact_mod_cast`）。 -/
theorem ex_21_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) {c c' : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcc : c ≤ c') : HasSubgaussianMGF X c' μ := by
  refine ⟨h.integrable_exp_mul, fun t ↦ (h.mgf_le t).trans ?_⟩
  have hcc' : (c : ℝ) ≤ c' := by exact_mod_cast hcc
  gcongr

/-- 练习 21.7（★★）：高斯变量的尾界。`X ~ N(0, v)` 时 `P(X ≥ ε) ≤ exp (-ε² / (2v))`；
正文已有 `id` 与 `gaussianReal` 的情形，这里是一般的 `HasLaw` 版本。先证 `HasSubgaussianMGF X v P`：
可积性用 `mgf_pos_iff`（把 `0 < mgf` 变成可积）加 `mgf_gaussianReal`，
不等式 `mgf_le` 其实是等号；再用 `measure_ge_le`。 -/
theorem ex_21_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (v : ℝ≥0) (hX : HasLaw X (gaussianReal 0 v) P) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * v)) := by
  have hsub : HasSubgaussianMGF X v P :=
    ⟨fun t ↦ mgf_pos_iff.1 (by rw [mgf_gaussianReal hX t]; exact Real.exp_pos _),
     fun t ↦ by rw [mgf_gaussianReal hX t]; simp⟩
  exact hsub.measure_ge_le hε

/-- 练习 21.8（★★）：联合界（实数版）。`n` 个变量各自满足 `P(Xᵢ ≥ ε) ≤ β`，则
`P(∃ i, Xᵢ ≥ ε) ≤ n β`；把事件写成并集（`Set.mem_iUnion`），用第 19 章的
`measureReal_biUnion_finset_le`（取 `Finset.univ`；或它的 `Fintype` 特化 `measureReal_iUnion_fintype_le`）、
`Finset.sum_le_sum`，最后 `simp` 算常数和。 -/
theorem ex_21_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ) (ε β : ℝ) (h : ∀ i, μ.real {ω | ε ≤ X i ω} ≤ β) :
    μ.real {ω | ∃ i, ε ≤ X i ω} ≤ n * β := by
  have hset : {ω | ∃ i, ε ≤ X i ω} = ⋃ i, {ω | ε ≤ X i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hset]
  calc μ.real (⋃ i, {ω | ε ≤ X i ω}) ≤ ∑ i, μ.real {ω | ε ≤ X i ω} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, β := Finset.sum_le_sum fun i _ ↦ h i
    _ = n * β := by simp

/-- 练习 21.9（★★）：由次高斯性得到 Hoeffding。设 `Yᵢ = Xᵢ - m` 相互独立且都具有参数 `1/4` 的次高斯
矩母函数（Hoeffding 引理对 `[0, 1]` 值变量给出的参数），则 `P(∑ Xᵢ ≥ n (m + t)) ≤ exp (-2 n t²)`。
用 §4 的 `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`（取 `c = 1/4`、`ε = n t`），事件改写用
`Finset.sum_sub_distrib`、`Finset.sum_const`；指数里 `n = 0` 要单独处理（分母为零），`n ≠ 0` 时 `field`。 -/
theorem ex_21_9 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℝ)
    (hind : iIndepFun (fun i ω ↦ X i ω - m) μ)
    (hsub : ∀ i, HasSubgaussianMGF (fun ω ↦ X i ω - m) (1 / 4) μ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (n : ℝ) * (m + t) ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-2 * n * t ^ 2) := by
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hind (c := 1 / 4) (n := n)
    (fun i _ ↦ hsub i) (ε := n * t) (by positivity)
  have hset : {ω | (n : ℝ) * (m + t) ≤ ∑ i ∈ Finset.range n, X i ω}
      = {ω | (n : ℝ) * t ≤ ∑ i ∈ Finset.range n, (X i ω - m)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine h.trans (le_of_eq ?_)
  congr 1
  push_cast
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · simp [hn]
  · field

/-- 练习 21.10（★★）：单个变量的 Hoeffding。`X` 几乎必然取值于 `[0, 1]`，则
`P(X - 𝔼X ≥ ε) ≤ exp (-2 ε²)`；用 `hasSubgaussianMGF_of_mem_Icc` 与 `measure_ge_le`，再把参数
`((‖1 - 0‖₊ / 2) ^ 2 : ℝ≥0)` 转成实数 `1/4`（`push_cast`、`Real.norm_eq_abs`、`abs_of_pos`、`norm_num`）。 -/
theorem ex_21_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 ≤ ε) : μ.real {ω | ε ≤ X ω - μ[X]} ≤ Real.exp (-2 * ε ^ 2) := by
  have h := (hasSubgaussianMGF_of_mem_Icc hm hb).measure_ge_le hε
  exact h.trans (le_of_eq (congrArg Real.exp (unit_exponent ε)))

/-- 练习 21.11（★★）：上一题的双侧版本。`P(|X - 𝔼X| ≥ ε) ≤ 2 exp (-2 ε²)`；
事件包含于 `{ε ≤ X - 𝔼X} ∪ {ε ≤ -(X - 𝔼X)}`（`le_abs`），用 `HasSubgaussianMGF.neg`、
`measureReal_mono`、`measureReal_union_le`。 -/
theorem ex_21_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 ≤ ε) : μ.real {ω | ε ≤ |X ω - μ[X]|} ≤ 2 * Real.exp (-2 * ε ^ 2) := by
  have hsg := hasSubgaussianMGF_of_mem_Icc hm hb
  have h1 := (hsg.measure_ge_le hε).trans (le_of_eq (congrArg Real.exp (unit_exponent ε)))
  have h2 := (hsg.neg.measure_ge_le hε).trans (le_of_eq (congrArg Real.exp (unit_exponent ε)))
  have hsub : {ω | ε ≤ |X ω - μ[X]|}
      ⊆ {ω | ε ≤ X ω - μ[X]} ∪ {ω | ε ≤ (-(fun ω ↦ X ω - μ[X])) ω} := by
    intro ω (hω : ε ≤ |X ω - μ[X]|)
    rcases le_abs.1 hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc μ.real {ω | ε ≤ |X ω - μ[X]|}
      ≤ μ.real ({ω | ε ≤ X ω - μ[X]} ∪ {ω | ε ≤ (-(fun ω ↦ X ω - μ[X])) ω}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ X ω - μ[X]} + μ.real {ω | ε ≤ (-(fun ω ↦ X ω - μ[X])) ω} :=
        measureReal_union_le _ _
    _ ≤ Real.exp (-2 * ε ^ 2) + Real.exp (-2 * ε ^ 2) := add_le_add h1 h2
    _ = 2 * Real.exp (-2 * ε ^ 2) := by ring

/-- 练习 21.12（★★★）：Hoeffding 给出的数值界。1000 次公平抛币里正面数 `≥ 600` 的概率被
`exp (-2 · 1000 · (1/10)²)` 控制；证明这个数不超过 `1/1000000`。`norm_num` 把指数化成 `-20`；
`Real.add_one_le_exp` 取 `x = 1` 得 `2 ≤ exp 1`；`Real.exp_nat_mul` 给 `exp 20 = (exp 1) ^ 20`，
再用 `pow_le_pow_left₀`；最后 `Real.exp_neg`、`one_div` 与 `inv_le_inv₀`。 -/
theorem ex_21_12 : Real.exp (-2 * 1000 * (1 / 10 : ℝ) ^ 2) ≤ 1 / 1000000 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h20 : Real.exp 20 = Real.exp 1 ^ 20 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hexp : -2 * 1000 * (1 / 10 : ℝ) ^ 2 = -20 := by norm_num
  rw [hexp, Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos 20) (by norm_num)]
  calc (1000000 : ℝ) ≤ 2 ^ 20 := by norm_num
    _ ≤ Real.exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) h1 20
    _ = Real.exp 20 := h20.symm

/-- 练习 21.13（★★）：指数衰减的概率趋于零。若 `0 ≤ pₙ ≤ exp (-2 n t²)` 且 `t ≠ 0`，则 `pₙ → 0`；
先证 `n * (2 t²) → ∞`（`tendsto_natCast_atTop_atTop`、`Filter.Tendsto.atTop_mul_const`），再取负号
（`tendsto_neg_atTop_atBot`）、复合 `Real.tendsto_exp_atBot`，最后用 `squeeze_zero`。 -/
theorem ex_21_13 (p : ℕ → ℝ) {t : ℝ} (ht : t ≠ 0) (h0 : ∀ n, 0 ≤ p n)
    (h : ∀ n : ℕ, p n ≤ Real.exp (-2 * n * t ^ 2)) : Tendsto p atTop (𝓝 0) := by
  have h2 : 0 < 2 * t ^ 2 := by positivity
  have h3 : Tendsto (fun n : ℕ ↦ (n : ℝ) * (2 * t ^ 2)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const h2
  have h4 : Tendsto (fun n : ℕ ↦ -((n : ℝ) * (2 * t ^ 2))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h3
  have h5 : Tendsto (fun n : ℕ ↦ Real.exp (-2 * n * t ^ 2)) atTop (𝓝 0) := by
    refine (Real.tendsto_exp_atBot.comp h4).congr fun n ↦ ?_
    show Real.exp (-((n : ℝ) * (2 * t ^ 2))) = Real.exp (-2 * n * t ^ 2)
    congr 1
    ring
  exact squeeze_zero h0 h h5

/-- 练习 21.14（★）：有上界的变量，矩母函数有上界。若 `X ≤ b` 几乎必然且 `t ≥ 0`，则
`mgf X t ≤ exp (t b)`；用 `mgf_mono_of_nonneg`（与常值函数 `fun _ ↦ b` 比较，可积性是
`integrable_const`）和 `mgf_const`。不要求 `X` 可测：若 `exp (t X)` 不可积，`mgf` 是垃圾值 `0`，
结论平凡成立（§1 的第 (4) 类）；`mgf_mono_of_nonneg` 自己处理这个分支。 -/
theorem ex_21_14 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {b t : ℝ} (hb : ∀ᵐ ω ∂μ, X ω ≤ b) (ht : 0 ≤ t) :
    mgf X μ t ≤ Real.exp (t * b) := by
  have h := mgf_mono_of_nonneg (X := X) (Y := fun _ ↦ b) hb ht (integrable_const _)
  rwa [mgf_const] at h

/-- 练习 21.15（★★）：单个伯努利变量的 Hoeffding。`X ~ Ber(1, 0, p)` 时 `P(X - p ≥ ε) ≤ exp (-2 ε²)`；
先证 `X` 几乎必然在 `[0, 1]` 里（`HasLaw.ae_iff`、`ae_iff`、`bernoulliMeasure_apply_of_notMem_of_notMem`，
见 §6 的 `hoeffding_bernoulli`）与 `μ[X] = p`（`HasLaw.integral_eq`、`integral_bernoulliMeasure`），
再把 `μ[X]` 换成 `p`，后面和练习 21.10 一样（`hasSubgaussianMGF_of_mem_Icc` 与 `measure_ge_le`）。 -/
theorem ex_21_15 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : I)
    (X : Ω → ℝ) (hX : HasLaw X Ber(1, 0, p) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω - (p : ℝ)} ≤ Real.exp (-2 * ε ^ 2) := by
  have hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hX.ae_iff (p := fun x ↦ x ∈ Set.Icc (0 : ℝ) 1) (measurable_mem.2 measurableSet_Icc),
      ae_iff]
    exact bernoulliMeasure_apply_of_notMem_of_notMem p
      (s := {x : ℝ | ¬ x ∈ Set.Icc (0 : ℝ) 1}) (measurableSet_Icc.compl) (by simp) (by simp)
  have hmean : μ[X] = (p : ℝ) := by
    simp [hX.integral_eq, integral_bernoulliMeasure]
  have h := ex_21_10 μ X hX.aemeasurable hb hε
  rwa [hmean] at h

end Exercises

end Solutions.Ch21

end
