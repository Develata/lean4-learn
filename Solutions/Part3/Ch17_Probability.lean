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
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 17 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part3/Ch17_Probability.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch17

section Exercises

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology unitInterval

/-- 练习 17.1（★）：概率测度下补集的实数概率是 `1 - P(A)`；用 `probReal_add_probReal_compl`
再 `linarith`。 -/
theorem ex_17_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {s : Set Ω} (hs : MeasurableSet s) : μ.real sᶜ = 1 - μ.real s := by
  have := probReal_add_probReal_compl (μ := μ) hs
  linarith

/-- 练习 17.2（★）：期望的线性性。`𝔼[2X + 3] = 2𝔼[X] + 3`；用 `integral_add`、
`Integrable.const_mul`、`integrable_const`、`integral_const_mul`，常数的积分用 `simp`。 -/
theorem ex_17_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) : μ[fun ω ↦ 2 * X ω + 3] = 2 * μ[X] + 3 := by
  calc μ[fun ω ↦ 2 * X ω + 3]
      = ∫ ω, 2 * X ω ∂μ + ∫ _ω, (3 : ℝ) ∂μ :=
        integral_add (hX.const_mul 2) (integrable_const 3)
    _ = 2 * μ[X] + 3 := by
        rw [integral_const_mul]
        simp

/-- 练习 17.3（★★）：对 `|X|` 用马尔可夫不等式。若 `X` 可积且 `c > 0`，则
`P(|X| ≥ c) ≤ 𝔼|X| / c`；用 `mul_meas_ge_le_integral_of_nonneg`（取 `f = fun ω ↦ |X ω|`，
非负用 `Filter.Eventually.of_forall`，可积用 `Integrable.abs`）与 `le_div_iff₀`。 -/
theorem ex_17_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hX : Integrable X μ) {c : ℝ} (hc : 0 < c) :
    μ.real {ω | c ≤ |X ω|} ≤ (∫ ω, |X ω| ∂μ) / c := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := fun ω ↦ |X ω|)
    (Eventually.of_forall fun ω ↦ abs_nonneg (X ω)) hX.abs c
  rw [le_div_iff₀ hc, mul_comm]
  exact h

/-- 练习 17.4（★★）：切比雪夫不等式的方差上界版。若 `Var[X; μ] ≤ v` 且 `c > 0`，则
`P(|X − 𝔼X| ≥ c) ≤ v / c²`（`ℝ≥0∞` 值）；用 `meas_ge_le_variance_div_sq`，再用
`ENNReal.ofReal_le_ofReal` 与 `gcongr`（第 11 章）比较两个分式。 -/
theorem ex_17_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) {v c : ℝ} (hv : Var[X; μ] ≤ v) (hc : 0 < c) :
    μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (v / c ^ 2) := by
  calc μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2) :=
        meas_ge_le_variance_div_sq hX hc
    _ ≤ ENNReal.ofReal (v / c ^ 2) := by gcongr

/-- 练习 17.5（★★）：缩放和的方差。`X`、`Y` 独立且属于 L²，则
`Var[2X + 3Y] = 4 Var[X] + 9 Var[Y]`；先用 `IndepFun.comp` 得到 `2X` 与 `3Y` 独立，
再用 `IndepFun.variance_fun_add`、`MemLp.const_mul` 与 `variance_const_mul`。 -/
theorem ex_17_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (h : X ⟂ᵢ[μ] Y) :
    Var[fun ω ↦ 2 * X ω + 3 * Y ω; μ] = 4 * Var[X; μ] + 9 * Var[Y; μ] := by
  have hX2 : MemLp (fun ω ↦ 2 * X ω) 2 μ := hX.const_mul 2
  have hY3 : MemLp (fun ω ↦ 3 * Y ω) 2 μ := hY.const_mul 3
  have hind : (fun ω ↦ 2 * X ω) ⟂ᵢ[μ] (fun ω ↦ 3 * Y ω) :=
    h.comp (by fun_prop : Measurable fun x : ℝ ↦ 2 * x)
      (by fun_prop : Measurable fun x : ℝ ↦ 3 * x)
  rw [hind.variance_fun_add hX2 hY3, variance_const_mul, variance_const_mul]
  norm_num

/-- 练习 17.6（★）：方差不超过二阶矩。`Var[X] ≤ 𝔼[X²]`；用 `variance_eq_sub`
（需要 `MemLp X 2 μ`）与 `sq_nonneg`，最后 `linarith`。 -/
theorem ex_17_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) : Var[X; μ] ≤ μ[X ^ 2] := by
  rw [variance_eq_sub hX]
  have := sq_nonneg μ[X]
  linarith

/-- 练习 17.7（★）：同分布的随机变量，同一事件的实数概率相同；用
`IdentDistrib.measure_mem_eq`（取 `s = Set.Iic 1`）与 `measureReal_def`。 -/
theorem ex_17_7 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (μ : Measure Ω)
    (μ' : Measure Ω') (X : Ω → ℝ) (Y : Ω' → ℝ) (h : IdentDistrib X Y μ μ') :
    μ.real {ω | X ω ≤ 1} = μ'.real {ω | Y ω ≤ 1} := by
  have h1 := h.measure_mem_eq (measurableSet_Iic (a := (1 : ℝ)))
  simp only [measureReal_def]
  exact congrArg ENNReal.toReal h1

/-- 练习 17.8（★★）：`Fin n → Bool` 上的独立计算。在 `n` 次独立抛币的模型
`Measure.pi fun _ ↦ Ber(true, false, p)` 下，两个不同的位置 `i ≠ j` 同时朝下的概率是
`(1 - p) * (1 - p)`。模仿 §8 的 `coins_two`，只是把 `true` 换成 `false`：`iIndepFun_pi` 给出独立性，
`measurePreserving_eval` 给出边缘分布；`Ber` 取 `false` 的概率要用
`bernoulliMeasure_real_apply_of_notMem_of_mem`（§7 用过的 `…_of_mem_of_notMem` 的孪生，条件是
`x ∉ s`、`y ∈ s`；在 `Distributions/Bernoulli.lean` 里按名字搜）。 -/
theorem ex_17_8 (n : ℕ) (p : unitInterval) (i j : Fin n) (hij : i ≠ j) :
    (Measure.pi fun _ : Fin n ↦ Ber(true, false, p)).real {ω | ω i = false ∧ ω j = false}
      = (1 - p) * (1 - p) := by
  have hind : (fun ω : Fin n → Bool ↦ ω i)
      ⟂ᵢ[Measure.pi fun _ : Fin n ↦ Ber(true, false, p)] (fun ω ↦ ω j) :=
    (iIndepFun_pi (μ := fun _ : Fin n ↦ Ber(true, false, p))
      (X := fun _ ↦ (id : Bool → Bool)) (fun _ ↦ aemeasurable_id)).indepFun hij
  have h := indepFun_iff_measure_inter_preimage_eq_mul.1 hind {false} {false}
    MeasurableSet.of_discrete MeasurableSet.of_discrete
  have marg : ∀ k : Fin n, (Measure.pi fun _ : Fin n ↦ Ber(true, false, p)).real
      {ω | ω k = false} = 1 - p := by
    intro k
    have hl : HasLaw (Function.eval k) Ber(true, false, p)
        (Measure.pi fun _ : Fin n ↦ Ber(true, false, p)) :=
      (measurePreserving_eval (fun _ : Fin n ↦ Ber(true, false, p)) k).hasLaw
    have h2 := hl.measureReal_eq (p := fun b : Bool ↦ b = false) MeasurableSet.of_discrete
    have h3 : (Measure.pi fun _ : Fin n ↦ Ber(true, false, p)).real {ω | ω k = false}
        = Ber(true, false, p).real {x | x = false} := h2
    rw [h3]
    exact bernoulliMeasure_real_apply_of_notMem_of_mem p MeasurableSet.of_discrete (by simp)
      (by simp)
  have e : {ω : Fin n → Bool | ω i = false ∧ ω j = false}
      = (fun ω : Fin n → Bool ↦ ω i) ⁻¹' {false} ∩ (fun ω : Fin n → Bool ↦ ω j) ⁻¹' {false} := by
    ext ω
    simp
  have ei : (fun ω : Fin n → Bool ↦ ω i) ⁻¹' {false} = {ω | ω i = false} := by
    ext ω
    simp
  have ej : (fun ω : Fin n → Bool ↦ ω j) ⁻¹' {false} = {ω | ω j = false} := by
    ext ω
    simp
  rw [e, measureReal_def, h, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def, ei, ej,
    marg, marg]

/-- 练习 17.9（★★）：伯努利变量之和的期望。若每个 `X i` 的分布都是 `Ber(1, 0, p)`，则
`𝔼[X₀ + ⋯ + X_{n-1}] = n p`；用 `integral_finsetSum`（可积性来自
`HasLaw.integrable`，其中 `f` 取 `id`，再用 `integrable_bernoulliMeasure`）、`HasLaw.integral_eq` 与
`integral_bernoulliMeasure`。 -/
theorem ex_17_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (p : unitInterval) (hX : ∀ i, HasLaw (X i) Ber((1 : ℝ), 0, p) P) (n : ℕ) :
    P[fun ω ↦ ∑ i ∈ Finset.range n, X i ω] = (n : ℝ) * p := by
  have hint : ∀ i, Integrable (X i) P := fun i ↦
    (hX i).integrable (integrable_bernoulliMeasure _ _ _ _)
  calc P[fun ω ↦ ∑ i ∈ Finset.range n, X i ω]
      = ∑ i ∈ Finset.range n, ∫ ω, X i ω ∂P := integral_finsetSum _ (fun i _ ↦ hint i)
    _ = ∑ _i ∈ Finset.range n, (p : ℝ) :=
        Finset.sum_congr rfl (fun i _ ↦ by
          rw [(hX i).integral_eq]
          simp [integral_bernoulliMeasure])
    _ = n * p := by simp

/-- 练习 17.10（★）：切比雪夫界的极限（弱大数定律的最后一步）。对任意实数 `v`、`ε`，
`v / (n ε²) → 0`；用 `tendsto_const_div_atTop_nhds_zero_nat` 加 `Tendsto.congr`，逐点相等用
`ring`（`ring` 不需要 `ε ≠ 0`）。 -/
theorem ex_17_10 (v ε : ℝ) : Tendsto (fun n : ℕ ↦ v / (n * ε ^ 2)) atTop (𝓝 0) := by
  have h := tendsto_const_div_atTop_nhds_zero_nat (v / ε ^ 2)
  refine h.congr (fun n ↦ ?_)
  ring

/-- 练习 17.11（★★★）：弱大数定律的补事件形式。若对每个 `ε > 0`，`P(|Sₙ − m| ≥ ε) → 0`，
则 `P(|Sₙ − m| < ε) → 1`。事件 `{|Sₙ − m| < ε}` 是 `{ε ≤ |Sₙ − m|}` 的补集；
用 `measureReal_compl`（需要可测性，用 `measurableSet_le` 与 `fun_prop`）、`probReal_univ`，
极限用 `tendsto_const_nhds`、`Tendsto.sub` 与 `sub_zero`。 -/
theorem ex_17_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → ℝ) (m : ℝ) (hS : ∀ n, Measurable (S n))
    (h : ∀ ε > 0, Tendsto (fun n : ℕ ↦ μ.real {ω | ε ≤ |S n ω - m|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | |S n ω - m| < ε}) atTop (𝓝 1) := by
  have hmeas : ∀ n, MeasurableSet {ω | ε ≤ |S n ω - m|} := fun n ↦ by
    have := hS n
    exact measurableSet_le measurable_const (by fun_prop)
  have e : ∀ n, μ.real {ω | |S n ω - m| < ε} = 1 - μ.real {ω | ε ≤ |S n ω - m|} := by
    intro n
    have hc : {ω | |S n ω - m| < ε} = {ω | ε ≤ |S n ω - m|}ᶜ := by
      ext ω
      simp
    rw [hc, measureReal_compl (hmeas n), probReal_univ]
  simp_rw [e]
  have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub (h ε hε)
  rw [sub_zero] at h1
  exact h1

/-- 练习 17.12（★★）：同方差两两独立变量之和的方差。若 `X i` 两两独立、属于 L²、
方差都是 `v`，则 `Var[X₀ + ⋯ + X_{n-1}] = n v`；用 `IndepFun.variance_sum`、
`Finset.sum_congr`、`Finset.sum_const`、`Finset.card_range`。 -/
theorem ex_17_12 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) (hind : Pairwise fun i j ↦ X i ⟂ᵢ[μ] X j)
    (v : ℝ) (hv : ∀ i, Var[X i; μ] = v) (n : ℕ) :
    Var[∑ i ∈ Finset.range n, X i; μ] = n * v := by
  rw [IndepFun.variance_sum (fun i _ ↦ hX i) (fun _ _ _ _ hij ↦ hind hij)]
  simp [hv]

/-- 练习 17.13（★★）：用 `exists_iid` 造一列抛币。对每个 `p`，存在概率空间和一列相互独立的
随机变量 `X i`，满足 `P(X i = 1) = p`；用 `exists_iid ℕ Ber(1, 0, p)`、`HasLaw.measureReal_eq`
（集合 `{1}` 的可测性是 `measurableSet_singleton`）与 `bernoulliMeasure_real_apply_of_mem_of_notMem`。 -/
theorem ex_17_13 (p : unitInterval) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : ℕ → Ω → ℝ),
      IsProbabilityMeasure P ∧ iIndepFun X P ∧ ∀ i, P.real {ω | X i ω = 1} = p := by
  obtain ⟨Ω, mΩ, P, X, -, hlaw, hind, hP⟩ := exists_iid ℕ (Ber((1 : ℝ), 0, p))
  refine ⟨Ω, mΩ, P, X, hP, hind, fun i ↦ ?_⟩
  have h := (hlaw i).measureReal_eq (p := fun x : ℝ ↦ x = 1) (measurableSet_singleton 1)
  rw [h]
  exact bernoulliMeasure_real_apply_of_mem_of_notMem p (measurableSet_singleton 1) (by simp)
    (by simp)

/-- 练习 17.14（★★）：从相互独立得到强大数定律。i.i.d. 的可积 `X i` 的样本均值几乎必然收敛到
`𝔼[X 0]`；用 `strong_law_ae_real`，两两独立由 `iIndepFun.indepFun` 得到（包一层
`fun _ _ hij ↦ …`）。 -/
theorem ex_17_14 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) μ) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, X i ω) / n) atTop (𝓝 μ[X 0]) := by
  exact strong_law_ae_real X hint (fun _ _ hij ↦ hind.indepFun hij) hid

/-- 练习 17.15（★★）：二项分布的期望。`X ~ Bin(n, p)` 时 `𝔼[2X] = 2 (p n)`；
用 `integral_const_mul` 与 `integral_of_hasLaw_binomial`。 -/
theorem ex_17_15 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {n : ℕ}
    {p : unitInterval} (hX : HasLaw X Bin(ℝ, n, p) P) :
    P[fun ω ↦ 2 * X ω] = 2 * (p.val * n) := by
  have h1 : P[fun ω ↦ 2 * X ω] = 2 * P[X] := integral_const_mul 2 X
  rw [h1, integral_of_hasLaw_binomial hX]

end Exercises

end Solutions.Ch17

end
