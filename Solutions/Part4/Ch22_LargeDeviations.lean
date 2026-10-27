module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# 第 22 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part4/Ch22_LargeDeviations.lean` 逐字相同，只是证明体已补全。
答案文件不导入章节文件，所以本章定义的 `Λ`、`Λstar`、`ΛstarE`、`IsLDP` 与用到的引理在这里重新证明了一遍：
`Λstar_nonneg`、`Λ_zero_variable`、`integrable_exp_of_identDistrib`、`Λ_eq_of_identDistrib`、
`chernoff_iid`、`cramer_upper`、`cramer_upper_of_mem_Icc`、`mgf_bernoulli`、`Λ_bernoulli`、
`ae_mem_Icc_of_bernoulli`、`bernoulli_exponent`、`bernoulli_rate_le`。
-/

@[expose] public section

namespace Solutions.Ch22

section Main

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology unitInterval

section Defs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- 记号上沿用大偏差文献：`Λ(t) = log 𝔼 exp (t X)`。它只是 `cgf` 的别名，
`Λ X P t = cgf X P t` 是 `rfl`。若 `exp (t X)` 不可积，`mgf` 取垃圾值 `0`（积分的约定），
`Λ` 随之取 `Real.log 0 = 0`；所以下面凡需要 `Λ` 取真值（而不是垃圾值）的定理
（`chernoff_iid`、`cramer_upper`……）都带可积性假设。 -/
noncomputable def Λ (X : Ω → ℝ) (P : Measure Ω) (t : ℝ) : ℝ := cgf X P t

end Defs

section Legendre

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- 单边 Legendre 变换 `Λ*(a) = sup_{t ≥ 0} (t a - Λ(t))`，写成子类型 `{t // 0 ≤ t}` 上的 `iSup`。
这是实数值的 `iSup`：若族无上界，值是垃圾值 `0`（见下面的例子）。 -/
noncomputable def Λstar (X : Ω → ℝ) (P : Measure Ω) (a : ℝ) : ℝ :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ((t : ℝ) * a - Λ X P t)

/-- `Λ*` 总是 `≥ 0`，不论族是否有上界：有上界时取 `t = 0`（`cgf_zero`），无上界时垃圾值本身就是 `0`。 -/
theorem Λstar_nonneg [IsProbabilityMeasure P] (X : Ω → ℝ) (a : ℝ) : 0 ≤ Λstar X P a := by
  by_cases hbdd : BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} ↦ ((t : ℝ) * a - Λ X P t))
  · have h := le_ciSup hbdd (⟨0, le_rfl⟩ : {t : ℝ // 0 ≤ t})
    -- h : 0 * a - Λ X P 0 ≤ ⨆ t, (t * a - Λ X P t)
    simpa [Λstar, Λ, cgf_zero] using h
  · rw [Λstar, Real.iSup_of_not_bddAbove hbdd]

theorem Λ_zero_variable [IsProbabilityMeasure P] (t : ℝ) : Λ (fun _ : Ω ↦ (0 : ℝ)) P t = 0 := by
  simp [Λ, cgf, mgf]

/-- 单边版本：`sup_{t ≥ 0} (t a - Λ(t))`，取值于 `EReal`。 -/
noncomputable def ΛstarE (X : Ω → ℝ) (P : Measure Ω) (a : ℝ) : EReal :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ((((t : ℝ) * a - Λ X P t : ℝ)) : EReal)

end Legendre

section Chernoff

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- 零件 1：同分布的 `X i` 与 `X 0`，`exp (t X 0)` 可积则 `exp (t X i)` 可积。
`IdentDistrib.comp` 把同分布性推到 `x ↦ exp (t x)` 之下，`IdentDistrib.integrable_iff`
说同分布的两个函数同时可积。 -/
theorem integrable_exp_of_identDistrib {X : ℕ → Ω → ℝ} (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (t : ℝ) (hint : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (i : ℕ) :
    Integrable (fun ω ↦ Real.exp (t * X i ω)) P :=
  ((hid i).comp (u := fun x : ℝ ↦ Real.exp (t * x)) (by fun_prop)).integrable_iff.2 hint

omit [IsProbabilityMeasure P] in
/-- 零件 2：同分布的变量，`Λ` 相同（`mgf_congr_of_identDistrib` 的 `t` 是显式参数）。 -/
theorem Λ_eq_of_identDistrib {X : ℕ → Ω → ℝ} (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (t : ℝ) (i : ℕ) : Λ (X i) P t = Λ (X 0) P t := by
  simp only [Λ, cgf, mgf_congr_of_identDistrib (X i) (X 0) (hid i) t]

/-- Chernoff 界，独立同分布和，固定 `t ≥ 0`。 -/
theorem chernoff_iid {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {t : ℝ} (ht : 0 ≤ t)
    (hint : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (a : ℝ) (n : ℕ) :
    P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-(n * (t * a - Λ (X 0) P t))) := by
  have hint' := integrable_exp_of_identDistrib hid t hint
  -- 零件 3：对 ∑ X i 用单变量的 Chernoff 界
  have h1 := measure_ge_le_exp_cgf (μ := P) (X := ∑ i ∈ Finset.range n, X i) (n * a) ht
    (hind.integrable_exp_mul_sum hm (fun i _ ↦ hint' i))
  -- 和的 cgf = n * Λ (X 0)
  have h2 : cgf (∑ i ∈ Finset.range n, X i) P t = n * Λ (X 0) P t := by
    have h3 : ∀ i ∈ Finset.range n, cgf (X i) P t = cgf (X 0) P t :=
      fun i _ ↦ Λ_eq_of_identDistrib hid t i
    rw [hind.cgf_sum hm (fun i _ ↦ hint' i), Finset.sum_congr rfl h3]
    simp [Λ]
  have e : -(n * (t * a - Λ (X 0) P t))
      = -t * (n * a) + cgf (∑ i ∈ Finset.range n, X i) P t := by
    rw [h2]; ring
  rw [e]
  simpa [Finset.sum_apply] using h1

/-- **Cramér 型上界。** 独立同分布，`exp (t X 0)` 对所有 `t ≥ 0` 可积，则
`P(S_n ≥ n a) ≤ exp (-(n * Λ*(a)))`。证明里没有用 `BddAbove`。 -/
theorem cramer_upper {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (a : ℝ) (n : ℕ) :
    P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-(n * Λstar (X 0) P a)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · calc P.real {ω | ((0 : ℕ) : ℝ) * a ≤ ∑ i ∈ Finset.range 0, X i ω} ≤ 1 := measureReal_le_one
      _ = _ := by simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set E : Set Ω := {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} with hE
  rcases (measureReal_nonneg (μ := P) (s := E)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact (Real.exp_pos _).le
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  -- 每个 t 给出 t a - Λ t ≤ -log P(E) / n
  have key : ∀ t : {t : ℝ // 0 ≤ t}, (t : ℝ) * a - Λ (X 0) P t ≤ -Real.log (P.real E) / n := by
    intro t
    have h := chernoff_iid hm hind hid t.2 (hint t t.2) a n
    have h' := Real.log_le_log hpos h
    rw [Real.log_exp] at h'
    rw [le_div_iff₀ hnR]
    linarith
  have hsup : Λstar (X 0) P a ≤ -Real.log (P.real E) / n := ciSup_le key
  have h3 : (n : ℝ) * Λstar (X 0) P a ≤ -Real.log (P.real E) := by
    rw [le_div_iff₀ hnR] at hsup
    linarith
  calc P.real E = Real.exp (Real.log (P.real E)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

/-- 有界变量（几乎必然落在 `[b, c]`）：可积性假设自动成立
（`integrable_exp_mul_of_mem_Icc` 对任意 `t` 成立）。 -/
theorem cramer_upper_of_mem_Icc {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {b c : ℝ}
    (hb : ∀ᵐ ω ∂P, X 0 ω ∈ Set.Icc b c) (a : ℝ) (n : ℕ) :
    P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-(n * Λstar (X 0) P a)) :=
  cramer_upper hm hind hid (fun _ _ ↦ integrable_exp_mul_of_mem_Icc (hm 0).aemeasurable hb) a n

end Chernoff

section Bernoulli

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem mgf_bernoulli [IsProbabilityMeasure P] {X : Ω → ℝ} (p : unitInterval)
    (hX : HasLaw X Ber(1, 0, p) P) (t : ℝ) :
    mgf X P t = (p : ℝ) * Real.exp t + (1 - (p : ℝ)) := by
  have h := hX.integral_comp (f := fun x : ℝ ↦ Real.exp (t * x)) (by fun_prop)
  rw [integral_bernoulliMeasure] at h
  simpa [mgf, Function.comp_def] using h

theorem Λ_bernoulli [IsProbabilityMeasure P] {X : Ω → ℝ} (p : unitInterval)
    (hX : HasLaw X Ber(1, 0, p) P) (t : ℝ) :
    Λ X P t = Real.log (1 - (p : ℝ) + p * Real.exp t) := by
  rw [Λ, cgf, mgf_bernoulli p hX t, add_comm]

/-- 伯努利变量几乎必然落在 `[0, 1]`：用 `HasLaw.ae_iff` 把「几乎必然」搬到
`Ber(1, 0, p)` 上，再用 `bernoulliMeasure_apply_of_notMem_of_notMem`（不含 `1` 也不含 `0`
的集合测度为 `0`）。 -/
theorem ae_mem_Icc_of_bernoulli {X : Ω → ℝ} (p : unitInterval) (hX : HasLaw X Ber(1, 0, p) P) :
    ∀ᵐ ω ∂P, X ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [hX.ae_iff (p := fun x ↦ x ∈ Set.Icc (0 : ℝ) 1) (measurable_mem.2 measurableSet_Icc),
    ae_iff]
  exact bernoulliMeasure_apply_of_notMem_of_notMem p
    (s := {x : ℝ | ¬ x ∈ Set.Icc (0 : ℝ) 1}) (measurableSet_Icc.compl) (by simp) (by simp)

theorem bernoulli_exponent {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 < a) (ha1 : a < 1) :
    Real.log (a * (1 - p) / (p * (1 - a))) * a
        - Real.log (1 - p + p * (a * (1 - p) / (p * (1 - a))))
      = a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  have h1p : 0 < 1 - p := sub_pos.2 hp1
  have h2 : 1 - p + p * (a * (1 - p) / (p * (1 - a))) = (1 - p) / (1 - a) := by
    field_simp
    ring
  rw [h2]
  simp only [Real.log_div ha0.ne' hp0.ne', Real.log_div h1a.ne' h1p.ne',
    Real.log_div h1p.ne' h1a.ne', Real.log_div (mul_pos ha0 h1p).ne' (mul_pos hp0 h1a).ne',
    Real.log_mul ha0.ne' h1p.ne', Real.log_mul hp0.ne' h1a.ne']
  ring

theorem bernoulli_rate_le {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    t * a - Real.log (1 - p + p * Real.exp t)
      ≤ a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  have h1p : 0 < 1 - p := sub_pos.2 hp1
  have hE : 0 < Real.exp t := Real.exp_pos t
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = 1 - p + p * Real.exp t := ⟨_, rfl⟩
  have hZ : 0 < Z := by rw [hZdef]; positivity
  have hZne : Z ≠ 0 := hZ.ne'
  have ha' : a ≠ 0 := ha0.ne'
  have h1a' : 1 - a ≠ 0 := h1a.ne'
  rw [← hZdef]
  -- 两次 `log x ≤ x - 1`：x = p e^t / (Z a) 与 x = (1-p) / (Z (1-a))
  have e1 := Real.log_le_sub_one_of_pos (x := p * Real.exp t / (Z * a)) (by positivity)
  have e2 := Real.log_le_sub_one_of_pos (x := (1 - p) / (Z * (1 - a))) (by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hp0.ne' hE.ne', Real.log_exp,
    Real.log_mul hZne ha'] at e1
  rw [Real.log_div h1p.ne' (by positivity), Real.log_mul hZne h1a'] at e2
  have k1 : a * (p * Real.exp t / (Z * a)) = p * Real.exp t / Z := by field_simp
  have k2 : (1 - a) * ((1 - p) / (Z * (1 - a))) = (1 - p) / Z := by field_simp
  have hsum : p * Real.exp t / Z + (1 - p) / Z = 1 := by
    rw [← add_div, div_eq_one_iff_eq hZne, hZdef]; ring
  rw [Real.log_div ha' hp0.ne', Real.log_div h1a' h1p.ne']
  nlinarith [mul_le_mul_of_nonneg_left e1 ha0.le, mul_le_mul_of_nonneg_left e2 h1a.le]

end Bernoulli

section LDP

/-- 大偏差原理（speed 为 `n`）：速率函数 `J : E → EReal` 非负、下半连续，且闭集上界与开集下界成立。 -/
structure IsLDP {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (J : E → EReal) : Prop where
  nonneg : ∀ x, 0 ≤ J x
  lsc : LowerSemicontinuous J
  upper : ∀ F : Set E, IsClosed F →
    limsup (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (μ n F)) atTop ≤ -⨅ x ∈ F, J x
  lower : ∀ G : Set E, IsOpen G →
    -⨅ x ∈ G, J x ≤ liminf (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (μ n G)) atTop

end LDP

section Exercises

/-- 练习 22.1（★）：`Λ(0) = 0`；用 `cgf_zero`（它要求 `IsZeroOrProbabilityMeasure`，概率测度满足）。 -/
theorem ex_22_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) : Λ X P 0 = 0 := by
  simp [Λ, cgf_zero]

/-- 练习 22.2（★★）：`upper_halfline` 的最后一步。`n > 0` 时，在 `EReal` 里
`(1/n) · log (ofReal (exp (-(n c)))) = -c`；用 `ENNReal.log_ofReal`、`split_ifs`
（`exp` 为正，`≤ 0` 的分支自己关掉）、`Real.log_exp`、`EReal.coe_mul` 与 `inv_mul_cancel₀`。 -/
theorem ex_22_2 (c : ℝ) {n : ℕ} (hn : 0 < n) :
    (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (-(n * c))))
      = ((-c : ℝ) : EReal) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : ¬ (Real.exp (-(n * c)) ≤ 0) := not_le.2 (Real.exp_pos _)
  rw [ENNReal.log_ofReal]
  split_ifs
  rw [Real.log_exp, ← EReal.coe_mul]
  exact congrArg (fun r : ℝ ↦ (r : EReal))
    (by rw [mul_neg, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul])

/-- 练习 22.3（★★）：缩放。`Λ_{cX}(t) = Λ_X(c t)`；展开定义，积分号下的函数相等
（`t * (c * X ω) = c * t * X ω`，`ring`）。 -/
theorem ex_22_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (c t : ℝ) :
    Λ (fun ω ↦ c * X ω) P t = Λ X P (c * t) := by
  have h : ∀ ω, t * (c * X ω) = c * t * X ω := fun ω ↦ by ring
  simp only [Λ, cgf, mgf, h]

/-- 练习 22.4（★★）：速率 `c > 0` 时 `exp (-(n c)) → 0`；用
`Real.tendsto_exp_neg_atTop_nhds_zero`、`tendsto_natCast_atTop_atTop` 与
`Filter.Tendsto.atTop_mul_const`，再 `Tendsto.comp`。 -/
theorem ex_22_4 (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-(n * c))) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_mul_const hc)
  simpa [Function.comp_def] using h

/-- 练习 22.5（★★）：Cramér 型上界蕴含指数衰减。若 `Λ*(a) > 0`，则
`P(S_n ≥ n a) → 0`；用 `cramer_upper`、练习 22.4 的结论，以及夹逼的特例 `squeeze_zero`
（夹逼见第 14 章；第 17 章用过带撇的 `squeeze_zero'`）。 -/
theorem ex_22_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (a : ℝ)
    (ha : 0 < Λstar (X 0) P a) :
    Tendsto (fun n : ℕ ↦ P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω}) atTop (𝓝 0) := by
  have hc := ex_22_4 (Λstar (X 0) P a) ha
  exact squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ cramer_upper hm hind hid hint a n) hc

/-- 练习 22.6（★★）：`Λ*` 关于 `a` 单调，但需要 `BddAbove`；用 `ciSup_mono`（它要右边的族有上界；
该引理在本题里第一次出现，位于 `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`）。
没有 `BddAbove` 时右边的 `Λstar` 是垃圾值 `0`（§3），所以必须假设 `hb`。 -/
theorem ex_22_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hb : BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} ↦ ((t : ℝ) * b - Λ X P t))) :
    Λstar X P a ≤ Λstar X P b := by
  unfold Λstar
  refine ciSup_mono hb (fun t ↦ ?_)
  have := mul_le_mul_of_nonneg_left hab t.2
  linarith

/-- 练习 22.7（★）：取值 `±1` 的伯努利变量（`Ber(1, -1, p)`）的矩母函数：
`mgf X P t = p e^t + (1-p) e^{-t}`；仿照 `mgf_bernoulli`：`HasLaw.integral_comp`、
`integral_bernoulliMeasure`，再 `simpa`。 -/
theorem ex_22_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (p : unitInterval) (hX : HasLaw X Ber(1, -1, p) P) (t : ℝ) :
    mgf X P t = (p : ℝ) * Real.exp t + (1 - (p : ℝ)) * Real.exp (-t) := by
  have h := hX.integral_comp (f := fun x : ℝ ↦ Real.exp (t * x)) (by fun_prop)
  rw [integral_bernoulliMeasure] at h
  simpa [mgf, Function.comp_def] using h

/-- 练习 22.8（★★）：`p = 1/2` 时的速率函数：
`I(a) = log 2 + a log a + (1-a) log (1-a)`；提示：`a / (1/2) = a * 2`，再用 `Real.log_mul`。 -/
theorem ex_22_8 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    a * Real.log (a / (1 / 2)) + (1 - a) * Real.log ((1 - a) / (1 - 1 / 2))
      = Real.log 2 + a * Real.log a + (1 - a) * Real.log (1 - a) := by
  have e1 : a / (1 / 2) = a * 2 := by ring
  have e2 : (1 - a) / (1 - 1 / 2) = (1 - a) * 2 := by
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]; ring
  rw [e1, e2, Real.log_mul ha0.ne' two_ne_zero, Real.log_mul (sub_pos.2 ha1).ne' two_ne_zero]
  ring

/-- 练习 22.9（★）：相对熵非负。用 `bernoulli_rate_le` 在 `t = 0` 处的特例。 -/
theorem ex_22_9 {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 < a) (ha1 : a < 1) :
    0 ≤ a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  have := bernoulli_rate_le hp0 hp1 ha0 ha1 0
  simpa using this

/-- 练习 22.10（★★★）：下尾。对 `[0,1]` 值的独立同分布变量，
`P(S_n ≤ n a) ≤ exp (-(n * Λ*_{-X}(-a)))`。把 `X i` 换成 `-X i`，用
`cramer_upper_of_mem_Icc`（区间 `[-1, 0]`）；独立性与同分布性用 `iIndepFun.comp` 与
`IdentDistrib.comp` 搬运；事件的等式用 `Finset.sum_neg_distrib`。 -/
theorem ex_22_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (hb : ∀ᵐ ω ∂P, X 0 ω ∈ Set.Icc (0 : ℝ) 1)
    (a : ℝ) (n : ℕ) :
    P.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ n * a}
      ≤ Real.exp (-(n * Λstar (fun ω ↦ -X 0 ω) P (-a))) := by
  have hind' : iIndepFun (fun i ω ↦ -X i ω) P :=
    hind.comp (fun _ (x : ℝ) ↦ -x) (fun _ ↦ measurable_neg)
  have hid' : ∀ i, IdentDistrib (fun ω ↦ -X i ω) (fun ω ↦ -X 0 ω) P P := fun i ↦
    (hid i).comp (u := fun x : ℝ ↦ -x) measurable_neg
  have hb' : ∀ᵐ ω ∂P, -X 0 ω ∈ Set.Icc (-1 : ℝ) 0 := by
    filter_upwards [hb] with ω hω
    exact ⟨by linarith [hω.2], by linarith [hω.1]⟩
  have h := cramer_upper_of_mem_Icc (P := P) (X := fun i ω ↦ -X i ω) (fun i ↦ (hm i).neg)
    hind' hid' hb' (-a) n
  have e : {ω | (n : ℝ) * (-a) ≤ ∑ i ∈ Finset.range n, -X i ω}
      = {ω | ∑ i ∈ Finset.range n, X i ω ≤ n * a} := by
    ext ω
    show (n : ℝ) * (-a) ≤ ∑ i ∈ Finset.range n, -X i ω
      ↔ ∑ i ∈ Finset.range n, X i ω ≤ n * a
    rw [Finset.sum_neg_distrib]
    constructor <;> intro h <;> linarith
  rw [e] at h
  exact h

/-- 练习 22.11（★★）：读 `IsLDP` 的定义。若 `μ` 满足速率函数为 `J` 的 LDP，`G` 是开集，`x ∈ G`，
则 `-J x ≤ liminf (1/n) log μ_n(G)`。用字段 `IsLDP.lower`、`EReal.neg_le_neg_iff` 与 `iInf₂_le`。 -/
theorem ex_22_11 {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure E} {J : E → EReal} (h : IsLDP μ J) {G : Set E} (hG : IsOpen G) {x : E}
    (hx : x ∈ G) :
    -J x ≤ liminf (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (μ n G)) atTop := by
  refine le_trans ?_ (h.lower G hG)
  exact EReal.neg_le_neg_iff.2 (iInf₂_le x hx)

/-- 练习 22.12（★★）：常数 `0` 的 `Λ*` 在 `a ≤ 0` 时是 `0`（与 `a = 1` 时的垃圾值 `0`
对照：这里 `0` 是对的）；`le_antisymm`，`ciSup_le` 与 `Λstar_nonneg`。 -/
theorem ex_22_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} (ha : a ≤ 0) : Λstar (fun _ : Ω ↦ (0 : ℝ)) P a = 0 := by
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  refine le_antisymm ?_ (Λstar_nonneg _ a)
  unfold Λstar
  refine ciSup_le fun t ↦ ?_
  rw [Λ_zero_variable]
  nlinarith [t.2]

/-- 练习 22.13（★）：概率测度下 `ENNReal.log (μ s) ≤ 0`；用 `ENNReal.log_le_zero_iff` 与
`prob_le_one`。 -/
theorem ex_22_13 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Set Ω) : ENNReal.log (μ s) ≤ 0 := by
  rw [ENNReal.log_le_zero_iff]
  exact prob_le_one

/-- 练习 22.14（★）：`EReal` 版本的 `Λstar_nonneg`：`0 ≤ ΛstarE X P a`，对一切 `a`
（不需要 `BddAbove`）。用 `le_iSup_of_le` 取 `t = 0`。 -/
theorem ex_22_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (a : ℝ) : 0 ≤ ΛstarE X P a := by
  unfold ΛstarE
  exact le_iSup_of_le (⟨0, le_rfl⟩ : {t : ℝ // 0 ≤ t}) (by simp [Λ, cgf_zero])

/-- 练习 22.15（★★★）：`Λ*(m) = 0`，其中 `m = 𝔼 X`（§9 第 2 条的一步）。分两步：
(1) 琴生不等式给出 `t * 𝔼 X ≤ Λ(t)`：`ConvexOn.map_integral_le` 配 `convexOn_exp`，再取
`Real.log`，积分号外提用 `integral_const_mul`；(2) `le_antisymm`，`ciSup_le` 与 `Λstar_nonneg`。 -/
theorem ex_22_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * X ω)) P) :
    Λstar X P (P[X]) = 0 := by
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  have jensen : ∀ t : {t : ℝ // 0 ≤ t}, (t : ℝ) * P[X] ≤ Λ X P t := by
    intro t
    have h : Real.exp (∫ ω, (t : ℝ) * X ω ∂P) ≤ ∫ ω, Real.exp ((t : ℝ) * X ω) ∂P :=
      convexOn_exp.map_integral_le (μ := P) (f := fun ω ↦ (t : ℝ) * X ω)
        Real.continuous_exp.continuousOn isClosed_univ
        (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _) (hX.const_mul t) (hint t t.2)
    have h2 := Real.log_le_log (Real.exp_pos _) h
    rw [Real.log_exp, integral_const_mul] at h2
    exact h2
  refine le_antisymm ?_ (Λstar_nonneg X _)
  refine ciSup_le fun t ↦ ?_
  have := jensen t
  linarith

end Exercises

end Main

end Solutions.Ch22

end
