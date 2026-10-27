module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.NormNum

/-!
# 第 16 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part3/Ch16_MeasureTheory.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch16

section Exercises

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- 练习 16.1（★）：可测集对补、并、交封闭；用 `MeasurableSet.compl/union/inter`。 -/
theorem ex_16_1 {α : Type*} [MeasurableSpace α] (s t u : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hu : MeasurableSet u) : MeasurableSet ((sᶜ ∪ t) ∩ u) :=
  (hs.compl.union ht).inter hu

/-- 练习 16.2（★）：`{x | 1 < x ∧ x ≤ 3}` 可测。两种做法：`measurability`；或者先用
`Set.ext`（第 7 章）证它等于 `Set.Ioc 1 3`，再用 `measurableSet_Ioc`。 -/
theorem ex_16_2 : MeasurableSet {x : ℝ | 1 < x ∧ x ≤ 3} := by
  have h : {x : ℝ | 1 < x ∧ x ≤ 3} = Set.Ioc 1 3 := by
    ext x
    simp
  rw [h]
  exact measurableSet_Ioc

/-- 练习 16.3（★）：可测函数的多项式组合可测；用 `fun_prop`。 -/
theorem ex_16_3 (f : ℝ → ℝ) (hf : Measurable f) : Measurable fun x ↦ (x ^ 2 + 1) * f x - 3 := by
  fun_prop

/-- 练习 16.4（★★）：`{x | f x ≤ 3 ∧ 0 ≤ f x}` 可测；用 `measurableSet_le`、`measurable_const` 与
`MeasurableSet.inter`（`measurability` 也行）。 -/
theorem ex_16_4 (f : ℝ → ℝ) (hf : Measurable f) : MeasurableSet {x | f x ≤ 3 ∧ 0 ≤ f x} :=
  (measurableSet_le hf measurable_const).inter (measurableSet_le measurable_const hf)

/-- 练习 16.5（★★）：`ℕ → ℝ` 上由前两个坐标定义的事件可测；用 `measurableSet_lt`、
`measurable_pi_apply`，或把集合写成 `{ω | p ω}` 后用 `measurableSet_setOfPred.2` 与 `fun_prop`。 -/
theorem ex_16_5 : MeasurableSet {ω : ℕ → ℝ | ω 0 + ω 1 < 1} :=
  measurableSet_lt (by fun_prop) measurable_const

/-- 练习 16.6（★★）：三个集合的联合界；对 `μ ((s ∪ t) ∪ u)` 用两次 `measure_union_le`，
中间用 `calc` 与 `gcongr`（第 11 章）。 -/
theorem ex_16_6 {α : Type*} [MeasurableSpace α] (μ : Measure α) (s t u : Set α) :
    μ (s ∪ t ∪ u) ≤ μ s + μ t + μ u := by
  calc μ (s ∪ t ∪ u) ≤ μ (s ∪ t) + μ u := measure_union_le _ _
    _ ≤ μ s + μ t + μ u := by gcongr; exact measure_union_le _ _

/-- 练习 16.7（★★）：有限测度的容斥；先用 `measureReal_union_add_inter`（注意它的可测性假设落在
哪个集合上；不确定名字时用 `exact?` 找），再用 `linarith`。 -/
theorem ex_16_7 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (s t : Set α)
    (ht : MeasurableSet t) : μ.real (s ∪ t) = μ.real s + μ.real t - μ.real (s ∩ t) := by
  have h := measureReal_union_add_inter (μ := μ) (s := s) ht
  linarith

/-- 练习 16.8（★）：有限测度下，`ℝ≥0∞` 里的和读成实数就是 `μ.real` 的和。用 `ENNReal.toReal_add`
（两个有限性假设由 `measure_ne_top` 或 `finiteness` 给出）与 `measureReal_def`。 -/
theorem ex_16_8 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (s t : Set α) :
    (μ s + μ t).toReal = μ.real s + μ.real t := by
  rw [ENNReal.toReal_add (measure_ne_top μ s) (measure_ne_top μ t), measureReal_def,
    measureReal_def]

/-- 练习 16.9（★）：几乎处处的传递；用 `filter_upwards [h₁, h₂] with x hx₁ hx₂`（第 14 章）。 -/
theorem ex_16_9 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g h : α → ℝ)
    (h₁ : ∀ᵐ x ∂μ, f x ≤ g x) (h₂ : ∀ᵐ x ∂μ, g x < h x) : ∀ᵐ x ∂μ, f x < h x := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact lt_of_le_of_lt hx₁ hx₂

/-- 练习 16.10（★★）：几乎处处相等给出积分的比例关系。先用 `integral_congr_ae` 把 `f` 换成
`fun x ↦ 2 * g x`（需要 `f =ᵐ[μ] fun x ↦ 2 * g x`，就是 `h`），再用 `integral_const_mul`。 -/
theorem ex_16_10 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (h : ∀ᵐ x ∂μ, f x = 2 * g x) : ∫ x, f x ∂μ = 2 * ∫ x, g x ∂μ := by
  have h' : f =ᵐ[μ] fun x ↦ 2 * g x := h
  rw [integral_congr_ae h', integral_const_mul]

/-- 练习 16.11（★★）：狄拉克测度加勒贝格测度。用 `Measure.add_apply`、`Measure.dirac_apply_of_mem`、
`Real.volume_Icc` 与 `ENNReal.ofReal` 的数值化简（`norm_num`）。 -/
theorem ex_16_11 : (Measure.dirac (2 : ℝ) + volume : Measure ℝ) (Set.Icc 0 3) = 4 := by
  rw [Measure.add_apply, Measure.dirac_apply_of_mem (by norm_num), Real.volume_Icc]
  norm_num

/-- 练习 16.12（★★）：积分的线性。用 `integral_add`（可积性：`hf.const_mul`、`integrable_const`）、
`integral_const_mul`、`integral_const`。 -/
theorem ex_16_12 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) :
    ∫ x, (3 * f x + 2) ∂μ = 3 * ∫ x, f x ∂μ + 2 * μ.real Set.univ := by
  rw [integral_add (hf.const_mul 3) (integrable_const 2), integral_const_mul, integral_const,
    smul_eq_mul]
  ring

/-- 练习 16.13（★★）：前推测度。狄拉克测度沿 `x ↦ 2 * x` 前推，仍是狄拉克测度。用
`Measure.map_dirac'`（需要 `Measurable`，交给 `fun_prop`）。 -/
theorem ex_16_13 (a : ℝ) :
    (Measure.dirac a).map (fun x : ℝ ↦ 2 * x) = Measure.dirac (2 * a) := by
  rw [Measure.map_dirac' (by fun_prop)]

/-- 练习 16.14（★★）：`Fin 3` 上计数测度的积分是有限和。用 `integral_count`、`Fin.sum_univ_three`
（第 12 章），再 `norm_num`。 -/
theorem ex_16_14 : ∫ x : Fin 3, ((x : ℕ) : ℝ) ∂(Measure.count : Measure (Fin 3)) = 3 := by
  rw [integral_count, Fin.sum_univ_three]
  norm_num

/-- 练习 16.15（★★）：两次抛硬币都是正面的概率是 `1 / 4`。把集合写成 `Finset.filter` 的强制转换
（像 `prob_head` 的证明），基数用 `decide` 算；这里的样本空间就是 `Coins 2`。 -/
theorem ex_16_15 :
    (uniformOn (Set.univ : Set (Fin 2 → Bool))).real {ω | ω 0 = true ∧ ω 1 = true} = 1 / 4 := by
  have h : {ω : Fin 2 → Bool | ω 0 = true ∧ ω 1 = true} =
      ((Finset.univ.filter fun ω : Fin 2 → Bool ↦ ω 0 = true ∧ ω 1 = true : Finset _) :
        Set _) := by
    ext ω
    simp
  have hc : (Finset.univ.filter fun ω : Fin 2 → Bool ↦ ω 0 = true ∧ ω 1 = true).card = 1 := by
    decide
  rw [h, measureReal_def, uniformOn_univ, Measure.count_apply_finset, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, hc]
  simp

end Exercises

end Solutions.Ch16

end
