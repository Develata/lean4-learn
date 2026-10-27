module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 19 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part3/Ch19_FiniteProbability.lean` 逐字相同，只是证明体已补全。
答案文件不导入章节文件，所以练习 19.6、19.13、19.14 用到的本章引理在这里重新证明了一遍：
`integral_uniformOn_univ`（连同它依赖的两条均匀分布引理）、`card_agree`、`expect_agree`、
`exists_avoid_expect`；另有辅助的 `avoid_windows`、`window`、`card_window`。
-/

@[expose] public section

namespace Solutions.Ch19

section MeasureHelpers

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem uniformOn_univ_apply_finset (A : Finset Ω) :
    uniformOn (Set.univ : Set Ω) (A : Set Ω) = (A.card : ℝ≥0∞) / (Fintype.card Ω : ℝ≥0∞) := by
  classical
  rw [← Finset.coe_univ, uniformOn_apply_finset, Finset.univ_inter, Finset.card_univ]

theorem uniformOn_univ_real_finset (A : Finset Ω) :
    (uniformOn (Set.univ : Set Ω)).real (A : Set Ω) = A.card / Fintype.card Ω := by
  rw [measureReal_def, uniformOn_univ_apply_finset, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

theorem integral_uniformOn_univ [Nonempty Ω] (f : Ω → ℝ) :
    ∫ ω, f ω ∂(uniformOn (Set.univ : Set Ω)) = 𝔼 ω, f ω := by
  rw [integral_fintype Integrable.of_finite, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have h := uniformOn_univ_real_finset ({x} : Finset Ω)
  rw [Finset.coe_singleton, Finset.card_singleton] at h
  rw [h, smul_eq_mul]
  push_cast
  ring

end MeasureHelpers

section Helpers

open scoped BigOperators

theorem exists_avoid_expect {Ω κ : Type} [Fintype Ω] [Nonempty Ω] (I : Finset κ) (A : κ → Ω → Prop)
    [∀ i, DecidablePred (A i)] (h : ∑ i ∈ I, 𝔼 ω, (if A i ω then (1 : ℝ) else 0) < 1) :
    ∃ ω, ∀ i ∈ I, ¬ A i ω := by
  rw [← Finset.expect_sum_comm] at h
  obtain ⟨ω, -, hω⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty h
  refine ⟨ω, fun i hi hA ↦ ?_⟩
  have h1 : (if A i ω then (1 : ℝ) else 0) ≤ ∑ j ∈ I, if A j ω then (1 : ℝ) else 0 :=
    Finset.single_le_sum (f := fun j ↦ if A j ω then (1 : ℝ) else 0)
      (fun j _ ↦ by split_ifs <;> norm_num) hi
  have h2 : (1 : ℝ) = if A i ω then 1 else 0 := by simp [hA]
  linarith

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem card_agree (T : Finset ι) (b : Bool) :
    (Finset.univ.filter fun c : ι → Bool ↦ ∀ i ∈ T, c i = b).card =
      2 ^ (Fintype.card ι - T.card) := by
  have h : (Finset.univ.filter fun c : ι → Bool ↦ ∀ i ∈ T, c i = b) =
      Fintype.piFinset (fun i ↦ if i ∈ T then {b} else Finset.univ) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ T
      · simp [hi, h i hi]
      · simp [hi]
    · intro h i hi
      simpa [hi] using h i
  rw [h, Fintype.card_piFinset]
  have h2 : ∀ i, (if i ∈ T then ({b} : Finset Bool) else Finset.univ).card =
      if i ∈ T then 1 else 2 := by
    intro i
    by_cases hi : i ∈ T <;> simp [hi]
  simp only [h2]
  have hc : (Finset.univ.filter fun x ↦ x ∉ T) = Tᶜ := by
    ext x
    simp
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hc, Finset.card_compl]

theorem expect_agree (T : Finset ι) (b : Bool) :
    𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then (1 : ℝ) else 0) = (1 / 2) ^ T.card := by
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole, card_agree, Fintype.card_fun,
    Fintype.card_bool]
  obtain ⟨d, hd⟩ : ∃ d, Fintype.card ι = T.card + d :=
    ⟨Fintype.card ι - T.card, by have := Finset.card_le_univ T; omega⟩
  rw [hd, Nat.add_sub_cancel_left]
  push_cast
  rw [one_div, inv_pow, pow_add]
  field_simp

/-- 一般形式的联合界：每个坏事件「指标 `x` 的窗口 `T x` 全取 `b x`」的概率是 `(1/2) ^ m`，
共 `#I` 个，`#I * (1/2) ^ m < 1` 则存在函数避开所有坏事件。 -/
theorem avoid_windows {κ : Type} (I : Finset κ) (T : κ → Finset ι) (b : κ → Bool) (m : ℕ)
    (hT : ∀ x ∈ I, (T x).card = m) (h : (I.card : ℝ) * (1 / 2) ^ m < 1) :
    ∃ c : ι → Bool, ∀ x ∈ I, ¬ ∀ i ∈ T x, c i = b x := by
  have : Nonempty (ι → Bool) := ⟨fun _ ↦ true⟩
  refine exists_avoid_expect I (fun (x : κ) (c : ι → Bool) ↦ ∀ i ∈ T x, c i = b x) ?_
  have h2 : ∑ x ∈ I, 𝔼 c : ι → Bool, (if ∀ i ∈ T x, c i = b x then (1 : ℝ) else 0) =
      ∑ _x ∈ I, (1 / 2 : ℝ) ^ m :=
    Finset.sum_congr rfl fun x hx ↦ by rw [expect_agree, hT x hx]
  rw [h2, Finset.sum_const, nsmul_eq_mul]
  exact h

end Helpers

/-- 辅助定义：长为 6 的窗口 `i, …, i + 5`（练习 19.14）。 -/
def window (i : Fin 15) : Finset (Fin 20) :=
  Finset.univ.filter fun j : Fin 20 ↦ i.val ≤ j.val ∧ j.val < i.val + 6

theorem card_window : ∀ i, (window i).card = 6 := by decide +kernel

section Exercises

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- 练习 19.1（★）：`Fin 4` 上 `i.val` 的平均是 `3 / 2`（§1）。用 `Fintype.expect_eq_sum_div_card` 与
`Fin.sum_univ_four`（第 12 章 `Fin.sum_univ_three` 的四元素版本），最后 `norm_num`。 -/
theorem ex_19_1 : 𝔼 i : Fin 4, ((i : ℕ) : ℝ) = 3 / 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_four]
  norm_num

/-- 练习 19.2（★）：期望的线性性（§1）。用 `Finset.expect_add_distrib` 与 `Finset.mul_expect`。 -/
theorem ex_19_2 {ι : Type} [Fintype ι] (f g : ι → ℝ) :
    𝔼 i, (f i + 2 * g i) = 𝔼 i, f i + 2 * 𝔼 i, g i := by
  rw [Finset.expect_add_distrib, Finset.mul_expect]

/-- 练习 19.3（★）：平均值夹在最小值与最大值之间（§2）：既有点不超过平均，也有点不低于平均。
用 `Finset.exists_le_of_expect_le` 与 `Finset.exists_le_of_le_expect`，`s := Finset.univ`。 -/
theorem ex_19_3 {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∃ i, f i ≤ 𝔼 j, f j) ∧ ∃ i, 𝔼 j, f j ≤ f i := by
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty (le_refl (𝔼 j, f j))
    exact ⟨i, hi⟩
  · obtain ⟨i, -, hi⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty (le_refl (𝔼 j, f j))
    exact ⟨i, hi⟩

/-- 练习 19.4（★）：两个函数之和的一阶矩（§2）：存在点使 `f i + g i` 不超过两个平均之和。
先用线性性把右端写成 `𝔼 j, (f j + g j)`。 -/
theorem ex_19_4 {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) :
    ∃ i, f i + g i ≤ 𝔼 j, f j + 𝔼 j, g j := by
  have h : 𝔼 j, (f j + g j) = 𝔼 j, f j + 𝔼 j, g j := Finset.expect_add_distrib _ _ _
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_expect_le Finset.univ_nonempty (le_of_eq h)
  exact ⟨i, hi⟩

/-- 练习 19.5（★★）：有限平均版的联合界（§1）：并事件的指示函数不超过两个指示函数之和，
再用 `Finset.expect_le_expect` 与 `Finset.expect_add_distrib`。 -/
theorem ex_19_5 {ι : Type} [Fintype ι] (p q : ι → Prop) [DecidablePred p] [DecidablePred q] :
    𝔼 i, (if p i ∨ q i then (1 : ℝ) else 0) ≤
      𝔼 i, (if p i then (1 : ℝ) else 0) + 𝔼 i, (if q i then (1 : ℝ) else 0) := by
  rw [← Finset.expect_add_distrib]
  refine Finset.expect_le_expect fun i _ ↦ ?_
  by_cases hp : p i <;> by_cases hq : q i <;> norm_num [hp, hq]

/-- 练习 19.6（★★）：均匀分布下的积分就是概率（§4）。三枚公平硬币里第一枚是正面的概率是 `1/2`，
写成积分：指示函数 `if ω 0 = true then 1 else 0` 关于 `uniformOn Set.univ` 的积分是 `1/2`。
提示：先用 `integral_uniformOn_univ`（`∫ ω, f ω ∂uniformOn Set.univ = 𝔼 ω, f ω`）换成有限平均，
再用 `expect_agree`（`𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then 1 else 0) = (1/2) ^ #T`），
取 `T = {0}`。 -/
theorem ex_19_6 :
    ∫ ω : Fin 3 → Bool, (if ω 0 = true then (1 : ℝ) else 0)
      ∂(uniformOn (Set.univ : Set (Fin 3 → Bool))) = 1 / 2 := by
  rw [integral_uniformOn_univ]
  simpa using expect_agree ({0} : Finset (Fin 3)) true

/-- 练习 19.7（★）：`5` 个顶点的图没有 `6`-团，补图也没有（§6.3，第 18 章）。
用 `SimpleGraph.cliqueFree_of_card_lt` 与 `Fintype.card_fin`。 -/
theorem ex_19_7 (G : SimpleGraph (Fin 5)) : G.CliqueFree 6 ∧ Gᶜ.CliqueFree 6 := by
  exact ⟨SimpleGraph.cliqueFree_of_card_lt (by simp), SimpleGraph.cliqueFree_of_card_lt (by simp)⟩

/-- 练习 19.8（★）：均匀分布下的一阶矩，另一个方向（§4）：存在点使 `f ω` 不小于积分。
用 `exists_integral_le`（与 `exists_le_integral` 成对）与 `Integrable.of_finite`。 -/
theorem ex_19_8 {Ω : Type} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (f : Ω → ℝ) : ∃ ω, ∫ ω, f ω ∂(uniformOn (Set.univ : Set Ω)) ≤ f ω := by
  exact exists_integral_le Integrable.of_finite

/-- 练习 19.9（★★）：有限样本空间上的马尔可夫不等式（§1）。非负函数 `f`，任意实数 `a`：
`a * P(f ≥ a) ≤ 𝔼 f`。用 `Finset.mul_expect` 与 `Finset.expect_le_expect`，逐点 `split_ifs`。 -/
theorem ex_19_9 {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (a : ℝ) :
    a * 𝔼 i, (if a ≤ f i then (1 : ℝ) else 0) ≤ 𝔼 i, f i := by
  rw [Finset.mul_expect]
  refine Finset.expect_le_expect fun i _ ↦ ?_
  split_ifs with h
  · linarith
  · simpa using hf i

/-- 练习 19.10（★）：拉姆齐下界在 `n = 16`、`k = 8` 时的数值验证（§6.1）：`16² = 2 ^ 8`，
`2 * C(16, 8) < 2 ^ C(8, 2)`。用 `decide +kernel`（第 5 章）。 -/
theorem ex_19_10 : 2 * Nat.choose 16 8 < 2 ^ Nat.choose 8 2 := by
  decide +kernel

/-- 练习 19.11（★★）：`n ≤ 2 ^ (k / 2)` 与 `n ^ 2 ≤ 2 ^ k` 等价（§5 开头）。右边的 `2 ^ (k / 2)` 是实数
幂 `Real.rpow`，`k / 2` 是实数除法。提示：先证 `(2 ^ ((k : ℝ) / 2)) ^ 2 = 2 ^ k`
（`Real.rpow_natCast`、`Real.rpow_mul`，这两个名字是新的，用 `rw [← Real.rpow_natCast]` 的方向把 `^ 2`
变成实数幂再合并），再用第 11 章的 `sq_le_sq₀`（两边非负时 `a ^ 2 ≤ b ^ 2 ↔ a ≤ b`）。 -/
theorem ex_19_11 (n k : ℕ) : ((n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2)) ↔ n ^ 2 ≤ 2 ^ k := by
  have h : ((2 : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = 2 ^ k := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hx : 0 ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := by positivity
  rw [← sq_le_sq₀ (Nat.cast_nonneg n) hx, h]
  norm_cast

/-- 练习 19.12（★）：`setBer(u, p)` 取到空集的概率是 `(1 - p) ^ u.ncard`（§7）。用
`setBernoulli_real_singleton`，`p ^ 0 = 1`，`u \ ∅ = u`（`Set.diff_empty`），`Set.ncard_empty`。 -/
theorem ex_19_12 (u : Set (Fin 5)) (p : unitInterval) :
    (setBer(u, p)).real {∅} = (1 - p : ℝ) ^ u.ncard := by
  rw [setBernoulli_real_singleton p (Set.empty_subset u) u.toFinite]
  simp

/-- 练习 19.13（★★）：坐标集不相交的两个事件在均匀平均下独立（§3，`expect_agree`）。
`T` 与 `U` 不相交时，「`T` 全取 `b`」与「`U` 全取 `b`」的指示函数乘积的平均等于平均的乘积。
提示：两个条件合起来就是「`T ∪ U` 全取 `b`」（`Finset.forall_mem_union`），三次用
`expect_agree`（`𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then 1 else 0) = (1/2) ^ #T`），
基数用 `Finset.card_union_of_disjoint`。拉姆齐问题里算单色集个数的协方差时，第一步就是它。 -/
theorem ex_19_13 {ι : Type} [Fintype ι] [DecidableEq ι] (T U : Finset ι) (hTU : Disjoint T U)
    (b : Bool) :
    𝔼 c : ι → Bool, (if (∀ i ∈ T, c i = b) ∧ (∀ i ∈ U, c i = b) then (1 : ℝ) else 0) =
      (𝔼 c : ι → Bool, if ∀ i ∈ T, c i = b then (1 : ℝ) else 0) *
        𝔼 c : ι → Bool, if ∀ i ∈ U, c i = b then (1 : ℝ) else 0 := by
  have h1 : (𝔼 c : ι → Bool, if (∀ i ∈ T, c i = b) ∧ (∀ i ∈ U, c i = b) then (1 : ℝ) else 0) =
      𝔼 c : ι → Bool, (if ∀ i ∈ T ∪ U, c i = b then (1 : ℝ) else 0) :=
    Finset.expect_congr rfl fun c _ ↦ if_congr Finset.forall_mem_union.symm rfl rfl
  rw [h1, expect_agree, expect_agree, expect_agree, Finset.card_union_of_disjoint hTU, pow_add]

/-- 练习 19.14（★★★）：存在长为 20 的 0-1 序列，其中任何 6 个相邻位置都不全相同（概率方法的联合界）。
坏事件 `A (i, b)`：位置 `i, …, i + 5` 全取 `b`，共 `15 * 2 = 30` 个，每个概率 `(1/2) ^ 6`，总和 `30/64 < 1`。
用 `exists_avoid_expect`（`∑ i ∈ I, 𝔼 ω, (if A i ω then 1 else 0) < 1` 推出 `∃ ω, ∀ i ∈ I, ¬ A i ω`）
和 `expect_agree`（`𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then 1 else 0) = (1/2) ^ #T`）；窗口写成
`T i := Finset.univ.filter fun j : Fin 20 ↦ i.val ≤ j.val ∧ j.val < i.val + 6`，
`(T i).card = 6` 可以对 `i : Fin 15` 用 `decide +kernel`。答案文件先证了一个一般的引理（`#I` 个窗口，
每个窗口大小为 `m`，`#I * (1/2) ^ m < 1`，则存在函数避开全部窗口），再套用它。 -/
theorem ex_19_14 : ∃ ω : Fin 20 → Bool, ∀ i : Fin 15, ∀ b : Bool,
    ¬ ∀ j : Fin 20, i.val ≤ j.val → j.val < i.val + 6 → ω j = b := by
  obtain ⟨ω, hω⟩ := avoid_windows (Finset.univ : Finset (Fin 15 × Bool)) (fun x ↦ window x.1)
    (fun x ↦ x.2) 6 (fun x _ ↦ card_window x.1) (by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      norm_num)
  refine ⟨ω, fun i b hb ↦ hω (i, b) (Finset.mem_univ _) fun j hj ↦ ?_⟩
  simp only [window, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hb j hj.1 hj.2

/-- 练习 19.15（★★）：`4` 个元素的随机子集恰有 `2` 个元素的概率是 `6 * p ^ 2 * (1 - p) ^ 2`
（§7，二项分布）。用 `map_ncard_setBernoulli_real_singleton`（`u.Finite`）、`Set.ncard_univ`，
`Nat.choose 4 2 = 6` 用 `decide`。 -/
theorem ex_19_15 (p : unitInterval) :
    (setBer((Set.univ : Set (Fin 4)), p).map Set.ncard).real {2} =
      6 * (p : ℝ) ^ 2 * (1 - p : ℝ) ^ 2 := by
  have h : Nat.choose 4 2 = 6 := by decide
  rw [map_ncard_setBernoulli_real_singleton Set.finite_univ, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin, h]
  norm_num

end Exercises

end Solutions.Ch19

end
