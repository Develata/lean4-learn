module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# 第 14 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part2/Ch14_Filters.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch14

open Filter
open scoped Topology

/-- 练习 14.1（★）：`3 / (n + 1) → 0`；用 `Tendsto.const_mul` 与
`tendsto_one_div_add_atTop_nhds_zero_nat`，再用 `simpa` 调整形状。 -/
theorem ex_14_1 : Tendsto (fun n : ℕ ↦ 3 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3
  simpa [div_eq_mul_inv] using h

/-- 练习 14.2（★）：最终 `4n ≤ n²`；用 `filter_upwards [eventually_ge_atTop 4] with n hn`，
再 `nlinarith`。 -/
theorem ex_14_2 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ n ^ 2 := by
  filter_upwards [eventually_ge_atTop 4] with n hn
  nlinarith

/-- 练习 14.3（★）：若 `u → 1`，则 `u n` 最终大于 `1 / 2`；用 `Tendsto.eventually` 与 `lt_mem_nhds`。 -/
theorem ex_14_3 (u : ℕ → ℝ) (h : Tendsto u atTop (𝓝 1)) : ∀ᶠ n in atTop, 1 / 2 < u n := by
  exact h.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))

/-- 练习 14.4（★★）：用 ε–N 证明 `(n + 1) / (n + 2) → 1`。取 `N > 1 / ε`；
先证 `(n + 1) / (n + 2) - 1 = -(1 / (n + 2))`（`field_simp`，`ring`）。 -/
theorem ex_14_4 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have key : ((n : ℝ) + 1) / ((n : ℝ) + 2) - 1 = -(1 / ((n : ℝ) + 2)) := by
    field_simp
    ring
  rw [Real.dist_eq, key, abs_neg, abs_of_pos (one_div_pos.2 hn2), div_lt_iff₀ hn2]
  rw [div_lt_iff₀ hε] at hN
  nlinarith [mul_le_mul_of_nonneg_left hNn hε.le]

/-- 练习 14.5（★）：从 `Tendsto` 取回 ε–N。收敛数列最终小于极限加一；用
`Metric.tendsto_atTop.1 h 1 one_pos`，再 `abs_lt`（第 11 章）。 -/
theorem ex_14_5 (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) :
    ∃ N : ℕ, ∀ n ≥ N, u n < a + 1 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h 1 one_pos
  refine ⟨N, fun n hn ↦ ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq] at h1
  linarith [(abs_lt.1 h1).2]

/-- 练习 14.6（★★★）：不用 `Tendsto.add`，只用 `Metric.tendsto_atTop` 证明和的极限。
对 `ε / 2` 取两个 `N`，再取 `max`；用 `Real.dist_eq` 把距离化成绝对值，
再用 `abs_add_le`（第 11 章）。 -/
theorem ex_14_6 (u v : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n ↦ u n + v n) atTop (𝓝 (a + b)) := by
  rw [Metric.tendsto_atTop] at hu hv ⊢
  intro ε hε
  obtain ⟨N₁, h₁⟩ := hu (ε / 2) (by positivity)
  obtain ⟨N₂, h₂⟩ := hv (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  have h1 := h₁ n (le_trans (le_max_left _ _) hn)
  have h2 := h₂ n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq] at h1 h2 ⊢
  calc
    |u n + v n - (a + b)| = |(u n - a) + (v n - b)| := by congr 1; ring
    _ ≤ |u n - a| + |v n - b| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-- 练习 14.7（★★）：单调收敛。若 `u` 单调、`u 0 = 1` 且处处 `u n ≤ 3`，则 `u` 收敛到某个
`L ≥ 1`；用 `tendsto_atTop_ciSup` 与 `Monotone.ge_of_tendsto`。 -/
theorem ex_14_7 (u : ℕ → ℝ) (hm : Monotone u) (h0 : u 0 = 1) (hb : ∀ n, u n ≤ 3) :
    ∃ L : ℝ, 1 ≤ L ∧ Tendsto u atTop (𝓝 L) := by
  have hbdd : BddAbove (Set.range u) := ⟨3, by rintro _ ⟨n, rfl⟩; exact hb n⟩
  have ht := tendsto_atTop_ciSup hm hbdd
  have h1 : u 0 ≤ ⨆ n, u n := hm.ge_of_tendsto ht 0
  rw [h0] at h1
  exact ⟨_, h1, ht⟩

/-- 练习 14.8（★★）：严格不等式在极限下不被保持。前一半：若 `u n > 0` 处处成立且 `u → a`，则 `a ≥ 0`
（`ge_of_tendsto'`）；后一半：「则 `a > 0`」不成立，反例取 `1 / (n + 1)`。 -/
theorem ex_14_8 :
    (∀ (u : ℕ → ℝ) (a : ℝ), (∀ n, 0 < u n) → Tendsto u atTop (𝓝 a) → 0 ≤ a) ∧
    ¬ (∀ (u : ℕ → ℝ) (a : ℝ), (∀ n, 0 < u n) → Tendsto u atTop (𝓝 a) → 0 < a) := by
  refine ⟨fun u a hu h ↦ ge_of_tendsto' h (fun n ↦ (hu n).le), fun H ↦ ?_⟩
  have key := H (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) 0
    (fun n ↦ by show (0 : ℝ) < 1 / ((n : ℝ) + 1); positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact lt_irrefl _ key

/-- 练习 14.9（★★★）：夹逼。`0 ≤ n / (n² + 1) ≤ 1 / n`（对 `n = 0` 两边都是 `0`：先
`rcases Nat.eq_zero_or_pos n`，另一支用 `div_le_div_iff₀` 与 `nlinarith`），上界用
`tendsto_one_div_atTop_nhds_zero_nat`。 -/
theorem ex_14_9 : Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) ^ 2 + 1)) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_atTop_nhds_zero_nat (fun n ↦ ?_) (fun n ↦ ?_)
  · show (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) ^ 2 + 1)
    positivity
  · show (n : ℝ) / ((n : ℝ) ^ 2 + 1) ≤ 1 / (n : ℝ)
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have hn : (0 : ℝ) < n := by exact_mod_cast hpos
      rw [div_le_div_iff₀ (by positivity) hn]
      nlinarith

/-- 练习 14.10（★★）：`n² = O(n³)`，即 `(fun n : ℕ ↦ (n : ℝ) ^ 2) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 3)`；
用 `Asymptotics.IsBigO.of_bound 1`、`filter_upwards [eventually_ge_atTop 1]`，
再用 `Real.norm_eq_abs` 与 `abs_of_nonneg` 去掉范数。 -/
theorem ex_14_10 : (fun n : ℕ ↦ (n : ℝ) ^ 2) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 3) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)]
  nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.2 h1)]

/-- 练习 14.11（★★）：比较判别法。`(1/3)^n * (1 + 1/(n+1)) ≤ 2 * (1/3)^n`；
用 `Summable.of_nonneg_of_le` 与 `Summable.mul_left`。 -/
theorem ex_14_11 : Summable (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n * (1 + 1 / ((n : ℝ) + 1))) := by
  have hg : Summable (fun n : ℕ ↦ 2 * (1 / 3 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (r := 1 / 3) (by norm_num) (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hp : (0 : ℝ) < (1 / 3) ^ n := by positivity
  nlinarith

/-- 练习 14.12（★★）：对 `n` 归纳（第 6 章）证明递推数列的通项。 -/
theorem ex_14_12 (u : ℕ → ℝ) (h0 : u 0 = 0) (h : ∀ n, u (n + 1) = (u n + 1) / 2) (n : ℕ) :
    u n = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [h, ih]
    ring

/-- 练习 14.13（★★★）：同一个递推数列收敛到 `1`。先用 14.12 得到通项，再用
`tendsto_pow_atTop_nhds_zero_of_lt_one`、`tendsto_const_nhds.sub` 与 `Tendsto.congr`。 -/
theorem ex_14_13 (u : ℕ → ℝ) (h0 : u 0 = 0) (h : ∀ n, u (n + 1) = (u n + 1) / 2) :
    Tendsto u atTop (𝓝 1) := by
  have hu : ∀ n, u n = 1 - (1 / 2 : ℝ) ^ n := fun n ↦ ex_14_12 u h0 h n
  have h1 : Tendsto (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h1
  rw [sub_zero] at h2
  exact h2.congr (fun n ↦ (hu n).symm)

/-- 练习 14.14（★）：连续函数的非零点集是开集：`{x | f x ≠ 0}` 是开集；
用原像 `f ⁻¹' {y | y ≠ 0}`、`isOpen_ne` 与 `Continuous.isOpen_preimage`（`hf.isOpen_preimage`）。 -/
theorem ex_14_14 (f : ℝ → ℝ) (hf : Continuous f) : IsOpen {x : ℝ | f x ≠ 0} := by
  exact hf.isOpen_preimage {y | y ≠ 0} isOpen_ne

/-- 练习 14.15（★★★）：`n` 不趋于 `0`。用 `Metric.tendsto_atTop`，`intro h`，对 `ε = 1`
取出 `N`，在 `n = max N 1` 处得到矛盾；不要用 `tendsto_nhds_unique`。 -/
theorem ex_14_15 : ¬ Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop (𝓝 0) := by
  intro h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h 1 one_pos
  have h1 := hN (max N 1) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Nat.cast_nonneg _)] at h1
  have h2 : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
  linarith

end Solutions.Ch14

end
