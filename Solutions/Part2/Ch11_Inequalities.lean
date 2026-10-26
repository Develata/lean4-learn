module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 11 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part2/Ch11_Inequalities.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch11

/-- 练习 11.1（★）：去掉 `pow_le_pow_left₀` 的非负条件，命题为假；证明它的否定。
提示：取 `a = -3`，`b = -2`（本章 §4 有类似的例子）。 -/
theorem ex_11_1 : ¬ ∀ a b : ℝ, a ≤ b → a ^ 2 ≤ b ^ 2 := by
  intro h
  have h1 := h (-3) (-2) (by norm_num)
  norm_num at h1

/-- 练习 11.2（★）：三角不等式的变形；写成两步的 `calc`，用 `abs_add_le`。
提示：`a - c = (a - b) + (b - c)`。 -/
theorem ex_11_2 (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
  calc
    |a - c| = |(a - b) + (b - c)| := by congr 1; ring
    _ ≤ |a - b| + |b - c| := abs_add_le _ _

/-- 练习 11.3（★★）：先用 `abs_lt.1` 拆开假设，再用 `abs_lt.2` 构造结论。 -/
theorem ex_11_3 (x : ℝ) (h : |x - 2| < 1) : |x ^ 2 - 4| < 5 := by
  obtain ⟨h1, h2⟩ := abs_lt.1 h   -- -1 < x - 2，x - 2 < 1
  exact abs_lt.2 ⟨by nlinarith, by nlinarith⟩

/-- 练习 11.4（★）：先用 `div_lt_iff₀` 去掉分母（本章 §2），再用 `linarith`；副条件用 `positivity`。 -/
theorem ex_11_4 (a : ℝ) (ha : 0 ≤ a) : a / (a + 1) < 1 := by
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- 练习 11.5（★）：`Real.sqrt` 的垃圾值；这个命题为假，证明它的否定（本章 §6 有类似的例子）。 -/
theorem ex_11_5 : ¬ ∀ x : ℝ, √x ^ 2 = x := by
  intro h
  have h1 := h (-1)
  rw [Real.sqrt_eq_zero_of_nonpos (by norm_num)] at h1
  norm_num at h1

/-- 练习 11.6（★★）：`min` 与 `max`；先 `rcases le_total a b`（本章 §5），再重写。 -/
theorem ex_11_6 (a b : ℝ) : max a b - min a b = |a - b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]

/-- 练习 11.7（★★）：`gcongr` 加 `calc`；先说明 `0 ≤ b`，再让 `gcongr` 逐项比较
`a ^ 2 ≤ b ^ 2` 与 `3 * a ≤ 3 * b`。 -/
theorem ex_11_7 (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 + 3 * a ≤ b ^ 2 + 3 * b := by
  have hb : 0 ≤ b := ha.trans hab
  calc
    a ^ 2 + 3 * a ≤ b ^ 2 + 3 * a := by gcongr
    _ ≤ b ^ 2 + 3 * b := by gcongr

/-- 练习 11.8（★★）：`log x ≤ 2 * (√x - 1)`；对 `√x` 用 `Real.log_le_sub_one_of_pos`，
再用 `Real.log_sqrt`（`Real.log √x = Real.log x / 2`，需要 `0 ≤ x`）与 `Real.sqrt_pos`
（`0 < √x ↔ 0 < x`）。 -/
theorem ex_11_8 (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * (√x - 1) := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)   -- log √x ≤ √x - 1
  rw [Real.log_sqrt hx.le] at h
  linarith

/-- 练习 11.9（★）：`Real.log x < x`；用 `Real.log_le_sub_one_of_pos` 与 `linarith`。 -/
theorem ex_11_9 (x : ℝ) (hx : 0 < x) : Real.log x < x := by
  have h := Real.log_le_sub_one_of_pos hx
  linarith

/-- 练习 11.10（★★）：逐项绝对值有界则和有界；用 `Finset.abs_sum_le_sum_abs`、
`Finset.sum_le_sum`，与本章 §8 的 `sum_le_card_mul` 同样的收尾。 -/
theorem ex_11_10 (s : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) (h : ∀ i ∈ s, |f i| ≤ c) :
    |∑ i ∈ s, f i| ≤ s.card * c := by
  calc
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := Finset.abs_sum_le_sum_abs f s
    _ ≤ ∑ i ∈ s, c := Finset.sum_le_sum h
    _ = s.card * c := by simp

/-- 练习 11.11（★）：ε–δ 形式的存在性命题。取 `δ = ε / 3`；用 `refine ⟨_, _, fun x hx ↦ ?_⟩`
（第 4 章）搭骨架，再用 `abs_lt` 拆开与构造。 -/
theorem ex_11_11 (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ x : ℝ, |x - 1| < δ → |3 * x - 3| < ε := by
  refine ⟨ε / 3, by positivity, fun x hx ↦ ?_⟩
  obtain ⟨h1, h2⟩ := abs_lt.1 hx
  exact abs_lt.2 ⟨by linarith, by linarith⟩

/-- 练习 11.12（★★）：两点的琴生不等式；用 `convexOn_exp.2`，权重取 `1 / 2`，
再用 `smul_eq_mul` 化简。注意 `(x + y) / 2` 与 `1 / 2 * x + 1 / 2 * y` 在 `Real.exp` 里面，
`linarith` 把两个 `Real.exp (…)` 当作不同的原子：先用 `ring` 证明二者相等并 `rw`（本章 §9.3）。 -/
theorem ex_11_12 (x y : ℝ) : Real.exp ((x + y) / 2) ≤ (Real.exp x + Real.exp y) / 2 := by
  have h := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : (x + y) / 2 = 1 / 2 * x + 1 / 2 * y := by ring
  rw [e]
  linarith

/-- 练习 11.13（★★）：三个变量的均值不等式（立方形式）；差是
`(a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2`。记 `hs : 0 ≤ a + b + c`，
给 `nlinarith` 三个提示 `mul_nonneg hs (sq_nonneg (a - b))`，以及对 `(b - c)`、`(c - a)` 的同类项。 -/
theorem ex_11_13 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  nlinarith [mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (a - b)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (b - c)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (c - a))]

/-- 练习 11.14（★★★）：伯努利不等式；对 `n` 归纳，归纳步里 `rw [pow_succ]`，`push_cast`，
再 `nlinarith`，提示为 `mul_nonneg (sub_nonneg.2 ih) h1` 与
`mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)`，
其中 `h1 : 0 ≤ 1 + x`。Mathlib 里是 `one_add_mul_le_pow`，这里不许用它，要你手工证明。 -/
theorem ex_11_14 (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    push_cast
    have h1 : 0 ≤ 1 + x := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 ih) h1, mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)]

/-- 练习 11.15（★★★）：`(1 + x / n) ^ n ≤ exp x`。仿 `one_sub_pow_le_exp`：先证
`0 ≤ 1 + x / n` 与 `1 + x / n ≤ exp (x / n)`，再 `pow_le_pow_left₀` 与 `Real.exp_nat_mul`。 -/
theorem ex_11_15 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : -(n : ℝ) ≤ x) :
    (1 + x / n) ^ n ≤ Real.exp x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := hn'.ne'
  have h0 : 0 ≤ 1 + x / n := by
    have : -1 ≤ x / n := by
      rw [le_div_iff₀ hn']
      linarith
    linarith
  calc
    (1 + x / n) ^ n ≤ Real.exp (x / n) ^ n :=
      pow_le_pow_left₀ h0 (by linarith [Real.add_one_le_exp (x / n)]) n
    _ = Real.exp (n * (x / n)) := (Real.exp_nat_mul (x / n) n).symm
    _ = Real.exp x := by congr 1; field_simp

end Solutions.Ch11

end
