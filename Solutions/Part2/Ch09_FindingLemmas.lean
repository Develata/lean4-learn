module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Set.Basic

/-!
# 第 9 章　答案

`Lean4Learn/Part2/Ch09_FindingLemmas.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；证明是一行，
随后的注释写出找到的引理名与找法。
-/

@[expose] public section

namespace Solutions.Ch09

/-- 练习 9.1（★）：按 `nonneg` 的命名规则猜名字。 -/
theorem ex_9_1 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := mul_nonneg hx hy
-- `nonneg` 规则：`mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b`。

/-- 练习 9.2（★）：平方非负；`x ^ 2` 在名字里怎么写，见第 2 节的词典。 -/
theorem ex_9_2 (x : ℝ) : 0 ≤ x ^ 2 := sq_nonneg x
-- `sq` 指 `x ^ 2`，`nonneg` 指 `0 ≤`（别名 `pow_two_nonneg` 也存在）。

/-- 练习 9.3（★）：第 3 章的合取；点记号。 -/
theorem ex_9_3 (p q : Prop) (h : p ∧ q) : q ∧ p := h.symm
-- `And.symm`，点记号 `h.symm`；等价于 `And.symm h` 或 `⟨h.2, h.1⟩`。

/-- 练习 9.4（★★）：第 2 章的不等式；点记号，名字里有 `not` 与 `ge`。 -/
theorem ex_9_4 (a b : ℝ) (h : a < b) : ¬b ≤ a := h.not_ge
-- `LT.lt.not_ge : a < b → ¬b ≤ a`（`not_le_of_gt` 的别名），点记号 `h.not_ge`。

/-- 练习 9.5（★★）：读成名字：`0 < x⁻¹` 是一个 `↔` 的一边，用 `.mpr`。 -/
theorem ex_9_5 (x : ℝ) (hx : 0 < x) : 0 < x⁻¹ := inv_pos.mpr hx
-- `inv_pos : 0 < a⁻¹ ↔ 0 < a`，`.mpr` 从右到左。

/-- 练习 9.6（★★）：`_left` 还是 `_right`？用 `#check` 看方向。 -/
theorem ex_9_6 (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := add_le_add_left h c
-- `add_le_add_left bc a : b + a ≤ c + a`：`a` 加在右边（与直觉相反）。

/-- 练习 9.7（★★★）：绝对值的三角不等式；加法名字由 `to_additive` 生成（第 12 节），先试 `exact?`。 -/
theorem ex_9_7 (a b : ℝ) : |a + b| ≤ |a| + |b| := abs_add_le a b
-- `abs_add_le`，由乘法版本 `mabs_mul_le` 经 `to_additive` 生成。

/-- 练习 9.8（★★）：第 8 章的 cast（类型转换）；`cast`、`le`，用 `↔`。 -/
theorem ex_9_8 (a b : ℕ) (h : a ≤ b) : (a : ℝ) ≤ b := Nat.cast_le.mpr h
-- `Nat.cast_le : ↑m ≤ ↑n ↔ m ≤ n`，`.mpr` 把 `ℕ` 上的不等式搬到 `ℝ`。

/-- 练习 9.9（★★★）：有限和非负；这个加法名字也由 `to_additive` 生成，`rg` 搜不到它的声明。 -/
theorem ex_9_9 (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i :=
  Finset.sum_nonneg h
-- `Finset.sum_nonneg`，由 `Finset.one_le_prod` 经 `to_additive` 生成，
-- 所以 `rg "theorem sum_nonneg"` 找不到声明。

/-- 练习 9.10（★）：第 7 章的集合；`inter`、`subset`、`left`。 -/
theorem ex_9_10 (s t : Set ℕ) : s ∩ t ⊆ s := Set.inter_subset_left
-- `Set.inter_subset_left : s ∩ t ⊆ s`，`s`、`t` 隐式。

/-- 练习 9.11（★★）：第 8 章的 cast；`inj` 与 `injective` 哪一个是 `↔`？ -/
theorem ex_9_11 (a b : ℕ) (h : (a : ℝ) = b) : a = b := Nat.cast_inj.mp h
-- `Nat.cast_inj : ↑m = ↑n ↔ m = n`，`.mp` 正向；`Nat.cast_injective h` 也行
-- （`injective` 是 `Function.Injective` 本身）。

/-- 练习 9.12（★）：第 7 章的集合；旧名 `Set.eq_mem_setOf` 已弃用，用它的新名字（`setOf` 变成了 `ofPred`）。 -/
theorem ex_9_12 (p : ℕ → Prop) : p = (· ∈ {a | p a}) :=
  Set.eq_mem_ofPred p
-- 旧名 `Set.eq_mem_setOf` 自 2026-07-09 弃用，新名 `Set.eq_mem_ofPred`（参数 `p` 显式）。

/-- 练习 9.13（★★）：整除与乘法；用 `exact?` 找，再找一个点记号形式的写法。 -/
theorem ex_9_13 (a b c : ℕ) (h : a ∣ b) : a ∣ b * c := h.mul_right c
-- 点记号 `Dvd.dvd.mul_right h c`（`dvd_mul_of_dvd_left` 的别名）。

/-- 练习 9.14（★★）：乘积为零；先拆成析取，再用第 4 章的消去。 -/
theorem ex_9_14 (a b : ℝ) (h : a * b = 0) (ha : a ≠ 0) : b = 0 := (mul_eq_zero.mp h).resolve_left ha
-- `mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0`，再用 `Or.resolve_left` 排除 `a = 0`。

/-- 练习 9.15（★★）：除法与不等式；`₀` 版本，注意假设顺序。 -/
theorem ex_9_15 (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := (le_div_iff₀ hc).mpr h
-- `le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b`，`.mpr` 从右到左。

end Solutions.Ch09

end
