module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 12 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part2/Ch12_Finsets.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch12

open scoped Finset

/-- 练习 12.1（★）：前 `n` 个奇数之和是 `n ^ 2`。对 `n` 归纳，用 `Finset.sum_range_succ`（§3）。 -/
theorem ex_12_1 (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- 练习 12.2（★★）：阶乘的乘积表示。对 `n` 归纳，用 `Finset.prod_range_succ` 与 `Nat.factorial_succ`。
不许直接用 `Finset.prod_range_add_one_eq_factorial`（§3）。 -/
theorem ex_12_2 (n : ℕ) : ∏ i ∈ Finset.range n, (i + 1) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    ring

/-- 练习 12.3（★★）：像的个数（§2）。先证 `fun x ↦ 3 * x` 单射（第 7 章；`simpa using h` 或 `omega`），
再用 `Finset.card_image_of_injective` 与 `Finset.card_range`。 -/
theorem ex_12_3 (n : ℕ) : #((Finset.range n).image (fun x ↦ 3 * x)) = n := by
  have hinj : Function.Injective (fun x : ℕ ↦ 3 * x) := fun a b h ↦ by simpa using h
  rw [Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- 练习 12.4（★★）：容斥原理的减法形式。用 `Finset.card_union_add_card_inter`（§2）加 `omega`；
`ℕ` 的减法是截断的（第 2 章），`omega` 能处理。 -/
theorem ex_12_4 (s t : Finset ℕ) : #(s ∪ t) = #s + #t - #(s ∩ t) := by
  have := Finset.card_union_add_card_inter s t
  omega

/-- 练习 12.5（★★）：调和和不超过项数。用 `Finset.sum_le_sum`（第 11 章 §8）逐项比较成常数 `1`，
再用 `Finset.sum_const`（§3）；每项 `1 / (i + 1) ≤ 1` 用 `div_le_one₀` 与 `positivity`。 -/
theorem ex_12_5 (n : ℕ) : ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) ≤ n := by
  calc
    ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [div_le_one₀ (by positivity)]
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    _ = n := by simp

/-- 练习 12.6（★★）：整数上的裂项求和。注意函数体要加括号（§3）。对 `n` 归纳，归纳步里
`rw [Finset.sum_range_succ, ih]`，再 `push_cast` 与 `ring`。 -/
theorem ex_12_6 (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℤ) + 1) ^ 2 - (i : ℤ) ^ 2) = (n : ℤ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- 练习 12.7（★★）：用 `Finset.induction_on`（§5）证明积与和的关系：
`∏ i ∈ s, 2 ^ f i = 2 ^ ∑ i ∈ s, f i`。注意 `α` 是任意类型，要先 `classical`（§5、§11）。
归纳步用 `Finset.prod_insert`、`Finset.sum_insert` 与 `pow_add`；不许直接用 `Finset.prod_pow_eq_pow_sum`。 -/
theorem ex_12_7 {α : Type*} (s : Finset α) (f : α → ℕ) :
    ∏ i ∈ s, 2 ^ f i = 2 ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pow_add]

/-- 练习 12.8（★）：对严格小于关系做双重计数（§6）：
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`，关系取 `fun a b ↦ a < b`。 -/
theorem ex_12_8 (s : Finset ℕ) :
    ∑ a ∈ s, #{b ∈ s | a < b} = ∑ b ∈ s, #{a ∈ s | a < b} := by
  exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun a b ↦ a < b)

/-- 练习 12.9（★★）：抽屉原理（§7）。五个自然数里有两个模 `4` 同余。把 `i` 映到
`(⟨f i % 4, _⟩ : Fin 4)`，用 `Fintype.exists_ne_map_eq_of_card_lt`；`Nat.mod_lt` 给出 `f i % 4 < 4`。 -/
theorem ex_12_9 (f : Fin 5 → ℕ) : ∃ i j, i ≠ j ∧ f i % 4 = f j % 4 := by
  obtain ⟨i, j, hij, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i ↦ (⟨f i % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4)) (by simp)
  exact ⟨i, j, hij, by simpa using h⟩

/-- 练习 12.10（★★）：`{0, …, 9}` 的任意 `6` 元子集里有两个数之和为 `9`。抽屉是 `Finset.range 5`，
映射是 `fun x ↦ min x (9 - x)`（`{k, 9 - k}` 进同一个抽屉）。仿 §7 的 `exists_consecutive`：
先验证 `Set.MapsTo`（`omega` 认得 `min`），再 `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`。 -/
theorem ex_12_10 (s : Finset ℕ) (hs : s ⊆ Finset.range 10) (hc : 5 < #s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y = 9 := by
  have hmaps : Set.MapsTo (fun x ↦ min x (9 - x)) ↑s ↑(Finset.range 5) := by
    intro x hx
    have hx' := Finset.mem_range.1 (hs hx)
    show min x (9 - x) ∈ Finset.range 5
    rw [Finset.mem_range]
    omega
  have hcard : #(Finset.range 5) < #s := by
    rw [Finset.card_range]
    exact hc
  obtain ⟨x, hx, y, hy, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have heq' : min x (9 - x) = min y (9 - y) := heq
  have hx' := Finset.mem_range.1 (hs hx)
  have hy' := Finset.mem_range.1 (hs hy)
  exact ⟨x, hx, y, hy, hne, by omega⟩

/-- 练习 12.11（★）：帕斯卡恒等式的一个特例（§8）。`Nat.choose_succ_succ' n 1` 给出
`(n + 1).choose 2 = n.choose 1 + n.choose 2`（`1 + 1` 与 `2` 定义相等，可以用类型标注写成后者），
再用 `Nat.choose_one_right` 与 `omega`。 -/
theorem ex_12_11 (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
  rw [Nat.choose_one_right] at h
  omega

/-- 练习 12.12（★★）：`∑ 2 ^ m * C(n, m) = 3 ^ n`。取 `x = 2`、`y = 1` 套 `add_pow`（§8），
再用 `simp` 化简 `1 ^ (n - m)` 与强制转换。 -/
theorem ex_12_12 (n : ℕ) : ∑ m ∈ Finset.range (n + 1), 2 ^ m * n.choose m = 3 ^ n := by
  simpa using (add_pow (2 : ℕ) 1 n).symm

/-- 练习 12.13（★）：五元集有十个三元子集。`Finset.card_powersetCard`（§8），再 `decide`。 -/
theorem ex_12_13 {α : Type*} (s : Finset α) (h : #s = 5) : #(s.powersetCard 3) = 10 := by
  rw [Finset.card_powersetCard, h]
  decide

/-- 练习 12.14（★★）：`Set.Iio n` 的 `Set.ncard`（§10）。把 `Set.Iio n` 改写成 `↑(Finset.range n)`
（`Finset.coe_range`），再用 `Set.ncard_coe_finset` 与 `Finset.card_range`。 -/
theorem ex_12_14 (n : ℕ) : (Set.Iio n).ncard = n := by
  rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- 练习 12.15（★★★）：指示函数之和等于总数。思路：把两个和并成一个，证明每一项都是 `1`，再数项数。
每项需要对 `p i` 分情形（`by_cases`，第 4 章）；会用到 `Finset.sum_add_distrib`、`Finset.sum_congr`
（§3）与常数求和。 -/
theorem ex_12_15 (p : ℕ → Prop) [DecidablePred p] (s : Finset ℕ) :
    (∑ i ∈ s, if p i then (1 : ℝ) else 0) + ∑ i ∈ s, (if p i then (0 : ℝ) else 1) = #s := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i ∈ s, ((if p i then (1 : ℝ) else 0) + if p i then (0 : ℝ) else 1) = 1 := by
    intro i _
    by_cases hp : p i <;> simp [hp]
  rw [Finset.sum_congr rfl h]
  simp

end Solutions.Ch12

end
