module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 8 章　答案

`Lean4Learn/Part1/Ch08_TypeClasses.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；章节里练习
用到的结构体 `Aff`（及其 `Mul`、`One`、`Monoid` 实例）、`MaxNat` 与 `step` 在这里原样重述一遍，使本文件自成一体。
-/

@[expose] public section

namespace Solutions.Ch08

@[ext] structure Aff where
  a : ℤ
  b : ℤ
  deriving Repr, DecidableEq

instance : Mul Aff where
  mul f g := ⟨f.a * g.a, f.a * g.b + f.b⟩

instance : One Aff where
  one := ⟨1, 0⟩

theorem Aff.mul_def (f g : Aff) : f * g = ⟨f.a * g.a, f.a * g.b + f.b⟩ := rfl
theorem Aff.one_def : (1 : Aff) = ⟨1, 0⟩ := rfl

instance : Monoid Aff where
  mul_assoc f g h := by
    ext <;> simp [Aff.mul_def] <;> ring
  one_mul f := by
    ext <;> simp [Aff.mul_def, Aff.one_def]
  mul_one f := by
    ext <;> simp [Aff.mul_def, Aff.one_def]

structure MaxNat where
  val : ℕ

instance : Mul MaxNat := ⟨fun x y ↦ ⟨max x.val y.val⟩⟩
instance : One MaxNat := ⟨⟨0⟩⟩

noncomputable def step (x : ℝ) : ℕ := if 0 ≤ x then 1 else 0

/-- 练习 8.1（★）：把 `Field` 降成 `Monoid`。不写证明，让实例合成完成。 -/
abbrev ex_8_1 (K : Type*) [Field K] : Monoid K := inferInstance

/-- 练习 8.2（★）：交换环里 `a * b = 1` 则 `a ^ 2 * b ^ 2 = 1`。提示：`mul_pow` 是 `CommMonoid` 的引理。 -/
theorem ex_8_2 {R : Type*} [CommRing R] (a b : R) (h : a * b = 1) : a ^ 2 * b ^ 2 = 1 := by
  rw [← mul_pow, h, one_pow]

/-- 练习 8.3（★）：域里的通分。提示：`field_simp`（第 10 章详讲）。 -/
theorem ex_8_3 {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  field_simp
  ring

/-- 练习 8.4（★★）：有序域里的平均值不等式。提示：先证
`a / b + b / a - 2 = (a - b) ^ 2 / (a * b)`，再 `positivity`。 -/
theorem ex_8_4 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (a b : K)
    (ha : 0 < a) (hb : 0 < b) : 2 ≤ a / b + b / a := by
  have h : a / b + b / a - 2 = (a - b) ^ 2 / (a * b) := by
    field_simp
    ring
  have h2 : 0 ≤ (a - b) ^ 2 / (a * b) := by positivity
  linarith

/-- 练习 8.5（★★）：复习第 3、4 章。群里 `(a * b)⁻¹ = b⁻¹ * a⁻¹`，不直接用 `mul_inv_rev`。
提示：`inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b`，再用 `mul_assoc`、`mul_inv_cancel`。 -/
theorem ex_8_5 {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  inv_eq_of_mul_eq_one_right
    (by rw [mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul, mul_inv_cancel])

/-- 练习 8.6（★）：复习第 3 章的项模式。格里的不等式。提示：`inf_le_left`、`le_sup_left`。 -/
theorem ex_8_6 {α : Type*} [Lattice α] (a b c : α) (h : a ≤ c) : a ⊓ b ≤ c ⊔ b :=
  (inf_le_left.trans h).trans le_sup_left

/-- 练习 8.7（★★）：为 `MaxNat` 定义 `Monoid` 实例。提示：每条公理写成 `fun ⟨x⟩ ⟨y⟩ ⟨z⟩ ↦ …`，
再用 `congrArg MaxNat.mk` 配 `max_assoc`、`Nat.zero_max`、`Nat.max_zero`。 -/
abbrev ex_8_7 : Monoid MaxNat :=
  { mul_assoc := fun ⟨x⟩ ⟨y⟩ ⟨z⟩ ↦ congrArg MaxNat.mk (max_assoc x y z)
    one_mul := fun ⟨x⟩ ↦ congrArg MaxNat.mk (Nat.zero_max x)
    mul_one := fun ⟨x⟩ ↦ congrArg MaxNat.mk (Nat.max_zero x) }

/-- 练习 8.8（★）：复习第 5、6 章。`Aff` 的平方有显式公式。提示：`pow_two`、`Aff.mul_def`。 -/
theorem ex_8_8 (f : Aff) : f ^ 2 = ⟨f.a * f.a, f.a * f.b + f.b⟩ := by
  rw [pow_two, Aff.mul_def]

/-- 练习 8.9（★）：`ℕ` 的严格不等式给出 `ℝ` 里的 `+ 1` 不等式。提示：`Nat.succ_le_of_lt`。 -/
theorem ex_8_9 (n m : ℕ) (h : n < m) : (n : ℝ) + 1 ≤ m := by
  exact_mod_cast Nat.succ_le_of_lt h

/-- 练习 8.10（★★）：被减数更大时，截断减法与转换。提示：`Nat.cast_sub`。 -/
theorem ex_8_10 (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) + b = a := by
  rw [Nat.cast_sub h]
  ring

/-- 练习 8.11（★★）：复习第 2 章的 `linarith`。提示：先在 `ℝ` 里得到 `(a : ℝ) = 2 * b`，
再 `exact_mod_cast`。 -/
theorem ex_8_11 (a b : ℕ) (h : (a : ℝ) / 2 = b) : a = 2 * b := by
  have h2 : (a : ℝ) = 2 * b := by linarith
  exact_mod_cast h2

/-- 练习 8.12（★）：`^` 的陷阱。指数 `1 / 2 + 1` 是 `ℕ`，值为 `1`。提示：`norm_num`。 -/
theorem ex_8_12 (x : ℝ) : x ^ (1 / 2 + 1) = x := by
  norm_num

/-- 练习 8.13（★）：复习第 2 章的 `simp [h]`。`if` 与可判定性（§11）。提示：`simp [h]`。 -/
theorem ex_8_13 (p : Prop) [Decidable p] (a b : ℕ) (h : ¬ p) : (if p then a else b) = b := by
  simp [h]

/-- 练习 8.14（★★）：`step`（见上）在 `ℝ` 上用了 `if`，所以是 `noncomputable`，`decide` 用不了。
提示：`norm_num [step]`。 -/
theorem ex_8_14 : step 2 = 1 ∧ step (-1) = 0 := by
  constructor <;> norm_num [step]

/-- 练习 8.15（★★★）：整除时 `ℕ` 的除法与转换交换。
提示：`Nat.even_mul_succ_self`、`Nat.cast_div`、`push_cast`。 -/
theorem ex_8_15 (n : ℕ) : ((n * (n + 1) / 2 : ℕ) : ℝ) = n * (n + 1) / 2 := by
  have h : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  have h2 := Nat.cast_div (K := ℝ) h (by norm_num)
  rw [h2]
  push_cast
  ring

end Solutions.Ch08

end
