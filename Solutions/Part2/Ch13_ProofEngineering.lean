module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring

/-!
# 第 13 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part2/Ch13_ProofEngineering.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch13

/-- 尾递归累加：`sumAux acc n = acc + (0 + 1 + … + n)`。 -/
def sumAux : ℕ → ℕ → ℕ
  | acc, 0 => acc
  | acc, n + 1 => sumAux (acc + n + 1) n

/-- 练习 13.1（★）：用 `suffices` 把目标化成只剩 `r`（第 4 章）。 -/
theorem ex_13_1 (p q r s : Prop) (h1 : p → q) (h2 : q → r) (h3 : r → s) : p → s := by
  intro hp
  suffices hr : r by exact h3 hr
  exact h2 (h1 hp)

/-- 练习 13.2（★）：`obtain ⟨k, hk⟩ := h` 拆开存在量词，然后 `omega`（第 2 章）。 -/
theorem ex_13_2 (n : ℕ) (h : ∃ k, n = 2 * k + 1) : n % 2 = 1 := by
  obtain ⟨k, hk⟩ := h
  omega

/-- 练习 13.3（★）：`set s := x + y with hs` 把长表达式换成 `s`，
然后 `mul_self_eq_zero`（`a * a = 0 ↔ a = 0`）。 -/
theorem ex_13_3 (x y : ℤ) (h : (x + y) * (x + y) = 0) : x + y = 0 := by
  set s := x + y with hs
  exact mul_self_eq_zero.mp h

/-- 练习 13.4（★★）：`induction n generalizing acc`；`succ` 情形先 `simp only [sumAux]`，
再对两个累加值分别用 `ih`（本章 §3.1）。 -/
theorem ex_13_4 (acc n : ℕ) : sumAux acc n = acc + sumAux 0 n := by
  induction n generalizing acc with
  | zero => simp [sumAux]
  | succ n ih =>
    simp only [sumAux]
    rw [ih (acc + n + 1), ih (0 + n + 1)]
    omega

/-- 练习 13.5（★★）：强归纳（§3.2）。写 `induction n using Nat.strong_induction_on with | _ n ih`；
`n = 2`、`n = 3` 直接给出见证，`n ≥ 4` 对 `n - 2` 用 `ih`。 -/
theorem ex_13_5 (n : ℕ) (hn : 2 ≤ n) : ∃ a b : ℕ, n = 2 * a + 3 * b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : 4 ≤ n
    · obtain ⟨a, b, hab⟩ := ih (n - 2) (by omega) (by omega)
      exact ⟨a + 1, b, by omega⟩
    · have h23 : n = 2 ∨ n = 3 := by omega
      rcases h23 with rfl | rfl
      · exact ⟨1, 0, by norm_num⟩
      · exact ⟨0, 1, by norm_num⟩

/-- 练习 13.6（★★）：`Nat.le_induction`（§3.3）：`induction n, hn using Nat.le_induction`，
`succ` 情形用 `pow_succ`，再 `omega`。 -/
theorem ex_13_6 (n : ℕ) (hn : 1 ≤ n) : n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    omega

/-- 练习 13.7（★）：`interval_cases`（§4.1）：用 `h1`、`h2` 对 `n` 穷举，再 `omega` 或
`simp_all` 收尾。 -/
theorem ex_13_7 (n : ℕ) (h1 : 3 ≤ n) (h2 : n ≤ 6) (h : n * n + n = 30) : n = 5 := by
  interval_cases n <;> simp_all

/-- 练习 13.8（★）：`fin_cases`（§4.1）的替代：`Fin.ext : a.val = b.val → a = b` 把 `h0`、`h1` 变成
`x.val ≠ 0`、`x.val ≠ 1`，再交给 `omega`。 -/
theorem ex_13_8 (x : Fin 4) (h0 : x ≠ 0) (h1 : x ≠ 1) : 2 ≤ x.val := by
  have h0' : x.val ≠ 0 := fun h' ↦ h0 (Fin.ext h')
  have h1' : x.val ≠ 1 := fun h' ↦ h1 (Fin.ext h')
  omega

/-- 练习 13.9（★）：`convert h using 2`（§4.2）把目标化成一个等式，再用 `hm` 关掉。 -/
theorem ex_13_9 (P : ℕ → Prop) (n m : ℕ) (hm : m = 0) (h : P (n + m)) : P n := by
  convert h using 2
  omega

/-- 练习 13.10（★★）：`wlog h : a ≤ b with H`（§2）。主情形用 `max_eq_right`、`min_eq_left` 与 `ring`；
另一个情形取 `H b a`，用 `max_comm`、`min_comm` 重写后 `ring`。 -/
theorem ex_13_10 (a b : ℤ) : (a - b) ^ 2 = (max a b - min a b) ^ 2 := by
  wlog h : a ≤ b with H
  · have := H b a (by omega)
    rw [max_comm, min_comm, ← this]
    ring
  · rw [max_eq_right h, min_eq_left h]
    ring

/-- 练习 13.11（★★）：调试 motive 错误（§6 ①，第 5 章）并处理类型转换（第 8 章）。
`v : Fin n` 的类型依赖 `n`，对 `n` 的 `rw [h]` 会遇到 §6 ① 的错误；先 `subst h`，再 `exact_mod_cast`。 -/
theorem ex_13_11 (n m : ℕ) (h : n = m) (v : Fin n) : (v.val : ℤ) < m := by
  subst h
  exact_mod_cast v.isLt

/-- 练习 13.12（★）：用三个 `have` 各给出一个平方非负的事实（`sq_nonneg (a - b)` 等），
再让 `linarith` 收尾（第 10 章）。 -/
theorem ex_13_12 (a b c : ℤ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h1 : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have h2 : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
  have h3 : 0 ≤ (c - a) ^ 2 := sq_nonneg (c - a)
  linarith

/-- 练习 13.13（★★★）：自顶向下写一个陌生的证明（§1）。立方数模 9 只能是 0、1、8。
提示：`Nat.pow_mod`、`generalize`、`interval_cases`。先写 `sorry` 骨架，再逐个填。 -/
theorem ex_13_13 (n : ℕ) : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by
  have hlt : n % 9 < 9 := Nat.mod_lt _ (by norm_num)
  rw [Nat.pow_mod]
  generalize n % 9 = r at hlt ⊢
  interval_cases r <;> decide

/-- 练习 13.14（★★）：`conv_lhs` 里用 `ext x` 进入 `fun`，再 `rw [h x]`（§7；直接 `rw [h]` 会失败）。 -/
theorem ex_13_14 (f g : ℕ → ℕ) (h : ∀ x, f x = g x + 1) :
    (fun x ↦ f x * f x) = fun x ↦ (g x + 1) * (g x + 1) := by
  conv_lhs =>
    ext x
    rw [h x]

/-- 练习 13.15（★）：类型转换（第 8 章）：先用 `exact_mod_cast` 得到 `ℤ` 里的等式，再收尾。 -/
theorem ex_13_15 (a b : ℕ) (h : a + b = 3) : ((a : ℤ) + b) * 2 = 6 := by
  have h' : (a : ℤ) + b = 3 := by exact_mod_cast h
  linarith

end Solutions.Ch13

end
