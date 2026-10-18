module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 2 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part1/Ch02_Calculation.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch02

/-- 练习 2.1（★）：只用 `rw`，从 `Nat.add_assoc` 与 `Nat.add_comm` 出发。 -/
theorem ex_2_1 (a b c : ℕ) : a + b + c = a + (c + b) := by
  rw [Nat.add_assoc, Nat.add_comm b c]

/-- 练习 2.2（★）：用 `ring`。 -/
theorem ex_2_2 (a b : ℤ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring

/-- 练习 2.3（★）：与练习 1.9 同类的 `ℕ` 问题；两个假设都要用到。 -/
theorem ex_2_3 (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : c - a = (c - b) + (b - a) := by
  omega

/-- 练习 2.4（★）：三个假设都要用到。 -/
theorem ex_2_4 (a b c : ℝ) (h1 : a + b = 10) (h2 : b + c = 7) (h3 : 0 ≤ c) : 3 ≤ a := by
  linarith

/-- 练习 2.5（★）：用 `exact?` 找一个引理（练习 1.8 的办法），再把 `exact?` 换成它报告的证明；
你得到的名字可能与 `Solutions/` 里的不同。 -/
theorem ex_2_5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  exact div_pos ha hb

/-- 练习 2.6（★）：先试 `norm_num`；如果它没证完，再用 `positivity`。 -/
theorem ex_2_6 (n : ℕ) (x : ℝ) : 0 < (n : ℝ) ^ 2 + x ^ 2 + 1 := by
  positivity

/-- 练习 2.7（★★）：第 4 节表里的四条，逐一证明（截断减法、`% 0`、`/ 0`、`0 ^ 0`）；每一条各选合适的策略。 -/
theorem ex_2_7 (n : ℕ) (x : ℝ) :
    n - (n + 1) = 0 ∧ (n + 1) % 0 = n + 1 ∧ x / 0 + 1 = 1 ∧ (0 : ℝ) ^ 0 + 1 = 2 := by
  constructor
  · omega
  constructor
  · simp
  constructor
  · simp
  · norm_num

/-- 练习 2.8（★）：只用 `rw`：先 `pow_succ'`（方向见第 14 节第 1 条），再 `mul_assoc`。 -/
theorem ex_2_8 (a b : ℝ) (n : ℕ) : a ^ (n + 1) * b = a * (a ^ n * b) := by
  rw [pow_succ', mul_assoc]

/-- 练习 2.9（★★）：对 `n` 归纳；零的情形用 `norm_num`。归纳步先用 `pow_succ` 展开 `2 ^ (n + 1)`
（方向见第 14 节第 1 条），再用 `omega` 收尾（它把 `2 ^ n` 当作原子，见第 6 节）；注意目标里是 `n + 1`。 -/
theorem ex_2_9 (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

/-- 练习 2.10（★★）：用 `nlinarith`，提示项取 `sq_nonneg (x - y)`（第 8 节）；`nlinarith` 会自己把
被否定的目标与 `hx`、`hy` 相乘。 -/
theorem ex_2_10 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x * y = 1) : 2 ≤ x + y := by
  nlinarith [sq_nonneg (x - y)]

/-- 练习 2.11（★）：先 `push_cast` 把转换推进运算内部（第 13 节），再用 `ring`（第 5 节）。 -/
theorem ex_2_11 (m n : ℕ) : ((m + n : ℕ) : ℝ) ^ 2 = (m : ℝ) ^ 2 + 2 * m * n + (n : ℝ) ^ 2 := by
  push_cast
  ring

/-- 练习 2.12（★★）：写成三步的 `calc`，关系依次是 `<`、`≤`、`=`（第 11 节）；每一步各选合适的策略。 -/
theorem ex_2_12 (x : ℝ) (hx : 0 < x) : x ^ 2 < (x + 1) ^ 2 := by
  calc
    x ^ 2 < x ^ 2 + 2 * x := by linarith
    _ ≤ x ^ 2 + 2 * x + 1 := by linarith
    _ = (x + 1) ^ 2 := by ring

/-- 练习 2.13（★★）：不点名工具；提示：想想哪几个平方的非负性，按适当的正系数加起来就是目标
（第 7 节有两个变量的版本）。 -/
theorem ex_2_13 (a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

/-- 练习 2.14（★）：练习 1.11 的 `Nat.factorial`，加上本章的截断减法与向下取整除法；用 `decide`。 -/
theorem ex_2_14 :
    Nat.factorial 4 - Nat.factorial 5 = 0 ∧ Nat.factorial 5 / Nat.factorial 4 = 5 := by
  decide

/-- 练习 2.15（★）：用 `constructor` 拆成两个目标（练习 1.6）；第一个用 `norm_num`（练习 1.1），
第二个先 `intro x y z`（练习 1.12），再用 `simp +arith`（第 10 节）。 -/
theorem ex_2_15 :
    (7 : ℝ) / 3 + 5 / 6 < 4 ∧ ∀ x y z : ℕ, x + y + z + 2 = z + y + x + 2 := by
  constructor
  · norm_num
  · intro x y z
    simp +arith

end Solutions.Ch02

end
