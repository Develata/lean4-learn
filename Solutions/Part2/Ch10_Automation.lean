module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar

/-!
# 第 10 章　答案

`Lean4Learn/Part2/Ch10_Automation.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；注释说明为什么选这个策略。
-/

@[expose] public section

namespace Solutions.Ch10

/-- 练习 10.1（★）：`ℕ` 上的取余与不等式（第 2 章）。 -/
theorem ex_10_1 (n : ℕ) (h : n % 4 = 3) : n % 2 = 1 ∧ 3 ≤ n := by
  omega
-- `n % 4 = 3` 给出 `n % 2 = 1` 与 `3 ≤ n`，都是线性整数算术。

/-- 练习 10.2（★）：`ℝ` 上的二次不等式（第 2 章）；差是一个平方，想想该给自动化什么提示。 -/
theorem ex_10_2 (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]
-- 差是 `(a - b) ^ 2 ≥ 0`；提示项把它交给线性部分。

/-- 练习 10.3（★）：交换环里的恒等式（第 2 章）。 -/
theorem ex_10_3 (a b : ℤ) : (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by
  ring

/-- 练习 10.4（★）：含除法，要用到 `a ≠ 0`。 -/
theorem ex_10_4 (a : ℝ) (ha : a ≠ 0) : (a ^ 2 - 1) / a = a - 1 / a := by
  field
-- `field_simp` 清分母（用 `ha`），`ring1` 收尾；`field` 是两者的缩写。

/-- 练习 10.5（★★）：`x ^ 2 + y ^ 2` 可用 `x + y` 与 `x * y` 表出；不要直接调 `grobner`，在纸上算出
`linear_combination` 的系数。 -/
theorem ex_10_5 (x y : ℝ) (h₁ : x * y = 2) (h₂ : x + y = 5) : x ^ 2 + y ^ 2 = 21 := by
  linear_combination (x + y + 5) * h₂ - 2 * h₁
-- `(x + y + 5) * (x + y - 5) - 2 * (x * y - 2) = x ^ 2 + y ^ 2 - 21`。

/-- 练习 10.6（★）：一个素数、一个合数、一个最大公约数。 -/
theorem ex_10_6 : Nat.Prime 211 ∧ ¬ Nat.Prime 221 ∧ Nat.gcd 84 90 = 6 := by
  norm_num
-- `Nat.Prime`、`Nat.gcd` 的扩展分别来自 `NormNum.Prime` 与 `NormNum.GCD`。

/-- 练习 10.7（★★）：不等式两边结构相同；`x ^ 2` 的非负性是个副条件。 -/
theorem ex_10_7 (a b c d x : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by
  gcongr
-- `gcongr` 自己推出模板 `x ^ 2 * ?_ + ?_`；副条件 `0 ≤ x ^ 2` 由 `positivity` 证，
-- 两个主目标由假设关闭。

/-- 练习 10.8（★）：每个因子的符号都能从语法看出（`Real.exp` 有扩展）。 -/
theorem ex_10_8 (x y : ℝ) : 0 < Real.exp x * (y ^ 2 + 1) := by
  positivity

/-- 练习 10.9（★）：命题逻辑（第 4 章）。 -/
theorem ex_10_9 (p q r : Prop) : (p → q ∨ r) → ¬q → p → r := by
  tauto

/-- 练习 10.10（★★）：第 5 章的 `simp`；`Nat.sub_add_cancel` 是带副条件 `m ≤ n` 的 simp 引理，
用 `(disch := assumption)` 处理副条件。 -/
theorem ex_10_10 (n m : ℕ) (h : m ≤ n) : n - m + m + 0 = n := by
  simp (disch := assumption)
-- `add_zero` 先去掉 `+ 0`，再用 simp 引理 `Nat.sub_add_cancel`，其副条件 `m ≤ n` 由 `assumption` 证。

/-- 练习 10.11（★★）：递推式的两个实例；`omega`、`lia` 不会自己实例化上下文里的 `∀` 假设
（`grind` 会，§4）。 -/
theorem ex_10_11 (f : ℕ → ℤ) (h : ∀ n, f (n + 1) = f n + 2) (h0 : f 0 = 1) : f 2 = 5 := by
  lia [h 0, h 1]
-- 给 `lia` 递推式的两个实例。`grind` 也行，下面的 `example` 验证了这点。

example (f : ℕ → ℤ) (h : ∀ n, f (n + 1) = f n + 2) (h0 : f 0 = 1) : f 2 = 5 := by grind

/-- 练习 10.12（★★）：集合恒等式（第 7 章系统地讲集合）；`aesop` 在这里没有进展，换个办法。 -/
theorem ex_10_12 (s t u : Set ℕ) : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := by
  ext x
  simp
  tauto
-- `aesop` 在这里没有进展；外延性加 `simp` 把两边化成命题逻辑，`tauto` 收尾。

/-- 练习 10.13（★）：任意全序里的矛盾。 -/
theorem ex_10_13 {α : Type*} [LinearOrder α] (a b c : α) (h : min a b ≤ c) (h₁ : c < a)
    (h₂ : c < b) : False := by
  order
-- `min a b ≤ c < a`、`c < b` 矛盾，`order` 认识 `min`。

/-- 练习 10.14（★★）：三个假设互相代入（第 5 章）。 -/
theorem ex_10_14 (a b c : ℕ) (h₁ : a + 0 = b) (h₂ : b * 1 = c) (h₃ : c = 4) : a = 4 := by
  simp_all
-- `h₁` 得 `a = b`，`h₂` 得 `b = c`，`h₃` 给出 `c = 4`；`simp_all` 让它们互相代入。

/-- 练习 10.15（★★）：诊断。直接调 `positivity` 证不了这个目标：说出原因，再换一个能证的办法。 -/
theorem ex_10_15 (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  fail_if_success positivity
  nlinarith [sq_nonneg (a - b)]
-- `positivity` 对减法没有办法：`- 2 * a * b` 的符号不确定，上面的 `fail_if_success` 验证了这点。
-- 补救：配方成 `(a - b) ^ 2 ≥ 0`，交给 `nlinarith`。

end Solutions.Ch10

end
