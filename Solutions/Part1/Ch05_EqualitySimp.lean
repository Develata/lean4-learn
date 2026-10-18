module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-!
# 第 5 章　答案

`Lean4Learn/Part1/Ch05_EqualitySimp.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；
练习 5.4 用到章节里定义的 `double`，这里重新定义一份。
-/

@[expose] public section

namespace Solutions.Ch05

def double (n : ℕ) : ℕ := n + n

/-- 练习 5.1（★）：项模式（第 3 章），用 `Eq.trans` 与 `Eq.symm`（或点记号）。 -/
theorem ex_5_1 (a b c : ℕ) (h₁ : a = b) (h₂ : c = b) : a = c := h₁.trans h₂.symm
-- `h₂.symm : b = c`，再接在 `h₁ : a = b` 后面。

/-- 练习 5.2（★）：先 `rw [h]`，再用第 2 章的 `ring` 收尾。 -/
theorem ex_5_2 (a b : ℤ) (h : a = b + 1) : a ^ 2 = b ^ 2 + 2 * b + 1 := by
  rw [h]
  ring

/-- 练习 5.3（★）：用 `rw [← h] at h₁` 把 `h₁` 里的 `b` 换成 `a + 1`，再用 `omega`。 -/
theorem ex_5_3 (a b : ℕ) (h : a + 1 = b) (h₁ : b * 2 = 8) : a = 3 := by
  rw [← h] at h₁
  omega

/-- 练习 5.4（★★）：先 `unfold double at h`（§2），再用第 2 章的 `omega`。 -/
theorem ex_5_4 (n : ℕ) (h : double n = 0) : n = 0 := by
  unfold double at h
  omega

/-- 练习 5.5（★★）：`rw ... at`，带副条件的引理（§4）。 -/
theorem ex_5_5 (m n k : ℕ) (h : m ≤ n) (h₁ : n - m + m = k) : n = k := by
  rw [Nat.sub_add_cancel h] at h₁
  exact h₁

/-- 练习 5.6（★★）：`calc` 混用 `≤`、`<`、`=`（第 2 章的 `linarith`）。 -/
theorem ex_5_6 (a b : ℝ) (h₁ : a ≤ b) (h₂ : b < 2) : a + b < 4 := by
  calc
    a + b ≤ b + b := by linarith
    _ < 2 + 2 := by linarith
    _ = 4 := by norm_num

/-- 练习 5.7（★★）：`calc` 分三步，各步用不同的策略：`ring`、`rw`、`norm_num`。 -/
theorem ex_5_7 (x y : ℝ) (h₁ : x + y = 5) (h₂ : x * y = 6) : x ^ 2 + y ^ 2 = 13 := by
  calc
    x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by ring
    _ = 5 ^ 2 - 2 * 6 := by rw [h₁, h₂]
    _ = 13 := by norm_num

/-- 练习 5.8（★★）：先用第 4 章的 `obtain` 拆开存在量词，再用 `subst`。 -/
theorem ex_5_8 (f : ℕ → ℕ) (h : ∃ a, a = 2 ∧ f a = 3) : f 2 = 3 := by
  obtain ⟨a, ha, hfa⟩ := h
  subst ha
  exact hfa

/-- 练习 5.9（★★）：在 `fun` 里重写；`rw` 不行，换 `funext` 或 `simp_rw`。 -/
theorem ex_5_9 (f : ℕ → ℕ) (h : ∀ x, f x = x + 0) :
    (fun x ↦ f x + 1) = fun x ↦ x + 1 := by
  funext x
  simp [h]

/-- 练习 5.10（★★）：先把骨架（带 `sorry` 的 `have`）写出来，确认它推得出结论，再逐个填空。 -/
theorem ex_5_10 (f : ℕ → ℕ) (hf : ∀ x, f (x + 1) = f x + 3) (x : ℕ) :
    f (x + 2) = f x + 6 := by
  have h1 : f (x + 1) = f x + 3 := hf x
  have h2 : f (x + 2) = f (x + 1) + 3 := hf (x + 1)
  omega

/-- 练习 5.11（★★★）：`rw [h]` 会遇到 motive 问题（§5），换一个办法。 -/
theorem ex_5_11 (n m : ℕ) (h : n = m) (v : Fin n) (w : Fin m) (hv : v.val = w.val) :
    (h ▸ v : Fin m) = w := by
  subst h
  exact Fin.ext hv

end Solutions.Ch05

end
