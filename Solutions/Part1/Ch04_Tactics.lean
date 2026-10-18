module

public import Batteries.Tactic.Init
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.TypeStar
public import Mathlib.Tactic.Use

/-!
# 第 4 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part1/Ch04_Tactics.lean` 逐字相同，只是证明体已补全；
部分题目附构造思路的注释。
-/

@[expose] public section

namespace Solutions.Ch04

/-- 练习 4.1（★）：第 3 章练习 3.2 的策略版本：蕴含与合取；用 `intro` 与 `constructor`。 -/
theorem ex_4_1 {p q r : Prop} : (p → q) → (p → r) → p → q ∧ r := by
  intro hq hr hp
  constructor
  · exact hq hp
  · exact hr hp
-- `intro` 依次引入三个前件；`constructor` 拆开 `∧`，两个目标各用一个前件。

/-- 练习 4.2（★）：第 3 章练习 3.5 的策略版本：析取的结合律；用 `rintro` 与 `left`/`right`。 -/
theorem ex_4_2 {p q r : Prop} : p ∨ (q ∨ r) → (p ∨ q) ∨ r := by
  rintro (hp | hq | hr)
  · left
    left
    exact hp
  · left
    right
    exact hq
  · right
    exact hr
-- 模式 `(hp | hq | hr)` 把 `p ∨ (q ∨ r)` 一次拆成三种情形。

/-- 练习 4.3（★★）：第 3 章练习 3.7 的策略版本：合取对析取的分配律；用 `constructor` 与 `rintro`。 -/
theorem ex_4_3 {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  · rintro ⟨hp, hq | hr⟩
    · left
      exact ⟨hp, hq⟩
    · right
      exact ⟨hp, hr⟩
  · rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    · exact ⟨hp, Or.inl hq⟩
    · exact ⟨hp, Or.inr hr⟩

/-- 练习 4.4（★★）：第 3 章练习 3.8 的策略版本：`p` 与 `¬p` 不等价；用 `intro` 与 `have`。 -/
theorem ex_4_4 {p : Prop} : ¬(p ↔ ¬p) := by
  intro h
  have hnp : ¬p := fun hp ↦ h.mp hp hp
  exact hnp (h.mpr hnp)
-- `h.mp hp : ¬p`，再作用到 `hp` 得 `False`；于是 `¬p`，再由 `h.mpr` 得到 `p`，矛盾。

/-- 练习 4.5（★★）：第 3 章练习 3.9 的策略版本：存在量词与析取；用 `rintro ⟨x, hx | hx⟩` 与 `use`。 -/
theorem ex_4_5 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · rintro ⟨x, hx | hx⟩
    · left
      use x
    · right
      use x
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · use x
      left
      exact hx
    · use x
      right
      exact hx
-- 在先 `left`/`right` 的两个分支里，`use x` 之后剩下的 `p x` 被它的 discharger 用 `assumption` 关闭。

/-- 练习 4.6（★）：矛盾推出一切；先 `rintro ⟨hp, hnp⟩`，再试 `contradiction`，`exfalso` 也行。 -/
theorem ex_4_6 {p q : Prop} : p ∧ ¬p → q := by
  rintro ⟨hp, hnp⟩
  contradiction
-- 也可以 `exfalso` 之后 `exact hnp hp`。

/-- 练习 4.7（★）：第 3 章练习 3.10 的策略版本：用 `use`。 -/
theorem ex_4_7 : ∃ n : ℕ, n * n = 49 ∧ n + 1 = 8 := by
  use 7

/-- 练习 4.8（★★）：第 3 章练习 3.13 的策略版本：`intro`、`use`，再用 `omega` 收尾。 -/
theorem ex_4_8 : ∀ n : ℕ, n < 5 → ∃ k : ℕ, k + n = 5 := by
  intro n hn
  use 5 - n
  omega

/-- 练习 4.9（★★）：`∃!` 的引入：先给见证，再证唯一性；用 `refine` 与 `omega`。 -/
theorem ex_4_9 : ∃! n : ℕ, 2 * n + 1 = 7 := by
  refine ⟨3, rfl, ?_⟩
  intro y hy
  omega
-- 见证 `3`；`refine` 之后的目标是 `∀ y, (fun n ↦ 2 * n + 1 = 7) y → y = 3`，`omega` 照样能用。

/-- 练习 4.10（★★）：存在量词的否定。不用 `push Not`，手工用 `intro`/`rintro`。 -/
theorem ex_4_10 {α : Type*} {p : α → Prop} : (¬∃ x, p x) ↔ ∀ x, ¬p x := by
  constructor
  · intro h x hx
    exact h ⟨x, hx⟩
  · rintro h ⟨x, hx⟩
    exact h x hx

/-- 练习 4.11（★★）：第 3 章练习 3.15 的策略版本：只用 `by_contra`（要用两次）、`intro`、`apply`、
`exact` 手工证明（§7 给出了 `push Not` 与 `by_contra!` 的写法，可以对照）。 -/
theorem ex_4_11 {α : Type*} {p : α → Prop} : ¬(∀ x, p x) → ∃ x, ¬p x := by
  intro h
  by_contra hne
  apply h
  intro x
  by_contra hx
  exact hne ⟨x, hx⟩

/-- 练习 4.12（★★）：用 `contrapose!` 证明；之后目标是一个蕴含，再用 `intro`。 -/
theorem ex_4_12 {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, ¬q x) → ∃ x, ¬p x := by
  contrapose!
  intro hp x
  exact h x (hp x)
-- `contrapose!` 之后目标是 `(∀ x, p x) → ∀ x, q x`。

/-- 练习 4.13（★★）：`∃!` 的消去：满足性质的两个元素相等；用 `obtain` 拆开 `∃!`。 -/
theorem ex_4_13 {α : Type*} {p : α → Prop} (h : ∃! x, p x) (a b : α) (ha : p a) (hb : p b) :
    a = b := by
  obtain ⟨x, -, hu⟩ := h
  exact (hu a ha).trans (hu b hb).symm
-- `hu a ha : a = x`，`hu b hb : b = x`。

/-- 练习 4.14（★）：组合子：`rintro` 拆开假设之后，用 `constructor <;> constructor <;> assumption`。 -/
theorem ex_4_14 {p q r : Prop} : p ∧ q ∧ r → (r ∧ q) ∧ (q ∧ p) := by
  rintro ⟨hp, hq, hr⟩
  constructor <;> constructor <;> assumption
-- 第一个 `constructor` 拆外层 `∧`，第二个拆两个内层 `∧`，四个目标各用 `assumption` 关掉。

/-- 练习 4.15（★★★）：「酒鬼悖论」：在非空的论域里，总有一个人，如果他在喝酒，那么所有人都在喝酒。
提示：对 `∀ y, D y` 做 `by_cases`。 -/
theorem ex_4_15 {α : Type*} (a : α) (D : α → Prop) : ∃ x, D x → ∀ y, D y := by
  by_cases h : ∀ y, D y
  · exact ⟨a, fun _ ↦ h⟩
  · push Not at h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, fun hDx ↦ absurd hDx hx⟩

end Solutions.Ch04

end
