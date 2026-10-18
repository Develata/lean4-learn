module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-!
# 第 3 章　答案

`Lean4Learn/Part1/Ch03_TypesTermsProps.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同，
证明全部写成项（需要计算时在项里嵌 `by`）。部分题目附构造思路的注释。
-/

@[expose] public section

namespace Solutions.Ch03

/-- 练习 3.1（★）：函数复合（柯里化的形式）。提示：三个 `fun` 参数。 -/
def ex_3_1 {α β γ : Type*} : (β → γ) → (α → β) → α → γ := fun g f a ↦ g (f a)
-- 三个参数依次接收。

/-- 练习 3.2（★）：蕴含与合取。 -/
theorem ex_3_2 {p q r : Prop} : (p → q) → (p → r) → p → q ∧ r :=
  fun hq hr hp ↦ ⟨hq hp, hr hp⟩

/-- 练习 3.3（★）：回顾第 1 章的 `#check`：用 `@Eq.symm` 并显式写出全部参数来证明。提示：先查签名。 -/
theorem ex_3_3 (a b : ℕ) (h : a = b) : b = a := @Eq.symm ℕ a b h
-- `@Eq.symm : ∀ {α : Sort u_1} {a b : α}, a = b → b = a`，依次给出 `α`、`a`、`b` 和证明。

/-- 练习 3.4（★）：把「取两个参数」的函数改成「取一个数对」的函数。提示：见 §2 的 `p.1`、`p.2`。 -/
def ex_3_4 {α β γ : Type*} : (α → β → γ) → α × β → γ := fun f p ↦ f p.1 p.2
-- 数对 `p` 的两个分量是 `p.1`、`p.2`，分别交给柯里化的 `f`。

/-- 练习 3.5（★）：析取的结合律（另一个方向）。 -/
theorem ex_3_5 {p q r : Prop} : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
  fun h ↦ match h with
    | Or.inl hp => Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => Or.inr hr

/-- 练习 3.6（★★）：析取三段论。提示：对 `Or.elim` 的第一个分支用 `absurd`（§8.4）。 -/
theorem ex_3_6 {p q : Prop} : ¬p → p ∨ q → q :=
  fun hnp h ↦ h.elim (fun hp ↦ absurd hp hnp) (fun hq ↦ hq)
-- 左分支有 `hp : p` 与 `hnp : ¬p`，`absurd` 给出任意结论；右分支的 `hq : q` 就是目标。

/-- 练习 3.7（★★）：合取对析取的分配律。 -/
theorem ex_3_7 {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨fun ⟨hp, h⟩ ↦ h.elim (fun hq ↦ Or.inl ⟨hp, hq⟩) (fun hr ↦ Or.inr ⟨hp, hr⟩),
   fun h ↦ h.elim (fun ⟨hp, hq⟩ ↦ ⟨hp, Or.inl hq⟩) (fun ⟨hp, hr⟩ ↦ ⟨hp, Or.inr hr⟩)⟩

/-- 练习 3.8（★★）：双向蕴含的消去与否定。提示：先用 `have` 得到 `¬p`。 -/
theorem ex_3_8 {p : Prop} : ¬(p ↔ ¬p) :=
  fun h ↦
    have hnp : ¬p := fun hp ↦ h.mp hp hp
    hnp (h.mpr hnp)
-- `h.mp hp : ¬p`，再作用于 `hp` 得 `False`，所以 `hnp : ¬p`；再用 `h.mpr` 得 `p`，矛盾。

/-- 练习 3.9（★★）：存在量词与析取。 -/
theorem ex_3_9 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨fun ⟨w, h⟩ ↦ h.elim (fun hp ↦ Or.inl ⟨w, hp⟩) (fun hq ↦ Or.inr ⟨w, hq⟩),
   fun h ↦ h.elim (fun ⟨w, hp⟩ ↦ ⟨w, Or.inl hp⟩) (fun ⟨w, hq⟩ ↦ ⟨w, Or.inr hq⟩)⟩

/-- 练习 3.10（★）：回顾第 2 章：给出见证，等式用 `norm_num`。 -/
theorem ex_3_10 : ∃ n : ℕ, n * n = 49 ∧ n + 1 = 8 := ⟨7, by norm_num, by norm_num⟩

/-- 练习 3.11（★★）：回顾第 2 章的 `omega`：否定与存在量词。提示：`¬` 是函数，见证用模式拆开（§8.7）。 -/
theorem ex_3_11 : ¬∃ n : ℕ, n + 1 = 0 :=
  fun ⟨n, h⟩ ↦ by omega
-- `¬∃ …` 是 `(∃ …) → False`：用模式拆开见证，`h : n + 1 = 0` 与 `False` 由 `omega` 推出矛盾。

/-- 练习 3.12（★★）：回顾第 2 章的 `ring`：β 规约。提示：用项 `show … by ring`（§10）。 -/
theorem ex_3_12 : ∀ a : ℕ, (fun f : ℕ → ℕ ↦ f (f a)) (· * 3) = 9 * a :=
  fun a ↦ show a * 3 * 3 = 9 * a by ring
-- `show … by ring`：先把目标按 β 规约改写成 `a * 3 * 3 = 9 * a`，再交给 `ring`。

/-- 练习 3.13（★★）：回顾第 2 章的 `omega`：先假设再构造见证。 -/
theorem ex_3_13 : ∀ n : ℕ, n < 5 → ∃ k : ℕ, k + n = 5 :=
  fun n h ↦ ⟨5 - n, by omega⟩
-- `omega` 从上下文里的 `h : n < 5` 得到 `5 - n + n = 5`。

/-- 练习 3.14（★★）：回顾第 2 章的 `omega`，并练习 ∀ 消去。提示：把 `h` 特化到 `0` 与 `1`。 -/
theorem ex_3_14 (f : ℕ → ℕ) (h : ∀ n, f (n + 1) = f n + 2) : f 2 = f 0 + 4 :=
  have h0 : f 1 = f 0 + 2 := h 0
  have h1 : f 2 = f 1 + 2 := h 1
  by omega
-- `h 0`、`h 1` 是 ∀ 消去，分别特化到 `0` 与 `1`；`omega` 把 `f 0`、`f 1`、`f 2` 当作未知数相加。

/-- 练习 3.15（★★★）：经典逻辑，提示：`Classical.byContradiction`（§8.8），要用两次，一层套一层。 -/
theorem ex_3_15 {α : Type*} {p : α → Prop} : ¬(∀ x, p x) → ∃ x, ¬p x :=
  fun h ↦ Classical.byContradiction fun hne ↦
    h fun x ↦ Classical.byContradiction fun hnp ↦ hne ⟨x, hnp⟩
-- 假设不存在这样的 `x`；则对每个 `x`，`¬p x` 会给出存在性，矛盾，故 `p x`；
-- 于是 `∀ x, p x`，与 `h` 矛盾。

end Solutions.Ch03

end
