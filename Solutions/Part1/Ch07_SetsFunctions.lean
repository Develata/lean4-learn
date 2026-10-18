module

public import Mathlib.Basic.Nonempty
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar

/-!
# 第 7 章　答案

`Lean4Learn/Part1/Ch07_SetsFunctions.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；
本章的练习都是自成一体的，不依赖章节里定义的辅助对象。
-/

@[expose] public section

namespace Solutions.Ch07

/-- 练习 7.1（★）：复习第 3 章的项模式。交集包含于并集。提示：`fun x hx ↦ Or.inl hx.1`。 -/
theorem ex_7_1 {α : Type*} (s t : Set α) : s ∩ t ⊆ s ∪ t := fun _ hx ↦ Or.inl hx.1

/-- 练习 7.2（★）：差集 `s \ t` 与被减去的集合 `t` 的交为空。
提示：`Set.eq_empty_iff_forall_notMem`，再 `rintro`。 -/
theorem ex_7_2 {α : Type*} (s t : Set α) : (s \ t) ∩ t = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨⟨_, hxt⟩, hxt'⟩
  exact hxt hxt'

/-- 练习 7.3（★）：复习第 4 章的 `tauto`。De Morgan 律。提示：`ext x`，`simp only` 化成命题，`tauto`。 -/
theorem ex_7_3 {α : Type*} (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_union]
  tauto

/-- 练习 7.4（★★）：并集的泛性质。提示：`constructor`；`→` 用 `fun x hx ↦ h (Or.inl hx)`，`←` 用 `rintro`。 -/
theorem ex_7_4 {α : Type*} (s t u : Set α) : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u := by
  constructor
  · intro h
    exact ⟨fun x hx ↦ h (Or.inl hx), fun x hx ↦ h (Or.inr hx)⟩
  · rintro ⟨hs, ht⟩ x (hx | hx)
    · exact hs hx
    · exact ht hx

/-- 练习 7.5（★★）：像对交集的包含。不要直接用 `Set.image_inter_subset`。
提示：`rintro _ ⟨x, ⟨hs, ht⟩, rfl⟩`。 -/
theorem ex_7_5 {α β : Type*} (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro _ ⟨x, ⟨hs, ht⟩, rfl⟩
  exact ⟨⟨x, hs, rfl⟩, ⟨x, ht, rfl⟩⟩

/-- 练习 7.6（★★）：单射时，`s` 的像的原像还在 `s` 里（`f ⁻¹' (f '' s) ⊆ s`）。
提示：`rintro x ⟨y, hy, hxy⟩`，再用 `hf hxy` 得到 `y = x`，然后 `obtain rfl`（或 `subst`）。 -/
theorem ex_7_6 {α β : Type*} (f : α → β) (hf : Function.Injective f) (s : Set α) :
    f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, hy, hxy⟩
  obtain rfl := hf hxy
  exact hy

/-- 练习 7.7（★★）：单射时像对交集的包含反向也成立（§4 的反例说明一般情形不成立）。
提示：`rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩`，再用 `hf hxy` 得到 `y = x`。 -/
theorem ex_7_7 {α β : Type*} (f : α → β) (hf : Function.Injective f) (s t : Set α) :
    f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  obtain rfl := hf hxy
  exact ⟨_, ⟨hx, hy⟩, rfl⟩

/-- 练习 7.8（★）：复习第 2 章的 `omega`。`x ↦ 3x + 1` 在 `ℤ` 上是单射。
提示：`intro a b h`，`dsimp only at h`，`omega`。 -/
theorem ex_7_8 : Function.Injective (fun x : ℤ ↦ 3 * x + 1) := by
  intro a b h
  dsimp only at h
  omega

/-- 练习 7.9（★）：复习第 2、4 章。`n ↦ 2n` 不是 `ℕ → ℕ` 的满射。
提示：取 `1` 的原像，`dsimp only at ha`，`omega`。 -/
theorem ex_7_9 : ¬ Function.Surjective (fun n : ℕ ↦ 2 * n) := by
  intro h
  obtain ⟨a, ha⟩ := h 1
  dsimp only at ha
  omega

/-- 练习 7.10（★★）：§5 的指标并。`⋃ i, s i ⊆ t` 当且仅当每个 `s i ⊆ t`。
不要直接用 `Set.iUnion_subset`。提示：`constructor`；两个方向各用 `Set.mem_iUnion.mpr`、`.mp`。 -/
theorem ex_7_10 {α ι : Type*} (s : ι → Set α) (t : Set α) :
    ⋃ i, s i ⊆ t ↔ ∀ i, s i ⊆ t := by
  constructor
  · intro h i x hx
    exact h (Set.mem_iUnion.mpr ⟨i, hx⟩)
  · intro h x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact h i hi

/-- 练习 7.11（★★）：复习第 5 章的 `calc`。有左逆则单射。不要直接用
`Function.LeftInverse.injective`。提示：`h a : g (f a) = a`，`calc a = g (f a) = g (f b) = b`。 -/
theorem ex_7_11 {α β : Type*} (f : α → β) (g : β → α) (h : Function.LeftInverse g f) :
    Function.Injective f := by
  intro a b hab
  calc a = g (f a) := (h a).symm
    _ = g (f b) := by rw [hab]
    _ = b := h b

/-- 练习 7.12（★）：`choose`。逐点的存在性给出一个函数。提示：`choose f hf using h`。 -/
theorem ex_7_12 {α β : Type*} (r : α → β → Prop) (h : ∀ a, ∃ b, r a b) :
    ∃ f : α → β, ∀ a, r a (f a) := by
  choose f hf using h
  exact ⟨f, hf⟩

/-- 练习 7.13（★★）：集合上的 `Nonempty`（§7、§9）。不要直接用 `Set.nonempty_coe_sort`。
提示：`constructor`；`rintro ⟨x, hx⟩` 拆开 `∃`，`⟨⟨x, hx⟩⟩` 造出 `Nonempty ↥s`。 -/
theorem ex_7_13 {α : Type*} (s : Set α) : s.Nonempty ↔ Nonempty ↥s := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  · rintro ⟨⟨x, hx⟩⟩
    exact ⟨x, hx⟩

/-- 练习 7.14（★★）：造一个 `ℤ ≃ ℤ`，它是 `n ↦ 5 - n`。
提示：`⟨⟨fun n ↦ 5 - n, fun n ↦ 5 - n, ?_, ?_⟩, fun n ↦ rfl⟩`，两条逆律各 `intro n`，`change`，`omega`。 -/
theorem ex_7_14 : ∃ e : ℤ ≃ ℤ, ∀ n, e n = 5 - n := by
  refine ⟨⟨fun n ↦ 5 - n, fun n ↦ 5 - n, ?_, ?_⟩, fun n ↦ rfl⟩
  · intro n
    change 5 - (5 - n) = n
    omega
  · intro n
    change 5 - (5 - n) = n
    omega

/-- 练习 7.15（★★★）：复习第 4 章的 `by_cases`。Cantor：没有从 `ℕ` 到它的幂集的满射。
提示：对满射 `f` 取集合 `{k | k ∉ f k}`，设 `n` 是它的原像，问 `n ∈ f n` 是否成立。 -/
theorem ex_7_15 (f : ℕ → Set ℕ) : ¬ Function.Surjective f := by
  intro h
  obtain ⟨n, hn⟩ := h {k | k ∉ f k}
  have h1 : n ∈ f n ↔ n ∉ f n := Set.ext_iff.mp hn n
  by_cases h2 : n ∈ f n
  · exact h1.mp h2 h2
  · exact h2 (h1.mpr h2)

end Solutions.Ch07

end
