module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# 第 23 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part4/Ch23_Methodology.lean` 逐字相同，只是证明体已补全。
答案文件不导入章节文件，所以章节里的玩具 blueprint（`Blueprint`、`Blueprint.ok`）与预算 `Budget`
在这里原样重新定义了一遍；练习的答案放在 `Exercises` 区段里，区段之后用 `#print axioms` 核对 23.3、23.4
的公理清单（练习 23.3、23.4 要求的检查）。
-/

@[expose] public section

open Filter Topology

namespace Solutions.Ch23

/-- 玩具版 blueprint：每个节点是（名字，直接依赖的节点名）。 -/
abbrev Blueprint : Type := List (String × List String)

/-- `Blueprint.ok bp seen`：按顺序检查，每个节点的名字是新的、依赖都已出现过（`seen` 是已出现的名字）。 -/
def Blueprint.ok : Blueprint → List String → Bool
  | [], _ => true
  | (n, us) :: rest, seen =>
    decide (n ∉ seen) && us.all (fun u ↦ decide (u ∈ seen)) && Blueprint.ok rest (n :: seen)

/-- 预算：总额与已花费。 -/
structure Budget where
  total : ℕ
  spent : ℕ

namespace Budget

/-- 剩余额度。`ℕ` 的减法是截断的，`spent > total` 时取垃圾值 `0`。 -/
def left (b : Budget) : ℕ := b.total - b.spent

theorem left_def (b : Budget) : b.left = b.total - b.spent := rfl

/-- 垃圾值引理：超支时 `left = 0`。它是真的，但在数学上没有意义，所以单独命名而不是藏在别的引理里。 -/
theorem left_eq_zero_of_total_le (b : Budget) (h : b.total ≤ b.spent) : b.left = 0 := by
  rw [left_def]
  omega

end Budget

section Exercises

/-- 练习 23.1（★）：补一个节点。`c` 依赖 `a` 和 `b`，请给出中间那个节点 `b`（名字只能是 `"b"`，
它的依赖自己选），使整个列表合格。提示：`decide`。 -/
theorem ex_23_1 : ∃ b : String × List String,
    Blueprint.ok [("a", []), b, ("c", ["a", "b"])] [] = true := by
  exact ⟨("b", ["a"]), by decide⟩

/-- 练习 23.2（★★）：为第 22 章的上界 `cramer_upper` 写一个 blueprint：至少 5 个节点，最后一个是 `cramer_upper`，
所有依赖都在前面，依赖边（各节点依赖个数之和）至少 4 条。给出一个列表并用 `decide` 验证。
（节点可以取 Chernoff 方法、`iIndepFun.mgf_sum`、`iSup` 的上界等，第 22 章 §3–§5；Lean 不检查节点名
是否对应第 22 章，请自己对照。）
提示：先写节点名，再从 `cramer_upper` 往回写它的依赖。 -/
theorem ex_23_2 : ∃ bp : Blueprint, Blueprint.ok bp [] = true ∧
    (bp.map Prod.fst).getLast? = some "cramer_upper" ∧ 5 ≤ bp.length ∧
    4 ≤ (bp.map fun nd ↦ nd.2.length).sum := by
  refine ⟨[("chernoff", []), ("mgf_sum", []), ("cgf_bound", ["mgf_sum"]),
    ("iSup_bound", ["chernoff", "cgf_bound"]), ("cramer_upper", ["iSup_bound", "cgf_bound"])],
    ?_, ?_, ?_, ?_⟩ <;> decide

/-- 练习 23.3（★）：经典逻辑要付出公理。证明 `¬¬p → p`，然后在你的草稿里运行 `#print axioms ex_23_3`，
确认清单里有 `Classical.choice`。提示：`by_contra` 或 `Classical.byContradiction`（第 4 章）。 -/
theorem ex_23_3 (p : Prop) (h : ¬¬p) : p := by
  by_contra hp
  exact h hp

/-- 练习 23.4（★）：同一个结论，命题可判定时不需要任何公理。证明后用 `#print axioms ex_23_4` 确认输出是
「does not depend on any axioms」，并与 23.3 对比。提示：`Decidable.of_not_not`。 -/
theorem ex_23_4 (p : Prop) [Decidable p] (h : ¬¬p) : p := Decidable.of_not_not h

/-- 练习 23.5（★★）：只用作者导出的 API 证明 `pentagonal (-1) = 2` 与 `pentagonal (-2) = 7`
（第 1 章 §8：`rfl` 与 `simp [pentagonal]` 都不行；`ℤ` 的除法与负数交给 `omega`）。
提示：`natCast_pentagonal (-1)` 给出 `(↑(pentagonal (-1)) : ℤ) = -1 * (3 * -1 - 1) / 2`。 -/
theorem ex_23_5 : pentagonal (-1) = 2 ∧ pentagonal (-2) = 7 := by
  have h1 := natCast_pentagonal (-1)
  have h2 := natCast_pentagonal (-2)
  refine ⟨?_, ?_⟩ <;> omega

/-- 练习 23.6（★★）：把 §2 的 `proof_wanted` 做成定理。提示：在本地 Mathlib 的
`Combinatorics/Enumerative/Pentagonal/Basic.lean` 里找 `pentagonal` 的单调性引理（第 9 章 §8 的方法），
再用 `omega` 补上区间成员条件。 -/
theorem ex_23_6 (k : ℤ) (hk : 0 ≤ k) : pentagonal k ≤ pentagonal (k + 1) :=
  pentagonal_strictMonoOn.monotoneOn (Set.mem_Ici.2 hk) (Set.mem_Ici.2 (by omega)) (by omega)

/-- 练习 23.7（★）：陈述漂移与垃圾值（§3、§8，第 2 章的截断减法）：`ℕ` 上 `a - b + b = a` 不总成立，
加上 `b ≤ a` 就成立。两个都要证。提示：反例取 `a = 0`、`b = 1`；`Nat.sub_add_cancel` 或 `omega`。 -/
theorem ex_23_7 : (¬ ∀ a b : ℕ, a - b + b = a) ∧ ∀ a b : ℕ, b ≤ a → a - b + b = a := by
  refine ⟨fun h ↦ ?_, fun a b h ↦ Nat.sub_add_cancel h⟩
  simpa using h 0 1

/-- 练习 23.8（★）：垃圾值引理的用法（§3）：超支时 `left = 0`，所以 `left + spent` 等于 `spent`；
严格超支时它不等于 `total`。提示：`Budget.left_eq_zero_of_total_le`，或 `Budget.left_def` 加 `omega`。 -/
theorem ex_23_8 (b : Budget) (h : b.total ≤ b.spent) : b.left + b.spent = b.spent := by
  rw [Budget.left_eq_zero_of_total_le b h]
  omega

/-- 练习 23.9（★）：把假设放最弱（§3，第 8 章）：对任意交换半环成立的二项平方公式，而不是 `ℕ` 或 `ℝ` 专用。
提示：`ring`。证完再把它用在 `ℕ` 与 `ℝ` 上。 -/
theorem ex_23_9 {R : Type*} [CommSemiring R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- 练习 23.10（★）：风格修正（第 7、9 章）。旧的证明是 `by rw [Set.mem_setOf_eq]`，用了已弃用的名字，
`lake build --wfail` 会失败；改用新名字 `Set.mem_ofPred_eq`。 -/
theorem ex_23_10 (p q : ℕ → Prop) (a : ℕ) : (a ∈ {x | p x ∧ q x}) = (p a ∧ q a) :=
  Set.mem_ofPred_eq

/-- 练习 23.11（★）：风格修正（第 4 章）。旧的证明是 `push_neg at h` 加 `exact h`（`push_neg` 已弃用）；
改用 `push Not at h`。 -/
theorem ex_23_11 (p : ℕ → Prop) (h : ¬ ∀ n, p n) : ∃ n, ¬ p n := by
  push Not at h
  exact h

/-- 练习 23.12（★★）：把 §2 的 `sorry` 骨架做成证明（第 14 章、第 20 章）：这次 `P n` 被两项之和控制，
`P n ≤ A n + B n`，`A`、`B` 都趋于 `0`。
分步骨架：(a) `hsum : Tendsto (fun n ↦ A n + B n) atTop (𝓝 0)`，用 `hA.add hB` 并把 `0 + 0` 化成 `0`；
(b) `squeeze_zero h0 hP hsum`。 -/
theorem ex_23_12 (P A B : ℕ → ℝ) (h0 : ∀ n, 0 ≤ P n) (hP : ∀ n, P n ≤ A n + B n)
    (hA : Tendsto A atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 0)) : Tendsto P atTop (𝓝 0) := by
  have hsum : Tendsto (fun n ↦ A n + B n) atTop (𝓝 0) := by
    simpa using hA.add hB
  exact squeeze_zero h0 hP hsum

end Exercises

/-!
公理清单（练习 23.3、23.4 要求的检查）：经典逻辑那条依赖三条标准公理，构造性的那条不依赖任何公理。
-/

/-- info: 'Solutions.Ch23.ex_23_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ex_23_3

/-- info: 'Solutions.Ch23.ex_23_4' does not depend on any axioms -/
#guard_msgs in
#print axioms ex_23_4

end Solutions.Ch23

end
