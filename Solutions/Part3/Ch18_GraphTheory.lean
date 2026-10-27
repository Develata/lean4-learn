module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic.NormNum.Basic

/-!
# 第 18 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part3/Ch18_GraphTheory.lean` 逐字相同，只是证明体已补全。
-/

@[expose] public section

namespace Solutions.Ch18

open scoped Finset

/-- 练习 18.1（★）：相邻蕴含两端点不同且反向也相邻。用 `Adj.ne` 与 `Adj.symm`（§1）。 -/
theorem ex_18_1 {V : Type*} (G : SimpleGraph V) (u v : V) (h : G.Adj u v) :
    u ≠ v ∧ G.Adj v u := by
  exact ⟨h.ne, h.symm⟩

/-- 练习 18.2（★）：补图的相邻关系（§2）。若 `u ≠ v` 且 `G` 里 `u v` 不相邻，则它们在 `Gᶜ` 里相邻。
用 `SimpleGraph.compl_adj`。 -/
theorem ex_18_2 {V : Type*} (G : SimpleGraph V) (u v : V) (huv : u ≠ v) (h : ¬ G.Adj u v) :
    Gᶜ.Adj u v := by
  exact (SimpleGraph.compl_adj G u v).2 ⟨huv, h⟩

/-- 练习 18.3（★）：5-圈是 2-正则的，有 5 条边，且没有三角形。度与边数可以 `decide`（§5、§13）；
无三角形先用 `cliqueFinset_eq_empty_iff` 化成数零（§10）。 -/
theorem ex_18_3 : (∀ v, (SimpleGraph.cycleGraph 5).degree v = 2) ∧
    #(SimpleGraph.cycleGraph 5).edgeFinset = 5 ∧ (SimpleGraph.cycleGraph 5).CliqueFree 3 := by
  exact ⟨by decide, by decide, SimpleGraph.cliqueFinset_eq_empty_iff.1 (by decide)⟩

/-- 练习 18.4（★）：边数的上界（§4）。`n` 个顶点的图至多有 `n * (n - 1) / 2` 条边。用
`SimpleGraph.card_edgeFinset_le_card_choose_two` 与第 12 章的 `Nat.choose_two_right`。 -/
theorem ex_18_4 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset ≤ Fintype.card V * (Fintype.card V - 1) / 2 := by
  have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
  rwa [Nat.choose_two_right] at h

/-- 练习 18.5（★★）：7 个顶点的图不可能是 3-正则的（握手引理，§6）。用
`sum_degrees_eq_twice_card_edges`、`IsRegularOfDegree.degree_eq` 与 `Finset.sum_const`（第 12 章 §3），
最后用 `omega` 看奇偶性。 -/
theorem ex_18_5 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) : ¬ G.IsRegularOfDegree 3 := by
  intro h
  have h1 := G.sum_degrees_eq_twice_card_edges
  simp [h.degree_eq, hV] at h1
  omega

/-- 练习 18.6（★★）：顶点数为奇数的图必有偶数度的顶点。思路同 §6 的 `even_card_of_forall_odd_degree`：
用 `by_contra` 与 `push Not`（第 4 章）得到每个顶点的度都是奇数（`Nat.not_even_iff_odd`），再由
`even_card_odd_degree_vertices` 与 `Finset.filter_true_of_mem` 推出顶点数是偶数，与 `hV` 矛盾。 -/
theorem ex_18_6 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Odd (Fintype.card V)) : ∃ v, Even (G.degree v) := by
  by_contra hne
  push Not at hne
  have hodd : ∀ v, Odd (G.degree v) := fun v ↦ Nat.not_even_iff_odd.1 (hne v)
  have hfilter : ({v | Odd (G.degree v)} : Finset V) = Finset.univ :=
    Finset.filter_true_of_mem fun v _ ↦ hodd v
  have h := G.even_card_odd_degree_vertices
  rw [hfilter, Finset.card_univ] at h
  exact (Nat.not_even_iff_odd.2 hV) h

/-- 练习 18.7（★）：空图里没有途径连接不同的顶点（§7）。对途径分情况讨论：`nil` 时相等，`cons` 时
有一条边，与 `⊥` 矛盾。 -/
theorem ex_18_7 {V : Type*} (u v : V) (p : (⊥ : SimpleGraph V).Walk u v) : u = v := by
  cases p with
  | nil => rfl
  | cons h _ => simp at h

/-- 辅助定义：朴素地数一条途径的步数（对 `Walk` 的结构递归，和 `Walk.length` 的定义同形）。 -/
def walkSteps {V : Type*} {G : SimpleGraph V} : {u v : V} → G.Walk u v → ℕ
  | _, _, .nil => 0
  | _, _, .cons _ p => walkSteps p + 1

/-- 练习 18.8（★★）：对途径归纳（§7）。上面的 `walkSteps` 与 `Walk.length` 相等：
`walkSteps p = p.length`。提示：`induction p with` 分 `nil`、`cons` 两种情形，`cons` 的情形展开
`walkSteps`，再用归纳假设。 -/
theorem ex_18_8 {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    walkSteps p = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [walkSteps, ih]

/-- 练习 18.9（★）：连通性随加边保持（§8）：若 `G ≤ H` 且 `G` 连通，则 `H` 连通。用 `exact?`
（第 9 章）找现成的引理。 -/
theorem ex_18_9 {V : Type*} {G H : SimpleGraph V} (h : G ≤ H) (hG : G.Connected) :
    H.Connected := by
  exact hG.mono h

/-- 练习 18.10（★★）：12 个顶点的树有 11 条边（§9）。用 `IsTree.card_edgeFinset`，再 `omega`。 -/
theorem ex_18_10 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsTree)
    (hV : Fintype.card V = 12) : #G.edgeFinset = 11 := by
  have := h.card_edgeFinset
  omega

/-- 练习 18.11（★★）：无三角形的图里，任一顶点的邻点集是独立集（§10）。先 `classical`（第 8 章），因为
`{a, b, c}` 这样的 `Finset` 字面量需要 `DecidableEq V`；用 `isIndepSet_iff` 展开，再用
`is3Clique_triple_iff`。 -/
theorem ex_18_11 {V : Type*} (G : SimpleGraph V) (h : G.CliqueFree 3) (v : V) :
    G.IsIndepSet (G.neighborSet v) := by
  classical
  rw [SimpleGraph.isIndepSet_iff]
  intro b hb c hc _ hbc
  have hb' : G.Adj v b := hb
  have hc' : G.Adj v c := hc
  exact h _ (SimpleGraph.is3Clique_triple_iff.2 ⟨hb', hc', hbc⟩)

/-- 练习 18.12（★★）：5-圈不能 2-着色（§11）。用 `chromaticNumber_cycleGraph_of_odd`（色数是 `3`）与
`chromaticNumber_le_iff_colorable`，最后 `ℕ∞` 里的不等式 `3 ≤ 2` 可交给 `decide`
（§11 里 `ℕ∞` 的 `2 < 3` 就是这样关上的）。 -/
theorem ex_18_12 : ¬ (SimpleGraph.cycleGraph 5).Colorable 2 := by
  intro h
  have h1 := SimpleGraph.chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)
  have h2 := SimpleGraph.chromaticNumber_le_iff_colorable.2 h
  rw [h1] at h2
  exact absurd h2 (by decide)

/-- 练习 18.13（★★）：二分图没有三角形（§10、§11）。设 `t` 是 3-团：`IsNClique` 的字段 `isClique`
与 `card_eq` 给出 `G.IsClique ↑t` 与 `#t = 3`；团的着色至少要 3 种颜色（`IsClique.card_le_of_colorable`），
与 `Colorable 2` 矛盾。 -/
theorem ex_18_13 {V : Type*} (G : SimpleGraph V) (h : G.Colorable 2) : G.CliqueFree 3 := by
  intro t ht
  have h1 := ht.isClique.card_le_of_colorable h
  have h2 := ht.card_eq
  omega

/-- 练习 18.14（★）：同构保持相邻（§12，第 15 章的打包映射）。若 `f : G ≃g H`，`f` 的逆也保持相邻：
`H.Adj x y → G.Adj (f.symm x) (f.symm y)`。 -/
theorem ex_18_14 {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (x y : W)
    (h : H.Adj x y) : G.Adj (f.symm x) (f.symm y) := by
  exact f.symm.map_rel_iff.2 h

/-- 练习 18.15（★★）：6 个顶点、没有三角形的图至多有 9 条边（Mantel，§14）。用
`CliqueFree.card_edgeFinset_le (r := 2)`、`turanNumber_two` 与 `Fintype.card_fin`，最后 `simpa`。 -/
theorem ex_18_15 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #G.edgeFinset ≤ 9 := by
  have h' := SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) h
  rw [SimpleGraph.turanNumber_two, Fintype.card_fin] at h'
  simpa using h'

end Solutions.Ch18

end
