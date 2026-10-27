module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Sym.Card
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# 第 20 章　答案

练习的陈述（含文档注释）与 `Lean4Learn/Part4/Ch20_RandomGraphs.lean` 逐字相同，只是证明体已补全。
答案文件不导入章节文件，所以章节里的辅助定理（可测性、联合概率引理 `measure_edges_eq`、期望与一阶矩界）
在这里原样重新证明了一遍，练习的答案放在最后的 `Exercises` 区段里。
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped SimpleGraph ENNReal NNReal
open unitInterval

namespace Solutions.Ch20




section Measurability

variable {V : Type*}



/-- 「`s` 里的每条边都在图里」是可测事件。 -/
theorem measurableSet_edges (s : Finset (Sym2 V)) :
    MeasurableSet {G : SimpleGraph V | ∀ e ∈ s, e ∈ G.edgeSet} := by
  have h : {G : SimpleGraph V | ∀ e ∈ s, e ∈ G.edgeSet}
      = ⋂ e ∈ s, SimpleGraph.edgeSet ⁻¹' {T : Set (Sym2 V) | e ∈ T} := by
    ext G
    simp
  rw [h]
  exact Finset.measurableSet_biInter s
    fun e _ ↦ SimpleGraph.measurable_edgeSet (measurableSet_mem e)

/-- 单条边是可测事件（`s = {e}`）。 -/
theorem measurableSet_mem_edgeSet (e : Sym2 V) :
    MeasurableSet {G : SimpleGraph V | e ∈ G.edgeSet} := by
  simpa using measurableSet_edges ({e} : Finset (Sym2 V))

/-- 「`u` 与 `v` 相邻」是可测事件：`s(u, v) ∈ G.edgeSet` 就是 `G.Adj u v`（`simp` 引理 `mem_edgeSet`）。 -/
theorem measurableSet_adj (u v : V) : MeasurableSet {G : SimpleGraph V | G.Adj u v} := by
  simpa using measurableSet_mem_edgeSet s(u, v)

/-- 事件的指示函数是可积的（概率测度，故有限测度）。这是下面 `integral_finsetSum` 要的形状：
被积函数写成 `s.indicator (1 : Ω → ℝ)` 的形式，下面的 `integral_finsetSum` 就按这个形状用。 -/
theorem integrable_indicator_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (s.indicator (1 : Ω → ℝ)) μ :=
  (integrable_const (1 : ℝ)).indicator hs

end Measurability


section Cylinder

variable {V : Type*}

/-- **联合概率引理**：任何有限的、全是非对角无序对的集合 `s`，`s` 里的边同时出现的概率是 `p ^ #s`。 -/
theorem measure_edges_eq [Countable V] (p : I) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ s, ¬ e.IsDiag) :
    G(V, p) {G | ∀ e ∈ s, e ∈ G.edgeSet} = (toNNReal p : ℝ≥0∞) ^ s.card := by
  rw [SimpleGraph.binomialRandom_eq_map, Measure.map_apply SimpleGraph.measurable_fromEdgeSet
    (measurableSet_edges s), setBernoulli_apply']
  have hpre : (fun q : Sym2 V → Prop ↦ {i | q i}) ⁻¹'
      (SimpleGraph.fromEdgeSet ⁻¹' {G : SimpleGraph V | ∀ e ∈ s, e ∈ G.edgeSet})
      = Set.pi (↑s) (fun _ ↦ {q : Prop | q}) := by
    ext q
    refine ⟨fun h ↦ Set.mem_pi.2 fun e he ↦ ?_, fun h e he ↦ ?_⟩
    · have h1 := h e he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h1
      exact h1.1
    · rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨Set.mem_pi.1 h e he, by simpa [Sym2.mem_diagSet] using hs e he⟩
  rw [hpre]
  refine (Measure.infinitePi_pi (μ := fun i : Sym2 V ↦ Ber(i ∈ Sym2.diagSetᶜ, False, p))
    (s := s) (t := fun _ ↦ {q : Prop | q}) (fun _ _ ↦ trivial)).trans ?_
  rw [Finset.prod_congr rfl (fun e he ↦ bernoulliMeasure_apply_of_mem_of_notMem p
    (s := {q : Prop | q}) trivial (by simpa using hs e he) (by simp))]
  simp

/-- 联合概率引理的实数版本：`G(V, p).real {…} = (p : ℝ) ^ #s`（§3 的换算）。 -/
theorem real_edges_eq [Countable V] (p : I) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ s, ¬ e.IsDiag) :
    G(V, p).real {G | ∀ e ∈ s, e ∈ G.edgeSet} = (p : ℝ) ^ s.card := by
  rw [measureReal_def, measure_edges_eq p s hs]
  simp

/-- **第 1 步　边的边缘概率**：对 `u ≠ v`，`P(u ~ v) = p`。取 `s = {s(u, v)}`；
`s(u, v)` 非对角正是 `u ≠ v`（`Sym2.mk_isDiag_iff`）。 -/
theorem edge_marginal [Countable V] (p : I) {u v : V} (huv : u ≠ v) :
    G(V, p).real {G | G.Adj u v} = p := by
  have h := real_edges_eq p {s(u, v)} (by simpa [Sym2.mk_isDiag_iff] using huv)
  simpa using h

end Cylinder


section Edges

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 潜在的边：`Sym2 V` 里的非对角元。 -/
def nonDiagEdges (V : Type*) [Fintype V] [DecidableEq V] : Finset (Sym2 V) :=
  Finset.univ.filter fun e ↦ ¬ e.IsDiag

theorem mem_nonDiagEdges {e : Sym2 V} : e ∈ nonDiagEdges V ↔ ¬ e.IsDiag := by
  simp [nonDiagEdges]

theorem card_nonDiagEdges : (nonDiagEdges V).card = (Fintype.card V).choose 2 := by
  rw [← Sym2.card_subtype_not_diag (α := V), Fintype.card_subtype]
  rfl

/-- 边数 `ncard` 等于潜在边上的指示函数之和。 -/
theorem edgeCount_eq_sum (G : SimpleGraph V) :
    (G.edgeSet.ncard : ℝ) = ∑ e ∈ nonDiagEdges V,
      {G : SimpleGraph V | e ∈ G.edgeSet}.indicator (1 : SimpleGraph V → ℝ) G := by
  classical
  have h1 : G.edgeSet = ↑((nonDiagEdges V).filter fun e ↦ e ∈ G.edgeSet) := by
    ext e
    rw [Finset.mem_coe, Finset.mem_filter, mem_nonDiagEdges]
    exact ⟨fun he ↦ ⟨G.not_isDiag_of_mem_edgeSet he, he⟩, fun h ↦ h.2⟩
  calc (G.edgeSet.ncard : ℝ)
      = (((nonDiagEdges V).filter fun e ↦ e ∈ G.edgeSet).card : ℝ) := by
        rw [← Set.ncard_coe_finset, ← h1]
    _ = ∑ e ∈ nonDiagEdges V, if e ∈ G.edgeSet then (1 : ℝ) else 0 :=
        (Finset.sum_boole (fun e ↦ e ∈ G.edgeSet) _).symm
    _ = _ := by simp [Set.indicator_apply]

/-- 边数可积：有限个可积指示函数之和。 -/
theorem integrable_edgeCount (p : I) :
    Integrable (fun G : SimpleGraph V ↦ (G.edgeSet.ncard : ℝ)) G(V, p) := by
  simp_rw [edgeCount_eq_sum]
  exact integrable_finsetSum _
    (fun e _ ↦ integrable_indicator_one (measurableSet_mem_edgeSet e))

/-- **第 2 步　边数的期望**：`E[|E(G)|] = C(n, 2) p`。 -/
theorem integral_edgeCount (p : I) :
    ∫ G, (G.edgeSet.ncard : ℝ) ∂G(V, p) = (Fintype.card V).choose 2 * p := by
  simp_rw [edgeCount_eq_sum]
  rw [integral_finsetSum _
    (fun e _ ↦ integrable_indicator_one (measurableSet_mem_edgeSet e))]
  have hint : ∀ e ∈ nonDiagEdges V,
      ∫ G, {G : SimpleGraph V | e ∈ G.edgeSet}.indicator (1 : SimpleGraph V → ℝ) G ∂G(V, p)
        = p := by
    intro e he
    rw [integral_indicator_one (measurableSet_mem_edgeSet e)]
    have := real_edges_eq p {e} (by simpa using mem_nonDiagEdges.1 he)
    simpa using this
  rw [Finset.sum_congr rfl hint, Finset.sum_const, nsmul_eq_mul, card_nonDiagEdges]

end Edges



section Cliques

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- 「`t` 是团」与「`t` 内部所有无序对都是边」是同一个事件。 -/
theorem isClique_eq_edges (t : Finset V) :
    {G : SimpleGraph V | G.IsClique (t : Set V)}
      = {G | ∀ e ∈ t.offDiag.image Sym2.mk.uncurry, e ∈ G.edgeSet} := by
  ext G
  constructor
  · intro h e he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 he
    rw [Finset.mem_offDiag] at hab
    have : s(a, b) ∈ G.edgeSet := (SimpleGraph.mem_edgeSet G).2 (h hab.1 hab.2.1 hab.2.2)
    exact this
  · intro h a ha b hb hab
    have := h s(a, b)
      (Finset.mem_image.2 ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩, rfl⟩)
    exact (SimpleGraph.mem_edgeSet G).1 this

omit [Fintype V] in
theorem measurableSet_isClique (t : Finset V) :
    MeasurableSet {G : SimpleGraph V | G.IsClique (t : Set V)} := by
  rw [isClique_eq_edges]
  exact measurableSet_edges _

/-- `t` 是团的概率是 `p ^ C(#t, 2)`：`Sym2.card_image_offDiag` 数出 `t` 内部有 `C(#t, 2)` 个无序对。 -/
theorem real_isClique (p : I) (t : Finset V) :
    G(V, p).real {G | G.IsClique (t : Set V)} = (p : ℝ) ^ t.card.choose 2 := by
  rw [isClique_eq_edges, real_edges_eq, Sym2.card_image_offDiag]
  intro e he
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 he
  rw [Finset.mem_offDiag] at hab
  show ¬ (s(a, b)).IsDiag
  rw [Sym2.mk_isDiag_iff]
  exact hab.2.2

open Classical in
/-- `k`-团个数等于对 `k` 元子集求和的团指示函数（`Finset.sum_boole`，第 12 章）。 -/
theorem cliqueCount_eq_sum (k : ℕ) (G : SimpleGraph V) :
    ((G.cliqueFinset k).card : ℝ) = ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset V),
      {G : SimpleGraph V | G.IsClique (t : Set V)}.indicator (1 : SimpleGraph V → ℝ) G := by
  have h : G.cliqueFinset k = (Finset.powersetCard k (Finset.univ : Finset V)).filter
      fun t : Finset V ↦ G.IsClique (t : Set V) := by
    ext t
    simp only [SimpleGraph.mem_cliqueFinset_iff, Finset.mem_filter, Finset.mem_powersetCard_univ]
    exact ⟨fun h ↦ ⟨h.card_eq, h.isClique⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  rw [h]
  calc (((Finset.powersetCard k (Finset.univ : Finset V)).filter
        fun t : Finset V ↦ G.IsClique (t : Set V)).card : ℝ)
      = ∑ t ∈ Finset.powersetCard k (Finset.univ : Finset V),
          if G.IsClique (t : Set V) then (1 : ℝ) else 0 :=
        (Finset.sum_boole (fun t : Finset V ↦ G.IsClique (t : Set V)) _).symm
    _ = _ := by simp [Set.indicator_apply]

open Classical in
/-- `k`-团个数可积。 -/
theorem integrable_cliqueCount (p : I) (k : ℕ) :
    Integrable (fun G : SimpleGraph V ↦ ((G.cliqueFinset k).card : ℝ)) G(V, p) := by
  simp_rw [cliqueCount_eq_sum]
  exact integrable_finsetSum _
    (fun t _ ↦ integrable_indicator_one (measurableSet_isClique t))

open Classical in
/-- **第 3 步（一般 `k`）　`k`-团个数的期望**：`E[#K_k] = C(n, k) p ^ C(k, 2)`。 -/
theorem integral_cliqueCount (p : I) (k : ℕ) :
    ∫ G, ((G.cliqueFinset k).card : ℝ) ∂G(V, p)
      = (Fintype.card V).choose k * (p : ℝ) ^ k.choose 2 := by
  simp_rw [cliqueCount_eq_sum]
  rw [integral_finsetSum _
    (fun t _ ↦ integrable_indicator_one (measurableSet_isClique t))]
  have hint : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset V),
      ∫ G, {G : SimpleGraph V | G.IsClique (t : Set V)}.indicator
        (1 : SimpleGraph V → ℝ) G ∂G(V, p) = (p : ℝ) ^ k.choose 2 := by
    intro t ht
    rw [integral_indicator_one (measurableSet_isClique t), real_isClique,
      Finset.mem_powersetCard_univ.1 ht]
  rw [Finset.sum_congr rfl hint, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
    Finset.card_univ]

open Classical in
/-- **第 3 步　三角形个数的期望**：`E[#三角形] = C(n, 3) p ^ 3`（`k = 3`，`C(3,2) = 3`）。 -/
theorem integral_triangleCount (p : I) :
    ∫ G, ((G.cliqueFinset 3).card : ℝ) ∂G(V, p) = (Fintype.card V).choose 3 * (p : ℝ) ^ 3 := by
  rw [integral_cliqueCount]
  have : Nat.choose 3 2 = 3 := by decide
  rw [this]

omit [Fintype V] in
/-- 「有三角形」展开成具体的存在量词：三个顶点两两相邻。 -/
theorem not_cliqueFree_three_iff (G : SimpleGraph V) :
    ¬ G.CliqueFree 3 ↔ ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  simp only [SimpleGraph.CliqueFree, not_forall, not_not]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨a, b, c, h1, h2, h3, -⟩ := SimpleGraph.is3Clique_iff.1 hs
    exact ⟨a, b, c, h1, h2, h3⟩
  · rintro ⟨a, b, c, h1, h2, h3⟩
    exact ⟨{a, b, c}, SimpleGraph.is3Clique_triple_iff.2 ⟨h1, h2, h3⟩⟩

end Cliques


section Markov

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- **第 4 步（一般 `k`）　一阶矩界**：`P(G 含 k-团) ≤ E[#K_k]`。 -/
theorem prob_not_cliqueFree_le (p : I) (k : ℕ) :
    G(V, p).real {G | ¬ G.CliqueFree k}
      ≤ (Fintype.card V).choose k * (p : ℝ) ^ k.choose 2 := by
  have hnn : 0 ≤ᵐ[G(V, p)] (fun G : SimpleGraph V ↦ ((G.cliqueFinset k).card : ℝ)) :=
    Filter.Eventually.of_forall fun G ↦ Nat.cast_nonneg _
  have hM := mul_meas_ge_le_integral_of_nonneg hnn (integrable_cliqueCount p k) 1
  rw [integral_cliqueCount] at hM
  calc G(V, p).real {G | ¬ G.CliqueFree k}
      ≤ G(V, p).real {G : SimpleGraph V | 1 ≤ ((G.cliqueFinset k).card : ℝ)} := by
        refine measureReal_mono ?_
        intro G hG
        have hne : (G.cliqueFinset k).Nonempty :=
          Finset.nonempty_iff_ne_empty.2 fun h ↦ hG (SimpleGraph.cliqueFinset_eq_empty_iff.1 h)
        have : 1 ≤ (G.cliqueFinset k).card := Finset.card_pos.2 hne
        show (1 : ℝ) ≤ _
        exact_mod_cast this
    _ ≤ _ := by simpa using hM

/-- **第 4 步　三角形的一阶矩界**：`P(G(V, p) 含三角形) ≤ C(n, 3) p ^ 3`。 -/
theorem prob_triangle_le (p : I) :
    G(V, p).real {G | ¬ G.CliqueFree 3} ≤ (Fintype.card V).choose 3 * (p : ℝ) ^ 3 := by
  have := prob_not_cliqueFree_le (V := V) p 3
  have h3 : Nat.choose 3 2 = 3 := by decide
  rwa [h3] at this

end Markov

/-- **第 5 步**：若 `n pₙ → 0`，则 `P(G(n, pₙ) 含三角形) → 0`。 -/
theorem tendsto_triangle (p : ℕ → I)
    (hp : Tendsto (fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ G(Fin n, p n).real {G | ¬ G.CliqueFree 3}) atTop (𝓝 0) := by
  have hcube : Tendsto (fun n : ℕ ↦ ((n : ℝ) * (p n : ℝ)) ^ 3) atTop (𝓝 0) := by
    simpa using hp.pow 3
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) hcube
  refine (prob_triangle_le (p n)).trans ?_
  rw [Fintype.card_fin, mul_pow]
  have h1 : ((n.choose 3 : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 := by exact_mod_cast Nat.choose_le_pow n 3
  exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (unitInterval.nonneg (p n)) 3)

/-- `1 / (n + 1) ^ 2 ∈ [0, 1]`。 -/
noncomputable def pInvSq (n : ℕ) : I :=
  ⟨1 / ((n : ℝ) + 1) ^ 2, by positivity,
    div_le_one_of_le₀ (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)⟩

theorem coe_pInvSq (n : ℕ) : (pInvSq n : ℝ) = 1 / ((n : ℝ) + 1) ^ 2 := rfl



section Exercises

/-- 练习 20.1（★）：「`u ~ v` 且 `v ~ w`」是可测事件（§4，第 16 章）。
提示：`measurableSet_adj` 与 `MeasurableSet.inter`；`{G | A G ∧ B G}` 与 `{G | A G} ∩ {G | B G}`
按定义相同，直接 `exact`。 -/
theorem ex_20_1 {V : Type*} (u v w : V) :
    MeasurableSet {G : SimpleGraph V | G.Adj u v ∧ G.Adj v w} :=
  (measurableSet_adj u v).inter (measurableSet_adj v w)

/-- 练习 20.2（★）：`σ p` 的 `ℝ≥0∞` 读法（§3）：`(toNNReal (σ p) : ℝ≥0∞).toReal = 1 - p`。
提示：`ENNReal.coe_toReal`、`unitInterval.coe_toNNReal`、`unitInterval.coe_symm_eq`，三次 `rw`。 -/
theorem ex_20_2 (p : I) : ((toNNReal (σ p) : ℝ≥0∞)).toReal = 1 - p := by
  rw [ENNReal.coe_toReal, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]

/-- 练习 20.3（★）：`p = 0` 时任意两点之间都没有边（§5）。对 `u = v` 与 `u ≠ v` 分情况：
前者 `G.Adj u u` 永假（`G.irrefl`，空集的测度是 `0`），后者用 `edge_marginal`。 -/
theorem ex_20_3 {V : Type*} [Countable V] (u v : V) :
    G(V, 0).real {G | G.Adj u v} = 0 := by
  by_cases huv : u = v
  · subst huv
    have h : {G : SimpleGraph V | G.Adj u u} = ∅ :=
      Set.eq_empty_of_forall_notMem fun G hG ↦ G.irrefl hG
    rw [h]
    exact measureReal_empty
  · rw [edge_marginal 0 huv]
    simp

/-- 练习 20.4（★★）：两条不同的非对角边同时出现的概率是 `p ^ 2`（§5）。
提示：`real_edges_eq` 取有限集 `{e, e'}`（先 `classical`），`Finset.card_pair`，最后 `simpa`。 -/
theorem ex_20_4 {V : Type*} [Countable V] (p : I) {e e' : Sym2 V} (hne : e ≠ e')
    (h : ¬ e.IsDiag) (h' : ¬ e'.IsDiag) :
    G(V, p).real {G | e ∈ G.edgeSet ∧ e' ∈ G.edgeSet} = (p : ℝ) ^ 2 := by
  classical
  have := real_edges_eq p {e, e'} (by simp [h, h'])
  rw [Finset.card_pair hne] at this
  simpa using this

/-- 练习 20.5（★）：`4` 个顶点的随机图平均有 `6 p` 条边（§6，第 12 章的 `Nat.choose`）。
提示：`integral_edgeCount`，`Fintype.card_fin`，`Nat.choose 4 2 = 6` 用 `decide`。 -/
theorem ex_20_5 (p : I) : ∫ G, (G.edgeSet.ncard : ℝ) ∂G(Fin 4, p) = 6 * p := by
  rw [integral_edgeCount, Fintype.card_fin]
  have h : Nat.choose 4 2 = 6 := by decide
  rw [h]
  norm_num

/-- 练习 20.6（★★）：比 `prob_triangle_le` 加 `C(n,3) ≤ n³` 更精确的估计（§8，第 11、12 章）：
`P(G(n, p) 含三角形) ≤ (n p)³ / 6`。
提示：`prob_triangle_le`；`Nat.choose_le_pow_div 3 n`（`C(n,3) ≤ n³ / 3!`，实数版用 `(α := ℝ)`）；
`Nat.factorial 3 = 6` 用 `decide`；`mul_pow`；`mul_le_mul_of_nonneg_right`；最后 `ring`。 -/
theorem ex_20_6 (n : ℕ) (p : I) :
    G(Fin n, p).real {G | ¬ G.CliqueFree 3} ≤ ((n : ℝ) * p) ^ 3 / 6 := by
  refine (prob_triangle_le p).trans ?_
  have h : (n.choose 3 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by
    have h0 := Nat.choose_le_pow_div (α := ℝ) 3 n
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by
      rw [show Nat.factorial 3 = 6 by decide]
      norm_num
    rw [h6] at h0
    exact_mod_cast h0
  rw [Fintype.card_fin, mul_pow]
  calc ((n.choose 3 : ℕ) : ℝ) * (p : ℝ) ^ 3 ≤ ((n : ℝ) ^ 3 / 6) * (p : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right h (pow_nonneg (unitInterval.nonneg p) 3)
    _ = (n : ℝ) ^ 3 * (p : ℝ) ^ 3 / 6 := by ring

/-- 练习 20.7（★★）：guided project 第 1 步（§5、§7）：4 元顶点集 `t` 内部的 `C(4,2) = 6` 条边
同时出现的概率是 `p ^ 6`。
提示：`rw [real_edges_eq, Sym2.card_image_offDiag, ht]`，`Nat.choose 4 2 = 6` 用 `decide`；
剩下的目标是「`t.offDiag` 的像里没有对角元」，仿照 `real_isClique` 证明的后半段。 -/
theorem ex_20_7 {V : Type*} [Fintype V] [DecidableEq V] (p : I) (t : Finset V)
    (ht : t.card = 4) :
    G(V, p).real {G | ∀ e ∈ t.offDiag.image Sym2.mk.uncurry, e ∈ G.edgeSet} = (p : ℝ) ^ 6 := by
  have h6 : Nat.choose 4 2 = 6 := by decide
  rw [real_edges_eq, Sym2.card_image_offDiag, ht, h6]
  intro e he
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 he
  rw [Finset.mem_offDiag] at hab
  show ¬ (s(a, b)).IsDiag
  rw [Sym2.mk_isDiag_iff]
  exact hab.2.2

/-- 练习 20.8（★）：第 2 步（§7）：4 元集 `t` 是团的概率是 `p ^ 6`。
提示：`isClique_eq_edges` 把事件换成第 1 步的事件，再用 `ex_20_7`。 -/
theorem ex_20_8 {V : Type*} [Fintype V] [DecidableEq V] (p : I) (t : Finset V)
    (ht : t.card = 4) :
    G(V, p).real {G | G.IsClique (t : Set V)} = (p : ℝ) ^ 6 := by
  rw [isClique_eq_edges]
  exact ex_20_7 p t ht

open Classical in
/-- 练习 20.9（★★）：第 3 步（§6、§7）：`E[#K₄] = C(n, 4) p ^ 6`。
提示：仿照 §6 的 `integral_edgeCount`：`simp_rw [cliqueCount_eq_sum]`；`integral_finsetSum`
（可积性 `integrable_indicator_one`、`measurableSet_isClique`）；每一项用 `integral_indicator_one`
和 `ex_20_8`（`Finset.mem_powersetCard_univ` 给出 `#t = 4`）；最后 `Finset.sum_congr`、
`Finset.sum_const`、`nsmul_eq_mul`、`Finset.card_powersetCard`、`Finset.card_univ`。 -/
theorem ex_20_9 {V : Type*} [Fintype V] [DecidableEq V] (p : I) :
    ∫ G, ((G.cliqueFinset 4).card : ℝ) ∂G(V, p) = (Fintype.card V).choose 4 * (p : ℝ) ^ 6 := by
  simp_rw [cliqueCount_eq_sum]
  rw [integral_finsetSum _
    (fun t _ ↦ integrable_indicator_one (measurableSet_isClique t))]
  have hint : ∀ t ∈ Finset.powersetCard 4 (Finset.univ : Finset V),
      ∫ G, {G : SimpleGraph V | G.IsClique (t : Set V)}.indicator
        (1 : SimpleGraph V → ℝ) G ∂G(V, p) = (p : ℝ) ^ 6 := by
    intro t ht
    rw [integral_indicator_one (measurableSet_isClique t)]
    exact ex_20_8 p t (Finset.mem_powersetCard_univ.1 ht)
  rw [Finset.sum_congr rfl hint, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
    Finset.card_univ]

open Classical in
/-- 练习 20.10（★★）：第 4 步（§8）：`P(G(V, p) 含 4-团) ≤ C(n, 4) p ^ 6`。
提示：马尔可夫不等式 `mul_meas_ge_le_integral_of_nonneg`（取 `ε = 1`；非负性用
`Filter.Eventually.of_forall`，可积性 `integrable_cliqueCount p 4`），用 `ex_20_9` 改写积分；
再用 `measureReal_mono` 证明 `{G | ¬ G.CliqueFree 4} ⊆ {G | 1 ≤ #K₄}`
（`SimpleGraph.cliqueFinset_eq_empty_iff`、`Finset.card_pos`）。 -/
theorem ex_20_10 {V : Type*} [Fintype V] [DecidableEq V] (p : I) :
    G(V, p).real {G | ¬ G.CliqueFree 4} ≤ (Fintype.card V).choose 4 * (p : ℝ) ^ 6 := by
  have hnn : 0 ≤ᵐ[G(V, p)] (fun G : SimpleGraph V ↦ ((G.cliqueFinset 4).card : ℝ)) :=
    Filter.Eventually.of_forall fun G ↦ Nat.cast_nonneg _
  have hM := mul_meas_ge_le_integral_of_nonneg hnn (integrable_cliqueCount p 4) 1
  rw [ex_20_9] at hM
  calc G(V, p).real {G | ¬ G.CliqueFree 4}
      ≤ G(V, p).real {G : SimpleGraph V | 1 ≤ ((G.cliqueFinset 4).card : ℝ)} := by
        refine measureReal_mono ?_
        intro G hG
        have hne : (G.cliqueFinset 4).Nonempty :=
          Finset.nonempty_iff_ne_empty.2 fun h ↦ hG (SimpleGraph.cliqueFinset_eq_empty_iff.1 h)
        have : 1 ≤ (G.cliqueFinset 4).card := Finset.card_pos.2 hne
        show (1 : ℝ) ≤ _
        exact_mod_cast this
    _ ≤ _ := by simpa using hM

/-- 练习 20.11（★★）：第 5 步，`K₄` 的阈值（§9，第 14 章）：
若 `n⁴ pₙ⁶ → 0`，则 `P(G(n, pₙ) 含 4-团) → 0`。
提示：仿照 `tendsto_triangle`：`squeeze_zero`，第 4 步 `ex_20_10`（`V := Fin n`），`Fintype.card_fin`，
`Nat.choose_le_pow n 4`，`mul_le_mul_of_nonneg_right`，`pow_nonneg`。 -/
theorem ex_20_11 (p : ℕ → I)
    (hp : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 * (p n : ℝ) ^ 6) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ G(Fin n, p n).real {G | ¬ G.CliqueFree 4}) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) hp
  refine (ex_20_10 (V := Fin n) (p n)).trans ?_
  have h1 : ((n.choose 4 : ℕ) : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast Nat.choose_le_pow n 4
  rw [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (unitInterval.nonneg (p n)) 6)

open Classical in
/-- 练习 20.12（★★★）：deletion method（删除法）的第一步（第 19 章）：存在一个图，使「边数减三角形个数」
不小于它的期望 `C(n, 2) p - C(n, 3) p ^ 3`（再从每个三角形里删掉一条边，就得到边数不少于这个值的
无三角形图）。分步骨架：
(a) `h₁ := integrable_edgeCount p`，`h₂ := integrable_cliqueCount p 3`，`h₁.sub h₂` 是差的可积性；
(b) `exists_integral_le` 给出 `G`，使差的积分不超过 `G` 处的差；
(c) `integral_sub h₁ h₂` 把积分拆成两个；
(d) `integral_edgeCount`、`integral_triangleCount` 把两个积分算出来。 -/
theorem ex_20_12 {V : Type*} [Fintype V] (p : I) :
    ∃ G : SimpleGraph V,
      ((Fintype.card V).choose 2 : ℝ) * p - (Fintype.card V).choose 3 * (p : ℝ) ^ 3
        ≤ (G.edgeSet.ncard : ℝ) - (G.cliqueFinset 3).card := by
  have h₁ := integrable_edgeCount (V := V) p
  have h₂ := integrable_cliqueCount (V := V) p 3
  have hi : Integrable
      (fun G : SimpleGraph V ↦ (G.edgeSet.ncard : ℝ) - (G.cliqueFinset 3).card) G(V, p) :=
    h₁.sub h₂
  obtain ⟨G, hG⟩ := exists_integral_le hi
  refine ⟨G, ?_⟩
  rw [integral_sub h₁ h₂, integral_edgeCount, integral_triangleCount] at hG
  exact hG

open Classical in
/-- 练习 20.13（★★）：第 19 章的期望存在性引理：存在一个图，三角形个数不超过期望 `C(n, 3) p ^ 3`。
结论本身很弱（空图就满足），练的是 `exists_le_integral` 的用法；有用的版本见 20.12。
提示：`exists_le_integral`（可积性 `integrable_cliqueCount`），再用 `integral_triangleCount` 改写。 -/
theorem ex_20_13 {V : Type*} [Fintype V] (p : I) :
    ∃ G : SimpleGraph V,
      ((G.cliqueFinset 3).card : ℝ) ≤ (Fintype.card V).choose 3 * (p : ℝ) ^ 3 := by
  obtain ⟨G, hG⟩ := exists_le_integral (integrable_cliqueCount (V := V) p 3)
  exact ⟨G, by rwa [integral_triangleCount] at hG⟩

/-- 练习 20.14（★★★）：`pₙ = 1 / (n + 1) ^ 2`（§9 末）时，`P(G(n, pₙ) 有三角形) → 0`。
提示：`tendsto_triangle pInvSq`，剩下 `n * pₙ → 0`：用夹逼，上界 `1 / (n + 1)`
（`tendsto_one_div_add_atTop_nhds_zero_nat`），不等式 `n / (n + 1) ^ 2 ≤ 1 / (n + 1)`
用 `coe_pInvSq`、`mul_one_div`、`div_le_div_iff₀`、`nlinarith`。 -/
theorem ex_20_14 :
    Tendsto (fun n : ℕ ↦ G(Fin n, pInvSq n).real {G | ¬ G.CliqueFree 3}) atTop (𝓝 0) := by
  refine tendsto_triangle pInvSq ?_
  have h1 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine squeeze_zero (fun n ↦ ?_) (fun n ↦ ?_) h1
  · show (0 : ℝ) ≤ (n : ℝ) * (pInvSq n : ℝ)
    rw [coe_pInvSq]
    positivity
  · show (n : ℝ) * (pInvSq n : ℝ) ≤ 1 / ((n : ℝ) + 1)
    rw [coe_pInvSq, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- 练习 20.15（★★）：「存在三个两两相邻的顶点」的概率至多 `C(n, 3) p ^ 3`（§7、§8，第 18 章）。
提示：`not_cliqueFree_three_iff` 说这个事件就是 `{G | ¬ G.CliqueFree 3}`（用 `Set.ext`），
再用 `prob_triangle_le`。 -/
theorem ex_20_15 {V : Type*} [Fintype V] [DecidableEq V] (p : I) :
    G(V, p).real {G | ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c}
      ≤ (Fintype.card V).choose 3 * (p : ℝ) ^ 3 := by
  have h : {G : SimpleGraph V | ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c}
      = {G | ¬ G.CliqueFree 3} :=
    Set.ext fun G ↦ (not_cliqueFree_three_iff G).symm
  rw [h]
  exact prob_triangle_le p

end Exercises

end Solutions.Ch20

end
