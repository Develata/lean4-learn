module

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
# 第 20 章　随机图 `G(n, p)` 与一阶矩方法

本章是一个 guided project（带引导的综合项目）。在 Mathlib 自带的 binomial random graph（二项随机图）
`G(V, p)` 上，从零证明一条完整的 first-moment method（一阶矩方法）链：边的边缘概率、边数与三角形数的
expectation（期望）、Markov's inequality（马尔可夫不等式）给出的上界，最后是一个 threshold（阈值）型的
极限定理。正文把这五步的证明全部写出来；练习 20.7–20.11 把同样的五步搬到 4-clique（4-团）`K₄` 上，
以分步 `sorry` 的形式留给你，后一步可以用前一步的结论。
Mathlib 在 v4.35.0 里只有 `G(V, p)` 的定义和几条基本引理（含 `binomialRandom_singleton`，见延伸阅读），
本章的概率估计都是本书自己证明的。读完以后，你能读懂定义链，能把「若干条边同时出现」这类事件算成
`p ^ k`，并能把同样的做法搬到别的 subgraph（子图）上。

## 学习目标
- 读懂 `SimpleGraph.binomialRandom` 的定义链（`Ber` → `infinitePi` → `setBer` → `G(V, p)`），
  用 `#check`、`#print` 看每一层。
- 会处理 `p : unitInterval` 的三种读法（`↑p`、`σ p`、`toNNReal p`）和 `ℝ≥0∞` 与 `ℝ` 之间的换算。
- 会证明图上的事件可测（`measurable_adj`、`measurable_edgeSet`、`fun_prop`）。
- 会把「有限条边同时出现」的概率算成 `p ^ #s`（本章唯一真正的测度论，`measure_edges_eq`）。
- 会把计数量写成 indicator function（指示函数）之和，用 `integral_finsetSum` 算期望，
  用 `mul_meas_ge_le_integral_of_nonneg` 做马尔可夫不等式，用 `squeeze_zero`（第 14 章夹逼定理
  对极限 `0` 的特化）得到 `Tendsto`；再在练习里把这五步独立地搬到 `K₄` 上。

## 前置知识
第 12 章（`Finset`、`Nat.choose`、`sum_boole`）；第 14 章（`Tendsto`、`atTop`、§7 的夹逼）；第 16 章
（`Measure`、`MeasurableSet`、`fun_prop`、`μ.real`）；第 17 章（`IsProbabilityMeasure`、`unitInterval`、
`Ber`、`infinitePi`、马尔可夫不等式）；第 18 章（`SimpleGraph`、`Sym2`、`CliqueFree`、`cliqueFinset`）；
第 19 章（`exists_le_integral`、`setBer`）。
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped SimpleGraph ENNReal NNReal
open unitInterval

namespace Lean4Learn.Ch20

/-!
## 1. 数学：`G(n, p)` 与一阶矩方法

顶点集 `V`（`n` 个顶点），每一对不同的顶点 `{u, v}` **独立地**以概率 `p` 连一条边，得到的 random graph（随机图）记作
`G(V, p)`（`V = Fin n` 时记作 `G(n, p)`；历史上常称 Erdős–Rényi 随机图，Mathlib 避开这个名字，原因见延伸阅读）。
设 `X` 是图的某个计数量（边数、三角形数……），它是若干个指示函数之和：`X = ∑ᵢ 1_{Aᵢ}`。
**一阶矩方法**只用两个事实：linearity of expectation（期望的线性性）
`E[X] = ∑ᵢ P(Aᵢ)`，以及对取值于 `ℕ` 的 `X`，马尔可夫不等式给出 `P(X ≥ 1) ≤ E[X]`。本章的五步：

| 步 | 陈述 | Lean 名字 | 节 |
|---|---|---|---|
| 1 | `u ≠ v` 时 `P(u ~ v) = p` | `edge_marginal` | 5 |
| 2 | `E[#边] = C(n,2) p` | `integral_edgeCount` | 6 |
| 3 | `E[#三角形] = C(n,3) p³` | `integral_triangleCount` | 7 |
| 4 | `P(有三角形) ≤ C(n,3) p³` | `prob_triangle_le` | 8 |
| 5 | `n pₙ → 0` ⟹ `P(G(n, pₙ) 有三角形) → 0` | `tendsto_triangle` | 9 |

第 5 步说的是：边概率比 `1/n` 小得多时，**with high probability（以高概率）**（概率趋于 `1`）没有三角形。

**阈值的含义。** 称 `t(n)` 是图性质（例如「含三角形」）的 threshold function（阈值函数），如果
`p ≪ t(n)` 时 `G(n, p)` 以高概率没有这个性质，`p ≫ t(n)` 时以高概率有。含三角形的阈值是 `1/n`：
`E[#三角形] = C(n,3) p³ ≈ (n p)³ / 6`。本章只证 `p ≪ 1/n` 这一半；另一半（`n pₙ → ∞` 时以高概率有
三角形）要用 second-moment method（二阶矩方法），Mathlib 里没有现成的，见延伸阅读。

**「一阶矩方法」的两种用法。** 第 19 章用的是「存在一个点不超过平均值」（`exists_le_integral`）；
本章用同一个期望，经马尔可夫不等式推出 `P(X ≥ 1) ≤ E[X]`，这是随机图文献里的常用含义。
练习 20.12、20.13 回到第 19 章的用法。

先看一眼我们要研究的对象：
-/

/--
info: SimpleGraph.binomialRandom : (V : Type u_1) → ↑I → Measure (SimpleGraph V)
-/
#guard_msgs (whitespace := lax) in
#check @SimpleGraph.binomialRandom

/-!
## 2. 定义链：`G(V, p)` 是怎么造出来的

`G(V, p)` 是 `SimpleGraph V` 这个类型上的一个测度，由四层搭成。从下往上：

1. `Ber(x, y, p)`（`bernoulliMeasure`，第 17 章）：以概率 `p` 取 `x`、以 `1 - p` 取 `y` 的
   Bernoulli distribution（伯努利分布）。
2. `Measure.infinitePi`（第 17 章）：一族概率测度的（无穷）product measure（积测度）。
3. `setBer(u, p)`（`setBernoulli`）：`Set ι` 上的测度，`u` 里的每个元素独立地以概率 `p` 入选，
   `u` 之外的元素从不入选（第 19 章）。
4. `G(V, p)`（`SimpleGraph.binomialRandom`）：取 `u =` 全体非对角的 unordered pair（无序对）
   `Sym2.diagSetᶜ`（即潜在的边），再沿 `SimpleGraph.edgeSet` 做 `comap`。

先逐层看定义（`#print` 打印定义体；输出里的 `@[expose]` 标记说明这几个定义的定义体对导入者可见。
`Measure.infinitePi` 的定义体对本章没有用处，所以只用 `#check` 看它的类型）：
-/

/--
info: @[expose] def ProbabilityTheory.bernoulliMeasure.{u_1} : {X : Type u_1} →
  [inst : MeasurableSpace X] → X → X → ↑I → Measure X :=
fun {X} [MeasurableSpace X] x y p ↦
  toNNReal p • Measure.dirac x + toNNReal (σ p) • Measure.dirac y
-/
#guard_msgs (whitespace := lax) in
#print ProbabilityTheory.bernoulliMeasure

/--
info: @Measure.infinitePi : {ι : Type u_1} → {X : ι → Type u_2} →
  {mX : (i : ι) → MeasurableSpace (X i)} → ((i : ι) → Measure (X i)) →
  Measure ((i : ι) → X i)
-/
#guard_msgs (whitespace := lax) in
#check @Measure.infinitePi

/--
info: @[expose] def ProbabilityTheory.setBernoulli.{u_1} :
  {ι : Type u_1} → Set ι → ↑I → Measure (Set ι) :=
fun {ι} u p ↦
  Measure.comap (fun s i ↦ i ∈ s) (Measure.infinitePi fun i ↦ Ber(i ∈ u, False, p))
-/
#guard_msgs (whitespace := lax) in
#print ProbabilityTheory.setBernoulli

/--
info: @[expose] def SimpleGraph.binomialRandom.{u_1} :
  (V : Type u_1) → ↑I → Measure (SimpleGraph V) :=
fun V p ↦ Measure.comap SimpleGraph.edgeSet setBer(Sym2.diagSetᶜ, p)
-/
#guard_msgs (whitespace := lax) in
#print SimpleGraph.binomialRandom

/-!
`comap f μ` 在 `s` 上的值是 `μ (f '' s)`（`V` 可数时 `edgeSet` 是 measurable embedding（可测嵌入），见下面的
`measurableEmbedding_edgeSet` 与 `binomialRandom_apply'`），要计算的是 `s` 的**像**（image）；
`map f μ` 在 `s` 上的值是 `μ (f ⁻¹' s)`（`Measure.map_apply`），只需要**原像**（preimage），好算得多。
`V` 可数时 `G(V, p)` 也等于 `setBer(Sym2.diagSetᶜ, p)` 沿 `fromEdgeSet` 的 `map`；
本章的计算都从这个 `map` 形式出发。下面的命令依次给出：`SimpleGraph V` 的 σ-algebra（σ-代数）
（从 `V → V → Prop` 沿 `Adj` 拉回来）；`edgeSet` 是可测嵌入；`comap` 形式的取值公式（对**任意**集合 `S`
成立，没有可测性假设）；`map` 形式。
-/

/--
info: @[instance_reducible, expose] def SimpleGraph.instMeasurableSpace.{u_1} : {V : Type u_1} →
  MeasurableSpace (SimpleGraph V) :=
fun {V} ↦ MeasurableSpace.comap SimpleGraph.Adj inferInstance
-/
#guard_msgs (whitespace := lax) in
#print SimpleGraph.instMeasurableSpace

/--
info: @SimpleGraph.measurableEmbedding_edgeSet : ∀ {V : Type u_1} [Countable V],
  MeasurableEmbedding SimpleGraph.edgeSet
-/
#guard_msgs (whitespace := lax) in
#check @SimpleGraph.measurableEmbedding_edgeSet

/--
info: @SimpleGraph.binomialRandom_apply' : ∀ {V : Type u_1} (p : ↑I) [Countable V]
  (S : Set (SimpleGraph V)), G(V, p) S = setBer(Sym2.diagSetᶜ, p) (SimpleGraph.edgeSet '' S)
-/
#guard_msgs (whitespace := lax) in
#check @SimpleGraph.binomialRandom_apply'

/--
info: SimpleGraph.binomialRandom_eq_map : ∀ (V : Type u_1) (p : ↑I) [Countable V],
  G(V, p) = Measure.map SimpleGraph.fromEdgeSet setBer(Sym2.diagSetᶜ, p)
-/
#guard_msgs (whitespace := lax) in
#check @SimpleGraph.binomialRandom_eq_map

/-- `G(V, p)` 是概率测度（`V` 可数时有实例）。 -/
example {V : Type*} [Countable V] (p : I) : IsProbabilityMeasure G(V, p) := inferInstance

/-- `p = 1` 时边全部出现，`G(V, 1)` 是 complete graph（完全图）`⊤` 处的 Dirac measure（狄拉克测度）；
`p = 0` 时是 edgeless graph（空图）`⊥` 处的狄拉克测度。两条等式 `binomialRandom_one`、
`binomialRandom_zero` 在 `Defs.lean` 里都标为 `@[simp]`，`simp` 直接证明。 -/
example {V : Type*} [Countable V] : G(V, 1) = Measure.dirac ⊤ ∧ G(V, 0) = Measure.dirac ⊥ := by
  simp

/-- 有限图上的单点质量：一个具体的图 `G` 的概率是 `p ^ #边 * (1 - p) ^ (C(n,2) - #边)`，
这正是「每对顶点独立连边」。`Fin 3` 上 `C(3,2) = 3`；`3 - G.edgeSet.ncard` 是自然数的截断减法
（第 2 章），这里 `ncard ≤ 3`，所以减法是准确的。这条等式是 Mathlib 的 `@[simp]` 引理
`binomialRandom_singleton`（顶点数写成 `Nat.card V`）加上 `Nat.card_eq_fintype_card`，
所以 `simp` 一步完成；这里没有 `{G}` 可测的假设（§4）。 -/
example (p : I) (G : SimpleGraph (Fin 3)) :
    G(Fin 3, p) {G} = toNNReal p ^ G.edgeSet.ncard * toNNReal (σ p) ^ (3 - G.edgeSet.ncard) := by
  simp [Nat.card_eq_fintype_card]

/-!
## 3. 参数 `p : unitInterval`

`p : unitInterval`（记号 `I`，第 17 章）有三种读法：coercion（强制转换）`(p : ℝ)`；补集 `σ p : I`，
即 `1 - p`；`toNNReal p : ℝ≥0`，也就是 `#print bernoulliMeasure` 里 `Ber` 的权重。这些记号都在
`unitInterval` 命名空间里，所以需要 `open unitInterval`。测度的值取在 `ℝ≥0∞` 里，而第 16 章的
`μ.real s` 是 `(μ s).toReal`（`measureReal_def`），所以概率先算成 `(toNNReal p : ℝ≥0∞) ^ k`，
再换回实数（最后一个例子；§5 的 `real_edges_eq` 把这一步交给 `simp`）：
-/

example (p : I) : 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ 1 := ⟨unitInterval.nonneg p, unitInterval.le_one p⟩

example (p : I) : (σ p : ℝ) = 1 - p := unitInterval.coe_symm_eq p

example (p : I) (k : ℕ) : ((toNNReal p : ℝ≥0∞) ^ k).toReal = (p : ℝ) ^ k := by
  rw [ENNReal.toReal_pow, ENNReal.coe_toReal, unitInterval.coe_toNNReal]

/-!
## 4. 可测性：图上的事件

测度可以作用在任何集合上（§2 末的单点例子、`binomialRandom_apply'` 都没有可测性假设），
`G(V, p) A` 本身不要求 `A` 可测。可测性是某些引理要的前提：§5 的 `Measure.map_apply` 要
`MeasurableSet s`，§6 的 `integrable_indicator_one` 与 `integral_indicator_one` 也要事件可测。
`SimpleGraph V` 的 σ-代数是 `.comap Adj`，Mathlib 把常用的结论登记成
`@[fun_prop]` 引理：`measurable_adj`、`measurable_edgeSet`、`measurable_fromEdgeSet`，
以及 `V` 可数时的 `measurable_ncard`（第 16 章的 `fun_prop`）。
-/

section Measurability

variable {V : Type*}

example (u v : V) : Measurable fun G : SimpleGraph V ↦ G.Adj u v := by fun_prop

example : Measurable (SimpleGraph.edgeSet : SimpleGraph V → Set (Sym2 V)) := by fun_prop

/-- 边数是一个 random variable（随机变量）。 -/
example [Countable V] : Measurable fun G : SimpleGraph V ↦ G.edgeSet.ncard := by fun_prop

/-!
注意 **`SimpleGraph V` 上没有登记 `MeasurableSingletonClass` 实例**。这不是说单点集不可测（`V` 可数时
`V → V → Prop` 上的单点集可测，沿单射 `Adj` 拉回去仍可测；这是数学论证，本章没有写成 Lean 代码），
只是依赖这个实例的工具不能直接用，例如第 16 章的 `integral_fintype`（类型里带 `[MeasurableSingletonClass X]`）；
实例合成在 `SimpleGraph (Fin 2)` 上失败：
-/

/--
info: @integral_fintype : ∀ {X : Type u_2} {E : Type u_3} {mX : MeasurableSpace X}
  [inst : NormedAddCommGroup E] {f : X → E} [inst_1 : NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSingletonClass X] {μ : Measure X} [inst_4 : Fintype X],
  Integrable f μ → ∫ (x : X), f x ∂μ = ∑ x, μ.real {x} • f x
-/
#guard_msgs (whitespace := lax) in
#check @integral_fintype

/--
error: failed to synthesize instance of type class
  MeasurableSingletonClass (SimpleGraph (Fin 2))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : MeasurableSingletonClass (SimpleGraph (Fin 2)) := inferInstance

/-!
所以本章不枚举图，而是直接对事件和函数做可测性的计算。需要的事件是「`s` 里的每条边都在图里」：
`{G | ∀ e ∈ s, e ∈ G.edgeSet}`，即有限个可测集 `edgeSet ⁻¹' {T | e ∈ T}` 的交；`{T | e ∈ T}` 可测是
根命名空间里的 `measurableSet_mem`：
-/

/--
info: @measurableSet_mem : ∀ {α : Type u_2} (a : α), MeasurableSet {s | a ∈ s}
-/
#guard_msgs (whitespace := lax) in
#check @_root_.measurableSet_mem

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

end Measurability

/-!
## 5. 第 1 步：边的边缘概率与「若干条边同时出现」

**本章唯一真正的测度论**是下面这条引理：对任何有限的、全是非对角无序对的集合 `s`，
`s` 里的边同时出现的概率是 `p ^ #s`。这是边独立性在一阶矩方法里实际用到的那一部分
（它只涉及「边在」这类事件；全体边的 `iIndepFun` 形式见延伸阅读）。
证明的路线（读时对照 §2 的四层；用 (a)–(e) 编号，以免与本章的「第 1–5 步」混淆）：

* (a) `binomialRandom_eq_map` 把 `G(V, p)` 写成 `setBer(Sym2.diagSetᶜ, p)` 沿 `fromEdgeSet` 的 `map`；
* (b) `Measure.map_apply` 把测度换成原像的测度（需要 `fromEdgeSet` 可测，`measurableSet_edges` 给事件可测）；
* (c) `setBernoulli_apply'` 再把 `setBer` 换成 `infinitePi fun e ↦ Ber(e ∈ diagSetᶜ, False, p)` 对原像的测度；
* (d) 原像恰好是 `Set.pi ↑s fun _ ↦ {q : Prop | q}`（只限制有限个坐标的集合；这一步用到
  `edgeSet_fromEdgeSet` 和 `s` 里没有对角元）；
* (e) `Measure.infinitePi_pi` 把这个集合的测度拆成乘积，每个因子是 `Ber(…)` 在 `{q | q}` 上的值，
  等于 `toNNReal p`。

下面两个 `#check` 是 (b)、(e) 用到的引理的陈述（(c) 的效果见证明里第一段目标注释）：
-/

/--
info: @Measure.map_apply : ∀ {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α}
  {mβ : MeasurableSpace β} {μ : Measure α} {f : α → β},
  Measurable f → ∀ {s : Set β}, MeasurableSet s → (Measure.map f μ) s = μ (f ⁻¹' s)
-/
#guard_msgs (whitespace := lax) in
#check @Measure.map_apply

/--
info: @Measure.infinitePi_pi : ∀ {ι : Type u_1} {X : ι → Type u_2}
  {mX : (i : ι) → MeasurableSpace (X i)} (μ : (i : ι) → Measure (X i))
  [hμ : ∀ (i : ι), IsProbabilityMeasure (μ i)] {s : Finset ι} {t : (i : ι) → Set (X i)},
  (∀ i ∈ s, MeasurableSet (t i)) → (Measure.infinitePi μ) ((↑s).pi t) = ∏ i ∈ s, (μ i) (t i)
-/
#guard_msgs (whitespace := lax) in
#check @Measure.infinitePi_pi

section Cylinder

variable {V : Type*}

/-- **联合概率引理**：任何有限的、全是非对角无序对的集合 `s`，`s` 里的边同时出现的概率是 `p ^ #s`。 -/
theorem measure_edges_eq [Countable V] (p : I) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ s, ¬ e.IsDiag) :
    G(V, p) {G | ∀ e ∈ s, e ∈ G.edgeSet} = (toNNReal p : ℝ≥0∞) ^ s.card := by
  -- (a)、(b)、(c)：三次改写
  rw [SimpleGraph.binomialRandom_eq_map, Measure.map_apply SimpleGraph.measurable_fromEdgeSet
    (measurableSet_edges s), setBernoulli_apply']
  -- ⊢ (Measure.infinitePi fun i ↦ Ber(i ∈ Sym2.diagSetᶜ, False, p))
  --     ((fun p ↦ {i | p i}) ⁻¹' SimpleGraph.fromEdgeSet ⁻¹' {G | ∀ e ∈ s, e ∈ G.edgeSet})
  --   = ↑(toNNReal p) ^ s.card
  -- (d)：先把这个原像算成 `Set.pi`
  have hpre : (fun q : Sym2 V → Prop ↦ {i | q i}) ⁻¹'
      (SimpleGraph.fromEdgeSet ⁻¹' {G : SimpleGraph V | ∀ e ∈ s, e ∈ G.edgeSet})
      = Set.pi (↑s) (fun _ ↦ {q : Prop | q}) := by
    ext q
    -- 两个方向：`q` 在原像里 ↔ `q` 在每个坐标 `e ∈ s` 上为真
    refine ⟨fun h ↦ Set.mem_pi.2 fun e he ↦ ?_, fun h e he ↦ ?_⟩
    · have h1 := h e he
      rw [SimpleGraph.edgeSet_fromEdgeSet] at h1
      exact h1.1
    · rw [SimpleGraph.edgeSet_fromEdgeSet]
      exact ⟨Set.mem_pi.1 h e he, by simpa [Sym2.mem_diagSet] using hs e he⟩
  rw [hpre]
  -- ⊢ (Measure.infinitePi fun i ↦ Ber(i ∈ Sym2.diagSetᶜ, False, p))
  --     ((↑s).pi fun x ↦ {q | q}) = ↑(toNNReal p) ^ s.card
  -- (e)：拆成乘积，再逐个因子计算
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

example (p : I) : G(Fin 3, p).real {G | G.Adj 0 1} = p :=
  edge_marginal p (by decide)

/-!
**这些引理名是怎么找到的。** 在项目根目录用 `rg` 搜 Mathlib 源码：`rg "binomialRandom" .lake/packages/mathlib/Mathlib`
只命中定义文件，读它的声明列表就得到 (a)；`rg "infinitePi_pi" .lake/packages/mathlib/Mathlib` 找到
(e) 的乘积公式及其假设；数无序对个数的 `Sym2.card_image_offDiag`（§7）则是按「`Finset.image` 加 `offDiag`
的基数」这个形状搜到的，在 `Mathlib/Data/Sym/Card.lean` 里。写好 (a) 之后，可以在 (b) 之后的目标上试 `exact?`
看看有没有现成的一步。
-/

/-- 假设 `u ≠ v` 不能去掉：`u = v` 时 `G.Adj u u` 永远不成立，概率是 `0`；
所以当 `p ≠ 0` 时 `edge_marginal` 的结论在 `u = v` 处是假的。 -/
example {V : Type*} [Countable V] (p : I) (u : V) : G(V, p).real {G | G.Adj u u} = 0 := by
  have h : {G : SimpleGraph V | G.Adj u u} = ∅ :=
    Set.eq_empty_of_forall_notMem fun G hG ↦ G.irrefl hG
  rw [h]
  exact measureReal_empty

/-!
## 6. 第 2 步：边数的期望

潜在的边是 `Sym2 V` 里的非对角元，共 `C(n,2)` 个（`Sym2.card_subtype_not_diag`）。边数
`G.edgeSet.ncard` 等于「潜在边 `e` 是否在图里」的指示函数之和（`edgeCount_eq_sum`），
于是期望的线性性（`integral_finsetSum`）加上第 1 步（`real_edges_eq`，取 `s = {e}`）就得到结论。

先备一条可积性引理。本章把被积函数写成 `s.indicator (1 : Ω → ℝ)` 的形状，这样可积性
（`integrable_const` 限制到可测集上）和积分（`integral_indicator_one`，换成 `μ.real s`）都有现成的引理可用。
-/

/-- 事件的指示函数是可积的（概率测度，故有限测度）。 -/
theorem integrable_indicator_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (s.indicator (1 : Ω → ℝ)) μ :=
  (integrable_const (1 : ℝ)).indicator hs

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

/-- 具体的 `V = Fin n`：`Fintype.card (Fin n) = n`，`simpa` 做这一步。 -/
example (n : ℕ) (p : I) :
    ∫ G, (G.edgeSet.ncard : ℝ) ∂G(Fin n, p) = n.choose 2 * p := by
  simpa using integral_edgeCount (V := Fin n) p

/-!
## 7. 第 3 步：团与三角形的期望

三角形是 3-团。一般地，`k`-团的个数 `(G.cliqueFinset k).card` 等于对 `k` 元子集 `t` 求和的
「`t` 是团」的指示函数；「`t` 是团」这个事件等于「`t` 内部所有 `C(k,2)` 对顶点都连边」，
联合概率引理（`real_edges_eq`）说它的概率是 `p ^ C(k,2)`。

**为什么语句前有 `open Classical in`。** `cliqueFinset` 需要 `[DecidableRel G.Adj]`，而 `G` 是任意的
`SimpleGraph V`，它的 `Adj` 只是一个 `Prop` 值的关系，没有统一的可判定性实例。按第 8 章 §12 的做法，
用 classical logic（经典逻辑）提供，写成 `open Classical in`。它是整条声明的前缀，所以写在文档注释之前
（本章所有出现处都是这个顺序）。
-/

section Cliques

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in -- `omit` 去掉这条定理不需要的区段变量 `[Fintype V]`
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
/-- 「有三角形」展开成具体的存在量词：三个顶点两两相邻（练习 20.15 用到）。 -/
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

/-!
## 8. 第 4 步：马尔可夫不等式

`X = #k-团 ≥ 0`，「有 `k`-团」包含于 `{1 ≤ X}`，马尔可夫不等式（第 17 章）说
`1 * P(X ≥ 1) ≤ E[X]`。Mathlib 的形式是 `mul_meas_ge_le_integral_of_nonneg`，需要
`0 ≤ᵐ X` 和 `Integrable X`（`integrable_cliqueCount` 提供），取阈值 `ε = 1`。
这里不能直接用 `integral_fintype` 一类的有限空间工具，因为 `SimpleGraph V` 上没有登记
`MeasurableSingletonClass` 实例（§4）；可积性来自「有限个可积指示函数之和」。
（另一条路线是 union bound（联合界）`measureReal_biUnion_finset_le`（第 19 章），对每个 `k` 元子集用
`real_isClique`，不需要积分；本章走马尔可夫，因为期望已经算出来了。）
-/

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

/-!
## 9. 第 5 步：阈值的一半

`C(n,3) ≤ n ^ 3`（`Nat.choose_le_pow`），所以 `P(有三角形) ≤ (n p)³`。若 `n pₙ → 0`，右边趋于 `0`，
左边是非负的，夹逼得到 `P → 0`。第 14 章 §7 的夹逼是 `tendsto_of_tendsto_of_tendsto_of_le_of_le`
（下界、上界两个极限）；下界是 `0` 时 Mathlib 有特化版 `squeeze_zero`（第 17 章用过带撇的 `squeeze_zero'`）：
-/

/--
info: @squeeze_zero : ∀ {α : Type u_1} {f g : α → ℝ} {t₀ : Filter α},
  (∀ (t : α), 0 ≤ f t) → (∀ (t : α), f t ≤ g t) → Tendsto g t₀ (𝓝 0) → Tendsto f t₀ (𝓝 0)
-/
#guard_msgs (whitespace := lax) in
#check @squeeze_zero

/-!
注意序列 `p : ℕ → I` 取值在 `unitInterval`，`Fin n` 上的 `G(Fin n, p n)` 随 `n` 变。
-/

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

/-!
一个具体的序列：`pₙ = 1 / (n + 1) ^ 2`。要把它装进 `unitInterval`，必须交出 `0 ≤ pₙ ≤ 1` 的证明
（这是 `p : I` 的代价，也是类型保证 `p` 合法的好处）。它满足 `n pₙ → 0`，因此 `tendsto_triangle` 适用
（练习 20.14）。
-/

/-- `1 / (n + 1) ^ 2 ∈ [0, 1]`。 -/
noncomputable def pInvSq (n : ℕ) : I :=
  ⟨1 / ((n : ℝ) + 1) ^ 2, by positivity,
    div_le_one_of_le₀ (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)⟩

theorem coe_pInvSq (n : ℕ) : (pInvSq n : ℝ) = 1 / ((n : ℝ) + 1) ^ 2 := rfl

example : (pInvSq 1 : ℝ) = 1 / 4 := by
  rw [coe_pInvSq]
  norm_num

/-!
## 常见错误

**1. 把 `p` 写成 `ℝ`。** `binomialRandom` 的参数是 `unitInterval`，实数 `1 / 2` 不是它的元素：
-/

/--
error: Application type mismatch: The argument
  1 / 2
has type
  ℝ
but is expected to have type
  ↑I
in the application
  G(V, 1 / 2)
-/
#guard_msgs in
noncomputable example (V : Type) : Measure (SimpleGraph V) :=
  SimpleGraph.binomialRandom V (1 / 2 : ℝ)

/-!
**2. 忘了经典可判定性。** `cliqueFinset` 需要 `DecidableRel G.Adj`（§7）：
-/

/--
error: failed to synthesize instance of type class
  DecidableRel G.Adj

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : ℕ :=
  (G.cliqueFinset 3).card

/-!
**3. 漏掉 `u ≠ v`。** `edge_marginal p` 还差一个假设 `u ≠ v`（§5：`u = v` 时概率是 `0`，
当 `p ≠ 0` 时命题是假的，所以对一般的 `p` 这个假设不能去掉），只给 `p` 得到的是一个蕴含式，不是等式：
-/

set_option pp.mvars false in
/--
error: Type mismatch
  edge_marginal p
has type
  ?_ ≠ ?_ → G(?_, p).real {G | G.Adj ?_ ?_} = ↑p
but is expected to have type
  G(V, p).real {G | G.Adj u v} = ↑p
-/
#guard_msgs in
example {V : Type*} [Countable V] (p : I) (u v : V) :
    G(V, p).real {G | G.Adj u v} = p :=
  edge_marginal p

/-!
**4. 把 `n pₙ → 0` 弱化成 `pₙ → 0`。** `tendsto_triangle` 的假设是 `n pₙ → 0`；
`pₙ → 0` 不足以让一阶矩界趋于 `0`（`pₙ = 1 / √n` 时三角形的期望个数趋于无穷）。事实上此时以高概率
有三角形，这需要二阶矩方法，本章不证。把后者当假设交给它，类型不匹配：
-/

/--
error: Application type mismatch: The argument
  hp
has type
  Tendsto (fun n ↦ ↑(p n)) atTop (𝓝 0)
but is expected to have type
  Tendsto (fun n ↦ ↑n * ↑(p n)) atTop (𝓝 0)
in the application
  tendsto_triangle p hp
-/
#guard_msgs in
example (p : ℕ → I) (hp : Tendsto (fun n : ℕ ↦ (p n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ G(Fin n, p n).real {G | ¬ G.CliqueFree 3}) atTop (𝓝 0) :=
  tendsto_triangle p hp

/-!
## 练习

共 15 题（★ 五题，★★ 八题，★★★ 两题）。20.1–20.4 是前面各节的变体；20.5、20.6 复习第 11、12 章的
`Nat.choose` 计算与估计。**20.7–20.11 是本章的 guided project**：把正文的五步（联合概率 → 团的概率 →
期望 → 马尔可夫不等式 → 阈值）在 `K₄` 上重走一遍，每步一个 `sorry`，后一步可以直接用前一步。请按提示
自己写，不要直接套用一般 `k` 的 `integral_cliqueCount`、`prob_not_cliqueFree_le`（那样就跳过了要练的部分）。
20.12、20.13 回到第 19 章的一阶矩方法（存在性）；20.14 复习第 14 章的夹逼；20.15 复习第 18 章的 `CliqueFree`。
-/

section Exercises

/-- 练习 20.1（★）：「`u ~ v` 且 `v ~ w`」是可测事件（§4，第 16 章）。
提示：`measurableSet_adj` 与 `MeasurableSet.inter`；`{G | A G ∧ B G}` 与 `{G | A G} ∩ {G | B G}`
按定义相同，直接 `exact`。 -/
theorem ex_20_1 {V : Type*} (u v w : V) :
    MeasurableSet {G : SimpleGraph V | G.Adj u v ∧ G.Adj v w} := by sorry

/-- 练习 20.2（★）：`σ p` 的 `ℝ≥0∞` 读法（§3）：`(toNNReal (σ p) : ℝ≥0∞).toReal = 1 - p`。
提示：`ENNReal.coe_toReal`、`unitInterval.coe_toNNReal`、`unitInterval.coe_symm_eq`，三次 `rw`。 -/
theorem ex_20_2 (p : I) : ((toNNReal (σ p) : ℝ≥0∞)).toReal = 1 - p := by sorry

/-- 练习 20.3（★）：`p = 0` 时任意两点之间都没有边（§5）。对 `u = v` 与 `u ≠ v` 分情况：
前者 `G.Adj u u` 永假（`G.irrefl`，空集的测度是 `0`），后者用 `edge_marginal`。 -/
theorem ex_20_3 {V : Type*} [Countable V] (u v : V) :
    G(V, 0).real {G | G.Adj u v} = 0 := by sorry

/-- 练习 20.4（★★）：两条不同的非对角边同时出现的概率是 `p ^ 2`（§5）。
提示：`real_edges_eq` 取有限集 `{e, e'}`（先 `classical`），`Finset.card_pair`，最后 `simpa`。 -/
theorem ex_20_4 {V : Type*} [Countable V] (p : I) {e e' : Sym2 V} (hne : e ≠ e')
    (h : ¬ e.IsDiag) (h' : ¬ e'.IsDiag) :
    G(V, p).real {G | e ∈ G.edgeSet ∧ e' ∈ G.edgeSet} = (p : ℝ) ^ 2 := by sorry

/-- 练习 20.5（★）：`4` 个顶点的随机图平均有 `6 p` 条边（§6，第 12 章的 `Nat.choose`）。
提示：`integral_edgeCount`，`Fintype.card_fin`，`Nat.choose 4 2 = 6` 用 `decide`。 -/
theorem ex_20_5 (p : I) : ∫ G, (G.edgeSet.ncard : ℝ) ∂G(Fin 4, p) = 6 * p := by sorry

/-- 练习 20.6（★★）：比 `prob_triangle_le` 加 `C(n,3) ≤ n³` 更精确的估计（§8，第 11、12 章）：
`P(G(n, p) 含三角形) ≤ (n p)³ / 6`。
提示：`prob_triangle_le`；`Nat.choose_le_pow_div 3 n`（`C(n,3) ≤ n³ / 3!`，实数版用 `(α := ℝ)`）；
`Nat.factorial 3 = 6` 用 `decide`；`mul_pow`；`mul_le_mul_of_nonneg_right`；最后 `ring`。 -/
theorem ex_20_6 (n : ℕ) (p : I) :
    G(Fin n, p).real {G | ¬ G.CliqueFree 3} ≤ ((n : ℝ) * p) ^ 3 / 6 := by
  sorry

/-- 练习 20.7（★★）：guided project 第 1 步（§5、§7）：4 元顶点集 `t` 内部的 `C(4,2) = 6` 条边
同时出现的概率是 `p ^ 6`。
提示：`rw [real_edges_eq, Sym2.card_image_offDiag, ht]`，`Nat.choose 4 2 = 6` 用 `decide`；
剩下的目标是「`t.offDiag` 的像里没有对角元」，仿照 `real_isClique` 证明的后半段。 -/
theorem ex_20_7 {V : Type*} [Fintype V] [DecidableEq V] (p : I) (t : Finset V)
    (ht : t.card = 4) :
    G(V, p).real {G | ∀ e ∈ t.offDiag.image Sym2.mk.uncurry, e ∈ G.edgeSet} = (p : ℝ) ^ 6 := by
  sorry

/-- 练习 20.8（★）：第 2 步（§7）：4 元集 `t` 是团的概率是 `p ^ 6`。
提示：`isClique_eq_edges` 把事件换成第 1 步的事件，再用 `ex_20_7`。 -/
theorem ex_20_8 {V : Type*} [Fintype V] [DecidableEq V] (p : I) (t : Finset V)
    (ht : t.card = 4) :
    G(V, p).real {G | G.IsClique (t : Set V)} = (p : ℝ) ^ 6 := by
  sorry

open Classical in
/-- 练习 20.9（★★）：第 3 步（§6、§7）：`E[#K₄] = C(n, 4) p ^ 6`。
提示：仿照 §6 的 `integral_edgeCount`：`simp_rw [cliqueCount_eq_sum]`；`integral_finsetSum`
（可积性 `integrable_indicator_one`、`measurableSet_isClique`）；每一项用 `integral_indicator_one`
和 `ex_20_8`（`Finset.mem_powersetCard_univ` 给出 `#t = 4`）；最后 `Finset.sum_congr`、
`Finset.sum_const`、`nsmul_eq_mul`、`Finset.card_powersetCard`、`Finset.card_univ`。 -/
theorem ex_20_9 {V : Type*} [Fintype V] [DecidableEq V] (p : I) :
    ∫ G, ((G.cliqueFinset 4).card : ℝ) ∂G(V, p) = (Fintype.card V).choose 4 * (p : ℝ) ^ 6 := by
  sorry

open Classical in
/-- 练习 20.10（★★）：第 4 步（§8）：`P(G(V, p) 含 4-团) ≤ C(n, 4) p ^ 6`。
提示：马尔可夫不等式 `mul_meas_ge_le_integral_of_nonneg`（取 `ε = 1`；非负性用
`Filter.Eventually.of_forall`，可积性 `integrable_cliqueCount p 4`），用 `ex_20_9` 改写积分；
再用 `measureReal_mono` 证明 `{G | ¬ G.CliqueFree 4} ⊆ {G | 1 ≤ #K₄}`
（`SimpleGraph.cliqueFinset_eq_empty_iff`、`Finset.card_pos`）。 -/
theorem ex_20_10 {V : Type*} [Fintype V] [DecidableEq V] (p : I) :
    G(V, p).real {G | ¬ G.CliqueFree 4} ≤ (Fintype.card V).choose 4 * (p : ℝ) ^ 6 := by
  sorry

/-- 练习 20.11（★★）：第 5 步，`K₄` 的阈值（§9，第 14 章）：
若 `n⁴ pₙ⁶ → 0`，则 `P(G(n, pₙ) 含 4-团) → 0`。
提示：仿照 `tendsto_triangle`：`squeeze_zero`，第 4 步 `ex_20_10`（`V := Fin n`），`Fintype.card_fin`，
`Nat.choose_le_pow n 4`，`mul_le_mul_of_nonneg_right`，`pow_nonneg`。 -/
theorem ex_20_11 (p : ℕ → I)
    (hp : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 4 * (p n : ℝ) ^ 6) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ G(Fin n, p n).real {G | ¬ G.CliqueFree 4}) atTop (𝓝 0) := by
  sorry

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
  sorry

open Classical in
/-- 练习 20.13（★★）：第 19 章的期望存在性引理：存在一个图，三角形个数不超过期望 `C(n, 3) p ^ 3`。
结论本身很弱（空图就满足），练的是 `exists_le_integral` 的用法；有用的版本见 20.12。
提示：`exists_le_integral`（可积性 `integrable_cliqueCount`），再用 `integral_triangleCount` 改写。 -/
theorem ex_20_13 {V : Type*} [Fintype V] (p : I) :
    ∃ G : SimpleGraph V,
      ((G.cliqueFinset 3).card : ℝ) ≤ (Fintype.card V).choose 3 * (p : ℝ) ^ 3 := by
  sorry

/-- 练习 20.14（★★★）：`pₙ = 1 / (n + 1) ^ 2`（§9 末）时，`P(G(n, pₙ) 有三角形) → 0`。
提示：`tendsto_triangle pInvSq`，剩下 `n * pₙ → 0`：用夹逼，上界 `1 / (n + 1)`
（`tendsto_one_div_add_atTop_nhds_zero_nat`），不等式 `n / (n + 1) ^ 2 ≤ 1 / (n + 1)`
用 `coe_pInvSq`、`mul_one_div`、`div_le_div_iff₀`、`nlinarith`。 -/
theorem ex_20_14 :
    Tendsto (fun n : ℕ ↦ G(Fin n, pInvSq n).real {G | ¬ G.CliqueFree 3}) atTop (𝓝 0) := by
  sorry

/-- 练习 20.15（★★）：「存在三个两两相邻的顶点」的概率至多 `C(n, 3) p ^ 3`（§7、§8，第 18 章）。
提示：`not_cliqueFree_three_iff` 说这个事件就是 `{G | ¬ G.CliqueFree 3}`（用 `Set.ext`），
再用 `prob_triangle_le`。 -/
theorem ex_20_15 {V : Type*} [Fintype V] [DecidableEq V] (p : I) :
    G(V, p).real {G | ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c}
      ≤ (Fintype.card V).choose 3 * (p : ℝ) ^ 3 := by
  sorry

end Exercises

/-!
## 小结

| 概念 | 写法 | 何时用 |
|---|---|---|
| 二项随机图 | `G(V, p)` = `SimpleGraph.binomialRandom V p` | 在随机图上谈概率、期望 |
| 定义链 | `Ber` → `infinitePi` → `setBer(Sym2.diagSetᶜ, p)` → `comap edgeSet` | 查性质来自哪一层 |
| 参数 `p : I` | `(p : ℝ)`、`σ p`、`toNNReal p`；`unitInterval.coe_symm_eq` 等 | `ℝ≥0∞` 换回实数 |
| 可测性 | `measurable_adj`、`measurable_edgeSet`、`fun_prop` | 用 `map_apply`、积分之前 |
| 联合概率引理 | `real_edges_eq`：`G(V,p).real {∀ e ∈ s, …} = p ^ #s` | 若干条指定边同时出现 |
| 边的边缘概率 | `edge_marginal (huv : u ≠ v) : … = p` | 一对不同顶点相邻 |
| 期望（边、团） | `integral_edgeCount`、`integral_cliqueCount` | 计数量是指示函数之和 |
| 一阶矩界 | `prob_not_cliqueFree_le`（马尔可夫，`ε = 1`） | 从期望推 `P(X ≥ 1) ≤ E[X]` |
| 阈值（一半） | `tendsto_triangle`（`squeeze_zero`） | `p` 低于阈值时以高概率不出现 |
| `cliqueFinset` | `open Classical in` 放在文档注释之前 | 数随机图中的团 |
-/

/-!
## 延伸阅读

- Mathlib 源码：`Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`（定义、
  `binomialRandom_eq_map`、`binomialRandom_singleton`、`binomialRandom_zero/one`；文件头的 TODO 写明
  「刻画 `G(V, p)` 的谓词」尚未加入，`Historical note` 解释为什么不叫 Erdős–Rényi 模型）、
  `Mathlib/Probability/Combinatorics/README.md`（「Binomial random graphs (just the definition)」）、
  `Mathlib/Probability/Distributions/SetBernoulli.lean`、`Bernoulli.lean`、
  `Mathlib/Probability/ProductMeasure.lean`、
  `Mathlib/MeasureTheory/Constructions/SimpleGraph.lean`（`SimpleGraph V` 的 σ-algebra 与可测性引理）。
- Mathlib 缺什么（v4.35.0；`rg binomialRandom` 只命中定义文件），也就是本章之后可以接着做的方向：
  (1) 边独立性的 `iIndepFun` 形式。定义文件头的 TODO（刻画 `G(V, p)` 的谓词）预期会包含它；
  本章只用了联合概率形式 `measure_edges_eq`。路线：`binomialRandom_eq_map`、`setBernoulli_eq_map`、
  `Measure.infinitePi_map_pi` 把 `G(V, p)` 的像等同于 `infinitePi`，再用 `iIndepFun_infinitePi`
  （`Mathlib/Probability/Independence/InfinitePi.lean`）[未编译，路线取自调研]。
  (2) **二阶矩方法**：阈值的另一半（`n pₙ → ∞` 时以高概率有三角形）要估计 variance（方差）`Var(#三角形)`。
  概率工具 Mathlib 有：Chebyshev's inequality（切比雪夫不等式）`meas_ge_le_variance_div_sq`、
  `variance_fun_sum`（方差等于 covariance（协方差）之和），都在
  `Mathlib/Probability/Moments/Variance.lean` [未编译：本章不导入该文件，名字与位置是在源码里 `rg` 核对的]；
  缺的是组合部分：对两个三角形按公共顶点数分类（`0` 或 `1` 个公共顶点时独立，`2` 个时共享一条边，
  联合概率 `p ^ 5`，仍是联合概率引理的实例）。
  (3) **connected（连通）的阈值** `log n / n`：第一步是把联合概率引理推广到「一部分边在、一部分边不在」，
  得到 isolated vertex（孤立点）个数的期望 `n (1 - p) ^ (n - 1)`。一阶矩只给出一侧：`n pₙ - log n → +∞` 时这个期望趋于 `0`，
  所以以高概率没有孤立点（只有 `pₙ > log n / n` 不够：`pₙ = (log n + 1) / n` 时期望趋于 `e⁻¹`）；
  反方向（`n pₙ - log n → -∞` 时以高概率有孤立点）要二阶矩，和 (2) 是同一套工具。
  (4) `G(n, M)` 模型（恰好 `M` 条边）。
  做法：先写陈述并用 `sorry` 钉住，每一步复用 `real_edges_eq`，先做一阶矩一侧再做二阶矩一侧。
- Erdős–Rényi, *On random graphs I*, Publ. Math. Debrecen 6 (1959), 290–297；
  Alon–Spencer, *The Probabilistic Method*（*The Second Moment* 与 *Random Graphs* 两章）；
  Janson–Łuczak–Ruciński, *Random Graphs*（*Small Subgraphs* 一章）。这里按章名引用，没有给章号。
- 本书：第 17 章（`Ber`、`infinitePi`、马尔可夫不等式）、第 18 章（`cliqueFinset`）、第 19 章（一阶矩方法、`setBer`）、
  第 21 章（集中不等式：把本章的期望换成 tail bound（尾界））。
-/

end Lean4Learn.Ch20

end
