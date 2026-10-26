module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# 第 14 章　滤子与极限：Mathlib 的分析语言

Mathlib 里没有「数列极限」「函数在一点的极限」「趋于无穷的极限」三套并行的理论，只有一个概念
`Filter.Tendsto`。它的参数是 filter（滤子）：滤子把「n 足够大」「x 足够靠近 a」「几乎处处」这类说法
统一成同一种对象，于是 `Tendsto.add`、`Tendsto.comp`、夹逼这些定理只需要证一次。本章先讲滤子是什么、
三个标准滤子和 `∀ᶠ`（最终成立）、`filter_upwards`，再讲 `Tendsto` 的展开以及它和你熟悉的 ε–N 语言之间的
互译（`Metric.tendsto_atTop`），然后是极限的代数、夹逼、复合与常用序列的极限，最后速览单调收敛、
`limsup`/`liminf`、级数 `Summable`/`tsum`、`IsBigO`，以及连续性与开集的最小集合。读完后你能把一个手写的
ε–N 论证改写成几行库引理，也能在需要时把库引理展开回 ε–N。

## 学习目标
- 说出 `Filter` 的三条公理，认出 `atTop`、`𝓝 x`、`𝓟 s` 三个标准滤子，并知道滤子之间的序是集合族的反向包含。
- 会用 `∀ᶠ x in l, p x`（沿 `l` 最终成立）与 `filter_upwards [h₁, …] with x hx₁ …` 合并、推导「最终成立」的命题。
- 会把 `Tendsto f l₁ l₂` 展开成 `map f l₁ ≤ l₂`、`∀ s ∈ l₂, f ⁻¹' s ∈ l₁`，并用 `Metric.tendsto_atTop` 与
  ε–N 双向互译；同一个极限（`1 / n → 0`）既能手工用 ε–N 证，也能用库引理证。
- 会用 `Tendsto.add/mul/const_mul/div_const/pow`、`tendsto_const_nhds`、`tendsto_nhds_unique`、
  夹逼 `tendsto_of_tendsto_of_tendsto_of_le_of_le`、`Tendsto.comp`，并认识常用序列极限引理。
- 会用单调收敛 `tendsto_atTop_ciSup`，读懂 `limsup`/`liminf` 的定义与「边界条件只在完备格里自动成立」。
- 会用 `HasSum`/`Summable`/`tsum` 处理几何级数与比较判别法，知道不可和时 `tsum = 0` 的垃圾值。
- 会读 `f =O[l] g`、`f =o[l] g`；会用 `fun_prop`/`continuity` 证连续性，用 `Metric.ball`、`IsOpen` 谈开集。

## 前置知识
第 4 章（量词、`obtain`、`intro` 与否定）；第 5 章（`rw`、`simp`、`calc`）；第 6 章（归纳，练习 14.12 用）；
第 7 章（集合与原像）；第 8 章（`ℝ`、强制转换 `↑`）；第 9 章（用 `#check`、Loogle、`exact?` 找引理名）；
第 10 章（`positivity`、`fun_prop`、`continuity`）；
第 11 章（`abs_lt`、`div_lt_iff₀`、`exists_nat_gt`：本章的 ε–N 证明直接使用它们）；
第 12 章（`Finset.range`、`∑ i ∈ s`：§9 的部分和）。
-/

@[expose] public section

namespace Lean4Learn.Ch14

/-!
## 1. 滤子是什么

先回忆 `n → ∞` 时数列的极限：条件是「对每个 ε > 0，**存在 N**，使得 **所有 n ≥ N** 都有
`|u n - a| < ε`」。「存在 N，所有 n ≥ N」这个量词结构只描述一件事：一个性质对**足够大的 n**成立。点处的
极限也有同样的量词结构（「存在 δ > 0，使所有满足 `|x - a| < δ` 的 x」：x 足够靠近 a）。这里的写法不去掉
`x = a` 这一点，对应 §2 的邻域滤子 `𝓝 a`（`Metric.mem_nhds_iff`）；去心的版本要求 `0 < |x - a| < δ`，
本章不用。Mathlib 把这种量词结构抽象成一个对象：filter（滤子），一个满足
三条公理的集合族 `F : Filter α`：

- 全集在 `F` 里；
- `F` 对超集封闭；
- `F` 对有限交封闭。

读作：`s ∈ F` 表示「`s` 是 `F` 眼里的大集合」，例如对 `n → ∞` 的滤子，`{n | n ≥ 100}` 是大集合，
`{n | n < 100}` 不是。
-/

section Main

open Filter
open scoped Topology

variable {α β : Type*}

example (F : Filter α) : Set.univ ∈ F := F.univ_sets
example (F : Filter α) (s t : Set α) (hs : s ∈ F) (hst : s ⊆ t) : t ∈ F := F.sets_of_superset hs hst
example (F : Filter α) (s t : Set α) (hs : s ∈ F) (ht : t ∈ F) : s ∩ t ∈ F := F.inter_sets hs ht

/-!
Mathlib 的 `Filter` **不**要求 `∅ ∉ F`（Bourbaki 的定义要求）。最小的滤子 `⊥` 就包含所有集合，包括
`∅`。要求滤子非平凡时，用类型类 `Filter.NeBot`，即 non-trivial filter（非平凡滤子）。
`tendsto_nhds_unique` 之类的定理需要这个条件。`ℕ` 上的 `atTop` 与 `ℝ` 上的 `𝓝 x` 都是非平凡的，
实例由 Lean 自动找到；`𝓟 s` 非平凡当且仅当 `s` 非空：
-/

example : (∅ : Set ℕ) ∈ (⊥ : Filter ℕ) := mem_bot
example : NeBot (atTop : Filter ℕ) := inferInstance
example : NeBot (𝓝 (0 : ℝ)) := inferInstance
example (s : Set ℕ) : NeBot (𝓟 s) ↔ s.Nonempty := principal_neBot_iff

/-!
## 2. 三个标准滤子

**principal filter（主滤子）`𝓟 s`**：所有包含 `s` 的集合。它最简单，常用来把「性质成立在 `s` 上」
装进滤子。**`atTop`（趋于无穷的滤子）**：在预序 `α` 上定义为所有 `𝓟 (Set.Ici a)` 的下确界；
对任何预序，尾巴 `{b | a ≤ b}` 都属于 `atTop`（`mem_atTop`）。在有向的非空序（`ℕ`、`ℝ` 都是）上，
`atTop` 的成员**正是**含有某条尾巴的集合（`mem_atTop_sets`），所以「大集合」就是「含有一条尾巴的集合」。
一般的预序没有这个刻画，下面第二个例子说明 `atTop` 非平凡恰好要求序有向且非空。
**neighborhood filter（邻域滤子）`𝓝 x`**：`x` 的所有邻域，即包含某个含 `x` 的开集的集合
（开集是拓扑空间的基本概念，`Continuous` 也靠它定义，见 §11）。记号 `𝓝` 是 `open scoped Topology`
带来的（已在上面 `section Main` 开头打开；`𝓝 x` 就是 `nhds x`），`𝓟` 同样是 `Filter` 命名空间里的
scoped 记号，需要 `open Filter`（`Mathlib/Order/Filter/Defs.lean` 里的 `scoped notation "𝓟"`）。
-/

example : (atTop : Filter ℕ) = ⨅ a, 𝓟 (Set.Ici a) := rfl
example [Preorder α] : NeBot (atTop : Filter α) ↔ Nonempty α ∧ IsDirectedOrder α := atTop_neBot_iff
example (s t : Set ℕ) : s ∈ 𝓟 t ↔ t ⊆ s := mem_principal
example (s : Set ℕ) : s ∈ (atTop : Filter ℕ) ↔ ∃ a, ∀ b ≥ a, b ∈ s := mem_atTop_sets
example (s : Set ℝ) (x : ℝ) : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t := mem_nhds_iff
example : {n : ℕ | 5 ≤ n} ∈ (atTop : Filter ℕ) := mem_atTop 5
example (x : ℝ) : 𝓝 x = nhds x := rfl
example (x : ℝ) : Set.Ioo (x - 1) (x + 1) ∈ 𝓝 x := Ioo_mem_nhds (by linarith) (by linarith)
example (U : Set ℝ) (hU : IsOpen U) (x : ℝ) (hx : x ∈ U) : U ∈ 𝓝 x := hU.mem_nhds hx

/-!
在度量空间里，`𝓝 x` 的成员正是包含某个开球的集合（`Metric.ball x ε` 是中心 `x`、半径 `ε` 的开球）：
-/

example (s : Set ℝ) (x : ℝ) : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s := Metric.mem_nhds_iff

/-!
**滤子的序。** `F ≤ G` 的定义是「`G` 的每个成员都是 `F` 的成员」，是集合族的**反向**包含：滤子越小，
成员越多，对应的「条件」越强。`𝓝 x ≤ 𝓟 s` 读作「`s` 是 `x` 的邻域」，而 `atTop ≤ 𝓟 (Set.Ici 5)` 读作
「`n` 足够大时 `n ≥ 5`」。`le_principal_iff : F ≤ 𝓟 s ↔ s ∈ F` 在两种说法之间转换：
-/

example (F G : Filter α) : F ≤ G ↔ ∀ s ∈ G, s ∈ F := le_def
example (x : ℝ) : 𝓝 x ≤ 𝓟 (Set.Ioo (x - 1) (x + 1)) :=
  le_principal_iff.2 (Ioo_mem_nhds (by linarith) (by linarith))
example : (atTop : Filter ℕ) ≤ 𝓟 (Set.Ici 5) := le_principal_iff.2 (mem_atTop 5)

/-!
## 3. 最终成立 `∀ᶠ` 与 `filter_upwards`

`∀ᶠ x in l, p x`（eventually，最终成立；读作「沿 `l` 最终成立」）的**定义**就是 `{x | p x} ∈ l`；
所以它和「成员关系」是同一件事（`Iff.rfl`）。对 `ℕ` 这样有向的序上的 `atTop`，它展开成熟悉的量词结构
`∃ N, ∀ n ≥ N, p n`（`Filter.eventually_atTop`）。记号 `∀ᶠ` 是全局的，`atTop` 与 `Tendsto` 等名字
需要 `open Filter`（见「常见错误」）。
-/

example (p : ℕ → Prop) : (∀ᶠ n in atTop, p n) ↔ {n | p n} ∈ atTop := Iff.rfl
example (p : ℕ → Prop) : (∀ᶠ n in atTop, p n) ↔ ∃ N, ∀ n ≥ N, p n := eventually_atTop
example : ∀ᶠ n : ℕ in atTop, 10 ≤ n := eventually_ge_atTop 10

/-!
最终成立对合取、蕴涵封闭，这正是滤子的公理换了个说法：`Eventually.and` 合并两个、`Eventually.mono` 沿蕴涵
弱化、`Eventually.of_forall` 把处处成立的命题送进来（旧名 `eventually_of_forall` 已经消失，见「常见错误」）：
-/

example (p q : ℕ → Prop) (hp : ∀ᶠ n in atTop, p n) (hq : ∀ᶠ n in atTop, q n) :
    ∀ᶠ n in atTop, p n ∧ q n := hp.and hq
example (p q : ℕ → Prop) (hp : ∀ᶠ n in atTop, p n) (h : ∀ n, p n → q n) : ∀ᶠ n in atTop, q n :=
  hp.mono h
example (p : ℕ → Prop) (h : ∀ n, p n) : ∀ᶠ n in atTop, p n := Eventually.of_forall h

/-!
手写这些合并很快就繁琐了，策略 `filter_upwards [h₁, …, hₙ] with x hx₁ … hxₙ` 一次完成：它把目标
`∀ᶠ x in l, q x` 换成「对任意 `x`，若 `h₁ … hₙ` 在 `x` 处成立则 `q x`」，并 `intro` 这些假设。
下面的例子里 `u n` 最终落在 `[1, 2]`，所以最终离 `3 / 2` 不超过 `1 / 2`：
-/

example (u : ℕ → ℝ) (h1 : ∀ᶠ n in atTop, 1 ≤ u n) (h2 : ∀ᶠ n in atTop, u n ≤ 2) :
    ∀ᶠ n in atTop, |u n - 3 / 2| ≤ 1 / 2 := by
  filter_upwards [h1, h2] with n hn1 hn2
  -- n : ℕ, hn1 : 1 ≤ u n, hn2 : u n ≤ 2 ⊢ |u n - 3 / 2| ≤ 1 / 2
  rw [abs_le]
  constructor <;> linarith

-- 只有一个来源时也可以；`eventually_ge_atTop N` 是把「n ≥ N」送进来的标准做法
example : ∀ᶠ n : ℕ in atTop, 9 ≤ n ^ 2 := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  nlinarith

/-!
## 4. `Tendsto`：把滤子推过函数

`Tendsto f l₁ l₂`（`f` 沿 `l₁` 趋于 `l₂`）的定义是 `map f l₁ ≤ l₂`。`Filter.map f l₁` 是 `l₁` 的
push-forward（前推）：`t ∈ map f l₁ ↔ f ⁻¹' t ∈ l₁`。展开后：对 `l₂` 里的每个大集合 `s`，`f ⁻¹' s` 是
`l₁` 里的大集合。下面第一个例子是 `map` 的定义，第二、三个是 `Tendsto` 的两种展开，第四个 `h.eventually`
把 `l₂` 上的「最终成立」沿 `f` 拉回 `l₁`，是 `Tendsto` 最常见的用法：
-/

example (f : α → β) (l₁ : Filter α) (t : Set β) : t ∈ map f l₁ ↔ f ⁻¹' t ∈ l₁ := Iff.rfl
example (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Tendsto f l₁ l₂ ↔ map f l₁ ≤ l₂ := Iff.rfl
example (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ := tendsto_def
example (f : α → β) (l₁ : Filter α) (l₂ : Filter β) (h : Tendsto f l₁ l₂) (p : β → Prop)
    (hp : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, p (f x) := h.eventually hp

/-!
同一个 `Tendsto` 覆盖三种「极限」：下面依次是 `n → ∞` 时 `2n → ∞`、数列极限、点处的函数极限
（后者的证明用到 §11 的 `Continuous.tendsto` 与 `fun_prop`，这里先当作黑盒）。第一个用
`tendsto_atTop_atTop` 展开成「∀ b, ∃ i, ∀ a ≥ i, b ≤ f a」：
-/

example : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
  rw [tendsto_atTop_atTop]
  -- ⊢ ∀ (b : ℕ), ∃ i, ∀ (a : ℕ), i ≤ a → b ≤ 2 * a
  intro b
  -- b : ℕ ⊢ ∃ i, ∀ (a : ℕ), i ≤ a → b ≤ 2 * a
  exact ⟨b, fun a ha ↦ by omega⟩

example : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

example : Tendsto (fun x : ℝ ↦ 2 * x) (𝓝 1) (𝓝 2) := by
  have h : Continuous (fun x : ℝ ↦ 2 * x) := by fun_prop
  simpa using h.tendsto 1

/-!
## 5. ε–N 与 `Tendsto` 互译

metric space（度量空间）里 `𝓝 a` 的成员就是含开球的集合，所以 `Tendsto u atTop (𝓝 a)` 展开后恰好是
ε–N 的量词结构。这座桥是 `Metric.tendsto_atTop`（下标集需要有向且非空，`ℕ` 满足）：

`Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε`

在 `ℝ` 上 `dist x y = |x - y|`（引理名 `Real.dist_eq`，它的证明就是 `rfl`）。我们先用它从头证 `1 / n → 0`：
用 `exists_nat_gt`（第 11 章）由 `ε` 选出 `N > 1 / ε`。
-/

example (x y : ℝ) : dist x y = |x - y| := rfl

theorem tendsto_inv_nat_by_hand : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)         -- hN : 1 / ε < ↑N
  refine ⟨N, fun n hn ↦ ?_⟩                       -- hn : n ≥ N ⊢ dist (1 / ↑n) 0 < ε
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hNpos hNn
  rw [Real.dist_eq, sub_zero, abs_of_pos (one_div_pos.2 hnpos), div_lt_iff₀ hnpos]
  rw [div_lt_iff₀ hε] at hN                       -- hN : 1 < ↑N * ε
  nlinarith

/-!
同一个命题，库里是一行：`tendsto_one_div_atTop_nhds_zero_nat`（它的泛型形式要求 `𝕜` 是特征为零、带拓扑的
除半环，并且 `ℚ≥0` 连续作用于它，`ℝ` 满足；这里 `𝕜 = ℝ` 由期望类型推出）：
-/

theorem tendsto_inv_nat_by_library : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

/-!
**反方向**：已知 `Tendsto`，用 `Metric.tendsto_atTop.1 h ε hε` 取出具体的 `N`。例如收敛的数列最终离极限不到 1：
-/

example (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) : ∃ N : ℕ, ∀ n ≥ N, |u n - a| < 1 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h 1 one_pos
  refine ⟨N, fun n hn ↦ ?_⟩
  have := hN n hn                                 -- dist (u n) a < 1
  rwa [Real.dist_eq] at this

/-!
`∀ε, ∃N` 也可以写成「对每个 ε，`∀ᶠ n`」——这是 `Metric.tendsto_nhds` 的形式，它对任意滤子 `l`
（和任意定义域 `α`）都成立，不限于 `atTop`；`Metric.tendsto_atTop` 与「`l = atTop` 时再用
`eventually_atTop` 展开它」等价：
-/

example (l : Filter α) (u : α → ℝ) (a : ℝ) :
    Tendsto u l (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in l, dist (u x) a < ε := Metric.tendsto_nhds

/-!
## 6. 极限的代数与唯一性

加、乘、数乘、除以常数、乘方都是 `Tendsto` 的方法；它们把「两个 `∀ᶠ` 合并」的工作收进库里（§3）。
`tendsto_const_nhds` 的常数是**隐式**参数（显式传入的后果见「常见错误」3）；`Tendsto.add` 的结论是
`𝓝 (a + b)`，所以要按需 `simpa` 把极限值化简成目标里写的形状。除以一个变量用 `Tendsto.div`，
它多要一个条件：分母的极限 `b ≠ 0`（最后一个例子）：
-/

example (a b : ℝ) (u v : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n ↦ u n * v n + 1) atTop (𝓝 (a * b + 1)) :=
  (hu.mul hv).add tendsto_const_nhds

example (a : ℝ) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n ↦ u n / 2) atTop (𝓝 (a / 2)) := hu.div_const 2

example (a : ℝ) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n ↦ u n ^ 2) atTop (𝓝 (a ^ 2)) := hu.pow 2

example : Tendsto (fun n : ℕ ↦ 3 * (1 / ((n : ℝ) + 1)) + 2) atTop (𝓝 2) := by
  have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3).add_const 2
  simpa using h                                  -- h 的极限是 3 * 0 + 2

example (u v : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (hb : b ≠ 0) : Tendsto (fun n ↦ u n / v n) atTop (𝓝 (a / b)) := hu.div hv hb

/-!
**唯一性**：在 Hausdorff 空间里（`ℝ` 是），同一个数列沿非平凡滤子至多有一个极限。
`tendsto_nhds_unique` 是「把某个未知的 `a` 钉死」的标准工具：
-/

example (u : ℕ → ℝ) (a b : ℝ) (ha : Tendsto u atTop (𝓝 a)) (hb : Tendsto u atTop (𝓝 b)) :
    a = b := tendsto_nhds_unique ha hb

example (a : ℝ) (h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 a)) : a = 0 :=
  tendsto_nhds_unique h tendsto_one_div_add_atTop_nhds_zero_nat

/-!
## 7. 夹逼、复合与常用序列

**夹逼**：`tendsto_of_tendsto_of_tendsto_of_le_of_le`，参数依次是下界的极限、上界的极限、`g ≤ f`、`f ≤ h`
（`≤` 是函数的逐点序，所以用 `fun n ↦ …` 提供）。下面夹出 `1 / (n + 1)² → 0`；
两个 `?_` 目标是逐点的 `0 ≤ 1 / (n + 1)²` 与 `1 / (n + 1)² ≤ 1 / (n + 1)`，用 `show` 把函数应用展开：
-/

theorem tendsto_one_div_succ_sq : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n ↦ ?_) (fun n ↦ ?_)
  -- 两个目标（n : ℕ）：「下界 n ≤ f n」与「f n ≤ 上界 n」，下面用 `show` 写成具体形状
  · show (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) ^ 2
    positivity
  · show 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

/-!
带撇的 `tendsto_of_tendsto_of_tendsto_of_le_of_le'` 只要求两个不等式**最终**成立（`∀ᶠ`），
可以用 `filter_upwards` 提供：
-/

example (u : ℕ → ℝ) (h : ∀ n ≥ 5, 0 ≤ u n ∧ u n ≤ 1 / ((n : ℝ) + 1)) : Tendsto u atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat
    (by filter_upwards [eventually_ge_atTop 5] with n hn using (h n hn).1)
    (by filter_upwards [eventually_ge_atTop 5] with n hn using (h n hn).2)

/-!
**复合**：`Tendsto.comp : Tendsto g y z → Tendsto f x y → Tendsto (g ∘ f) x z`。把
`r ↦ r⁻¹ : atTop → 𝓝 0` 与 `Nat.cast : atTop → atTop` 复合，得到 `(n : ℝ)⁻¹ → 0`。

**极限保持非严格不等式**（`ℝ` 的序拓扑是闭序，`OrderClosedTopology`）：`le_of_tendsto'` 说若数列
处处 `≤ b`，则极限 `≤ b`（`ge_of_tendsto'` 是对偶）。**严格不等式不被保持**：`1 / (n + 1)` 处处 `> 0`，
极限却是 `0`，最后一个例子把这三件事放在一起：
-/

example : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

example (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) (hu : ∀ n, u n ≤ 0) : a ≤ 0 :=
  le_of_tendsto' h hu

example (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) (hu : ∀ n, 1 ≤ u n) : 1 ≤ a :=
  ge_of_tendsto' h hu

example : (∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1)) ∧
    Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) ∧ ¬ ((0 : ℝ) < 0) :=
  ⟨fun n ↦ by positivity, tendsto_one_div_add_atTop_nhds_zero_nat, lt_irrefl 0⟩

/-!
**常用序列**：几何数列、`C / n`、倒数在无穷处、自然数本身趋于无穷。这些名字的读法是
「函数 + 滤子 + 极限」：`tendsto_const_div_atTop_nhds_zero_nat` 读作「`C / n` 沿 `atTop` 趋于 `𝓝 0`，
`n` 是自然数（`_nat`）」；找这类引理的方法见第 9 章：
-/

example : Tendsto (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
example (C : ℝ) : Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat C
example : Tendsto (fun r : ℝ ↦ r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
example : Tendsto ((↑) : ℕ → ℝ) atTop atTop := tendsto_natCast_atTop_atTop

/-!
## 8. 单调收敛与 `limsup`/`liminf`

monotone convergence theorem（单调收敛定理）让你不知道极限值也能断言收敛。它在 Mathlib 里是
`tendsto_atTop_ciSup`（根命名空间，没有 `Monotone.` 别名）：单调且有上界的序列收敛到它的
supremum（上确界）`⨆ i, u i`。`Monotone.ge_of_tendsto` 说每一项都不超过极限：
-/

theorem exists_limit_of_monotone_bdd (u : ℕ → ℝ) (B : ℝ) (hm : Monotone u) (hb : ∀ n, u n ≤ B) :
    ∃ L, Tendsto u atTop (𝓝 L) :=
  -- BddAbove (Set.range u) 展开后是 ∃ B, B ∈ upperBounds (Set.range u)；这里用 ⟨B, …⟩ 给出
  ⟨⨆ n, u n, tendsto_atTop_ciSup hm ⟨B, by rintro _ ⟨n, rfl⟩; exact hb n⟩⟩

example (u : ℕ → ℝ) (a : ℝ) (hm : Monotone u) (h : Tendsto u atTop (𝓝 a)) (n : ℕ) : u n ≤ a :=
  hm.ge_of_tendsto h n

-- 具体一例：`1 - (1 / 2) ^ n` 单调有界，所以收敛
example : ∃ L, Tendsto (fun n : ℕ ↦ 1 - ((1 : ℝ) / 2) ^ n) atTop (𝓝 L) := by
  refine exists_limit_of_monotone_bdd _ 1 (monotone_nat_of_le_succ fun n ↦ ?_) fun n ↦ ?_
  · have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
    rw [pow_succ]
    linarith
  · have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n
    linarith

/-!
limsup / liminf（上极限 / 下极限）：`limsup u f` 的定义是 `limsSup (map u f)`，而 `limsSup f` 是集合
`{a | ∀ᶠ n in f, n ≤ a}`（所有「最终被 `a` 上界」的 `a`）的下确界（`liminf` 对偶）；
**参数顺序是函数在前、滤子在后**。在 complete lattice（完备格）里它们总有意义，例如 `EReal`
（扩展实数 `[-∞, +∞]`）和 `ℝ≥0∞`（扩展非负实数，记号需要 `open scoped ENNReal`）；
在完备格里对数列还有熟悉的公式 `limsup u atTop = ⨅ n, ⨆ i ≥ n, u i`。
-/

example (f : Filter EReal) : limsSup f = sInf {a | ∀ᶠ n in f, n ≤ a} := rfl
example (u : ℕ → EReal) : limsup u atTop = limsSup (map u atTop) := rfl
example (u : ℕ → EReal) : limsup u atTop = ⨅ n : ℕ, ⨆ i ≥ n, u i := limsup_eq_iInf_iSup_of_nat
example (u : ℕ → EReal) (a : EReal) (h : ∀ᶠ n in atTop, u n ≤ a) : limsup u atTop ≤ a :=
  limsup_le_of_le (h := h)
example (u : ℕ → EReal) : liminf u atTop ≤ limsup u atTop := liminf_le_limsup

/-!
`ℝ` 不是完备格（`⨆`/`⨅` 对无界族取垃圾值），所以在 `ℝ` 里 `limsup_le_of_le` 的边界假设
（`IsCoboundedUnder`）不会自动成立，要手工给出：下面用 `isCoboundedUnder_le_of_le` 提供一个下界。
另一种办法是把实数嵌进 `EReal` 或 `ℝ≥0∞` 再做（见「常见错误」5）。收敛数列的上、下极限等于极限。
先看垃圾值（无上界的集合，`sSup` 取 `0`）：
-/

example (s : Set ℝ) (h : ¬ BddAbove s) : sSup s = 0 := by
  rw [csSup_of_not_bddAbove h, Real.sSup_empty]

example (u : ℕ → ℝ) (hl : ∀ n, 0 ≤ u n) (h : ∀ᶠ n in atTop, u n ≤ 1) : limsup u atTop ≤ 1 :=
  limsup_le_of_le (isCoboundedUnder_le_of_le atTop hl) h

example (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) : limsup u atTop = a := h.limsup_eq
example (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) : liminf u atTop = a := h.liminf_eq

/-!
## 9. 级数：`HasSum`、`Summable`、`tsum`

`HasSum f a` 表示「`f` 的**无条件**求和等于 `a`」（对有限子集的部分和沿有限子集的滤子取极限）。
它还有第三个参数 `L : SummationFilter`，默认是 `unconditional`，所以 `#check` 与报错里会看到它。
`Summable f`（summable，可和）是 `∃ a, HasSum f a`；`∑' n, f n`（`tsum`，无穷和）是在可和时取这个值的
函数（在 `ℝ` 这类 Hausdorff 空间里和唯一）。三者的联系：`HasSum.tsum_eq`、`HasSum.summable`、
`Summable.hasSum`。注意 `ℝ` 上无条件可和等价于绝对可和（`summable_abs_iff`，第一个例子），所以交错级数
`∑ (-1)ⁿ / (n + 1)` **不是** `Summable`（`Mathlib/Topology/Algebra/InfiniteSum/Defs.lean` 里
`HasSum` 的文档注释举了这个例子）。几何级数库里现成：
-/

example (f : ℕ → ℝ) : Summable f ↔ Summable (fun n ↦ |f n|) := summable_abs_iff.symm


example : HasSum (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) 2 := hasSum_geometric_two
example : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := hasSum_geometric_two.tsum_eq
example (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_lt_one h0 h1
example (f : ℕ → ℝ) (a : ℝ) (h : HasSum f a) : Summable f := h.summable
example (f : ℕ → ℝ) (a : ℝ) :
    HasSum f a ↔ Tendsto (fun s : Finset ℕ ↦ ∑ i ∈ s, f i) atTop (𝓝 a) := Iff.rfl

/-!
非负项级数的 `HasSum` 等价于部分和序列收敛（`hasSum_iff_tendsto_nat_of_nonneg`）；一般的可和族
推出部分和收敛（`HasSum.tendsto_sum_nat`）。`Summable.of_nonneg_of_le` 是比较判别法。下面证
`(1/2)^n / (n+1)` 可和：
-/

example (f : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i) (r : ℝ) :
    HasSum f r ↔ Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i) atTop (𝓝 r) :=
  hasSum_iff_tendsto_nat_of_nonneg hf r

example (f : ℕ → ℝ) (a : ℝ) (h : HasSum f a) :
    Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i) atTop (𝓝 a) := h.tendsto_sum_nat

example : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n / ((n : ℝ) + 1)) := by
  have hg : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hg
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact div_le_self (by positivity) (by linarith)

/-!
**junk value（垃圾值）**：`tsum` 对不可和的族取 `0`（`tsum_eq_zero_of_not_summable`）。常数 `1` 的级数
发散，它的「无穷和」却是 `0`：所以把 `∑'` 当作普通求和来变形时，通常要先确认可和性。
-/

theorem not_summable_one : ¬ Summable (fun _ : ℕ ↦ (1 : ℝ)) :=
  fun h ↦ one_ne_zero ((summable_const_iff (1 : ℝ)).1 h)

example : ∑' _ : ℕ, (1 : ℝ) = 0 := tsum_eq_zero_of_not_summable not_summable_one

/-!
## 10. 渐近记号与 `IsBigO`

比较增长速度是分析里的常规操作（Stirling 公式、尾界估计都会用到），Mathlib 同样把它写成滤子语言。
`f =O[l] g` 读作「沿 `l`，`f` 是 `g` 的大 O」，定义是 `∃ c, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖`；
`f =o[l] g` 是小 o：对**每个** `c > 0` 最终有 `‖f x‖ ≤ c * ‖g x‖`。它们依然是滤子语言（`∀ᶠ`）。
记号 `=O[l]`、`=o[l]` 是全局的，不像 `𝓝` 那样需要 `open scoped`：本章没有 `open Asymptotics`，
下面的例子照样能用。
-/

example (f g : ℕ → ℝ) :
    f =O[atTop] g ↔ ∃ c : ℝ, ∀ᶠ n in atTop, ‖f n‖ ≤ c * ‖g n‖ := Asymptotics.isBigO_iff

example (f g : ℕ → ℝ) :
    f =o[atTop] g ↔ ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ‖f n‖ ≤ c * ‖g n‖ := Asymptotics.isLittleO_iff

-- `2n + 1 = O(n)`：常数取 3，对 `n ≥ 1` 有 `2n + 1 ≤ 3n`
example : (fun n : ℕ ↦ (2 * n + 1 : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 3 ?_
  -- ⊢ ∀ᶠ x in atTop, ‖2 * ↑x + 1‖ ≤ 3 * ‖↑x‖
  filter_upwards [eventually_ge_atTop 1] with n hn
  -- n : ℕ, hn : 1 ≤ n ⊢ ‖2 * ↑n + 1‖ ≤ 3 * ‖↑n‖
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * n + 1),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
  linarith

-- 库里的现成结论：多项式是指数函数的小 o
example : (fun x : ℝ ↦ x ^ 3) =o[atTop] Real.exp := Real.isLittleO_pow_exp_atTop

/-!
## 11. 连续性与开集的最小集合

开集是拓扑空间的基本概念：拓扑就是一族满足公理的开集。`𝓝 x` 的定义（§2）用到它，**连续**也靠它：
`Continuous f` 的定义是「开集的原像是开集」（`continuous_def`，原像见第 7 章）。度量空间里 `IsOpen U`
等价于「每个点周围有一个开球落在 `U` 里」，开球本身是开集；连续性有 ε–δ 形式 `Metric.continuous_iff`。
连续函数保极限：`hf.tendsto x : Tendsto f (𝓝 x) (𝓝 (f x))`（`hf : Continuous f`），
再用 `Tendsto.comp` 得到「连续函数复合收敛数列」。
-/

example (f : ℝ → ℝ) : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) := continuous_def

example (x ε y : ℝ) : y ∈ Metric.ball x ε ↔ dist y x < ε := Metric.mem_ball
example (x ε : ℝ) : IsOpen (Metric.ball x ε) := Metric.isOpen_ball
example (U : Set ℝ) : IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, Metric.ball x ε ⊆ U := Metric.isOpen_iff
example (f : ℝ → ℝ) : Continuous f ↔
    ∀ b : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ a : ℝ, dist a b < δ → dist (f a) (f b) < ε := Metric.continuous_iff

example (f : ℝ → ℝ) (hf : Continuous f) : IsOpen (f ⁻¹' Set.Ioo 0 1) :=
  hf.isOpen_preimage _ isOpen_Ioo

example (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n ↦ Real.exp (u n)) atTop (𝓝 (Real.exp a)) :=
  (Real.continuous_exp.tendsto a).comp h

/-!
证明具体函数连续，交给第 10 章的 `fun_prop` 或 `continuity`；
`isOpen_lt` 把两个连续函数的严格不等式变成开集：
-/

example : Continuous (fun x : ℝ ↦ Real.exp (x ^ 2) + 3) := by fun_prop
example : Continuous (fun x : ℝ ↦ x ^ 2 + 3 * x) := by continuity
example : IsOpen {x : ℝ | x ^ 2 < Real.exp x} := isOpen_lt (by fun_prop) (by fun_prop)

end Main

/-!
## 常见错误

**1. 忘记 `open Filter`。** `atTop`、`Tendsto` 等是 `Filter.atTop`、`Filter.Tendsto`，在 `open Filter`
之外是未知标识符（记号 `∀ᶠ` 是全局的，错误出在 `atTop`；`𝓟` 同理需要 `open Filter`，`𝓝` 需要
`open scoped Topology`）。下面的报错文本里提到 `autoImplicit`，是因为本书项目关闭了它（见第 1 章）：
-/

/--
error: Unknown identifier `atTop`

Note: It is not possible to treat `atTop` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
-/
#guard_msgs in
example : ∀ᶠ n : ℕ in atTop, 0 ≤ n := Filter.Eventually.of_forall (fun n ↦ n.zero_le)

/-!
**2. 旧名字：`eventually_of_forall`。** 在本书锁定的版本里它已经不存在，新名字是
`Filter.Eventually.of_forall`（用第 9 章的方法，`#check` 与 Loogle，找新名字）。
另一类错误不是改名而是放错命名空间：`Real.tendsto_inv_atTop_zero` 不存在，
只有根命名空间的 `tendsto_inv_atTop_zero`：
-/

/-- error: Unknown constant `Filter.eventually_of_forall` -/
#guard_msgs in
example : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ n := Filter.eventually_of_forall (fun n ↦ n.zero_le)

/-- error: Unknown constant `Real.tendsto_inv_atTop_zero` -/
#guard_msgs in
example : Filter.Tendsto (fun r : ℝ ↦ r⁻¹) Filter.atTop (nhds 0) := Real.tendsto_inv_atTop_zero

/-!
**3. 给 `tendsto_const_nhds` 传常数。** 常数是隐式参数（`{x : X}`）。`Tendsto` 展开后是一个函数
（`∀ ⦃s⦄, s ∈ 𝓝 x → …`），所以多写的 `2` 被当成了 `s ∈ 𝓝 x` 的证明，报错说期望的类型是命题，
而数字是数据。需要指定常数时用具名参数 `(x := 2)`：
-/

set_option pp.mvars false in
/--
error: numerals are data in Lean, but the expected type is a proposition
  ?_ ∈ nhds ?_ : Prop
-/
#guard_msgs in
example : Filter.Tendsto (fun _ : ℕ ↦ (2 : ℝ)) Filter.atTop (nhds 2) := tendsto_const_nhds 2

example : Filter.Tendsto (fun _ : ℕ ↦ (2 : ℝ)) Filter.atTop (nhds 2) := tendsto_const_nhds (x := 2)

/-!
**4. 把单调收敛当成 `Monotone` 的方法。** 没有 `Monotone.tendsto_atTop_ciSup`，要用根命名空间的
`tendsto_atTop_ciSup`，并且要同时提供 `BddAbove`。报错里出现 `Function.` 是因为 `Monotone` 展开后
是函数类型 `a ≤ b → f a ≤ f b`，点记号于是去 `Function` 命名空间找：
-/

set_option pp.mvars false in
/--
error: Invalid field `tendsto_atTop_ciSup`: The environment does not contain `Function.tendsto_atTop_ciSup`, so it is not possible to project the field `tendsto_atTop_ciSup` from an expression
  hm
of type `?_ ≤ ?_ → u ?_ ≤ u ?_`
-/
#guard_msgs in
example (u : ℕ → ℝ) (hm : Monotone u) (hb : BddAbove (Set.range u)) :
    Filter.Tendsto u Filter.atTop (nhds (⨆ n, u n)) := hm.tendsto_atTop_ciSup hb

/-!
**5. `limsup_le_of_le` 的第一个显式参数不是你想的那个。** 它的第一个显式参数是边界假设
`hf`（带默认值 `by isBoundedDefault`），「最终 `≤`」的假设排在第二位，所以位置参数 `h` 被塞进 `hf`；
要用具名参数 `(h := h)`（§8 的 `EReal` 例子）。在 `ℝ` 里 `hf` 的默认证明不会自动成立（第二条报错），
要像 §8 那样用 `isCoboundedUnder_le_of_le` 等手工给出：
-/

set_option pp.mvars false in
/--
error: Application type mismatch: The argument
  h
has type
  ∀ᶠ (n : ℕ) in Filter.atTop, u n ≤ 1
but is expected to have type
  autoParam (Filter.IsCoboundedUnder (fun x1 x2 ↦ x1 ≤ x2) ?_ ?_) Filter.limsup_le_of_le._auto_1
in the application
  Filter.limsup_le_of_le h
-/
#guard_msgs in
example (u : ℕ → ℝ) (h : ∀ᶠ n in Filter.atTop, u n ≤ 1) : Filter.limsup u Filter.atTop ≤ 1 :=
  Filter.limsup_le_of_le h

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: Tactic `assumption` failed

u : ℕ → ℝ
h : ∀ᶠ (n : ℕ) in Filter.atTop, u n ≤ 1
⊢ Filter.IsCoboundedUnder (fun x1 x2 ↦ x1 ≤ x2) Filter.atTop u
-/
#guard_msgs in
example (u : ℕ → ℝ) (h : ∀ᶠ n in Filter.atTop, u n ≤ 1) : Filter.limsup u Filter.atTop ≤ 1 :=
  Filter.limsup_le_of_le (h := h)

/-!
## 练习

练习 14.4、14.5、14.6、14.15 需要 ε–N 翻译（`Metric.tendsto_atTop`）；其中 14.4、14.5、14.6 和 14.9 回到
第 11 章的不等式；14.12 用第 6 章的归纳；14.14 用第 7 章的原像；14.15 是第 4 章的否定证明
（`intro h` 后找矛盾）。引理名在本章出现，或由题面的提示给出。
-/

section Exercises

open Filter
open scoped Topology

/-- 练习 14.1（★）：`3 / (n + 1) → 0`；用 `Tendsto.const_mul` 与
`tendsto_one_div_add_atTop_nhds_zero_nat`，再用 `simpa` 调整形状。 -/
theorem ex_14_1 : Tendsto (fun n : ℕ ↦ 3 / ((n : ℝ) + 1)) atTop (𝓝 0) := by sorry

/-- 练习 14.2（★）：最终 `4n ≤ n²`；用 `filter_upwards [eventually_ge_atTop 4] with n hn`，
再 `nlinarith`。 -/
theorem ex_14_2 : ∀ᶠ n : ℕ in atTop, 4 * n ≤ n ^ 2 := by sorry

/-- 练习 14.3（★）：若 `u → 1`，则 `u n` 最终大于 `1 / 2`；用 `Tendsto.eventually` 与 `lt_mem_nhds`。 -/
theorem ex_14_3 (u : ℕ → ℝ) (h : Tendsto u atTop (𝓝 1)) : ∀ᶠ n in atTop, 1 / 2 < u n := by
  sorry

/-- 练习 14.4（★★）：用 ε–N 证明 `(n + 1) / (n + 2) → 1`。取 `N > 1 / ε`；
先证 `(n + 1) / (n + 2) - 1 = -(1 / (n + 2))`（`field_simp`，`ring`）。 -/
theorem ex_14_4 : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / ((n : ℝ) + 2)) atTop (𝓝 1) := by sorry

/-- 练习 14.5（★）：从 `Tendsto` 取回 ε–N。收敛数列最终小于极限加一；用
`Metric.tendsto_atTop.1 h 1 one_pos`，再 `abs_lt`（第 11 章）。 -/
theorem ex_14_5 (u : ℕ → ℝ) (a : ℝ) (h : Tendsto u atTop (𝓝 a)) :
    ∃ N : ℕ, ∀ n ≥ N, u n < a + 1 := by sorry

/-- 练习 14.6（★★★）：不用 `Tendsto.add`，只用 `Metric.tendsto_atTop` 证明和的极限。
对 `ε / 2` 取两个 `N`，再取 `max`；用 `Real.dist_eq` 把距离化成绝对值，
再用 `abs_add_le`（第 11 章）。 -/
theorem ex_14_6 (u v : ℕ → ℝ) (a b : ℝ) (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b)) :
    Tendsto (fun n ↦ u n + v n) atTop (𝓝 (a + b)) := by sorry

/-- 练习 14.7（★★）：单调收敛。若 `u` 单调、`u 0 = 1` 且处处 `u n ≤ 3`，则 `u` 收敛到某个
`L ≥ 1`；用 `tendsto_atTop_ciSup` 与 `Monotone.ge_of_tendsto`。 -/
theorem ex_14_7 (u : ℕ → ℝ) (hm : Monotone u) (h0 : u 0 = 1) (hb : ∀ n, u n ≤ 3) :
    ∃ L : ℝ, 1 ≤ L ∧ Tendsto u atTop (𝓝 L) := by sorry

/-- 练习 14.8（★★）：严格不等式在极限下不被保持。前一半：若 `u n > 0` 处处成立且 `u → a`，则 `a ≥ 0`
（`ge_of_tendsto'`）；后一半：「则 `a > 0`」不成立，反例取 `1 / (n + 1)`。 -/
theorem ex_14_8 :
    (∀ (u : ℕ → ℝ) (a : ℝ), (∀ n, 0 < u n) → Tendsto u atTop (𝓝 a) → 0 ≤ a) ∧
    ¬ (∀ (u : ℕ → ℝ) (a : ℝ), (∀ n, 0 < u n) → Tendsto u atTop (𝓝 a) → 0 < a) := by
  sorry

/-- 练习 14.9（★★★）：夹逼。`0 ≤ n / (n² + 1) ≤ 1 / n`（对 `n = 0` 两边都是 `0`：先
`rcases Nat.eq_zero_or_pos n`，另一支用 `div_le_div_iff₀` 与 `nlinarith`），上界用
`tendsto_one_div_atTop_nhds_zero_nat`。 -/
theorem ex_14_9 : Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) ^ 2 + 1)) atTop (𝓝 0) := by sorry

/-- 练习 14.10（★★）：`n² = O(n³)`，即 `(fun n : ℕ ↦ (n : ℝ) ^ 2) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 3)`；
用 `Asymptotics.IsBigO.of_bound 1`、`filter_upwards [eventually_ge_atTop 1]`，
再用 `Real.norm_eq_abs` 与 `abs_of_nonneg` 去掉范数。 -/
theorem ex_14_10 : (fun n : ℕ ↦ (n : ℝ) ^ 2) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ 3) := by sorry

/-- 练习 14.11（★★）：比较判别法。`(1/3)^n * (1 + 1/(n+1)) ≤ 2 * (1/3)^n`；
用 `Summable.of_nonneg_of_le` 与 `Summable.mul_left`。 -/
theorem ex_14_11 : Summable (fun n : ℕ ↦ (1 / 3 : ℝ) ^ n * (1 + 1 / ((n : ℝ) + 1))) := by sorry

/-- 练习 14.12（★★）：对 `n` 归纳（第 6 章）证明递推数列的通项。 -/
theorem ex_14_12 (u : ℕ → ℝ) (h0 : u 0 = 0) (h : ∀ n, u (n + 1) = (u n + 1) / 2) (n : ℕ) :
    u n = 1 - (1 / 2) ^ n := by sorry

/-- 练习 14.13（★★★）：同一个递推数列收敛到 `1`。先用 14.12 得到通项，再用
`tendsto_pow_atTop_nhds_zero_of_lt_one`、`tendsto_const_nhds.sub` 与 `Tendsto.congr`。 -/
theorem ex_14_13 (u : ℕ → ℝ) (h0 : u 0 = 0) (h : ∀ n, u (n + 1) = (u n + 1) / 2) :
    Tendsto u atTop (𝓝 1) := by sorry

/-- 练习 14.14（★）：连续函数的非零点集是开集：`{x | f x ≠ 0}` 是开集；
用原像 `f ⁻¹' {y | y ≠ 0}`、`isOpen_ne` 与 `Continuous.isOpen_preimage`（`hf.isOpen_preimage`）。 -/
theorem ex_14_14 (f : ℝ → ℝ) (hf : Continuous f) : IsOpen {x : ℝ | f x ≠ 0} := by sorry

/-- 练习 14.15（★★★）：`n` 不趋于 `0`。用 `Metric.tendsto_atTop`，`intro h`，对 `ε = 1`
取出 `N`，在 `n = max N 1` 处得到矛盾；不要用 `tendsto_nhds_unique`。 -/
theorem ex_14_15 : ¬ Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop (𝓝 0) := by sorry

end Exercises

/-!
## 小结

| 概念 | 语法 / 名字 | 何时用 |
|---|---|---|
| 滤子 | `Filter α`；`s ∈ F`；`F ≤ G ↔ ∀ s ∈ G, s ∈ F` | 「大集合」的族；序是反向包含 |
| 三个标准滤子 | `atTop`、`𝓝 x`（`open scoped Topology`）、`𝓟 s` | 趋于无穷 / 靠近一点 / 限制在集合内 |
| 最终成立 | `∀ᶠ x in l, p x`；`eventually_atTop`；`Eventually.and/mono/of_forall` | 「足够大 / 足够近」的性质 |
| 合并与推导 | `filter_upwards [h₁, h₂] with x hx₁ hx₂` | 把多个 `∀ᶠ` 化为逐点推导 |
| 趋于 | `Tendsto f l₁ l₂`（`= map f l₁ ≤ l₂`）；`tendsto_def`；`Tendsto.eventually` | 所有类型的极限 |
| ε–N 互译 | `Metric.tendsto_atTop`、`Metric.tendsto_nhds`、`Real.dist_eq` | 手工证 / 取回显式的 `N` |
| 极限的代数 | `Tendsto.add/mul/const_mul/div_const/pow`、`tendsto_const_nhds`、`tendsto_nhds_unique` | 拼装已知极限 |
| 夹逼、复合、序 | `tendsto_of_tendsto_of_tendsto_of_le_of_le`（及带撇的）、`Tendsto.comp`、`le_of_tendsto'` | 估计与代换；只保持 `≤` |
| 常用序列 | `tendsto_pow_atTop_nhds_zero_of_lt_one`、`tendsto_const_div_atTop_nhds_zero_nat`、`tendsto_inv_atTop_zero`、`tendsto_natCast_atTop_atTop` | 直接引用 |
| 单调收敛 | `tendsto_atTop_ciSup`、`Monotone.ge_of_tendsto` | 单调有界序列 |
| 上 / 下极限 | `limsup u l`、`liminf u l`、`limsup_le_of_le`、`Tendsto.limsup_eq` | 完备格里无条件；`ℝ` 要边界条件 |
| 级数 | `HasSum`、`Summable`、`∑'`、`summable_abs_iff`、`hasSum_geometric_of_lt_one`、`Summable.of_nonneg_of_le` | 不可和时 `∑' = 0`；`ℝ` 上可和即绝对可和 |
| 渐近 | `f =O[l] g`、`f =o[l] g`；`Asymptotics.isBigO_iff` | 增长速度比较 |
| 拓扑最小集 | `IsOpen`、`Metric.ball`、`continuous_def`、`Continuous.tendsto`、`fun_prop`、`isOpen_lt` | 连续性与开集 |
-/

/-!
## 延伸阅读

- Mathlib 源码：`Mathlib/Order/Filter/Defs.lean`（`Filter`、`Eventually`、`Tendsto`、`filter_upwards`
  的文档注释）、`Mathlib/Order/Filter/AtTopBot/Defs.lean`（`atTop`）、
  `Mathlib/Topology/Defs/Filter.lean`（`nhds`）。
- ε–N 之桥：`Mathlib/Topology/MetricSpace/Pseudo/Defs.lean` 中的 `Metric.tendsto_atTop`；常用序列极限：
  `Mathlib/Analysis/SpecificLimits/Basic.lean`；
  单调收敛：`Mathlib/Topology/Order/MonotoneConvergence.lean`。
- `limsup`/`liminf`：`Mathlib/Order/LiminfLimsup.lean`；渐近记号：`Mathlib/Analysis/Asymptotics/Defs.lean`；
  级数：`Mathlib/Topology/Algebra/InfiniteSum/Defs.lean`。
- Mathematics in Lean（《Lean 形式化数学》）Topology 一章的 *Filters* 一节：以 `atTop`、`𝓝 x`、`𝓟 s` 等为例引入
  滤子，给出 `Tendsto` 的显式量词形式与 `map f F ≤ G` 的改写（网页版 `C11_Topology.html`）。
- 本书第 9 章（找引理）、第 10 章（`fun_prop`/`continuity`）、第 11 章（ε–N 用的不等式）、第 16 章（`ae` 是测度
  空间上的又一个滤子）、第 22 章（大偏差入门）。
-/

end Lean4Learn.Ch14

end
