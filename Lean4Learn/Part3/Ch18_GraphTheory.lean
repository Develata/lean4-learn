module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.Hall
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
public import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!
# 第 18 章　图论

随机图与概率方法最终都要落到「数一个图里的某种东西」上：edge（边）、degree（度）、三角形、
connected component（连通分量）、coloring（着色）。本章用 Mathlib 的 `SimpleGraph` 备齐这些词汇：
怎样定义一个图、怎样让 Lean 能数它的边和度、handshaking lemma（握手引理）怎样用、walk（途径）与
connected（连通）是什么类型的对象、clique（团）和着色怎样表达，最后用 Turán's theorem（图兰定理）、
Hall's marriage theorem（霍尔婚配定理）、regularity lemma（正则性引理，即 Szemerédi 正则性引理）三个
大定理看 Mathlib 的图论陈述长什么样。读完后你能读懂 `Mathlib/Combinatorics/SimpleGraph/` 里的陈述，
处理它最常见的麻烦（`Decidable` 实例，decidable（可判定）见第 6 章），并对 vertex（顶点）不多的
具体图用 `decide` 直接核算（本章的示例用 `decide` 算到 6 个顶点、`decide +kernel` 算到 8 个，§13）。

## 学习目标
- 会手写一个图（`Adj` 加对称、无自环两个证明，或让 `aesop_graph` 自动补上），会用 `⊥`、`⊤`、`fromRel`、
  `fromEdgeSet` 造图。
- 区分 `edgeSet : Set (Sym2 V)` 与 `edgeFinset : Finset (Sym2 V)`，会写 `s(a, b)`，知道 `edgeFinset`、
  `neighborFinset`、`degree` 需要哪些实例，缺实例时报什么错、怎样修。
- 会用握手引理 `sum_degrees_eq_twice_card_edges` 与 `even_card_odd_degree_vertices` 做计数并推出新的推论。
- 知道 `Walk` 是归纳类型（不是命题），会读 `length`、`support`、`IsPath`、`IsTrail`，会用 `Reachable`、
  `Connected`、`IsAcyclic`、`IsTree` 与 `IsTree.card_edgeFinset`。
- 会用 `IsNClique`、`CliqueFree`、`cliqueFinset`、`is3Clique_triple_iff` 数三角形，会用 `Coloring`、
  `Colorable`、`chromaticNumber` 给出并验证着色，认识 `induce`、`Subgraph`、`→g`、`↪g`、`≃g`。
- 会用 `decide` 核对小图的命题，会读图兰、霍尔、正则性这三个定理的陈述，会在 `SimpleGraph` 目录里找引理。

## 前置知识
第 2 章（`ℕ` 的截断减法）；第 4–5 章（反证、`push Not`、`decide`）；第 6 章（结构体、归纳类型、
`Decidable`）；第 7 章（子类型、`Nonempty`）；第 8 章（格、实例隐式参数、`classical`）；第 9 章
（`exact?`）；第 10 章（`aesop`）；第 12 章（`Finset`、`#s`、双重计数、`Nat.choose`、小情形 `decide`）；
第 13 章（`convert`）；第 15 章（打包映射与 `⇑f`，§12 的 `→g`、`≃g` 就是它们）。
-/

@[expose] public section

namespace Lean4Learn.Ch18

open scoped Finset -- 打开 `#s` 记号

/-!
## 1. `SimpleGraph V`：一个结构体

simple graph（简单图）是顶点集 `V` 上的一个对称、无自环的相邻关系。Mathlib 把它写成带三个字段的结构体
（第 6 章）：`Adj : V → V → Prop` 是 adjacent（相邻）关系，`symm` 说它对称，`loopless` 说它没有自环。
顶点就是 `V` 的元素；边不是单独存的数据，而是相邻的顶点对（§3）。

后两个字段的类型是 `Std.Symm Adj` 与 `Std.Irrefl Adj`，它们是核心库里的小结构体，各有一个字段
`symm`、`irrefl`，所以取出证明时要多写一层：`G.symm.symm u v h`、`G.loopless.irrefl v`。日常更常用的是
Mathlib 提供的引理 `Adj.symm`、`Adj.ne`：
-/

example (V : Type) (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : G.Adj v u :=
  G.symm.symm u v h
example (V : Type) (G : SimpleGraph V) (v : V) : ¬ G.Adj v v := G.loopless.irrefl v
example (V : Type) (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : G.Adj v u := h.symm
example (V : Type) (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : u ≠ v := h.ne

/-!
**手写一个图。** 两个证明字段带有默认值 `by aesop_graph`（一个专为图论调过的 `aesop`，第 10 章）：只要
关系的对称性与无自环能被它自动证明，就可以只写 `Adj`。下面的星形图（`0` 与其余三点相连）就是这样：
-/

def star4 : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b ∧ (a = 0 ∨ b = 0)

/-!
自动证明失败时，`def` 报的是 `aesop` 的错误，指向缺的那个字段。`a < b` 不对称，无论如何都证不出：
-/

/--
error: could not synthesize default value for field 'symm' of 'SimpleGraph' using tactics
---
error: Tactic `aesop` failed, failed to prove the goal after exhaustive search.
Initial goal:
  ⊢ Std.Symm fun a b ↦ ↑a < ↑b
Remaining goals after safe rules:
  a b : Fin 4
  a_1 : a < b
  ⊢ b < a
-/
#guard_msgs in
example : SimpleGraph (Fin 4) where
  Adj a b := a.val < b.val

/-!
这时要自己提供证明。字段名是 `symm` 和 `loopless`，而它们的值是 `Std.Symm`、`Std.Irrefl` 的实例，在 `where`
块里写成 `symm.symm a b h := …` 和 `loopless.irrefl a := …`（Mathlib 自己的写法）。下面的 `square` 把
`0, 1, 2, 3` 中和为奇数的两点相连，得到 `0 - 1 - 2 - 3 - 0` 这个 4-圈（§13 证明它就是
`cycleGraph 4`）。证明里的 `have`/`show` 把目标里的 `Adj` 展开成具体的算术式，写出来让读者看清
`omega` 面对的是什么：
-/

def square : SimpleGraph (Fin 4) where
  Adj a b := (a.val + b.val) % 2 = 1
  symm.symm a b h := by
    have h' : (a.val + b.val) % 2 = 1 := h
    show (b.val + a.val) % 2 = 1
    omega
  loopless.irrefl a := by
    show ¬ (a.val + a.val) % 2 = 1
    omega

/-!
**`Adj` 是命题，不是布尔值。** 要让 `decide` 判断 `square.Adj 0 1`，需要 `Decidable` 实例（第 6 章）。
`square` 是普通 `def`，实例合成不会替你展开它，所以先看到找不到实例：
-/

/--
error: failed to synthesize
  Decidable (square.Adj 0 1)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
example : square.Adj 0 1 := by decide

/-!
补一个实例：用 `inferInstanceAs` 把 `Adj a b` 的展开式的实例（`Nat` 上的等式，自带）重新声明给
`square.Adj`。Mathlib 里的 `turanGraph`、`pathGraph` 也是这样写实例的（`cycleGraph` 的实例按 `n` 分情况，
写法不同，但同样能被 `decide` 规约，§13 用到）。此后 `decide` 可以核对任意具体的相邻关系：
-/

instance : DecidableRel square.Adj := fun a b ↦
  inferInstanceAs (Decidable ((a.val + b.val) % 2 = 1))

example : square.Adj 0 1 := by decide
example : ¬ square.Adj 0 2 := by decide
example : ∀ a b : Fin 4, square.Adj a b → square.Adj b a := by decide

/-!
## 2. 最小的图、最大的图与造图的方法

造图可以像 §1 那样逐字段手写，也可以从已有的图运算得到。`SimpleGraph V` 是 complete lattice（完备格；
格见第 8 章，完备格见第 14 章）：`G ≤ H` 表示 `G` 的每条边都在 `H` 里；最小元 `⊥` 是 edgeless graph
（空图，没有边），最大元 `⊤` 是 complete graph（完全图，所有不同顶点两两相邻）；`completeGraph V` 与
`emptyGraph V` 只是 `⊤`、`⊥` 的别名。并 `⊔` 与补 `Gᶜ` 也是图的运算：
-/

example (V : Type) (u v : V) : (⊤ : SimpleGraph V).Adj u v ↔ u ≠ v := SimpleGraph.top_adj u v
example (V : Type) (u v : V) : (⊥ : SimpleGraph V).Adj u v ↔ False := SimpleGraph.bot_adj u v
example (V : Type) : SimpleGraph.completeGraph V = ⊤ ∧ SimpleGraph.emptyGraph V = ⊥ := ⟨rfl, rfl⟩
example (V : Type) : CompleteLattice (SimpleGraph V) := inferInstance
example (V : Type) (G H : SimpleGraph V) : G ≤ H ↔ ∀ v w, G.Adj v w → H.Adj v w :=
  SimpleGraph.le_iff_adj
example (V : Type) (G H : SimpleGraph V) (u v : V) : (G ⊔ H).Adj u v ↔ G.Adj u v ∨ H.Adj u v :=
  SimpleGraph.sup_adj G H u v
example (V : Type) (G : SimpleGraph V) (u v : V) : Gᶜ.Adj u v ↔ u ≠ v ∧ ¬ G.Adj u v :=
  SimpleGraph.compl_adj G u v

/-!
`⊤` 与 `⊥` 的 `Adj` 是可判定的（`Top.adjDecidable` 需要 `DecidableEq V`），所以 `Fin n` 上直接 `decide`：
-/

example : (⊤ : SimpleGraph (Fin 4)).Adj 1 2 := by decide
example : ¬ (⊥ : SimpleGraph (Fin 4)).Adj 1 2 := by decide

/-!
**`fromRel`：任意关系变成图。** `SimpleGraph.fromRel r` 把关系 `r` 对称化并去掉自环，
`(fromRel r).Adj a b ↔ a ≠ b ∧ (r a b ∨ r b a)`（`fromRel_adj`）。不必证明任何东西，最适合快速造图。
它自带 `DecidableRel` 实例（要求 `r` 可判定、顶点类型有 `DecidableEq`）：
-/

example (V : Type) (r : V → V → Prop) (a b : V) :
    (SimpleGraph.fromRel r).Adj a b ↔ a ≠ b ∧ (r a b ∨ r b a) := SimpleGraph.fromRel_adj r a b
example : (SimpleGraph.fromRel fun a b : Fin 4 ↦ b = a + 1).Adj 3 0 := by decide

/-!
**`fromEdgeSet`：由边集造图。** `SimpleGraph.fromEdgeSet s` 的边是 `s` 里的无序对，但会丢掉自环
（`fromEdgeSet_adj : (fromEdgeSet s).Adj v w ↔ s(v, w) ∈ s ∧ v ≠ w`）。下面的 `paw` 是三角形 `{0, 1, 2}` 加上
一条挂在 `2` 上的悬挂边 `2 - 3`。这个图后面会反复用：
-/

def paw : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(1, 2), s(0, 2), s(2, 3)}

instance : DecidableRel paw.Adj := fun a b ↦
  inferInstanceAs (Decidable (s(a, b) ∈ ({s(0, 1), s(1, 2), s(0, 2), s(2, 3)} : Set (Sym2 (Fin 4)))
    ∧ a ≠ b))

example : paw.Adj 0 2 := by decide
example : ¬ paw.Adj 0 3 := by decide
example : ¬ (SimpleGraph.fromEdgeSet {s(0, 0)} : SimpleGraph (Fin 2)).Adj 0 0 := by simp

/-!
## 3. 边集与无序对 `Sym2`

边在 Mathlib 里是 unordered pair（无序对）。类型 `Sym2 V` 是 `V × V` 模去「交换两个分量」后的
quotient type（商类型，第 15 章 §7），无序对 `{a, b}` 写作 `s(a, b)`（全局记号，是 `Sym2.mk a b`；
注意 `Sym2.mk` 接两个参数，不是一个数对，见 §16）。`s(a, b) = s(b, a)` 由 `Sym2.eq_swap` 给出，
一般的相等判据是 `Sym2.eq_iff`：
-/

example (a b : ℕ) : s(a, b) = s(b, a) := Sym2.eq_swap
example (a b : ℕ) : s(a, b) = Sym2.mk a b := rfl
example (a b c d : ℕ) : s(a, b) = s(c, d) ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := Sym2.eq_iff

/-!
`G.edgeSet : Set (Sym2 V)` 是 `G` 的边集。它的成员判据 `mem_edgeSet` 是定义相等（`Iff.rfl`，第 5 章），
所以 `s(u, v) ∈ G.edgeSet` 与 `G.Adj u v` 在 Lean 眼里是同一个命题。`⊤` 的边集是「所有非对角的无序对」
`Sym2.diagSet` 的补，`fromEdgeSet G.edgeSet = G`：
-/

example (V : Type) (G : SimpleGraph V) (u v : V) : s(u, v) ∈ G.edgeSet ↔ G.Adj u v := Iff.rfl
example (V : Type) (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : s(v, u) ∈ G.edgeSet := by
  rw [Sym2.eq_swap]
  exact h
example (V : Type) : (⊤ : SimpleGraph V).edgeSet = Sym2.diagSetᶜ := SimpleGraph.edgeSet_top
example (V : Type) (G : SimpleGraph V) : SimpleGraph.fromEdgeSet G.edgeSet = G :=
  SimpleGraph.fromEdgeSet_edgeSet G
example : s(3, 2) ∈ paw.edgeSet := by decide

/-!
## 4. 有限图：`edgeFinset` 与实例的搭配

要数边，需要 `Finset`：`G.edgeFinset : Finset (Sym2 V)` 定义为 `Set.toFinset G.edgeSet`，所以它依赖
实例 `[Fintype G.edgeSet]`。这个实例由 `SimpleGraph.fintypeEdgeSet`（在 `Basic.lean`）给出，它要求
`[Fintype (Sym2 V)]`（来自 `[Fintype V]`）和 `[DecidableRel G.Adj]`。换句话说，数边需要三样东西：
`G`、`Fintype V`、`DecidableRel G.Adj`。用 `#synth` 可以看到实例合成走的是哪条路（`pp` 把
`SimpleGraph.fintypeEdgeSet paw` 显示成点记号）：
-/

/-- info: paw.fintypeEdgeSet -/
#guard_msgs in
#synth Fintype paw.edgeSet

example : paw.edgeFinset.card = 4 := by decide
example : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by decide

/-!
比如只有 `Fintype V` 而没有 `DecidableRel G.Adj`（对一般的 `G`，`G.Adj` 是任意的命题，Lean 不知道怎样判断它）：
-/

/--
error: failed to synthesize instance of type class
  Fintype ↑G.edgeSet

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (V : Type) [Fintype V] (G : SimpleGraph V) : ℕ := G.edgeFinset.card

/-!
三种修法（一般原则见第 12 章 §11）：(1) 把实例写进假设，由调用者提供；Mathlib 里度与握手一类的定理带
`[Fintype V] [DecidableRel G.Adj]`，数边的定理常常只要 `[Fintype G.edgeSet]`（如
`IsTree.card_edgeFinset`）。(2) 换成不需要实例的 `Set.ncard`（第 12 章 §10），它对有限图与
`edgeFinset` 的个数一致。(3) `open scoped Classical in` 加 `noncomputable` 定义（第 12 章 §11 的
方式 2）。经典实例与定理里的实例是不同的项，用 `convert`（第 13 章 §4）对齐：`convert rfl` 关上
实例目标，因为 `Fintype` 实例是 subsingleton（至多一个项，`Fintype.subsingleton`）：
-/

noncomputable example (V : Type) (G : SimpleGraph V) : ℕ := G.edgeSet.ncard

example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeSet.ncard = #G.edgeFinset := Set.ncard_eq_toFinset_card' _

open scoped Classical in
noncomputable def numEdges {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := #G.edgeFinset

example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    numEdges G = #G.edgeFinset := by
  unfold numEdges
  convert rfl

/-!
**完全图的边数。** `G` 有 `n` 个顶点时，`⊤` 的边数是 `n.choose 2`（第 12 章 §8）；任何图的边数都不会
超过它：
-/

example {V : Type*} [Fintype V] [DecidableEq V] :
    #(⊤ : SimpleGraph V).edgeFinset = (Fintype.card V).choose 2 :=
  SimpleGraph.card_edgeFinset_top_eq_card_choose_two
example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset ≤ (Fintype.card V).choose 2 :=
  SimpleGraph.card_edgeFinset_le_card_choose_two

/-!
## 5. 邻点与度

顶点 `v` 的 neighbor set（邻点集）是 `G.neighborSet v = {w | G.Adj v w}`（本书不叫它邻域，那个词留给
拓扑）。有限版本是 `G.neighborFinset v`，依赖 `[Fintype (G.neighborSet v)]`；度是它的
元素个数，`G.degree v := #(G.neighborFinset v)`，由定义相等直接成立：
-/

example (V : Type) (G : SimpleGraph V) (v w : V) : w ∈ G.neighborSet v ↔ G.Adj v w :=
  SimpleGraph.mem_neighborSet G v w
example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v w : V) :
    w ∈ G.neighborFinset v ↔ G.Adj v w :=
  SimpleGraph.mem_neighborFinset G v w
example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    #(G.neighborFinset v) = G.degree v := rfl

/-!
`Fintype (G.neighborSet v)` 由实例合成从 §4 的那两个实例得到（下面第一例）；具体的小图上全部可以 `decide`：
-/

example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype (G.neighborSet v) := inferInstance

example : paw.degree 2 = 3 := by decide
example : paw.neighborFinset 2 = {0, 1, 3} := by decide
example : ∀ v, square.degree v = 2 := by decide

/-!
`minDegree`、`maxDegree` 是全图的最小、最大度（需要 `Fintype V` 与 `DecidableRel G.Adj`）；
`IsRegularOfDegree d` 说每个顶点的度都是 `d`。完全图是 `(n - 1)`-正则的（`ℕ` 的截断减法，第 2 章）：
-/

example : paw.minDegree = 1 := by decide
example : paw.maxDegree = 3 := by decide
example {V : Type*} [Fintype V] [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) :=
  SimpleGraph.IsRegularOfDegree.top

/-!
## 6. 握手引理

握手引理：所有顶点的度之和等于边数的两倍，因为每条边被它的两个端点各数一次。Mathlib 的证明是
第 12 章 §6 双重计数的直接应用：`Dart`（带方向的边，即有序的相邻顶点对）的个数既等于度之和，又等于
边数的两倍。推论 `even_card_odd_degree_vertices`：度为奇数的顶点个数是偶数。`variable`（第 15 章 §8）
一次声明实例：
-/

section Handshake

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

example : ∑ v, G.degree v = 2 * #G.edgeFinset := G.sum_degrees_eq_twice_card_edges
example : Even #{v | Odd (G.degree v)} := G.even_card_odd_degree_vertices
example : Fintype.card G.Dart = ∑ v, G.degree v := G.dart_card_eq_sum_degrees
example : Fintype.card G.Dart = 2 * #G.edgeFinset := G.dart_card_eq_twice_card_edges

/-!
**推论 1：每个顶点的度都是奇数时，顶点数是偶数。** 把「度为奇数的顶点」那个过滤集化成全集：
-/

theorem even_card_of_forall_odd_degree (h : ∀ v, Odd (G.degree v)) : Even (Fintype.card V) := by
  have hfilter : ({v | Odd (G.degree v)} : Finset V) = Finset.univ :=
    Finset.filter_true_of_mem fun v _ ↦ h v
  have := G.even_card_odd_degree_vertices
  rwa [hfilter, Finset.card_univ] at this

end Handshake

/-!
## 7. 途径：`Walk` 是归纳类型

途径不是命题，而是数据：`G.Walk u v` 是从 `u` 到 `v` 的相邻顶点序列，定义为归纳类型（第 6 章），
有两个构造子：`nil`（长度 `0`，起点终点相同）和 `cons`（先走一条边，再走一个短一点的途径）。
`length` 是边数，`support` 是经过的顶点列表（`List V`）。它们都对 `Walk` 结构递归定义，所以小例子可以 `rfl`：
-/

def sqWalk : square.Walk 0 2 :=
  .cons (by decide : square.Adj 0 1) (.cons (by decide : square.Adj 1 2) .nil)

example : sqWalk.length = 2 := rfl
example : sqWalk.support = [0, 1, 2] := rfl
example : sqWalk.edges = [s(0, 1), s(1, 2)] := rfl

/-!
> **术语提示（撞词）。** 本书的「途径」是 `Walk`（顶点可以重复），「路径」是 `IsPath`（顶点不重复），
> 「迹」是 `IsTrail`（边不重复），「圈」是 `IsCycle`。其他图论教材这几个词可能互换（有的书把 `Walk` 叫
> 「路径」），读书时要先看定义。

`IsTrail`（trail，迹：边不重复）、`IsPath`（path，路径：顶点不重复）、`IsCircuit`（circuit，回路：
起点终点相同的非空迹）、`IsCycle`（cycle，圈：回路且除起点外顶点不重复）是 `Walk` 上的**谓词**。
它们是只带命题字段的结构体（第 6 章）：`IsTrail` 有字段 `edges_nodup`，`IsPath` 继承 `IsTrail` 并多一个
字段 `support_nodup`，所以 `IsPath` 的证明是 `⟨⟨edges_nodup⟩, support_nodup⟩`。对具体途径把字段交给
`decide`（`Nodup` 是可判定的），也可以用 `simp` 一次展开：
-/

example : sqWalk.IsTrail := ⟨by decide⟩
example : sqWalk.IsPath := by
  refine ⟨⟨?_⟩, ?_⟩
  · -- ⊢ sqWalk.edges.Nodup
    decide
  · -- ⊢ sqWalk.support.Nodup
    decide
example : sqWalk.IsPath := by simp [sqWalk]

/-!
**对途径做归纳**是图论证明的基本功：`induction p with | nil => … | cons h p ih => …`。
下面的例子用归纳证明「途径的 `support` 比 `length` 多一」（Mathlib 里是 `Walk.length_support`）：
-/

theorem support_length_eq {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.length = p.length + 1 := by
  induction p with
  | nil =>
    -- ⊢ SimpleGraph.Walk.nil.support.length = SimpleGraph.Walk.nil.length + 1
    rfl
  | cons h p ih =>
    -- h : G.Adj u✝ v✝,  p : G.Walk v✝ w✝,  ih : p.support.length = p.length + 1
    -- ⊢ (SimpleGraph.Walk.cons h p).support.length = (SimpleGraph.Walk.cons h p).length + 1
    simp [ih]

/-!
## 8. 可达、连通与连通分量

`G.Reachable u v`（reachable，可达）是命题 `Nonempty (G.Walk u v)`：存在一条途径。把数据（`Walk`）压成
命题是 `Nonempty` 的典型用法（第 7 章 §9），所以用 `⟨p⟩` 构造、用 `rintro ⟨p⟩` 拆开。`Reachable` 是
等价关系（`refl`、`symm`、`trans`）。`G.Connected`（连通）说所有顶点两两可达且顶点集非空，
连通分量 `G.ConnectedComponent` 是 `Reachable` 的商类型：
-/

example : square.Reachable 0 2 := ⟨sqWalk⟩
example (V : Type) (G : SimpleGraph V) (u v w : V) (h₁ : G.Reachable u v) (h₂ : G.Reachable v w) :
    G.Reachable u w := h₁.trans h₂
example (V : Type) (G : SimpleGraph V) (u v : V) (h : G.Adj u v) : G.Reachable u v := h.reachable

/-!
不可达要证明「不存在途径」：拆开 `Reachable` 后对途径分情况讨论。这里 `cases p` 只剩 `cons` 一种情形，
因为 `nil` 要求两端点相同，而 `0` 与 `1` 是 `Fin 2` 里不同的字面量，`cases` 自动排除了它。`cons` 的情形里有
一条边，与「没有边」矛盾（`⊥` 的 `Adj` 是 `False`，定义相等）。现成的引理是 `reachable_bot`：
-/

example : ¬ (⊥ : SimpleGraph (Fin 2)).Reachable 0 1 := by
  rintro ⟨p⟩
  -- p : ⊥.Walk 0 1 ⊢ False
  cases p with
  | cons h _ =>
    -- h : ⊥.Adj 0 v✝ ⊢ False
    exact h
example : ¬ (⊥ : SimpleGraph (Fin 2)).Reachable 0 1 := by
  rw [SimpleGraph.reachable_bot]
  decide

/-!
对有限图，`Reachable`、`Connected` 与 `ConnectedComponent` 的个数都是可判定的（Mathlib 的
`Connectivity/Finite.lean` 提供实例，要求 `[DecidableEq V] [Fintype V] [DecidableRel G.Adj]`），所以小图
直接核算：
-/

example : square.Connected := by decide
example : ¬ (⊥ : SimpleGraph (Fin 2)).Connected := by decide
example : Fintype.card (⊥ : SimpleGraph (Fin 3)).ConnectedComponent = 3 := by decide

/-!
大 `n` 时用现成的引理。标准的路 `pathGraph n`（`0 - 1 - ⋯ - (n-1)`）与圈 `cycleGraph n` 都是 `Fin n` 上
的图（§13 再细看），它们的连通性分别是 `connected_pathGraph_add_one`、`connected_cycleGraph_add_one`：
-/

example (n : ℕ) : (SimpleGraph.pathGraph (n + 1)).Connected :=
  SimpleGraph.connected_pathGraph_add_one n
example (n : ℕ) : (SimpleGraph.cycleGraph (n + 1)).Connected :=
  SimpleGraph.connected_cycleGraph_add_one

/-!
## 9. 无圈图与树

`G.IsAcyclic` 说 `G` 里没有圈，即 `∀ v (c : G.Walk v v), ¬ c.IsCycle`；tree（树）`G.IsTree` 是连通的无圈图。
`IsTree` 是 `Prop` 结构体，两个字段 `connected`、`isAcyclic`，所以可以用 `⟨hc, ha⟩` 构造。
`cycleGraph.cycle n` 是 `cycleGraph (n + 3)` 里从 `0` 出发的一条圈（`isCycle_cycle`），所以 `n := 1` 给出
`cycleGraph 4` 里的 4-圈，说明它不是无圈图。Mathlib 里最常用的是树的边数公式
`IsTree.card_edgeFinset : #G.edgeFinset + 1 = Fintype.card V`：
-/

example : ¬ (SimpleGraph.cycleGraph 4).IsAcyclic :=
  fun h ↦ h _ (SimpleGraph.cycleGraph.isCycle_cycle (n := 1))

example : (SimpleGraph.pathGraph 4).IsTree :=
  ⟨SimpleGraph.connected_pathGraph_add_one 3, SimpleGraph.isAcyclic_pathGraph 4⟩

example (n : ℕ) : #(SimpleGraph.pathGraph (n + 1)).edgeFinset = n := by
  have := (SimpleGraph.isTree_pathGraph_add_one n).card_edgeFinset
  -- this : #(SimpleGraph.pathGraph (n + 1)).edgeFinset + 1 = Fintype.card (Fin (n + 1))
  simpa using this

/-!
## 10. 团与独立集，案例：数三角形

团是两两相邻的顶点集合。`G.IsClique s` 对 `s : Set V`（可无限）定义为 `s.Pairwise G.Adj`；
`G.IsNClique n s` 对 `s : Finset V` 是一个有两个字段的结构体：`isClique`（`s` 是团）与 `card_eq`（`#s = n`），
即 `n`-团。`G.CliqueFree n` 说 `G` 里没有 `n`-团，`G.cliqueFinset n` 是全部 `n`-团构成的
`Finset (Finset V)`，要求 `[Fintype V] [DecidableEq V] [DecidableRel G.Adj]`。`n = 3` 的团就是三角形。
判断三个顶点是不是三角形有现成的引理：
-/

example {V : Type} (G : SimpleGraph V) (s : Finset V) (h : G.IsNClique 3 s) :
    G.IsClique ↑s ∧ #s = 3 := ⟨h.isClique, h.card_eq⟩

example (V : Type) [DecidableEq V] (G : SimpleGraph V) (a b c : V) :
    G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c :=
  SimpleGraph.is3Clique_triple_iff

example : paw.IsNClique 3 {0, 1, 2} :=
  SimpleGraph.is3Clique_triple_iff.2 ⟨by decide, by decide, by decide⟩

/-!
**案例：数三角形。** 三角形的个数就是 `cliqueFinset 3` 的元素个数（每个三角形对应一个无序的三元集）。
概率里常见的量「随机图中三角形的期望个数」（第 20 章）正是在这个有限集上求和。小图上整个 `Finset` 都能
`decide`；一般的上界是 `card_cliqueFinset_le : #(G.cliqueFinset n) ≤ (card α).choose n`；
`cliqueFinset n = ∅` 与 `CliqueFree n` 等价（`cliqueFinset_eq_empty_iff`），所以「没有三角形」可以先数成零
再转成命题：
-/

example : paw.cliqueFinset 3 = {{0, 1, 2}} := by decide
example : paw.CliqueFree 4 := SimpleGraph.cliqueFinset_eq_empty_iff.1 (by decide)
example : square.CliqueFree 3 := SimpleGraph.cliqueFinset_eq_empty_iff.1 (by decide)
example (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] : #(G.cliqueFinset 3) ≤ 20 := by
  have := SimpleGraph.card_cliqueFinset_le (G := G) (n := 3)
  simpa [Nat.choose] using this

/-!
**无三角形的推理。** `CliqueFree 3` 的定义是 `∀ t, ¬ G.IsNClique 3 t`，所以给出三个两两相邻的
顶点就得到矛盾：
-/

example (V : Type) [DecidableEq V] (G : SimpleGraph V) (h : G.CliqueFree 3) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) : ¬ G.Adj b c :=
  fun hbc ↦ h _ (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hac, hbc⟩)

/-!
independent set（独立集）是两两不相邻的集合：`G.IsIndepSet s`（展开是
`isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise fun v w ↦ ¬G.Adj v w`）、`G.IsNIndepSet n s`。补图把团变成
独立集（`isClique_compl`）：
-/

example : square.IsNIndepSet 2 {0, 2} := by decide
example (V : Type) (G : SimpleGraph V) (s : Set V) :
    G.IsIndepSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) := SimpleGraph.isIndepSet_iff G
example (V : Type) (G : SimpleGraph V) (s : Set V) : Gᶜ.IsClique s ↔ G.IsIndepSet s :=
  SimpleGraph.isClique_compl G

/-!
## 11. 着色

一个着色是相邻顶点不同色的赋值。Mathlib 把它定义成到完全图的 graph homomorphism（图同态，
保持相邻的映射 `G →g H`，§12 细看）：`G.Coloring α := G →g completeGraph α`。构造用
`Coloring.mk color valid`，`valid` 是相邻则异色。`G.Colorable n` 是 `Nonempty (G.Coloring (Fin n))`，
chromatic number（色数）`G.chromaticNumber : ℕ∞` 是能着色的最小颜色数。`ℕ∞`（即 `ENat`）是 `ℕ` 再添一个
`⊤`，无限图可能没有有限的着色，色数就是 `⊤`。bipartite graph（二分图）`G.IsBipartite` 就是 `G.Colorable 2`。
`square` 的 2-着色按奇偶性：
-/

def sqColor : square.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk (fun v ↦ ⟨v.val % 2, by omega⟩) (by decide)

example : square.Colorable 2 := ⟨sqColor⟩
example : square.IsBipartite := ⟨sqColor⟩
example (u v : Fin 4) (h : square.Adj u v) : sqColor u ≠ sqColor v := sqColor.valid h

/-!
色数的值：`chromaticNumber_cycleGraph_of_even`、`_of_odd` 给出圈的色数，`chromaticNumber_top` 给出
`n` 个点的完全图色数是 `n`；`chromaticNumber_le_iff_colorable` 在「色数 ≤ n」与「可 n-着色」之间转换。
团给出下界：一个 `n`-团需要 `n` 种颜色（`IsClique.card_le_of_colorable`）：
-/

example : (SimpleGraph.cycleGraph 4).chromaticNumber = 2 :=
  SimpleGraph.chromaticNumber_cycleGraph_of_even 4 (by norm_num) (by decide)
example : (SimpleGraph.cycleGraph 5).chromaticNumber = 3 :=
  SimpleGraph.chromaticNumber_cycleGraph_of_odd 5 (by norm_num) (by decide)
example : (⊤ : SimpleGraph (Fin 4)).chromaticNumber = 4 := by
  rw [SimpleGraph.chromaticNumber_top]
  -- ⊢ ↑(Fintype.card (Fin 4)) = 4
  simp
example (V : Type) [Infinite V] : (⊤ : SimpleGraph V).chromaticNumber = ⊤ :=
  SimpleGraph.chromaticNumber_top_eq_top_of_infinite V
example (V : Type) [DecidableEq V] (G : SimpleGraph V) (s : Finset V) (n : ℕ) (h : G.IsClique s)
    (hc : G.Colorable n) : #s ≤ n := h.card_le_of_colorable hc
example : ¬ (⊤ : SimpleGraph (Fin 3)).Colorable 2 := by
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable, SimpleGraph.chromaticNumber_top]
  -- ⊢ ¬↑(Fintype.card (Fin 3)) ≤ ↑2
  simp
  -- ⊢ 2 < 3
  decide

/-!
## 12. 子图、导出子图与图同态

`G.induce s`（`s : Set V`）是 induced subgraph（导出子图）：顶点是 `s` 的元素（类型 `↥s`，第 7 章），
相邻关系取自 `G`。它只是一个 `comap`，所以 `induce_adj` 是定义相等；一个集合是团当且仅当它的导出子图
是完全图（`induce_eq_top`）。更一般的 subgraph（子图）`G.Subgraph` 是另一个结构体，字段有顶点集
`verts`、相邻关系 `Adj`，以及 `Adj` 蕴含 `G.Adj` 和顶点属于 `verts`，是匹配等的对象：
-/

example (V : Type) (G : SimpleGraph V) (s : Set V) (u v : s) :
    (G.induce s).Adj u v ↔ G.Adj u v := Iff.rfl
example (V : Type) (G : SimpleGraph V) (s : Set V) : G.induce s = ⊤ ↔ G.IsClique s :=
  SimpleGraph.induce_eq_top
example (V : Type) (G : SimpleGraph V) : (⊤ : G.Subgraph).verts = Set.univ :=
  SimpleGraph.Subgraph.verts_top
example (V : Type) (G : SimpleGraph V) (H : G.Subgraph) (u v : V) (h : H.Adj u v) : G.Adj u v :=
  H.adj_sub h

/-!
**图之间的映射。** 它们都是第 15 章的打包映射，记号是全局的：`G →g H`（`SimpleGraph.Hom`，同态，
保持相邻）、`G ↪g H`（`Embedding`，embedding（嵌入）：单射且相邻当且仅当相邻）、`G ≃g H`（`Iso`，
isomorphism（同构）：可逆的嵌入）。作用写成 `f v`（背后是 `⇑f`）。同构有逆：`f.symm : H ≃g G`：
-/

example (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : G →g H) (u v : V)
    (h : G.Adj u v) : H.Adj (f u) (f v) := f.map_rel h
example (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : G ≃g H) (u v : V) :
    H.Adj (f u) (f v) ↔ G.Adj u v := f.map_rel_iff
example (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : G ↪g H) (u v : V) :
    H.Adj (f u) (f v) ↔ G.Adj u v := f.map_rel_iff
example (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : G ≃g H) : H ≃g G := f.symm

/-!
## 13. 小图与 `decide`

固定的小图可以直接核算：§4–§11 已经用 `decide` 数过边、度、三角形，判断过连通。`decide` 把 `Decidable`
实例规约成 `true`（第 6 章），Mathlib 自己就是这样证明 `cycleGraph_two_eq_top` 的。两个具体的图相等
也能核算：`SimpleGraph.ext` 化成 `Adj` 的逐点比较。`pathGraph n`、`cycleGraph n` 是 `Fin n` 上的
标准图；对 `n ≥ 2`，`(cycleGraph n).Adj a b` 是 `a - b = 1 ∨ b - a = 1`（`cycleGraph_adj`，`Fin n`
上的减法模 `n`）。`ext a b` 之后目标是 `Adj` 的双向蕴含，`revert a b` 把它变成闭的
`∀ a b : Fin 4, …`，`decide` 才能枚举。于是 `square` 就是 `cycleGraph 4`，能用 §9 的结论；同构
不直接 `decide`，而是由相等得到（最后一例）：
-/

theorem square_eq_cycleGraph : square = SimpleGraph.cycleGraph 4 := by
  ext a b
  -- a b : Fin 4 ⊢ square.Adj a b ↔ (SimpleGraph.cycleGraph 4).Adj a b
  revert a b
  -- ⊢ ∀ (a b : Fin 4), square.Adj a b ↔ (SimpleGraph.cycleGraph 4).Adj a b
  decide

example : SimpleGraph.cycleGraph 2 = ⊤ := SimpleGraph.cycleGraph_two_eq_top
example : ¬ square.IsTree := by
  rw [square_eq_cycleGraph]
  exact fun h ↦ h.isAcyclic _ (SimpleGraph.cycleGraph.isCycle_cycle (n := 1))
example : SimpleGraph.cycleGraph 4 ≃g square := square_eq_cycleGraph ▸ SimpleGraph.Iso.refl

/-!
**边界。** 数据一大，`decide` 在 elaborator（精译器；另译繁饰器）里规约，可能撞到递归深度或超时
（真实报错见第 12 章 §12 错误 5）；`decide +kernel` 交给 kernel（内核）规约（两者的区别见第 12 章
§9）。下面两例分别算到 6、8 个顶点；这只是本章示例的规模，不是通用的阈值：
-/

example : ((⊤ : SimpleGraph (Fin 6)).cliqueFinset 3).card = 20 := by decide
example : ((⊤ : SimpleGraph (Fin 8)).cliqueFinset 3).card = 56 := by decide +kernel

/-!
## 14. 大定理导览

Mathlib 的 `Combinatorics/SimpleGraph/` 里有几个组合学的大定理。本节只看陈述、不看证明。读陈述的
办法：先看变量行（有哪些实例），再看假设，最后看结论，对照本章的词汇逐个认。下面的 `example` 都由
对应的 Mathlib 定理推出；完整的参数与假设见源码。

**图兰定理。** 读法示范：变量行 `[Fintype V]`、`[DecidableRel G.Adj]` 与 §4 一样，是为了
有 `edgeFinset`；假设 `G.CliqueFree (r + 1)` 是没有 `(r+1)`-团（§10）；结论的右边 `turanNumber n r` 是
图兰图 `turanGraph n r`（`Fin n` 上，`v % r ≠ w % r` 则相邻）的边数。所以无 `(r+1)`-团的图至多有这么多边。
`r = 2` 时就是 Mantel 定理（无三角形图至多 `n ^ 2 / 4` 条边，`turanNumber_two`）：
-/

example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : G.CliqueFree (r + 1)) : #G.edgeFinset ≤ SimpleGraph.turanNumber (Fintype.card V) r :=
  h.card_edgeFinset_le

example {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #G.edgeFinset ≤ Fintype.card V ^ 2 / 4 := by
  have := SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) h
  rwa [SimpleGraph.turanNumber_two] at this

/-!
**霍尔婚配定理**（图版本）。`G.IsBipartiteWith p₁ p₂` 说 `p₁` 与 `p₂` 不相交，
且 `G` 的每条边一端在 `p₁`、一端在 `p₂`；`[G.LocallyFinite]` 说每个顶点的邻点集是有限的。若 `p₁` 的每个
子集 `s` 的邻点并集都至少与 `s` 一样大，则存在 matching（匹配）覆盖 `p₁`。匹配是 `G.Subgraph` 的谓词
`IsMatching`：子图 `M` 的每个顶点（`v ∈ M.verts`）在 `M` 中恰有一个邻点；perfect matching
（完美匹配）再要求 `M` 覆盖所有顶点：
-/

example {V : Type*} (G : SimpleGraph V) [G.LocallyFinite] {p₁ p₂ : Set V}
    (h₁ : G.IsBipartiteWith p₁ p₂)
    (h₂ : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching :=
  SimpleGraph.exists_isMatching_of_forall_ncard_le h₁ h₂

/-!
**Szemerédi 正则性引理。** 注意它在根命名空间（没有 `SimpleGraph.` 前缀）。
对任意 `ε > 0` 与下界 `l`，任意够大（`l ≤ card α`）的图有一个 equipartition（等分划，各块大小至多差 `1`
的 `Finpartition`，`IsEquipartition`），块数在 `l` 与一个只依赖 `ε`、`l` 的常数 `bound ε l` 之间，且
这个分划是 `ε`-`IsUniform` 的：不均匀的块对至多占 `ε` 的比例，其余块对之间的边近似均匀分布：
-/

open SzemerediRegularity in
example {α : Type*} [DecidableEq α] [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] {ε : ℝ}
    {l : ℕ} (hε : 0 < ε) (hl : l ≤ Fintype.card α) :
    ∃ P : Finpartition (Finset.univ : Finset α),
      P.IsEquipartition ∧ l ≤ #P.parts ∧ #P.parts ≤ bound ε l ∧ P.IsUniform G ε :=
  szemeredi_regularity G hε hl

/-!
同一目录里还有完美匹配的 Tutte 定理（`Tutte.lean`，`SimpleGraph.tutte`）和三角形移除引理
（`Triangle/Removal.lean`，`SimpleGraph.triangle_removal`），本章不展开。

## 15. 怎样找图论引理

搜索的一般流程（命名规则、`exact?`、Loogle）见第 9 章，这里只补图论特有的文件定位：一个主题一个
文件。团在 `Clique.lean`（如 `card_cliqueFinset_le`），着色在 `Coloring/Vertex.lean`（如
`chromaticNumber_top`），度与边数在 `Finite.lean`，握手引理在 `DegreeSum.lean`，途径在
`Walk/Basic.lean` 与 `Paths.lean`，连通性在 `Connectivity/`。在对应文件里用
`rg "theorem .*cliqueFinset"` 这样的模式搜。

## 16. 常见错误

缺 `DecidableRel` 的报错在 §1、§4 已经见过。

**1. 老写法 `Sym2.mk (a, b)`。** 本书固定的 Mathlib 里 `Sym2.mk` 是 `α → α → Sym2 α`（旧版接一个数对
`α × α`，Mathlib 自己的部分文档注释仍沿用旧写法），数对写法会类型不对：
-/

/--
error: Type mismatch
  Sym2.mk (a, b)
has type
  ℕ × ℕ → Sym2 (ℕ × ℕ)
but is expected to have type
  Sym2 ℕ
-/
#guard_msgs in
example (a b : ℕ) : Sym2 ℕ := Sym2.mk (a, b)

/-!
**2. 老写法 `symm := fun a b h ↦ …`。** `symm` 的类型是 `Std.Symm Adj`（一个结构体）而不是
`Symmetric Adj`（一个 `∀` 命题），旧教程里的 lambda 写法不再成立（这里 `set_option pp.mvars false`
只是为了让错误信息里的元变量编号稳定，见第 3 章 §7）：
-/

/--
error: Type mismatch
  fun a b h ↦ ?_
has type
  (a : ?_) → (b : ?_ a) → (h : ?_ a b) → ?_ a b h
but is expected to have type
  Std.Symm fun a b ↦ a ≠ b
-/
#guard_msgs in
set_option pp.mvars false in
example : SimpleGraph (Fin 4) where
  Adj a b := a ≠ b
  symm := fun a b h ↦ by omega

/-!
**3. 对 `IsPath` 用 `decide`。** `Walk.IsPath` 有 `Decidable` 实例，但它是用 `rw` 写出来的，
`decide` 规约到 `▸`（`Eq.rec`）就卡住；编译器给出的提示正好说了原因。换成 §7 的做法
（把字段交给 `decide`，或者 `simp`）：
-/

/--
error: Tactic `decide` failed to reduce
  @decide sqWalk.IsPath sqWalk.instDecidableIsPathOfDecidableEq
to `true` or `false`.

After unfolding the instance `SimpleGraph.Walk.instDecidableIsPathOfDecidableEq`, reduction got stuck at
  ⋯ ▸ inferInstance

Hint: Reduction got stuck on `▸` (Eq.rec), which suggests that one of the `Decidable` instances is defined using tactics such as `rw` or `simp`. To avoid tactics, make use of functions such as `«inferInstanceAs»` or `decidable_of_decidable_of_iff` to alter a proposition.
-/
#guard_msgs in
example : sqWalk.IsPath := by decide

/-!
**4. 把 `Walk` 当命题。** `G.Walk u v` 住在 `Type`，不是 `Prop`，不能当证明用；要的是「存在一条途径」
时用 `Reachable`（§8）：
-/

/--
error: Type mismatch
  h
has type
  G.Walk u v
of sort `Type` but is expected to have type
  u = v
of sort `Prop`
-/
#guard_msgs in
example (V : Type) (G : SimpleGraph V) (u v : V) (h : G.Walk u v) : u = v := h

/-!
## 练习

练习按小节顺序。重温前面章节的有：18.4–18.5（第 12 章的 `Nat.choose`、`Finset.sum_const`），18.6（第 4 章的
反证与 `push Not`），18.7–18.8（第 6 章的 `cases` 与归纳），18.9（第 9 章的 `exact?`），18.11（第 8 章的
`classical`），18.3（第 5 章的 `decide`），18.14（第 15 章的打包映射）。引理名在本章出现，或由题面的提示给出。
-/

/-- 练习 18.1（★）：相邻蕴含两端点不同且反向也相邻。用 `Adj.ne` 与 `Adj.symm`（§1）。 -/
theorem ex_18_1 {V : Type*} (G : SimpleGraph V) (u v : V) (h : G.Adj u v) :
    u ≠ v ∧ G.Adj v u := by sorry

/-- 练习 18.2（★）：补图的相邻关系（§2）。若 `u ≠ v` 且 `G` 里 `u v` 不相邻，则它们在 `Gᶜ` 里相邻。
用 `SimpleGraph.compl_adj`。 -/
theorem ex_18_2 {V : Type*} (G : SimpleGraph V) (u v : V) (huv : u ≠ v) (h : ¬ G.Adj u v) :
    Gᶜ.Adj u v := by sorry

/-- 练习 18.3（★）：5-圈是 2-正则的，有 5 条边，且没有三角形。度与边数可以 `decide`（§5、§13）；
无三角形先用 `cliqueFinset_eq_empty_iff` 化成数零（§10）。 -/
theorem ex_18_3 : (∀ v, (SimpleGraph.cycleGraph 5).degree v = 2) ∧
    #(SimpleGraph.cycleGraph 5).edgeFinset = 5 ∧ (SimpleGraph.cycleGraph 5).CliqueFree 3 := by
  sorry

/-- 练习 18.4（★）：边数的上界（§4）。`n` 个顶点的图至多有 `n * (n - 1) / 2` 条边。用
`SimpleGraph.card_edgeFinset_le_card_choose_two` 与第 12 章的 `Nat.choose_two_right`。 -/
theorem ex_18_4 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset ≤ Fintype.card V * (Fintype.card V - 1) / 2 := by sorry

/-- 练习 18.5（★★）：7 个顶点的图不可能是 3-正则的（握手引理，§6）。用
`sum_degrees_eq_twice_card_edges`、`IsRegularOfDegree.degree_eq` 与 `Finset.sum_const`（第 12 章 §3），
最后用 `omega` 看奇偶性。 -/
theorem ex_18_5 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Fintype.card V = 7) : ¬ G.IsRegularOfDegree 3 := by sorry

/-- 练习 18.6（★★）：顶点数为奇数的图必有偶数度的顶点。思路同 §6 的 `even_card_of_forall_odd_degree`：
用 `by_contra` 与 `push Not`（第 4 章）得到每个顶点的度都是奇数（`Nat.not_even_iff_odd`），再由
`even_card_odd_degree_vertices` 与 `Finset.filter_true_of_mem` 推出顶点数是偶数，与 `hV` 矛盾。 -/
theorem ex_18_6 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : Odd (Fintype.card V)) : ∃ v, Even (G.degree v) := by sorry

/-- 练习 18.7（★）：空图里没有途径连接不同的顶点（§7）。对途径分情况讨论：`nil` 时相等，`cons` 时
有一条边，与 `⊥` 矛盾。 -/
theorem ex_18_7 {V : Type*} (u v : V) (p : (⊥ : SimpleGraph V).Walk u v) : u = v := by sorry

/-- 辅助定义：朴素地数一条途径的步数（对 `Walk` 的结构递归，和 `Walk.length` 的定义同形）。 -/
def walkSteps {V : Type*} {G : SimpleGraph V} : {u v : V} → G.Walk u v → ℕ
  | _, _, .nil => 0
  | _, _, .cons _ p => walkSteps p + 1

/-- 练习 18.8（★★）：对途径归纳（§7）。上面的 `walkSteps` 与 `Walk.length` 相等：
`walkSteps p = p.length`。提示：`induction p with` 分 `nil`、`cons` 两种情形，`cons` 的情形展开
`walkSteps`，再用归纳假设。 -/
theorem ex_18_8 {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    walkSteps p = p.length := by sorry

/-- 练习 18.9（★）：连通性随加边保持（§8）：若 `G ≤ H` 且 `G` 连通，则 `H` 连通。用 `exact?`
（第 9 章）找现成的引理。 -/
theorem ex_18_9 {V : Type*} {G H : SimpleGraph V} (h : G ≤ H) (hG : G.Connected) :
    H.Connected := by sorry

/-- 练习 18.10（★★）：12 个顶点的树有 11 条边（§9）。用 `IsTree.card_edgeFinset`，再 `omega`。 -/
theorem ex_18_10 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsTree)
    (hV : Fintype.card V = 12) : #G.edgeFinset = 11 := by sorry

/-- 练习 18.11（★★）：无三角形的图里，任一顶点的邻点集是独立集（§10）。先 `classical`（第 8 章），因为
`{a, b, c}` 这样的 `Finset` 字面量需要 `DecidableEq V`；用 `isIndepSet_iff` 展开，再用
`is3Clique_triple_iff`。 -/
theorem ex_18_11 {V : Type*} (G : SimpleGraph V) (h : G.CliqueFree 3) (v : V) :
    G.IsIndepSet (G.neighborSet v) := by sorry

/-- 练习 18.12（★★）：5-圈不能 2-着色（§11）。用 `chromaticNumber_cycleGraph_of_odd`（色数是 `3`）与
`chromaticNumber_le_iff_colorable`，最后 `ℕ∞` 里的不等式 `3 ≤ 2` 可交给 `decide`
（§11 里 `ℕ∞` 的 `2 < 3` 就是这样关上的）。 -/
theorem ex_18_12 : ¬ (SimpleGraph.cycleGraph 5).Colorable 2 := by sorry

/-- 练习 18.13（★★）：二分图没有三角形（§10、§11）。设 `t` 是 3-团：`IsNClique` 的字段 `isClique`
与 `card_eq` 给出 `G.IsClique ↑t` 与 `#t = 3`；团的着色至少要 3 种颜色（`IsClique.card_le_of_colorable`），
与 `Colorable 2` 矛盾。 -/
theorem ex_18_13 {V : Type*} (G : SimpleGraph V) (h : G.Colorable 2) : G.CliqueFree 3 := by
  sorry

/-- 练习 18.14（★）：同构保持相邻（§12，第 15 章的打包映射）。若 `f : G ≃g H`，`f` 的逆也保持相邻：
`H.Adj x y → G.Adj (f.symm x) (f.symm y)`。 -/
theorem ex_18_14 {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H) (x y : W)
    (h : H.Adj x y) : G.Adj (f.symm x) (f.symm y) := by sorry

/-- 练习 18.15（★★）：6 个顶点、没有三角形的图至多有 9 条边（Mantel，§14）。用
`CliqueFree.card_edgeFinset_le (r := 2)`、`turanNumber_two` 与 `Fintype.card_fin`，最后 `simpa`。 -/
theorem ex_18_15 (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    #G.edgeFinset ≤ 9 := by sorry

/-!
## 小结

| 概念 | 写法 | 何时用 |
|---|---|---|
| 图 | `SimpleGraph V`、`G.Adj`、`G.symm.symm`、`G.loopless.irrefl` | 取对称性、无自环的证明 |
| 造图 | `⊥`、`⊤`、`fromRel`、`fromEdgeSet`、`where Adj … symm.symm …` | 小图与具体构造 |
| 具体图的实例 | `instance : DecidableRel G.Adj := inferInstanceAs …` | 要 `decide`、`edgeFinset` |
| 缺实例 | 写进假设、`Set.ncard`、`open scoped Classical in` 加 `convert` | 报 `failed to synthesize` |
| 边与边数 | `edgeSet`、`s(a, b)`、`edgeFinset`、`card_edgeFinset_le_card_choose_two` | 边是无序对；数边 |
| 度与握手引理 | `degree`、`minDegree`、`IsRegularOfDegree`、`sum_degrees_eq_twice_card_edges` | 度与边数互换 |
| 途径 | `Walk`（`nil`/`cons`）、`length`、`support`、`IsPath`、`IsTrail`、`IsCycle` | 对途径归纳 |
| 连通 | `Reachable`、`Connected`、`ConnectedComponent` | 要「存在途径」（`Nonempty (Walk …)`） |
| 树 | `IsAcyclic`、`IsTree`、`IsTree.card_edgeFinset` | 由顶点数得边数 |
| 团与独立集 | `IsNClique`、`CliqueFree`、`cliqueFinset`、`is3Clique_triple_iff`、`IsIndepSet` | 数三角形 |
| 着色 | `Coloring.mk`、`Colorable`、`chromaticNumber`、`IsBipartite` | 给着色、估色数（在 `ℕ∞`） |
| 子图与映射 | `induce`、`Subgraph`、`→g`、`↪g`、`≃g` | 比较两个图；`f.map_rel_iff` |
| 小图核算 | `decide`、`decide +kernel` | 本章示例分别算到 6、8 个顶点 |
| 图兰、霍尔 | `CliqueFree.card_edgeFinset_le`、`exists_isMatching_of_forall_ncard_le` | 读陈述 |
| 正则性引理 | `szemeredi_regularity`（根命名空间） | 读陈述 |
-/

/-!
## 延伸阅读

- Mathlib 源码：`Mathlib/Combinatorics/SimpleGraph/Basic.lean`（结构体、`aesop_graph`、`edgeSet`、
  `fromEdgeSet`、`fintypeEdgeSet`）、`Finite.lean`（`edgeFinset`、`degree`）、`DegreeSum.lean`。
- 途径与连通：`Mathlib/Combinatorics/SimpleGraph/Walk/Basic.lean`、`SimpleGraph/Paths.lean`、
  `Connectivity/Connected.lean`、`Connectivity/Finite.lean`（可判定性实例）、`Acyclic.lean`（`IsTree`）。
  旧的 `Walks/` 目录与 `Coloring.lean` 已是弃用的转发文件，不要再导入。
- 团与着色：`Mathlib/Combinatorics/SimpleGraph/Clique.lean`、`Coloring/Vertex.lean`、
  `Coloring/Constructions.lean`、`Bipartite.lean`。
- 大定理：`Extremal/Turan.lean`、`Hall.lean`、`Regularity/Lemma.lean`（基于 `Regularity/Uniform.lean`）。
- 本书：第 12 章（`Finset`、双重计数、`Nat.choose`）、第 15 章（打包映射 `→g`/`≃g`）、
  第 19 章（有限概率空间与概率方法，会用到本章的计数）、第 20 章（`SimpleGraph.binomialRandom`）。
-/

end Lean4Learn.Ch18

end
