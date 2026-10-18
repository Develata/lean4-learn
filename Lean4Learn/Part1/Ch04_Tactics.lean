module

public import Batteries.Tactic.Init
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar
public import Mathlib.Tactic.Use

/-!
# 第 4 章　策略即构造项：逻辑与量词

第 3 章用 term-mode（项模式）直接写 proof term（证明项）。本章讲 tactic-mode（策略模式）：`by` 之后的
一串 tactic（策略）一步步改写 goal（目标），最后拼成**同一个**项。中心观点只有一句：策略不是另一种证明，
而是写项的另一种方式。凡是第一次遇到的构造，都在策略版本旁边给出项模式的写法。

## 学习目标
- 说明策略如何通过 metavariable（元变量）逐步拼出一个项，并用 `show_term`（第 3 章 §11）检查它；
- 对 `→ ∧ ↔ ∨ ¬ ∀ ∃ ∃!`，说出 introduction（引入）与 elimination（消去）各用哪个策略，读懂 proof state
  （证明状态），用 `·`、`case`、`<;>` 组织多个目标；
- 会做 case analysis（分情况讨论）与 proof by contradiction（反证法）：`by_cases`、`by_contra`、`push Not`、
  `contrapose!`、`tauto`；知道 `push_neg` 已弃用，`constructor` 对 `Or` 会给出歧义警告；
- 会用 `have`、`show`、`suffices` 搭证明的骨架。

## 前置知识
第 1 章（`trace_state`，§4；`#guard_msgs`，§6）；第 3 章（每个联结词的引入与消去项，§8；`#print axioms`，
§8.8；`show_term`，§11）；第 2 章的 `omega`，后面的例子用它收尾算术部分。
-/

@[expose] public section

namespace Lean4Learn.Ch04

/-!
## 1. 策略如何拼出一个项

`by` 后面写 tactic 序列。elaborator（精译器；另译繁饰器）遇到 `by` 时，先造一个元变量代表「还没造出
的项」，把目标记在它上面；每条策略把这个元变量赋值，通常赋成一个带新 hole（洞）的项，新的洞成为新的
目标。全部目标关闭时，元变量被填满，剩下的就是一个完整的项。

`trace_state`（第 1 章 §4）把 infoview（信息视图）在该处显示的证明状态变成一条消息。下面把
`p ∧ q → q ∧ p` 写成两种形式，并看 `intro` 之后的状态：
-/

example {p q : Prop} : p ∧ q → q ∧ p := fun h ↦ ⟨h.2, h.1⟩

/--
trace: p q : Prop
h : p ∧ q
⊢ q ∧ p
-/
#guard_msgs in
example {p q : Prop} : p ∧ q → q ∧ p := by
  intro h
  trace_state
  exact ⟨h.2, h.1⟩

/-!
`intro h` 把目标 `p ∧ q → q ∧ p` 的前件搬进 context（上下文），成为一条 hypothesis（假设）`h`
（项模式的 `fun h ↦ …`），目标变成 `q ∧ p`；`exact e` 用项 `e` 一次关闭目标。策略证明与项模式是同一个
东西，§2 里用 `show_term` 看 `apply` 拼出的项。

## 2. 蕴含与全称：`intro`、`exact`、`apply`、`assumption`

第 3 章说过，`p → q` 与 `∀ x, p x` 都是函数类型。对应地，**引入**一个蕴含或全称量词用 `intro`
（项模式的 `fun`），**消去**就是把它当函数应用到参数上。`intro` 可以一次带多个名字。
-/

example {p q r : Prop} : (p → q) → (q → r) → p → r :=
  fun hpq hqr hp ↦ hqr (hpq hp)

example {p q r : Prop} : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  -- hpq : p → q, hqr : q → r, hp : p ⊢ r
  exact hqr (hpq hp)

example {α : Type*} {p : α → Prop} (h : ∀ x, p x) (a : α) : p a := h a

/-!
`exact e` 要求 `e` 的类型与目标 definitional equality（定义相等），不要求字面相同；`assumption` 在上下文
里找一个类型与目标定义相等的假设。`¬p` 展开就是 `p → False`，所以下面两个都成立：
-/

example {p : Prop} (h : p → False) : ¬p := by exact h

example {p : Prop} (h : ¬p) : p → False := by assumption

/-!
`apply f` 从目标出发倒着推：`f` 的结论与目标做 unification（合一），`f` 的每个没被合一确定的参数成为
新目标。下例目标是 `r`，而 `h : p → q → r`，所以 `apply h` 留下 `p` 与 `q` 两个目标。`·`（聚焦）让缩进的
块只处理当前第一个目标，并且必须把它关掉；它与 `(· + 1)` 里的 `·` 无关（第 3 章）。项模式就是 `h hp hq`：
-/

example {p q r : Prop} (h : p → q → r) (hp : p) (hq : q) : r := h hp hq

example {p q r : Prop} (h : p → q → r) (hp : p) (hq : q) : r := by
  apply h
  -- 两个目标：⊢ p 与 ⊢ q
  · exact hp
  · exact hq

/-!
用 `show_term`（第 3 章 §11）看每一步策略拼出的项。下面每一步 `apply` 都在项里放一个洞，最后拼出的
就是手写的 `hqr (hpq hp)`：
-/

/--
info: Try this:
  [apply] exact hqr (hpq hp)
-/
#guard_msgs in
example {p q r : Prop} (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  show_term
    apply hqr
    -- ⊢ q
    apply hpq
    -- ⊢ p
    assumption

/-!
**`refine` 与 `?_`。** `refine e` 的 `e` 里没被合一解决的 `?_`（或具名的 `?h`）成为新目标。`?_` 是手写的
洞；精译器自己生成的洞在消息里显示成 `?m.N`（第 3 章 §7），两者共用 `?`，别混淆。`_` 是 placeholder
（占位符），必须由精译器自己填出来，填不出就报错（§10）。`apply hqr` 与 `refine hqr ?_` 在这里等价：
-/

example {p q r : Prop} (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  refine hqr ?_
  -- ⊢ q
  refine hpq ?_
  -- ⊢ p
  exact hp

/-!
## 3. 合取与双向蕴含：`constructor`、`obtain`、`rintro`

证 `p ∧ q` 要同时交出两个证明；用 `p ∧ q` 则可以取出两个。**引入** `p ∧ q`：`constructor` 把目标拆成两个，
标签（case tag）是 `left` 与 `right`（§10 第 3 个错误里能看到），逐个用 `·` 解决；`refine ⟨?_, ?_⟩`
与 `exact ⟨hp, hq⟩` 是等价的写法（`⟨…⟩` 是 anonymous constructor（匿名构造子））；`refine` 还允许只填一半：
-/

example {p q : Prop} (hp : p) (hq : q) : p ∧ q := by
  constructor
  -- 两个目标：⊢ p 与 ⊢ q
  · exact hp
  · exact hq

example {p q : Prop} (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

example {p q : Prop} (hp : p) (hq : q) : p ∧ q := by
  refine ⟨hp, ?_⟩
  -- ⊢ q
  exact hq

/-!
**消去** `h : p ∧ q`：`obtain ⟨hp, hq⟩ := h` 把它拆成两个假设。`⟨hp, hq⟩` 叫 pattern（模式）；
pattern matching（模式匹配）的一般理论在第 6 章，这里只用 `rcases` 一族策略的几种模式：

| 模式 | 作用 |
|---|---|
| `⟨a, b⟩` | 拆只有一个 constructor（构造子）的类型（`∧`、`∃`、`↔`）；可嵌套，向右折叠：`⟨a, b, c⟩ = ⟨a, ⟨b, c⟩⟩` |
| `a \| b` | 拆 `∨`：每个构造子一个目标；`a \| b \| c` 同样向右折叠，对应 `p ∨ q ∨ r`（§4）；也拆一般的 inductive type（归纳类型，第 6 章） |
| `rfl` | 假设是一边为变量的等式时，把这个变量处处换掉（§6） |
| `_` / `-` | `_` 不起名字，由系统自动命名成不可访问的名字；`-` 把这个部分清除，不留在上下文里（见下面 `rintro ⟨_, -, hr⟩` 那个例子） |

`obtain pat := e` 等价于先 `have` 再 `rcases`；`rintro pat` 是 `intro` 之后再 `rcases`，一次可以带多个
模式（用空格隔开），所以顶层的 `a | b` 要加括号：`rintro (a | b)`（§4）。三者都在核心库的
`Init/RCases.lean` 里。
-/

example {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) := fun ⟨⟨hp, hq⟩, hr⟩ ↦ ⟨hp, hq, hr⟩

example {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) := by
  intro h
  obtain ⟨⟨hp, hq⟩, hr⟩ := h
  -- hp : p, hq : q, hr : r ⊢ p ∧ q ∧ r
  exact ⟨hp, hq, hr⟩

/--
trace: p q r : Prop
left✝ : p
hr : r
⊢ r
-/
#guard_msgs in
example {p q r : Prop} : p ∧ q ∧ r → r := by
  rintro ⟨_, -, hr⟩
  trace_state
  exact hr

/-!
**biconditional（双向蕴含）** `p ↔ q` 是 structure（结构体），有 field（字段）`mp` 与 `mpr`，只有一个构造子，
所以引入同样用 `constructor`，两个目标的标签就是 `mp` 与 `mpr`。`case tag => tac` 按标签选目标，不依赖
目标的顺序；消去则取出字段：
-/

example {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  case mpr =>
    rintro ⟨hp, hq, hr⟩
    exact ⟨⟨hp, hq⟩, hr⟩
  case mp =>
    rintro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, hq, hr⟩

example {p q : Prop} (h : p ↔ q) (hp : p) : q := h.mp hp

/-!
## 4. 析取：`left`、`right` 与 `rcases`

用 `p ∨ q` 时不知道哪一边成立，所以两边都要处理。**引入** `p ∨ q`：`left` 把目标换成 `p`，`right` 把目标
换成 `q`（即项模式的 `Or.inl`、`Or.inr`）。**消去** `h : p ∨ q`：`rcases h with hp | hq` 产生两个目标，
标签是 `inl` 与 `inr`：
-/

example {p q : Prop} : p ∨ q → q ∨ p := fun
  | Or.inl hp => Or.inr hp
  | Or.inr hq => Or.inl hq

example {p q : Prop} : p ∨ q → q ∨ p := by
  intro h
  rcases h with hp | hq
  -- 两个目标：`case inl`（有 `hp : p`）与 `case inr`（有 `hq : q`），目标都是 `q ∨ p`
  case inl =>
    right
    exact hp
  case inr =>
    left
    exact hq

/-!
`rintro` 直接在引入时拆开：模式 `(hp | hq | hr)` 把 `p ∨ q ∨ r` 一次拆成三种情形；`|` 也可以嵌在
`⟨…⟩` 里面，如 `⟨hp | hq, hr⟩` 拆 `(p ∨ q) ∧ r`（练习 4.2、4.3）：
-/

example {p q r : Prop} : p ∨ q ∨ r → r ∨ q ∨ p := by
  rintro (hp | hq | hr)
  · exact Or.inr (Or.inr hp)
  · exact Or.inr (Or.inl hq)
  · exact Or.inl hr

example {p q r : Prop} : (p ∨ q) ∧ r → (p ∧ r) ∨ (q ∧ r) := by
  rintro ⟨hp | hq, hr⟩
  · exact Or.inl ⟨hp, hr⟩
  · exact Or.inr ⟨hq, hr⟩

/-!
**`constructor` 对 `Or` 有歧义。** `Or.inl` 与 `Or.inr` 都能用时，`constructor` 取声明顺序里的第一个，
而不是证明需要的那个；自 Lean 4.35 起这种情形给出警告。下面的证明恰好因为 `Or.inl` 排第一而成立，仍收到
警告。修法是写明意图：`left` 或 `right`。真要沿用「取第一个」，写警告里建议的 `constructor!`。本书一律
用 `left`/`right`。
-/

/--
warning: Tactic `constructor` applied constructor `Or.inl`, but `Or.inr` also matches the goal.

Hint: Use `constructor!` to apply the first matching constructor without this warning:
  [apply] constructor!
-/
#guard_msgs in
example {p q : Prop} (hp : p) : p ∨ q := by
  constructor
  exact hp

/-!
## 5. 否定与矛盾：`exfalso`、`contradiction`、`absurd`

`¬p` 就是 `p → False`，所以证 `¬p` 用 `intro`（它会自动展开 `¬`）。得到矛盾后，要证任何目标 `q` 都行：
`exfalso` 把目标换成 `False`（即 `False.elim`），`contradiction` 在上下文里自己找矛盾，`absurd hp`
则指定矛盾的一方：它把目标换成 `¬p`；若给的是 `h : ¬r`，`absurd h` 把目标换成 `r`。`absurd`（策略）来自
Batteries，由本文件第一条 `public import Batteries.Tactic.Init` 引入；项模式的 `absurd hp hnp` 在核心库里。
-/

theorem double_neg_intro {p : Prop} : p → ¬¬p := by
  intro hp hnp
  exact hnp hp

example {p q : Prop} (hp : p) (hnp : ¬p) : q := by
  exfalso
  -- ⊢ False
  exact hnp hp

example {p q : Prop} (hp : p) (hnp : ¬p) : q := by
  contradiction

example {p q : Prop} (hp : p) (hnp : ¬p) : q := by
  absurd hp
  -- ⊢ ¬p
  exact hnp

example {r q : Prop} (h : ¬r) (hr : r) : q := by
  absurd h
  -- ⊢ r
  exact hr

/-!
## 6. 量词：`∃`、`use`、`obtain` 与 `∃!`

证 `∃ x, p x` 要交出一个 witness（见证）；用它则取出见证。**引入** `∃ x, p x`：给出见证 `w`，再证
`p w`。三种写法：
- `refine ⟨w, ?_⟩`：给出见证，把 `p w` 留作目标；
- `exists w`（核心库中的策略）：据其文档注释，是 `refine ⟨w, ?_⟩` 之后试 `trivial`；
- `use w`（Mathlib，需要 `Mathlib.Tactic.Use`）：给出见证后，对剩下的目标尝试 discharger（副条件处理器）
  `try with_reducible use_discharger`：默认能做 `rfl`、`assumption`、`And.intro` 等（见
  `Mathlib/Tactic/Use.lean`），能关的关掉，关不掉的留给你；可以一次给多个见证：`use a, b`。
-/

example : ∃ n : ℕ, n + 3 = 5 := ⟨2, rfl⟩

example : ∃ n : ℕ, n + 3 = 5 := by
  refine ⟨2, ?_⟩
  rfl

example : ∃ n : ℕ, n + 3 = 5 := by exists 2

example : ∃ a b : ℕ, a + b = 5 ∧ a * b = 6 := by
  use 2, 3

example {α : Type*} {p : α → Prop} (a : α) (h : p a) : ∃ x, p x := by
  use a

/-!
`use 2, 3` 之后剩下 `2 + 3 = 5 ∧ 2 * 3 = 6`，discharger 先用 `And.intro` 拆开，再对两部分各用 `rfl`
关掉；`use a` 之后剩下的 `p a` 上下文里就有，也被关掉了。含变量、要靠 `omega` 的目标，`use` 关不掉，留给你
（标签 `h` 是 `Exists.intro` 的字段名）：
-/

/--
trace: case h
m : ℕ
h : 3 ≤ m
⊢ m - 3 + 3 = m
-/
#guard_msgs in
example (m : ℕ) (h : 3 ≤ m) : ∃ n : ℕ, n + 3 = m := by
  use m - 3
  trace_state
  omega

/-!
**消去** `h : ∃ x, p x`：`obtain ⟨w, hw⟩ := h`。得到的 `w` 是任意但固定的见证，不能追问它是哪个数。
消去模式里的 `rfl` 很常用：若 `hw` 是 `n = m + 1` 这样一边为变量的等式，`rfl` 把 `n` 处处换成 `m + 1`：
-/

example {α : Type*} {p q : α → Prop} : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ ∃ x, q x :=
  fun ⟨x, hpx, hqx⟩ ↦ ⟨⟨x, hpx⟩, ⟨x, hqx⟩⟩

example {α : Type*} {p q : α → Prop} : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ ∃ x, q x := by
  rintro ⟨x, hpx, hqx⟩
  exact ⟨⟨x, hpx⟩, ⟨x, hqx⟩⟩

/--
trace: m : ℕ
⊢ 0 < m + 1
-/
#guard_msgs in
example (n : ℕ) (h : ∃ m, n = m + 1) : 0 < n := by
  obtain ⟨m, rfl⟩ := h
  trace_state
  omega

/-!
**`∃!`（唯一存在）。** `∃! x, p x`（`ExistsUnique p`，需要 `Mathlib.Basic.ExistsUnique`）意为
`∃ x, p x ∧ ∀ y, p y → y = x`：见证、它满足性质、唯一性三部分。匿名构造子与 `obtain` 会把类型展开到
weak head normal form（弱头正规形，whnf）再找构造子，所以看得穿这个 `def`，下面的 `⟨2, rfl, …⟩` 就是
证明。`refine` 之后的目标里，性质 `p y` 还没做 β-reduction（β 规约），是 `(fun n ↦ …) y` 的形状，
`omega` 照样能用：
-/

/-- trace: ⊢ ∀ (y : ℕ), (fun n ↦ n + 3 = 5) y → y = 2 -/
#guard_msgs in
example : ∃! n : ℕ, n + 3 = 5 := by
  refine ⟨2, rfl, ?_⟩
  trace_state
  intro y hy
  omega

example : ∃! n : ℕ, n + 3 = 5 := ⟨2, rfl, fun y hy ↦ by omega⟩

-- 使用 `∃!` 时，`obtain` 同样得到这三个部分：
example (h : ∃! n : ℕ, n + 3 = 5) : ∀ m : ℕ, m + 3 = 5 → m = 2 := by
  obtain ⟨x, hx, hu⟩ := h
  intro m hm
  have := hu m hm
  omega

/-!
## 7. 经典逻辑：`by_cases`、`by_contra`、`push Not`、`contrapose!`、`tauto`

前面各节用到的规则（`→ ∧ ∨ ¬ ∃` 的引入与消去）都有现成的项（`fun`、`⟨_, _⟩`、`Or.inl`……），本身不需要
排中律。classical logic（经典逻辑）的核心是排中律 `p ∨ ¬p`，即核心库里的 `Classical.em`；`by_cases` 也是
核心库的策略，对任意命题可用，不需要 Mathlib。`by_cases h : p` 分情况讨论，两个目标的标签是 `pos`
（`h : p`）与 `neg`（`h : ¬p`）。`by_contra` 来自 Batteries（§5 引入的同一个模块）；Mathlib 提供围绕
否定的 `push Not`、`by_contra!`、`contrapose!` 与 `tauto`。
-/

example {p q : Prop} : (p → q) → (¬p → q) → q := fun hpq hnpq ↦ (Classical.em p).elim hpq hnpq

theorem by_cases_demo {p q : Prop} : (p → q) → (¬p → q) → q := by
  intro hpq hnpq
  by_cases hp : p
  -- 两个目标：`case pos`（`hp : p`）与 `case neg`（`hp : ¬p`），目标都是 `q`
  case pos => exact hpq hp
  case neg => exact hnpq hp

/-!
**反证法。** `by_contra h` 把目标 `p` 换成 `False`，同时加入假设 `h : ¬p`；当目标本身是否定 `¬q` 时，
它引入的是 `h : q`，而不是 `¬¬q`（下面第二个例子）。项模式的对应物是 `Classical.byContradiction`：
-/

example {p q : Prop} : (¬q → ¬p) → p → q :=
  fun h hp ↦ Classical.byContradiction fun hnq ↦ h hnq hp

theorem double_neg_elim {p : Prop} : ¬¬p → p := by
  intro hnn
  by_contra hn
  -- hnn : ¬¬p, hn : ¬p ⊢ False
  exact hnn hn

example {p q : Prop} (h : p → q) : ¬q → ¬p := by
  intro hnq
  by_contra hp
  -- h : p → q, hnq : ¬q, hp : p ⊢ False（不是 `hp : ¬¬p`）
  exact hnq (h hp)

/-!
经典推理要付出代价：`#print axioms`（第 3 章 §8.8）列出定理依赖的 axiom（公理）。`by_cases` 与 `by_contra`
都不是魔法，它们依赖的公理与第 3 章 `dne'` 里的 `Classical.byContradiction` 一样（`propext` 见第 3 章 §8.5，
机制见第 28 章）：
-/

/--
info: 'Lean4Learn.Ch04.by_cases_demo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms by_cases_demo

/--
info: 'Lean4Learn.Ch04.double_neg_elim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms double_neg_elim

/-!
**否定的整理：`push Not`。** 带量词的否定读起来别扭：`¬∀ x, p x` 在经典逻辑里等价于「存在 `x` 使
`¬p x`」。`push Not` 把 `¬` 推进量词与联结词里面（需要 `Mathlib.Tactic.Push`）；`at h` 指定作用在假设
`h` 上，不写就作用在目标上。每个例子最后的 `exact h` 能通过，说明目标与整理后的 `h` 形状一致。
`¬(p ∧ q)` 默认变成 `p → ¬q`；加 `+distrib` 才是 de Morgan 形式 `¬p ∨ ¬q`。
-/

example {α : Type*} {p : α → Prop} (h : ¬∀ x, p x) : ∃ x, ¬p x := by
  push Not at h  -- h : ∃ x, ¬p x
  exact h

example {p q : Prop} (h : ¬(p ∧ q)) : p → ¬q := by
  push Not at h  -- h : p → ¬q
  exact h

example {p q : Prop} (h : ¬(p ∧ q)) : ¬p ∨ ¬q := by
  push +distrib Not at h  -- h : ¬p ∨ ¬q
  exact h

/-!
> deprecation（弃用）提示：`push Not` 的前身 `push_neg` 在 Mathlib 2026-03-29 起弃用：现在写它得到警告，
> 但仍能用。网上和 LLM 给出的旧证明里大量出现 `push_neg`，读到时换成 `push Not`。
-/

/-- warning: `push_neg` has been deprecated. Prefer using `push Not` instead. -/
#guard_msgs (substring := true) in
example {α : Type*} {p : α → Prop} (h : ¬∀ x, p x) : ∃ x, ¬p x := by
  push_neg at h
  exact h

/-!
`by_contra!` 是「`by_contra` 之后对新假设 `push Not`」；`contrapose!` 把目标 `A → B` 换成它的
contrapositive（逆否命题）`¬B → ¬A`，并同样整理否定。第一个例子用 `trace_state` 看整理后的假设；
第二个例子最后的 `exact h` 能通过，说明目标恰好是 `(∀ x, q x) → ∀ x, p x`：
-/

/--
trace: α : Type u_1
p : α → Prop
h : ¬∀ (x : α), p x
hne : ∀ (x : α), p x
⊢ False
-/
#guard_msgs in
example {α : Type*} {p : α → Prop} (h : ¬∀ x, p x) : ∃ x, ¬p x := by
  by_contra! hne
  trace_state
  exact h hne

example {α : Type*} {p q : α → Prop} (h : (∀ x, q x) → ∀ x, p x) :
    (∃ x, ¬p x) → ∃ x, ¬q x := by
  contrapose!
  exact h

/-!
最后，`tauto` 在经典命题逻辑里证明重言式。它不告诉你证明的结构，学习阶段应当先手写，再用 `tauto` 核对：
-/

example {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  tauto

/-!
## 8. 中间步骤：`have`、`show`、`suffices`

证明变长时，要给中间结论起名、标明目标现在的形状，或先说清「只要证什么」。`have h : T := e` 在上下文中
加入假设 `h`（项模式见第 3 章）；`show T` 标明目标现在的样子；真要把目标改写成定义相等的另一种形状，
Mathlib 风格用 `change T`（用 `show` 改写目标会被 `linter.style.show` 报告，该 linter 默认关闭）；
`suffices h : T by tac` 说「只要证 `T`，因为由 `T` 能推出原目标（用 `tac` 证）」，随后主目标变成 `T`。
-/

example {p q r : Prop} (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  have hq : q := hpq hp  -- hq : q
  show r  -- 只是标明目标，没有改变它
  exact hqr hq

example {p : Prop} (h : p → False) : ¬p := by
  change p → False  -- `¬p` 与 `p → False` 定义相等
  exact h

example {p q r : Prop} (hpq : p → q) (hqr : q → r) (hp : p) : r := by
  suffices hq : q by exact hqr hq
  -- ⊢ q
  exact hpq hp

example {p q r : Prop} (hpq : p → q) (hqr : q → r) (hp : p) : r :=
  suffices hq : q from hqr hq; hpq hp

/-!
## 9. 组织多个目标：`<;>` 与策略组合子

`·` 与 `case` 已经在 §2、§3 用过：目标通常按参数的顺序排列，`case tag => tac` 不依赖顺序。
`t₁ <;> t₂`（对每个新目标运行）：运行 `t₁`，再对它产生的**每个**新目标运行 `t₂`。这类把策略接起来的
东西叫 tactic combinator（策略组合子）。另外两个常用的：`all_goals t` 对所有目标各运行 `t`，有一个失败
就整体失败；`try t` 在 `t` 失败时当作什么都没做。
-/

example {p q : Prop} (hp : p) (hq : q) : (p ∧ q) ∧ (q ∧ p) := by
  constructor <;> constructor <;> assumption

/--
error: Tactic `assumption` failed

case right
p q : Prop
hp : p
⊢ q
-/
#guard_msgs in
example {p q : Prop} (hp : p) : p ∧ q := by
  constructor
  all_goals assumption

example {p q : Prop} (hq : q) : q ∧ (p → p) := by
  constructor <;> try assumption
  exact fun h ↦ h

/-!
## 10. 常见错误

**1. 用 `_` 当作新目标。** `refine` 里没被合一解决的 `?_`（或具名的 `?h`）成为新目标；`_` 不会，填不出
就报 `don't know how to synthesize placeholder`。`refine ⟨_, _⟩` 是 Lean 3 的习惯。输出有多条错误，
`substring := true` 只要求输出里含有下面这一句：
-/

/-- don't know how to synthesize placeholder for argument `right` -/
#guard_msgs (substring := true) in
example {p q : Prop} (hp : p) (hq : q) : p ∧ q := by
  refine ⟨_, _⟩

/-!
**2. `apply` 合一失败。** 目标 `p` 与 `hqr : q → r` 的结论 `r` 对不上；完整的信息还列出 `hqr` 的完整类型
和当前证明状态：
-/

/-- Tactic `apply` failed: could not unify the conclusion of `hqr` -/
#guard_msgs (substring := true) in
example {p q r : Prop} (hqr : q → r) (hq : q) : p := by
  apply hqr
  exact hq

/-!
**3. 忘了处理某个目标。** `constructor` 产生两个目标，只关一个，另一个留在 `unsolved goals` 里，
标签 `right` 提示漏了哪一个：
-/

/--
error: unsolved goals
case right
p q : Prop
hp : p
hq : q
⊢ q
-/
#guard_msgs in
example {p q : Prop} (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp

/-!
## 练习

4.1–4.5、4.7、4.8、4.11 是第 3 章练习的**策略版本**，陈述相同；4.8 同时回头用第 2 章的 `omega`。
4.6、4.10 练习否定，4.9、4.13 练习 `∃!`，4.12 练习 `contrapose!`，4.14 练习 `<;>`，4.15 练习
`by_cases`。4.1–4.6 与 4.14 请手写，不要用 `tauto`。★ 直接应用，★★ 综合两个想法，★★★ 需要新想法
（策略版本按本章重新评估，4.11 因此比第 3 章的 3.15 少一颗星）。
-/

/-- 练习 4.1（★）：第 3 章练习 3.2 的策略版本：蕴含与合取；用 `intro` 与 `constructor`。 -/
theorem ex_4_1 {p q r : Prop} : (p → q) → (p → r) → p → q ∧ r := sorry

/-- 练习 4.2（★）：第 3 章练习 3.5 的策略版本：析取的结合律；用 `rintro` 与 `left`/`right`。 -/
theorem ex_4_2 {p q r : Prop} : p ∨ (q ∨ r) → (p ∨ q) ∨ r := sorry

/-- 练习 4.3（★★）：第 3 章练习 3.7 的策略版本：合取对析取的分配律；用 `constructor` 与 `rintro`。 -/
theorem ex_4_3 {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry

/-- 练习 4.4（★★）：第 3 章练习 3.8 的策略版本：`p` 与 `¬p` 不等价；用 `intro` 与 `have`。 -/
theorem ex_4_4 {p : Prop} : ¬(p ↔ ¬p) := sorry

/-- 练习 4.5（★★）：第 3 章练习 3.9 的策略版本：存在量词与析取；用 `rintro ⟨x, hx | hx⟩` 与 `use`。 -/
theorem ex_4_5 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

/-- 练习 4.6（★）：矛盾推出一切；先 `rintro ⟨hp, hnp⟩`，再试 `contradiction`，`exfalso` 也行。 -/
theorem ex_4_6 {p q : Prop} : p ∧ ¬p → q := sorry

/-- 练习 4.7（★）：第 3 章练习 3.10 的策略版本：用 `use`。 -/
theorem ex_4_7 : ∃ n : ℕ, n * n = 49 ∧ n + 1 = 8 := sorry

/-- 练习 4.8（★★）：第 3 章练习 3.13 的策略版本：`intro`、`use`，再用 `omega` 收尾。 -/
theorem ex_4_8 : ∀ n : ℕ, n < 5 → ∃ k : ℕ, k + n = 5 := sorry

/-- 练习 4.9（★★）：`∃!` 的引入：先给见证，再证唯一性；用 `refine` 与 `omega`。 -/
theorem ex_4_9 : ∃! n : ℕ, 2 * n + 1 = 7 := sorry

/-- 练习 4.10（★★）：存在量词的否定。不用 `push Not`，手工用 `intro`/`rintro`。 -/
theorem ex_4_10 {α : Type*} {p : α → Prop} : (¬∃ x, p x) ↔ ∀ x, ¬p x := sorry

/-- 练习 4.11（★★）：第 3 章练习 3.15 的策略版本：只用 `by_contra`（要用两次）、`intro`、`apply`、
`exact` 手工证明（§7 给出了 `push Not` 与 `by_contra!` 的写法，可以对照）。 -/
theorem ex_4_11 {α : Type*} {p : α → Prop} : ¬(∀ x, p x) → ∃ x, ¬p x := sorry

/-- 练习 4.12（★★）：用 `contrapose!` 证明；之后目标是一个蕴含，再用 `intro`。 -/
theorem ex_4_12 {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, ¬q x) → ∃ x, ¬p x := sorry

/-- 练习 4.13（★★）：`∃!` 的消去：满足性质的两个元素相等；用 `obtain` 拆开 `∃!`。 -/
theorem ex_4_13 {α : Type*} {p : α → Prop} (h : ∃! x, p x) (a b : α) (ha : p a) (hb : p b) :
    a = b := sorry

/-- 练习 4.14（★）：组合子：`rintro` 拆开假设之后，用 `constructor <;> constructor <;> assumption`。 -/
theorem ex_4_14 {p q r : Prop} : p ∧ q ∧ r → (r ∧ q) ∧ (q ∧ p) := sorry

/-- 练习 4.15（★★★）：「酒鬼悖论」：在非空的论域里，总有一个人，如果他在喝酒，那么所有人都在喝酒。
提示：对 `∀ y, D y` 做 `by_cases`。 -/
theorem ex_4_15 {α : Type*} (a : α) (D : α → Prop) : ∃ x, D x → ∀ y, D y := sorry

/-!
## 小结

| 概念 | 策略 / 项模式 | 何时用 |
|---|---|---|
| 证明状态 / 策略拼出的项 | `trace_state` / `show_term` | 想看当前目标，或想把策略证明还原成项 |
| `→`、`∀` 引入 | `intro x`、`rintro` / `fun x ↦ …` | 目标是蕴含或全称量词 |
| 用已知项 / 倒推 | `exact`、`assumption`、`apply f`、`refine f ?_` / `e`、`f _` | 现成项用 `exact`，倒推用 `apply` |
| `∧` | `constructor`、`⟨?_, ?_⟩`、`obtain ⟨a, b⟩ := h` / `⟨a, b⟩`、`h.1` | 目标或假设是合取 |
| `↔` | `constructor`（`mp`、`mpr`）、`h.mp` / `⟨mp, mpr⟩` | 两个方向分别证 |
| `∨` | `left`、`right`、`rcases h with a \| b`、`rintro (a \| b)` / `Or.inl`、`h.elim` | 引入选一边；消去两边都要证 |
| `¬`、`False` | `intro`、`exfalso`、`contradiction`、`absurd` / `False.elim` | 已有矛盾，或证否定 |
| `∃` | `use w`、`exists w`、`obtain ⟨w, hw⟩ := h` / `⟨w, h⟩` | `use` 自动关 `rfl` 等；`obtain` 拆假设 |
| `∃!` | `refine ⟨w, h, ?_⟩`、`obtain ⟨x, hx, hu⟩ := h` / `ExistsUnique.intro` | 证唯一性；使用唯一性 |
| 分情况 / 反证 | `by_cases h : p`、`by_contra h` / `Classical.em`、`Classical.byContradiction` | 需要经典逻辑 |
| 整理否定 | `push Not (at h)`、`by_contra!`（`push_neg` 已弃用） | 否定在量词外面，想变成肯定形式 |
| 逆否命题 | `contrapose!` | 反方向的蕴含更好证 |
| 命题逻辑重言式 | `tauto` | 核对手写的命题逻辑证明 |
| 中间步骤 | `have`、`show`、`change`、`suffices h : T by tac` | 给中间结论起名；标明或改写目标；先说清只要证什么 |
| 组织目标 | `·`、`case tag =>`、`<;>`、`all_goals`、`try` | 一条策略产生了多个目标 |

## 延伸阅读

- *Theorem Proving in Lean 4*：第 5 章「Tactics」（§5.1–§5.5）；第 3 章 §3.5「Classical Logic」。
- *Mathematics in Lean*：第 3 章「Logic」（§3.1 蕴含与全称量词、§3.2 存在量词、§3.3 否定、
  §3.4 合取与 Iff、§3.5 析取）。
- *Lean Language Reference* 4.35.0（`https://lean-lang.org/doc/reference/4.35.0/`）：第 14 章「Tactic Proofs」
  的 14.2「Reading Proof States」与 14.3「The Tactic Language」。
- 源码：核心库 `Init/Tactics.lean`、`Init/RCases.lean`（模式语法的文档注释）；Batteries
  `Batteries/Tactic/Init.lean`（`by_contra`、`absurd`）；Mathlib `Mathlib/Tactic/` 下的 `Push.lean`
  （含弃用的 `push_neg`）、`ByContra.lean`、`Contrapose.lean`、`Use.lean`、`Tauto.lean`，以及
  `Mathlib/Basic/ExistsUnique.lean`。
- 本书第 3 章（项模式写法）、第 5 章（`rw`、`simp`、`calc`）、第 6 章（`cases`、`induction`、模式匹配）。
-/

end Lean4Learn.Ch04

end
