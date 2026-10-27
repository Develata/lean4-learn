module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public meta import Lean.Meta.Reduce
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.TypeStar

/-!
# 第 28 章　类型论与内核机制

本章把前面各章留下的「机制见第 28 章」一次交代清楚：Lean 的类型论由哪几条规则组成，kernel（内核）检查什么、
不检查什么，elaborator（精译器；另译繁饰器）在内核之前替你做了什么，以及你每天遇到的现象（`rfl` 失败、
instance（实例）找不到、`decide` 卡住、`@[expose]` 报错）各自对应哪一层。

## 学习目标
- 能判断一个错误出在精译器还是内核，并选对 transparency（透明度）；
- 能读懂 `#print axioms`，说清 `Prop` 的三条特殊性质（proof irrelevance（证明无关性）、impredicative
  （非直谓的）、restricted elimination（受限的消去））和 `Quot` 的作用；
- 能解释 `decide` 与 `decide +kernel` 的差别、instance synthesis（实例合成）与 coercion（强制转换）
  在精译器里怎样运行；
- 知道 `module` 文件的可见性规则，以及一份 Lean 证明在什么意义上「可信」。

## 前置知识
第 3 章（`Prop`、`Type`、依值函数、`#print axioms` 的预览）、第 5 章（`rfl` 与 definitional equality（定义相等）、
`decide +kernel`）、第 6 章（inductive type（归纳类型）、structural recursion（结构递归）与
well-founded recursion（良基递归））、第 7 章（`Subtype`、`Classical.choose`）、
第 8、15 章（type class（类型类））、第 12 章（`decide +kernel` 与 `decide` 的比较）、第 25 章（`native_decide`）、
第 27 章（`MetaM`、`whnf`、`isDefEq`）。本章的少数演示用 `MetaM` 做实验：每个这样的演示前面都说明哪几行
是重点（`withTransparency`、`addDecl`、`isDefEq`），其余样板可以略读。

**证据约定。** 本章的行为性断言，除下面三类外，都有同文件里编译通过的例子紧挨着它（报错由 `#guard_msgs`
固定）：（一）§15 的多文件演示放在 `examples/modprobe/`，那里的输出是逐字摘录，不由 `#guard_msgs` 检查；
（二）引自 Lean 参考手册或 Lean 源码的说法，在正文里注明出处与「本章不复现」；（三）引自发行说明、本机不能
复现的说法，同样注明。
-/

@[expose] public section

namespace Lean4Learn.Ch28

universe u v

/-!
## 1. 依值类型：Π 与 Σ

类型论要回答的第一个问题是：返回值的类型能不能依赖参数的值？「长度为 `n` 的向量」「第 `n` 个元素」都需要这样
的类型，即 dependent type（依值类型），所以 Lean 的函数类型一开始就是依值的。

Pi type / dependent function type（Π 类型（依值函数类型））`(a : α) → β a`：返回类型依赖参数。
`∀ x, p x` 是它在 `β a : Prop` 时的写法，普通函数类型 `α → β` 是 `β` 不依赖 `a` 的特例，三者是同一个构造
（第 3 章 §8.6）。Sigma type / dependent pair（Σ 类型（依值对））`(a : α) × β a`：第二个分量的类型
依赖第一个分量的值。
-/

/-- 依值函数：返回类型 `Fin (n + 1)` 依赖参数 `n`。 -/
def lastFin : (n : ℕ) → Fin (n + 1) := fun n ↦ Fin.last n

/-- info: (n : ℕ) → Fin (n + 1) : Type -/
#guard_msgs in #check (n : ℕ) → Fin (n + 1)

example : (∀ _ : ℕ, ℕ) = (ℕ → ℕ) := rfl
example : lastFin 3 = Fin.last 3 := rfl

/-- 依值对：第二个分量 `2 : Fin (3 + 1)` 的类型由第一个分量 `3` 决定。 -/
def sigEx : (n : ℕ) × Fin (n + 1) := ⟨3, 2⟩

/-- info: (n : ℕ) × Fin (n + 1) : Type -/
#guard_msgs in #check (n : ℕ) × Fin (n + 1)

example : sigEx.1 = 3 := rfl

/-!
`Σ` 有三个常用的变体，区别只在「第二个分量是数据还是证明」与「整体住在哪个宇宙」：
`Sigma`（两个分量都是数据）、`Subtype`（第二个分量是证明，所以只是 `α` 的子类型）、`Exists`（整体是
`Prop`，见证不能被取出，§3）。三者的 constructor（构造子）形状相同（先给第一个分量，再给依赖于它的第二个分量），区别只在
各个分量与整体住在哪个宇宙：
-/

/-- info: @Sigma.mk : {α : Type u_1} → {β : α → Type u_2} → (fst : α) → β fst → Sigma β -/
#guard_msgs in #check @Sigma.mk
/-- info: @Subtype.mk : {α : Sort u_1} → {p : α → Prop} → (val : α) → p val → Subtype p -/
#guard_msgs in #check @Subtype.mk
/-- info: @Exists.intro : ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p -/
#guard_msgs in #check @Exists.intro

/-!
## 2. 宇宙

类型本身也是项，所以它们也要有类型；若让「所有类型的类型」是它自己，会推出矛盾（Girard 悖论）。
解法是把类型分层：`Sort u` 是第 `u` 层 universe（宇宙）；`Prop := Sort 0`，`Type u := Sort (u + 1)`。每个宇宙
是下一层的一个 inhabitant（居留者）。`Prop : Type`、`Type : Type 1` 与无累积性的报错见第 3 章 §4、§7；这里补上
函数类型的 `imax` 规则和 `ULift`/`PLift`。
-/

/-- info: Sort u : Type u -/
#guard_msgs in #check Sort u

example : Sort 5 := Sort 4

/-!
**函数类型的宇宙。** `Type` 层是 predicative（直谓的）：
函数类型的宇宙是定义域与值域宇宙的 `max`。`Prop` 层是 impredicative（非直谓的）：只要值域是 `Prop`，不管定义域
多大，整体仍在 `Prop`。
统一的规则是 `(a : α) → β a : Sort (imax u v)`，其中 `imax u 0 = 0`，否则 `imax u v = max u v`：
-/

/-- info: Type u → Type v : Type (max (u + 1) (v + 1)) -/
#guard_msgs in #check Type u → Type v
/-- info: fun α β ↦ (a : α) → β a : (α : Sort u) → (α → Sort v) → Sort (imax u v) -/
#guard_msgs in #check fun (α : Sort u) (β : α → Sort v) ↦ (a : α) → β a

/-- 值域是 `Type`：定义域 `Type 3` 把整体推到 `Type 4`（取 `max`）。 -/
example : Type 4 := ∀ (α : Type 3), α → α

/-- 非直谓性：`∀` 跨过 `Type 3`，整体仍是 `Prop`（练习 28.3 用到它）。 -/
example : Prop := ∀ (α : Type 3) (a : α), a = a

/--
error: Type mismatch
  α → β
has type
  Type 2
of sort `Type 3` but is expected to have type
  Type 1
of sort `Type 2`
-/
#guard_msgs in
example (α : Type 2) (β : Type 1) : Type 1 := α → β

example (α : Type 2) (β : Type 1) : Type 2 := α → β

/-!
**没有累积性**（`ℕ : Type` 不会自动成为 `Type 1` 的居留者，报错见第 3 章 §7）。要抬升宇宙，用
`ULift.{r} : Type s → Type (max s r)`（构造子 `ULift.up`，字段 `down`）；`PLift : Sort u → Type u` 把命题
抬成类型：
-/

example : Type 1 := ULift.{1} ℕ
example : (ULift.up 3 : ULift.{1} ℕ).down = 3 := rfl

/-- info: PLift : Sort u_1 → Type u_1 -/
#guard_msgs in #check @PLift

/-!
universe polymorphism（宇宙多态；`Type*`，见第 3 章 §7；返回类型里的 `Type _` 由 unification（合一）
解出）。每个宇宙实例化是一个不同的类型，住在不同的宇宙里，所以它们之间不能直接比较（报错显示
`Wrap (ULift ℕ)` 在 `Type 1`，而左边在 `Type`）：
-/

def Wrap (α : Type*) : Type _ := List α

/--
error: Type mismatch
  Wrap (ULift ℕ)
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1`
-/
#guard_msgs in
example : Wrap.{0} ℕ = Wrap.{1} (ULift ℕ) := rfl

/-!
## 3. `Prop`：证明无关性与子单点消去

为什么要把 `Prop` 单独做成一层？因为数学里的证明只关心「有没有」，不关心「怎么证的」。参考手册 4.2 列出
`Prop` 与 `Type` 不同的几条性质（还有「证明在编译后的代码里被擦除」等，本章不复现）；本章用到其中三条：
**证明无关性**（proof irrelevance）、**非直谓性**（§2）、以及**受限的消去**（restricted elimination）。先看
第一条：同一命题的任意两个证明**定义相等**，内核在比较两个项时，只要发现它们的类型是命题就直接判相等，
不再看项的内容。（第 3 章 §9 用过它，§8 用过 `Or` 与 `Exists` 的消去；这里给出判据。）
-/

example (h₁ h₂ : 0 < 1) : (⟨1, h₁⟩ : {n : ℕ // 0 < n}) = ⟨1, h₂⟩ := rfl

/-!
**受限的消去。** 一个归纳类型 `T` 的 recursor（递归子）`T.rec` 的 motive 可以落在哪个宇宙，由 `T` 自己决定。
`And` 的递归子 motive 是 `Sort u`，`Or` 与 `Exists` 的只能是 `Prop`（`#check` 里看 `motive` 的类型）：
-/

/--
info: @And.rec : {a b : Prop} → {motive : a ∧ b → Sort u_1} → ((left : a) → (right : b) → motive ⋯)
→ (t : a ∧ b) → motive t
-/
#guard_msgs in #check @And.rec
/--
info: @Or.rec : ∀ {a b : Prop} {motive : a ∨ b → Prop},
  (∀ (h : a), motive ⋯) → (∀ (h : b), motive ⋯) → ∀ (t : a ∨ b), motive t
-/
#guard_msgs in #check @Or.rec
/--
info: @Exists.rec : ∀ {α : Sort u_1} {p : α → Prop} {motive : Exists p → Prop},
  (∀ (w : α) (h : p w), motive ⋯) → ∀ (t : Exists p), motive t
-/
#guard_msgs in #check @Exists.rec

/-!
判据（参考手册「归纳类型」一章的 Subsingleton Elimination 一节；精确条件见上游内核源码
`src/kernel/inductive.cpp` 第 483–536 行，`v4.35.0` 标签，本地工具链不带它，本章不复现）：一个住在 `Prop` 里的
归纳类型可以消去到任意 `Sort`（这叫子单点消去：subsingleton（子单点类型）即至多一个居留者的类型），当且仅当

- 它至多有一个构造子，且不在互递归块里；
- 排除类型自己的参数之后，构造子的每个字段，要么本身是证明，要么**本身就是**构造子结果类型里的某一个下标
  （那个下标位置上恰好是这个字段变量；只在某个下标的表达式里出现不算）。参数是类型签名里冒号前、各构造子
  共用的变量；下标是冒号后的、各构造子可以取不同值的位置（下面 `Hidden : ℕ → Prop` 的那个 `ℕ`）。

`False`（零个构造子）、`True`、`And`（字段全是证明）满足；`Eq` 也满足，因为排除参数 `α`、`a` 之后
`Eq.refl` 没有字段（见下面的 `#check @Eq.rec`：`a` 是参数，下标是 `a_1`）。`Or`（两个构造子）与 `Exists`
（字段 `w : α` 既不是证明，也不是下标）不满足。直观原因：若能从 `p ∨ q` 里算出一个 `Bool` 告诉你是哪一边，
证明无关性就会让 `Or.inl h` 与 `Or.inr h'` 定义相等，而 `true ≠ false`，矛盾。看实例：
-/

-- 允许：`And.rec` 把两个证明消去成数据；`Eq.rec` 沿等式转运数据（`▸`）；`False` 零个构造子。
example (p q : Prop) (h : p ∧ q) : ℕ := And.rec (motive := fun _ ↦ ℕ) (fun _ _ ↦ 5) h
example (n m : ℕ) (h : n = m) (x : Fin n) : Fin m := h ▸ x
example (h : False) : ℕ := h.elim

/--
info: @Eq.rec : {α : Sort u_2} →
  {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u_1} → motive a ⋯ → {a_1 : α} → (t : a = a_1) → motive a_1 t
-/
#guard_msgs in #check @Eq.rec

-- `Exists.rec` 不允许把 motive 取成 `ℕ`，所以不能凭 `∃ n, 0 < n` 取出那个 `n`：
/--
error: Type mismatch
  ℕ
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type`
-/
#guard_msgs in
example (h : ∃ n : ℕ, 0 < n) : ℕ := Exists.rec (motive := fun _ ↦ ℕ) (fun n _ ↦ n) h

/-!
用自造的命题逐条对照第二个条件。`PField` 的字段 `a : α` 的类型只是类型的参数，字段本身既不是证明也不是
下标；`Hidden` 的字段 `n` 出现在下标 `n + 1` 里，但那个下标位置上不是 `n` 本身。两者的递归子都只能消去到
`Prop`（看 `motive` 的类型）：
-/

inductive PField (α : Type) : Prop where
  | mk (a : α) : PField α

inductive Hidden : ℕ → Prop where
  | mk (n : ℕ) : Hidden (n + 1)

/--
info: @PField.rec : ∀ {α : Type} {motive : PField α → Prop}, (∀ (a : α), motive ⋯) → ∀ (t : PField α), motive t
-/
#guard_msgs in #check @PField.rec
/--
info: @Hidden.rec : ∀ {motive : (a : ℕ) → Hidden a → Prop},
  (∀ (n : ℕ), motive (n + 1) ⋯) → ∀ {a : ℕ} (t : Hidden a), motive a t
-/
#guard_msgs in #check @Hidden.rec

/-!
`Direct` 的下标位置上恰好是字段 `n`，于是 `motive` 可以落在任意 `Sort u_1`。注意 Lean 默认会把「每个构造子里
都是变量」的下标自动提升为参数（选项 `inductive.autoPromoteIndices`），提升之后 `mk` 没有字段，和 `Eq` 同类
（下面的 `Promo`）；为了看第二个条件本身，`Direct` 关掉了提升：
-/

set_option inductive.autoPromoteIndices false in
inductive Direct : ℕ → Prop where
  | mk (n : ℕ) : Direct n

inductive Promo : ℕ → Prop where
  | mk (n : ℕ) : Promo n

/--
info: @Direct.rec : {motive : (a : ℕ) → Direct a → Sort u_1} → ((n : ℕ) → motive n ⋯) → {a : ℕ} → (t : Direct a) → motive a t
-/
#guard_msgs in #check @Direct.rec
/--
info: @Promo.rec : {a : ℕ} → {motive : Promo a → Sort u_1} → motive ⋯ → (t : Promo a) → motive t
-/
#guard_msgs in #check @Promo.rec

/-!
**出路是公理。** `Classical.choice : Nonempty α → α` 是一条公理，它让 `Classical.choose` 能从
`∃` 里取出一个见证；代价是定义变成不可计算（§14），并且 `#print axioms` 会显示它。
-/

noncomputable def pick (h : ∃ n : ℕ, 3 < n) : ℕ := Classical.choose h

theorem pick_spec (h : ∃ n : ℕ, 3 < n) : 3 < pick h := Classical.choose_spec h

/-- info: 'Lean4Learn.Ch28.pick' depends on axioms: [Classical.choice] -/
#guard_msgs in #print axioms pick

/-!
## 4. 归纳类型、递归子与结构 eta

除了 §5 的内核原语 `Quot`，内核「造新类型」的方式只有归纳类型一种（`structure`、`Nat`、`List`、`Eq` 都是它的
特例），所以它必须知道怎样消去一个归纳类型的项。每个归纳类型 `T` 由内核自动配一个递归子 `T.rec`，它的类型完全由 `T` 的
签名与构造子的签名决定，并附带 reduction（规约）规则（ι 规约）。`#print` 能把规则打出来：
-/

/--
info: recursor Nat.rec.{u} {motive : ℕ → Sort u} (zero : motive Nat.zero) (succ : (n : ℕ) → motive
n → motive n.succ)
  (t : ℕ) : motive t
number of parameters: 0
number of motives: 1 (position 1)
number of minor premises: 2 (positions 2–3)
number of indices: 0
major premise position: 4
rules:
  Nat.rec zero succ Nat.zero
    ==> zero
  Nat.rec zero succ n.succ
    ==> succ n (Nat.rec zero succ n)
-/
#guard_msgs in #print Nat.rec

/-!
`casesOn`、`recOn`、`below`、`brecOn`、`noConfusion` 等不是内核原语，是 Lean 核心代码在 `rec` 之上生成的
辅助定义。`#print` 能看到 `casesOn` 的定义体就是 `rec`；结构递归的函数经 `brecOn` 编译（`below` 把
所有递归调用的结果打包成一个值，`brecOn` 把它喂给函数体），下面的 `dbl` 打印出来就是 `Nat.brecOn`：
-/

/--
info: @[reducible, expose] def Nat.casesOn.{u} : {motive : ℕ → Sort u} →
  (t : ℕ) → motive Nat.zero → ((n : ℕ) → motive n.succ) → motive t :=
fun {motive} t zero succ ↦ Nat.rec zero (fun n n_ih ↦ succ n) t
-/
#guard_msgs in #print Nat.casesOn

def dbl : ℕ → ℕ
  | 0 => 0
  | n + 1 => dbl n + 2

/--
info: @[expose] def Lean4Learn.Ch28.dbl : ℕ → ℕ :=
fun x ↦ Nat.brecOn x dbl._f
-/
#guard_msgs in #print dbl

/-!
**结构 eta。** 单构造子、无下标、**非递归**的结构体（`Prod`、普通 `structure`）满足：
`S.mk x.f₁ x.f₂ ≡ x`，不需要对 `x` 分情况。内核与精译器都内置这条规则；没有字段的结构体里，任意两个
元素都定义相等。**递归**结构体（字段类型里出现它自己，包括 `Option Lst` 这样的嵌套出现）没有这条规则：
-/

example (p : ℕ × ℕ) : (p.1, p.2) = p := rfl
example (a b : Unit) : a = b := rfl

structure Lst where
  hd : ℕ
  tl : Option Lst

/--
error: Tactic `rfl` failed: The left-hand side
  { hd := x.hd, tl := x.tl }
is not definitionally equal to the right-hand side
  x

x : Lst
⊢ { hd := x.hd, tl := x.tl } = x
-/
#guard_msgs in
example (x : Lst) : Lst.mk x.hd x.tl = x := by rfl

-- 没有 eta 时先分情况，之后两边都是构造子，`rfl` 照常成立：
example (x : Lst) : Lst.mk x.hd x.tl = x := by cases x; rfl

/-!
## 5. 商类型 `Quot`

归纳类型造不出「把若干元素粘成一个」的类型，而数学处处要商（整数是自然数对模去一个关系，商群，……）。
所以内核另外内置了 quotient type（商类型）：类型 `Quot r`（`r` 是任意二元关系），加三个常量
`Quot.mk`（引入）、`Quot.lift`（消去：只能用**尊重 `r`** 的函数）、`Quot.ind`（归纳原理），再加一条公理
`Quot.sound : r a b → Quot.mk r a = Quot.mk r b`（`Quotient` 一层的用法见第 15 章 §7）。内核里还有一条
规约规则：`Quot.lift f h (Quot.mk r a) ≡ f a`（商的 ι 规约）。但 `Quot.mk r a` 与 `Quot.mk r b` 的相等只由
`Quot.sound` 给出，是 propositional equality（命题相等），不是定义相等：
-/

example (r : ℕ → ℕ → Prop) (f : ℕ → ℕ) (h : ∀ a b, r a b → f a = f b) (a : ℕ) :
    Quot.lift f h (Quot.mk r a) = f a := rfl

example : Quot.mk (fun a b : ℕ ↦ a % 2 = b % 2) 0 = Quot.mk _ 2 := Quot.sound rfl

/--
error: Tactic `rfl` failed: The left-hand side
  Quot.mk (fun a b ↦ a % 2 = b % 2) 0
is not definitionally equal to the right-hand side
  Quot.mk (fun a b ↦ a % 2 = b % 2) 2

⊢ Quot.mk (fun a b ↦ a % 2 = b % 2) 0 = Quot.mk (fun a b ↦ a % 2 = b % 2) 2
-/
#guard_msgs in
example : Quot.mk (fun a b : ℕ ↦ a % 2 = b % 2) 0 = Quot.mk _ 2 := by rfl

/-!
`Quotient`、`Setoid`、`QuotientGroup` 都建在 `Quot` 之上。

## 6. 公理

内核的规则管不到的数学事实（命题外延、选择）只能靠 axiom（公理）。Mathlib 式数学的标准公理基础是三条：
`propext`（命题外延性）、`Classical.choice`、`Quot.sound`。这是一种约定，不是语言的限制：Lean 允许任何人用
`axiom` 声明新公理，`sorry` 留下 `sorryAx`，`native_decide` 每用一次添一条专属公理（第 23 章 §5 演示了后两者）。
所以内核接受一个定理，并不说明它只依赖这三条，要用 `#print axioms 定理` 审计：它列出一个定理**传递地**依赖的
全部公理。`#print` 能显示公理的陈述：
-/

/-- info: axiom propext : ∀ {a b : Prop}, (a ↔ b) → a = b -/
#guard_msgs in #print propext
/-- info: axiom Classical.choice.{u} : {α : Sort u} → Nonempty α → α -/
#guard_msgs in #print Classical.choice

theorem ax_none : 1 + 1 = 2 := rfl
theorem ax_propext (p q : Prop) : (p ∧ q) = (q ∧ p) := propext and_comm
theorem ax_kernel : 2 ^ 100 % 7 = 2 := by decide +kernel

/-- info: 'Lean4Learn.Ch28.ax_none' does not depend on any axioms -/
#guard_msgs in #print axioms ax_none
/-- info: 'Lean4Learn.Ch28.ax_propext' depends on axioms: [propext] -/
#guard_msgs in #print axioms ax_propext
-- `decide +kernel` 不引入公理（对比第 25 章的 `native_decide`）：
/-- info: 'Lean4Learn.Ch28.ax_kernel' does not depend on any axioms -/
#guard_msgs in #print axioms ax_kernel

/-!
函数外延性 `funext` 不是公理，是由 `Quot.sound` 推出的定理；排中律是由 `Classical.choice` 加上另外两条
推出的（Diaconescu 定理）。核心库里这两个定理的 `#print axioms` 证实了这一点：
-/

/-- info: 'funext' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms funext
/-- info: 'Classical.em' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Classical.em

/-!
## 7. 定义相等

内核判两个项**定义相等**时用的规则（参考手册第 4 章）：

| 规则 | 含义 | 本章演示 |
|---|---|---|
| β | `(fun x ↦ b) a ≡ b[a/x]` | 下面 |
| δ | 展开定义 | 下面、§8 |
| ι | 递归子作用在构造子上 | §4 `#print Nat.rec`，下面 |
| ζ | `let x := v; b ≡ b[v/x]` | 下面 |
| η | `fun x ↦ f x ≡ f`；结构 eta | 下面、§4 |
| 商 | `Quot.lift f h (Quot.mk r a) ≡ f a` | §5 |
| 证明无关性 | 同一命题的两个证明相等 | §3 |

`with_reducible rfl` 只展开 `@[reducible]` 的定义，别的 `def` 一律不动。所以普通 `def` 的 δ 在它下面做不到，
能通过的是 β、ζ、η、ι、商规则，以及 `@[reducible]` 常量的 δ（透明度见 §8；`whnf` 与 `#reduce` 见 §9）：
-/

example (a : ℕ) : (fun x : ℕ ↦ x) a = a := by with_reducible rfl
example (a : ℕ) : (let x := a; x) = a := by with_reducible rfl
example (f : ℕ → ℕ) : (fun x ↦ f x) = f := by with_reducible rfl
example : Nat.rec (motive := fun _ ↦ ℕ) 5 (fun _ ih ↦ ih) (Nat.succ Nat.zero) = 5 := by
  with_reducible rfl

/-!
δ 要看 transparency（透明度，§8 详述）。普通 `def` 在默认透明度下展开，在 `with_reducible` 下不展开；加
`@[reducible]`（`abbrev` 就是它）就展开；`@[irreducible]` 连默认透明度都不展开，但内核**不看**这个标记：
-/

def kk : ℕ := 3
@[reducible] def kkR : ℕ := 3
@[irreducible] def secret : ℕ := 5

example : kk = 3 := rfl
example : kkR = 3 := by with_reducible rfl

/--
error: Tactic `rfl` failed: The left-hand side
  kk
is not definitionally equal to the right-hand side
  3

⊢ kk = 3
-/
#guard_msgs in
example : kk = 3 := by with_reducible rfl

/--
error: Tactic `rfl` failed: The left-hand side
  secret
is not definitionally equal to the right-hand side
  5

⊢ secret = 5
-/
#guard_msgs in
example : secret = 5 := by rfl

example : secret = 5 := by with_unfolding_all rfl
example : secret = 5 := by decide +kernel

/-!
同一条规则也决定 `simp` 的重写能否匹配：`simp` 用 `reducible` 透明度比较，`h : P kk` 作为重写规则
匹配不上目标里的 `P 3`，`h : P kkR` 却可以：
-/

/-- error: `simp` made no progress -/
#guard_msgs in
example (P : ℕ → Prop) (h : P kk) : P 3 := by simp only [h]

example (P : ℕ → Prop) (h : P kkR) : P 3 := by simp only [h]

/-!
第 5 章 §2 见过 `n + 0 = n` 是 `rfl`、`0 + n = n` 不是（`Nat.add` 对第二个参数递归）。`#reduce`（规约到底，
§9）能看到 `0 + n` 卡在哪里：它被展开成对 `n` 的递归子（输出里的 `⟨_, _⟩` 配对是结构递归的 `below` 编码，
§4），而 `n` 是变量，ι 规约无从进行：
-/

/-- info: fun n ↦ n -/
#guard_msgs in #reduce fun n : ℕ ↦ n + 0
/--
info: fun n ↦ (Nat.rec ⟨fun x ↦ x, PUnit.unit⟩ (fun n n_ih ↦ ⟨fun x ↦ (n_ih.1 x).succ, n_ih⟩) n).1 0
-/
#guard_msgs in #reduce fun n : ℕ ↦ 0 + n

/-!
## 8. 透明度梯级

精译器里的 `whnf`（§9）与 `isDefEq` 受**透明度**控制，一共六级，从严到宽是
`none < reducible < instances < implicit < default < all`。定义侧有五个属性，各自在哪一级开始被展开：
`@[reducible]`（`reducible`）、`@[instance_reducible]`（`instances`；`instance` 命令自动添加，见下面的
`#print`）、`@[implicit_reducible]`（`implicit`，比较隐式参数时用）、普通 `def`（`default`，即
`@[semireducible]`）、`@[irreducible]`（只有 `all`）。下面造五个探针定义，对每个透明度做 `whnf`，列出哪些
被展开（`✓`）：
-/

@[reducible] def pR : Bool := true
@[instance_reducible] def pI : Bool := true
@[implicit_reducible] def pM : Bool := true
def pD : Bool := true
@[irreducible] def pX : Bool := true

open Lean Meta in
/--
info: none: · · · · ·
---
info: reducible: ✓ · · · ·
---
info: instances: ✓ ✓ · · ·
---
info: implicit: ✓ ✓ ✓ · ·
---
info: default: ✓ ✓ ✓ ✓ ·
---
info: all: ✓ ✓ ✓ ✓ ✓
-/
#guard_msgs in
#eval show MetaM Unit from do
  let modes : List (String × TransparencyMode) :=
    [("none", .none), ("reducible", .reducible), ("instances", .instances),
     ("implicit", .implicit), ("default", .default), ("all", .all)]
  for (nm, m) in modes do
    let mut row := s!"{nm}:"
    for c in [``pR, ``pI, ``pM, ``pD, ``pX] do
      let r ← withTransparency m (whnf (mkConst c))
      row := row ++ (if r.isConstOf ``Bool.true then " ✓" else " ·")
    logInfo row

/-!
列是 `pR pI pM pD pX`。每一级恰好比上一级多展开一类，梯级的名字就是这样来的。策略层面的包装分别是
`with_unfolding_none`、`with_reducible`、`with_reducible_and_instances`、`with_implicit`、
（默认）、`with_unfolding_all`：
-/

example : pI = true := by with_reducible_and_instances rfl
example : pM = true := by with_implicit rfl
example : pD = true := rfl

/-!
`instance` 命令确实自动加 `@[instance_reducible]`（`#print` 能看到属性）：
-/

/--
info: @[instance_reducible, expose] def instAddNat : Add ℕ :=
{ add := Nat.add }
-/
#guard_msgs in #print instAddNat

/-!
谁用哪一级：

- `simp` 与 `rw` 比较项时用 `reducible`：上面 `simp only [h]` 只对 `kkR` 成功；`rw` 改写之后也只用
  `with_reducible rfl` 尝试收尾（见「常见错误」1）。
- `exact`、`decide` 与 `rfl` 策略用 `default`：上面的 `kk = 3 := rfl`、`pD = true := rfl`。
- 实例合成用 `instances` 一级：普通 `def` 起的别名不会被展开（「常见错误」2）。这一条的出处是
  `Lean/Meta/SynthInstance.lean` 里对透明度的设置，本章不复现。
- `with_unfolding_all` 把 `@[irreducible]` 也展开（上面的 `secret`）。

**良基递归与透明度。** 第 6 章 §9 演示过：良基递归的函数默认 `@[irreducible]`，`decide` 卡住，`decide +kernel`
与 `simp [f]` 能绕过，`@[semireducible]` 只在 termination measure（度量）取 `ℕ` 值时有效。机制在精译器交给内核的定义体上：度量取 `ℕ`
值时（`half`），定义体是 `WellFounded.Nat.fix`；其他度量（`half2` 的 `(n, 0)`）是 `WellFounded.fix`（`#print`
写成 `half2._proof_1.fix`，`half2._proof_1` 是良基性的证明）。结构递归（§4 的 `dbl`）不受影响：
-/

example : dbl 5 = 10 := by decide

def half (n : ℕ) : ℕ := if n < 2 then 0 else half (n - 2) + 1
termination_by n
decreasing_by omega

def half2 (n : ℕ) : ℕ := if n < 2 then 0 else half2 (n - 2) + 1
termination_by (n, 0)

/--
info: @[irreducible, expose] def Lean4Learn.Ch28.half : ℕ → ℕ :=
WellFounded.Nat.fix (fun x ↦ x) fun n a ↦ if h : n < 2 then 0 else a (n - 2) ⋯ + 1
-/
#guard_msgs in #print half
/--
info: @[irreducible, expose] def Lean4Learn.Ch28.half2 : ℕ → ℕ :=
half2._proof_1.fix fun n a ↦ if h : n < 2 then 0 else a (n - 2) ⋯ + 1
-/
#guard_msgs in #print half2

/-!
按 `Init/WF.lean` 里 `WellFounded.Nat.fix` 的文档注释，它与 `WellFounded.fix` 不同，在闭项上能规约：它是以燃料
为参数的 `Nat.rec`（燃料取「度量 + 1」），每一步都是 ι 规约，所以重新标成可展开（`@[semireducible]`）后
`decide` 就能算。`WellFounded.fix` 要沿可及性证明（`Acc`）规约，没有这个保证，标了也没有用（Lean 发出
「not effective」的警告，见第 6 章 §9）。内核不看 `@[irreducible]`，所以 `decide +kernel` 照样展开 `half`：
-/

example : half 10 = 5 := by decide +kernel

/-!
## 9. `whnf`：弱头正规形

精译器回答「展开到哪一步」的基本操作是求 weak head normal form（弱头正规形，whnf；函数 `whnf` 的用法见
第 27 章 §2）：只规约到头部是构造子、λ、Π、字面量或卡住的应用为止，不规约内部；`#reduce`（与 `Meta.reduce`）则规约
到底。同一个列表上对照（重点是 `whnf` 与 `reduce` 两行）：
-/

open Lean Meta in
/--
info: whnf: Nat.succ 1 :: List.map Nat.succ [2]
---
info: reduce: [2, 3]
-/
#guard_msgs in
#eval show MetaM Unit from do
  let l ← mkListLit (mkConst ``Nat) [mkNatLit 1, mkNatLit 2]
  let e ← mkAppM ``List.map #[mkConst ``Nat.succ, l]
  logInfo m!"whnf: {← whnf e}"
  logInfo m!"reduce: {← reduce e}"

/-!
`whnf` 停在头部构造子 `cons`，元素与尾部都不动；`reduce` 把整个列表算完。

## 10. 内核加速的 `Nat` 运算

如果 `100 位数 * 100 位数` 要靠 `Nat.mul` 的递归定义一位一位地展开，`decide` 与 `rfl` 对大数就毫无用处。
所以 `Nat` 字面量在内核里是任意精度整数（参考手册：通常用 GMP），下列 15 个运算在字面量上由内核直接计算，
不展开定义：`Nat.succ`，以及 `add`、`sub`、`mul`、`pow`、`gcd`、`mod`、`div`、`beq`、`ble`、`land`、`lor`、
`xor`、`shiftLeft`、`shiftRight`（内核源码 `type_checker.cpp` 的 `reduce_nat`，本章不复现）。精译器里的
`reduceNat?`（`Lean/Meta/WHNF.lean`）镜像同一张表，所以连 `decide`（先在精译器里求值，再交给内核重检）
对 100 位数也能一步算完：
-/

example : ((10 ^ 99 + 7) * (3 ^ 200 + 11)) % 1000003 = 877350 := by decide
example : (10 ^ 99 + 7) / (3 ^ 200 + 11) = 3764 := by decide
example : Nat.gcd (2 ^ 200 * 3) (2 ^ 100 * 5) = 2 ^ 100 := by decide
example : Nat.xor (10 ^ 99 + 7) (3 ^ 200 + 11) % 1000003 = 180427 := by decide
example : Nat.shiftRight (Nat.shiftLeft (10 ^ 99 + 7) 10) 10 = 10 ^ 99 + 7 := by decide

/-!
`decide +kernel` 跳过精译器这一步、直接让内核算，下面是它与 `decide` 不同的两处边界。
**一，精译器对 `^` 另设了阈值**（选项 `exponentiation.threshold`，默认 256），内核没有。指数超过阈值时，
精译器不走字面量的快速路径，给出警告并改按定义逐步展开 `Nat.pow`，指数一大就撞上递归深度；
`decide +kernel` 不受影响：
-/

/--
warning: exponent 5000 exceeds the threshold 256, exponentiation operation was not evaluated, use
`set_option exponentiation.threshold <num>` to set a new threshold
---
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : 2 ^ 5000 % 7 = 4 := by decide

example : 2 ^ 5000 % 7 = 4 := by decide +kernel

/-!
**二，内核对数字大小设了上限**（环境变量 `LEAN_NAT_MAX_SIZE`，默认 128 MB），超过就拒绝计算：
-/

/--
error: (kernel) the kernel refused to evaluate `Nat.pow` because the result would exceed the
maximum numeral size; increase the LEAN_NAT_MAX_SIZE environment variable to allow it
-/
#guard_msgs in
example : 0 < 2 ^ (2 ^ 31) := by decide +kernel

/-!
**不在表里的运算按定义展开。** `Nat.log2` 有 `@[extern]` 的编译实现，但按上面两处源码（`reduce_nat`、
`reduceNat?`，本章不复现）它不在加速表里：它的逻辑模型是以 `n` 为燃料的 `Nat.rec`（`#print` 能看到），每一步
才用到被加速的 `ble` 与 `div`。所以步数随 `log₂ n` 增长，`decide` 在递归深度上撞墙（`maxRecDepth`，§16），
而同样大小的 `shiftRight` 不受影响。下面看得到的是现象：`decide` 在 300 位成功、700 位撞墙，`decide +kernel`
两者都过（它不受精译器的递归深度限制）；这组例子本身区分不了「内核有没有加速 `log2`」，那一点只靠源码：
-/

/--
info: @[expose] def Nat.log2 : ℕ → ℕ :=
fun n ↦ Nat.rec (motive := fun x ↦ ℕ → ℕ) (fun x ↦ 0) (fun x ih n ↦ Bool.rec 0 (ih (n.div 2)).succ
(Nat.ble 2 n)) n n
-/
#guard_msgs in #print Nat.log2

example : Nat.log2 (Nat.shiftLeft 1 300) = 300 := by decide

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : Nat.log2 (Nat.shiftLeft 1 700) = 700 := by decide

example : Nat.log2 (Nat.shiftLeft 1 700) = 700 := by decide +kernel

example : Nat.shiftRight (Nat.shiftLeft 1 100000) 99999 = 2 := by decide

/-!
## 11. 精译器与内核

一条声明的旅程：**解析** → 宏展开与**精译**（补全隐式参数、解决重载、插入强制转换、合一出 metavariable
（元变量）、运行策略，得到完整的 `Expr`）→ 内核**重新检查**这个 `Expr`（每个声明提交时都会）。内核很小：
不做合一、不解元变量、不搜索实例、没有语法层面的 termination（终止性）检查（良基递归在精译阶段已被翻译成
`WellFounded.fix`，度量是 `ℕ` 时是 `WellFounded.Nat.fix`，见 §8）。凡是内核拒绝的，都是精译器放过去的。
直接用 `addDecl` 把一个不合法的声明交给内核（重点是 `addDecl` 这一行，其余是造一个声明的样板），就能看到
内核自己的报错。`withoutModifyingEnv` 在演示结束后丢弃对环境的一切改动，保证这两个演示名不会被导出。
-/

open Lean Meta in
/--
error: (kernel) declaration type mismatch, 'bad' has type
  Bool
but it is expected to have type
  ℕ
-/
#guard_msgs in
#eval show MetaM Unit from withoutModifyingEnv do
  addDecl <| .defnDecl
    (mkDefinitionValEx `bad [] (mkConst ``Nat) (mkConst ``Bool.true) .abbrev .safe [`bad])

open Lean Meta in
/-- error: (kernel) declaration has metavariables 'bad2' -/
#guard_msgs in
#eval show MetaM Unit from withoutModifyingEnv do
  let mv ← mkFreshExprMVar (some (mkConst ``Nat))
  addDecl <| .defnDecl (mkDefinitionValEx `bad2 [] (mkConst ``Nat) mv .abbrev .safe [`bad2])

/-- error: Unknown identifier `bad` -/
#guard_msgs in #check bad

/-!
带 `(kernel)` 前缀的错误来自内核；最后的 `#check` 确认 `bad` 没有留在环境里。第二个例子说明元变量必须在交给内核
之前被精译器解完。

**合一**是精译器的工作（`isDefEq` 一边比较一边给元变量赋值，第 27 章 §2）。`?n + 1 =?= 3` 可以解（`Nat` 的
偏移量合一，得 `?n := 2`）；`?n * 2 =?= 6` 不是模式，不解：
-/

example : ∃ n : ℕ, n + 1 = 3 := ⟨_, rfl⟩

set_option pp.mvars false in
/--
error: Application type mismatch: The argument
  rfl
has type
  ?_ = ?_
but is expected to have type
  ?_ * 2 = 6
in the application
  Exists.intro ?_ rfl
-/
#guard_msgs in
example : ∃ n : ℕ, n * 2 = 6 := ⟨_, rfl⟩

/-!
**延后**（postpone）：精译器按顺序处理参数，遇到信息不够的项就先挂起，等元变量被解出来再回来。
`List.map (fun x ↦ x.succ) [1, 2]` 里处理 `fun x ↦ x.succ` 时 `x` 的类型还是元变量，它被挂起，
等 `[1, 2]` 的元素类型定下来（这里靠数字字面量的默认实例 `ℕ`）才恢复；孤零零的 `fun x ↦ x.fooBar`
永远等不到，只能报错：
-/

/-- info: List.map (fun x ↦ x.succ) [1, 2] : List ℕ -/
#guard_msgs in #check List.map (fun x ↦ x.succ) [1, 2]

set_option pp.mvars false in
/--
error: Invalid field notation: Type of
  x
is not known; cannot resolve field `fooBar`
---
info: fun x ↦ ?_ : (x : ?_) → ?_ x
-/
#guard_msgs in #check fun x ↦ x.fooBar

/-!
参考手册还提醒（本章不复现）：内核的定义相等**不保证传递性**，也没有主体规约性质（subject reduction），
精心构造的项可以让检查器不终止。这些是实现层面的事实，不影响日常使用，但它们是 §17 的背景。

## 12. 实例合成

第 15 章讲过怎样写实例；这里看精译器怎样**找**实例。instance synthesis（实例合成）是**带表的回溯式深度
优先搜索**：目标是 `C a`，候选实例按**优先级从高到低、同优先级后声明者先试**排序；已解决的子目标进表，供
后来者复用（trace 里的 `answer` 与 `resume` 就是写表与续用）。表使得左递归之类的循环不会反复展开同一个
子目标，但搜索并非必然终止，所以另有资源上限（本节末）。用一个自带的小类型类看全过程（跟踪选项
`trace.Meta.synthInstance`）：
-/

class Pretty (α : Type) where
  pr : α → String

instance : Pretty ℕ := ⟨toString⟩
instance : Pretty Bool := ⟨toString⟩
instance {α β : Type} [Pretty α] [Pretty β] : Pretty (α × β) where
  pr p := Pretty.pr p.1 ++ Pretty.pr p.2

set_option trace.Meta.synthInstance true in
/--
info: instPrettyProd
---
trace: [Meta.synthInstance] ✅️ Pretty (ℕ × Bool)
  [Meta.synthInstance] ✅️ new goal Pretty (ℕ × Bool)
    [Meta.synthInstance.instances] #[@instPrettyProd]
  [Meta.synthInstance.apply] ✅️ apply @instPrettyProd to Pretty (ℕ × Bool)
    [Meta.synthInstance.tryResolve] ✅️ Pretty (ℕ × Bool) ≟ Pretty (ℕ × Bool)
    [Meta.synthInstance] ✅️ new goal Pretty ℕ
      [Meta.synthInstance.instances] #[instPrettyNat]
  [Meta.synthInstance.apply] ✅️ apply instPrettyNat to Pretty ℕ
    [Meta.synthInstance.tryResolve] ✅️ Pretty ℕ ≟ Pretty ℕ
    [Meta.synthInstance.answer] ✅️ Pretty ℕ
  [Meta.synthInstance.resume] ✅️ propagating Pretty ℕ to subgoal Pretty ℕ of Pretty (ℕ × Bool)
    [Meta.synthInstance.resume] size: 1
    [Meta.synthInstance] ✅️ new goal Pretty Bool
      [Meta.synthInstance.instances] #[instPrettyBool]
  [Meta.synthInstance.apply] ✅️ apply instPrettyBool to Pretty Bool
    [Meta.synthInstance.tryResolve] ✅️ Pretty Bool ≟ Pretty Bool
    [Meta.synthInstance.answer] ✅️ Pretty Bool
  [Meta.synthInstance.resume] ✅️ propagating Pretty Bool to subgoal Pretty Bool of Pretty (ℕ × Bool)
    [Meta.synthInstance.resume] size: 2
    [Meta.synthInstance.answer] ✅️ Pretty (ℕ × Bool)
  [Meta.synthInstance] result instPrettyProd
-/
#guard_msgs in
#synth Pretty (ℕ × Bool)

/-!
读法：先为 `Pretty (ℕ × Bool)` 建新目标，唯一匹配的实例是 `Prod` 那条；它带来两个子目标
`Pretty ℕ`、`Pretty Bool`，各自解出答案后回传，最后合成整体。

**优先级与 `outParam`**（用法与报错见第 15 章 §2）。候选实例的顺序就是上面说的：高优先级先试，同优先级
**后声明的先试**（练习 28.15）。`outParam` 参数不参与匹配：合成开始前它被换成一个占位的元变量（trace 里的
`_tc.0`），由选中的实例**给出**，所以调用者不必先知道它：
-/

class Sing (α : Type) (β : outParam Type) where
  f : α → β

instance : Sing ℕ Bool := ⟨fun n ↦ n == 0⟩

set_option trace.Meta.synthInstance true in
/--
info: fun n ↦ Sing.f n : ℕ → Bool
---
trace: [Meta.synthInstance] ✅️ Sing ℕ Bool
  [Meta.synthInstance] ✅️ new goal Sing ℕ _tc.0
    [Meta.synthInstance.instances] #[instSingNatBool]
  [Meta.synthInstance.apply] ✅️ apply instSingNatBool to Sing ℕ Bool
    [Meta.synthInstance.tryResolve] ✅️ Sing ℕ Bool ≟ Sing ℕ Bool
    [Meta.synthInstance.answer] ✅️ Sing ℕ Bool
  [Meta.synthInstance] result instSingNatBool
-/
#guard_msgs in #check fun n : ℕ ↦ Sing.f n

/-!
**资源上限。** 一次合成的计算量由 `synthInstance.maxHeartbeats`（默认 20000）限制；超出就报错，而不是
无限搜索：
-/

-- `substring := true` 只核对报错的这一段：
set_option synthInstance.maxHeartbeats 1 in
/--
error: failed to synthesize
  Pretty (ℕ × Bool × ℕ)
(deterministic) timeout at `typeclass`, maximum number of heartbeats (1) has been reached
-/
#guard_msgs (substring := true) in
example : Pretty (ℕ × Bool × ℕ) := inferInstance

/-!
## 13. 强制转换

coercion（强制转换）的用法见第 8 章 §8；这里看精译器怎样实现它。它不是内核概念：精译器遇到类型不符时，
去合成 `CoeT α a β`，用得到的实例把项包起来，再展开所有标了 `coe_decl` 的辅助常量（`CoeT.coe`、`Coe.coe`、
`CoeFun.coe` 等类投影），直到露出实例字段里写的东西（`Lean/Meta/Coe.lean` 的 `coeDeclAttr` 与 `expandCoe`，
本章不复现），所以结果项里没有 `CoeT`。类型类 `Coe`、`CoeTC`（`Coe` 的自反传递闭包）、`CoeOut`、`CoeHead`、
`CoeTail`、`CoeDep`（依赖于具体项）、`CoeT` 一族规定了链的形状：`CoeT := CoeHead? CoeOut* Coe* CoeTail? | CoeDep`
（`Init/Coe.lean` 的注释）。下面三个结构体之间只声明相邻的两条 `Coe`，两步转换自动完成；两个实例的字段都是
λ，所以展开之后只剩结构体字面量：
-/

structure Mm where
  v : ℕ

structure Cm where
  v : ℕ

structure Metre where
  v : ℕ

instance : Coe Mm Cm := ⟨fun x ↦ ⟨x.v / 10⟩⟩
instance : Coe Cm Metre := ⟨fun x ↦ ⟨x.v / 100⟩⟩

/-- info: fun x ↦ { v := { v := x.v / 10 }.v / 100 } : Mm → Metre -/
#guard_msgs in #check fun (x : Mm) ↦ (x : Metre)

/-!
展开只到实例字段为止：字段若是一个有名字的函数，它的应用**留在**项里。显示时的 `↑`、`⇑` 是另一套机制：
delaborator（反精译器，把项转回语法）只给登记为强制转换函数（`@[coe]`）的函数加箭头。`CoeFun` 让项可以像
函数一样应用，下面两个版本只差 `@[coe]`：
-/

structure Poly where
  coeffs : List ℕ

def Poly.eval (p : Poly) (x : ℕ) : ℕ := p.coeffs.foldr (fun c acc ↦ c + x * acc) 0

instance : CoeFun Poly (fun _ ↦ ℕ → ℕ) := ⟨Poly.eval⟩

/-- info: fun p ↦ p.eval 3 : Poly → ℕ -/
#guard_msgs in #check fun (p : Poly) ↦ p 3

structure Poly2 where
  coeffs : List ℕ

@[coe] def Poly2.eval (p : Poly2) (x : ℕ) : ℕ := p.coeffs.foldr (fun c acc ↦ c + x * acc) 0

instance : CoeFun Poly2 (fun _ ↦ ℕ → ℕ) := ⟨Poly2.eval⟩

/-- info: fun p ↦ ↑p 3 : Poly2 → ℕ -/
#guard_msgs in #check fun (p : Poly2) ↦ p 3

/-!
Mathlib 的打包映射（例如 `Equiv`）的 `coe` 是登记过的 `DFunLike.coe`，显示为 `⇑e`；`CoeSort` 让项出现在类型的
位置，集合当类型时输入 `↥S`，显示为 `↑S`，它就是函数 `Set.Elem S`。`Equiv` 的 `⇑` 展开后就是字段 `toFun`：
-/

/-- info: fun e ↦ ⇑e : ℕ ≃ ℤ → ℕ → ℤ -/
#guard_msgs in #check fun (e : ℕ ≃ ℤ) ↦ ⇑e
/-- info: fun S ↦ ↑S : Set ℕ → Type -/
#guard_msgs in #check fun (S : Set ℕ) ↦ ↥S

example (S : Set ℕ) : ↥S = Set.Elem S := rfl
example (e : ℕ ≃ ℤ) (n : ℕ) : e n = e.toFun n := rfl

/-!
## 14. `noncomputable`、`unsafe` 与 `implemented_by`

内核只管逻辑，**代码生成**是另一回事：每个会被运行的定义还要经过编译器。依赖不可计算内容的定义要标
`noncomputable`（第 8 章 §13；§3 的 `pick`）：它照常进入内核，只是不生成代码。反过来，`unsafe` 声明
可以做内核不允许的事（比如 `ptrAddrUnsafe`），内核拒绝让**安全**声明引用它们：
-/

unsafe def implU (n : ℕ) : ℕ := n + 1

/-- error: (kernel) invalid declaration, it uses unsafe declaration 'Lean4Learn.Ch28.implU' -/
#guard_msgs in
example (n : ℕ) : ℕ := implU n

/-!
`@[implemented_by impl]` 的合法用途是：逻辑上用简单的定义做规约，运行时换成更快的 `unsafe` 实现。
它也说明了**程序行为不在 trusted computing base（可信基）里**：编译器相信你，内核看的是逻辑定义。
下面故意说谎：
-/

@[implemented_by implU] def lying (n : ℕ) : ℕ := n

/-- info: 1 -/
#guard_msgs in #eval lying 0

theorem lying_zero : lying 0 = 0 := by decide

/-- info: 'Lean4Learn.Ch28.lying_zero' does not depend on any axioms -/
#guard_msgs in #print axioms lying_zero

/-!
运行得 `1`，定理证得 `0`，而 `#print axioms` 毫无异常。证明只谈逻辑定义，所以 `lying_zero` 完全正确；
但你若以为 `#eval lying 0` 的输出也是被验证过的，就错了。这与第 25 章把 `native_decide` 当成扩大
可信基是同一类原因：可信基里多了「编译器相信你」这一环。
-/

/-!
## 15. 模块系统内部

文件头见第 1 章 §8；import（导入）与 `public import`（公开导入）的区别（名字转不转发、公开签名里的名字要公开
导入）第 23 章 §4 已用小文件实测。这里补 module system（模块系统）的机制。`module` 文件的每次编译产出三份
olean 文件（本仓库 `.lake/build/lib/lean/Lean4Learn/Part1/` 里有 `Ch01_Setup.olean`、
`Ch01_Setup.olean.private`、`Ch01_Setup.olean.server`），分别是 public（公开）部分（别的模块能看到的）、
private（私有）部分、以及给语言服务器用的**服务**部分（参考手册说是文档与源码位置，本章不复现）。普通
`import M` 只加载 `M` 的公开部分，`import all M` 才加载私有部分。私有名字在环境里带一个与模块名有关的前缀
（本文件在 `public section` 里，所以下面要显式写 `private`）：
-/

private def hidden : ℕ := 3

open Lean in
/--
info: private: true, name: _private.Lean4Learn.Part5.Ch28_Internals.0.Lean4Learn.Ch28.hidden, user
name: Lean4Learn.Ch28.hidden
-/
#guard_msgs in
#eval show CoreM Unit from do
  let n := (← getConstInfo ``hidden).name
  logInfo m!"private: {isPrivateName n}, name: {n}, user name: {privateToUserName n}"

/-!
**`@[expose]`（expose（暴露））控制定义体是否对导入者可见。** 这必须用多个文件演示，所以仓库里有 `examples/modprobe/`：
八个只依赖核心库的探针模块和脚本 `run.sh`（`bash examples/modprobe/run.sh`，十几秒）。脚本为每个探针记着
预期结果（有三个应当编译失败，并且要出现指定的报错），前置模块失败时跳过依赖它的探针，结果不符时以非零
状态退出。下面的源码和输出逐字取自它的运行；它们不由 `#guard_msgs` 检查，换工具链后请重跑。

`ModProbeA.lean` 定义三个常量：无 `@[expose]` 的公开定义、有 `@[expose]` 的公开定义、私有定义，
外加一条公开定理（编译无输出）：

```
module
public def hiddenBody : Nat := 3
@[expose] public def shownBody : Nat := 3
private def secretA : Nat := 3
public theorem hiddenBody_eq : hiddenBody = 3 := by unfold hiddenBody; rfl
```

`ModProbeF.lean` 用普通 `import ModProbeA`，逐条尝试（行号在输出里）：

```
 7  example : shownBody = 3 := rfl
 9  example : hiddenBody = 3 := rfl
11  example : hiddenBody = 3 := by simp [hiddenBody]
13  example : hiddenBody = 3 := by unfold hiddenBody; rfl
15  example : hiddenBody = 3 := hiddenBody_eq
17  example : secretA = 3 := rfl
```

编译输出（第 7、15 行无输出，即通过）：

```
ModProbeF.lean:9:28: error: Type mismatch
  rfl
has type
  ?m.5 = ?m.5
but is expected to have type
  hiddenBody = 3

Note: The following definitions were not unfolded because their definition is not exposed:
  hiddenBody ↦ 1
ModProbeF.lean:11:37: error: Invalid simp theorem `hiddenBody`: Expected a definition with an
exposed body
ModProbeF.lean:11:31: error: `simp` made no progress
ModProbeF.lean:13:38: error: Tactic `unfold` failed to unfold `hiddenBody` in
  hiddenBody = 3
ModProbeF.lean:17:10: error(lean.unknownIdentifier): Unknown identifier `secretA`

Note: It is not possible to treat `secretA` as an implicitly bound variable here because the
`autoImplicit` option is set to `false`.
```

结论：没有 `@[expose]` 的公开定义，导入者只看到名字和类型，`rfl`、`simp [f]`、`unfold f` 都不行，但作者
在 A 里证好的定理（`hiddenBody_eq`）照常可用；`@[expose]` 的 `shownBody` 可以 `rfl`；`private` 的名字
完全不可见。同一条规则也约束作者自己：`ModProbeE.lean` 里，公开定理若用项模式的 `rfl` 去展开一个
未暴露的定义，编译就拒绝（上面 A 里改用 `by unfold …; rfl` 才通过）：

```
ModProbeE.lean:7:0: error: Not a definitional equality: the left-hand side
  hiddenBody
is not definitionally equal to the right-hand side
  3

Note: This theorem is exported from the current module. This requires that all definitions that
need to be unfolded to prove this theorem must be exposed.
```

`ModProbeD.lean` 写 `public import ModProbeA` 再加 `import all ModProbeA`，之后 `secretA = 3 := rfl` 与
`hiddenBody = 3 := rfl` 都通过（编译无输出）：`import all` 能越过这道墙。其余四个探针（B、C、G、H）重做
第 23 章 §4 的转发实验，结果相同：经普通 `import` 转手的 C 里 `#check shownBody` 报
`Unknown identifier `shownBody``，经 `public import` 转手的 H 里通过。

**`meta` 阶段**（第 26 章 §1）。第 26 章演示了 `meta` 定义不能调用普通定义；反方向也不行：可执行的普通代码
不能引用 `meta` 声明，类型和证明里可以。本章文件头的 `public meta import` 让导入的模块在 meta 阶段可用：
-/

meta def metaOnly : ℕ := 5

example : metaOnly = 5 := rfl

/-- error: Invalid definition `useMeta`, may not access declaration `metaOnly` marked as `meta` -/
#guard_msgs in
def useMeta : ℕ := metaOnly

/-!
## 16. 心跳与递归深度

精译器用两个**确定性**的限额防止失控：`maxHeartbeats`（heartbeat（心跳），按小块内存分配计数；超限的样子
见第 13 章 §6）与 `maxRecDepth`（递归深度）。限额与机器速度无关，同一个文件到处结果一样：
-/

open Lean in
/-- info: maxHeartbeats := 200000, maxRecDepth := 512 -/
#guard_msgs in
#eval show CoreM Unit from do
  logInfo m!"maxHeartbeats := {maxHeartbeats.defValue}, maxRecDepth := {maxRecDepth.defValue}"

set_option maxRecDepth 50 in
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : (List.range 100).length = 100 := by decide

/-!
撞墙的是**精译器**的规约。内核走另一条规约路径，所以 §10 的 `2 ^ 5000` 与 `Nat.log2` 两例里，`decide` 撞上
`maxRecDepth`，`decide +kernel` 却通过。内核另有自己的深度保护：发行说明（4.33.0，#13956）记载内核的递归深度
也受 `maxRecDepth` 约束，本章不复现。

## 17. 验证阶梯与内核的信任边界

验证阶梯（`#print axioms`、`leanchecker`、外部检查器、`lake check`）的用法见**第 23 章 §5**。本章补的是它存在的
理由，即内核一侧的事实：`#print axioms` 不覆盖 `implemented_by`/`unsafe` 这类运行时之事（§14）；内核是一份
被信任的实现，不是被证明的，它的定义相等不保证传递（§11）；发行说明记载 4.32.1 至 4.34.0 的若干版本修复了
内核可靠性漏洞，其中一部分由 AI 对抗性测试发现（本章不复现）。所以对外宣称「已证明」时要写明工具链版本，
重要结果再用更高的层检查。
-/

/-!
## 常见错误

**1. `rw` 之后剩下 `kk = 3`。** `rw` 只用 `with_reducible rfl` 收尾（§7、§8），`kk`（§7）是普通 `def`；把它改成
`abbrev` 或手动 `rfl`（默认透明度）：
-/

/--
error: unsolved goals
a : ℕ
h : a = kk
⊢ kk = 3
-/
#guard_msgs in
example (a : ℕ) (h : a = kk) : a = 3 := by rw [h]

example (a : ℕ) (h : a = kk) : a = 3 := by rw [h]; rfl

/-!
**2. 用 `def` 起别名，实例找不到。** 实例合成不展开普通 `def`（§8，§12），类型别名要用 `abbrev`：
-/

def MyNat := ℕ
abbrev MyNat' := ℕ

/--
error: failed to synthesize instance of type class
  Add MyNat

Hint: Type class instance resolution failures can be inspected with the `set_option
trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Add MyNat := inferInstance

example : Add MyNat' := inferInstance

/-!
**3. 想从自定义归纳命题里取出数据。** §3 的 `Hidden` 把字段 `n` 藏在下标 `n + 1` 里，所以 `Hidden.rec`
只能消去到 `Prop`；要取数据，得让字段本身就是下标（§3 的 `Direct`），或者改用 `Type` 里的结构体：
-/

/--
error: Type mismatch
  ℕ
has type
  Type
of sort `Type 1` but is expected to have type
  Prop
of sort `Type`
-/
#guard_msgs in
example (m : ℕ) (h : Hidden m) : ℕ := Hidden.rec (motive := fun _ _ ↦ ℕ) (fun n ↦ n) h

/-!
## 练习

练习 28.4、28.5、28.6、28.9、28.10、28.12、28.13 分别复习第 7、7、6、5、5、5、7 章。28.11 要写一个
`MetaM` 函数，所以放在 `public meta section` 里。28.15 用到下面自带的类型类 `Tag`。
★ 直接应用，★★ 综合两个想法，★★★ 需要新想法。
-/

/-- 练习 28.1（★）：依值对 `p` 的第二个分量是 `Fin (p.1 + 1)` 的元素，所以它的值不超过第一个分量（§1）。
提示：`p.2.isLt`、`omega`。 -/
theorem ex_28_1 (p : (n : ℕ) × Fin (n + 1)) : p.2.val ≤ p.1 := sorry

/-- 练习 28.2（★）：抬升到 `Type 1` 不丢信息（§2）。提示：`ULift.down`、`congrArg`。 -/
theorem ex_28_2 (α : Type) (a b : α) (h : ULift.up.{1} a = ULift.up b) : a = b := sorry

/-- 练习 28.3（★★）：`∀ α : Type 3, Nonempty α` 是命题（非直谓性，§2），而且是假命题。
提示：取一个空类型，注意它要住在 `Type 3`（`PEmpty.{4}`），消去用 `PEmpty.elim`。 -/
theorem ex_28_3 : ¬ ∀ α : Type 3, Nonempty α := sorry

/-- 练习 28.4（★）：正整数的子类型里，值相等就相等（证明无关性，§3）。 -/
theorem ex_28_4 (a b : {n : ℕ // 0 < n}) (h : a.1 = b.1) : a = b := sorry

/-- 练习 28.5（★★）：对任意谓词 `p`，`∃ n, p n` 的见证不能直接取出（§3），但「存在一个选择函数」是个
`Prop`，可以证明。提示：`Classical.choose`、`Classical.choose_spec`。 -/
theorem ex_28_5 (p : ℕ → Prop) : ∃ f : (∃ n, p n) → ℕ, ∀ h, p (f h) := sorry

/-- 练习 28.6（★★）：用 `Nat.rec` 直接定义的「加 2」递推，在每个 `n` 上都等于 `2 * n`（ι 规约，§4）。
提示：对 `n` 归纳；归纳步先用 `show` 把 `Nat.rec` 在 `k + 1` 上的值写成 `… + 2`，再 `omega`。 -/
theorem ex_28_6 (n : ℕ) :
    (Nat.rec (motive := fun _ ↦ ℕ) 0 (fun _ ih ↦ ih + 2) n : ℕ) = 2 * n := sorry

/-- 练习 28.7（★）：递归结构体没有 eta（§4），但对任何函数 `f`，`f` 作用在重新拼好的 `Lst.mk x.hd x.tl`
上仍等于 `f x`。提示：先分情况。 -/
theorem ex_28_7 (f : Lst → ℕ) (x : Lst) : f (Lst.mk x.hd x.tl) = f x := sorry

/-- 练习 28.8（★）：用 `Quot.sound` 证明模 3 余数相同的任意两个数在商里相等（§5）。 -/
theorem ex_28_8 (a b : ℕ) (h : a % 3 = b % 3) :
    Quot.mk (fun a b : ℕ ↦ a % 3 = b % 3) a = Quot.mk _ b := sorry

/-- 练习 28.9（★）：两个二元函数逐点相等则相等（函数外延性，§6）。证明之后运行
`#print axioms ex_28_9`，对照 §6 说明为什么只有一条公理（答案文件里有这条命令）。 -/
theorem ex_28_9 (f g : ℕ → ℕ → ℕ) (h : ∀ a b, f a b = g a b) : f = g := sorry

/-- 练习 28.10（★）：§7 的 `kk` 是 `def`。`simp only [h]` 用不上 `h : P kk`，但 `exact` 在默认透明度下
可以。选对工具完成证明。 -/
theorem ex_28_10 (P : ℕ → Prop) (h : P kk) : P 3 := sorry

section MetaExercise
public meta section

open Lean Meta

/-- 练习 28.11（★★）：对常量 `c`，依次在 `none`、`reducible`、`instances`、`implicit`、`default`、
`all` 六种透明度下对 `mkConst c` 做 `whnf`，返回「结果与 `mkConst c` 不同」（即被展开了）的布尔值
列表。提示：`withTransparency`、`whnf`；`Expr` 有 `!=`。用 §8 的探针 `pD`、`pX` 检验。 -/
def ex_28_11 (c : Name) : MetaM (List Bool) := sorry

end
end MetaExercise

/-- 练习 28.12（★）：`Nat.log2` 不在加速表里（§10），普通 `decide` 在 700 位上撞上递归深度。
换一个策略。 -/
theorem ex_28_12 : Nat.log2 (Nat.shiftLeft 1 700) = 700 := sorry

/-- 练习 28.13（★★）：`Equiv` 的函数形式展开成字段 `toFun`（§13）；利用这一点和 `Equiv` 的
引理证明：先走 `e`、再走 `e.symm` 回到原点。 -/
theorem ex_28_13 (e : ℕ ≃ ℤ) (n : ℕ) : (e.trans e.symm) n = n := sorry

/-- 练习 28.14（★★★）：§3 的直观原因，写成定理：没有函数能在 `True ∨ True` 上区分 `Or.inl` 与 `Or.inr`
给出的两个证明。提示：证明无关性让 `f (Or.inl trivial) = f (Or.inr trivial)` 成立，且是 `rfl`。 -/
theorem ex_28_14 :
    ¬ ∃ f : (True ∨ True) → Bool, f (Or.inl trivial) = true ∧ f (Or.inr trivial) = false := sorry

/-- 供练习 28.15 使用的类型类，五个实例。 -/
class Tag (α : Type) where
  name : String

instance (priority := low) : Tag ℕ := ⟨"low"⟩
instance : Tag ℕ := ⟨"mid"⟩
instance (priority := high) : Tag ℕ := ⟨"high1"⟩
instance (priority := high) : Tag ℕ := ⟨"high2"⟩
instance : Tag ℕ := ⟨"mid2"⟩

/-- 练习 28.15（★★）：先不运行，按 §12 的规则（优先级，同优先级后声明的先试）预测 `Tag.name ℕ` 是哪个
字符串，再验证下面的陈述；然后设想删掉 `"high2"` 那个实例，预测新的值。 -/
theorem ex_28_15 : Tag.name ℕ = "high2" := sorry

/-!
## 小结

| 概念 | 语法 / 命令 | 要点 |
|---|---|---|
| Π、Σ | `(a : α) → β a`、`(a : α) × β a` | `∀`、`→`、`Subtype`、`Exists` 都是特例或变体 |
| 宇宙 | `Sort u`、`Type*`、`ULift` | 无累积性；`Prop` 非直谓，其余直谓（`imax`） |
| 证明无关性 | `rfl` 证 `⟨1, h₁⟩ = ⟨1, h₂⟩` | 命题的任意两个证明定义相等 |
| 子单点消去 | `And.rec`、`Eq.rec` 可；`Or.rec`、`Hidden.rec` 不可 | 至多一个构造子；排除参数后字段是证明或本身是下标 |
| 递归子 | `#print Nat.rec`、`T.casesOn` | 内核原语 `rec`；其余是定义 |
| 结构 eta | `(p.1, p.2) = p := rfl` | 仅非递归、单构造子、无下标 |
| `Quot` | `Quot.mk/lift/ind/sound` | 商的 ι 规约是定义相等，`sound` 是命题相等 |
| 公理 | `#print axioms` | 标准三条 `propext`、`Classical.choice`、`Quot.sound`；其余名字要审计 |
| 定义相等 | β δ ι ζ η，商，证明无关 | `with_reducible rfl` 只展开 `@[reducible]` 的 δ |
| 透明度 | `none<reducible<instances<implicit<default<all` | `rw` 用 `reducible`；内核不看 |
| 良基递归 | `#print f` | `WellFounded.Nat.fix` 在闭项上可算，`WellFounded.fix` 不保证 |
| `whnf` | `#reduce`、`Meta.whnf` | 只化头部 |
| 内核 `Nat` | `decide`、`decide +kernel` | 15 种运算加速；`log2` 不在内；128 MB 上限 |
| 精译器 vs 内核 | `addDecl`、`isDefEq` | 内核无合一、无元变量、无实例搜索 |
| 实例合成 | `#synth`、`trace.Meta.synthInstance` | 优先级，后声明先试；`outParam`；心跳上限 |
| 强制转换 | `Coe`…`CoeT`、`CoeFun`、`CoeSort`、`↑ ⇑ ↥` | `coe_decl` 管展开，`@[coe]` 管显示 |
| 编译侧 | `noncomputable`、`unsafe`、`implemented_by` | 不在可信基里的是程序行为 |
| 模块 | `public`/`private`、`@[expose]`、`import all`、`meta` | 三份 olean；定义体默认不暴露；`public import` 才转发 |
| 限额 | `maxHeartbeats`、`maxRecDepth`、`synthInstance.maxHeartbeats` | 确定性；内核另有深度保护 |
| 验证阶梯 | `#print axioms`、`leanchecker`、`lake check` | 对外宣称「已证明」时用更高的层（第 23 章 §5） |

## 延伸阅读

- *Lean Language Reference* 4.35.0（`https://lean-lang.org/doc/reference/4.35.0/`）：「The Type System」
  （宇宙、命题与 Subsingleton Elimination、归纳类型、商）；「Axioms」；「Source Files and Modules」；「Type
  Classes」的 Instance Synthesis；「Coercions」；「Definitions」的 Controlling Reduction；「Validating a Lean
  Proof」（和第 23 章 §5 一起读）。
- Lean 核心源码：`Init/MetaTypes.lean`（`TransparencyMode` 的文档注释）、`Init/Prelude.lean`（`Quot`、
  `Classical.choice`、`Nat.add` 一族）、`Lean/Meta/WHNF.lean`（`reduceNat?`、`reduceQuotRec`）、
  `Lean/Structure.lean`（`isNonRecStructure`）、`Init/Coe.lean` 与 `Lean/Meta/Coe.lean`（`coe_decl`、
  `expandCoe`）、`Init/WF.lean`（`WellFounded.fix`、`WellFounded.Nat.fix`）、
  `Lean/Elab/MutualInductive.lean`（`inductive.autoPromoteIndices`）。
- 内核：`src/kernel/type_checker.cpp`（`is_def_eq_core`、`reduce_nat`）与 `src/kernel/inductive.cpp`
  （`elim_only_at_universe_zero`，第 483–536 行），在 GitHub 仓库 `leanprover/lean4` 的 `v4.35.0` 标签；
  本地工具链不带内核源码。内核可靠性修复见该仓库 GitHub Releases 里 4.32.1 至 4.34.0 各版的说明。
- Mathlib：`Mathlib/Data/Quot.lean`、`Mathlib/Logic/Equiv/Defs.lean`、
  `Mathlib/Basic/FunLike/Basic.lean`（`⇑`）、`Mathlib/Tactic/Linter/PrivateModule.lean`（模块的可见性提示）。
- *Metaprogramming in Lean 4*：`04_metam.lean`（MetaM 一章）里讲透明度的一节（六级梯级的演示）。
- 本仓库 `examples/modprobe/`：§15 的探针模块与 `run.sh`。
- 本书第 1 章（文件头）、第 3 章、第 5 章、第 6 章、第 15 章（实例、优先级）、第 23 章 §5（验证阶梯）、第 25 章、
  第 26–27 章。
-/

end Lean4Learn.Ch28

end
