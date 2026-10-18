module

public import Batteries.Tactic.Trans
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.TypeStar

/-!
# 第 5 章　等式、simp 与证明的骨架

前几章你已经会用 `rw`、`simp`、`calc` 做计算。本章回答三个问题：等式在 Lean 里到底是什么（答案：
inductive type（归纳类型）`Eq`，它只有一个 constructor（构造子））；`rw` 与 `simp` 各自精确地做什么、
会在哪里失败；一个十行左右的证明应该怎样搭骨架。读完后，你能预测 `rfl` 何时成功，读懂 `rw` 与
`simp` 的失败信息并选对补救办法，把长证明拆成 `have` / `calc` 骨架再逐块填入。

## 学习目标
- 说出 `Eq` 的定义，用 `rfl`、`Eq.symm`、`Eq.trans`、`▸`、`congrArg`、`congrFun` 写等式的项模式证明；
- 区分 definitional equality（定义相等）与 propositional equality（命题相等），预测 `rfl` 何时成功，
  知道 `decide` 能做什么、在哪里停下；
- 用 rewriting（重写）`rw`（`←`、`at`、`nth_rw`、side condition（副条件）），读懂它的两类失败，知道
  binder（引入绑定变量的构造，如 `fun`、`∀`、`∃`）里不能 `rw`，以及 `rw!` 的用途；
- 说明 simplifier（简化器）的工作方式：simp lemma（simp 引理）、simp set（simp 集）、`@[simp]`、
  `simp only`、`simp?`、`simpa`、`simp at`、`simp +arith`、`simp_rw`，认得 simp normal form（simp 正规形）；
- 写完整的 `calc`（首行的写法，用 `Trans` 混用 `=`、`≤`、`<`），用 `congr`、`subst`、`ext`、`funext`、
  `symm`、`trans` 处理等式的结构性步骤，并先搭骨架（`sorry`）再填空。

## 前置知识
第 1 章（`trace_state`、`#guard_msgs`）；第 2 章（`rw`、`simp`、`calc` 的初步用法，`omega`、`ring`、
`linarith`）；第 3 章（命题即类型，`rfl` 的项）；第 4 章（`intro`、`exact`、`have`、`change`、`suffices`
与目标状态的读法）。
-/

@[expose] public section

namespace Lean4Learn.Ch05

/-!
## 1. `Eq` 是一个归纳类型

`a = b` 是 `Eq a b` 的记号。`#print` 显示它的定义：`Eq` 只有一个构造子 `Eq.refl`，类型是 `a = a`
（归纳类型的一般理论在第 6 章）。直接用构造子证明 `a = b`，要求 `a` 与 `b` 在类型检查器眼里是同一个项
（`rfl` 就是 `Eq.refl _`）。其余的等式证明来自假设、已有的定理（如 `Nat.zero_add`）和公理 `propext`、
`Quot.sound`。
-/

/--
info: inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop
number of parameters: 2
constructors:
Eq.refl : ∀ {α : Sort u_1} (a : α), a = a
-/
#guard_msgs in #print Eq

/-!
对手头已有的等式，用 eliminator（消去子）`Eq.subst` 使用它：若 `a = b` 且 `a` 满足 `motive`（一个以
被替换的项为变量的谓词，类型 `α → Prop`），则 `b` 也满足。对称 `Eq.symm`、传递 `Eq.trans` 与 `rw`
都建立在它之上。
-/

/-- info: @Eq.subst : ∀ {α : Sort u_1} {motive : α → Prop} {a b : α}, a = b → motive a → motive b -/
#guard_msgs in #check @Eq.subst

-- 项模式：dot notation（点记号）`h.symm` 就是 `Eq.symm h`；`h ▸ e` 用 `h` 在 `e` 的类型里代换。
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := Eq.trans h₁ h₂
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : c = a := (h₁.trans h₂).symm
example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (ha : P a) : P b := h ▸ ha
-- 策略模式：同一个命题；`rw [← h]` 把目标里的 `b` 换成 `a`，目标变成 `P a`。
example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (ha : P a) : P b := by
  rw [← h]
  exact ha

-- 再加两条「函数保持等式」：`congrArg f h : f a = f b`，`congrFun h x : f x = g x`（当 `h : f = g`）。
example (a b c : ℕ) (h : a = b) : a + c = b + c := congrArg (· + c) h
example (f g : ℕ → ℕ) (h : f = g) (x : ℕ) : f x = g x := congrFun h x

/-!
## 2. `rfl` 与定义相等

`rfl : a = a` 的类型是 `?x = ?x`，要让它有类型 `a = b`，elaborator（精译器；另译繁饰器）必须检查 `a` 与
`b` 是不是 definitional equality（定义相等）：能否通过 β（函数应用）、δ（展开定义）、ι（recursor（递归子）
作用在构造子上）、ζ（`let`）reduction（规约）化成同一个项。**命题相等**则是「有一个 `a = b` 的证明项」，
可以靠定理、归纳、`simp` 得到。定义相等一定给出命题相等（`rfl`），反过来不然。

先看成功的情形：展开一个 `def`、`Nat.add` 对第二个参数的递归。
-/

def double (n : ℕ) : ℕ := n + n

example : double 3 = 6 := rfl                          -- δ 规约后是 3 + 3
example (n : ℕ) : double n = n + n := rfl              -- 只需展开 `double`
example (n : ℕ) : n + 0 = n := rfl                     -- `n + 0` 按定义规约成 `n`
example (n m : ℕ) : n + (m + 1) = (n + m) + 1 := rfl  -- `Nat.add` 对**第二个**参数递归

/-!
`Nat.add` 的定义对第二个参数做 pattern matching（模式匹配）：`n + 0 ⟶ n`，`n + (m + 1) ⟶ (n + m) + 1`。
于是第二个参数是变量时就卡住了：`0 + n` 不能规约，`rfl` 失败，报错列出两边并指出它们不是定义相等。
-/

/--
error: Tactic `rfl` failed: The left-hand side
  0 + n
is not definitionally equal to the right-hand side
  n

n : ℕ
⊢ 0 + n = n
-/
#guard_msgs in
example (n : ℕ) : 0 + n = n := by rfl

/-!
`0 + n = n` 是真命题，只是需要命题相等：库里的 `Nat.zero_add`（用归纳证明）、`simp`、`omega` 都行。
这就是「定义相等 vs 命题相等」的实际含义：能算出来的归 `rfl`，要推理的归证明。`unfold f` 把目标里的
`f` 按定义展开，`unfold f at h` 展开假设 `h`：
-/

example (n : ℕ) : 0 + n = n := Nat.zero_add n
example (n : ℕ) : 0 + n = n := by simp
example (n : ℕ) : 0 + n = n := by omega
example (n : ℕ) : double n = 2 * n := by
  unfold double         -- ⊢ n + n = 2 * n
  omega
example (n : ℕ) (h : double n = 4) : n = 2 := by
  unfold double at h    -- h : n + n = 4
  omega

/-!
## 3. `decide` 的边界

`decide` 面向 decidable（可判定）命题：它合成 `Decidable` 实例，再把 `Decidable.decide p` 规约成 `true`
（4.35 里 `Decidable` 的新定义见第 6 章）。所以它能证 `rfl` 证不了的东西——`≠`、有界的 `∀`。
-/

example : 2 + 2 ≠ 5 := by decide

/-!
**边界一：目标里不能有自由变量。** 报错自带补救办法：`decide +revert` 先把局部变量 revert 回目标。
-/

/--
error: Expected type must not contain free variables
  n < 10 → n * n < 100

Hint: Use the `+revert` option to automatically clean up and revert free variables
-/
#guard_msgs in
example (n : ℕ) : n < 10 → n * n < 100 := by decide

example (n : ℕ) : n < 10 → n * n < 100 := by decide +revert

/-!
**边界二：实例必须真的能规约。** `ℝ` 上的序是经典的（不可计算），`decide` 卡在实例里的
`Classical.choice` 上，这类目标交给 `norm_num`。较大的有限检查可以改用 `decide +kernel`，它让 kernel
（内核）直接算，不经过精译器的规约（`native_decide` 另需信任编译器，Mathlib 禁用，见第 25 章）。
-/

/-- error: Tactic `decide` failed to reduce
  @decide (1 < 2) (Real.decidableLT 1 2)
to `true` or `false`.

After unfolding the instances `Classical.propDecidable`, `LinearOrder.toDecidableLT`,
and `Real.decidableLT`, reduction got stuck at
  Classical.choice ⋯ -/
#guard_msgs (whitespace := lax, substring := true) in
example : (1 : ℝ) < 2 := by decide

example : (1 : ℝ) < 2 := by norm_num
example : ∀ n : ℕ, n < 1000 → n * n < 1000000 := by decide +kernel

/-!
## 4. `rw` 的机制

`rw [h]`（`h : a = b`）做四件事：①在目标里找 `a` 的实例（`a` 含 metavariable（元变量）时，先找到的第一个
匹配把元变量固定下来）；②把**所有**与该实例相同的子项一起抽象成 `fun _a ↦ …`——这个函数就是 motive；
③由 `h` 得到 `motive a = motive b`（`congrArg`），再用 `Eq.mpr` 把目标换成 `motive b`；④用
`with_reducible rfl` 试着关掉目标——只在 reducible 透明度下比较，不展开普通定义，所以很弱。
`show_term` 打印策略生成的项（`id` 只是包装），②③两步一目了然；紧接着的例子展示④的局限：
-/

/--
info: Try this:
  [apply] exact Eq.mpr (id (congrArg (fun _a ↦ P _a) h)) hb
-/
#guard_msgs in
example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (hb : P b) : P a := by
  show_term (rw [h]; exact hb)

/--
error: unsolved goals
a b : ℕ
h : a = b
⊢ double b = b + b
-/
#guard_msgs in
example (a b : ℕ) (h : a = b) : double a = b + b := by
  rw [h]                -- `a` 换成 `b` 后，`rw` 的 rfl 不展开 `double`，目标留下了

/-!
再看两个典型情形。无元变量时，`a` 的所有出现一起被替换；有元变量时，模式 `?n + ?m` 由第一个匹配
（先父后子、先左后右，即最外层的 `a + b + c`）固定。`←` 把等式倒过来用。
-/

example (a b : ℕ) (h : a = b) : a + a = b + b := by rw [h]   -- 两处 `a` 一起换，再由 rfl 关掉

example (a b c : ℕ) : a + b + c = c + (a + b) := by
  rw [Nat.add_comm]

/--
trace: a b c : ℕ
h : a = b
⊢ a + c = c + a
-/
#guard_msgs in
example (a b c : ℕ) (h : a = b) : b + c = c + b := by
  rw [← h]           -- 把 `b` 换成 `a`
  trace_state
  exact Nat.add_comm a c

/-!
想只改某几处时用 `nth_rw`（Mathlib）：`nth_rw 1 [h]` 只改第一处出现，计数按上面说的次序。
`rw [h] at h₁` 改假设 `h₁`，`at h₁ ⊢` 同时改假设和目标。
-/

example (a b : ℕ) (h : a = b) : a + a = b + a := by
  nth_rw 1 [h]
example (a b : ℕ) (h : a = 2) (h₁ : a + 1 = b) : b + a = 5 := by
  rw [h] at h₁ ⊢          -- 假设 `h₁` 与目标里的 `a` 都换成 `2`
  omega

/-!
**副条件。** 引理带假设时（`Nat.sub_add_cancel : m ≤ n → n - m + m = n`），`rw` 先改写主目标，把
side condition（副条件）作为**新目标**排在主目标后面。下面主目标 `n = n` 已被 `rfl` 关掉，所以只剩副条件。
也可以直接把证明作为参数交给它。
-/

/--
trace: m n : ℕ
h : m ≤ n
⊢ m ≤ n
-/
#guard_msgs in
example (m n : ℕ) (h : m ≤ n) : n - m + m = n := by
  rw [Nat.sub_add_cancel]
  trace_state
  exact h

example (m n : ℕ) (h : m ≤ n) : n - m + m = n := by
  rw [Nat.sub_add_cancel h]

/-!
## 5. `rw` 的边界：binder 与 motive

**边界一：不能在 binder 里重写。** `∀ x, …`、`∃ x, …`、`fun x ↦ …` 引入 bound variable（绑定变量）`x`。
`rw` 用 `kabstract` 找模式的实例，跳过含有松散绑定变量的子项；`x + 0` 就含有 `x`，所以 `rw` 报
「没找到模式」，尽管目标里明明写着 `x + 0`。`∀` 与 `∃` 都是如此：
-/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?n + 0
in the target expression
  ∀ (x : ℕ), x + 0 + 1 = x + 1

⊢ ∀ (x : ℕ), x + 0 + 1 = x + 1
-/
#guard_msgs in
example : ∀ x : ℕ, x + 0 + 1 = x + 1 := by
  rw [Nat.add_zero]

/-- error: Tactic `rewrite` failed: Did not find an occurrence of the pattern -/
#guard_msgs (whitespace := lax, substring := true) in
example : ∃ x : ℕ, x + 0 = 3 := by
  rw [Nat.add_zero]

/-!
补救办法有三：先 `intro x`（或 `funext x`），让 `x` 变成上下文里的普通变量再 `rw`；用会进入 binder 的
`simp only`；用 `simp_rw`（Mathlib），它是「逐条规则各跑一遍 `simp only`」。
-/

example : ∀ x : ℕ, x + 0 + 1 = x + 1 := by
  intro x
  rw [Nat.add_zero]             -- `x` 成了普通变量
example : ∀ x : ℕ, x + 0 + 1 = x + 1 := by
  simp only [Nat.add_zero, implies_true]
example : (fun x : ℕ ↦ x * 1 + 0) = fun x ↦ x := by
  simp_rw [Nat.add_zero, Nat.mul_one]

/-!
**边界二：motive is not type correct。** 若目标里别的东西的**类型**依赖于被重写的项，抽象之后的
`fun _a ↦ …` 可能写不出来。`Fin n` 是「小于 `n` 的自然数」的类型，`v.val` 取出那个数。下面的 `v : Fin n`
的类型含 `n`，把 `n` 换成 `m` 后 `v` 的类型对不上。报错后面还有一大段解释，这里用 `substring` 只核对
前半：motive 是 `fun _a ↦ ↑v < _a`，其中 `v` 的类型 `Fin n` 与 `Fin _a` 对不上。
-/

/-- error: Tactic `rewrite` failed: motive is not type correct:
  fun _a ↦ ↑v < _a -/
#guard_msgs (whitespace := lax, substring := true) in
example (n m : ℕ) (h : n = m) (v : Fin n) : v.val < n := by
  rw [h]

/-!
补救办法：①最好是 `subst h`，把 `m` 整个换成 `n`，依赖关系消失（见 §9）；②`rw!`（Mathlib，
`Mathlib/Tactic/DepRewrite.lean`）在需要时沿等式转运（cast）依赖的项；选项 `castMode` 默认 `.proofs`，
只转运证明项，`(castMode := .all)` 则任何位置都转运。
-/

set_option linter.unusedVariables false in   -- `subst h` 消去 `h`，linter 会误报
example (n m : ℕ) (h : n = m) (v : Fin n) : v.val < n := by
  subst h
  exact v.isLt

/--
trace: n m : ℕ
h : n = m
v : Fin n
⊢ ↑(h ▸ v) < m
-/
#guard_msgs in
example (n m : ℕ) (h : n = m) (v : Fin n) : v.val < n := by
  rw! (castMode := .all) [h]       -- `v` 被转运成 `h ▸ v : Fin m`
  trace_state
  exact Fin.isLt _

/-!
## 6. `simp` 的机制

simplifier（简化器）`simp` 从目标的最内层子项开始，反复用 simp lemma（simp 引理）把子项换成「更简单」
的形式，直到没有引理可用。一个 simp 引理是一个等式 `lhs = rhs`（**从左往右**用）、一个等价 `p ↔ q`，或一个
命题 `p`（当作 `p = True`）。当前可用的 simp 引理的集合叫 simp set（simp 集）。除了引理，`simp` 还用
simproc（用程序而不是等式实现的简化规则，许多用来计算字面量，如 `Nat.reduceAdd`）和 `rfl`。结果称为
simp normal form（simp 正规形）。**`simp` 默认不看上下文里的假设**，要用就写 `simp [h]`；**`simp` 一点也
没改动目标时会报错**（§11）。

先做自己的 simp 引理：给 `double` 配两条引理，`double_zero` 带 `@[simp]`，`double_eq` 不带。
-/

@[simp] theorem double_zero : double 0 = 0 := rfl

theorem double_eq (n : ℕ) : double n = 2 * n := by
  unfold double
  omega

-- `double_zero` 带 `@[simp]` 属性，所以 `simp` 自动用它：
example : double 0 + 5 = 5 := by simp
-- `double_eq` 没有 `@[simp]` 属性，必须手动传；方向是 `double n ⟶ 2 * n`：
example (n : ℕ) : double n + 1 = 2 * n + 1 := by simp [double_eq]
-- 反方向 `← double_eq` 把 `2 * n` 换成 `double n`，于是两边变成同一个项：
example (n : ℕ) : 2 * n + 1 = double n + 1 := by simp [← double_eq]

/-!
挑方向的原则：右边应当比左边「更简单」，且右边不能再被同一条引理匹配（否则无限循环，§11）。`a + b = b + a`
这类**置换引理**左右两边形状相同，`simp` 对它们采用有序重写，只在结果按某个固定的项次序变小时才改写，因此不会
循环。给 `Nat.add_comm`、`Nat.add_left_comm` 就能把加法的各种排列（左结合、右结合都行）排成同一个形状：
-/

example (a b c : ℕ) : a + (b + c) = c + (b + a) := by simp [Nat.add_comm, Nat.add_left_comm]
example (a b c : ℕ) : a + b + c = c + b + a := by simp [Nat.add_comm, Nat.add_left_comm]

/-!
**`simp only [l₁, l₂]`** 只用你列出的引理（外加 `rfl` 和少量内置规则），结果可预测，也最稳定。
**`simp at h`** 简化假设；`simp at h ⊢` 同时简化假设与目标。若某个假设被简化成 `False`，目标直接关闭。
**`simpa using h`** 对目标和 `h` 各做一遍 `simp`，再用 `exact` 对上，代替「`simp at h; exact h`」。
-/

example (n : ℕ) (h : n + 1 = 0) : False := by
  simp at h
example (x y : ℕ) (h : x + 0 = y) : x = y := by
  simpa using h

/-!
**`simp?`** 执行 `simp`，并打印它用到的引理，写成 `simp only [...]`，可以复制回去替换（名字随导入的
文件而变，这里是 `add_zero`）。复制之后还要检查：下面的输出里 `Nat.add_left_cancel_iff` 其实没有派上用场，
`simp only` 版本会被 `linter.unusedSimpArgs` 警告，删掉即可。Mathlib 的风格是：不要把末尾的 `simp`
换成 `simp?` 的结果；只有 `simp` 之后紧跟 `rw`、`exact` 这类依赖其输出形状的策略时，`linter.flexible`
才要求改成 `simp only`。
-/

/--
info: Try this:
  [apply] simp only [add_zero, Nat.add_left_cancel_iff]
-/
#guard_msgs in
example (x : ℕ) : x + 0 + 1 = x + 1 := by simp?

/--
warning: This simp argument is unused:
  Nat.add_left_cancel_iff

Hint: Omit it from the simp argument list.
  [apply] simp only [add_zero]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
-/
#guard_msgs in
example (x : ℕ) : x + 0 + 1 = x + 1 := by simp only [add_zero, Nat.add_left_cancel_iff]

/-!
## 7. simp 正规形与配置选项

`simp` 会把假设与目标改写成固定的写法，你得认得它们，否则 `exact h` 会对不上。最常见的四条：
`a ≠ b ⟶ ¬a = b`（`ne_eq`）、`Nat.succ n ⟶ n + 1`（`Nat.succ_eq_add_one`）、`x ≥ y ⟶ y ≤ x`
（`ge_iff_le`）、`¬x < y ⟶ y ≤ x`（`not_lt`，在线性序上）。被改写的假设在上下文里的位置可能变动
（下面 `h₄` 排到了 `h₂` 前面）。再用 `simp only` 逐条点名：四条引理都没被 `linter.unusedSimpArgs`
报告为多余，说明各自都派上了用场。
-/

set_option linter.unusedVariables false in   -- `simp at` 之后 linter 误报「未引用」
/--
trace: a b n m : ℕ
x y : ℝ
h₁ : ¬a = b
h₄ : n + 1 = m
h₂ : y ≤ x
h₃ : y ≤ x
⊢ True
-/
#guard_msgs in
example (a b n m : ℕ) (x y : ℝ) (h₁ : a ≠ b) (h₂ : ¬x < y) (h₃ : x ≥ y) (h₄ : Nat.succ n = m) :
    True := by
  simp at h₁ h₂ h₃ h₄
  trace_state
  trivial

set_option linter.unusedVariables false in
example (a b n m : ℕ) (x y : ℝ) (h₁ : a ≠ b) (h₂ : ¬x < y) (h₃ : x ≥ y) (h₄ : Nat.succ n = m) :
    True := by
  simp only [ne_eq, Nat.succ_eq_add_one, ge_iff_le, not_lt] at h₁ h₂ h₃ h₄
  trivial

/-!
`simp` 也把假设 `h : a ≠ b` 当作 `(a = b) = False` 来用；把命题 `hp : p` 当作 `p = True` 来用。
**配置选项**用 `+flag`、`-flag`、`(opt := v)` 的语法（旧写法 `simp_arith` 已弃用，在 4.35 里直接报错，
见第 2 章第 14 节）；`simp +arith` 打开 `ℕ`、`ℤ` 上线性算术的正规化（第 2 章第 10 节）。`simp_all` 对
所有假设与目标互相简化，直到稳定，它的策略与调试留到第 10 章。
-/

example (a b : ℕ) (h : a ≠ b) : (a = b) = False := by simp [h]
example (x y : ℤ) : x + y + 3 ≤ y + x + 5 := by simp +arith
example (a b : ℕ) (h₁ : a = b) (h₂ : b = 3) : a + 1 = 4 := by simp_all

/-!
## 8. `calc` 的完整语法

`calc` 把一串关系连成一条链。第一步写成完整的关系 `a = b := proof`；之后每一步以 `_` 开头，`_` 代表
上一步的右端。**首行有两种写法**：把第一步写在 `calc` 同一行；或者 `calc a` 单独占一行，后面每一步都以
`_` 开头。策略模式里本书按第 2 章的排版：`calc` 单独一行，步骤另起一行。
-/

example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c :=
  calc a = b := h₁
    _ = c := h₂
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c :=
  calc a
    _ = b := h₁
    _ = c := h₂

/-!
`=`、`≤`、`<` 能混写，靠的是 `Trans` 类（第 2 章第 11 节留下的问题）：`Trans r s t` 表示「`r a b` 与
`s b c` 能推出 `t a c`」，`calc` 对相邻两步的关系各查一次实例，结论的关系就是 `t`。三个名字别混：
`Eq.trans` 是等式的传递（项），`trans` 是策略（§9），`Trans` 是这个类：
-/

example : Trans (· ≤ · : ℕ → ℕ → Prop) (· < ·) (· < ·) := inferInstance

/-!
没有对应实例的关系不能相接，比如 `≤` 后接 `≠`。在**策略模式**里，如果链的左端与目标的左端一致、关系又
能由 `Trans` 与目标的关系拼接，而链的右端和目标的右端不同，`calc` 不直接报错，而是把差额作为一个新目标
`calc.step` 留给你（§11）。
-/

set_option pp.mvars false in
/-- error: invalid 'calc' step, failed to synthesize `Trans` instance -/
#guard_msgs (whitespace := lax, substring := true) in
example (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b ≠ c) : a ≠ c := by
  calc
    a ≤ b := h₁
    _ ≠ c := h₂

/-!
## 9. `congr`、`subst`、`ext`、`funext`、`symm`、`trans`

**`congr`** 把 `f a₁ … = f b₁ …` 拆成各个参数的等式。一个撞词提示：这里的 congruence（同余）指「函数保持
等式」，与数论里的同余无关。`congr 1` 只拆一层；拆出的新目标若能由上下文的假设直接关闭，就自动关闭，所以
下面把两个等式藏在一个合取里：
-/

example (a b c d : ℕ) (h : a = b ∧ c = d) : a + c = b + d := by
  congr 1
  · exact h.1           -- ⊢ a = b
  · exact h.2           -- ⊢ c = d

/-!
**`subst h`**（`h : a = b`，其中至少一端是局部变量）把变量整个消去，比 `rw` 彻底：连假设与别的类型里的依赖
一起换。两端都是变量时，`b` 被换成 `a`：
-/

/--
trace: a : ℕ
h₂ : a + 1 = 3
⊢ a + 1 = 3
-/
#guard_msgs in
example (a b : ℕ) (h : a = b) (h₂ : a + 1 = 3) : b + 1 = 3 := by
  subst h               -- 两端都是变量：`b` 被换成 `a`
  trace_state
  exact h₂

/-!
**外延性。** 要从「每一点相等」推出函数相等，用 `funext`（函数的 extensionality（外延性）；它是一条定理，
只依赖公理 `Quot.sound`）。`ext` 是通用版本：它按目标的类型挑一条带 `@[ext]` 属性的外延性引理（函数类型
用 `funext`，`ℕ × ℕ` 用 `Prod.ext`，登记在 `Init/Ext.lean`）。
-/

/--
info: 'funext' depends on axioms: [Quot.sound]
-/
#guard_msgs in
#print axioms funext

example (f g : ℕ → ℕ) (h : ∀ x, f x = g x) : f = g := funext h
example (f g : ℕ → ℕ) (h : ∀ x, f x = g x) : f = g := by
  ext x                 -- ⊢ f x = g x
  exact h x

/-!
**`symm`** 把目标 `a = b` 翻成 `b = a`。**`trans b`**（来自 Batteries）把 `a = c` 拆成 `a = b` 与
`b = c` 两个目标。项模式里对应的是 `h.symm`、`h₁.trans h₂`（§1）。
-/

example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : c = a := by
  symm                  -- ⊢ a = c
  trans b
  · exact h₁            -- ⊢ a = b
  · exact h₂            -- ⊢ b = c

/-!
## 10. 证明的骨架

`have`、`change`、`suffices` 在第 4 章 §8 已经引入（`show T` 同样接受定义相等的 `T`，但按那里的风格只用来
标明目标）。本章要的是工作顺序：先写骨架，每个 `have` 都先用 `sorry`；确认骨架本身能把定理推出来；再
逐个填空。例子：函数 `f` 满足 `f (x + 1) = f x + 2`，要证 `f (x + 2) = f x + 4`。先看填空前的骨架：
只有 `sorry` 的 `have`，但最后一行已经把结论推出来了。
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (f : ℝ → ℝ) (hf : ∀ x, f (x + 1) = f x + 2) (x : ℝ) : f (x + 2) = f x + 4 := by
  have h1 : f (x + 1) = f x + 2 := sorry
  have h2 : f (x + 1 + 1) = f (x + 1) + 2 := sorry
  rw [show x + 2 = x + 1 + 1 by ring, h2, h1]; ring

/-!
再逐个填空。`h1`、`h2` 都是 `hf` 的实例；最后一步也可以写成 `calc`，其中 `congrArg f` 负责改写参数：
-/

example (f : ℝ → ℝ) (hf : ∀ x, f (x + 1) = f x + 2) (x : ℝ) : f (x + 2) = f x + 4 := by
  have h1 : f (x + 1) = f x + 2 := hf x
  have h2 : f (x + 1 + 1) = f (x + 1) + 2 := hf (x + 1)
  calc
    f (x + 2) = f (x + 1 + 1) := congrArg f (by ring)
    _ = f (x + 1) + 2 := h2
    _ = f x + 4 := by rw [h1]; ring

/-!
## 11. 常见错误

已捕获过的错误：`rfl` 对 `0 + n = n` 失败（§2）；`decide` 含自由变量、在 `ℝ` 上失败（§3）；`rw` 进
binder、`motive is not type correct`（§5）；`simp` 之后 `exact h` 对不上（先看 §7 的正规形）。再补三个。

**① `simp` 没有任何进展。** 目标里没有 simp 集能处理的东西（`simp` 不看假设 `h`）时，`simp` 报错而不是
默默不动：
-/

/--
error: `simp` made no progress
-/
#guard_msgs in
example (x y : ℕ) (h : x ≤ y) : x ≤ y := by simp

/-!
**② 漏写 `calc` 的最后一步。** 链到 `b` 就停了，目标是 `a = c`，于是多出一个 `calc.step` 目标：
-/

/--
error: unsolved goals
case calc.step
a b c : ℕ
h₁ : a = b
h₂ : b = c
⊢ b = c
-/
#guard_msgs in
example (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : a = c := by
  calc
    a = b := h₁

/-!
**③ 循环的 simp 引理。** `← Nat.add_zero` 把任何 `a` 换成 `a + 0`，新的 `a` 又可以继续换；`simp` 先警告，
最终撞上递归深度上限：
-/

/--
warning: Possibly looping simp theorem: `← Nat.add_zero`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (a : ℕ) : a = a + 0 := by
  simp [← Nat.add_zero]

/-!
## 练习

下列练习在 `ℕ`、`ℤ`、`ℝ` 与函数上混用 `rw`、`simp`、`calc`。★ 直接应用，★★ 综合两个想法，★★★ 需要新
想法。其中 `ex_5_2`、`ex_5_4`、`ex_5_6`、`ex_5_7` 复习第 2 章的工具，`ex_5_1` 复习第 3 章，`ex_5_8`
复习第 4 章。
-/

/-- 练习 5.1（★）：项模式（第 3 章），用 `Eq.trans` 与 `Eq.symm`（或点记号）。 -/
theorem ex_5_1 (a b c : ℕ) (h₁ : a = b) (h₂ : c = b) : a = c := sorry

/-- 练习 5.2（★）：先 `rw [h]`，再用第 2 章的 `ring` 收尾。 -/
theorem ex_5_2 (a b : ℤ) (h : a = b + 1) : a ^ 2 = b ^ 2 + 2 * b + 1 := sorry

/-- 练习 5.3（★）：用 `rw [← h] at h₁` 把 `h₁` 里的 `b` 换成 `a + 1`，再用 `omega`。 -/
theorem ex_5_3 (a b : ℕ) (h : a + 1 = b) (h₁ : b * 2 = 8) : a = 3 := sorry

/-- 练习 5.4（★★）：先 `unfold double at h`（§2），再用第 2 章的 `omega`。 -/
theorem ex_5_4 (n : ℕ) (h : double n = 0) : n = 0 := sorry

/-- 练习 5.5（★★）：`rw ... at`，带副条件的引理（§4）。 -/
theorem ex_5_5 (m n k : ℕ) (h : m ≤ n) (h₁ : n - m + m = k) : n = k := sorry

/-- 练习 5.6（★★）：`calc` 混用 `≤`、`<`、`=`（第 2 章的 `linarith`）。 -/
theorem ex_5_6 (a b : ℝ) (h₁ : a ≤ b) (h₂ : b < 2) : a + b < 4 := sorry

/-- 练习 5.7（★★）：`calc` 分三步，各步用不同的策略：`ring`、`rw`、`norm_num`。 -/
theorem ex_5_7 (x y : ℝ) (h₁ : x + y = 5) (h₂ : x * y = 6) : x ^ 2 + y ^ 2 = 13 := sorry

/-- 练习 5.8（★★）：先用第 4 章的 `obtain` 拆开存在量词，再用 `subst`。 -/
theorem ex_5_8 (f : ℕ → ℕ) (h : ∃ a, a = 2 ∧ f a = 3) : f 2 = 3 := sorry

/-- 练习 5.9（★★）：在 `fun` 里重写；`rw` 不行，换 `funext` 或 `simp_rw`。 -/
theorem ex_5_9 (f : ℕ → ℕ) (h : ∀ x, f x = x + 0) :
    (fun x ↦ f x + 1) = fun x ↦ x + 1 := sorry

/-- 练习 5.10（★★）：先把骨架（带 `sorry` 的 `have`）写出来，确认它推得出结论，再逐个填空。 -/
theorem ex_5_10 (f : ℕ → ℕ) (hf : ∀ x, f (x + 1) = f x + 3) (x : ℕ) :
    f (x + 2) = f x + 6 := sorry

/-- 练习 5.11（★★★）：`rw [h]` 会遇到 motive 问题（§5），换一个办法。 -/
theorem ex_5_11 (n m : ℕ) (h : n = m) (v : Fin n) (w : Fin m) (hv : v.val = w.val) :
    (h ▸ v : Fin m) = w := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| `Eq` | `Eq.refl`、`rfl`、`h.symm`、`h₁.trans h₂`、`h ▸ e` | 项模式里直接构造等式 |
| 定义相等 | `rfl`、`by rfl`、`unfold f` | 两边按 β/δ/ι 规约相同；`0 + n` 对变量 `n` 不行 |
| `decide` | `decide`、`decide +revert`、`decide +kernel` | 小的可判定命题（`≠`、`<`、有界 `∀`）；`ℝ` 上无效 |
| `rw` | `rw [h]`、`[← h]`、`at h ⊢`、`nth_rw n [h]` | 精确改写一个子项；进不了 binder |
| `rw!` | `rw! [h]`、`rw! (castMode := .all) [h]` | motive is not type correct 时 |
| `simp` | `simp`、`simp only [l]`、`simp [h]`、`simp at h`、`simpa` | 到正规形；`simp?` 写出 `simp only` |
| 配置 | `simp +arith`、`simp_all`、`simp_rw [l₁, l₂]` | 线性算术；全部互相简化；按序逐条重写、可进 binder |
| `calc` | `calc a = b := …` 换行 `_ ≤ c := …` | 等式与不等式的链；靠 `Trans` 混写 |
| 结构性步骤 | `congr 1`、`congrArg f h`、`congrFun h x` | 把等式推到函数的参数或函数值上 |
| `subst`、外延性 | `subst h`、`funext x`、`ext x` | 消去变量，比 `rw` 彻底；函数相等拆成逐点相等 |
| 方向与拼接 | `symm`、`trans b` | 翻转等式、拆传递链 |
| 骨架 | `have h : T := sorry`、`change`、`suffices` | 先搭骨架（`sorry`），再填 |

## 延伸阅读

- *Theorem Proving in Lean 4*：「Quantifiers and Equality」一章的 Equality 与 Calculational Proofs 两节；
  「Tactics」一章的 Rewriting 与 Using the Simplifier 两节。
- *Lean Language Reference* 4.35.0（`https://lean-lang.org/doc/reference/4.35.0/`）：「The Type System」
  开头的 Definitional equality 一节；「Basic Propositions」的 Propositional Equality 一节；「Basic Types」
  下「Natural Numbers」一节（`Nat` 字面量运算的加速）；「The Simplifier」一章（simp 集与有序重写）。
- 源码：`Init/Prelude.lean`（`Eq`、`Nat.add`）；`Init/Tactics.lean`（`rw`、`simp`、`decide` 的文档注释）；
  `Lean/Meta/Tactic/Rewrite.lean`（`motive is not type correct` 的出处）；`Init/Ext.lean`（`@[ext]` 属性）；
  Mathlib 的 `Mathlib/Tactic/NthRewrite.lean`、`SimpRw.lean`、`DepRewrite.lean`。
- 本书第 6 章（`Eq` 的消去子与归纳）、第 10 章（`simp` 深入：`simp_all`、循环、副条件处理器）、第 13 章
  （`conv`、`convert`、`congr!`）、第 28 章（定义相等与透明度的内核机制）。
-/

end Lean4Learn.Ch05

end
