module

public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter
public import Plausible
public import Std.Tactic.Do
public import Std.WP

/-!
# 第 25 章　程序验证

前一章把 Lean 当作编程语言来用；本章回答下一个问题：怎样证明程序是对的。做法是先把
specification（规格说明）写成定理，再用归纳证明；同时说明什么时候不必证明（`#guard`、`plausible`），
什么时候证明代价太高（`native_decide`），以及 4.35 里实验性的 `vcgen`。读完后你能给自己写的递归函数
陈述并证明性质，并证明一个插入排序既有序又是原列表的 permutation（重排）。

## 学习目标
- 先证自己的函数等于库函数，再借库里的定理推出其余性质（§1），并把带 accumulator（累加器）的
  线性版本接到规格说明上（§2）；
- 在多分支的良基递归函数上用 `fun_induction`，并与 `Nat.gcd` 对账（§3）；
- 知道默认的终止证明何时不够、怎样用 `decreasing_by` 补上，以及 fuel（燃料）怎样替代 `partial`（§4）；
- 区分 `decide`、`decide +kernel`、`native_decide`，用 `#print axioms` 看依赖的公理（§5）；
- 在 `Array` 下标、`Fin` 与 subtype（子类型）里携带证明（§6、§7）；
- 用 `plausible` 在证明前寻找 counterexample（反例）（§8）；
- 证明插入排序的输出有序（`List.Pairwise`）且是输入的重排（`List.Perm`）（§9）；
- 知道 `vcgen` 怎样为命令式程序生成 verification condition（验证条件），以及它的导入、选项与
  现状（§10）。

## 前置知识
第 2 章（`omega`）、第 4 章、第 5 章（`simp`、`rw`）、第 6 章（结构递归、等式引理、`fun_induction`、
`termination_by`、`decide`，尤其 §5、§9、§10）、第 7 章（子类型）、第 13 章（§3 的强归纳与
`induction … generalizing`），第 24 章（`List`、`Array`、`do`、`#guard`、§9 的 `partial`）。
用到的函数都在文件里重写一遍。
-/

@[expose] public section

namespace Lean4Learn.Ch25

/-!
## 1. 规格说明就是定理

验证的第一步是把「对」翻译成命题。沿用第 6 章的 `app`（追加，§6）和 `rev`（反转，练习前的定义块），
那里的正文与练习已经逐条证过长度、结合律等性质。这次只证**一条**规格说明，把自己的函数和库函数对上：
`app` 就是 `++`，`rev` 就是 `List.reverse`；证完之后，库里关于 `++` 与 `reverse` 的全部定理立刻
对我们的版本可用。
-/

section Lists

variable {α : Type*}

/-- 列表追加。 -/
def app : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys

/-- 列表反转（朴素版）。 -/
def rev : List α → List α
  | [] => []
  | x :: xs => app (rev xs) [x]

-- 先检查几个具体的值。`#guard`（第 24 章）只检查写下的例子，不是证明。
#guard app [1, 2] [3] = [1, 2, 3]
#guard rev [1, 2, 3] = [3, 2, 1]

-- 归纳的写法与第 6 章相同：`nil` 分支两边都定义相等于 `ys`；`cons` 分支展开一步再用 `ih`。
theorem app_eq_append (xs ys : List α) : app xs ys = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]

theorem rev_eq_reverse (xs : List α) : rev xs = xs.reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, ih, app_eq_append]

/-!
有了这两条，别的性质都不必再归纳：把 `app`、`rev` 换成 `++`、`reverse`，剩下的由库里的 simp
引理完成。例如 `List.reverse_reverse` 已经是 simp 引理，所以：
-/

theorem rev_rev (xs : List α) : rev (rev xs) = xs := by
  simp [rev_eq_reverse]

/-!
## 2. 带累加器的版本

朴素 `rev` 每步调用一次要走完左边列表的 `app`；带累加器参数的写法每步只做一次 `::`。归纳时累加器会变，
所以先证更强的 `revAux xs acc = xs.reverse ++ acc`，并用 `induction xs generalizing acc` 让归纳假设
对**所有** `acc` 成立（原因与忘记时的报错见第 13 章 §3.1）。
-/

/-- 线性时间的反转：第二个参数是累加器。 -/
def revAux : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => revAux xs (x :: acc)

theorem revAux_eq (xs acc : List α) : revAux xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [revAux]
  | cons x xs ih => simp [revAux, ih]

/-- 线性反转的规格说明：从空累加器出发就是 `rev`。 -/
theorem revAux_nil (xs : List α) : revAux xs [] = rev xs := by
  simp [revAux_eq, rev_eq_reverse]

end Lists

/-!
## 3. 多分支的 `fun_induction`：减法版 Euclid 算法

良基递归的函数没有现成的结构归纳。一条路是对终止度量做强归纳（第 13 章 §3.2），再自己展开定义、
证明每个递归调用的度量更小——第 24 章练习 24.15 就这样证明 `log2'` 的性质。更方便的接口是
`fun_induction f args`（第 6 章 §5）：它按 `f` 自己的递归路径分情形，每个递归调用自动带一个归纳
假设，分支与函数体一一对应。这里的函数有**四条**路径、两个会变的参数，正好看清分支的命名与绑定。
减法版 Euclid 算法 `sgcd` 重复地用大数减小数，直到有一个为 0；终止度量取 `a + b`（第 6 章 §9），
默认策略能证 `a + (b - a) < a + b`：
-/

/-- 减法版 Euclid 算法。 -/
def sgcd (a b : ℕ) : ℕ :=
  if a = 0 then b
  else if b = 0 then a
  else if a ≤ b then sgcd a (b - a)
  else sgcd (a - b) b
termination_by a + b

#guard sgcd 12 18 = 6

/-!
下面证明 `sgcd` 与核心库的 `Nat.gcd` 相等。分支名是 `case1` … `case4`，对应函数体的四条路径；
绑定的变量依次是函数的参数、路径上的条件、归纳假设。`trace_state` 打印 `case3` 的状态：`ih` 说
递归调用等于库函数，目标里的 `sgcd a b` 已经被展开成一层 `sgcd a (b - a)`（`fun_induction` 默认用
带展开的归纳原理 `sgcd.induct_unfolding`），所以 `rw [ih]` 之后只剩库里的 gcd 引理：
-/

/--
trace: case case3
a b : ℕ
h₁ : ¬a = 0
h₂ : ¬b = 0
h : a ≤ b
ih : sgcd a (b - a) = a.gcd (b - a)
⊢ sgcd a (b - a) = a.gcd b
-/
#guard_msgs in
theorem sgcd_eq (a b : ℕ) : sgcd a b = Nat.gcd a b := by
  fun_induction sgcd a b with
  | case1 b => simp
  | case2 a h => simp
  | case3 a b h₁ h₂ h ih =>
    trace_state
    rw [ih]
    exact Nat.gcd_sub_self_right h
  | case4 a b h₁ h₂ h ih =>
    rw [ih]
    exact Nat.gcd_sub_self_left (by omega)

/-! **引理名从哪来？** 把 `case3` 里 `rw [ih]` 之后的目标单独写成 `example`，交给 `exact?`（第 9 章）： -/

/--
info: Try this:
  [apply] exact Nat.gcd_sub_self_right h
-/
#guard_msgs (whitespace := lax) in
example (a b : ℕ) (h : a ≤ b) : a.gcd (b - a) = a.gcd b := by exact?

/-! `case4` 的 `Nat.gcd_sub_self_left` 按命名规范（`_left` / `_right` 指被减的是哪一边）可以猜到；
`(by omega)` 证明它的前提 `b ≤ a`，来自路径上的 `¬a ≤ b`。 -/

/-!
## 4. 终止性：默认策略何时不够，不能终止怎么办

默认的 `decreasing_tactic` 带着 `omega`（第 6 章 §9），所以 `sgcd` 这样线性的下降不需要
`decreasing_by`。下降依赖非线性事实时，`omega` 无能为力：`n / b < n` 需要乘除法性质。报错显示
卡住的目标，`h : 1 < b ∧ 0 < m` 正是 `if h :` 带进来的条件（失败的定义放进 `example` 的 `let rec`，
因为写成 `def` 无法撤销）：
-/

/--
error: failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
b m : ℕ
h : 1 < b ∧ 0 < m
⊢ m / b < m
-/
#guard_msgs in
example (n b : ℕ) : ℕ :=
  let rec go (m : ℕ) : ℕ := if h : 1 < b ∧ 0 < m then go (m / b) + 1 else 0
  termination_by m
  go n

/-- 连续除以 `b` 直到 0 的次数（即 `b` 进制的位数）；`b ≤ 1` 或 `n = 0` 时为 0。 -/
def logSteps (n b : ℕ) : ℕ :=
  if h : 1 < b ∧ 0 < n then logSteps (n / b) b + 1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self h.2 h.1

#guard logSteps 1000 10 = 4
#guard logSteps 0 10 = 0
#guard logSteps 5 1 = 0

/-!
Collatz 序列是否总停止至今未知，所以无法给出终止性证明。办法有二：`partial`（第 24 章 §9：证明器
看到的是不透明常量，不能靠展开实现来证明它算出的值），或者加一个燃料参数：递归深度由燃料显式限制，
函数变成关于燃料的结构递归，`decide` 可以直接算。代价是语义变了：燃料不够时它返回当前的 `steps`，
所以陈述性质时要把燃料考虑进去，例如对任意燃料都成立的下界（ex_25_9）：
-/

/-- 带燃料的 Collatz：燃料用完就停。对燃料的递归是结构递归。 -/
def collatzFuel : ℕ → ℕ → ℕ → ℕ
  | 0, _, steps => steps
  | fuel + 1, n, steps =>
    if n ≤ 1 then steps
    else if n % 2 = 0 then collatzFuel fuel (n / 2) (steps + 1)
    else collatzFuel fuel (3 * n + 1) (steps + 1)

#guard collatzFuel 200 27 0 = 111
example : collatzFuel 100 6 0 = 8 := by decide

/-!
## 5. 有限检查：`decide`、`decide +kernel`、`native_decide`

对封闭的、可判定的命题，可以让机器直接算。`decide` 在 elaborator（精译器；另译繁饰器）里把目标
的 `Decidable` 实例求值；三种策略的区别在于谁来求值：

| 策略 | 谁求值 | 专属公理 | 对良基递归函数 |
|---|---|---|---|
| `decide` | 精译器里的 whnf | 无专属公理 | 默认失败：良基递归定义默认不可约（下例） |
| `decide +kernel` | 内核，不看 reducibility（可约性） | 无专属公理 | 度量取值于 `ℕ` 时可以（`sgcd`）；否则不保证 |
| `native_decide` | 编译器（与 `#eval` 同一套）编译后求值 | **每次使用一条** | 可以 |

第 6 章 §9 的 `myGcd` 演示过 `decide` 被不可约挡住；`sgcd` 同样如此：
-/

/--
error: Tactic `decide` failed to reduce
  @decide (sgcd 12 18 = 6) (instDecidableEqNat (sgcd 12 18) 6)
to `true` or `false`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at
  (sgcd 12 18).beq 6
-/
#guard_msgs in
example : sgcd 12 18 = 6 := by decide

/-!
绕过的办法：`decide +kernel`；`simp [sgcd]` 反复用等式引理（得到证明而不是计算）；`cbv`
（按值调用式化简，4.29 引入时是实验性的，4.30 起为正式策略）；以及 `native_decide`。`decide` 的文档
（`Init/Tactics.lean`）另外提醒：用良基递归定义的 `Decidable` 实例，`decide +kernel` 也可能失败。
-/

example : sgcd 12 18 = 6 := by decide +kernel
example : sgcd 12 18 = 6 := by simp [sgcd]
example : sgcd 12 18 = 6 := by cbv
example : sgcd 12 18 = 6 := by native_decide

/-! `native_decide` 用编译器求值，再用一条专属公理断言「编译器说它为真」。用 `#print axioms` 比较
三者（`demo_native` 是本章唯一导出新公理的声明；其余的 `native_decide` 都用 `example`）： -/

theorem demo_decide : (2 : ℕ) + 2 = 4 := by decide
theorem demo_kernel : sgcd 12 18 = 6 := by decide +kernel
theorem demo_native : sgcd 12 18 = 6 := by native_decide

/-- info: 'Lean4Learn.Ch25.demo_decide' does not depend on any axioms -/
#guard_msgs in
#print axioms demo_decide

/-- info: 'Lean4Learn.Ch25.demo_kernel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms demo_kernel

/--
info: 'Lean4Learn.Ch25.demo_native' depends on axioms: [propext, Quot.sound,
 demo_native._native.native_decide.ax_1_1]
-/
#guard_msgs (whitespace := lax) in
#print axioms demo_native

/-!
读法：两个 `sgcd` 值都依赖标准公理 `propext`、`Quot.sound`（第 28 章），`native_decide` 另外多出
一条以定理名命名的专属公理。

`native_decide` 等于把整个 Lean 编译器与运行时加入 trusted computing base（可信基），而不只是
小而可审计的内核，理论上能借此证明 `False`，所以 Mathlib 不允许它。linter（代码检查器）选项
`linter.style.native`（旧名 `linter.style.nativeDecide` 自 2026-08-28 起弃用）默认关闭，但在 Mathlib
构建所用的标准集 `linter.mathlibStandardSet` 里（`Mathlib/Init.lean`）。打开后会收到警告：
-/

section NativeLint

set_option linter.style.native true

/--
warning: Using `native_decide` is not allowed in mathlib: because it trusts the entire Lean
compiler (not just the Lean kernel), it could quite possibly be used to prove `False`.

Note: This linter can be disabled with `set_option linter.style.native false`
-/
#guard_msgs in
example : (2 : ℕ) + 2 = 4 := by native_decide

end NativeLint

/-! 选择规则：能 `simp` / `omega` / `decide` 就用它们，被不可约挡住时用 `decide +kernel`；
`native_decide` 只用于不打算进 Mathlib 的文件，并在注释里写明依赖了它。 -/

/-!
## 6. 数组下标与 `Fin`

三种下标 `a[i]`、`a[i]?`、`a[i]!` 见第 24 章 §3。本节的问题是让**类型自己**携带「下标合法」的证明：
`Fin n` 是「小于 `n` 的自然数」，`i : Fin a.size` 作下标永远合法。
-/

example (a : Array ℕ) (i : Fin a.size) : ℕ := a[i]

#guard #[10, 20, 30][5]? = none

/-! 线性查找：返回类型 `Option (Fin a.size)` 保证若有结果，下标一定合法。`where` 里的 `go` 是独立的
递归函数（全名 `findIdx.go`），终止度量 `a.size - i` 随 `i` 增加而下降。 -/

/-- 在数组中从左到右查找等于 `x` 的位置。 -/
def findIdx (a : Array ℕ) (x : ℕ) : Option (Fin a.size) :=
  go 0
where
  go (i : ℕ) : Option (Fin a.size) :=
    if h : i < a.size then
      if a[i] = x then some ⟨i, h⟩ else go (i + 1)
    else none
  termination_by a.size - i

#guard (findIdx #[5, 7, 9] 7).map Fin.val = some 1
#guard (findIdx #[5, 7, 9] 4).map Fin.val = none

/-!
规格说明有三部分：（a）找到的位置上确实是 `x`；（b）返回 `none` 则数组里没有 `x`；（c）返回的
是**第一个**匹配。本章只证（a），（b）是 ex_25_15，（c）不证。`findIdx.go` 有三条路径，所以
`fun_induction` 有三个分支：命中（`case1`）、未命中继续（`case2`，带归纳假设）、越界（`case3`，
结果是 `none`，与假设 `some i` 矛盾）。假设 `h` 依赖会变的 `j`，`fun_induction` 像
`induction … generalizing`（第 13 章 §3.1）那样自动把它放回目标再引入，所以 `ih` 是一个**蕴涵**，
要先喂给它 `h`（不必像练习 6.11 那样手写 `revert`）。`case2` 的状态：
-/

/--
trace: case case2
a : Array ℕ
x : ℕ
i : Fin a.size
j : ℕ
hj : j < a.size
hx : ¬a[j] = x
ih : findIdx.go a x (j + 1) = some i → a[i] = x
h : findIdx.go a x (j + 1) = some i
⊢ a[i] = x
-/
#guard_msgs in
theorem findIdx_go_some (a : Array ℕ) (x j : ℕ) (i : Fin a.size)
    (h : findIdx.go a x j = some i) : a[i] = x := by
  fun_induction findIdx.go a x j with
  | case1 j hj hx =>
    -- `Option.some.inj` 把 `some ⟨j, hj⟩ = some i` 化成 `⟨j, hj⟩ = i`，`rfl` 代入
    obtain rfl := Option.some.inj h
    exact hx
  | case2 j hj hx ih =>
    trace_state
    exact ih h
  | case3 j hj => simp at h

/-!
## 7. 子类型：把规格说明写进返回类型

另一种验证风格是 intrinsic verification（内在验证）：不单独写定理，而是让类型本身携带性质。
子类型（第 7 章）`{n : ℕ // 0 < n}` 的项是一个数加上一个证明；函数要返回它，就必须同时
产出证明，调用者拿到结果时自动得到性质（`.property`）。参数也可以用子类型表达
precondition（前置条件）。
-/

/-- 后继一定是正数：性质在返回类型里。 -/
def posSucc (n : ℕ) : {m : ℕ // 0 < m} := ⟨n + 1, Nat.succ_pos n⟩

/-- 非空列表的首元素：前置条件写在参数类型里，函数体用 `.property` 取出证明。 -/
def headS {α : Type*} (l : {l : List α // l ≠ []}) : α := l.val.head l.property

/-- 反转保持长度：规格说明是返回类型的一部分。 -/
def revS {α : Type*} (xs : List α) : {ys : List α // ys.length = xs.length} :=
  ⟨rev xs, by rw [rev_eq_reverse]; exact List.length_reverse⟩

example (n : ℕ) : 0 < (posSucc n).val := (posSucc n).property
#guard headS ⟨[3, 1], by decide⟩ = 3
#guard (revS [1, 2, 3]).val = [3, 2, 1]

/-!
## 8. 先找反例，再证明：`plausible` 与 `#guard`

写不出证明的时候，常常是陈述本身错了。`plausible`（包 `Plausible`，见文件头）做 property-based
testing（性质测试）：随机生成输入，在 100 个样本里找反例；找到就报错并打印尽量缩小后的反例
（greedy shrinking，不保证最小）。`randomSeed` 固定随机种子，让输出可复现。一个故意写错的性质：
-/

/--
error:
===================
Found a counter-example!
xs := [1]
ys := [0]
issue: [1, 0] = [0, 1] does not hold
(3 shrinks)
-------------------
-/
#guard_msgs in
example (xs ys : List ℕ) : xs ++ ys = ys ++ xs := by
  plausible (config := { randomSeed := some 7 })

/-!
没找到反例时，`plausible` **把目标当作 `sorry` 关闭**：只是通过了测试，并没有证明。
（`quiet := true` 关掉了「没找到反例」的提示，所以只剩 `sorry` 警告。）
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (xs : List ℕ) : (rev xs).length = xs.length := by
  plausible (config := { randomSeed := some 7, quiet := true })

/-!
用它抓真实的 bug：`insBad` 想写插入排序的插入，遇到相等元素时却丢了一个。没有重复元素的
`#guard` 全部通过；`plausible` 会随机造出重复元素：
-/

/-- 有 bug 的插入：相等时丢掉新元素。 -/
def insBad (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insBad x ys

#guard insBad 2 [1, 3] = [1, 2, 3]
#guard insBad 4 [1, 2, 3] = [1, 2, 3, 4]

/--
error:
===================
Found a counter-example!
x := 2
l := [2]
issue: 1 = 2 does not hold
(0 shrinks)
-------------------
-/
#guard_msgs in
example (x : ℕ) (l : List ℕ) : (insBad x l).length = l.length + 1 := by
  plausible (config := { randomSeed := some 7 })

/-!
## 9. 案例：插入排序的正确性

排序程序的正确性有两半，缺一不可：输出**有序**，且输出是输入的**重排**。只证前者，
`fun _ ↦ []` 就是「排序函数」；只证后者，恒等函数就是。有序用 `List.Pairwise (· ≤ ·)`
（任意靠前的元素 `≤` 靠后的元素）；重排用 `List.Perm`。

函数本身两行：`ins x l` 把 `x` 插进有序的 `l` 里正确的位置，`isort` 对列表逐个插入。`ins` 就是
`insBad` 的修正：相等的情形并进 `x ≤ y`，不再丢元素（长度性质是 ex_25_12）。
-/

/-- 把 `x` 插入一个（假定有序的）列表。 -/
def ins (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

/-- 插入排序。 -/
def isort : List ℕ → List ℕ
  | [] => []
  | x :: xs => ins x (isort xs)

#guard isort [5, 2, 9, 1, 5, 6] = [1, 2, 5, 5, 6, 9]

/-!
### 9.1 重排

重排的谓词 `List.Perm` 有记号 `l₁ ~ l₂`，它是 `List` 命名空间里 scoped 的记号，所以要 `open List`：
-/

open List in
example (l : List ℕ) : l ~ l := List.Perm.refl l

/-!
有序的谓词在旧教程里常写 `List.Sorted (· ≤ ·) l`，它在 Mathlib 中已不存在；本章规格说明统一写
`Pairwise`：
-/

/-- error: Unknown constant `List.Sorted` -/
#guard_msgs in
#check List.Sorted

/-!
要证 `ins x l` 是 `x :: l` 的重排，对 `l` 归纳，`cons` 分支按 `x ≤ y` 分情形。若 `x ≤ y`，
`ins x (y :: ys)` 按定义就是 `x :: y :: ys`，用 `Perm.refl`；否则 `ins x (y :: ys) = y :: ins x ys`，
归纳假设给出 `ins x ys ~ x :: ys`，再用 `Perm.cons` 把 `y` 加到两边，并用 `Perm.swap` 交换前两个
元素。`simp only [ins, h, ↓reduceIte]` 里的 `reduceIte` 是内置的 simproc（简化过程）：条件被化简成
`True` 或 `False` 时，把 `if` 直接换成对应的分支；前缀 `↓` 表示在进入子项**之前**就尝试它。
-/

theorem perm_ins (x : ℕ) (l : List ℕ) : List.Perm (ins x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    by_cases h : x ≤ y
    · simp only [ins, h, ↓reduceIte]
      exact List.Perm.refl _
    · simp only [ins, h, ↓reduceIte]
      -- ⊢ (y :: ins x ys).Perm (x :: y :: ys)
      exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem perm_isort (l : List ℕ) : List.Perm (isort l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (perm_ins x (isort xs)).trans (ih.cons x)

/-!
### 9.2 有序与完整的规格说明

归纳的关键引理：对有序的 `l`，`ins x l` 仍有序。`List.pairwise_cons` 把 `Pairwise R (a :: l)` 拆成
「`a` 与 `l` 中每个元素有关系」和「`l` 内部 `Pairwise`」。`trace_state` 打印 `x ≤ y` 不成立的分支
`simp only` 之后的目标，第一个合取项要用上 `perm_ins`：
-/

/--
trace: case neg
x y : ℕ
ys : List ℕ
ih : List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ys → List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) (ins x ys)
hl : (∀ (a' : ℕ), a' ∈ ys → y ≤ a') ∧ List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) ys
h : ¬x ≤ y
⊢ (∀ (a' : ℕ), a' ∈ ins x ys → y ≤ a') ∧
    List.Pairwise (fun x1 x2 ↦ x1 ≤ x2) (ins x ys)
-/
#guard_msgs (whitespace := lax) in
theorem sorted_ins (x : ℕ) (l : List ℕ) (hl : l.Pairwise (· ≤ ·)) :
    (ins x l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [ins]
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    by_cases h : x ≤ y
    · simp only [ins, h, ↓reduceIte, List.pairwise_cons, List.mem_cons]
      refine ⟨?_, hl⟩
      rintro a (rfl | ha)
      · exact h
      · exact Nat.le_trans h (hl.1 a ha)
    · simp only [ins, h, ↓reduceIte, List.pairwise_cons]
      trace_state
      refine ⟨fun a ha ↦ ?_, ih hl.2⟩
      -- `ha : a ∈ ins x ys`；`perm_ins` 与 `Perm.mem_iff` 把它变成 `a ∈ x :: ys`
      rcases List.mem_cons.mp ((perm_ins x ys).mem_iff.mp ha) with rfl | hmem
      · omega -- 此时 `a = x`，由 `¬x ≤ y` 得 `y ≤ x`
      · exact hl.1 a hmem

theorem sorted_isort (l : List ℕ) : (isort l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [isort]
  | cons x xs ih => exact sorted_ins x _ ih

/-!
两半合起来就是完整的规格说明。立刻得到推论：排序结果唯一。核心库的 `List.Perm.eq_of_pairwise` 说：
若关系 `r` 在两个列表的元素之间反对称，则两个互为重排、且都满足 `Pairwise r` 的列表相等。所以任意
一个有序的重排都等于 `isort l`（`fun _ _ _ _ h₁ h₂ ↦ …` 的四个下划线依次是 `a`、`b` 与它们属于两个
列表的两条证明）：
-/

theorem eq_isort_of_sorted_perm (l m : List ℕ) (hm : m.Pairwise (· ≤ ·))
    (hp : List.Perm m l) : m = isort l :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ ↦ Nat.le_antisymm h₁ h₂) hm (sorted_isort l)
    (hp.trans (perm_isort l).symm)

/-!
Mathlib 的 `List.insertionSort r` 有同样两条定理 `perm_insertionSort` 与 `pairwise_insertionSort`，
由唯一性，`isort` 与它处处相等，库里关于 `insertionSort` 的结论都可以搬过来：
-/

theorem isort_eq_insertionSort (l : List ℕ) : isort l = l.insertionSort (· ≤ ·) :=
  (eq_isort_of_sorted_perm l _ (List.pairwise_insertionSort _ l)
    (List.perm_insertionSort _ l)).symm

/-!
## 10. `vcgen`：命令式程序的验证条件（实验性）

`do` 记号可以写 `let mut`、`for`、`return` 这样的命令式程序。验证循环的关键是
loop invariant（循环不变量）：一条在每次迭代前后都成立的断言，它扮演对迭代次数归纳时的归纳假设。
`vcgen` 把这场归纳拆成若干验证条件，你只需给出不变量。4.35 里有两个名字：`mvcgen`（`Std.Do`）已弃用；
替代品 `vcgen`（`Std.WP`）是**实验性**的。文件头已有 `public import Std.WP` 与
`public import Std.Tactic.Do`；定理 `Id.of_run_eq_wp` 在命名空间 `Std.WP` 里，所以要 `open Std.WP`
（`open Lean.Order` 照参考手册同写）；还要 `set_option experimental.vcgen true` 承认它是实验性的，
否则会收到警告（第二个例子）。
-/

/-- 数组求和，命令式写法。 -/
def sumArr (a : Array ℕ) : ℕ := Id.run do
  let mut s := 0
  for x in a do
    s := s + x
  return s

#guard sumArr #[1, 2, 3] = 6

/-!
流程：`generalize` 把 `sumArr a` 记为 `r`，`Id.of_run_eq_wp` 把「`Id.run` 的结果满足性质」变成关于
weakest precondition（最弱前置条件）的目标；`vcgen` 为 `for` 循环生成验证条件。不变量的类型
（`Std/WP/Triple/SpecLemmas.lean` 的 `Invariant`）依次接收已遍历的前缀、尚未遍历的后缀和当前累加值：
这里说「前缀之和等于 `s`」，后缀用不到所以写 `_`。`with finish` 用 `grind` 模式的 `finish` 收尾：
-/

set_option experimental.vcgen true in
open Std.WP Lean.Order in
example (a : Array ℕ) : sumArr a = a.sum := by
  generalize h : sumArr a = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ s ↦ pref.sum = s
  with finish

/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will
eventually replace it; `set_option experimental.vcgen true` acknowledges its experimental
status and silences this warning.
-/
#guard_msgs in
open Std.WP Lean.Order in
example (a : Array ℕ) : sumArr a = a.sum := by
  generalize h : sumArr a = r
  apply Id.of_run_eq_wp h
  vcgen invariants
  · fun pref _ s ↦ pref.sum = s
  with finish

/-!
旧名字 `mvcgen` 自 2026-08-21 起弃用（`Std/Tactic/Do/Syntax.lean` 里的 `deprecated_syntax`），不变量
写成 `⇓⟨xs, s⟩ => ⌜…⌝`。本书建议：先试着把循环改写成递归（§1–§9 的办法），`vcgen` 只适合尝鲜。
-/

/-!
## 11. 常见错误

前文已有：`decide` 被良基递归挡住（§5）；把通过的 `plausible` 当作证明（§8）。这里补三条。

**1. `fun_induction` 分支的变量个数写错。** `fun_induction f a b` 里，递归调用中保持不变的参数
（`logSteps` 的 `b`）不再作为分支变量绑定；绑定的只有会变的参数、路径上的条件和归纳假设。
`sgcd` 的两个参数都会变，所以 §3 里是 `case3 a b h₁ h₂ h ih`；`logSteps` 的 `case1` 只有
`n h ih` 三个：
-/

/-- error: Too many variable names provided at alternative `case1`: 4 provided, but 3 expected -/
#guard_msgs in
example (n b : ℕ) : logSteps n b ≤ n := by
  fun_induction logSteps n b with
  | case1 n b h ih => sorry
  | case2 n h => omega

/-!
**2. `if` 没有写 `h :`，`decreasing_by` 里却用了 `h`。** 条件不带名字时，它仍然作为假设进入
终止性证明，但名字是自动生成的、不可访问的（第 6 章 §9 的 trace 里显示为 `h✝`），写 `h` 就找不到。
报了两次，因为 `h.2` 与 `h.1` 各引用了一次：
-/

/--
error: Unknown identifier `h`
---
error: Unknown identifier `h`
-/
#guard_msgs in
example (n b : ℕ) : ℕ :=
  let rec go (m : ℕ) : ℕ := if 1 < b ∧ 0 < m then go (m / b) + 1 else 0
  termination_by m
  decreasing_by exact Nat.div_lt_self h.2 h.1
  go n

/-!
**3. 对追加的第二个参数用 `rfl`。** `app` 对第一个参数递归，`app xs []` 在 `xs` 是变量时
不会规约，`rfl` 失败；需要归纳，或者借 §1 的 `app_eq_append` 用 simp 一次解决：
-/

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  app xs [] = xs
-/
#guard_msgs in
set_option pp.mvars false in
example (xs : List ℕ) : app xs [] = xs := rfl

example (xs : List ℕ) : app xs [] = xs := by simp [app_eq_append]

/-!
## 练习

`sumList`、`lastOpt` 与第 24 章 §1 的定义相同（重写一遍以自成一体），`mapL`、`sumAcc` 是新的。
复习前面章节：ex_25_4（第 3、4 章）、ex_25_5 与 ex_25_6（第 24 章）、ex_25_7（第 2 章）、
ex_25_10（第 6 章）、ex_25_13（第 4 章）、ex_25_14（第 7 章）。★ 直接应用，★★ 综合两个想法，
★★★ 需要新想法。
-/

/-- 列表求和（第 24 章 §1）。 -/
def sumList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sumList xs

/-- 最后一个元素，空列表给 `none`（第 24 章 §1）。 -/
def lastOpt {α : Type*} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => lastOpt xs

/-- 逐元素映射。 -/
def mapL {α β : Type*} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: mapL f xs

/-- 带累加器的求和（尾递归写法）。 -/
def sumAcc : ℕ → List ℕ → ℕ
  | acc, [] => acc
  | acc, x :: xs => sumAcc (acc + x) xs

/-- 练习 25.1（★）：`mapL` 保持长度。 -/
theorem ex_25_1 {α β : Type*} (f : α → β) (xs : List α) :
    (mapL f xs).length = xs.length := sorry

/-- 练习 25.2（★）：`mapL` 与 `++` 交换。 -/
theorem ex_25_2 {α β : Type*} (f : α → β) (xs ys : List α) :
    mapL f (xs ++ ys) = mapL f xs ++ mapL f ys := sorry

/-- 练习 25.3（★★）：`mapL` 与 `reverse` 交换。提示：用上一题和归纳假设。 -/
theorem ex_25_3 {α β : Type*} (f : α → β) (xs : List α) :
    mapL f xs.reverse = (mapL f xs).reverse := sorry

/-- 练习 25.4（★★）：`mapL` 的成员刻画。提示：`simp [mapL, ih]` 之后只剩逻辑；
两侧的等式可能方向相反，需要 `eq_comm`（第 3、4 章）。 -/
theorem ex_25_4 {α β : Type*} (f : α → β) (b : β) (xs : List α) :
    b ∈ mapL f xs ↔ ∃ a ∈ xs, f a = b := sorry

/-- 练习 25.5（★★）：尾递归求和与第 24 章的 `sumList` 一致。提示：`induction xs generalizing acc`。 -/
theorem ex_25_5 (acc : ℕ) (xs : List ℕ) : sumAcc acc xs = acc + sumList xs := sorry

/-- 练习 25.6（★★）：验证第 24 章的 `lastOpt`：它就是库函数 `List.getLast?`。
提示：`fun_induction lastOpt xs`。 -/
theorem ex_25_6 {α : Type*} (xs : List α) : lastOpt xs = xs.getLast? := sorry

/-- 练习 25.7（★）：`sgcd` 不超过两数之和。提示：`fun_induction sgcd a b`，四个分支都可以用
`omega`（第 2 章；注意每个分支的变量个数，§3）。 -/
theorem ex_25_7 (a b : ℕ) : sgcd a b ≤ a + b := sorry

/-- 练习 25.8（★★）：`logSteps` 不超过 `n`。提示：`fun_induction logSteps n b`（§11 第 1 条说明
分支的变量个数），递归分支里先 `have := Nat.div_lt_self h.2 h.1`，再 `omega`。 -/
theorem ex_25_8 (n b : ℕ) : logSteps n b ≤ n := sorry

/-- 练习 25.9（★★）：燃料不会让步数变少。提示：`induction fuel generalizing n steps`，
然后对 `n ≤ 1` 与 `n % 2 = 0` 用 `by_cases`，`simp [collatzFuel, h]` 之后 `omega`。 -/
theorem ex_25_9 (fuel n steps : ℕ) : steps ≤ collatzFuel fuel n steps := sorry

/-- 练习 25.10（★）：用 `decide +kernel`（§5）证明一个具体的 `sgcd` 值，并用 `#print axioms`
确认它没有引入专属公理。 -/
theorem ex_25_10 : sgcd 100 75 = 25 := sorry

/-- 练习 25.11（★）：`isort` 保持长度与成员关系。提示：`perm_isort`、`List.Perm.length_eq`、
`List.Perm.mem_iff`。 -/
theorem ex_25_11 (l : List ℕ) :
    (isort l).length = l.length ∧ ∀ x : ℕ, x ∈ isort l ↔ x ∈ l := sorry

/-- 练习 25.12（★）：`ins` 恰好多一个元素，即 `insBad` 违反的那条性质。
提示：`perm_ins` 与 `List.Perm.length_eq`，或者归纳。 -/
theorem ex_25_12 (x : ℕ) (l : List ℕ) : (ins x l).length = l.length + 1 := sorry

/-- 练习 25.13（★★）：`isort` 与 `++` 不交换（排序不是追加的同态）。提示：先把去掉 `¬` 的命题
写成一个 `example`，用 `plausible` 找反例（找到后删掉这个 `example`），再回到本题；
证明里 `intro h`，把反例代入。 -/
theorem ex_25_13 : ¬ ∀ xs ys : List ℕ, isort (xs ++ ys) = isort xs ++ isort ys := sorry

/-- 练习 25.14（★★）：`headS` 的结果属于原列表。提示：`unfold headS`，`List.head_mem`。 -/
theorem ex_25_14 {α : Type*} (l : {l : List α // l ≠ []}) : headS l ∈ l.val := sorry

/-- 练习 25.15（★★★）：`findIdx` 的另一半规格说明（§6 的（b））：返回 `none` 时数组里没有 `x`。
提示：先对内部循环 `findIdx.go` 证明一个对起点 `j` 一般化的引理。 -/
theorem ex_25_15 (a : Array ℕ) (x : ℕ) (h : findIdx a x = none) :
    ∀ (i : ℕ) (hi : i < a.size), a[i] ≠ x := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 规格说明即定理 | `theorem f_spec … : P (f x)` | 先写陈述，再证明；优先证「等于库函数」 |
| 结构归纳 | `induction xs with \| nil => … \| cons x xs ih => …` | 结构递归函数 |
| 一般化归纳假设 | `induction xs generalizing acc` | 带累加器的函数 |
| 函数归纳 | `fun_induction f a b with \| case1 … => …` | 非结构递归；分支变量是会变的参数、条件、`ih` |
| 终止性 | `termination_by`，`decreasing_by exact …` | 默认策略（含 `omega`）不够时；`if h :` 才能引用 `h` |
| 燃料 | `def f : ℕ → … \| 0, … \| fuel + 1, …` | 不能证明终止的函数，换来可证明性 |
| 封闭检查 | `decide`，`decide +kernel`，`native_decide` | 由弱到强；最后一个每次加一条公理 |
| 公理清单 | `#print axioms thm` | 验证依赖的公理 |
| 下标证明 | `a[i]`，`a[i]'h`，`a[i]?`，`Fin a.size` | 避免越界 |
| 子类型 | `{n : ℕ // 0 < n}`，`.val`，`.property` | 性质写进类型或参数 |
| 找反例 | `plausible (config := { randomSeed := some 7 })` | 证明前检查陈述；通过时目标被当作 `sorry` |
| 可执行检查 | `#guard e` | 回归测试，不是证明 |
| 排序规格 | `l.Pairwise (· ≤ ·)` 与 `List.Perm` | 有序且是重排 |
| 命令式验证 | `vcgen`，`Id.of_run_eq_wp`，`set_option experimental.vcgen true` | 实验性；`mvcgen` 已弃用 |

怎样选择：先 `plausible` 与 `#guard` 检查陈述，再证明；封闭的具体例子用 `decide`，被不可约挡住用
`decide +kernel` 或 `simp [f]`；带循环的程序，本书建议先试着改写成递归。

## 延伸阅读

- *Lean Language Reference* 4.35.0（`https://lean-lang.org/doc/reference/4.35.0/`）：7.6「Recursive
  Definitions」（良基递归、`termination_by`、`decreasing_by`、可约性）；第 17 章「The `vcgen` tactic」。
- *Functional Programming in Lean* 第 8 章：8.1–8.2（尾递归与等价证明，对应 §2）、8.6 Insertion Sort
  （对应 §9）（`https://lean-lang.org/functional_programming_in_lean/`）。
- Lean 源码：`Init/Tactics.lean`（`fun_induction`、`decide` 的文档字符串）；`Init/Data/List/Perm.lean`
  （含 `Perm.eq_of_pairwise`）；`Std/WP/Triple/SpecLemmas.lean`（`Invariant`）与
  `Std/Tactic/Do/Syntax.lean`（`vcgen`、`mvcgen` 的语法与弃用）。
- Mathlib：`Mathlib/Data/List/Sort.lean`（`insertionSort`）；
  `Mathlib/Tactic/Linter/DeprecatedSyntaxLinter.lean`（`linter.style.native`）。
- Plausible：`Plausible/Testable.lean`（`structure Configuration`）。第 28 章讲内核、可约性与公理。
-/

end Lean4Learn.Ch25

end
