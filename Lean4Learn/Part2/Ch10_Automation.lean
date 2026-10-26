module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Order
public import Mathlib.Tactic.Peel
public import Mathlib.Tactic.Polyrith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar

/-!
# 第 10 章　自动化策略全景与选择

前面的章节陆续用过十几个会「自动」证明的 tactic（策略）：`simp`、`ring`、`omega`、`linarith`、
`positivity`……本章把它们放进同一张地图：每个策略判定什么（适用范围）、要导入哪个模块、在哪条边界上失败、
失败之后换什么。读完后，面对一个目标，你能按决策表排出该试的策略顺序，并看懂它们失败时的 error message
（错误信息）。

## 学习目标
- 区分三类自动化：decision procedure（判定过程）、重写、搜索，并说出每一类失败时意味着什么；
- 设计 simp set（simp 集）：`@[simp]` 引理的方向与 side condition（副条件），用 discharger
  （副条件处理器）`(disch := …)` 处理条件引理，读懂循环与「无进展」，分清 `simp at *`、`simp_all` 与
  `failIfUnchanged`；
- 为恒等式选 `ring`、`ring_nf`、`ring1`、`field_simp`、`field`、`abel` 或 `linear_combination`，知道
  `polyrith` 已死；为 `ℕ`、`ℤ` 与数值选 `omega`、`lia`、`decide`、`norm_num`；
- 为不等式选 `linarith`、`nlinarith`、`positivity`、`gcongr`、`bound`、`order`，并会给提示；
- 认识 `tauto`、`aesop`、`grind` 的能力与边界，会用 `grind?` 取出可复现的脚本；
- 用本章末尾的决策表把「目标形状」映射到「策略与导入」。

## 前置知识
第 2 章（`ring`、`omega`、`linarith`、`nlinarith`、`positivity`、`norm_num` 的基本用法与边界），第 4 章
（`tauto`），第 5 章（`simp` 的机制：§6、§7、§11），第 6 章（`induction … with`），第 7 章（集合的 `∩`、`∪`），
第 8 章（`[LinearOrder α]`、`Type*`），第 9 章（`exact?` 与弃用警告的读法）。本章不重复那些章节里的失败例子，
只补各策略的新边界。出现的 `Finset`、`Nat.Prime` 等对象各在用到处给一句说明。
-/

@[expose] public section

namespace Lean4Learn.Ch10

/-!
## 1. 三类自动化

自动化策略按它们**承诺**的东西分三类。**判定过程**对一个固定的逻辑片段保证给出答案（`omega`、`decide`、
`ring1`，以及 `norm_num` 的数值扩展）。这个保证属于抽象的算法：片段外的目标不归它管，片段内的假命题被判为假
（§5 的 `Nat.Prime 91`）。真正运行的策略还受递归深度等资源上限与求值方式的限制：§4 里真命题
`Nat.Prime 1009` 用 `decide` 撞上递归深度上限而失败，换成 `decide +kernel` 就成功。所以失败本身不是反例：
先读错误信息，分清是越界、为假还是资源不够，再决定换工具、把目标改写进片段，还是换一种求值方式。
**重写**把目标换成另一个目标，不保证关掉它（`simp`、`field_simp`、`ring_nf`）；`ring` 与 `norm_num` 是
外层重写、内层判定的组合。**搜索**在规则库里搜索
（`aesop`、`grind`、`tauto`），失败只说明在它的搜索范围内没找到。同一个目标常有几个策略都能证，重写则不一定
关得掉目标，下面的 `simp` 把 `a + 0 = b` 变成 `a = b` 就停了，因为 `simp` 不读假设 `h`：
-/

example (x y : ℕ) (h : x < y) : x + 1 ≤ y := by omega
example (x y : ℕ) (h : x < y) : x + 1 ≤ y := by grind

example (a b : ℕ) (h : a = b) : a + 0 = b := by
  simp
  guard_target = (a = b)
  exact h

/-!
选策略的第一原则：**先看目标属于哪个片段，再看谁的错误信息最好读**。下面每个策略按「范围、导入、成功、边界、
补救」讲，最后给决策表。

## 2. `simp` 深入：设计 simp 集

第 5 章讲了 simplifier（简化器）怎样工作，这里换成**设计者**的视角：往 simp set 里加一条 simp lemma
（simp 引理）时，方向与副条件怎么选（`simp only`、`simp?`、`+arith` 见第 5 章 §6、§7）。先造一个小对象，把
自然数截到不超过 10 的函数 `clamp`，和几条关于它的引理：
-/

def clamp (n : ℕ) : ℕ := min n 10

theorem clamp_le (n : ℕ) (h : n ≤ 10) : clamp n = n := by
  unfold clamp
  omega

@[simp] theorem clamp_clamp (n : ℕ) : clamp (clamp n) = clamp n := by
  unfold clamp
  omega

theorem clamp_eq_min (n : ℕ) : clamp n = min n 10 := rfl
theorem min_eq_clamp (n : ℕ) : min n 10 = clamp n := rfl
theorem var_head (n : ℕ) (h : 0 < n) : n = n - 1 + 1 := by omega

/-!
一条好的 `@[simp]` 引理满足四条经验规则：**(a)** 左端的头符号是常量，不是变量；**(b)** 右端比左端简单，且不会
被同一批引理再次匹配；**(c)** 副条件要么 simp 自己能证，要么你准备好处理它；**(d)** 左端的子项已经是
simp normal form（simp 正规形）。只有 (a) 由 Lean 自己警告，其余靠判断，或靠 Batteries/Mathlib 的 `simpNF`
检查。`clamp_clamp` 满足全部四条，套多少层都被压平；用 `simp [-clamp_clamp]`（或
`attribute [-simp] clamp_clamp`）把它从 simp 集里去掉，`simp` 就没有可用的引理：
-/

example (n : ℕ) : clamp (clamp (clamp n)) = clamp n := by simp

/-- error: `simp` made no progress -/
#guard_msgs in
example (n : ℕ) : clamp (clamp n) = clamp n := by simp [-clamp_clamp]

/-!
**(a) 头符号是变量。** 这样的引理要在每个子项上试一次。加进 simp 集时 Lean 就警告
（`warning.simp.varHead`）；对 `local` 引理也一样，这里用 `section` 限定范围：
-/

section
/-- warning: Left-hand side of simp theorem has a variable as head symbol. -/
#guard_msgs (substring := true) in
attribute [local simp] var_head
end

/-!
**(b) 方向。** 两条方向相反的引理互相改写，单看都「没错」，合在一起 `simp` 就绕圈。第 5 章 §11 演示了一条引理
的自我循环，这里是 2-环：`simp` 撞上递归深度上限，并指出哪条引理在循环（`Possibly looping simp theorem`）：
-/

/-- error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached -/
#guard_msgs (error, substring := true) in
/-- warning: Possibly looping simp theorem: `clamp_eq_min`

Note: Possibly caused by: `min_eq_clamp` -/
#guard_msgs (warning, substring := true) in
example (n : ℕ) : clamp n = min n 10 := by simp [clamp_eq_min, min_eq_clamp]

/-!
**(c) 副条件与 discharger。** `clamp_le` 是条件引理：先证 `n ≤ 10`，才能把 `clamp n` 换成 `n`。simp 重写时遇到
副条件，调用 discharger 去证；默认的处理器就是 `simp` 自己，上下文里的 `h` 对它不可见，所以下面没有进展。
三种补救：把 `h` 交给 simp（副条件被简化成 `True`）；或者换处理器 `simp (disch := tac) [...]`，`tac` 是任意
策略，用来证每个副条件。`assumption` 在上下文里找，`omega` 连上下文里没有的 `n % 4 ≤ 10` 都能证：
-/

/-- error: `simp` made no progress -/
#guard_msgs in
example (n : ℕ) (h : n ≤ 10) : clamp n = n := by simp [clamp_le]

example (n : ℕ) (h : n ≤ 10) : clamp n = n := by simp [clamp_le, h]
example (n : ℕ) (h : n ≤ 10) : clamp n = n := by simp (disch := assumption) [clamp_le]
example (n : ℕ) : clamp (n % 4) = n % 4 := by simp (disch := omega) [clamp_le]

/-!
**(d) 左端不是正规形。** `simp` 从内层开始，先把 `m * 1` 简化成 `m`，走到外层 `clamp` 时，左端是
`clamp (n * 1)` 的假设 `h` 已经对不上，目标留成 `clamp m = 7`。被传进去的参数没用上，
`linter.unusedSimpArgs`（代码检查器，第 5 章 §6）会指出来；`simp only` 同样：
-/

/-- error: unsolved goals
h : ∀ (n : ℕ), clamp (n * 1) = 7
m : ℕ
⊢ clamp m = 7 -/
#guard_msgs (substring := true) in
example (h : ∀ n, clamp (n * 1) = 7) (m : ℕ) : clamp (m * 1) = 7 := by simp [h]

/-- warning: This simp argument is unused: -/
#guard_msgs (substring := true) in
example (a : ℕ) : a + 0 = a := by simp only [mul_one, add_zero]

/-!
**作用位置。** `simp at *` 对每个假设和目标**各自**简化，不互相代入；`simp_all` 才让它们互相简化直到稳定
（第 5 章 §7）。下面 `simp at *` 简化了 `h₁`，目标 `a = 3` 原样不动（`guard_target` 断言这一点），得靠 `omega`；
`simp_all` 一步到位：
-/

example (a b : ℕ) (h₁ : a + 0 = b) (h₂ : b = 3) : a = 3 := by
  simp at *
  guard_target = (a = 3)
  omega

example (a b : ℕ) (h₁ : a + 0 = b) (h₂ : b = 3) : a = 3 := by simp_all

/-!
**`failIfUnchanged`** 默认开：什么都没改就是错误；用 `-failIfUnchanged` 关掉它，不再报错，但 unused tactic
linter（未用策略的代码检查器）会指出这一步什么都没做：
-/

/-- error: `simp` made no progress -/
#guard_msgs in
example (x y : ℕ) (h : x ≤ y) : x ≤ y := by simp at h

/-- warning: Unused tactic linter: `simp -failIfUnchanged at h` does nothing. -/
#guard_msgs (substring := true) in
example (x y : ℕ) (h : x ≤ y) : x ≤ y := by
  simp -failIfUnchanged at h
  exact h

/-!
**`simp_rw` 与 `simp only`。** `simp_rw [r₁, r₂]` 依次对每条规则执行一次 `simp only [rᵢ]`，所以**每条规则都必须
改动目标**，否则报错；`simp only [r₁, r₂]` 一次用全部规则，没用上的只触发上面那条警告。`simp_rw` 能进入
binder（引入绑定变量的构造，第 5 章 §5），顺序严格，这是它相对 `rw` 的用处：
-/

/-- error: `simp` made no progress -/
#guard_msgs in
example (a b : ℕ) : a + 0 + b = a + b := by simp_rw [mul_one, add_zero]

example (f : ℕ → ℕ) (h : ∀ n, f (n + 0) * 1 = 5) : ∀ n, f n = 5 := by
  simp_rw [mul_one, add_zero] at h
  exact h

/-!
## 3. 恒等式：`ring` 一族、`field_simp`、`field`、`linear_combination`、`abel`

目标是「等式两边都是同一个环里的表达式」时先想这一族。**`ring`**（导入 `Mathlib.Tactic.Ring`）有三个形态：
`ring1` 把目标证完，证不完就失败；`ring_nf` 把表达式化成 normal form（正规形），不要求关掉目标；`ring` 先试
`ring1`，失败后退回 `ring_nf` 并建议改用它（第 2 章 §5 的例子给出了完整的两条消息）。指数里带变量也在范围内。
**边界：不读假设。** 补救是 `rw [h]` 或 `linear_combination h`（见下）：
-/

example (n : ℕ) (x : ℝ) : x ^ (n + 1) = x * x ^ n := by ring

/-- error: ring failed, ring expressions not equal -/
#guard_msgs (substring := true) in
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by ring1

example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by rw [h]
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by linear_combination h

/-!
目标里有除法时用 **`field_simp`**（导入 `Mathlib.Tactic.FieldSimp`）：它在域里把含除法的表达式改写成
`n / d`（`n`、`d` 都不含除法），对等式与不等式则交叉相乘，清掉分母。约去一个因子要先证明它的符号条件：
等式只要因子 `≠ 0`，不等式要因子 `> 0`（否则乘过去会反号；见 `FieldSimp.lean` 里 `reduceProp` 的文档注释），
证不出的步骤就跳过。它已被重写过：新版 `field_simp [t]` 里的 `t` 只是交给 discharger 的项，不再是 simp 引理（见
`FieldSimp.lean` 的文档注释），旧教程里的配方要小心。常见搭配是 `field_simp` 然后 `ring`；**`field`**（导入
`Mathlib.Tactic.Field`）是这个搭配的缩写。`trace_state` 看 `field_simp` 留下的目标：
-/

/--
trace: x : ℝ
hx : x ≠ 0
⊢ (x ^ 2 + 1) ^ 2 = x ^ 2 * (x ^ 2 + 2) + 1
-/
#guard_msgs in
example (x : ℝ) (hx : x ≠ 0) : (x + 1 / x) ^ 2 = x ^ 2 + 2 + 1 / x ^ 2 := by
  field_simp
  trace_state
  ring

example (x : ℝ) (hx : x ≠ 0) : (x + 1 / x) ^ 2 = x ^ 2 + 2 + 1 / x ^ 2 := by field

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  field_simp
  guard_target = (a ≤ b)
  exact h

/-!
同一个不等式只给 `≠ 0`，分母的正负不知道，`field_simp` 不能交叉相乘：目标原样留下，它自己也不报错，下面的
错误只是 `by` 块结束时目标还没证完：
-/

/--
error: unsolved goals
a b : ℝ
ha : a ≠ 0
hb : b ≠ 0
h : a ≤ b
⊢ 1 / b ≤ 1 / a
-/
#guard_msgs in
example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  field_simp

/-!
**边界与 discharger。** 没有 `x ≠ 0` 两个策略都不会替你猜（`x / x = 1` 在 `x = 0` 时是假的，第 2 章 §4）。
默认的 discharger 会用上下文里的 `≠ 0` 假设与序性质；不认识的分母事实用 `(disch := tac)` 交给你的策略，或
`field [hf]` 把项提供给它：
-/

/--
info: Try this:
  [apply] field_simp
---
error: unsolved goals
x : ℝ
⊢ x / x = 1
-/
#guard_msgs in
example (x : ℝ) : x / x = 1 := by field

/--
error: unsolved goals
x : ℝ
⊢ x / x = 1
-/
#guard_msgs in
example (x : ℝ) : x / x = 1 := by field_simp

example (f : ℝ → ℝ) (hf : ∀ t, f t ≠ 0) (x : ℝ) : x / f x * f x = x := by
  field_simp (disch := exact hf x)

example (f : ℝ → ℝ) (hf : ∀ t, f t ≠ 0) (x : ℝ) : x / f x * f x = x := by field [hf]

/-!
**`linear_combination`**（导入 `Mathlib.Tactic.LinearCombination`）：你写出假设的线性组合，它检查「目标减去组合」
能被 `ring1` 证成恒等式。系数可以是任意表达式；目标是不等式时，`≤` 假设前的系数须非负；`(exp := n)` 先把目标
取 `n` 次方。`polyrith` 曾经替你找系数，但它依赖的服务已经关闭（§9）；现在只能自己找，或交给 `grobner`
（核心）：它证得出，但不输出 `linear_combination` 的系数，下面的 `#guard_msgs` 不带任何消息，正说明没有建议：
-/

example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  linear_combination (h₁ + h₂) / 2

example {x y z w : ℤ} (h₁ : x * z = y ^ 2) (h₂ : y * w = z ^ 2) :
    z * (x * w - y * z) = 0 := by
  linear_combination w * h₁ + y * h₂

example (a b : ℝ) (h₁ : a ≤ 1) (h₂ : b ≤ 3) : (a + b) / 2 ≤ 2 := by
  linear_combination (h₁ + h₂) / 2

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by linear_combination sq_nonneg (a - b)

example (x : ℝ) (h : x ^ 2 = 0) : x = 0 := by linear_combination (exp := 2) h

#guard_msgs in
example (x y : ℝ) (h₁ : x * y = 1) (h₂ : x + y = 3) : x ^ 2 + y ^ 2 = 7 := by grobner

/-- error: could not establish the nonnegativity of -1 -/
#guard_msgs in
example (a b : ℝ) (h : a ≤ b) : -b ≤ -a := by linear_combination (-1) * h

/-!
**边界：系数不对。** 下面少了 `h₂`。排错用 `(norm := ring_nf)`：不要求校验成功，把残差留成新目标。残差
`1 - y` 正好是 `(h₂ - h₁) / 2`，补上它就得到 `(h₁ + h₂) / 2`：
-/

/-- error: ring failed, ring expressions not equal -/
#guard_msgs (substring := true) in
example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by linear_combination h₁

/-- ⊢ 1 - y = 0 -/
#guard_msgs (substring := true) in
example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by
  linear_combination (norm := ring_nf) h₁

/-!
**`abel`**（导入 `Mathlib.Tactic.Abel`）：交换加法幺半群与加群里的恒等式，只用加、减、整数倍；它不读假设，
补救同样是先 `rw`：
-/

example {G : Type*} [AddCommGroup G] (a b c : G) : a + b - (c + a) = b - c := by abel

/-- ⊢ 2 • a = 2 • b -/
#guard_msgs (substring := true) in
example {G : Type*} [AddCommGroup G] (a b : G) (h : a = b) : a + a = b + b := by abel

example {G : Type*} [AddCommGroup G] (a b : G) (h : a = b) : a + a = b + b := by rw [h]

/-!
## 4. 整数与可判定命题：`omega`、`lia`、`decide`

目标是 `ℕ`、`ℤ` 上的线性算术时用 **`omega`**（核心，无需导入，第 2 章 §6）。它也处理 `Fin n` 上的比较：
`i.val` 被当作带界 `i.val < n` 的变量，`i ≠ 0` 这样的假设也被用上：
-/

example (i j : Fin 5) (h : i < j) : i.val + 1 ≤ j.val := by omega
example (i : Fin 5) (h : i ≠ 0) : 0 < i.val := by omega

/-!
**边界：全称量词。** `omega` 不实例化 `∀`，`h : ∀ n, f n = 2 * n` 它直接忽略。补救一：自己
`specialize`。补救二：**`lia`**（核心）。它是 `grind` 里整数线性算术引擎的单独入口（`cutsat` 的新名字，§9），
同样只做线性整数算术，也不会自己用 `∀` 假设（下面失败），但接受一串额外事实 `lia [h 3]`。所以选择规则很
简单：不需要额外事实时用 `omega`，需要把 `∀` 假设的实例喂进去时用 `lia [...]`：
-/

/-- a possible counterexample may satisfy the constraints -/
#guard_msgs (substring := true) in
example (f : ℕ → ℤ) (h : ∀ n, f n = 2 * n) : f 3 = 6 := by omega

example (f : ℕ → ℤ) (h : ∀ n, f n = 2 * n) : f 3 = 6 := by
  specialize h 3
  omega

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example (f : ℕ → ℤ) (h : ∀ n, f n = 2 * n) : f 3 = 6 := by lia

example (f : ℕ → ℤ) (h : ∀ n, f n = 2 * n) : f 3 = 6 := by lia [h 3]

/-!
不实例化 `∀` 假设是 `omega`、`lia` 的边界，不是所有自动化的边界：`grind`（§7）会自己找实例，同一个目标
它直接证完：
-/

example (f : ℕ → ℤ) (h : ∀ n, f n = 2 * n) : f 3 = 6 := by grind

/-!
**`decide`**（核心）对可判定命题求值。第 5 章 §3 讲过它不能含自由变量、对 `ℝ` 无效；这里补一条规模的边界：
`Nat.Prime n`（「`n` 是素数」）的判定实例对每个小于 `n` 的数逐个检查，`n` 稍大时求值就失败。补救是
`decide +kernel`（交给内核，第 5 章），或者更好的 `norm_num`（§5）：
-/

example : ∀ i : Fin 8, i.val ^ 2 % 4 ≠ 2 := by decide
example : Nat.Prime 97 := by decide

/-- error: maximum recursion depth has been reached -/
#guard_msgs (substring := true) in
example : Nat.Prime 1009 := by decide

example : Nat.Prime 1009 := by decide +kernel
example : Nat.Prime 1009 := by norm_num

/-!
## 5. `norm_num` 与它的扩展

目标里有具体的数字运算、素数、最大公约数时用 `norm_num`（导入 `Mathlib.Tactic.NormNum.Basic`，`linarith` 会带上
它）。它在 simp 集之外带一组可扩展的数值程序，每个扩展负责一类函数：`Nat.Prime` 在
`Mathlib.Tactic.NormNum.Prime`，`Nat.gcd` 在 `Mathlib.Tactic.NormNum.GCD`，其余见
`Mathlib/Tactic/NormNum/`。
`norm_num [h]` 把 `h` 加进 simp 集，`norm_num at h` 简化假设。**边界：假命题。** 数值扩展是判定过程，算出来是
假就简化成 `False`；注意错误信息报的是简化之后的目标，不是你写的目标：
-/

example : Nat.gcd 84 36 = 12 := by norm_num
example (x : ℝ) (h : x = 2) : x ^ 2 + 1 = 5 := by norm_num [h]

example (x : ℝ) (h : (2 : ℝ) ^ 3 = x) : x = 8 := by
  norm_num at h
  linarith

/-- ⊢ False -/
#guard_msgs (substring := true) in
example : Nat.Prime 91 := by norm_num

example : ¬ Nat.Prime 91 := by norm_num

/-!
## 6. 不等式：`linarith`、`nlinarith`、`positivity`、`gcongr`、`bound`、`order`

**`linarith` 与 `nlinarith`**（导入 `Mathlib.Tactic.Linarith`，第 2 章 §7、§8）。新的边界：`≠` 假设默认不被
使用，因为它要分情况；配置项 `+splitNe` 打开分情况，代价是每个 `≠` 让分支数翻倍，`k` 个 `≠` 最坏要跑 `2 ^ k`
次（`Linarith/Frontend.lean`）。`nlinarith` 把假设两两相乘、加上平方项，两个一次因子的积它自己能造；需要它猜不到
的因式时给**提示**，把关键的积作为额外的项传进方括号（下面要的是 `(x + 1) * (x - 1) ^ 2 ≥ 0`；第 11 章系统讲
提示）：
-/

/-- error: linarith failed to find a contradiction -/
#guard_msgs (substring := true) in
example (x y : ℝ) (h : x ≠ y) (h₁ : x ≤ y) : x < y := by linarith

example (x y : ℝ) (h : x ≠ y) (h₁ : x ≤ y) : x < y := by linarith +splitNe

example (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y := by nlinarith

/-- error: linarith failed to find a contradiction -/
#guard_msgs (substring := true) in
example (x : ℝ) (hx : 0 ≤ x) : x ^ 2 + x ≤ x ^ 3 + 1 := by nlinarith

example (x : ℝ) (hx : 0 ≤ x) : x ^ 2 + x ≤ x ^ 3 + 1 := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x + 1) (sq_nonneg (x - 1))]

/-!
目标是 `0 < e`、`0 ≤ e` 或 `e ≠ 0` 时用 **`positivity`**（导入 `Mathlib.Tactic.Positivity`）。它按语法递归，
扩展负责各个函数：`Real.exp` 恒正（扩展在 `Mathlib/Analysis/Complex/Exponential.lean`），`Finset.sum`（用
`∑ i ∈ s, f i` 记有限集 `s` 上的有限和，第 12 章系统讲）与 `Real.sqrt` 也各有扩展。边界是差：
`a * c - b * c` 的符号靠语法看不出，要先把假设 `b ≤ a` 乘上 `c`，那是 `bound`（下面）或 `nlinarith` 的事：
-/

example (x : ℝ) : 0 < Real.exp x + x ^ 2 := by positivity
example (s : Finset ℕ) (f : ℕ → ℝ) : 0 ≤ ∑ i ∈ s, (f i) ^ 2 := by positivity
example (x : ℝ) : 0 ≤ Real.sqrt x + x ^ 2 := by positivity

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example (a b c : ℝ) (hc : 0 ≤ c) (h : b ≤ a) : 0 ≤ a * c - b * c := by positivity

-- 不需要假设也一样：这个目标恒成立，但中间那项带减号（练习 10.15）
/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by positivity

/-!
**`gcongr`**（导入 `Mathlib.Tactic.GCongr`）：两边形状相同、只在某些位置不同的不等式，它找出对应的单调性引理
（标注 `@[gcongr]` 的），把目标拆成各位置各自的比较。引理的副条件由 `positivity` 一类的 discharger 处理，证不了
的留给你。模板 `gcongr x ^ 2 * ?_ + 5` 限制拆解深度；`gcongr with i hi` 给进入 binder 时引入的变量命名：
-/

example (a b c d : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) (hc : 0 ≤ c) (hb : 0 ≤ b) :
    a * c ≤ b * d := by gcongr

example {a b x c d : ℝ} (h : a + c + 1 ≤ b + d + 1) :
    x ^ 2 * (a + c) + 5 ≤ x ^ 2 * (b + d) + 5 := by
  gcongr x ^ 2 * ?_ + 5
  guard_target = (a + c ≤ b + d)
  linarith

example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  gcongr with i hi
  guard_target = (f i ≤ g i)
  exact h i hi

/-!
**边界：副条件证不了，或两边没有共同结构。** 下面缺 `0 ≤ c`，副条件留作新目标（case 名 `ha` 来自引理的
假设名）；`x ≤ y` 两边没有共同结构，`gcongr` 找不到可拆的位置：
-/

/-- case ha -/
#guard_msgs (substring := true) in
example (a b c : ℝ) (h : a ≤ b) : a * c ≤ b * c := by gcongr

/-- error: `gcongr` did not make progress. -/
#guard_msgs (substring := true) in
example (x y : ℝ) : x ≤ y := by gcongr

/-!
**`bound`**（导入 `Mathlib.Tactic.Bound`）是建立在 `aesop` 上的专用规则集（`@[bound]`），能在 `0 ≤ x` 与 `x ≤ y`
两种形态间来回跳（`0 ≤ a * c - b * c` 先变成 `b * c ≤ a * c`），但只在已有的 `@[bound]` 规则范围内递归，不会
自己构造需要的项，比如 `(a - b) ^ 2`；失败时是 `aesop` 的错误信息（它用 `terminal := true`，必须证完）。补救是
`nlinarith [sq_nonneg (a - b)]`（第 2 章）：
-/

example (a b c : ℝ) (hc : 0 ≤ c) (h : b ≤ a) : 0 ≤ a * c - b * c := by bound

/-- error: Tactic `aesop` failed, failed to prove the goal after exhaustive search. -/
#guard_msgs (substring := true) in
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by bound

/-!
**`order`**（导入 `Mathlib.Tactic.Order`）是 `Preorder`、`PartialOrder`、`LinearOrder` 与格（含 `max`、`min`）上的
判定过程，只用上下文里的序事实，不需要知道元素是什么：
-/

example {α : Type*} [LinearOrder α] (a b c : α) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by order

example {α : Type*} [LinearOrder α] (a b c : α) (h : max a b ≤ c) (h' : c < b) : False := by
  order

/-!
**边界：分配律。** `order` 认识格运算 `⊓`、`⊔`（以及 `min`、`max`），只用格的公理，而分配律不是格的公理。
`a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c)` 在任何格里成立，`order` 能证；反方向要分配律，即使 `α` 是分配格，`order` 也找不到
矛盾。补救是直接用分配律的引理 `inf_sup_left`（找法见第 9 章）：
-/

example {α : Type*} [Lattice α] (a b c : α) : a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c) := by order

/-- error: No contradiction found. -/
#guard_msgs (substring := true) in
example {α : Type*} [DistribLattice α] (a b c : α) : a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c := by order

example {α : Type*} [DistribLattice α] (a b c : α) : a ⊓ (b ⊔ c) ≤ a ⊓ b ⊔ a ⊓ c :=
  (inf_sup_left a b c).le

/-!
## 7. 搜索类：`tauto`、`aesop`、`grind`

**`tauto`**（导入 `Mathlib.Tactic.Tauto`，第 4 章 §7）是命题逻辑的搜索：拆开 `∧`、`∨`、`↔`、`∃`，最后用
`rfl`、`contradiction`、`solve_by_elim` 收尾；它不懂算术，目标一出命题逻辑就失败：
-/

example (p q r : Prop) : (p ∨ q) ∧ (p → r) ∧ (q → r) → r := by tauto

/-- error: Tactic `tauto` failed -/
#guard_msgs (substring := true) in
example (x y : ℕ) (h : x < y) : x ≤ y := by tauto

/-!
**`aesop`**（随 `Mathlib.Tactic.Common` 进来）在规则库里做最佳优先搜索。规则分 `norm`（先应用，含 `simp_all`）、
`safe`（不回溯）、`unsafe`（带成功概率，可回溯）三种（`.lake/packages/aesop/README.md`）。它擅长逻辑与集合
关系的混合目标；新定义它不展开，要用 `(add norm unfold Small)` 告诉它：
-/

example (s t u : Set ℕ) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by aesop

def Small (n : ℕ) : Prop := n < 10

/-- error: Tactic `aesop` failed, made no progress -/
#guard_msgs (substring := true) in
example : Small 3 := by aesop

example : Small 3 := by aesop (add norm unfold Small)

/-!
它也不是对所有集合恒等式都有效。下面这个差集等式（练习 10.12）`aesop` 同样没有进展：
-/

/-- error: Tactic `aesop` failed, made no progress -/
#guard_msgs (substring := true) in
example (s t u : Set ℕ) : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := by aesop

/-!
**`grind`**（核心，无需导入）自 2025 年中（v4.22）起成熟，是兜底的收尾策略：它同时维护等式的 congruence closure
（同余闭包）、线性整数算术（`lia`）、交换环与域的代数引擎，并按需对 `if`、`match` 分情况。三个强项：同余、
`if` 分情况、域里的恒等式。`grind?` 报告一个等价的 `grind only [...]`，只含实际用到的事实，是把一次性的搜索
换成可复现脚本的办法，把它打印的脚本贴回去就是一个确定的证明：
-/

example (f : ℕ → ℕ) (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : f a = f c := by grind

example (x : ℤ) : (if x < 0 then -x else x) ≥ 0 := by grind

example (x y : ℝ) (hxy : x ≠ y) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by grind

/--
info: Try this:
  [apply] grind only
-/
#guard_msgs in
example (f : ℕ → ℕ) (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : f a = f c := by grind?

example (f : ℕ → ℕ) (a b c : ℕ) (h₁ : a = b) (h₂ : b = c) : f a = f c := by grind only

/-!
**边界：归纳。** `grind` 不会自己归纳。错误信息很长（列出它断言的全部事实与等价类），用 `substring := true`
只取第一句。补救是先归纳、再让 `grind` 收尾：
-/

/-- error: `grind` failed -/
#guard_msgs (substring := true) in
example (n : ℕ) : n < 2 ^ n := by grind

example (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => grind
  | succ n ih => grind

/-!
## 8. 一行速览：留给后面的章节

`fun_prop`（导入 `Mathlib.Tactic.FunProp`）沿着 `fun` 的语法递归，证 `Continuous`、`Measurable` 一类性质
（这两个概念在第 14、16 章讲，这里只当作「函数的性质」）；`continuity`（`…Continuity`）与 `measurability`
（`…Measurability`）是更老的、基于 `aesop` 的同类策略，后者的文档说新引理应标 `@[fun_prop]`；`finiteness`
（`…Finiteness`）证 `ℝ≥0∞` 里的 `x ≠ ∞`（第 16 章）。找不到引理时不要「搜索策略」，用 `exact?`（第 9 章）：
-/

example : Continuous fun x : ℝ ↦ Real.exp (x ^ 2) + 3 := by fun_prop
example : Continuous fun x : ℝ ↦ Real.exp (x ^ 2) + 3 := by continuity
example : Measurable fun x : ℝ ↦ Real.exp (x ^ 2) + 3 := by measurability

open scoped ENNReal in
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) : a + 2 * b ≠ ∞ := by finiteness

/-!
## 9. 常见错误

**① 旧名字 `cutsat`。** 整数线性算术的入口在 Lean v4.27.0（2026-01-24）改名为 `lia`，旧名字在 4.35 里是弃用
别名，会警告：
-/

/-- warning: `cutsat` has been deprecated, use `lia` instead -/
#guard_msgs (substring := true) in
example (x : ℤ) (h : 2 * x + 1 = 7) : x = 3 := by cutsat

/-!
**② 指望 `polyrith`。** 它依赖的外部服务已经关闭，Mathlib 里只剩占位，调用即报错，没有弃用日期
（`Mathlib/Tactic/Polyrith.lean` 的文档推荐 `grobner`）：
-/

/--
error: `polyrith` is no longer available, as the external service it relied on has been shut down.
-/
#guard_msgs in
example (x y : ℝ) (h₁ : x + y = 3) (h₂ : x - y = 1) : x = 2 := by polyrith

/-!
**③ 沿用 `peel`。** 自 2026-08-03 起弃用，换成 `gconvert` 或 `congr!`：
-/

/-- has been deprecated: use `gconvert` or `congr!` instead of `peel` -/
#guard_msgs (substring := true) in
example (h : ∀ n : ℕ, 0 < n → 1 ≤ n) : ∀ n : ℕ, 0 < n → 0 < n + 1 := by
  peel h with n hn h'
  omega

/-!
**④ 策略用错了片段。** `omega` 只认 `ℕ`、`ℤ`（以及 `Fin`），对 `ℝ` 它没有可用的约束，要换 `linarith`：
-/

/-- No usable constraints found. -/
#guard_msgs (substring := true) in
example (x : ℝ) (h : 0 < x) : 0 < x + 1 := by omega

example (x : ℝ) (h : 0 < x) : 0 < x + 1 := by linarith

/-!
## 练习

下面每一题都是「选哪个策略」：先判断目标在哪个片段，再选工具；有的需要给提示，有的要诊断一次失败。
★ 直接应用，★★ 综合两个想法，★★★ 需要想一想。练习 10.1、10.2、10.3、10.9、10.10、10.14 复习第 2、4、5 章。
-/

/-- 练习 10.1（★）：`ℕ` 上的取余与不等式（第 2 章）。 -/
theorem ex_10_1 (n : ℕ) (h : n % 4 = 3) : n % 2 = 1 ∧ 3 ≤ n := by sorry

/-- 练习 10.2（★）：`ℝ` 上的二次不等式（第 2 章）；差是一个平方，想想该给自动化什么提示。 -/
theorem ex_10_2 (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by sorry

/-- 练习 10.3（★）：交换环里的恒等式（第 2 章）。 -/
theorem ex_10_3 (a b : ℤ) : (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by sorry

/-- 练习 10.4（★）：含除法，要用到 `a ≠ 0`。 -/
theorem ex_10_4 (a : ℝ) (ha : a ≠ 0) : (a ^ 2 - 1) / a = a - 1 / a := by sorry

/-- 练习 10.5（★★）：`x ^ 2 + y ^ 2` 可用 `x + y` 与 `x * y` 表出；不要直接调 `grobner`，在纸上算出
`linear_combination` 的系数。 -/
theorem ex_10_5 (x y : ℝ) (h₁ : x * y = 2) (h₂ : x + y = 5) : x ^ 2 + y ^ 2 = 21 := by sorry

/-- 练习 10.6（★）：一个素数、一个合数、一个最大公约数。 -/
theorem ex_10_6 : Nat.Prime 211 ∧ ¬ Nat.Prime 221 ∧ Nat.gcd 84 90 = 6 := by sorry

/-- 练习 10.7（★★）：不等式两边结构相同；`x ^ 2` 的非负性是个副条件。 -/
theorem ex_10_7 (a b c d x : ℝ) (h₁ : a ≤ b) (h₂ : c ≤ d) :
    x ^ 2 * a + c ≤ x ^ 2 * b + d := by sorry

/-- 练习 10.8（★）：每个因子的符号都能从语法看出（`Real.exp` 有扩展）。 -/
theorem ex_10_8 (x y : ℝ) : 0 < Real.exp x * (y ^ 2 + 1) := by sorry

/-- 练习 10.9（★）：命题逻辑（第 4 章）。 -/
theorem ex_10_9 (p q r : Prop) : (p → q ∨ r) → ¬q → p → r := by sorry

/-- 练习 10.10（★★）：第 5 章的 `simp`；`Nat.sub_add_cancel` 是带副条件 `m ≤ n` 的 simp 引理，
用 `(disch := assumption)` 处理副条件。 -/
theorem ex_10_10 (n m : ℕ) (h : m ≤ n) : n - m + m + 0 = n := by sorry

/-- 练习 10.11（★★）：递推式的两个实例；`omega`、`lia` 不会自己实例化上下文里的 `∀` 假设
（`grind` 会，§4）。 -/
theorem ex_10_11 (f : ℕ → ℤ) (h : ∀ n, f (n + 1) = f n + 2) (h0 : f 0 = 1) : f 2 = 5 := by
  sorry

/-- 练习 10.12（★★）：集合恒等式（第 7 章系统地讲集合）；`aesop` 在这里没有进展，换个办法。 -/
theorem ex_10_12 (s t u : Set ℕ) : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := by sorry

/-- 练习 10.13（★）：任意全序里的矛盾。 -/
theorem ex_10_13 {α : Type*} [LinearOrder α] (a b c : α) (h : min a b ≤ c) (h₁ : c < a)
    (h₂ : c < b) : False := by sorry

/-- 练习 10.14（★★）：三个假设互相代入（第 5 章）。 -/
theorem ex_10_14 (a b c : ℕ) (h₁ : a + 0 = b) (h₂ : b * 1 = c) (h₃ : c = 4) : a = 4 := by sorry

/-- 练习 10.15（★★）：诊断。直接调 `positivity` 证不了这个目标：说出原因，再换一个能证的办法。 -/
theorem ex_10_15 (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by sorry

/-!
## 小结

**尝试顺序**（从便宜、错误信息好读的到贵的）：纯命题逻辑 `tauto`；`ℕ`、`ℤ` 线性 `omega`；环恒等式 `ring`，含
除法 `field`；线性不等式 `linarith`；符号可由语法看出 `positivity`；结构相同 `gcongr`；全序 `order`；逻辑与集合
混合 `aesop`；以上都不行再用 `grind`；找引理用 `exact?`。

**决策表**（目标形状，首选策略，导入，边界与补救）：

| 目标形状 | 首选 | 导入 | 边界与补救 |
|---|---|---|---|
| 重写到 simp 正规形 | `simp`、`simp only`、`simp_all` | 核心 | 条件引理：`(disch := tac)`；`simp [-foo]` |
| `ℕ`、`ℤ`、`Fin` 线性等式/不等式，含 `%`、`/` 字面量 | `omega` | 核心 | `∀` 假设：`specialize`、`lia [h 3]`、`grind` |
| 小的可判定命题 | `decide` | 核心 | 规模大：`decide +kernel`、`norm_num` |
| 数值，`Nat.Prime`，`gcd` | `norm_num` | `…NormNum.Prime`、`…GCD` | 假命题简化成 `False` |
| 交换环恒等式 | `ring` | `Mathlib.Tactic.Ring` | 不读假设：`linear_combination h`、`rw` |
| 含除法的恒等式 | `field` | `Mathlib.Tactic.Field` | 分母 `≠ 0`：`(disch := …)`、`field [h]` |
| 假设的线性组合给出结论 | `linear_combination` | `…LinearCombination` | `(norm := ring_nf)` 看残差；`grobner` |
| 加群恒等式 | `abel` | `Mathlib.Tactic.Abel` | 不读假设：先 `rw` |
| 有序域线性不等式 | `linarith` | `Mathlib.Tactic.Linarith` | `≠`：`+splitNe`；乘积：`nlinarith [提示]` |
| `0 < e`、`0 ≤ e`、`e ≠ 0` | `positivity` | `Mathlib.Tactic.Positivity` | 含减法：`nlinarith` |
| 结构相同的不等式 | `gcongr` | `Mathlib.Tactic.GCongr` | 补副条件；`bound` |
| 全序与格的纯序事实 | `order` | `Mathlib.Tactic.Order` | 分配律：直接用引理 |
| 命题逻辑 | `tauto` | `Mathlib.Tactic.Tauto` | 算术：`omega`、`linarith` |
| 逻辑与成员关系的混合 | `aesop` | `Mathlib.Tactic.Common` | 新定义：`(add norm unfold D)` |
| 同余、算术、分情况混合 | `grind` | 核心 | 归纳：先 `induction` |
| `Continuous`、`Measurable`、`x ≠ ∞` | `fun_prop`、`finiteness` | `…FunProp`、`…Finiteness` | 见第 14、16 章 |
| 找不到引理 | `exact?`（第 9 章） | 核心 | 换成显式名字再提交 |
-/

/-!
## 延伸阅读

- Lean 参考手册 4.35.0（`https://lean-lang.org/doc/reference/4.35.0/`）：第 14 章 Tactic Proofs（§14.3 The
  Tactic Language、§14.5 Tactic Reference）、第 15 章 The Simplifier、第 16 章 The `grind` tactic；
  `Init/Grind/Tactics.lean` 的文档注释列出 `grind` 的引擎与选项（`lia`、`grobner` 也在那里）。
- 核心库 `Lean/Meta/Tactic/Simp/LoopProtection.lean`（循环检测）、`SimpTheorems.lean`（`warning.simp.varHead`）。
- Mathlib：`Tactic/Ring/Basic.lean`、`FieldSimp.lean`、`Field.lean`、`LinearCombination.lean`、
  `Linarith/Frontend.lean`、`GCongr/Core.lean`、`Bound.lean`、`Order.lean` 的文档注释，以及
  `Polyrith.lean`（它为什么已死）。
- Aesop：`.lake/packages/aesop/README.md`；本书第 2、5、9、11 章（计算策略、simp 的机制、找引理、`nlinarith` 提示）。
-/

end Lean4Learn.Ch10

end
