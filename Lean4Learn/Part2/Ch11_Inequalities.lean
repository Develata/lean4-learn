module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 11 章　不等式与实数

研究里的大部分估计最后都落在实数不等式上：Chernoff 界要用 `1 + x ≤ exp x`，方差要用 Cauchy–Schwarz
inequality（柯西–施瓦茨不等式），熵要用 Jensen's inequality（琴生不等式）。本章整理 `ℝ` 上的不等式工具箱：
序的基本 lemma（引理）与 `calc` 链、乘除法与乘方的单调性、绝对值、`min`/`max`、`Real.sqrt`、`Real.exp` 与
`Real.log`、有限和的比较，然后是三个经典不等式（柯西–施瓦茨、AM–GM inequality（均值不等式）、琴生）在
Mathlib 里的形态，最后总结 `nlinarith` 的提示技巧。读完后你能把一个手写的不等式证明拆成「调用哪条引理、
在哪一步用哪个 tactic（策略）」，并能解释每条引理为什么需要它的副条件。

## 学习目标
- 用 `le_trans`、`lt_of_le_of_lt` 与 `calc + gcongr` 组织多步不等式；知道什么时候选 `linarith`、`nlinarith`、
  `gcongr`、`positivity`。
- 说出乘除法与乘方引理各自需要的符号条件（`mul_le_mul_of_nonneg_left`、`div_le_iff₀`、`pow_le_pow_left₀`），
  并用反例说明去掉条件之后命题为什么为假。
- 会用 `abs_le`、`abs_lt`、`abs_sub_lt_iff`、`abs_add_le`、`abs_sub_comm` 做 ε 估计；会处理 `min`/`max`。
- 知道 `Real.sqrt`、`Real.log`、除法的 junk value（垃圾值），以及它们如何决定引理的 hypothesis（假设）。
- 会写 `exp`/`log` 的基本界（`Real.add_one_le_exp`、`Real.log_le_sub_one_of_pos`），并由它们推出
  `(1 - p) ^ n ≤ exp (-(n * p))` 这类估计。
- 会用 `Finset.sum_le_sum`、`Finset.sum_nonneg` 与 `gcongr` 比较有限和。
- 会找到并使用 Mathlib 里柯西–施瓦茨、均值不等式、琴生不等式的具体形态（`Finset.sum_mul_sq_le_sq_mul_sq`、
  `Real.geom_mean_le_arith_mean_weighted`、`ConvexOn.map_sum_le`）。

## 前置知识
第 2 章（`linarith`、`nlinarith`、`positivity`、`calc`、垃圾值）；第 8 章（`ℝ`、coercion（强制转换）`↑`）；
第 9 章（找引理的方法）；第 10 章 §6（`gcongr` 与 `bound`，本章直接使用，不再重讲）。
§8 起出现 finset（有限集）与 big operator（大算子）`∑ i ∈ s, f i`（对 `s` 中的每个 `i` 求 `f i` 的和）和
`s.card`（`s` 的元素个数）；它们在第 12 章系统讲解，本章只把它们当作现成的对象来用。
-/

@[expose] public section

namespace Lean4Learn.Ch11

/-!
## 1. 序的基本引理、`calc` 链与 `ℝ` 的基本事实

不等式证明的骨架是传递性。三条核心引理按「两个前提各是 `≤` 还是 `<`」命名：`le_trans`、`lt_of_le_of_lt`、
`lt_of_lt_of_le`；`le_antisymm` 由两个方向的 `≤` 得到 `=`。它们有点记号版本：`h₁.trans h₂`、`h.le`。
-/

example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := le_trans h₁ h₂
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c := lt_of_le_of_lt h₁ h₂
example (a b : ℝ) (h : a < b) : a ≤ b := h.le

/-!
前提都是线性关系时，不必手写：第 2 章的 `linarith` 会自己找传递链。手写引理的价值在于一步需要「两边同乘
一个非负数」「两边取平方」「两边取 `exp`」这样的非线性操作时；`linarith` 不会自己做乘法：
-/

/--
error: linarith failed to find a contradiction
a b c : ℝ
h : a ≤ b
hc : 0 ≤ c
a✝ : c * b < c * a
⊢ False
failed
-/
#guard_msgs in
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by linarith

/-!
**`calc` 加 `gcongr`。** 链里的一步常常是「把 `X ≤ Y` 里的某个子项换成更大的」，这正是 `gcongr` 做的事
（第 10 章 §6）。下面两步的副条件（side condition）`0 ≤ c`、`0 ≤ b` 分别来自上下文里的假设：
-/

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    a * c ≤ b * d := by
  have hb : 0 ≤ b := ha.trans hab
  calc
    a * c ≤ b * c := by gcongr   -- 主目标 a ≤ b 由 hab 关闭，副条件 0 ≤ c 由 hc 关闭
    _ ≤ b * d := by gcongr       -- 主目标 c ≤ d 由 hcd 关闭，副条件 0 ≤ b 由 hb 关闭

/-!
**`ℝ` 的两个基本事实（第 14 章会大量用到）。** 一是阿基米德性质 `exists_nat_gt`：任何实数都小于某个自然数；
二是 `ℕ → ℝ` 的强制转换保序，用 `exact_mod_cast`（第 8 章）。合起来就能「由 `ε` 选 `N`」：
-/

example (m n : ℕ) (h : m ≤ n) : (m : ℝ) ≤ n := by exact_mod_cast h

example (ε : ℝ) (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)   -- hN : 1 / ε < ↑N
  have hpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  refine ⟨N, by exact_mod_cast hpos, ?_⟩
  rw [div_lt_iff₀ hε] at hN                 -- hN : 1 < ↑N * ε
  rw [div_lt_iff₀ hpos]
  linarith

/-!
## 2. 乘法与除法：符号条件从哪里来

加法保序不需要任何条件；乘法保序要求乘数非负（类 `PosMulMono` 一族说的就是「乘以非负数保序」，`ℝ` 满足它们）：
-/

example : PosMulMono ℝ := inferInstance

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := add_le_add_left h c
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := mul_le_mul_of_nonneg_left h hc
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := mul_le_mul_of_nonneg_right h hc

-- 条件不能去掉：乘以负数反序（取 `c = -1`）
example : ¬ ∀ a b c : ℝ, a ≤ b → c * a ≤ c * b := by
  intro h
  have h1 := h 0 1 (-1) (by norm_num)
  norm_num at h1

/-!
**`_left`/`_right` 的方向要逐个确认。** 在 `add_le_add_left h c : a + c ≤ b + c` 里，常数 `c` 在**右边**；
在 `mul_le_mul_of_nonneg_left h hc : c * a ≤ c * b` 里，乘数在**左边**。Mathlib 的 `mul_le_mul_left`、
`mul_le_mul_right` 属于没有符号条件的有序幺半群，用在 `ℝ` 上会失败（见「常见错误」第 1 条）；核心库里
`Nat.mul_le_mul_left` 的方向又和 Mathlib 的 `mul_le_mul_left` 不同（乘数 `k` 作为第一个参数、在左边）。
旧教程常把这些名字混用，永远靠 `#check` 或上面这样的例子确认，不要凭记忆。
-/

example (m n k : ℕ) (h : m ≤ n) : k * m ≤ k * n := Nat.mul_le_mul_left k h

/-!
**除法。** 除以正数保序，除以负数反序，除以 `0` 得 `0`（第 2 章的垃圾值）。最常用的一族「把除法搬到另一边」
的引理带条件 `0 < c`，名字里带 `₀` 后缀（`₀` 标记它们适用于带零元的结构，如 `ℝ`）：

- `div_le_iff₀ (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c`
- `le_div_iff₀ (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b`
- `div_lt_iff₀`、`lt_div_iff₀`：严格不等号版本

这一族之外还有不带 `₀` 的（如 `div_le_one`），以及专门针对负分母的 `div_le_iff_of_neg`。
-/

example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := (div_le_iff₀ hc).2 h
example (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := (le_div_iff₀ hc).2 h
example (a b c : ℝ) (hc : 0 < c) (h : a < b * c) : a / c < b := (div_lt_iff₀ hc).2 h
example (a b c : ℝ) (hc : c < 0) : a / c ≤ b ↔ b * c ≤ a := div_le_iff_of_neg hc

-- 用 `rw` 把除法清掉，再交给 `nlinarith`：a / b + b / a ≥ 2
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 ≤ a / b + b / a := by
  rw [div_add_div _ _ hb.ne' ha.ne', le_div_iff₀ (by positivity)]
  -- ⊢ 2 * (b * a) ≤ a * a + b * b
  nlinarith [sq_nonneg (a - b)]

/-!
其余几条：与 `1` 比较、取倒数反序（`one_div` 是 `1 / a = a⁻¹`）。写「等价形式」的取倒数引理是
`one_div_le_one_div`（本锁定版本里没有叫 `one_div_le_one_div_iff` 的引理，见「常见错误」第 2 条）：
-/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / b ≤ 1 / a ↔ a ≤ b := one_div_le_one_div hb ha

/-!
**条件不能去掉。** 把 `div_le_iff₀` 的假设 `0 < c` 去掉，命题就是假的：取 `a = 1`、`b = 0`、`c = 0`，
左边 `1 / 0 ≤ 0` 因为 `1 / 0 = 0` 而成立，右边 `1 ≤ 0 * 0` 不成立：
-/

example : ¬ ∀ a b c : ℝ, a / c ≤ b ↔ a ≤ b * c := by
  intro h
  have h1 := (h 1 0 0).1 (by simp)
  norm_num at h1

/-!
## 3. 绝对值

`|x|` 是 `abs x`。证明含绝对值的不等式有两个套路：用 `abs_le` 一类的引理把它拆成两个不含绝对值的
不等式，再交给 `linarith`；或用 `abs_add_le` 一类的引理做估计。`abs_le`、`abs_lt`、`abs_add_le` 等名字
没有可见的声明行，是由 `to_additive` 从乘法版本生成的，所以用 `#check` 和下面的例子确认：
-/

example (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y := abs_le
example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := abs_lt
example (x a ε : ℝ) : |x - a| < ε ↔ x - a < ε ∧ a - x < ε := abs_sub_lt_iff
example (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y
example (x y : ℝ) : |x - y| = |y - x| := abs_sub_comm x y
example (x : ℝ) (hx : 0 ≤ x) : |x| = x := abs_of_nonneg hx
example (x : ℝ) (hx : x < 0) : |x| = -x := abs_of_neg hx

/-!
**套路一：拆开。** 假设里的绝对值用 `abs_le.1` 拆成一对不等式，目标里的绝对值用 `abs_le.2 ⟨_, _⟩` 构造：
-/

example (x : ℝ) (h : |x - 1| ≤ 2) : -1 ≤ x ∧ x ≤ 3 := by
  obtain ⟨h1, h2⟩ := abs_le.1 h   -- h1 : -2 ≤ x - 1，h2 : x - 1 ≤ 2
  constructor <;> linarith

example (x : ℝ) : |x| ≤ x ^ 2 + 1 :=
  abs_le.2 ⟨by nlinarith [sq_nonneg (x + 1)], by nlinarith [sq_nonneg (x - 1)]⟩

/-!
**套路二：估计。** 经典的 ε 论证：两个量各自离目标不到 `ε`、`δ`，和离目标的和不到 `ε + δ`。一步一步用
`calc`，每步一条引理（`abs_add_lt` 是本章自己的命名，在命名空间 `Lean4Learn.Ch11` 内，不是 Mathlib 的名字）：
-/

theorem abs_add_lt (x y a b ε δ : ℝ) (hx : |x - a| < ε) (hy : |y - b| < δ) :
    |(x + y) - (a + b)| < ε + δ := by
  calc
    |(x + y) - (a + b)| = |(x - a) + (y - b)| := by congr 1; ring
    _ ≤ |x - a| + |y - b| := abs_add_le _ _
    _ < ε + δ := add_lt_add hx hy

/-!
## 4. 乘方与平方

平方非负是 `nlinarith` 的主要原料，`sq_nonneg a : 0 ≤ a ^ 2`。乘方的单调性按「底数变」还是「指数变」分：
`pow_le_pow_left₀` 底数变（要 `0 ≤ a`），`pow_le_pow_right₀` 指数变（要 `1 ≤ a`），严格版本是
`pow_lt_pow_left₀`、`pow_lt_pow_right₀`。老教程里的 `pow_le_pow_left` 在本锁定版本里已被删除（见「常见错误」）。
-/

example (a : ℝ) : 0 ≤ a ^ 2 := sq_nonneg a
example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := pow_le_pow_left₀ ha hab n
example (a : ℝ) (ha : 1 ≤ a) {m n : ℕ} (h : m ≤ n) : a ^ m ≤ a ^ n := pow_le_pow_right₀ ha h

-- 两个条件都不能去掉
example : ¬ ∀ a b : ℝ, a ≤ b → a ^ 2 ≤ b ^ 2 := by   -- 去掉 `0 ≤ a`：a = -3，b = -2
  intro h
  have h1 := h (-3) (-2) (by norm_num)
  norm_num at h1

example : ¬ ∀ (a : ℝ) (m n : ℕ), m ≤ n → a ^ m ≤ a ^ n := by   -- 去掉 `1 ≤ a`：a = 1/2
  intro h
  have h1 := h (1 / 2) 1 2 (by norm_num)
  norm_num at h1

/-!
**平方与绝对值。** `x ^ 2 ≤ y ^ 2` 并不推出 `x ≤ y`：缺的是 `y` 的符号，反例 `x = 0`、`y = -1`（下面）。
有了 `0 ≤ y` 就行：`x ≤ |x| ≤ y`（下面第二个例子）。一般只有 `|x| ≤ |y|`
（`sq_le_sq`）；在 `0 ≤ y` 时推出 `|x| ≤ y`（`abs_le_of_sq_le_sq`）；只有 `x`、`y` 都非负时才等价（`sq_le_sq₀`）。
反方向：`-y ≤ x ≤ y` 推出 `x ^ 2 ≤ y ^ 2`（`sq_le_sq'`）。
-/

example (a b : ℝ) : a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b| := sq_le_sq
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b := sq_le_sq₀ ha hb
example (a b : ℝ) (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := abs_le_of_sq_le_sq h hb

example : ¬ ∀ x y : ℝ, x ^ 2 ≤ y ^ 2 → x ≤ y := by   -- x = 0，y = -1
  intro h
  have h1 := h 0 (-1) (by norm_num)
  norm_num at h1

example (x y : ℝ) (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : x ≤ y :=   -- x ≤ |x| ≤ y
  (le_abs_self x).trans (abs_le_of_sq_le_sq h hy)

-- 伯努利不等式在 Mathlib 里叫 `one_add_mul_le_pow`，假设比常见写法更弱：`-2 ≤ a` 就够
example (a : ℝ) (ha : -2 ≤ a) (n : ℕ) : 1 + n * a ≤ (1 + a) ^ n := one_add_mul_le_pow ha n

/-!
## 5. `min` 与 `max`

`min`/`max` 出现在「取 `N` 为两个阈值中较大者」这类 ε 论证里。它们的引理分两类：「上界/下界」型
（`min_le_left`、`le_min`、`le_max_left`、`max_le`）和「当且仅当」型（`min_le_iff`、`le_max_iff`、`max_lt_iff`、
`lt_min_iff`）。`linarith` 不会拆开 `min` 与 `max`，要把需要的引理作为额外的项交给它（不给就失败，见「常见错误」）：
-/

example (a b c : ℝ) (h₁ : c ≤ a) (h₂ : c ≤ b) : c ≤ min a b := le_min h₁ h₂
example (a b c : ℝ) (h₁ : a ≤ c) (h₂ : b ≤ c) : max a b ≤ c := max_le h₁ h₂
example (a b c : ℝ) : c ≤ max a b ↔ c ≤ a ∨ c ≤ b := le_max_iff

example (a b : ℝ) : min a b ≤ (a + b) / 2 := by
  linarith [min_le_left a b, min_le_right a b]

-- 想证等式时按大小分情形：`le_total a b : a ≤ b ∨ b ≤ a`
example (a b : ℝ) : max a b + min a b = a + b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]; ring
  · rw [max_eq_left h, min_eq_right h]   -- 两边已经相同，`rw` 末尾的 `rfl` 关闭目标

/-!
## 6. 平方根

`Real.sqrt x`（记号 `√x`）对负数取 `0`，这是又一个垃圾值；所以许多关于 `√` 的等式引理带 `0 ≤ x` 的假设
（单调与非负性引理常常不带）。`Real.sq_sqrt` 与 `Real.sqrt_sq` 是两个复合顺序，假设同为 `0 ≤ x`，但失败的
方式不同：负数 `x` 时 `√x ^ 2` 变成 `0`，而 `√(x ^ 2)` 变成 `|x|`（无条件版本 `Real.sqrt_sq_eq_abs`）。
`NNReal` 里有同名的 `NNReal.sq_sqrt`，所以本书一律写全 `Real.` 前缀。
-/

example (x : NNReal) : NNReal.sqrt x ^ 2 = x := NNReal.sq_sqrt x

example (x : ℝ) : 0 ≤ √x := Real.sqrt_nonneg x
example (x : ℝ) (hx : 0 ≤ x) : √x ^ 2 = x := Real.sq_sqrt hx
example (x : ℝ) (hx : 0 ≤ x) : √(x ^ 2) = x := Real.sqrt_sq hx
example (x : ℝ) : √(x ^ 2) = |x| := Real.sqrt_sq_eq_abs x
example (x y : ℝ) (hy : 0 ≤ y) : √x ≤ y ↔ x ≤ y ^ 2 := Real.sqrt_le_left hy
example (x y : ℝ) (h : x ^ 2 ≤ y) : |x| ≤ √y := Real.abs_le_sqrt h

-- 垃圾值：`√(-1) = 0`，所以 `√x ^ 2 = x` 对负的 `x` 是假的
example : √(-1 : ℝ) = 0 := Real.sqrt_eq_zero_of_nonpos (by norm_num)
example : √(-1 : ℝ) ^ 2 ≠ -1 := by
  rw [Real.sqrt_eq_zero_of_nonpos (by norm_num)]
  norm_num

-- 另一个方向：`√(x ^ 2) = |x|`，所以 `√(x ^ 2) = x` 对负的 `x` 也是假的
example : ¬ ∀ x : ℝ, √(x ^ 2) = x := by
  intro h
  have h1 := h (-1)
  rw [Real.sqrt_sq_eq_abs] at h1
  norm_num at h1

/-!
`Real.sqrt` 在源码里标了 `@[irreducible]`（`Mathlib/Analysis/Real/Sqrt.lean`），`rfl` 算不出具体的根。
求具体的根要靠 `norm_num` 的扩展 `Mathlib.Tactic.NormNum.RealSqrt`（本章导入了它；不导入时只能用
`4 = 2 ^ 2` 加 `Real.sqrt_sq` 这样的引理）：
-/

/--
error: Tactic `rfl` failed: The left-hand side
  √4
is not definitionally equal to the right-hand side
  2

⊢ √4 = 2
-/
#guard_msgs in
example : √(4 : ℝ) = 2 := by rfl

example : √(4 : ℝ) = 2 := by norm_num

/-!
## 7. `exp` 与 `log`

`Real.exp` 处处为正且严格递增；`Real.log` 是它在正数上的反函数，对 `x ≤ 0` 取垃圾值（`Real.log 0 = 0`，
`Real.log (-x) = Real.log x`）。两个最重要的界是 `x + 1 ≤ exp x`（`Real.add_one_le_exp`）与
`log x ≤ x - 1`（`Real.log_le_sub_one_of_pos`）。
-/

example (x : ℝ) : 0 < Real.exp x := Real.exp_pos x
example (x : ℝ) : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
example (x y : ℝ) (hx : 0 < x) (hy : x ≤ y) : Real.log x ≤ Real.log y := Real.log_le_log hx hy
example (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx
example (x : ℝ) (hx : 0 ≤ x) : Real.log (√x) = Real.log x / 2 := Real.log_sqrt hx

/-!
**两个界互推。** 从 `x + 1 ≤ exp x` 得 `log x ≤ x - 1`：对 `log x` 用前者，再用 `exp_log` 消去
`exp (log x)`；反过来，对 `exp x` 用后者，再用 `log_exp`：
-/

example (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1 := by
  have h := Real.add_one_le_exp (Real.log x)   -- h : log x + 1 ≤ exp (log x)
  rw [Real.exp_log hx] at h                    -- h : log x + 1 ≤ x
  linarith

example (x : ℝ) : x + 1 ≤ Real.exp x := by
  have h := Real.log_le_sub_one_of_pos (Real.exp_pos x)   -- h : log (exp x) ≤ exp x - 1
  rw [Real.log_exp] at h                                   -- h : x ≤ exp x - 1
  linarith

/-!
**`log` 的恒等式也有条件。** `Real.log_mul` 要 `x ≠ 0` 与 `y ≠ 0`；去掉之后命题为假：取 `x = 0`，
`log (0 * y) = log 0 = 0`，而 `log 0 + log y = log y` 一般不为 `0`。另一个后果：`log` 在负数上不单调，
`log (-2) = log 2 > 0 = log (-1)`，尽管 `-2 ≤ -1`：
-/

example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : Real.log (x * y) = Real.log x + Real.log y :=
  Real.log_mul hx hy

example : ¬ ∀ x y : ℝ, Real.log (x * y) = Real.log x + Real.log y := by
  intro h
  have h1 := h 0 (Real.exp 1)
  simp at h1

example : ¬ ∀ x y : ℝ, x ≤ y → Real.log x ≤ Real.log y := by
  intro h
  have h1 := h (-2) (-1) (by norm_num)
  rw [Real.log_neg_eq_log, Real.log_neg_eq_log, Real.log_one] at h1
  linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]

/-!
**应用：`(1 - p) ^ n ≤ exp (-(n * p))`。** 这是概率里最常用的估计之一（`n` 次独立试验全部落空的概率）。
思路：`1 - p ≤ exp (-p)`（`add_one_le_exp (-p)`），两边取 `n` 次幂（底数非负才能保序，所以要 `p ≤ 1`），再用
`Real.exp_nat_mul` 合并指数。`gcongr` 做第二步：
-/

theorem one_sub_pow_le_exp (p : ℝ) (hp : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ Real.exp (-(n * p)) := by
  have h0 : 0 ≤ 1 - p := by linarith
  calc
    (1 - p) ^ n ≤ Real.exp (-p) ^ n := by
      gcongr                                  -- 副条件 0 ≤ 1 - p 来自 h0；主目标留下一个
      linarith [Real.add_one_le_exp (-p)]
    _ = Real.exp (n * -p) := (Real.exp_nat_mul (-p) n).symm
    _ = Real.exp (-(n * p)) := by congr 1; ring

/-!
## 8. 有限和与有限积的比较

逐项比较推出和的比较：`Finset.sum_le_sum`（每项 `≤`）、`Finset.sum_nonneg`（每项 `≥ 0`）、
`Finset.abs_sum_le_sum_abs`（三角不等式）。假设的形状是 `∀ i ∈ s, …`：只需对 `s` 里的元素成立；
手上是 `∀ i, …` 时写成 `fun i _ ↦ h i`。
-/

example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := Finset.sum_le_sum h
example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i, f i ≤ g i) :
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := Finset.sum_le_sum fun i _ ↦ h i
example (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i :=
  Finset.sum_nonneg h

-- 每项有界，则和有界
theorem sum_le_card_mul (s : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) (h : ∀ i ∈ s, f i ≤ c) :
    ∑ i ∈ s, f i ≤ s.card * c := by
  calc
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, c := Finset.sum_le_sum h
    _ = s.card * c := by simp

/-!
**有限积。** 乘积的比较要非负条件：`ℝ` 上用 `Finset.prod_le_prod₀`（两个假设：每项非负、每项 `≤`）和
`Finset.prod_nonneg`。不带 `₀` 的 `Finset.prod_le_prod` 只适用于有序交换幺半群，不适用于 `ℝ`（见「常见错误」）。
去掉非负条件，命题为假（两个负数的积反序）：
-/

example (s : Finset ℕ) (f g : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := Finset.prod_le_prod₀ h0 h
example (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∏ i ∈ s, f i :=
  Finset.prod_nonneg h

example : ¬ ∀ f g : ℕ → ℝ, (∀ i, f i ≤ g i) → f 0 * f 1 ≤ g 0 * g 1 := by
  intro h
  have h1 := h (fun _ ↦ -2) (fun _ ↦ -1) (fun _ ↦ by norm_num)
  norm_num at h1

/-!
## 9. 三个经典不等式在 Mathlib 里的形态

### 9.1 柯西–施瓦茨

有限和版本是 `Finset.sum_mul_sq_le_sq_mul_sq s f g`：
`(∑ f i * g i) ^ 2 ≤ (∑ f i ^ 2) * ∑ g i ^ 2`。它不要求各项非负，但要求值域是线性有序的交换半环，且满足
`IsStrictOrderedRing` 与 `ExistsAddOfLE`（`ℕ`、`ℤ`、`ℚ`、`ℝ` 都满足）。取 `g = 1` 的特例
`sq_sum_le_card_mul_sum_sq` 在 Mathlib 里另有一个来自 Chebyshev 和不等式的证明。
（内积空间版本在 `Mathlib/Analysis/InnerProductSpace/Basic.lean`，本章不用。）
-/

example (s : Finset ℕ) (f g : ℕ → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

example (s : Finset ℕ) (f : ℕ → ℝ) : (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 :=
  sq_sum_le_card_mul_sum_sq

/-!
### 9.2 均值不等式

两个变量的平方形式 `a * b ≤ (a² + b²) / 2` 靠 `nlinarith [sq_nonneg (a - b)]`（本章 §10）。Mathlib 里的
版本带权重、带实数幂。这里的 `x ^ (y : ℝ)` 是 `Real.rpow`，与指数为 `ℕ` 的 `^`（第 8 章）是两回事；
它的引理几乎都要底数 `0 < x` 或 `0 ≤ x`（如下面的 `Real.rpow_add hx`），指数为自然数时两者一致：
-/

example (a b : ℝ) : a ^ b = Real.rpow a b := (Real.rpow_eq_pow a b).symm
example (x y z : ℝ) (hx : 0 < x) : x ^ (y + z) = x ^ y * x ^ z := Real.rpow_add hx y z

/-!
均值不等式的两个版本：`Real.geom_mean_le_arith_mean2_weighted`（两项）与
`Real.geom_mean_le_arith_mean_weighted`（`n` 项，权重 `w i ≥ 0` 且和为 `1`，点 `z i ≥ 0`），结论是
`∏ z i ^ w i ≤ ∑ w i * z i`。
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) ≤ 1 / 2 * a + 1 / 2 * b :=
  Real.geom_mean_le_arith_mean2_weighted (by norm_num) (by norm_num) ha hb (by norm_num)

example (s : Finset ℕ) (w z : ℕ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 ≤ z i) : ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i :=
  Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz

/-!
### 9.3 琴生不等式

`ConvexOn ℝ s f` 说 `f` 在凸集 `s` 上是 convex function（凸函数）。它的定义里含两点形式：`.2` 取出
「对 `s` 中两点 `x`、`y`，权重 `a`、`b ≥ 0` 且 `a + b = 1`，有 `f (a • x + b • y) ≤ a • f x + b • f y`」。
琴生不等式是 `ConvexOn.map_sum_le`：权重 `w i ≥ 0`、和为 `1`、点都在 `s` 里，则
`f (∑ w i • p i) ≤ ∑ w i • f (p i)`。这里是标量乘 `•`，在 `ℝ` 上用 `smul_eq_mul` 化成 `*`。
-/

example (x y : ℝ) :
    Real.exp ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤
      (1 / 2 : ℝ) • Real.exp x + (1 / 2 : ℝ) • Real.exp y :=
  convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) (by norm_num) (by norm_num) (by norm_num)

/-!
用 `smul_eq_mul` 化简后，括号里是 `1 / 2 * x + 1 / 2 * y`，常与你的目标里的 `(x + y) / 2` 不同。两者相等是线性事实，
`linarith` 能证；但它们在 `Real.exp` 里面时，`linarith` 把 `Real.exp (…)` 整个当作 atom（原子），两种写法
是两个不同的原子，它不会替你改写括号里的内容。补救是先用 `ring` 证明二者相等并 `rw`：
-/

example (x y : ℝ) : (x + y) / 2 = 1 / 2 * x + 1 / 2 * y := by linarith

/-- error: linarith failed to find a contradiction -/
#guard_msgs (substring := true) in
example (x y c : ℝ) (h : Real.exp (1 / 2 * x + 1 / 2 * y) ≤ c) :
    Real.exp ((x + y) / 2) ≤ c := by linarith

example (x y c : ℝ) (h : Real.exp (1 / 2 * x + 1 / 2 * y) ≤ c) :
    Real.exp ((x + y) / 2) ≤ c := by
  rw [show (x + y) / 2 = 1 / 2 * x + 1 / 2 * y by ring]
  linarith

/-!
**例 1：`exp` 的琴生不等式。** 定义域是全空间，点的归属条件由 `Set.mem_univ` 给出：
-/

theorem exp_sum_le (s : Finset ℕ) (w x : ℕ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) :
    Real.exp (∑ i ∈ s, w i * x i) ≤ ∑ i ∈ s, w i * Real.exp (x i) := by
  have h := convexOn_exp.map_sum_le hw hw1 (fun i _ ↦ Set.mem_univ (x i))
  simpa only [smul_eq_mul] using h

/-!
**例 2：`x ^ 2` 的琴生不等式。** 结论是「加权平均的平方 `≤` 平方的加权平均」。`convexOn_pow n` 的定义域
是 `Set.Ici 0`（需要点非负）；偶数次幂另有 `Even.convexOn_pow`，定义域是全空间，所以这里不要求 `x i ≥ 0`：
-/

theorem sq_sum_le (s : Finset ℕ) (w x : ℕ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤ ∑ i ∈ s, w i * x i ^ 2 := by
  have h := (Even.convexOn_pow (𝕜 := ℝ) even_two).map_sum_le hw hw1
    (fun i _ ↦ Set.mem_univ (x i))
  simpa only [smul_eq_mul] using h

/-!
## 10. `nlinarith` 的提示技巧

`nlinarith`（第 2 章）把假设和提示项两两相乘，再交给 `linarith`。它找不到的时候，缺的几乎总是某个
**平方非负**或某个**乘积非负**的事实，你把它写进方括号。找提示的方法：先把目标移项成「差 `≥ 0`」，试着
配方或因式分解，每个平方、每对非负因子之积就是一个提示。常用的提示：

| 要用的事实 | 提示项 |
|---|---|
| `(a - b)² ≥ 0` | `sq_nonneg (a - b)` |
| 两个正数的积为正 | `mul_pos ha hb` |
| 两个非负数的积非负 | `mul_nonneg ha hb` |
| `(x - 1)(y - 1) ≥ 0`，已知 `1 ≤ x`、`1 ≤ y` | `mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy)` |
| 把 `|a| ^ 2` 化成 `a ^ 2` | `sq_abs a` |

下面每个例子展示一种提示。先看不带假设的：
-/

example (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]

-- 带假设：把假设相乘的结果作为提示
example (x y : ℝ) (h1 : 1 ≤ x) (h2 : 1 ≤ y) : x + y ≤ x * y + 1 := by
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x ^ 2 + y ^ 2 < (x + y) ^ 2 := by
  nlinarith [mul_pos hx hy]

-- 绝对值：先用 `sq_abs` 把 `|a| ^ 2` 换成 `a ^ 2`
example (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-!
三次的不等式 `a b (a + b) ≤ a³ + b³`（`a, b ≥ 0`）：差是 `(a + b)(a - b)²`。不给提示时 `nlinarith` 找不到；
给一个平方 `sq_nonneg (a - b)`，它会自己把它与假设 `0 ≤ a`、`0 ≤ b` 相乘，凑出 `(a + b)(a - b)²`；

-/

/--
error: linarith failed to find a contradiction
a b : ℝ
ha : 0 ≤ a
hb : 0 ≤ b
a✝ : a ^ 3 + b ^ 3 < a * b * (a + b)
⊢ False
failed
-/
#guard_msgs in
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b * (a + b) ≤ a ^ 3 + b ^ 3 := by
  nlinarith

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b * (a + b) ≤ a ^ 3 + b ^ 3 := by
  nlinarith [sq_nonneg (a - b)]

/-!
**`positivity` 与 `bound`** 认得本章的函数（它们在第 10 章 §6 已系统介绍）：
-/

example (x y : ℝ) : 0 < Real.exp x + √y := by positivity
example : 0 < Real.log 2 := by positivity
example (x y : ℝ) (h : x ≤ y) : Real.exp x ≤ Real.exp y := by bound

/-!
## 11. 常见错误

**1. 在 `ℝ` 上用 `mul_le_mul_left`。** 它的前提是「右乘保序」，不带符号条件，只有有序幺半群才满足；
`ℝ` 上右乘负数反序，所以 instance（实例）找不到。改用 `mul_le_mul_of_nonneg_right h hc`：
-/

/-- error: failed to synthesize instance of type class
  MulRightMono ℝ -/
#guard_msgs (whitespace := lax, substring := true) in
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := mul_le_mul_left h c

/-!
**2. 旧名字或不存在的名字。** `pow_le_pow_left`（现为 `pow_le_pow_left₀`）是未知标识符
（`div_le_iff` 见第 9 章 §15 ①）；`one_div_le_one_div_iff` 在本锁定版本里没有这个名字，等价形式是
`one_div_le_one_div`。本书不记录这些名字的删除日期，遇到旧教程时按这里的对照改：
-/

/-- error: Unknown identifier `pow_le_pow_left` -/
#guard_msgs in
example (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := pow_le_pow_left ha hab 2

/-- error: Unknown identifier `one_div_le_one_div_iff` -/
#guard_msgs in
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / b ≤ 1 / a ↔ a ≤ b :=
  one_div_le_one_div_iff ha hb

/-!
**3. `Finset.prod_le_prod` 用在 `ℝ` 上。** 它要求有序交换幺半群；`ℝ` 对乘法不是（负数乘法反序），
所以报找不到实例。改用 `Finset.prod_le_prod₀` 并补上非负假设：
-/

/-- error: failed to synthesize instance of type class
  MulLeftMono ℝ -/
#guard_msgs (whitespace := lax, substring := true) in
example (s : Finset ℕ) (f g : ℕ → ℝ) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := Finset.prod_le_prod h

/-!
**4. `linarith` 不拆 `min`。** 同第 5 节：缺 `min_le_left` 一类的引理就失败：
-/

/--
error: linarith failed to find a contradiction
a b : ℝ
a✝ : (a + b) / 2 < min a b
⊢ False
failed
-/
#guard_msgs in
example (a b : ℝ) : min a b ≤ (a + b) / 2 := by linarith

/-!
## 练习

练习大致按小节顺序排列。11.1 用反例（第 4 章的否定与量词），11.2、11.10 用 `calc`（第 5 章），11.5 回到垃圾值
（第 2 章），11.6 用 `rcases`（第 4 章），11.11 是 ε–δ 的存在性证明（第 4 章），11.14 是归纳（第 6 章），
11.15 里有 `ℕ → ℝ` 的强制转换（第 8 章）。引理名在本章出现，或由题面的提示给出。
-/

/-- 练习 11.1（★）：去掉 `pow_le_pow_left₀` 的非负条件，命题为假；证明它的否定。
提示：取 `a = -3`，`b = -2`（本章 §4 有类似的例子）。 -/
theorem ex_11_1 : ¬ ∀ a b : ℝ, a ≤ b → a ^ 2 ≤ b ^ 2 := by sorry

/-- 练习 11.2（★）：三角不等式的变形；写成两步的 `calc`，用 `abs_add_le`。
提示：`a - c = (a - b) + (b - c)`。 -/
theorem ex_11_2 (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by sorry

/-- 练习 11.3（★★）：先用 `abs_lt.1` 拆开假设，再用 `abs_lt.2` 构造结论。 -/
theorem ex_11_3 (x : ℝ) (h : |x - 2| < 1) : |x ^ 2 - 4| < 5 := by sorry

/-- 练习 11.4（★）：先用 `div_lt_iff₀` 去掉分母（本章 §2），再用 `linarith`；副条件用 `positivity`。 -/
theorem ex_11_4 (a : ℝ) (ha : 0 ≤ a) : a / (a + 1) < 1 := by sorry

/-- 练习 11.5（★）：`Real.sqrt` 的垃圾值；这个命题为假，证明它的否定（本章 §6 有类似的例子）。 -/
theorem ex_11_5 : ¬ ∀ x : ℝ, √x ^ 2 = x := by sorry

/-- 练习 11.6（★★）：`min` 与 `max`；先 `rcases le_total a b`（本章 §5），再重写。 -/
theorem ex_11_6 (a b : ℝ) : max a b - min a b = |a - b| := by sorry

/-- 练习 11.7（★★）：`gcongr` 加 `calc`；先说明 `0 ≤ b`，再让 `gcongr` 逐项比较
`a ^ 2 ≤ b ^ 2` 与 `3 * a ≤ 3 * b`。 -/
theorem ex_11_7 (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : a ^ 2 + 3 * a ≤ b ^ 2 + 3 * b := by sorry

/-- 练习 11.8（★★）：`log x ≤ 2 * (√x - 1)`；对 `√x` 用 `Real.log_le_sub_one_of_pos`，
再用 `Real.log_sqrt`（`Real.log √x = Real.log x / 2`，需要 `0 ≤ x`）与 `Real.sqrt_pos`
（`0 < √x ↔ 0 < x`）。 -/
theorem ex_11_8 (x : ℝ) (hx : 0 < x) : Real.log x ≤ 2 * (√x - 1) := by sorry

/-- 练习 11.9（★）：`Real.log x < x`；用 `Real.log_le_sub_one_of_pos` 与 `linarith`。 -/
theorem ex_11_9 (x : ℝ) (hx : 0 < x) : Real.log x < x := by sorry

/-- 练习 11.10（★★）：逐项绝对值有界则和有界；用 `Finset.abs_sum_le_sum_abs`、
`Finset.sum_le_sum`，与本章 §8 的 `sum_le_card_mul` 同样的收尾。 -/
theorem ex_11_10 (s : Finset ℕ) (f : ℕ → ℝ) (c : ℝ) (h : ∀ i ∈ s, |f i| ≤ c) :
    |∑ i ∈ s, f i| ≤ s.card * c := by sorry

/-- 练习 11.11（★）：ε–δ 形式的存在性命题。取 `δ = ε / 3`；用 `refine ⟨_, _, fun x hx ↦ ?_⟩`
（第 4 章）搭骨架，再用 `abs_lt` 拆开与构造。 -/
theorem ex_11_11 (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ x : ℝ, |x - 1| < δ → |3 * x - 3| < ε := by
  sorry

/-- 练习 11.12（★★）：两点的琴生不等式；用 `convexOn_exp.2`，权重取 `1 / 2`，
再用 `smul_eq_mul` 化简。注意 `(x + y) / 2` 与 `1 / 2 * x + 1 / 2 * y` 在 `Real.exp` 里面，
`linarith` 把两个 `Real.exp (…)` 当作不同的原子：先用 `ring` 证明二者相等并 `rw`（本章 §9.3）。 -/
theorem ex_11_12 (x y : ℝ) : Real.exp ((x + y) / 2) ≤ (Real.exp x + Real.exp y) / 2 := by sorry

/-- 练习 11.13（★★）：三个变量的均值不等式（立方形式）；差是
`(a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2`。记 `hs : 0 ≤ a + b + c`，
给 `nlinarith` 三个提示 `mul_nonneg hs (sq_nonneg (a - b))`，以及对 `(b - c)`、`(c - a)` 的同类项。 -/
theorem ex_11_13 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by sorry

/-- 练习 11.14（★★★）：伯努利不等式；对 `n` 归纳，归纳步里 `rw [pow_succ]`，`push_cast`，
再 `nlinarith`，提示为 `mul_nonneg (sub_nonneg.2 ih) h1` 与
`mul_nonneg (Nat.cast_nonneg n) (sq_nonneg x)`，
其中 `h1 : 0 ≤ 1 + x`。Mathlib 里是 `one_add_mul_le_pow`，这里不许用它，要你手工证明。 -/
theorem ex_11_14 (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n := by sorry

/-- 练习 11.15（★★★）：`(1 + x / n) ^ n ≤ exp x`。仿 `one_sub_pow_le_exp`：先证
`0 ≤ 1 + x / n` 与 `1 + x / n ≤ exp (x / n)`，再 `pow_le_pow_left₀` 与 `Real.exp_nat_mul`。 -/
theorem ex_11_15 (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : -(n : ℝ) ≤ x) :
    (1 + x / n) ^ n ≤ Real.exp x := by sorry

/-!
## 小结

| 工具 | 名字 / 语法 | 何时用 | 条件（本章有例子） |
|---|---|---|---|
| 链 | `calc` + `gcongr` | 多步单调代入 | 副条件由 `positivity` 证 |
| 乘法 | `mul_le_mul_of_nonneg_left/right`、`mul_le_mul` | 乘一个量 | `0 ≤ c`；不是 `mul_le_mul_left` |
| 除法 | `div_le_iff₀`、`le_div_iff₀`、`div_lt_iff₀` | 搬走分母 | `0 < c`；`x / 0 = 0` |
| 乘方 | `pow_le_pow_left₀`、`pow_le_pow_right₀`、`sq_nonneg` | 底数 / 指数变 | `0 ≤ a` / `1 ≤ a` |
| 平方根 | `Real.sq_sqrt`、`Real.sqrt_sq`、`Real.sqrt_le_left` | 去根号 | `0 ≤ x`；`√(-1) = 0` |
| 指数对数 | `Real.add_one_le_exp`、`Real.log_le_sub_one_of_pos` | `exp`/`log` 的界 | `log` 要 `0 < x` |
| 有限和 | `Finset.sum_le_sum`、`Finset.sum_nonneg`、`Finset.sum_lt_sum` | 逐项比较 | `∀ i ∈ s, …` |
| 有限积 | `Finset.prod_le_prod₀`、`Finset.prod_nonneg` | 非负项的积 | 每项非负 |
| 柯西–施瓦茨 | `Finset.sum_mul_sq_le_sq_mul_sq` | 和的平方 | 线性有序交换半环 |
| 均值不等式 | `Real.geom_mean_le_arith_mean_weighted` | 几何 ≤ 算术 | 权重与点非负、权重和为 `1` |
| 琴生 | `ConvexOn.map_sum_le`、`convexOn_exp`、`Even.convexOn_pow` | 凸函数的加权平均 | 点在定义域内 |
-/

/-!
## 延伸阅读

- Mathematics in Lean（MIL，《Lean 形式化数学》）第 2 章 2.3 *Using Theorems and Lemmas*（`le_trans`、
  `min`/`max`、`abs` 的引理）及其后的 *More examples using apply and rw*；第 3 章 3.1 *Implication and the
  Universal Quantifier* 与 3.6 *Sequences and Convergence*（绝对值与 ε 论证）。
- Mathlib 源码：`Mathlib/Algebra/Order/Field/Basic.lean`（`one_div_le_one_div`、`div_le_iff_of_neg`）、
  `Mathlib/Algebra/Order/Group/Abs.lean`（`abs_*` 的乘法原型 `mabs_*`）、
  `Mathlib/Analysis/Real/Sqrt.lean`、`Mathlib/Tactic/NormNum/RealSqrt.lean`、
  `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`。
- 经典不等式：`Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`（`Finset.sum_mul_sq_le_sq_mul_sq`）、
  `Mathlib/Analysis/MeanInequalities.lean`（`Real.geom_mean_le_arith_mean_weighted`、Hölder、Young）、
  `Mathlib/Analysis/Convex/Jensen.lean`（`ConvexOn.map_sum_le`）、
  `Mathlib/Analysis/Convex/Mul.lean`（`Even.convexOn_pow`）。
- 本书第 2 章（`linarith`/`nlinarith`/`positivity`）、第 10 章（`gcongr` 与 `bound` 的完整比较）、第 12 章
  （有限和的计算）、第 14 章（极限与 ε–N）、第 17 章（马尔可夫不等式、切比雪夫不等式的概率形态）。
-/

end Lean4Learn.Ch11

end
