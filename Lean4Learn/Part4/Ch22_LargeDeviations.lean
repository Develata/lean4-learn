module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.StrongLaw
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# 第 22 章　大偏差入门：Cramér 型上界

weak law of large numbers（弱大数定律，第 17 章）说 `S_n / n` 以高概率靠近均值；large deviations
（大偏差）问的是：偏离均值一个固定的量 `a` 的概率，趋于 `0` 有多快？在 exponential moment（指数矩）条件下
（例如有界变量）答案是指数快，而且指数是一个可以写出来的函数：rate function（速率函数），它是
cumulant-generating function（累积量母函数）`Λ` 的 Legendre–Fenchel 变换。本章手工定义 `Λ` 与（单边的）`Λ*`，完整证明 Cramér 型上界
`P(S_n ≥ n a) ≤ exp (-n Λ*(a))`，对 Bernoulli distribution（伯努利分布）把 `Λ*` 算成相对熵的闭式，
然后盘点：Mathlib 在这个方向上有什么（`Measure.tilted`、`klDiv`、`LowerSemicontinuous`、Chernoff 界），
没有什么（Cramér 定理、Sanov 定理、大偏差原理本身），以及如果要把 Cramér 定理形式化，
依赖关系图（blueprint）长什么样。

本章的主要定理（Chernoff 界、Cramér 型上界、伯努利分布的速率函数）都给出完整证明；§9 的待办条目
是自己做项目的起点。所有被引用的 Mathlib 名字都在本地 `.lake/packages/mathlib` 里核对过。

## 学习目标
- 能用一段话说清楚大偏差问题与速率函数，并手算伯努利分布的速率函数。
- 会定义 `Λ t := cgf X μ t` 与 `Λ* a := ⨆ t ≥ 0, (t * a - Λ t)`（这里用子类型上的 `iSup`），
  知道 `ℝ` 上 `iSup`（supremum（上确界））对无上界族取 junk value（垃圾值）`0`，
  并能举出一个让这个垃圾值真正改变结论的例子。
- 会用 `le_ciSup`（要 `BddAbove`）与 `ciSup_le`（只要 `Nonempty`）。
- 会用 `measure_ge_le_exp_cgf`、`iIndepFun.cgf_sum`、`mgf_congr_of_identDistrib` 证明 i.i.d.（独立同分布）
  和的 Chernoff bound（Chernoff 界），并对 `t` 取上确界得到 Cramér 型上界。
- 会用 `integral_bernoulliMeasure` 算出伯努利变量的 `Λ`，并把 `Λ*` 算成
  `a log (a/p) + (1-a) log ((1-a)/(1-p))`。
- 读懂并会写大偏差原理的定义（`IsLDP`：lower semicontinuous（下半连续）的速率函数 + 闭集上界
  + 开集下界，一个字段全是命题的结构体），知道 Mathlib 里哪些零件现成、哪些缺失，
  并能把一个大定理拆成 `[有]`/`[待办]` 的依赖清单。

## 前置知识
第 11 章（`Real.exp`、`Real.log` 与不等式）；第 14 章（`Tendsto`、`limsup`、`sSup`/`iSup` 的垃圾值）；
第 16、17 章（`μ.real`、`HasLaw`、`IdentDistrib`、`iIndepFun`、`Ber(x, y, p)`、`unitInterval`）；
第 21 章（`mgf`、`cgf`、Chernoff 界 `measure_ge_le_exp_cgf`）；第 9、10 章（找引理、`positivity`、
`field_simp`）。第 21 章的结论在用到时重述一次，不再重证。
-/

@[expose] public section

namespace Lean4Learn.Ch22

section Main

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology unitInterval

/-!
## 1. 大偏差问题与速率函数

设 `X₁, X₂, …` 独立同分布，均值 `m`，`S_n = X₁ + ⋯ + X_n`。对 `a > m`，大数定律给出
`P(S_n ≥ n a) → 0`。Chebyshev's inequality（切比雪夫不等式，第 17 章）在方差有限时给出 `O(1/n)`；
若还存在 `t > 0` 使 `𝔼 exp (t X) < ∞`，Chernoff 界（第 21 章）给出形如 `exp (-n c)`、`c > 0` 的速度。
没有指数矩时衰减可以只是多项式的（纸笔推导）：`X ≥ 1` 且 `P(X ≥ x) = x⁻³`，均值 `3/2`、方差有限，
但 `P(S_n ≥ 2n) ≥ P(X₁ ≥ 2n) = (2n)⁻³`。large deviations 理论的中心论断是：指数速度的常数是
**精确**的，即存在速率函数 `I`，使得

    lim (1/n) log P(S_n ≥ n a) = -I(a)        （`a > m`，在适当的正则性条件下）。

rare event（稀有事件）的概率按 `exp (-n I)` 衰减，就是 `I` 作为速率函数的含义。Cramér 定理说 `I` 就是
`Λ(t) = log E exp (t X)` 的 Legendre–Fenchel 变换 `Λ*(a) = sup_t (t a - Λ(t))`；这里 `E exp (t X) = ∞`
时 `Λ(t) = +∞`，那一项是 `-∞`，不起作用。

**记号提醒。** 这里的 `Λ*` 是双边的（`sup` 取遍所有实数 `t`）；从 §3 起本章用的是单边的
`sup_{t ≥ 0}`。对上面这个 `Λ`（允许 `+∞`），二者在 `a ≥ m` 时相等（`m` 为均值），这一步见 §9
第 3 条，本章没有证明；本章的上界定理只需要单边的。

**伯努利分布情形手算。** 设 `P(X_i = 1) = p`，`S_n ~ Bin(n, p)`，`0 < p < a < 1`，则
`P(S_n ≥ n a) = ∑_{k ≥ n a} C(n,k) p^k (1-p)^{n-k}`。右边至多 `n+1` 项，其中 `k = ⌈n a⌉` 附近的项
是最大项（`a > p`）。所以 `(1/n) log P` 与 `(1/n) log` 最大项只差 `(log (n+1))/n → 0`。
Stirling 公式给出 `(1/n) log C(n, ⌈n a⌉) → -a log a - (1-a) log (1-a)`，于是

    (1/n) log [C(n, n a) p^{n a} (1-p)^{n (1-a)}]
        → -a log a - (1-a) log (1-a) + a log p + (1-a) log (1-p)
        = -( a log (a/p) + (1-a) log ((1-a)/(1-p)) ).

因此伯努利分布的速率函数是

    I(a) = a log (a/p) + (1-a) log ((1-a)/(1-p)),

即 `Ber(a)` 相对于 `Ber(p)` 的 relative entropy（相对熵，KL 散度）。这个手算（最大项与 Stirling 公式
两步）只是动机，本章**没有**形式化；本章形式化的是更容易的另一半：上界。

落到数字上：`p = 1/2`、`a = 3/4` 时 `I(a) = (3/4) log 3 - log 2`（约 `0.1308`；小数是手算的近似值，
没有在 Lean 里验证，下面验证的只是闭式）。端点 `a = 1` 时全是正面的概率恰为 `p^n`，速率是
`-log p`，公式里令 `a → 1` 也得到它。
-/

example : (3 / 4 : ℝ) * Real.log ((3 / 4) / (1 / 2))
    + (1 - 3 / 4) * Real.log ((1 - 3 / 4) / (1 - 1 / 2)) = 3 / 4 * Real.log 3 - Real.log 2 := by
  have h1 : ((3 : ℝ) / 4) / (1 / 2) = 3 / 2 := by norm_num
  have h2 : (1 - (3 : ℝ) / 4) / (1 - 1 / 2) = 1 / 2 := by norm_num
  rw [h1, h2, Real.log_div (by norm_num) (by norm_num), one_div, Real.log_inv]
  ring

/-!
## 2. 累积量母函数 `Λ`

第 21 章介绍了 Mathlib 的 moment-generating function（矩母函数）`mgf X μ t = 𝔼 exp (t X)` 与
累积量母函数 `cgf X μ t = log (mgf X μ t)`。它们都是普通的定义，可以用 `rfl` 展开：
-/

section Defs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

example (X : Ω → ℝ) (t : ℝ) : mgf X P t = P[fun ω ↦ Real.exp (t * X ω)] := rfl

example (X : Ω → ℝ) (t : ℝ) : cgf X P t = Real.log (mgf X P t) := rfl

/-!
Chernoff 界（第 21 章）是本章的起点。对 `t ≥ 0`，`P(X ≥ ε) ≤ exp (-t ε + cgf X P t)`；
假设只有 `exp (t X)` 可积（它保证 `mgf` 不是垃圾值）：
-/

example [IsProbabilityMeasure P] {X : Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) (ε : ℝ)
    (h : Integrable (fun ω ↦ Real.exp (t * X ω)) P) :
    P.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε + cgf X P t) := measure_ge_le_exp_cgf ε ht h

/-- 记号上沿用大偏差文献：`Λ(t) = log 𝔼 exp (t X)`。它只是 `cgf` 的别名，
`Λ X P t = cgf X P t` 是 `rfl`。若 `exp (t X)` 不可积，`mgf` 取垃圾值 `0`（积分的约定），
`Λ` 随之取 `Real.log 0 = 0`；所以下面凡需要 `Λ` 取真值（而不是垃圾值）的定理
（`chernoff_iid`、`cramer_upper`……）都带可积性假设。 -/
noncomputable def Λ (X : Ω → ℝ) (P : Measure Ω) (t : ℝ) : ℝ := cgf X P t

example (X : Ω → ℝ) (t : ℝ) : Λ X P t = cgf X P t := rfl

/-- `exp (t X)` 不可积时 `Λ` 是垃圾值：`mgf` 里的积分取 `0`，`log 0 = 0`。 -/
example (X : Ω → ℝ) (t : ℝ) (h : ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) P) :
    Λ X P t = 0 := by
  simp [Λ, cgf, mgf, integral_undef h]

end Defs

/-!
## 3. 单边 Legendre 变换 `Λ*` 与 `iSup` 的垃圾值

按定义 `Λ*(a) = sup_{t ≥ 0} (t a - Λ(t))`。「`t ≥ 0`」这个下标集在 Lean 里有两种写法：

* `⨆ t ≥ 0, (t * a - Λ t)`，即嵌套的 `⨆ t, ⨆ (_ : 0 ≤ t), …`（下面第一个例子验证这个展开）；
* 子类型上的 `⨆ t : {t : ℝ // 0 ≤ t}, …`。

本章用第二种：`ciSup_le`、`le_ciSup` 直接适用于它，族里也没有多余的项。第一种在 `ℝ` 里多出一些项：
当 `0 ≤ t` 不成立时，内层 `iSup` 取在空类型上，而 `ℝ` 里空族的上确界是垃圾值 `0`
（`Real.iSup_of_isEmpty`）。
-/

example (f : ℝ → ℝ) : (⨆ t ≥ 0, f t) = ⨆ t, ⨆ (_ : 0 ≤ t), f t := rfl

example : ⨆ (_ : (0 : ℝ) ≤ -1), (5 : ℝ) = 0 := by
  have : IsEmpty ((0 : ℝ) ≤ -1) := ⟨fun h ↦ by linarith⟩
  exact Real.iSup_of_isEmpty _

/-!
也就是说，嵌套写法把「`t < 0` 的项」都当成值 `0` 并进了外层上确界（两种写法是否总相等，本章没有
证明，也用不到）。

### `iSup` 的三条事实

`ℝ` 不是 complete lattice（完备格）：`iSup` 的行为取决于族是否有上界，这正是第 14 章说的 `sSup`
垃圾值。三条事实，每条配一个例子（第三条的代价见下面的 `Λstar_zero_one`）：
-/

section Sup

variable {ι : Type*} (f : ι → ℝ)

-- 有上界时，每一项都 `≤` 上确界
example (h : BddAbove (Set.range f)) (i : ι) : f i ≤ ⨆ j, f j := le_ciSup h i

-- 上确界 `≤ c` 只需要 `Nonempty`，不需要 `BddAbove`
example [Nonempty ι] (c : ℝ) (h : ∀ i, f i ≤ c) : ⨆ j, f j ≤ c := ciSup_le h

-- 无上界时，`iSup` 是垃圾值 `0`
example (h : ¬ BddAbove (Set.range f)) : ⨆ j, f j = 0 := Real.iSup_of_not_bddAbove h

end Sup

/-!
### 定义 `Λstar`，以及 `Λstar ≥ 0`
-/

section Legendre

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- 单边 Legendre 变换 `Λ*(a) = sup_{t ≥ 0} (t a - Λ(t))`，写成子类型 `{t // 0 ≤ t}` 上的 `iSup`。
这是实数值的 `iSup`：若族无上界，值是垃圾值 `0`（见下面的例子）。 -/
noncomputable def Λstar (X : Ω → ℝ) (P : Measure Ω) (a : ℝ) : ℝ :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ((t : ℝ) * a - Λ X P t)

/-- `Λ*` 总是 `≥ 0`，不论族是否有上界：有上界时取 `t = 0`（`cgf_zero`），无上界时垃圾值本身就是 `0`。 -/
theorem Λstar_nonneg [IsProbabilityMeasure P] (X : Ω → ℝ) (a : ℝ) : 0 ≤ Λstar X P a := by
  by_cases hbdd : BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} ↦ ((t : ℝ) * a - Λ X P t))
  · have h := le_ciSup hbdd (⟨0, le_rfl⟩ : {t : ℝ // 0 ≤ t})
    -- h : 0 * a - Λ X P 0 ≤ ⨆ t, (t * a - Λ X P t)
    simpa [Λstar, Λ, cgf_zero] using h
  · rw [Λstar, Real.iSup_of_not_bddAbove hbdd]

/-!
### 垃圾值的真实代价

取 `X ≡ 0`（常数随机变量）。此时 `Λ(t) = log 1 = 0`，所以 `t * 1 - Λ(t) = t` 在 `t ≥ 0` 上无上界：
数学上 `Λ*(1) = +∞`（对 `n ≥ 1`，事件 `S_n ≥ n` 的概率其实是 `0`）。但实数值的 `Λstar` 给出 `0`。
-/

theorem Λ_zero_variable [IsProbabilityMeasure P] (t : ℝ) : Λ (fun _ : Ω ↦ (0 : ℝ)) P t = 0 := by
  simp [Λ, cgf, mgf]

theorem Λstar_zero_one [IsProbabilityMeasure P] : Λstar (fun _ : Ω ↦ (0 : ℝ)) P 1 = 0 := by
  refine Real.iSup_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  have hnn : 0 ≤ max M 0 + 1 := by have := le_max_right M 0; linarith
  have h := hM ⟨⟨max M 0 + 1, hnn⟩, rfl⟩
  simp only [Λ_zero_variable] at h
  have := le_max_left M 0
  linarith

/-!
### `EReal` 版本

要避免这种静默失败，需要取值于 `EReal`（含 `+∞`）的版本。`legendreE f a = ⨆ t, (t a - f t)` 是
双边的（Cramér 定理的形状），`ΛstarE` 是单边的（对应上面的 `Λstar`）。`EReal` 是完备格，`iSup`
没有垃圾值。但这只修好了**输出端**：输入 `Λ X P t` 在 `exp (t X)` 不可积处仍是垃圾值 `0`
（§2），而真值是 `+∞`。所以 `legendreE (Λ X P)` 只在 `∀ t, exp (t X)` 可积时（例如有界变量，
`integrable_exp_mul_of_mem_Icc`）才是 Cramér 定理的速率函数，`ΛstarE X P` 也只在 `cramer_upper`
的假设（`∀ t ≥ 0` 可积）下才是真正的单边变换。一般情形要把上确界限制在 `integrableExpSet X P`
（使 `exp (t X)` 可积的 `t` 的集合）上，或把域外的 `Λ` 定义为 `+∞`。§5 有一个反例。
-/

example {X : Ω → ℝ} {t : ℝ} (h : t ∈ integrableExpSet X P) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) P := integrable_of_mem_integrableExpSet h

/-- 双边 Legendre 变换，取值于 `EReal`：`sup_{t ∈ ℝ} (t a - f t)`，可以是 `+∞`。`f` 要是处处有限的
真实函数；`f = Λ X P` 时这要求 `∀ t, exp (t X)` 可积（见上文）。 -/
noncomputable def legendreE (f : ℝ → ℝ) (a : ℝ) : EReal :=
  ⨆ t : ℝ, (((t * a - f t : ℝ)) : EReal)

/-- 单边版本：`sup_{t ≥ 0} (t a - Λ(t))`，取值于 `EReal`。 -/
noncomputable def ΛstarE (X : Ω → ℝ) (P : Measure Ω) (a : ℝ) : EReal :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ((((t : ℝ) * a - Λ X P t : ℝ)) : EReal)

theorem ΛstarE_zero_one [IsProbabilityMeasure P] : ΛstarE (fun _ : Ω ↦ (0 : ℝ)) P 1 = ⊤ := by
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  refine lt_of_lt_of_le ?_ (le_iSup _ (⟨max (y + 1) 0, le_max_right _ _⟩ : {t : ℝ // 0 ≤ t}))
  simp only [Λ_zero_variable]
  rw [EReal.coe_lt_coe_iff]
  have := le_max_left (y + 1) 0
  linarith

/-!
同一个 `X ≡ 0`、同一个 `a = 1`：实数版 `Λstar` 是 `0`，`EReal` 版 `ΛstarE` 是 `⊤`。
所以下面的 `cramer_upper`（实数版）在这里只说 `P(S_n ≥ n) ≤ exp 0 = 1`（`n ≥ 1`）——对，但没有信息。
实数版的定理**永远正确**（见证明里没有用 `BddAbove`），只是在族无上界时变弱。
当族有上界时两个版本一致，垃圾值永远不起作用：
-/

theorem ΛstarE_eq_coe (X : Ω → ℝ) (a : ℝ)
    (hb : BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} ↦ ((t : ℝ) * a - Λ X P t))) :
    ΛstarE X P a = (Λstar X P a : EReal) := by
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  exact (Monotone.map_ciSup_of_continuousAt continuous_coe_real_ereal.continuousAt
    EReal.coe_strictMono.monotone hb).symm

/-!
`EReal` 版本还有第二个好处：速率函数必须是下半连续的（§8 解释），而
Legendre 变换是一族连续函数的上确界，`EReal` 里这个性质有现成引理（§8 的末尾证明）。
-/

end Legendre

/-!
## 4. 独立同分布和的 Chernoff 界

目标：对独立同分布的 `X i`、固定 `t ≥ 0`，
`P(S_n ≥ n a) ≤ exp (-(n * (t a - Λ(t))))`，其中 `S_n = ∑_{i<n} X i`。证明有三个零件，每个对应一条
Mathlib 引理：

1. 把 `exp (t X 0)` 的可积性搬到每个 `X i` 上（同分布）；
2. 同分布的变量 `Λ` 相同；
3. 对和 `S_n` 用单变量的 Chernoff 界 `measure_ge_le_exp_cgf`；和的累积量母函数是累积量母函数之和
   （独立：`iIndepFun.cgf_sum`），由第 2 条每项等于 `Λ (X 0)`，共 `n` 项。

**怎样找到这些名字。** 目标是「和的 `cgf` 等于 `cgf` 的和」，按命名规范（结论在前，`_sum` 表示对
`Finset` 求和，第 9 章）猜 `iIndepFun.cgf_sum`，再用
`rg "theorem iIndepFun.cgf_sum" .lake/packages/mathlib/Mathlib` 核对。它的可积性假设
`h_int` 要求每个 `exp (t X i)` 可积；对和本身可积性的需求，同一文件里的
`iIndepFun.integrable_exp_mul_sum` 给出（按同样的办法在 `Probability/Moments/Basic.lean`
附近搜 `integrable_exp_mul`）。
-/

section Chernoff

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- 零件 1：同分布的 `X i` 与 `X 0`，`exp (t X 0)` 可积则 `exp (t X i)` 可积。
`IdentDistrib.comp` 把同分布性推到 `x ↦ exp (t x)` 之下，`IdentDistrib.integrable_iff`
说同分布的两个函数同时可积。 -/
theorem integrable_exp_of_identDistrib {X : ℕ → Ω → ℝ} (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (t : ℝ) (hint : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (i : ℕ) :
    Integrable (fun ω ↦ Real.exp (t * X i ω)) P :=
  ((hid i).comp (u := fun x : ℝ ↦ Real.exp (t * x)) (by fun_prop)).integrable_iff.2 hint

omit [IsProbabilityMeasure P] in
/-- 零件 2：同分布的变量，`Λ` 相同（`mgf_congr_of_identDistrib` 的 `t` 是显式参数）。 -/
theorem Λ_eq_of_identDistrib {X : ℕ → Ω → ℝ} (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (t : ℝ) (i : ℕ) : Λ (X i) P t = Λ (X 0) P t := by
  simp only [Λ, cgf, mgf_congr_of_identDistrib (X i) (X 0) (hid i) t]

/-- Chernoff 界，独立同分布和，固定 `t ≥ 0`。 -/
theorem chernoff_iid {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {t : ℝ} (ht : 0 ≤ t)
    (hint : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (a : ℝ) (n : ℕ) :
    P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-(n * (t * a - Λ (X 0) P t))) := by
  have hint' := integrable_exp_of_identDistrib hid t hint
  -- 零件 3：对 ∑ X i 用单变量的 Chernoff 界
  have h1 := measure_ge_le_exp_cgf (μ := P) (X := ∑ i ∈ Finset.range n, X i) (n * a) ht
    (hind.integrable_exp_mul_sum hm (fun i _ ↦ hint' i))
  -- 和的 cgf = n * Λ (X 0)
  have h2 : cgf (∑ i ∈ Finset.range n, X i) P t = n * Λ (X 0) P t := by
    have h3 : ∀ i ∈ Finset.range n, cgf (X i) P t = cgf (X 0) P t :=
      fun i _ ↦ Λ_eq_of_identDistrib hid t i
    rw [hind.cgf_sum hm (fun i _ ↦ hint' i), Finset.sum_congr rfl h3]
    simp [Λ]
  have e : -(n * (t * a - Λ (X 0) P t))
      = -t * (n * a) + cgf (∑ i ∈ Finset.range n, X i) P t := by
    rw [h2]; ring
  rw [e]
  simpa [Finset.sum_apply] using h1

end Chernoff

/-!
## 5. Cramér 型上界

对每个 `t ≥ 0` 有一个界 `exp (-n (t a - Λ(t)))`；最好的界对应使 `t a - Λ(t)` 最大的 `t`，
即 `Λ*(a)`。严格地说，要证明
`P(S_n ≥ n a) ≤ exp (-n Λ*(a))`，只需对每个 `t`，`t a - Λ(t) ≤ -(1/n) log P(S_n ≥ n a)`，
然后对 `t` 取上确界（`ciSup_le`：只要 `Nonempty`）。分三种情形：

* `n = 0`：事件是整个空间，概率 `≤ 1 = exp 0`；
* `P(S_n ≥ n a) = 0`：右边 `exp` 恒正；
* 否则对 `chernoff_iid` 的两边取对数，整理。

这里需要 `t ≥ 0` 的整个半直线上 `exp (t X 0)` 可积（假设 `hint`）。证明里 `set E : Set Ω := … with hE`
给事件起名 `E`，并把后面出现的同一个集合都替换成 `E`；`hE` 保存定义等式。
-/

section Cramer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Cramér 型上界。** 独立同分布，`exp (t X 0)` 对所有 `t ≥ 0` 可积，则
`P(S_n ≥ n a) ≤ exp (-(n * Λ*(a)))`。证明里没有用 `BddAbove`。 -/
theorem cramer_upper {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (a : ℝ) (n : ℕ) :
    P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-(n * Λstar (X 0) P a)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · calc P.real {ω | ((0 : ℕ) : ℝ) * a ≤ ∑ i ∈ Finset.range 0, X i ω} ≤ 1 := measureReal_le_one
      _ = _ := by simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set E : Set Ω := {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} with hE
  rcases (measureReal_nonneg (μ := P) (s := E)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact (Real.exp_pos _).le
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  -- 每个 t 给出 t a - Λ t ≤ -log P(E) / n
  have key : ∀ t : {t : ℝ // 0 ≤ t}, (t : ℝ) * a - Λ (X 0) P t ≤ -Real.log (P.real E) / n := by
    intro t
    have h := chernoff_iid hm hind hid t.2 (hint t t.2) a n
    have h' := Real.log_le_log hpos h
    rw [Real.log_exp] at h'
    rw [le_div_iff₀ hnR]
    linarith
  have hsup : Λstar (X 0) P a ≤ -Real.log (P.real E) / n := ciSup_le key
  have h3 : (n : ℝ) * Λstar (X 0) P a ≤ -Real.log (P.real E) := by
    rw [le_div_iff₀ hnR] at hsup
    linarith
  calc P.real E = Real.exp (Real.log (P.real E)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

/-- 有界变量（几乎必然落在 `[b, c]`）：可积性假设自动成立
（`integrable_exp_mul_of_mem_Icc` 对任意 `t` 成立）。 -/
theorem cramer_upper_of_mem_Icc {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hid : ∀ i, IdentDistrib (X i) (X 0) P P) {b c : ℝ}
    (hb : ∀ᵐ ω ∂P, X 0 ω ∈ Set.Icc b c) (a : ℝ) (n : ℕ) :
    P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-(n * Λstar (X 0) P a)) :=
  cramer_upper hm hind hid (fun _ _ ↦ integrable_exp_mul_of_mem_Icc (hm 0).aemeasurable hb) a n

/-!
**用到的假设。** `Measurable (X i)`（`iIndepFun.integrable_exp_mul_sum` 要求 `Measurable`，
`AEMeasurable` 版本见『常见错误』2）；`iIndepFun X P`；`IdentDistrib (X i) (X 0)`；
`exp (t X 0)` 的可积性。

**与大偏差原理的关系。** 取 `S_n / n` 的分布 `P.map (S_n / n)` 与半直线 `[a, ∞)`，
上界定理可以写成
`limsup (1/n) log P(S_n / n ≥ a) ≤ -Λ*(a)`，形状与 LDP 对闭集 `[a, ∞)` 的上界相同（LDP 见 §8）。
Cramér 定理的速率函数是双边的 `sup_t (t a - Λ(t))`（`Λ` 允许取 `+∞`，§1）。当 `∀ t, exp (t X 0)`
可积（例如有界变量）时它就是 `legendreE (Λ (X 0) P)`；要把这个界当成它的闭集上界，还差 §9 第 3 条
（`a ≥ m` 时单边等于双边）。没有这个可积性时，`legendreE (Λ (X 0) P)` 可以是错的。
反例（纸笔推导，未形式化）：`X = -Y`，`Y ~ Exp(1)`（密度 `e^{-y}`，`y ≥ 0`），均值 `m = -1`。真实的 `Λ(t) = -log (1 + t)`
（`t > -1`），`t ≤ -1` 时 `Λ(t) = +∞`；但 `cgf` 在 `t ≤ -1` 返回 `0`。取 `a = -1/2 > m`：
真实速率是 `sup_{t > -1} (-t/2 + log (1 + t)) = log 2 - 1/2`（在 `t = 1` 取到），而
`legendreE` 的族含 `t ≤ -1` 的垃圾项 `t a = -t/2 → +∞`，结果是 `⊤`。下面的例子就是这个机制：
每个 `t ∉ integrableExpSet` 都向 `legendreE (Λ X P) a` 贡献垃圾项 `t a`。
-/

omit [IsProbabilityMeasure P] in
example (X : Ω → ℝ) (a t : ℝ) (ht : t ∉ integrableExpSet X P) :
    ((t * a : ℝ) : EReal) ≤ legendreE (Λ X P) a := by
  have h : Λ X P t = 0 := cgf_undef ht
  unfold legendreE
  exact le_iSup_of_le t (by simp [h])

/-!
另外，实数值的 `Λstar` 在族无上界时是垃圾值（§3），那时这个界是空的：§3 的 `X ≡ 0`、`a = 1`
只得到 `≤ 0`，而 LDP 在那里要求 `≤ ⊥`（`ΛstarE = ⊤`），见 §9 第 1 条。
这个重述包含 `EReal` 的乘法、`ENNReal.log`、`limsup`，是本节最复杂的一步：
-/

/-- 大偏差原理的上界，半直线版本：`(1/n) log P(S_n / n ≥ a)` 的上极限 `≤ -Λ*(a)`，右边是实值
`Λstar`，速率为 `+∞` 时这个界太弱。
`ENNReal.log : ℝ≥0∞ → EReal` 把测度值（可以是 `0`，`log 0 = ⊥`）送进 `EReal`。 -/
theorem upper_halfline {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (a : ℝ) :
    limsup (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : EReal) *
      ENNReal.log (P.map (fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) (Set.Ici a))) atTop
      ≤ ((-Λstar (X 0) P a : ℝ) : EReal) := by
  -- `limsup_le_of_le`：只需「最终」每一项 `≤ 右边`；第一个参数是余有界性（cobounded），
  -- 在 `EReal` 这样的完备格里由 `isBoundedDefault` 自动给出
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : Measurable fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω :=
    (Finset.measurable_sum _ fun i _ ↦ hm i).const_mul _
  have hpre : (fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, X i ω) ⁻¹' Set.Ici a
      = {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} := by
    ext ω
    exact le_inv_mul_iff₀ hnR
  rw [Measure.map_apply hS measurableSet_Ici, hpre,
    ← ofReal_measureReal (measure_ne_top P _)]
  have h := cramer_upper hm hind hid hint a n
  have hx : ¬ (Real.exp (-(n * Λstar (X 0) P a)) ≤ 0) := not_le.2 (Real.exp_pos _)
  set E : Set Ω := {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω} with hE
  calc (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (P.real E))
      ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) *
        ENNReal.log (ENNReal.ofReal (Real.exp (-(n * Λstar (X 0) P a)))) :=
        mul_le_mul_of_nonneg_left (ENNReal.log_monotone (ENNReal.ofReal_le_ofReal h))
          (EReal.coe_nonneg.2 (inv_nonneg.2 hnR.le))
    _ = ((-Λstar (X 0) P a : ℝ) : EReal) := by
        rw [ENNReal.log_ofReal]
        -- `ENNReal.log_ofReal` 把 `log (ofReal x)` 写成按 `x ≤ 0` 分情形的 `if`；
        -- `split_ifs` 拆开它，`x ≤ 0` 的分支与 `hx` 矛盾，自动关掉，剩下的分支继续算
        split_ifs
        rw [Real.log_exp, ← EReal.coe_mul]
        exact congrArg (fun r : ℝ ↦ (r : EReal))
          (by rw [mul_neg, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul])

end Cramer

/-!
## 6. 伯努利分布：`Λ` 与 `Λ*` 的闭式

设 `X ~ Ber(1, 0, p)`（以概率 `p` 取 `1`，否则取 `0`；`p : unitInterval`，第 17 章）。则
`mgf X t = p e^t + (1-p)`，`Λ(t) = log (1 - p + p e^t)`。

**Step 1。** `mgf` 的闭式就是第 21 章 §1 的 `mgf_bernoulli`（证明见那里）；本章不导入第 21 章，
所以原样重述。取对数即得 `Λ`。
-/

section Bernoulli

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- 与第 21 章的 `mgf_bernoulli` 相同。 -/
theorem mgf_bernoulli [IsProbabilityMeasure P] {X : Ω → ℝ} (p : unitInterval)
    (hX : HasLaw X Ber(1, 0, p) P) (t : ℝ) :
    mgf X P t = (p : ℝ) * Real.exp t + (1 - (p : ℝ)) := by
  have h := hX.integral_comp (f := fun x : ℝ ↦ Real.exp (t * x)) (by fun_prop)
  rw [integral_bernoulliMeasure] at h
  simpa [mgf, Function.comp_def] using h

theorem Λ_bernoulli [IsProbabilityMeasure P] {X : Ω → ℝ} (p : unitInterval)
    (hX : HasLaw X Ber(1, 0, p) P) (t : ℝ) :
    Λ X P t = Real.log (1 - (p : ℝ) + p * Real.exp t) := by
  rw [Λ, cgf, mgf_bernoulli p hX t, add_comm]

/-- 伯努利变量几乎必然落在 `[0, 1]`：用 `HasLaw.ae_iff` 把「几乎必然」搬到
`Ber(1, 0, p)` 上，再用 `bernoulliMeasure_apply_of_notMem_of_notMem`（不含 `1` 也不含 `0`
的集合测度为 `0`）。 -/
theorem ae_mem_Icc_of_bernoulli {X : Ω → ℝ} (p : unitInterval) (hX : HasLaw X Ber(1, 0, p) P) :
    ∀ᵐ ω ∂P, X ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [hX.ae_iff (p := fun x ↦ x ∈ Set.Icc (0 : ℝ) 1) (measurable_mem.2 measurableSet_Icc),
    ae_iff]
  exact bernoulliMeasure_apply_of_notMem_of_notMem p
    (s := {x : ℝ | ¬ x ∈ Set.Icc (0 : ℝ) 1}) (measurableSet_Icc.compl) (by simp) (by simp)

/-!
### `Λ*` 的闭式与 Cramér 型上界

**Step 2：倾斜的代数。** 目标 `Λ*(a) = a log (a/p) + (1-a) log ((1-a)/(1-p))`。
最优的 `t` 满足 `e^t = q := a (1-p) / (p (1-a))`（令 `t a - Λ(t)` 的导数为零，但我们不用导数）。
代入：`1 - p + p q = (1-p)/(1-a)`，于是
`t a - Λ(t) = a log q - log ((1-p)/(1-a))` 恰好是 `a log (a/p) + (1-a) log ((1-a)/(1-p))`。
`positivity` 在 `0 < a`、`0 < 1 - a` 等作为假设在场时能证明分式为正。
-/

theorem bernoulli_exponent {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 < a) (ha1 : a < 1) :
    Real.log (a * (1 - p) / (p * (1 - a))) * a
        - Real.log (1 - p + p * (a * (1 - p) / (p * (1 - a))))
      = a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  have h1p : 0 < 1 - p := sub_pos.2 hp1
  have h2 : 1 - p + p * (a * (1 - p) / (p * (1 - a))) = (1 - p) / (1 - a) := by
    field_simp
    ring
  rw [h2]
  simp only [Real.log_div ha0.ne' hp0.ne', Real.log_div h1a.ne' h1p.ne',
    Real.log_div h1p.ne' h1a.ne', Real.log_div (mul_pos ha0 h1p).ne' (mul_pos hp0 h1a).ne',
    Real.log_mul ha0.ne' h1p.ne', Real.log_mul hp0.ne' h1a.ne']
  ring

/-!
**Step 3：变分上界。** 对**所有** `t`（不只是最优的），`t a - log (1-p+p e^t)` 不超过
`I(a) := a log (a/p) + (1-a) log ((1-a)/(1-p))`。证明只用 `log x ≤ x - 1`
（`Real.log_le_sub_one_of_pos`）两次，没有微积分；这和证明 Gibbs 不等式（`KL ≥ 0`）
是同一个技巧。它同时给出 `BddAbove`。
-/

theorem bernoulli_rate_le {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) :
    t * a - Real.log (1 - p + p * Real.exp t)
      ≤ a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  have h1p : 0 < 1 - p := sub_pos.2 hp1
  have hE : 0 < Real.exp t := Real.exp_pos t
  -- 给 `1 - p + p e^t` 起名 `Z`，等式保存在 `hZdef`
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = 1 - p + p * Real.exp t := ⟨_, rfl⟩
  have hZ : 0 < Z := by rw [hZdef]; positivity
  have hZne : Z ≠ 0 := hZ.ne'
  have ha' : a ≠ 0 := ha0.ne'
  have h1a' : 1 - a ≠ 0 := h1a.ne'
  rw [← hZdef]
  -- 两次 `log x ≤ x - 1`：x = p e^t / (Z a) 与 x = (1-p) / (Z (1-a))
  have e1 := Real.log_le_sub_one_of_pos (x := p * Real.exp t / (Z * a)) (by positivity)
  have e2 := Real.log_le_sub_one_of_pos (x := (1 - p) / (Z * (1 - a))) (by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hp0.ne' hE.ne', Real.log_exp,
    Real.log_mul hZne ha'] at e1
  rw [Real.log_div h1p.ne' (by positivity), Real.log_mul hZne h1a'] at e2
  have k1 : a * (p * Real.exp t / (Z * a)) = p * Real.exp t / Z := by field_simp
  have k2 : (1 - a) * ((1 - p) / (Z * (1 - a))) = (1 - p) / Z := by field_simp
  have hsum : p * Real.exp t / Z + (1 - p) / Z = 1 := by
    rw [← add_div, div_eq_one_iff_eq hZne, hZdef]; ring
  rw [Real.log_div ha' hp0.ne', Real.log_div h1a' h1p.ne']
  nlinarith [mul_le_mul_of_nonneg_left e1 ha0.le, mul_le_mul_of_nonneg_left e2 h1a.le]

/-- 上确界在 `t* = log (a (1-p) / (p (1-a))) ≥ 0` 处取到。 -/
theorem exists_tilt [IsProbabilityMeasure P] {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X Ber(1, 0, p) P) {a : ℝ} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpa : (p : ℝ) ≤ a) (ha1 : a < 1) :
    ∃ t : ℝ, 0 ≤ t ∧
      t * a - Λ X P t = a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  have ha0 : 0 < a := lt_of_lt_of_le hp0 hpa
  have h1a : 0 < 1 - a := sub_pos.2 ha1
  have h1p : 0 < 1 - (p : ℝ) := sub_pos.2 hp1
  have hq : 0 < a * (1 - p) / (p * (1 - a)) := by positivity
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.log (a * (1 - p) / (p * (1 - a))) := ⟨_, rfl⟩
  have hexp : Real.exp t = a * (1 - p) / (p * (1 - a)) := by rw [htdef, Real.exp_log hq]
  refine ⟨t, ?_, ?_⟩
  · rw [htdef]
    refine Real.log_nonneg ((one_le_div (by positivity)).2 ?_)
    nlinarith
  · rw [← bernoulli_exponent hp0 hp1 ha0 ha1, ← htdef, Λ_bernoulli p hX, hexp]

/-- **伯努利分布的速率函数**（`p ≤ a < 1`）：`Λ*(a) = a log (a/p) + (1-a) log ((1-a)/(1-p))`。
这里 `BddAbove` 是**证明出来的**（变分上界），垃圾值从未被用到。 -/
theorem bernoulli_Λstar [IsProbabilityMeasure P] {X : Ω → ℝ} {p : unitInterval}
    (hX : HasLaw X Ber(1, 0, p) P) {a : ℝ} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hpa : (p : ℝ) ≤ a) (ha1 : a < 1) :
    Λstar X P a = a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  have ha0 : 0 < a := lt_of_lt_of_le hp0 hpa
  have hle : ∀ t : {t : ℝ // 0 ≤ t}, (t : ℝ) * a - Λ X P t
      ≤ a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := fun t ↦ by
    rw [Λ_bernoulli p hX]
    exact bernoulli_rate_le hp0 hp1 ha0 ha1 t
  refine le_antisymm (ciSup_le hle) ?_
  have hbdd : BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} ↦ (t : ℝ) * a - Λ X P t) :=
    ⟨_, by rintro _ ⟨t, rfl⟩; exact hle t⟩
  obtain ⟨t, ht, hteq⟩ := exists_tilt hX hp0 hp1 hpa ha1
  have := le_ciSup hbdd (⟨t, ht⟩ : {t : ℝ // 0 ≤ t})
  rw [Λstar]
  simpa [hteq] using this

/-- **伯努利和的 Cramér 型上界（精确速率函数）**：`0 < p < 1`，`p ≤ a < 1`，
`P(S_n ≥ n a) ≤ exp (-(n * (a log (a/p) + (1-a) log ((1-a)/(1-p)))))`。
为什么要 `p ≤ a`：`a < p` 时事件 `S_n ≥ n a` 的概率趋于 `1`，而 `I(a) > 0`，带 `I(a)` 的界是假的
（此时 `Λ*(a) = 0`，由 Jensen's inequality（琴生不等式），见 §9 第 2 条）。
`a = 1` 是边界情形（§1 末尾的端点），本章不处理。 -/
theorem bernoulli_cramer [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {p : unitInterval}
    (hm : ∀ i, Measurable (X i)) (hX : ∀ i, HasLaw (X i) Ber(1, 0, p) P)
    (hind : iIndepFun X P) {a : ℝ} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hpa : (p : ℝ) ≤ a)
    (ha1 : a < 1) (n : ℕ) :
    P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω}
      ≤ Real.exp (-(n * (a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p))))) := by
  have h := cramer_upper_of_mem_Icc hm hind (fun i ↦ (hX i).identDistrib (hX 0))
    (ae_mem_Icc_of_bernoulli p (hX 0)) a n
  rwa [bernoulli_Λstar (hX 0) hp0 hp1 hpa ha1] at h

end Bernoulli

/-!
## 7. 相对熵与 `klDiv`：Mathlib 的现成零件

`Λ*` 在伯努利情形等于相对熵 `KL(Ber(a) ‖ Ber(p))`（这是我们要说明的事实，本章只证明通向它的
代数，等式本身见本节末尾）。直观理由：最优的 `t*` 恰好把 `Ber(p)` exponentially tilted
（指数倾斜）成均值为 `a` 的伯努利分布，而「倾斜后的分布」相对于原分布的相对熵恰是
`t* a - Λ(t*)`。

Mathlib 里有这条链上的零件（`klDiv`、`Measure.tilted`、倾斜测度的均值是 `cgf` 的导数），
但**没有**把它们连起来的离散闭式。`klDiv` 的值在 `ℝ≥0∞`，用 `irreducible_def` 定义：
这是 Mathlib 提供的命令，生成一个不可展开的常数，并附一条展开用的等式 `klDiv_def`，所以
值只能通过引理（`klDiv_self`、`klDiv_of_not_ac`……）或 `rw [klDiv_def]` 得到。先看现成的零件。
-/

section KL

open InformationTheory
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

-- 指数倾斜：`P.tilted f` 的密度是 `exp (f x) / ∫ exp (f z)`；在 `exp ∘ f` 可积时，
-- 概率测度的倾斜仍是概率测度
example [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Integrable (fun ω ↦ Real.exp (f ω)) P) :
    IsProbabilityMeasure (P.tilted f) := isProbabilityMeasure_tilted hf

-- 倾斜后的均值是 `cgf` 的导数；`t` 在 `integrableExpSet X P`（使 `exp (t X)` 可积的 `t`
-- 的集合）的内部
example {X : Ω → ℝ} {t : ℝ} (ht : t ∈ interior (integrableExpSet X P)) :
    (P.tilted (t * X ·))[X] = deriv (cgf X P) t := integral_tilted_mul_self ht

-- `klDiv` 的基本事实：自己对自己为 `0`
example (μ : Measure Ω) [SigmaFinite μ] : klDiv μ μ = 0 := klDiv_self μ

-- 用 `klDiv_def` 展开（Mathlib 自己证明 `klDiv_of_not_ac` 的写法）
example (μ ν : Measure Ω) (h : ¬ μ ≪ ν) : klDiv μ ν = ∞ := by
  rw [klDiv_def]
  exact ite_eq_right (not_and_of_not_left _ h)

-- `μ ≪ ν` 且总质量相等时，`toReal` 后等于对数似然比 `llr` 的积分，不带可积性假设
example {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν)
    (h_eq : μ Set.univ = ν Set.univ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ := toReal_klDiv_of_measure_eq h h_eq

-- 但 `llr` 不可积时 `klDiv = ∞`，`toReal ∞ = 0`，右边的积分也是垃圾值 `0`：上式退化为 `0 = 0`
-- （Mathlib 的证明就是这样分情况的）。要真正的积分表示，还要 `Integrable (llr μ ν) μ`
-- （`toReal_klDiv`）
example {μ ν : Measure Ω} (h : ¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞ :=
  klDiv_of_not_integrable h

#guard_msgs (drop info) in
#check @toReal_klDiv

/-!
伯努利速率函数与 Mathlib 的 `klFun x = x log x + 1 - x`（`klDiv` 的积分表示里出现的凸函数）
的联系是纯代数：`I(a) = p · klFun (a/p) + (1-p) · klFun ((1-a)/(1-p))`。
-/

example {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p))
      = p * klFun (a / p) + (1 - p) * klFun ((1 - a) / (1 - p)) := by
  have h1p : 1 - p ≠ 0 := (sub_pos.2 hp1).ne'
  unfold klFun
  field_simp
  ring

/-!
**未证明的部分（明确标注）。** 等式
`(klDiv Ber(1,0,a) Ber(1,0,p)).toReal = a log (a/p) + (1-a) log ((1-a)/(1-p))`
本章**没有证明**。设想的路线（没有编译过，只是计划）：证明
`Ber(1,0,a) = Ber(1,0,p).tilted (fun x ↦ t* * x)`（`x` 的四种隶属情形逐一验证）；
再用 `log_rnDeriv_tilted_left_self` 得 `llr (Ber a) (Ber p) =ᵐ[Ber p] t* x - log Z`，
`toReal_klDiv_of_measure_eq` 化为积分，最后 `integral_bernoulliMeasure`。量级大约一百行。

倾斜测度的均值公式（上面第二个例子）才是 Cramér 下界证明的关键：选 `t*` 使倾斜后的均值恰好等于
`a`，在倾斜测度下 `S_n ≈ n a` 是典型事件，再把概率换回原测度，代价正好是 `exp (-n Λ*(a))`。
-/

end KL

/-!
## 8. 什么是大偏差原理

测度序列 `μ_n`（比如 `μ_n = S_n / n` 的分布）满足 large deviation principle（大偏差原理，LDP），
以 `n` 为 speed（速度）、以 `I` 为速率函数，若：

1. `I` 取值于 `[0, +∞]` 且下半连续；
2. **闭集上界**：对每个闭集 `F`，`limsup (1/n) log μ_n(F) ≤ -inf_F I`；
3. **开集下界**：对每个开集 `G`，`liminf (1/n) log μ_n(G) ≥ -inf_G I`。

下半连续在 Mathlib 里是 `LowerSemicontinuous`，定义是：对每个点 `x` 和每个 `y < f x`，在 `x`
附近 `y < f x'` 最终成立。在全序的目标空间里，它等价于每个水平集 `{f ≤ y}` 是闭集：
-/

example {α γ : Type*} [TopologicalSpace α] [LinearOrder γ] (f : α → γ) :
    LowerSemicontinuous f ↔ ∀ x, ∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x' := Iff.rfl

example {α γ : Type*} [TopologicalSpace α] [LinearOrder γ] (f : α → γ) :
    LowerSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Set.Iic y) :=
  lowerSemicontinuous_iff_isClosed_preimage

/-!
若水平集还是紧的，`I` 称 good rate function（好速率函数）。在 Lean 里，`log μ_n(F)` 要用
`ENNReal.log : ℝ≥0∞ → EReal`（`log 0 = ⊥`），`I` 取值于 `EReal`，`limsup`/`liminf`/`iInf` 都在完备格
`EReal` 里，不需要 `BddAbove` 的补丁。下面的定义没有出现在 Mathlib 里（见本节末的表），
是本书为了讲清楚而写的。它是一个 `structure … : Prop`：四个字段 `nonneg`、`lsc`、`upper`、`lower`
的类型都是命题，所以 `IsLDP μ J` 是命题，构造它要同时给出四个证明（`structure` 见第 6 章）。
代码里速率函数记作 `J`：`open scoped unitInterval`（第 17 章）之后 `I` 是 `unitInterval`
的记号，为避免与它混淆，改用 `J`：
-/

example : I = unitInterval := rfl

section LDP

/-- 大偏差原理（speed 为 `n`）：速率函数 `J : E → EReal` 非负、下半连续，且闭集上界与开集下界成立。 -/
structure IsLDP {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure E) (J : E → EReal) : Prop where
  nonneg : ∀ x, 0 ≤ J x
  lsc : LowerSemicontinuous J
  upper : ∀ F : Set E, IsClosed F →
    limsup (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (μ n F)) atTop ≤ -⨅ x ∈ F, J x
  lower : ∀ G : Set E, IsOpen G →
    -⨅ x ∈ G, J x ≤ liminf (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (μ n G)) atTop

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : ℕ → Measure E} {J : E → EReal}

-- 下半连续 ⇒ 水平集是闭集（`LowerSemicontinuous.isClosed_preimage`）
example (h : IsLDP μ J) (c : EReal) : IsClosed (J ⁻¹' Set.Iic c) := h.lsc.isClosed_preimage c

end LDP

/-!
**Legendre 变换的下半连续。** 速率函数必须下半连续。`lowerSemicontinuous_iSup` 要求值域是
complete linear order（完备全序，`CompleteLinearOrder`）：`ℝ` 不满足，`EReal` 满足（`ℝ` 只有带
`BddAbove` 假设的 `lowerSemicontinuous_ciSup`，失败的实例见『常见错误』1）。这是本章用 `EReal`
版本的第二个理由。每一项 `a ↦ t * a - f t` 连续，所以对任意 `f`（同样的证明对只取遍一部分 `t`
的上确界也适用，例如 `ΛstarE` 或 `integrableExpSet` 上的上确界；这一点未编译）：
-/

theorem lowerSemicontinuous_legendreE (f : ℝ → ℝ) : LowerSemicontinuous (legendreE f) := by
  unfold legendreE
  exact lowerSemicontinuous_iSup fun t ↦
    (continuous_coe_real_ereal.comp (by fun_prop : Continuous fun a : ℝ ↦ t * a - f t)
      ).lowerSemicontinuous

/-!
### Mathlib 里有什么、没有什么

下面的结论来自对本地 Mathlib（`v4.35.0`）源码的 `rg` 搜索。「无」只表示命令没有命中，不是证明；
Mathlib 更新后请重新搜索。表里的路径都在 `Mathlib/` 下。

| 对象 | 状态 | 位置 |
|---|---|---|
| Chernoff 界、`mgf`/`cgf`、独立和 | 有 | `Probability/Moments/Basic.lean` |
| 次高斯与 Hoeffding | 有 | `Probability/Moments/SubGaussian.lean`（第 21 章） |
| 倾斜测度，倾斜后均值/方差是 `cgf` 的导数 | 有 | `{MeasureTheory/Measure,Probability/Moments}/Tilted.lean` |
| `cgf` 的解析性与导数 | 有 | `Probability/Moments/MGFAnalytic.lean` |
| 相对熵 `klDiv`，链式法则，数据处理 | 有 | `InformationTheory/KullbackLeibler/` 下三个文件 |
| `LowerSemicontinuous`，`iSup` 的下半连续 | 有 | `Topology/Semicontinuity/Basic.lean` |
| 强大数定律、中心极限定理 | 有 | `Probability/StrongLaw.lean`；`Probability/CentralLimitTheorem.lean` |
| Cramér、Sanov、Gärtner–Ellis、Varadhan 引理、LDP 的定义 | **无** | 搜索 (1) 只命中无关文件 |
| Legendre–Fenchel 变换（凸共轭） | **无** | 搜索 (2) 无命中 |
| `cgf` 的凸性 | **无**（有二阶导判别法，可自证） | `Analysis/Convex/Deriv.lean` |
| 任意个仿射函数之上确界的凸性 | **无**（仅二元的 `ConvexOn.sup`） | `Analysis/Convex/Function.lean` |
| 倾斜与乘积交换；`klDiv` 对 `Measure.pi` 张量化 | **无**（仅二元 `klDiv_compProd_eq_add`） | `…/ChainRule.lean` |
| `klDiv` 的离散/伯努利闭式 | **无** | 搜索 (3)：`klDiv` 只在上面三个文件里出现 |

```
(1) rg -il "cram[eé]r|large deviation|sanov|gärtner" .lake/packages/mathlib/Mathlib
(2) rg -il "fenchel|convex conjugate|legendre transform" .lake/packages/mathlib/Mathlib
(3) rg -l klDiv .lake/packages/mathlib/Mathlib
```

(1) 命中的文件是：`Probability/CramerWold.lean`（Cramér–Wold 技巧）、一批矩阵与环论文件（Cramer 法则、
判别式）和 `Geometry/Convex/Cone/Basic.lean`（一条以 Gärtner 为作者之一的书目引用，与
Gärtner–Ellis 定理无关）；没有 LDP 相关的文件。

## 9. 规划：把 Cramér 定理形式化需要什么

下面是一份 blueprint 风格的依赖列表（工作流见第 23 章）。每一行是一个**可以单独陈述、单独证明的
引理**；`[有]` 是本章或 Mathlib 已有，`[待办]` 是没有证明的。没有给出行数估计：除第 1 条外
都没有写过，估计不可靠。**范围**：下面按大纲的有界情形写，即 `∀ t, exp (t X)` 可积，此时速率函数
就是 `legendreE (Λ X P)`（§3、§5）；一般情形要把每处上确界限制在 `integrableExpSet` 上。

1. **半直线上界**。实值版 `[有]`：`upper_halfline`（Chernoff + `ciSup_le`），右边是实值 `Λstar`。
   `EReal` 版 `limsup ≤ -ΛstarE(a)` `[待办]`：它多出速率为 `+∞` 的分支（§3 的 `X ≡ 0`、`a = 1`：
   `Λstar = 0` 只给出 `≤ 0`，LDP 要 `≤ ⊥`），要对每个 `t` 用 Chernoff 界，再让 `t a - Λ(t) → +∞`。
2. **`Λ` 的凸性与 `Λ*(m) = 0`** `[待办]`：`Λ` 在可积集内部二阶可导（`iteratedDeriv_two_cgf`、
   `variance_tilted_mul`），用 `convexOn_of_deriv2_nonneg'` 得凸性；对 `exp (t X)` 可积的 `t`，
   琴生不等式（`ConvexOn.map_integral_le`）给 `Λ(t) ≥ t m`，于是 `Λ*(m) = 0`（后一步是练习 22.15）。
3. **单边与双边的 Legendre 变换在 `a ≥ m` 处一致** `[待办]`：对 `t < 0`，`t a ≤ t m ≤ Λ(t)`
   （第 2 条的琴生不等式，要求 `exp (t X)` 可积），故 `t a - Λ(t) ≤ 0 ≤` 单边的 `Λ*(a)`。
   不可积的 `t` 上真实的 `Λ(t) = +∞`，该项也不起作用，但 `legendreE (Λ X P)` 在那里得到垃圾项
   `t a`（§5 的反例），所以这一条要么假设处处可积，要么改用 `integrableExpSet` 上的上确界。
4. **闭集上界** `[待办]`：分情况。`F = ∅` 时右边是 `-⊤ = ⊥`，左边 `log 0 = ⊥`；`m ∈ F` 时
   `inf_F I = I(m) = 0`，概率 `≤ 1` 即得。否则令 `F₊ = F ∩ [m, ∞)`、`F₋ = F ∩ (-∞, m]`：非空的
   一侧有最近点（`y = min F₊ > m` 或 `x = max F₋ < m`，闭集），`F₊ ⊆ [y, ∞)`，用 1 的 `EReal` 版
   （下侧用练习 22.10 的下尾版本）与 `Λ*` 在 `[m, ∞)` 上单调（来自 2）；只有一侧非空就到此为止，
   两侧都非空再用联合界 `μ_n(F) ≤ 2 max (μ_n(F₋), μ_n(F₊))`。
5. **好速率函数** `[待办]`：`Λ*` 下半连续 `[有]`（`lowerSemicontinuous_legendreE`，对任意 `f`）；
   水平集紧需要 `Λ` 在 `0` 附近有限，从而 `Λ*(a) ≥ δ|a| - C`。
6. **倾斜测度的乘积** `[待办]`：`Measure.pi (fun _ ↦ μ.tilted f) = (Measure.pi (fun _ ↦ μ)).tilted (∑ f)`，
   Mathlib 没有，要从 cylinder set（柱集）上的 `Measure.infinitePi_pi` 与 `tilted_apply'` 证明。
7. **换测度恒等式** `[待办]`：`P(S_n ∈ A) = E_t[ exp (-t S_n + n Λ(t)) 1_A ]`；
   零件 `llr_tilted_left`、`log_rnDeriv_tilted_left_self` 已有。
8. **存在 `t*` 使倾斜均值 = `a`** `[待办]`：`Λ'` 的值域；`analyticAt_cgf`、`deriv_cgf` 已有，
   需要严格凸性与边界情形（`a` 在支撑的端点，`Λ*(a)` 为 `+∞` 或极限值）。
9. **倾斜测度下的大数定律** `[待办]`：`strong_law_ae_real` 已有，只需验证它的假设（独立、同分布、可积）
   在倾斜测度下成立；方差有限则用 `variance_tilted_mul` 与切比雪夫即可。
10. **开集下界** `[待办]`：由 6–9 与 `Λ*` 的连续性在定义域内部，是整个项目最难的一步。
11. **打包为 `IsLDP`** `[待办]`：用本章的 `IsLDP`、上面范围内的速率函数，加上 4、10，以及 `Λ*`
    非负（`Λstar_nonneg` 的 `EReal` 版本，练习 22.14）。
12. **伯努利分布的下界（手算里的最大项与 Stirling 公式）** `[待办]`：§1 的手算只是动机；
    若要得到伯努利情形的 `lim (1/n) log P(S_n ≥ n a)`，需要二项系数的 Stirling 估计。

据本书的判断（未验证），第 6 条（倾斜的乘积）是 Cramér 下界最大的缺口。上面标 `[有]` 的 Mathlib
名字都在下面的 `#check` 里检查过：它们在当前导入下存在（`(drop info)` 丢掉 `#check` 的输出，
所以编译不产生任何信息）。
-/

#guard_msgs (drop info) in
#check And.intro (@iteratedDeriv_two_cgf) <| And.intro (@variance_tilted_mul) <|
  And.intro (@convexOn_of_deriv2_nonneg') <| And.intro (@ConvexOn.map_integral_le) <|
  And.intro (@analyticAt_cgf) <| And.intro (@deriv_cgf) <| And.intro (@strong_law_ae_real) <|
  And.intro (@llr_tilted_left) <| And.intro (@log_rnDeriv_tilted_left_self) <|
  And.intro (@Measure.infinitePi_pi) (@tilted_apply')


/-!
## 常见错误

**1. 把实数 `iSup` 当成完备格里的 `iSup`。** `lowerSemicontinuous_iSup` 要求值域是
`CompleteLinearOrder`（完备全序）；`ℝ` 不是（`ℝ` 上的 `⨆` 来自 `Real.instSupSet`，只是
`ConditionallyCompleteLinearOrder` 的 `iSup`）。对实数值族直接用，报的是 `Type mismatch`，
信息不算清楚。线索在 `Note:` 里提到的 `Real.instLT`、`Real.instLE`：引理需要的序结构在 `ℝ` 上合成
不出来，两边的 `LT`/`LE` 实例对不上（这是对报错的解读，编译器没有直接说出原因）。补救：值域换成
`EReal`（本章的 `legendreE`、`ΛstarE`），或者用 `lowerSemicontinuous_ciSup` 并提供 `BddAbove`：
-/

set_option pp.mvars false in
/--
error: Type mismatch
  lowerSemicontinuous_iSup ?_
has type
  LowerSemicontinuous fun x' ↦ ⨆ i, ?_ i x'
but is expected to have type
  LowerSemicontinuous fun x ↦ ⨆ i, f i x

Note: The following definitions were not unfolded because their definition is not exposed:
  Real.instLT ↦ 5
  Real.instLE ↦ 6
-/
#guard_msgs in
example (f : ℕ → ℝ → ℝ) (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x ↦ ⨆ i, f i x := lowerSemicontinuous_iSup h

-- 补救：提供 `BddAbove`
example (f : ℕ → ℝ → ℝ) (h : ∀ i, LowerSemicontinuous (f i))
    (bdd : ∀ x, BddAbove (Set.range fun i ↦ f i x)) :
    LowerSemicontinuous fun x ↦ ⨆ i, f i x := lowerSemicontinuous_ciSup bdd h

/-!
**2. 把 `AEMeasurable` 交给要 `Measurable` 的引理。** `iIndepFun.integrable_exp_mul_sum` 要求每个
`X i` `Measurable`；Mathlib 里没有它的 `₀` 版本（`rg` 只找到这一个名字），所以 `chernoff_iid`
保留了 `Measurable` 假设：
-/

set_option pp.mvars false in
/--
error: Application type mismatch: The argument
  hm
has type
  ∀ (i : ℕ), AEMeasurable (X i) P
but is expected to have type
  ∀ (i : ℕ), Measurable (X i)
in the application
  @iIndepFun.integrable_exp_mul_sum Ω ℕ inst✝¹ P ?_ ?_ X hind hm
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hm : ∀ i, AEMeasurable (X i) P) (hind : iIndepFun X P) (t : ℝ) (n : ℕ)
    (hint : ∀ i, Integrable (fun ω ↦ Real.exp (t * X i ω)) P) :
    Integrable (fun ω ↦ Real.exp (t * (∑ i ∈ Finset.range n, X i) ω)) P :=
  hind.integrable_exp_mul_sum hm (fun i _ ↦ hint i)

/-!
和的 `cgf` 那一步则有几乎处处可测的版本 `iIndepFun.cgf_sum₀`。后缀 `₀` 在测度论引理里常表示
`AEMeasurable` 版本（第 16 章的 `Measure.map_apply₀`，第 21 章的 `mgf_sum₀`）；在代数里同一个后缀
表示 `GroupWithZero` 版本（第 9 章）：
-/

example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} (hm : ∀ i, AEMeasurable (X i) P) (hind : iIndepFun X P) (t : ℝ) (n : ℕ)
    (hint : ∀ i, Integrable (fun ω ↦ Real.exp (t * X i ω)) P) :
    cgf (∑ i ∈ Finset.range n, X i) P t = ∑ i ∈ Finset.range n, cgf (X i) P t :=
  hind.cgf_sum₀ hm (fun i _ ↦ hint i)

/-!
**3. 忘了概率测度假设。** `Λstar_nonneg` 用到 `cgf_zero`。`cgf_zero` 本身只要求
`IsZeroOrProbabilityMeasure`（所以 `P = 0` 时也成立）；对一般测度，`cgf_zero'` 给出
`Λ X P 0 = log (P.real univ)`，不一定是 `0`：
-/

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) :
    Λ X P 0 = Real.log (P.real Set.univ) := cgf_zero'

/-!
于是 `Λstar_nonneg` 的结论对一般测度真的可能为假。反例：`P.real univ = 2`，`X ≡ 0`，`a = 0`，
此时每一项都是 `t * 0 - log 2 = -log 2`，`Λstar = -log 2 < 0`：
-/

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h2 : P.real Set.univ = 2) :
    Λstar (fun _ : Ω ↦ (0 : ℝ)) P 0 < 0 := by
  have hΛ : ∀ t : {t : ℝ // 0 ≤ t}, ((t : ℝ) * 0 - Λ (fun _ : Ω ↦ (0 : ℝ)) P t) = -Real.log 2 := by
    intro t
    simp [Λ, cgf, mgf, h2]
  have : Nonempty {t : ℝ // 0 ≤ t} := ⟨⟨0, le_rfl⟩⟩
  simp only [Λstar, hΛ, ciSup_const]
  linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-!
没有 `IsProbabilityMeasure P` 时，`Λstar_nonneg` 的使用报在实例合成这一步；补上实例即可：
-/

set_option pp.mvars false in
/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure P

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (a : ℝ) :
    0 ≤ Λstar X P a := Λstar_nonneg X a

example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (a : ℝ) : 0 ≤ Λstar X P a := Λstar_nonneg X a

/-!
**4. 想对 `klDiv` 用 `rfl`。** `rfl` 算不出 `klDiv μ μ = 0`：`klDiv` 用 `irreducible_def` 定义（§7），
值里还有一个要先判定条件的 `if`。正确做法是用引理（`klDiv_self`、`klDiv_of_not_ac`、
`toReal_klDiv_of_measure_eq`……）或 `rw [klDiv_def]`（§7 的例子）：
-/

set_option pp.mvars false in
/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  InformationTheory.klDiv μ μ = 0
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] :
    InformationTheory.klDiv μ μ = 0 := rfl

/-!
## 练习

练习 22.1、22.3 是 `Λ` 的基本性质（第 21 章的 `cgf`）；22.4、22.6 回到第 14 章（`Tendsto`、
`BddAbove` 与 `iSup` 的垃圾值）；22.7 回到第 17 章（`HasLaw`、`integral_bernoulliMeasure`）；
22.8 回到第 11 章（`Real.log` 的代数）；22.13 回到第 16 章（概率测度的值 `≤ 1`）。
其余是本章的 guided project：22.2 是 `upper_halfline` 的最后一步，22.5 用 `cramer_upper`，
22.9 用伯努利一节的引理，22.10 是 Cramér 型上界的下尾版本（§9 第 4 条用到），22.11 读 `IsLDP` 的
定义，22.12、22.14 与垃圾值有关，22.15 是 §9 第 2 条的一步。练习中出现的 `Λ`、`Λstar`、`ΛstarE`、
`IsLDP` 是本章定义的。
-/

section Exercises

/-- 练习 22.1（★）：`Λ(0) = 0`；用 `cgf_zero`（它要求 `IsZeroOrProbabilityMeasure`，概率测度满足）。 -/
theorem ex_22_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) : Λ X P 0 = 0 := by
  sorry

/-- 练习 22.2（★★）：`upper_halfline` 的最后一步。`n > 0` 时，在 `EReal` 里
`(1/n) · log (ofReal (exp (-(n c)))) = -c`；用 `ENNReal.log_ofReal`、`split_ifs`
（`exp` 为正，`≤ 0` 的分支自己关掉）、`Real.log_exp`、`EReal.coe_mul` 与 `inv_mul_cancel₀`。 -/
theorem ex_22_2 (c : ℝ) {n : ℕ} (hn : 0 < n) :
    (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (-(n * c))))
      = ((-c : ℝ) : EReal) := by
  sorry

/-- 练习 22.3（★★）：缩放。`Λ_{cX}(t) = Λ_X(c t)`；展开定义，积分号下的函数相等
（`t * (c * X ω) = c * t * X ω`，`ring`）。 -/
theorem ex_22_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (c t : ℝ) :
    Λ (fun ω ↦ c * X ω) P t = Λ X P (c * t) := by
  sorry

/-- 练习 22.4（★★）：速率 `c > 0` 时 `exp (-(n c)) → 0`；用
`Real.tendsto_exp_neg_atTop_nhds_zero`、`tendsto_natCast_atTop_atTop` 与
`Filter.Tendsto.atTop_mul_const`，再 `Tendsto.comp`。 -/
theorem ex_22_4 (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-(n * c))) atTop (𝓝 0) := by
  sorry

/-- 练习 22.5（★★）：Cramér 型上界蕴含指数衰减。若 `Λ*(a) > 0`，则
`P(S_n ≥ n a) → 0`；用 `cramer_upper`、练习 22.4 的结论，以及夹逼的特例 `squeeze_zero`
（夹逼见第 14 章；第 17 章用过带撇的 `squeeze_zero'`）。 -/
theorem ex_22_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P) (a : ℝ)
    (ha : 0 < Λstar (X 0) P a) :
    Tendsto (fun n : ℕ ↦ P.real {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω}) atTop (𝓝 0) := by
  sorry

/-- 练习 22.6（★★）：`Λ*` 关于 `a` 单调，但需要 `BddAbove`；用 `ciSup_mono`（它要右边的族有上界；
该引理在本题里第一次出现，位于 `Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`）。
没有 `BddAbove` 时右边的 `Λstar` 是垃圾值 `0`（§3），所以必须假设 `hb`。 -/
theorem ex_22_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) {a b : ℝ}
    (hab : a ≤ b)
    (hb : BddAbove (Set.range fun t : {t : ℝ // 0 ≤ t} ↦ ((t : ℝ) * b - Λ X P t))) :
    Λstar X P a ≤ Λstar X P b := by
  sorry

/-- 练习 22.7（★）：取值 `±1` 的伯努利变量（`Ber(1, -1, p)`）的矩母函数：
`mgf X P t = p e^t + (1-p) e^{-t}`；仿照 `mgf_bernoulli`：`HasLaw.integral_comp`、
`integral_bernoulliMeasure`，再 `simpa`。 -/
theorem ex_22_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (p : unitInterval) (hX : HasLaw X Ber(1, -1, p) P) (t : ℝ) :
    mgf X P t = (p : ℝ) * Real.exp t + (1 - (p : ℝ)) * Real.exp (-t) := by
  sorry

/-- 练习 22.8（★★）：`p = 1/2` 时的速率函数：
`I(a) = log 2 + a log a + (1-a) log (1-a)`；提示：`a / (1/2) = a * 2`，再用 `Real.log_mul`。 -/
theorem ex_22_8 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    a * Real.log (a / (1 / 2)) + (1 - a) * Real.log ((1 - a) / (1 - 1 / 2))
      = Real.log 2 + a * Real.log a + (1 - a) * Real.log (1 - a) := by
  sorry

/-- 练习 22.9（★）：相对熵非负。用 `bernoulli_rate_le` 在 `t = 0` 处的特例。 -/
theorem ex_22_9 {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ha0 : 0 < a) (ha1 : a < 1) :
    0 ≤ a * Real.log (a / p) + (1 - a) * Real.log ((1 - a) / (1 - p)) := by
  sorry

/-- 练习 22.10（★★★）：下尾。对 `[0,1]` 值的独立同分布变量，
`P(S_n ≤ n a) ≤ exp (-(n * Λ*_{-X}(-a)))`。把 `X i` 换成 `-X i`，用
`cramer_upper_of_mem_Icc`（区间 `[-1, 0]`）；独立性与同分布性用 `iIndepFun.comp` 与
`IdentDistrib.comp` 搬运；事件的等式用 `Finset.sum_neg_distrib`。 -/
theorem ex_22_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P) (hb : ∀ᵐ ω ∂P, X 0 ω ∈ Set.Icc (0 : ℝ) 1)
    (a : ℝ) (n : ℕ) :
    P.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ n * a}
      ≤ Real.exp (-(n * Λstar (fun ω ↦ -X 0 ω) P (-a))) := by
  sorry

/-- 练习 22.11（★★）：读 `IsLDP` 的定义。若 `μ` 满足速率函数为 `J` 的 LDP，`G` 是开集，`x ∈ G`，
则 `-J x ≤ liminf (1/n) log μ_n(G)`。用字段 `IsLDP.lower`、`EReal.neg_le_neg_iff` 与 `iInf₂_le`。 -/
theorem ex_22_11 {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure E} {J : E → EReal} (h : IsLDP μ J) {G : Set E} (hG : IsOpen G) {x : E}
    (hx : x ∈ G) :
    -J x ≤ liminf (fun n : ℕ ↦ (((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (μ n G)) atTop := by
  sorry

/-- 练习 22.12（★★）：常数 `0` 的 `Λ*` 在 `a ≤ 0` 时是 `0`（与 `a = 1` 时的垃圾值 `0`
对照：这里 `0` 是对的）；`le_antisymm`，`ciSup_le` 与 `Λstar_nonneg`。 -/
theorem ex_22_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {a : ℝ} (ha : a ≤ 0) : Λstar (fun _ : Ω ↦ (0 : ℝ)) P a = 0 := by
  sorry

/-- 练习 22.13（★）：概率测度下 `ENNReal.log (μ s) ≤ 0`；用 `ENNReal.log_le_zero_iff` 与
`prob_le_one`。 -/
theorem ex_22_13 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Set Ω) : ENNReal.log (μ s) ≤ 0 := by
  sorry

/-- 练习 22.14（★）：`EReal` 版本的 `Λstar_nonneg`：`0 ≤ ΛstarE X P a`，对一切 `a`
（不需要 `BddAbove`）。用 `le_iSup_of_le` 取 `t = 0`。 -/
theorem ex_22_14 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (a : ℝ) : 0 ≤ ΛstarE X P a := by
  sorry

/-- 练习 22.15（★★★）：`Λ*(m) = 0`，其中 `m = 𝔼 X`（§9 第 2 条的一步）。分两步：
(1) 琴生不等式给出 `t * 𝔼 X ≤ Λ(t)`：`ConvexOn.map_integral_le` 配 `convexOn_exp`，再取
`Real.log`，积分号外提用 `integral_const_mul`；(2) `le_antisymm`，`ciSup_le` 与 `Λstar_nonneg`。 -/
theorem ex_22_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun ω ↦ Real.exp (t * X ω)) P) :
    Λstar X P (P[X]) = 0 := by
  sorry

end Exercises

/-!
## 小结

| 概念 | 语法 / 名字 | 何时用 |
|---|---|---|
| 累积量母函数 | `cgf X P t`；本章别名 `Λ X P t` | 要 `Λ` 取真值就带可积性假设，否则是垃圾值 `0` |
| 单边 Legendre 变换 | `Λstar X P a := ⨆ t : {t // 0 ≤ t}, (t * a - Λ X P t)` | 上界定理；族无上界时是垃圾值 `0` |
| `iSup` 引理 | `le_ciSup`、`ciSup_le`、`ciSup_mono`、`Real.iSup_of_not_bddAbove` | 证 `⨆ ≤ c` 无需上界 |
| `EReal` 版本 | `legendreE`、`ΛstarE`；`ΛstarE_eq_coe` | 要 `+∞` 或下半连续；输入 `Λ` 仍需可积 |
| 可积集 | `integrableExpSet X P` | 一般情形的 Legendre 变换只取遍它 |
| Chernoff（i.i.d.） | `chernoff_iid` | 固定 `t ≥ 0` 的指数界 |
| Cramér 型上界 | `cramer_upper`、`cramer_upper_of_mem_Icc` | 想要 `exp (-n Λ*(a))` 型的尾界 |
| 半直线上界 | `upper_halfline`（`ENNReal.log`、`limsup`、`EReal`） | 想把上界写成 LDP 的形状 |
| 伯努利分布 | `mgf_bernoulli`、`bernoulli_rate_le`、`bernoulli_Λstar`、`bernoulli_cramer` | 想要显式的速率函数 |
| 大偏差原理 | `IsLDP`（本章定义，Mathlib 无）、`LowerSemicontinuous.isClosed_preimage` | 要陈述或使用 LDP |
| 现成零件 | `Measure.tilted`、`integral_tilted_mul_self`、`klDiv_self`、`klDiv_def` | 倾斜与相对熵 |
| Mathlib 缺失 | Cramér/Sanov/Gärtner–Ellis、Legendre 变换、倾斜的乘积、`klDiv` 张量化 | 规划项目时查 §9 的清单 |
-/

/-!
## 延伸阅读

- 本章的 Mathlib 来源：`Mathlib/Probability/Moments/Basic.lean`（`mgf`、`cgf`、
  `measure_ge_le_exp_cgf`、`iIndepFun.cgf_sum`、`mgf_congr_of_identDistrib`、
  `integrable_exp_mul_of_mem_Icc`）；`Mathlib/Probability/Distributions/Bernoulli.lean`
  （`integral_bernoulliMeasure`、`bernoulliMeasure_apply_of_notMem_of_notMem`）。
- 倾斜与相对熵：`Mathlib/MeasureTheory/Measure/Tilted.lean`、
  `Mathlib/Probability/Moments/Tilted.lean`（`integral_tilted_mul_self`、`variance_tilted_mul`）、
  `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean`、
  `Mathlib/InformationTheory/KullbackLeibler/{KLFun,Basic,ChainRule,DataProcessing}.lean`。
- 序与上确界：`Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean`（`ciSup_le`、`le_ciSup`、
  `ciSup_mono`）、`Mathlib/Algebra/Order/Archimedean/Real/Basic.lean`（`Real.iSup_of_not_bddAbove`、
  `Real.iSup_of_isEmpty`）；半连续：`Mathlib/Topology/Semicontinuity/Basic.lean`；
  `EReal`：`Mathlib/Data/EReal/Basic.lean`、`Mathlib/Analysis/SpecialFunctions/Log/ENNRealLog.lean`。
- Cramér 定理与 LDP 的数学：Dembo–Zeitouni, *Large Deviations Techniques and Applications*,
  Cramér 定理一节与 LDP 定义一节（节号和定理编号凭记忆，本书未核对，使用前请对照原书）；
  den Hollander, *Large Deviations*, 第 I 章（章节号未核对）。
- 本书第 21 章（Chernoff 与 Hoeffding）、第 14 章（`limsup` 与 `iSup`）、第 17 章（`Ber`、`HasLaw`）、
  第 23 章（blueprint 工作流，§9 的清单就是它的一个小例子）。
-/

end Main

end Lean4Learn.Ch22

end
