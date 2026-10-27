module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Sym.Card
public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 21 章　集中不等式：Chernoff 与 Hoeffding

第 17 章的 Chebyshev's inequality（切比雪夫不等式）说：`n` 个 i.i.d.（独立同分布）变量之和
偏离均值 `n t` 的概率至多 `v / (n t²)`，只是多项式地小。本章的 concentration inequality（集中不等式）
把它改进成**指数地小**，例如独立的 `[0, 1]` 值变量满足 `P(Sₙ - 𝔼Sₙ ≥ n t) ≤ exp (-2 n t²)`。

工具是 moment-generating function（矩母函数）：对 `exp (t X)` 用 Markov's inequality（马尔可夫不等式），
再对 `t` 取最优，这就是 Chernoff bound（Chernoff 界）的方法。Mathlib 已经有矩母函数的整套 API、
Chernoff 界、sub-Gaussian（次高斯）变量、Hoeffding 引理与 Hoeffding 不等式；
本章一行一行读它们的假设。

然后把它们装配成三个可直接使用的结论：(a) `n` 个独立 `[0, 1]` 值变量之和的 tail bound（尾界）；
(b) binomial distribution（二项分布）`Bin(ℝ, n, p)` 的上尾界（Mathlib 没有「独立 Bernoulli
distribution（伯努利分布）变量之和服从二项分布」这条引理，所以这一步要自己搭模型）；
(c) binomial random graph（二项随机图）`G(V, p)` 里一个顶点的 degree（度）的集中（需要先证明
边指示随机变量 mutually independent（相互独立），Mathlib 里没有这条）。

## 学习目标
- 会读 `mgf`、`cgf` 的定义，知道不可积时它们取 junk value（垃圾值）`0`，以及哪些定理因此要可积性。
- 会把独立和的矩母函数写成乘积（`mgf_sum₀`），从马尔可夫不等式推出 Chernoff 界并对 `t` 取最优。
- 会用 `HasSubgaussianMGF` 与 Hoeffding 引理、Hoeffding 不等式装配有界变量之和的指数尾界。
- 会把尾界用于二项分布与 `G(V, p)` 的度，并用 union bound（联合界）得到「所有顶点同时」的版本。

## 前置知识
第 17 章（`IndepFun`/`iIndepFun`、`HasLaw`、`Ber`/`Bin`、马尔可夫不等式）；
第 10、11 章（`field`、`positivity`、`fun_prop`、`gcongr`、`div_le_iff₀`）；第 12 章（`∑ i ∈ s`）；
第 14 章（`Tendsto`，仅练习用）；第 15 章（`omit … in`）；第 16 章（`μ.real`、`ae`、`Measure.map`）；
第 18 章（`SimpleGraph.degree`）；第 19 章（联合界）；第 20 章（`G(V, p)` 的定义链，仅 §7、§8 用）。
-/

@[expose] public section

namespace Lean4Learn.Ch21

open MeasureTheory ProbabilityTheory
open scoped NNReal unitInterval

/-!
## 1. 矩母函数与累积量母函数

随机变量 `X` 的 moment-generating function（矩母函数）是 `t ↦ 𝔼[exp (t X)]`，
cumulant-generating function（累积量母函数）是它的对数。Mathlib 的定义就是这一行（`mgf`、`cgf`
都在 `Probability/Moments/Basic.lean`；该文件在 `@[expose] public section` 里，所以 `rfl` 能展开，
机制见第 28 章）：
-/

section MGF

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}

example : mgf X μ t = μ[fun ω ↦ Real.exp (t * X ω)] := rfl
example : cgf X μ t = Real.log (mgf X μ t) := rfl

/-!
`exp (t X)` 不可积时，积分是 junk value `0`（第 17 章的 `integral_undef`），于是 `mgf` 是 `0`，
`cgf = log 0 = 0`。哪些定理要把可积性写成假设，要看证明里哪一步用了真实的积分，不看式子里有没有 `log`：
(1) 需要 `mgf > 0` 的步骤要它，例如 `mgf_pos`、`exp_cgf`（`exp (log 0) = 1 ≠ 0`）、`cgf_add`
（`log (a b) = log a + log b` 要求两个因子非零）；(2) 把概率和真实积分比较的步骤要它，例如 Chernoff 界
（垃圾值 `0` 会让右边变成 `0`）。不需要的有两类：(3) 纯恒等式，两边同时是垃圾值，例如 `mgf_neg`、
`mgf_const_mul`、`mgf_sum`，以及对它们两边取 `log` 的 `cgf` 版本（练习 21.1）；(4) 某些单调性，例如
`mgf_mono_of_nonneg` 只要求较大一侧可积，因为较小一侧若不可积，`0 ≤ mgf` 自动成立（练习 21.14）：
-/

example (h : ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) μ) : mgf X μ t = 0 := mgf_undef h
example (h : ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) μ) : cgf X μ t = 0 := cgf_undef h
example {Y : Ω → ℝ} (hXY : X ≤ᵐ[μ] Y) (ht : 0 ≤ t)
    (hY : Integrable (fun ω ↦ Real.exp (t * Y ω)) μ) : mgf X μ t ≤ mgf Y μ t :=
  mgf_mono_of_nonneg hXY ht hY

/-!
`mgf` 总是非负（被积函数非负，不需要任何假设）；可积加概率测度就严格为正，可积时
`exp (cgf) = mgf`；概率测度下 `mgf X μ 0 = 1`；常数的矩母函数是 `exp (t c)`：
-/

example : 0 ≤ mgf X μ t := mgf_nonneg
example [IsProbabilityMeasure μ] (h : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    0 < mgf X μ t := mgf_pos h
example [NeZero μ] (h : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    Real.exp (cgf X μ t) = mgf X μ t := exp_cgf h
example [IsProbabilityMeasure μ] : mgf X μ 0 = 1 := mgf_zero
example [IsProbabilityMeasure μ] (c : ℝ) : mgf (fun _ ↦ c) μ t = Real.exp (t * c) := mgf_const c

/-!
线性变换：数乘把参数缩放，加常数乘上 `exp (t a)`，取负号把 `t` 变号（后一条是「下尾 = 上尾」
对称性的来源）：
-/

example (a : ℝ) : mgf (fun ω ↦ a * X ω) μ t = mgf X μ (a * t) := mgf_const_mul a
example (a : ℝ) : mgf (fun ω ↦ X ω + a) μ t = mgf X μ t * Real.exp (t * a) := mgf_add_const a
example : mgf (-X) μ t = mgf X μ (-t) := mgf_neg

/-!
两个具体例子。**Gaussian distribution（正态分布）**：`X ~ N(0, v)` 时 `mgf X t = exp (v t² / 2)`
（`mgf_gaussianReal`）；「次高斯」这个名字就来自这个函数（§4）。**伯努利分布**：`X ~ Ber(1, 0, p)` 时
`mgf X t = p eᵗ + (1 - p)`：`HasLaw.integral_comp`（`Probability/HasLaw.lean`，`HasLaw.integral_eq`
多带一个函数 `f` 的版本）把积分搬到分布上，`integral_bernoulliMeasure` 把它写成 `p f(x) + (1-p) f(y)`。
`p : I`（`unitInterval`）出现在实数式子里时是 coercion（强制转换）`↑p`：
-/

example (v : ℝ≥0) (hX : HasLaw X (gaussianReal 0 v) μ) (t : ℝ) :
    mgf X μ t = Real.exp (v * t ^ 2 / 2) := by
  rw [mgf_gaussianReal hX t]
  simp

theorem mgf_bernoulli [IsProbabilityMeasure μ] (p : I) (hX : HasLaw X Ber(1, 0, p) μ) (t : ℝ) :
    mgf X μ t = p * Real.exp t + (1 - p) := by
  have h := hX.integral_comp (f := fun x : ℝ ↦ Real.exp (t * x)) (by fun_prop)
  rw [integral_bernoulliMeasure] at h
  simpa [mgf, Function.comp_def] using h

end MGF

/-!
## 2. 独立性把矩母函数变成乘积

`exp (t (X + Y)) = exp (t X) * exp (t Y)`，独立变量的乘积 expectation（期望）等于期望之积（第 17 章的
`IndepFun.integral_mul_eq_mul_integral`），所以独立和的矩母函数是矩母函数之积，累积量母函数相加。
这是 Chernoff 方法对独立和有效的主要原因。两个变量：`mgf_add'` 假设 `X`、`Y`
almost everywhere（几乎处处）强可测；`cgf_add` 还需要可积性：
-/

section Independent

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X Y : Ω → ℝ} {t : ℝ}

example (h : X ⟂ᵢ[μ] Y) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    mgf (X + Y) μ t = mgf X μ t * mgf Y μ t := h.mgf_add' hX hY

example (h : X ⟂ᵢ[μ] Y) (hX : Integrable (fun ω ↦ Real.exp (t * X ω)) μ)
    (hY : Integrable (fun ω ↦ Real.exp (t * Y ω)) μ) :
    cgf (X + Y) μ t = cgf X μ t + cgf Y μ t := h.cgf_add hX hY

/-!
有限个相互独立（`iIndepFun`，第 17 章）变量之和：`mgf_sum` 要求每个 `Z i` 可测，
`mgf_sum₀` 只要求 `AEMeasurable`（常见错误 5）；`cgf_sum` 额外要求每个 `exp (t Z i)` 可积。注意这里的和是
**函数**之和 `∑ i ∈ s, Z i : Ω → ℝ`，不是 `fun ω ↦ ∑ i ∈ s, Z i ω`（二者相等，但 `rw` 时要看清）：
-/

example {Z : ι → Ω → ℝ} (s : Finset ι) : (∑ i ∈ s, Z i) = fun ω ↦ ∑ i ∈ s, Z i ω := by
  ext ω
  simp

example {Z : ι → Ω → ℝ} (h : iIndepFun Z μ) (hZ : ∀ i, Measurable (Z i)) (s : Finset ι) :
    mgf (∑ i ∈ s, Z i) μ t = ∏ i ∈ s, mgf (Z i) μ t := h.mgf_sum hZ s

example {Z : ι → Ω → ℝ} (h : iIndepFun Z μ) (hZ : ∀ i, AEMeasurable (Z i) μ) (s : Finset ι) :
    mgf (∑ i ∈ s, Z i) μ t = ∏ i ∈ s, mgf (Z i) μ t := h.mgf_sum₀ hZ s

example {Z : ι → Ω → ℝ} (h : iIndepFun Z μ) (hZ : ∀ i, Measurable (Z i)) {s : Finset ι}
    (hint : ∀ i ∈ s, Integrable (fun ω ↦ Real.exp (t * Z i ω)) μ) :
    cgf (∑ i ∈ s, Z i) μ t = ∑ i ∈ s, cgf (Z i) μ t := h.cgf_sum hZ hint

/-!
**例：`n` 个独立伯努利(p) 变量之和的矩母函数是 `(p eᵗ + 1 - p)ⁿ`**。先用 `mgf_sum₀` 拆成乘积，
再对每个因子用 `mgf_bernoulli`，最后 `Finset.prod_const` 与 `Finset.card_range`（第 12 章）：
-/

theorem mgf_sum_bernoulli [IsProbabilityMeasure μ] {Z : ℕ → Ω → ℝ} (p : I)
    (hZ : ∀ i, HasLaw (Z i) Ber(1, 0, p) μ) (h : iIndepFun Z μ) (n : ℕ) (t : ℝ) :
    mgf (∑ i ∈ Finset.range n, Z i) μ t = (p * Real.exp t + (1 - p)) ^ n :=
  calc mgf (∑ i ∈ Finset.range n, Z i) μ t = ∏ i ∈ Finset.range n, mgf (Z i) μ t :=
        h.mgf_sum₀ (fun i ↦ (hZ i).aemeasurable) _
    _ = ∏ i ∈ Finset.range n, ((p : ℝ) * Real.exp t + (1 - p)) :=
        Finset.prod_congr rfl fun i _ ↦ mgf_bernoulli p (hZ i) t
    _ = (p * Real.exp t + (1 - p)) ^ n := by rw [Finset.prod_const, Finset.card_range]

end Independent

/-!
## 3. Chernoff 方法：从马尔可夫不等式出发

马尔可夫不等式只用 `X ≥ 0` 的一阶矩。Chernoff 的想法是把它用在 `exp (t X)` 上：
对 `t ≥ 0`，事件 `{ε ≤ X}` 包含于 `{exp (t ε) ≤ exp (t X)}`（`exp` 单调），后者由马尔可夫不等式
（`mul_meas_ge_le_integral_of_nonneg`，第 17 章）有
`exp (t ε) * P(exp (t ε) ≤ exp (t X)) ≤ 𝔼 exp (t X) = mgf X t`。下面是完整证明；只用「包含」而不是
「相等」，所以不需要把 `t = 0` 分出来：
-/

section Chernoff

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {t : ℝ}

theorem chernoff_by_hand [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t := by
  have hsub : {ω | ε ≤ X ω} ⊆ {ω | Real.exp (t * ε) ≤ Real.exp (t * X ω)} := by
    intro ω (hω : ε ≤ X ω)
    show Real.exp (t * ε) ≤ Real.exp (t * X ω)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hω ht)
  have hmarkov : Real.exp (t * ε) * μ.real {ω | Real.exp (t * ε) ≤ Real.exp (t * X ω)}
      ≤ ∫ ω, Real.exp (t * X ω) ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ (Real.exp_pos _).le) h_int _
  -- hsub : {ω | ε ≤ X ω} ⊆ {ω | Real.exp (t * ε) ≤ Real.exp (t * X ω)}
  -- hmarkov : Real.exp (t * ε) * μ.real {ω | Real.exp (t * ε) ≤ Real.exp (t * X ω)}
  --             ≤ ∫ (ω : Ω), Real.exp (t * X ω) ∂μ
  -- ⊢ μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t
  calc μ.real {ω | ε ≤ X ω}
      ≤ μ.real {ω | Real.exp (t * ε) ≤ Real.exp (t * X ω)} := measureReal_mono hsub
    _ = Real.exp (-t * ε) * (Real.exp (t * ε) *
          μ.real {ω | Real.exp (t * ε) ≤ Real.exp (t * X ω)}) := by
        rw [← mul_assoc, ← Real.exp_add, show -t * ε + t * ε = 0 by ring, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-t * ε) * mgf X μ t := mul_le_mul_of_nonneg_left hmarkov (Real.exp_pos _).le

/-!
Mathlib 里同样的定理叫 `measure_ge_le_exp_mul_mgf`（第 9 章的读法：`measure_ge_le` 是结论的形状，
`exp_mul_mgf` 是界的形状；在 `Mathlib/Probability/Moments/` 下 `rg "theorem measure_ge_le"` 找到这一族）。
假设与上面的证明一一对应：`[IsFiniteMeasure μ]`（`measureReal_mono` 需要）；`0 ≤ t`（`t` 必须**非负**，
否则从 `ε ≤ X` 推不出 `exp (t ε) ≤ exp (t X)`；常见错误 4）；`h_int`（马尔可夫不等式比较的是真实积分）。
对 `X` 本身不要求可测。`…_exp_cgf` 把右边写成 `exp (-t ε + cgf X μ t)`；**下尾**版本
`measure_le_le_exp_mul_mgf` 把 `t ≥ 0` 换成 `t ≤ 0`、事件换成 `{X ≤ ε}`：
-/

example [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t :=
  measure_ge_le_exp_mul_mgf ε ht h_int

example [IsFiniteMeasure μ] (ε : ℝ) (ht : 0 ≤ t)
    (h_int : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε + cgf X μ t) :=
  measure_ge_le_exp_cgf ε ht h_int

example [IsFiniteMeasure μ] (ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    μ.real {ω | X ω ≤ ε} ≤ Real.exp (-t * ε) * mgf X μ t :=
  measure_le_le_exp_mul_mgf ε ht h_int

/-!
**对 `t` 取最优。** 上界对每个 `t ≥ 0` 都成立，所以可以对 `t` 取 infimum（下确界）。典型情形：
矩母函数被 `exp (c t² / 2)` 控制（高斯的形状），界是 `exp (-t ε + c t² / 2)`，指数关于 `t` 的最小值
在 `t = ε / c` 处取得，值为 `-ε² / (2c)`（练习 21.4）。把 `t = ε / c` 代入：
-/

theorem chernoff_optimized [IsFiniteMeasure μ] {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε)
    (h_int : ∀ t, Integrable (fun ω ↦ Real.exp (t * X ω)) μ)
    (h_mgf : ∀ t, mgf X μ t ≤ Real.exp (c * t ^ 2 / 2)) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * c)) := by
  have hc' : c ≠ 0 := hc.ne'
  calc μ.real {ω | ε ≤ X ω}
      ≤ Real.exp (-(ε / c) * ε) * mgf X μ (ε / c) :=
        measure_ge_le_exp_mul_mgf ε (div_nonneg hε hc.le) (h_int _)
    _ ≤ Real.exp (-(ε / c) * ε) * Real.exp (c * (ε / c) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (h_mgf _) (Real.exp_pos _).le
    _ = Real.exp (-ε ^ 2 / (2 * c)) := by
        rw [← Real.exp_add]
        congr 1
        field

end Chernoff

/-!
## 4. 次高斯变量

上面的 `h_int` 与 `h_mgf` 两个假设成对出现，Mathlib 把它们打包成一个结构体
`HasSubgaussianMGF X c μ`（`Probability/Moments/SubGaussian.lean`），两个字段 `integrable_exp_mul`、
`mgf_le` 正是这两个假设（下面前三个例子）。读作「`X` 具有参数 `c` 的次高斯矩母函数」。
`exp (c t² / 2)` 恰好是 variance（方差）为 `c` 的中心高斯变量的矩母函数，所以这是说 `X` 的矩母函数
不超过高斯的。参数 `c : ℝ≥0` 是**非负实数**，不是 `ℝ`（常见错误 2）。高斯分布本身是等号成立的例子
（`mgf_id_gaussianReal`，`id` 是 `ℝ` 上的恒等变量，测度是它的分布）：
-/

section SubGaussian

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

example (h : HasSubgaussianMGF X c μ) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ := h.integrable_exp_mul t

example (h : HasSubgaussianMGF X c μ) (t : ℝ) : mgf X μ t ≤ Real.exp (c * t ^ 2 / 2) := h.mgf_le t

example (hint : ∀ t, Integrable (fun ω ↦ Real.exp (t * X ω)) μ)
    (hmgf : ∀ t, mgf X μ t ≤ Real.exp (c * t ^ 2 / 2)) : HasSubgaussianMGF X c μ :=
  ⟨hint, hmgf⟩

example (v : ℝ≥0) : HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-!
Mathlib 在这个结构体上证了本章要用的全部性质。`cgf_le` 是 `mgf_le` 取对数的结果；`measure_ge_le` 是
上面 `chernoff_optimized` 的打包版本（可积性由结构体提供）；`neg` 说 `-X` 有同一个参数；
`integrable` 说次高斯变量可积。双侧界由对称性得到：`{ε ≤ |X|}` 包含于 `{ε ≤ X} ∪ {ε ≤ -X}`，
上尾用 `h`，下尾用 `h.neg`，再用 `measureReal_union_le`（练习 21.11 就是这样做的）：
-/

example (h : HasSubgaussianMGF X c μ) (t : ℝ) : cgf X μ t ≤ c * t ^ 2 / 2 := h.cgf_le t
example (h : HasSubgaussianMGF X c μ) : Integrable X μ := h.integrable

example (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * c)) := h.measure_ge_le hε

example (h : HasSubgaussianMGF X c μ) : HasSubgaussianMGF (-X) c μ := h.neg
example (A B : Set Ω) : μ.real (A ∪ B) ≤ μ.real A + μ.real B := measureReal_union_le A B

/-!
**`c = 0` 是边界情形。** 参数 `0` 的次高斯变量 almost surely（几乎必然；即 `∀ᵐ ω ∂μ`，第 16 章）
为 `0`；在尾界里分母是 `0`，`x / 0 = 0`（第 2 章）使界变成 `exp 0 = 1`：定理仍然成立，只是平凡。
-/

example (h : HasSubgaussianMGF X 0 μ) : X =ᵐ[μ] 0 := h.ae_eq_zero_of_hasSubgaussianMGF_zero

example (ε : ℝ) : -ε ^ 2 / (2 * ((0 : ℝ≥0) : ℝ)) = 0 := by simp

/-!
**独立和。** 独立的次高斯变量之和仍是次高斯，参数相加（`add_of_indepFun` 是两个变量的版本，
`sum_of_iIndepFun` 是有限族）。再接上 `measure_ge_le` 就是 `measure_sum_ge_le_of_iIndepFun`，它在
Mathlib 里的文档注释就是「**Hoeffding inequality** for sub-Gaussian random variables」：假设
`iIndepFun`（相互独立，不是 pairwise independent（两两独立））、每个 `Z i` 次高斯、`0 ≤ ε`，
**不要求同分布，不要求 `Z i` 有界**：
-/

example {Y : Ω → ℝ} {c' : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (hY : HasSubgaussianMGF Y c' μ)
    (h : X ⟂ᵢ[μ] Y) : HasSubgaussianMGF (fun ω ↦ X ω + Y ω) (c + c') μ :=
  hX.add_of_indepFun hY h

example {ι : Type*} {Z : ι → Ω → ℝ} {d : ι → ℝ≥0} (h : iIndepFun Z μ) {s : Finset ι}
    (hs : ∀ i ∈ s, HasSubgaussianMGF (Z i) (d i) μ) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, Z i ω) (∑ i ∈ s, d i) μ :=
  HasSubgaussianMGF.sum_of_iIndepFun h hs

example {ι : Type*} {Z : ι → Ω → ℝ} {d : ι → ℝ≥0} (h : iIndepFun Z μ) {s : Finset ι}
    (hs : ∀ i ∈ s, HasSubgaussianMGF (Z i) (d i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, Z i ω} ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, d i)) :=
  HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun h hs hε

/-!
参数全相同、指标集是 `range n` 时有现成的特化 `measure_sum_range_ge_le_of_iIndepFun`，分母是 `2 n c`
（练习 21.9 用它）：
-/

example {Z : ℕ → Ω → ℝ} (h : iIndepFun Z μ) {n : ℕ} (hs : ∀ i < n, HasSubgaussianMGF (Z i) c μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Z i ω} ≤ Real.exp (-ε ^ 2 / (2 * n * c)) :=
  HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun h hs hε

end SubGaussian

/-!
**导览（不展开）：Azuma–Hoeffding inequality（Azuma–Hoeffding 不等式）。** 把独立性换成条件次高斯性，
同一个界仍成立。Mathlib 的 `measure_sum_ge_le_of_hasCondSubgaussianMGF` 与 Hoeffding 在同一个文件
`SubGaussian.lean` 里。下面只确认它的签名：`ℱ` 是 filtration（滤流；与滤子 `Filter` 无关），
`StronglyAdapted ℱ Y` 说 `Y` 是 adapted process（适应过程），`HasCondSubgaussianMGF` 是条件版本的
`HasSubgaussianMGF`；`n - 1` 是 `ℕ` 的截断减法（第 2 章）：
-/

section Azuma

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {d : ℕ → ℝ≥0}

example (hadapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (d 0) μ) (n : ℕ)
    (hsub : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (d (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, d i)) :=
  measure_sum_ge_le_of_hasCondSubgaussianMGF hadapted h0 n hsub hε

end Azuma

/-!
**Mathlib 里没有什么。** 在 `Mathlib/` 下 `rg -i "mcdiarmid|bennett"` 没有结果，`Probability/` 下搜
`bernstein` 也没有结果（别处的 Bernstein 是 Bernstein 多项式和 Schröder–Bernstein 定理）。所以
McDiarmid、Bennett、Bernstein 不等式这个版本的 Mathlib 里都没有（搜索结果，换版本后要重搜）。
`SubGaussian.lean` 的文件头还说，次高斯的其他刻画（尾概率、矩、Orlicz norm（Orlicz 范数），即其中的
(i)–(iv)）尚未实现（文件头的 TODO），Mathlib 只实现了以矩母函数为准的 (v)。
-/

/-!
## 5. Hoeffding 引理与 Hoeffding 不等式

有界变量是次高斯的，这就是 **Hoeffding 引理**。Mathlib 有两个版本（`Moments/SubGaussian.lean`）：
期望为零的 `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`，与一般的 `hasSubgaussianMGF_of_mem_Icc`。
后者的假设：`[IsProbabilityMeasure μ]`；`AEMeasurable X μ`（不是 `Measurable`）；
`∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b`（不要求 `a < b`）。**结论是关于中心化变量 `fun ω ↦ X ω - μ[X]` 的**
（常见错误 3），参数 `(‖b - a‖₊ / 2) ^ 2 : ℝ≥0` 即 `(b - a)² / 4`；`‖x‖₊` 是范数的 `ℝ≥0` 版本，
对实数转回 `ℝ` 就是绝对值：
-/

example (x : ℝ) : ((‖x‖₊ : ℝ≥0) : ℝ) = |x| := by rw [coe_nnnorm, Real.norm_eq_abs]

section Hoeffding

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

example {X : Ω → ℝ} {a b : ℝ} (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hc : μ[X] = 0) : HasSubgaussianMGF X ((‖b - a‖₊ / 2) ^ 2) μ :=
  hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc

example {X : Ω → ℝ} {a b : ℝ} (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) ((‖b - a‖₊ / 2) ^ 2) μ :=
  hasSubgaussianMGF_of_mem_Icc hm hb

/-!
现在装配。目标：独立的 `[a, b]` 值变量 `X i`（`i ∈ s`），
`P(∑ 𝔼 Xᵢ + |s| t ≤ ∑ Xᵢ) ≤ exp (-2 |s| t² / (b - a)²)`。步骤：(1) Hoeffding 引理给出每个
`X i - 𝔼 X i` 次高斯；(2) 中心化后的族仍相互独立（`iIndepFun.comp`，每个坐标复合可测函数
`x ↦ x - 𝔼 X i`）；(3) `sum_of_iIndepFun` 与 `measure_ge_le`（取 `ε = |s| t`）；(4) 纯代数：把 `ℝ≥0`
的参数转成实数并化简指数。第 (4) 步先单独证明（`N = 0` 时分母为零，`simp` 处理）：
-/

theorem hoeffding_exponent (N t a b : ℝ) (hab : a < b) :
    -(N * t) ^ 2 / (2 * (N * ((b - a) ^ 2 / 4))) = -2 * N * t ^ 2 / (b - a) ^ 2 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
    field_simp
    ring

theorem hoeffding_const {a b : ℝ} (hab : a < b) :
    (((‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (b - a) ^ 2 / 4 := by
  push_cast
  rw [Real.norm_eq_abs, abs_of_pos (sub_pos.2 hab)]
  ring

theorem hoeffding_rate (s : Finset ι) {a b : ℝ} (hab : a < b) (t : ℝ) :
    -((s.card : ℝ) * t) ^ 2 / (2 * ((∑ _i ∈ s, (‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))
      = -2 * s.card * t ^ 2 / (b - a) ^ 2 := by
  have hsum : ((∑ _i ∈ s, (‖b - a‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = s.card * ((b - a) ^ 2 / 4) := by
    rw [NNReal.coe_sum]
    simp [hoeffding_const hab]
  rw [hsum, hoeffding_exponent _ _ _ _ hab]

/-!
第 (1)–(3) 步给出中心化的和的次高斯性；上尾界只需再把事件改写成 `{ω | |s| t ≤ ∑ (X i ω - 𝔼 X i)}`
的形状：
-/

theorem hoeffding_subG {X : ι → Ω → ℝ} (hind : iIndepFun X μ) (s : Finset ι)
    (hm : ∀ i ∈ s, AEMeasurable (X i) μ) {a b : ℝ}
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b) :
    HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, (X i ω - μ[X i])) (∑ _i ∈ s, (‖b - a‖₊ / 2) ^ 2) μ := by
  have hsg : ∀ i ∈ s,
      HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) ((‖b - a‖₊ / 2) ^ 2) μ :=
    fun i hi ↦ hasSubgaussianMGF_of_mem_Icc (hm i hi) (hb i hi)
  have hind' : iIndepFun (fun i ω ↦ X i ω - μ[X i]) μ :=
    hind.comp (fun i (x : ℝ) ↦ x - ∫ ω, X i ω ∂μ) (fun i ↦ measurable_id.sub_const _)
  -- hsg : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - ∫ (x : Ω), X i x ∂μ) ((‖b - a‖₊ / 2) ^ 2) μ
  -- hind' : iIndepFun (fun i ω ↦ X i ω - ∫ (x : Ω), X i x ∂μ) μ
  -- ⊢ HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, (X i ω - ∫ (x : Ω), X i x ∂μ))
  --     (∑ _i ∈ s, (‖b - a‖₊ / 2) ^ 2) μ
  exact HasSubgaussianMGF.sum_of_iIndepFun hind' hsg

/-- **Hoeffding 不等式**（上尾），独立的 `[a, b]` 值变量，不要求同分布。 -/
theorem hoeffding {X : ι → Ω → ℝ} (hind : iIndepFun X μ) (s : Finset ι)
    (hm : ∀ i ∈ s, AEMeasurable (X i) μ)
    {a b : ℝ} (hab : a < b) (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc a b) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ s, μ[X i] + s.card * t ≤ ∑ i ∈ s, X i ω}
      ≤ Real.exp (-2 * s.card * t ^ 2 / (b - a) ^ 2) := by
  have h := (hoeffding_subG hind s hm hb).measure_ge_le (ε := s.card * t) (by positivity)
  have hset : {ω | ∑ i ∈ s, μ[X i] + s.card * t ≤ ∑ i ∈ s, X i ω}
      = {ω | (s.card : ℝ) * t ≤ ∑ i ∈ s, (X i ω - μ[X i])} := by
    ext ω
    simp only [Finset.sum_sub_distrib, Set.mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  -- 改写事件后，`h` 与目标只差指数的代数形式（`hoeffding_rate`）
  rw [hset]
  exact h.trans_eq (congrArg Real.exp (hoeffding_rate s hab t))

/-!
## 6. 应用 (a)：`n` 个独立 `[0, 1]` 值变量之和

`[a, b] = [0, 1]` 时 `(b - a)² = 1`，指数是 `-2 |s| t²`。若所有 `X i` 的期望都是 `m`，和的期望项
化成 `n m`，得到最常用的形式 `P(Sₙ - n m ≥ n t) ≤ exp (-2 n t²)`（练习 21.9 从次高斯性出发证明它；
这里**没有**同分布假设）。对比第 17 章的切比雪夫界 `v / (n t²)`：偏离 `t = 0.1` 的概率现在不超过
`exp (-0.02 n)`，练习 21.12 算出 `n = 1000` 时的数值。
-/

theorem hoeffding_unit {X : ι → Ω → ℝ} (hind : iIndepFun X μ) (s : Finset ι)
    (hm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∑ i ∈ s, μ[X i] + s.card * t ≤ ∑ i ∈ s, X i ω}
      ≤ Real.exp (-2 * s.card * t ^ 2) := by
  have h := hoeffding hind s hm (a := 0) (b := 1) zero_lt_one hb ht
  -- `h` 的指数里多一个分母 `(1 - 0) ^ 2`，`simpa` 把它化成 `1`
  simpa using h

/-!
伯努利变量是 `[0, 1]` 值的（`HasLaw.ae_iff` 把「几乎必然」搬到分布上，要求谓词可测，即下面的
`measurable_mem.2 measurableSet_Icc`），期望是 `p`（`HasLaw.integral_eq`、`integral_bernoulliMeasure`）：
-/

theorem hoeffding_bernoulli {X : ι → Ω → ℝ} (hind : iIndepFun X μ) (p : I)
    (s : Finset ι) (hX : ∀ i ∈ s, HasLaw (X i) Ber(1, 0, p) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (s.card : ℝ) * ((p : ℝ) + t) ≤ ∑ i ∈ s, X i ω}
      ≤ Real.exp (-2 * s.card * t ^ 2) := by
  have hb : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    rw [(hX i hi).ae_iff (p := fun x ↦ x ∈ Set.Icc (0 : ℝ) 1) (measurable_mem.2 measurableSet_Icc),
      ae_iff]
    exact bernoulliMeasure_apply_of_notMem_of_notMem p
      (s := {x : ℝ | ¬ x ∈ Set.Icc (0 : ℝ) 1}) (measurableSet_Icc.compl) (by simp) (by simp)
  have hmean : ∀ i ∈ s, μ[X i] = (p : ℝ) := by
    intro i hi
    simp [(hX i hi).integral_eq, integral_bernoulliMeasure]
  have h := hoeffding_unit hind s (fun i hi ↦ (hX i hi).aemeasurable) hb ht
  rw [Finset.sum_congr rfl hmean] at h
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  rw [mul_add]
  exact h

end Hoeffding

/-!
## 7. 应用 (b)：二项分布 `Bin(ℝ, n, p)` 的上尾

`hoeffding_bernoulli` 说的是**独立伯努利变量之和**的尾巴；而 Mathlib 的 binomial distribution 是一个
**测度** `Bin(ℝ, n, p)`（第 17 章）。它的定义 `binomial` 经过 `setBer`，也就是规范空间上独立 Bernoulli
坐标的 product measure（积测度），所以独立坐标藏在定义里；缺的是一条对**任意**独立族
（`iIndepFun` 加 `HasLaw … Ber(1, 0, p)`）成立的引理，Mathlib 里没有它（在 `Probability/` 下搜 `binomial`
只命中分布文件、质量函数文件、泊松极限、二项随机图的定义和一个 README）。所以要自己补一座桥：在
`ℕ → Prop` 上取积测度 `coins n p`（第 `i < n` 个坐标是 `Ber(p)` 硬币，其余坐标几乎必然为 `False`），
`Bin(ℝ, n, p)` 就是「为真的坐标个数」在 `coins n p` 下的 push-forward measure（前推测度，
`binomial_eq_map`）。`coin b` 是 `Prop` 到 `ℝ` 的 indicator function（指示函数）。
-/

section Binomial

open Classical in
/-- `Prop` 的指示函数：`True` 取 `1`，`False` 取 `0`。 -/
noncomputable def coin (b : Prop) : ℝ := if b then 1 else 0

@[simp] theorem coin_true : coin True = 1 := by simp [coin]
@[simp] theorem coin_false : coin False = 0 := by simp [coin]

theorem coin_of {b : Prop} (h : b) : coin b = 1 := by simp [coin, h]

theorem coin_mem_Icc (b : Prop) : coin b ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : b <;> simp [coin, h]

theorem measurable_coin : Measurable coin := Measurable.of_discrete

/-- `ℕ → Prop` 上的积测度：第 `i < n` 个坐标是 `Ber(p)` 硬币，其余坐标几乎必然为 `False`
（Mathlib 的 `setBer(Iio n, p)` 就建在这个空间上）。 -/
noncomputable def coins (n : ℕ) (p : I) : Measure (ℕ → Prop) :=
  Measure.infinitePi fun i : ℕ ↦ Ber(i ∈ Set.Iio n, False, p)

instance (n : ℕ) (p : I) : IsProbabilityMeasure (coins n p) := by
  unfold coins; infer_instance

/-- `Bin(ℝ, n, p)` 是「为真的坐标个数」的分布。 -/
theorem binomial_eq_map (n : ℕ) (p : I) :
    Bin(ℝ, n, p) = (coins n p).map fun q ↦ (({i | q i} : Set ℕ).ncard : ℝ) := by
  have h1 : Measurable fun q : ℕ → Prop ↦ ({i | q i} : Set ℕ) :=
    measurable_set_iff.2 fun i ↦ measurable_pi_apply i
  rw [binomial, setBernoulli_eq_map, Measure.map_map (by fun_prop) h1,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- 坐标 `≥ n` 几乎必然为假。 -/
theorem ae_coins_false (n : ℕ) (p : I) : ∀ᵐ q ∂coins n p, ∀ i, n ≤ i → ¬ q i := by
  rw [ae_all_iff]
  intro i
  by_cases hi : n ≤ i
  · have hmap : (coins n p).map (fun q : ℕ → Prop ↦ q i) = Ber(i ∈ Set.Iio n, False, p) :=
      Measure.infinitePi_map_eval _ i
    have h0 : coins n p {q : ℕ → Prop | q i} = 0 := by
      have := Measure.map_apply (μ := coins n p) (measurable_pi_apply i)
        (MeasurableSet.of_discrete (s := {x : Prop | x}))
      rw [hmap] at this
      have h2 : {q : ℕ → Prop | q i} = (fun q : ℕ → Prop ↦ q i) ⁻¹' {x : Prop | x} := rfl
      rw [h2, ← this]
      exact bernoulliMeasure_apply_of_notMem_of_notMem p MeasurableSet.of_discrete
        (by simpa using hi) (by simp)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    exact fun _ ↦ hq
  · exact ae_of_all _ fun q h ↦ absurd h hi

/-!
下面的证明分五步，前四步是常规的，最后一步才是这座桥的内容：

1. 变量 `X i q = coin (q i)` 相互独立（`iIndepFun_infinitePi`），取 `[0, 1]` 值；
2. `i < n` 时 `𝔼 X i = p`：`Measure.infinitePi_map_eval` 说坐标的前推测度是 `Ber`，再
   `integral_map` 与 `integral_bernoulliMeasure`；
3. `hoeffding_unit` 给出 `∑ i<n, X i` 的尾界；
4. `binomial_eq_map` 与 `map_measureReal_apply` 把 `Bin(ℝ, n, p).real` 换成 `coins n p` 下的概率；
5. `ae_coins_false` 说坐标 `≥ n` 几乎必然为假，于是几乎必然「为真的坐标个数 `= ∑ i<n, X i`」
   （`hcount`，用 `Finset.sum_boole` 数数）；几乎必然相等的事件概率相等（`measureReal_congr`）。
-/

/-- **二项分布的 Hoeffding 尾界**：`Bin(ℝ, n, p)` 的质量落在 `[n (p + t), ∞)` 的概率
至多 `exp (-2 n t²)`。 -/
theorem binomial_tail (n : ℕ) (p : I) {t : ℝ} (ht : 0 ≤ t) :
    Bin(ℝ, n, p).real {x | (n : ℝ) * (p + t) ≤ x} ≤ Real.exp (-2 * n * t ^ 2) := by
  classical
  let X : ℕ → (ℕ → Prop) → ℝ := fun i q ↦ coin (q i)
  have hX : ∀ i, Measurable (X i) := fun i ↦ measurable_coin.comp (measurable_pi_apply i)
  have hind : iIndepFun X (coins n p) :=
    iIndepFun_infinitePi (P := fun i : ℕ ↦ Ber(i ∈ Set.Iio n, False, p))
      (X := fun _ b ↦ coin b) fun _ ↦ measurable_coin
  have hb : ∀ i, ∀ᵐ q ∂coins n p, X i q ∈ Set.Icc (0 : ℝ) 1 :=
    fun i ↦ ae_of_all _ fun q ↦ coin_mem_Icc (q i)
  have hmean : ∀ i ∈ Finset.range n, (coins n p)[X i] = (p : ℝ) := by
    intro i hi
    have hin : i < n := Finset.mem_range.1 hi
    have hmap : (coins n p).map (fun q : ℕ → Prop ↦ q i) = Ber(i ∈ Set.Iio n, False, p) :=
      Measure.infinitePi_map_eval _ i
    have h2 : ∫ q, coin (q i) ∂coins n p = ∫ b, coin b ∂Ber(i ∈ Set.Iio n, False, p) := by
      rw [← hmap, integral_map (measurable_pi_apply i).aemeasurable
        measurable_coin.aestronglyMeasurable]
    show ∫ q, coin (q i) ∂coins n p = (p : ℝ)
    rw [h2, integral_bernoulliMeasure]
    simp [hin]
  have h := hoeffding_unit hind (Finset.range n) (fun i _ ↦ (hX i).aemeasurable)
    (fun i _ ↦ hb i) ht
  rw [Finset.sum_congr rfl hmean] at h
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have hmeas : MeasurableSet {x : ℝ | (n : ℝ) * (p + t) ≤ x} := measurableSet_Ici
  have hY : Measurable fun q : ℕ → Prop ↦ (({i | q i} : Set ℕ).ncard : ℝ) := by
    have h1 : Measurable fun q : ℕ → Prop ↦ ({i | q i} : Set ℕ) :=
      measurable_set_iff.2 fun i ↦ measurable_pi_apply i
    fun_prop
  rw [binomial_eq_map, map_measureReal_apply hY hmeas]
  have hae : (fun q : ℕ → Prop ↦ (({i | q i} : Set ℕ).ncard : ℝ)) ⁻¹'
        {x : ℝ | (n : ℝ) * (p + t) ≤ x}
      =ᵐ[coins n p] {q | (n : ℝ) * p + n * t ≤ ∑ i ∈ Finset.range n, X i q} := by
    filter_upwards [ae_coins_false n p] with q hq
    refine propext ?_
    have hcount : (({i | q i} : Set ℕ).ncard : ℝ) = ∑ i ∈ Finset.range n, X i q := by
      have hs : ({i | q i} : Set ℕ) = ↑((Finset.range n).filter fun i ↦ q i) := by
        ext i
        simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
        exact ⟨fun hi ↦ ⟨by by_contra hh; exact hq i (not_lt.1 hh) hi, hi⟩, fun hi ↦ hi.2⟩
      rw [hs, Set.ncard_coe_finset]
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hi : q i <;> simp [X, coin, hi]
    show (n : ℝ) * (p + t) ≤ (({i | q i} : Set ℕ).ncard : ℝ) ↔ _
    rw [hcount, mul_add]
  rw [measureReal_congr hae]
  exact h

end Binomial

/-!
## 8. 应用 (c)：`G(V, p)` 中顶点的度

`G(V, p) = SimpleGraph.binomialRandom V p` 是 `SimpleGraph V` 上的测度（第 20 章），每条可能的边独立地
以概率 `p` 出现。顶点 `v` 的度 `G.degree v` 是 `V \ {v}` 中与 `v` 相邻的顶点个数，所以是 `|V| - 1` 个
**独立** Bernoulli(p) 指示随机变量之和，`hoeffding_bernoulli` 适用。

难点只有一个：边的相互独立性在 Mathlib 里没有现成的 `iIndepFun` 陈述
（`Probability/Combinatorics/` 下搜 `Indep` 没有结果；`BinomialRandomGraph/Defs.lean` 只构造了测度）。
证明思路：`G(V, p)` 是 `setBernoulli` 经 `fromEdgeSet` 的前推测度，而 `setBernoulli` 是积测度
`infinitePi` 的前推测度；把「边指示向量」`G ↦ (e ↦ e ∈ G.edgeSet)` 的前推测度算出来，恰好是积测度
`∏ Ber(p)`（对角线上的 unordered pair（无序对）`s(a, a)`，即 `e.IsDiag` 为真的位置，取 `False`），再用
`iIndepFun_iff_map_fun_eq_infinitePi_map`（`Independence/InfinitePi.lean`）得到独立性。
`map_edgeIndicator` 的证明（合成两层 `Measure.map`，逐坐标化简）是例行公事，读者可以只看陈述。
-/

section RandomGraph

open scoped SimpleGraph

variable {V : Type*} [Countable V]

omit [Countable V] in
theorem measurable_edgeIndicator :
    Measurable (fun (G : SimpleGraph V) (e : Sym2 V) ↦ e ∈ G.edgeSet) :=
  measurable_pi_iff.2 fun e ↦ (measurable_set_mem e).comp SimpleGraph.measurable_edgeSet

/-- **`G(V, p)` 的边指示向量服从积测度 `∏ Ber(p)`**（对角线上的无序对取 `False`）。 -/
theorem map_edgeIndicator (p : I) :
    (G(V, p)).map (fun (G : SimpleGraph V) (e : Sym2 V) ↦ e ∈ G.edgeSet)
      = Measure.infinitePi (fun e : Sym2 V ↦ Ber(¬ e.IsDiag, False, p)) := by
  have h1 : Measurable fun q : Sym2 V → Prop ↦ ({i | q i} : Set (Sym2 V)) :=
    measurable_set_iff.2 fun i ↦ measurable_pi_apply i
  rw [SimpleGraph.binomialRandom_eq_map,
    Measure.map_map measurable_edgeIndicator SimpleGraph.measurable_fromEdgeSet,
    setBernoulli_eq_map,
    Measure.map_map (measurable_edgeIndicator.comp SimpleGraph.measurable_fromEdgeSet) h1]
  have hcomp : ((fun (G : SimpleGraph V) (e : Sym2 V) ↦ e ∈ G.edgeSet) ∘
      SimpleGraph.fromEdgeSet) ∘ (fun q : Sym2 V → Prop ↦ ({i | q i} : Set (Sym2 V)))
      = fun (q : Sym2 V → Prop) (e : Sym2 V) ↦
        (fun (e : Sym2 V) (b : Prop) ↦ b ∧ ¬ e.IsDiag) e (q e) := by
    funext q e
    simp [SimpleGraph.edgeSet_fromEdgeSet, Sym2.mem_diagSet]
  rw [hcomp, Measure.infinitePi_map_pi _ (f := fun (e : Sym2 V) (b : Prop) ↦ b ∧ ¬ e.IsDiag)
    (fun e ↦ Measurable.of_discrete)]
  refine congrArg Measure.infinitePi (funext fun e ↦ ?_)
  rw [map_bernoulliMeasure' _ _ Measurable.of_discrete]
  simp

/-- 单条边的指示随机变量的边缘分布。 -/
theorem map_edge_marginal (p : I) (e : Sym2 V) :
    G(V, p).map (fun G : SimpleGraph V ↦ e ∈ G.edgeSet) = Ber(¬ e.IsDiag, False, p) := by
  have h1 := Measure.map_map (μ := G(V, p)) (measurable_pi_apply e)
    (measurable_edgeIndicator (V := V))
  rw [map_edgeIndicator, Measure.infinitePi_map_eval] at h1
  exact h1.symm

/-- **`G(V, p)` 的边相互独立。** -/
theorem iIndepFun_edges (p : I) :
    iIndepFun (fun (e : Sym2 V) (G : SimpleGraph V) ↦ e ∈ G.edgeSet) G(V, p) := by
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map (fun e ↦ ?_)).2 ?_
  · exact (measurable_set_mem e).comp SimpleGraph.measurable_edgeSet
  · refine (map_edgeIndicator p).trans ?_
    exact congrArg Measure.infinitePi (funext fun e ↦ (map_edge_marginal p e).symm)

theorem hasLaw_coin_edge (p : I) {e : Sym2 V} (he : ¬ e.IsDiag) :
    HasLaw (fun G : SimpleGraph V ↦ coin (e ∈ G.edgeSet)) Ber(1, 0, p) G(V, p) := by
  have hmeas : Measurable (fun G : SimpleGraph V ↦ e ∈ G.edgeSet) :=
    (measurable_set_mem e).comp SimpleGraph.measurable_edgeSet
  refine ⟨(measurable_coin.comp hmeas).aemeasurable, ?_⟩
  rw [show (fun G : SimpleGraph V ↦ coin (e ∈ G.edgeSet))
      = coin ∘ (fun G : SimpleGraph V ↦ e ∈ G.edgeSet) from rfl,
    ← Measure.map_map measurable_coin hmeas, map_edge_marginal,
    map_bernoulliMeasure' _ _ measurable_coin, coin_of he, coin_false]

theorem iIndepFun_coin_edges (p : I) :
    iIndepFun (fun (e : Sym2 V) (G : SimpleGraph V) ↦ coin (e ∈ G.edgeSet)) G(V, p) :=
  (iIndepFun_edges p).comp (fun _ b ↦ coin b) (fun _ ↦ measurable_coin)

/-!
有了独立性，度的上尾界是 `hoeffding_bernoulli` 的直接推论。固定顶点 `v`，指标集取 `V \ {v}`，
变量 `u ↦ coin (s(v, u) ∈ G.edgeSet)` 是边族沿 injective（单射）映射 `u ↦ s(v, u)` 的复合（`iIndepFun.precomp`）。
陈述前面的 `open Classical in` 为随机的 `G` 经典地给出 `G.neighborSet v` 的 `Fintype` 实例，
`G.degree v` 需要它（本书把 `open … in` 写在文档注释之前）：
-/

open Classical in
/-- **固定顶点的度的集中**：记 `n = Fintype.card V`，则
`P(G.degree v ≥ (n - 1) (p + t)) ≤ exp (-2 (n - 1) t²)`。 -/
theorem degree_tail [Fintype V] (p : I) (v : V) {t : ℝ} (ht : 0 ≤ t) :
    G(V, p).real {G | ((Fintype.card V - 1 : ℕ) : ℝ) * (p + t) ≤ (G.degree v : ℝ)}
      ≤ Real.exp (-2 * ((Fintype.card V - 1 : ℕ) : ℝ) * t ^ 2) := by
  have hinj : Function.Injective fun u : V ↦ s(v, u) := fun a b hab ↦ Sym2.congr_right.1 hab
  have hind : iIndepFun (fun (u : V) (G : SimpleGraph V) ↦ coin (s(v, u) ∈ G.edgeSet))
      G(V, p) := (iIndepFun_coin_edges p).precomp hinj
  have h := hoeffding_bernoulli hind p (Finset.univ.erase v)
    (fun u hu ↦ hasLaw_coin_edge p (by
      rw [Sym2.mk_isDiag_iff]; exact (Finset.ne_of_mem_erase hu).symm)) ht
  have hsum : ∀ G : SimpleGraph V,
      ∑ u ∈ Finset.univ.erase v, coin (s(v, u) ∈ G.edgeSet) = (G.degree v : ℝ) := by
    intro G
    have hdeg : G.degree v = ((Finset.univ.erase v).filter fun u ↦ G.Adj v u).card := by
      rw [← G.card_neighborFinset_eq_degree]
      congr 1
      ext u
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_erase,
        Finset.mem_univ, and_true]
      exact ⟨fun h ↦ ⟨(G.ne_of_adj h).symm, h⟩, fun h ↦ h.2⟩
    rw [hdeg]
    calc ∑ u ∈ Finset.univ.erase v, coin (s(v, u) ∈ G.edgeSet)
        = ∑ u ∈ Finset.univ.erase v, if G.Adj v u then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun u _ ↦ by simp [coin]
      _ = _ := Finset.sum_boole _ _
  simp_rw [hsum] at h
  rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at h
  exact h

/-!
**联合界。** 想知道「**所有**顶点的度同时严格小于 `(n-1)(p + t)`」时，对 `n` 个顶点用联合界
（`Fintype` 上的特化 `measureReal_iUnion_fintype_le`；事件改写成并集用 `Set.ofPred_exists`），
失败概率至多 `n exp (-2 (n-1) t²)`。数学上它 `→ 0` 当且仅当 `2 (n-1) t² - log n → ∞`，例如
`t² = log n / n` 就够了：这就是随机图里「所有度同时集中」的第一步。
-/

open Classical in
theorem exists_degree_tail [Fintype V] (p : I) {t : ℝ} (ht : 0 ≤ t) :
    G(V, p).real {G | ∃ v, ((Fintype.card V - 1 : ℕ) : ℝ) * (p + t) ≤ (G.degree v : ℝ)}
      ≤ Fintype.card V * Real.exp (-2 * ((Fintype.card V - 1 : ℕ) : ℝ) * t ^ 2) := by
  rw [Set.ofPred_exists]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_sum fun v _ ↦ degree_tail p v ht).trans_eq ?_
  simp

end RandomGraph

/-!
## 常见错误

**1. `μ[X] = p` 里 `p` 是 `unitInterval`。** `μ[X]` 是积分，类型由等号另一边决定；右边是
`I`（`unitInterval`）时，Lean 试图在 `I` 里做积分。补救：`= (p : ℝ)`，让积分留在 `ℝ`。
-/

set_option pp.mvars false in
/--
error: Type mismatch
  X x✝
has type
  ℝ
but is expected to have type
  ↑I
---
error: failed to synthesize instance of type class
  NormedAddCommGroup ↑I

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (p : I)
    (h : μ[X] = p) : True := trivial

/-!
**2. 次高斯参数是 `ℝ≥0`，不是 `ℝ`。**
-/

set_option pp.mvars false in
/--
error: Application type mismatch: The argument
  1 / 4
has type
  ℝ
but is expected to have type
  ℝ≥0
in the application
  @HasSubgaussianMGF Ω ?_ X (1 / 4)
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) :
    HasSubgaussianMGF X (1 / 4 : ℝ) μ → True := fun _ ↦ trivial

/-!
**3. Hoeffding 引理的结论是关于中心化变量的。** `hasSubgaussianMGF_of_mem_Icc` 给的是
`HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) …`，不是 `HasSubgaussianMGF X …`；想要后者要么像
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` 那样假设 `μ[X] = 0`，要么先中心化（正确的写法见
`hoeffding_subG`）。报错末尾的 `Note: … not exposed` 是模块系统的提示（第 28 章）：比较两个类型时有些
定义（如 `Real.instAdd`）没有暴露给 importer，不能展开；它不是错误的原因，可以忽略：
-/

set_option pp.mvars false in
/--
error: Type mismatch
  hasSubgaussianMGF_of_mem_Icc hm hb
has type
  HasSubgaussianMGF (fun ω ↦ X ω - ∫ (x : Ω), X x ∂μ) ((‖1 - 0‖₊ / 2) ^ 2) μ
but is expected to have type
  HasSubgaussianMGF X (1 / 4) μ

Note: The following definitions were not unfolded because their definition is not exposed:
  Real.instAdd ↦ 1
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) :
    HasSubgaussianMGF X (1 / 4) μ := hasSubgaussianMGF_of_mem_Icc hm hb

/-!
**4. Chernoff 界的 `t` 必须非负。** 上尾版本要 `0 ≤ t`；传 `t ≤ 0` 的假设是类型错误，
下尾要用 `measure_le_le_exp_mul_mgf`（同样，`Note:` 行是模块系统的提示，可忽略）：
-/

/--
error: Application type mismatch: The argument
  ht
has type
  t ≤ 0
but is expected to have type
  0 ≤ t
in the application
  measure_ge_le_exp_mul_mgf ε ht

Note: The following definitions were not unfolded because their definition is not exposed:
  Real.instLE ↦ 2
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    (t ε : ℝ) (ht : t ≤ 0)
    (h_int : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * mgf X μ t :=
  measure_ge_le_exp_mul_mgf ε ht h_int

/-!
**5. `mgf_sum` 要 `Measurable`，`AEMeasurable` 要用 `mgf_sum₀`。**
-/

/--
error: Application type mismatch: The argument
  hZ
has type
  ∀ (i : ℕ), AEMeasurable (Z i) μ
but is expected to have type
  ∀ (i : ℕ), Measurable (Z i)
in the application
  iIndepFun.mgf_sum h hZ
-/
#guard_msgs in
example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : ℕ → Ω → ℝ) (t : ℝ)
    (h : iIndepFun Z μ) (hZ : ∀ i, AEMeasurable (Z i) μ) (s : Finset ℕ) :
    mgf (∑ i ∈ s, Z i) μ t = ∏ i ∈ s, mgf (Z i) μ t := h.mgf_sum hZ s

/-!
## 练习

练习 21.4 回到第 11 章（`div_le_iff₀`、`nlinarith`），21.8 回到第 19 章（联合界）与第 12 章
（`Finset.sum_const`），21.12 回到第 2、10、11 章（`norm_num`、`Real.add_one_le_exp`、
`pow_le_pow_left₀`），21.13 回到第 14 章（`Tendsto`）与第 17、20 章（夹逼 `squeeze_zero'`、
`squeeze_zero`），21.14 回到第 16 章（`ae`）。练习的陈述只用 Mathlib 的名字，不用本章自定义的
定理（`hoeffding` 等），解答自成一体；需要本章结论的地方，陈述里把它写成假设。
-/

section Exercises

open Filter
open scoped Topology

/-- 练习 21.1（★）：累积量母函数的缩放。`cgf (a X) t = cgf X (a t)`；`cgf` 展开成 `log (mgf …)`，
再用 `mgf_const_mul`。 -/
theorem ex_21_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (a t : ℝ) :
    cgf (fun ω ↦ a * X ω) μ t = cgf X μ (a * t) := by
  sorry

/-- 练习 21.2（★）：中心化的矩母函数。`mgf (X - m) t = mgf X t * exp (-(t m))`；
用 `mgf_add_const`（取 `a = -m`），再用 `sub_eq_add_neg`、`mul_neg` 把 `X ω + -m`、`t * -m` 改写成
陈述里的形状（`simpa [sub_eq_add_neg]` 一步完成）。这是 Hoeffding 装配里「中心化」一步的矩母函数版本。 -/
theorem ex_21_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (m t : ℝ) :
    mgf (fun ω ↦ X ω - m) μ t = mgf X μ t * Real.exp (-(t * m)) := by
  sorry

/-- 练习 21.3（★）：下尾的 Chernoff 界，参数写成 `s ≥ 0`。`P(X ≤ ε) ≤ exp (s ε) * mgf X (-s)`；
用 `measure_le_le_exp_mul_mgf`（取 `t = -s`），再用 `neg_neg` 把 `- -s * ε` 化成 `s * ε`。 -/
theorem ex_21_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    {s : ℝ} (hs : 0 ≤ s) (h_int : Integrable (fun ω ↦ Real.exp (-s * X ω)) μ) (ε : ℝ) :
    μ.real {ω | X ω ≤ ε} ≤ Real.exp (s * ε) * mgf X μ (-s) := by
  sorry

/-- 练习 21.4（★）：`t = ε / c` 确实最优。对 `c > 0` 与任意 `t`，
`-ε² / (2c) ≤ -(t ε) + c t² / 2`；先用 `div_le_iff₀` 去分母，再用 `nlinarith [sq_nonneg (c * t - ε)]`
（右边减左边乘 `2c` 恰是 `(c t - ε)²`）。 -/
theorem ex_21_4 {c : ℝ} (hc : 0 < c) (ε t : ℝ) :
    -ε ^ 2 / (2 * c) ≤ -(t * ε) + c * t ^ 2 / 2 := by
  sorry

/-- 练习 21.5（★）：次高斯变量的下尾。`P(X ≤ -ε) ≤ exp (-ε² / (2c))`；用 `HasSubgaussianMGF.neg`、
`HasSubgaussianMGF.measure_ge_le`，以及集合相等 `{ω | X ω ≤ -ε} = {ω | ε ≤ (-X) ω}`
（`Set.mem_ofPred_eq`、`Pi.neg_apply`、`linarith`）。 -/
theorem ex_21_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | X ω ≤ -ε} ≤ Real.exp (-ε ^ 2 / (2 * c)) := by
  sorry

/-- 练习 21.6（★）：次高斯参数可以放大。若 `X` 具有参数 `c` 的次高斯矩母函数且 `c ≤ c'`，则它也具有
参数 `c'` 的；用匿名构造子，可积性取 `h.integrable_exp_mul`，不等式用 `h.mgf_le`、`Real.exp_le_exp`
或 `gcongr`（先把 `c ≤ c'` 转成 `(c : ℝ) ≤ c'`，用 `exact_mod_cast`）。 -/
theorem ex_21_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) {c c' : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hcc : c ≤ c') : HasSubgaussianMGF X c' μ := by
  sorry

/-- 练习 21.7（★★）：高斯变量的尾界。`X ~ N(0, v)` 时 `P(X ≥ ε) ≤ exp (-ε² / (2v))`；
正文已有 `id` 与 `gaussianReal` 的情形，这里是一般的 `HasLaw` 版本。先证 `HasSubgaussianMGF X v P`：
可积性用 `mgf_pos_iff`（把 `0 < mgf` 变成可积）加 `mgf_gaussianReal`，
不等式 `mgf_le` 其实是等号；再用 `measure_ge_le`。 -/
theorem ex_21_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (v : ℝ≥0) (hX : HasLaw X (gaussianReal 0 v) P) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ X ω} ≤ Real.exp (-ε ^ 2 / (2 * v)) := by
  sorry

/-- 练习 21.8（★★）：联合界（实数版）。`n` 个变量各自满足 `P(Xᵢ ≥ ε) ≤ β`，则
`P(∃ i, Xᵢ ≥ ε) ≤ n β`；把事件写成并集（`Set.mem_iUnion`），用第 19 章的
`measureReal_biUnion_finset_le`（取 `Finset.univ`；或它的 `Fintype` 特化 `measureReal_iUnion_fintype_le`）、
`Finset.sum_le_sum`，最后 `simp` 算常数和。 -/
theorem ex_21_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (X : Fin n → Ω → ℝ) (ε β : ℝ) (h : ∀ i, μ.real {ω | ε ≤ X i ω} ≤ β) :
    μ.real {ω | ∃ i, ε ≤ X i ω} ≤ n * β := by
  sorry

/-- 练习 21.9（★★）：由次高斯性得到 Hoeffding。设 `Yᵢ = Xᵢ - m` 相互独立且都具有参数 `1/4` 的次高斯
矩母函数（Hoeffding 引理对 `[0, 1]` 值变量给出的参数），则 `P(∑ Xᵢ ≥ n (m + t)) ≤ exp (-2 n t²)`。
用 §4 的 `HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`（取 `c = 1/4`、`ε = n t`），事件改写用
`Finset.sum_sub_distrib`、`Finset.sum_const`；指数里 `n = 0` 要单独处理（分母为零），`n ≠ 0` 时 `field`。 -/
theorem ex_21_9 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (m : ℝ)
    (hind : iIndepFun (fun i ω ↦ X i ω - m) μ)
    (hsub : ∀ i, HasSubgaussianMGF (fun ω ↦ X i ω - m) (1 / 4) μ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (n : ℝ) * (m + t) ≤ ∑ i ∈ Finset.range n, X i ω} ≤ Real.exp (-2 * n * t ^ 2) := by
  sorry

/-- 练习 21.10（★★）：单个变量的 Hoeffding。`X` 几乎必然取值于 `[0, 1]`，则
`P(X - 𝔼X ≥ ε) ≤ exp (-2 ε²)`；用 `hasSubgaussianMGF_of_mem_Icc` 与 `measure_ge_le`，再把参数
`((‖1 - 0‖₊ / 2) ^ 2 : ℝ≥0)` 转成实数 `1/4`（`push_cast`、`Real.norm_eq_abs`、`abs_of_pos`、`norm_num`）。 -/
theorem ex_21_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 ≤ ε) : μ.real {ω | ε ≤ X ω - μ[X]} ≤ Real.exp (-2 * ε ^ 2) := by
  sorry

/-- 练习 21.11（★★）：上一题的双侧版本。`P(|X - 𝔼X| ≥ ε) ≤ 2 exp (-2 ε²)`；
事件包含于 `{ε ≤ X - 𝔼X} ∪ {ε ≤ -(X - 𝔼X)}`（`le_abs`），用 `HasSubgaussianMGF.neg`、
`measureReal_mono`、`measureReal_union_le`。 -/
theorem ex_21_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hm : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ}
    (hε : 0 ≤ ε) : μ.real {ω | ε ≤ |X ω - μ[X]|} ≤ 2 * Real.exp (-2 * ε ^ 2) := by
  sorry

/-- 练习 21.12（★★★）：Hoeffding 给出的数值界。1000 次公平抛币里正面数 `≥ 600` 的概率被
`exp (-2 · 1000 · (1/10)²)` 控制；证明这个数不超过 `1/1000000`。`norm_num` 把指数化成 `-20`；
`Real.add_one_le_exp` 取 `x = 1` 得 `2 ≤ exp 1`；`Real.exp_nat_mul` 给 `exp 20 = (exp 1) ^ 20`，
再用 `pow_le_pow_left₀`；最后 `Real.exp_neg`、`one_div` 与 `inv_le_inv₀`。 -/
theorem ex_21_12 : Real.exp (-2 * 1000 * (1 / 10 : ℝ) ^ 2) ≤ 1 / 1000000 := by
  sorry

/-- 练习 21.13（★★）：指数衰减的概率趋于零。若 `0 ≤ pₙ ≤ exp (-2 n t²)` 且 `t ≠ 0`，则 `pₙ → 0`；
先证 `n * (2 t²) → ∞`（`tendsto_natCast_atTop_atTop`、`Filter.Tendsto.atTop_mul_const`），再取负号
（`tendsto_neg_atTop_atBot`）、复合 `Real.tendsto_exp_atBot`，最后用 `squeeze_zero`。 -/
theorem ex_21_13 (p : ℕ → ℝ) {t : ℝ} (ht : t ≠ 0) (h0 : ∀ n, 0 ≤ p n)
    (h : ∀ n : ℕ, p n ≤ Real.exp (-2 * n * t ^ 2)) : Tendsto p atTop (𝓝 0) := by
  sorry

/-- 练习 21.14（★）：有上界的变量，矩母函数有上界。若 `X ≤ b` 几乎必然且 `t ≥ 0`，则
`mgf X t ≤ exp (t b)`；用 `mgf_mono_of_nonneg`（与常值函数 `fun _ ↦ b` 比较，可积性是
`integrable_const`）和 `mgf_const`。不要求 `X` 可测：若 `exp (t X)` 不可积，`mgf` 是垃圾值 `0`，
结论平凡成立（§1 的第 (4) 类）；`mgf_mono_of_nonneg` 自己处理这个分支。 -/
theorem ex_21_14 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {b t : ℝ} (hb : ∀ᵐ ω ∂μ, X ω ≤ b) (ht : 0 ≤ t) :
    mgf X μ t ≤ Real.exp (t * b) := by
  sorry

/-- 练习 21.15（★★）：单个伯努利变量的 Hoeffding。`X ~ Ber(1, 0, p)` 时 `P(X - p ≥ ε) ≤ exp (-2 ε²)`；
先证 `X` 几乎必然在 `[0, 1]` 里（`HasLaw.ae_iff`、`ae_iff`、`bernoulliMeasure_apply_of_notMem_of_notMem`，
见 §6 的 `hoeffding_bernoulli`）与 `μ[X] = p`（`HasLaw.integral_eq`、`integral_bernoulliMeasure`），
再把 `μ[X]` 换成 `p`，后面和练习 21.10 一样（`hasSubgaussianMGF_of_mem_Icc` 与 `measure_ge_le`）。 -/
theorem ex_21_15 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : I)
    (X : Ω → ℝ) (hX : HasLaw X Ber(1, 0, p) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ X ω - (p : ℝ)} ≤ Real.exp (-2 * ε ^ 2) := by
  sorry

end Exercises

/-!
## 小结

| 概念 | 语法 / 名字 | 何时用 |
|---|---|---|
| 矩母函数 | `mgf X μ t = μ[exp (t X)]`，`cgf = log ∘ mgf` | 不可积时是 `0`；正性、真实积分才要可积 |
| 变换 | `mgf_const_mul`、`mgf_add_const`、`mgf_neg`、`mgf_pos` | 化简；`mgf_neg` 给下尾 |
| 独立和 | `mgf_add'`、`mgf_sum`（`Measurable`）、`mgf_sum₀`（`AEMeasurable`） | `mgf` 化成乘积 |
| Chernoff 界 | `measure_ge_le_exp_mul_mgf`（`0 ≤ t`）、`measure_le_le_…`（`t ≤ 0`） | 再对 `t` 取最优 |
| 次高斯 | `HasSubgaussianMGF X c μ`（`c : ℝ≥0`）：`measure_ge_le`、`neg` | 打包「可积 + `mgf` 上界」 |
| Hoeffding 引理 | `hasSubgaussianMGF_of_mem_Icc`（中心化变量） | 有界变量是次高斯的 |
| Hoeffding 不等式 | `measure_sum_ge_le_of_iIndepFun`；本章 `hoeffding` | 独立有界变量和，不要求同分布 |
| 应用 | `binomial_tail`、`iIndepFun_edges`、`degree_tail`、`exists_degree_tail` | 二项分布、`G(V, p)` 的度 |
| 缺什么 | McDiarmid、Bennett、Bernstein；次高斯的 (i)–(iv) 刻画 | 自己证，或改用 Hoeffding |
-/

/-!
## 延伸阅读

- 矩母函数与 Chernoff 界：`Mathlib/Probability/Moments/Basic.lean`；解析性质与最优 `t` 的微积分
  （`deriv_cgf`）在 `Moments/MGFAnalytic.lean`，exponential tilting（指数倾斜）在 `Moments/Tilted.lean`。
- 次高斯、Hoeffding、Azuma：`Mathlib/Probability/Moments/SubGaussian.lean`（文件头列出 Vershynin 的五条
  性质 (i)–(v)：(i)–(iv) 相互等价，(v) 在 `𝔼X = 0` 时与它们等价，而且 (v) 蕴含 `𝔼X = 0`）。
- 独立性与积测度：`Mathlib/Probability/Independence/InfinitePi.lean`、
  `Mathlib/Probability/ProductMeasure.lean`。
- 随机图：`Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`；本书第 20 章（`G(V, p)` 与
  first-moment method（一阶矩方法））、第 22 章（本章 Chernoff 界的指数最优化就是 Cramér 型
  large deviations（大偏差）上界）。
- 教材：Vershynin, *High-Dimensional Probability*（Cambridge UP, 2018）第 2 章（次高斯变量与 Hoeffding
  不等式）；Boucheron–Lugosi–Massart, *Concentration Inequalities*（Oxford UP, 2013）第 2 章
  （Chernoff 方法）。章号凭记忆，未逐条核对。
-/

end Lean4Learn.Ch21

end
