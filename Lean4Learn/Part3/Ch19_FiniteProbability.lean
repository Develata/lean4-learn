module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Sym.Card
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Distributions.SetBernoulli
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 19 章　有限概率空间与概率方法

probabilistic method（概率方法）想证明「存在满足某性质的对象」：在对象的集合上放一个概率，证明随机取到
目标对象的概率为正，或者某个计数量的 expectation（期望）小于 `1`。样本空间有限时，这件事有两种等价的说法：
**对有限类型取平均** `𝔼 i, f i`（`Finset.expect`，本章简称「有限平均」，纯代数，不需要测度论）和
**uniform distribution（均匀分布）** `uniformOn Set.univ`（第 16 章；它是一个 probability measure（概率测度））。
本章把两种说法并排写出来、证明它们一致，然后用它们完整证明 Erdős 的拉姆齐数下界：存在 `n` 个顶点的图，
既没有 clique（团）也没有 independent set（独立集），具体说是没有 `k`-团和 `k`-独立集，只要 `k ≥ 3` 且
`n² ≤ 2 ^ k`。

## 学习目标
- 会读写 `𝔼 i ∈ s, f i`（`Finset.expect`），用 `Fintype.expect_eq_sum_div_card`、
  `Finset.expect_add_distrib`、`Finset.expect_sum_comm` 做期望的线性性计算。
- 会用一阶矩方法 `Finset.exists_le_of_le_expect`、`Finset.exists_lt_of_expect_lt` 一族从平均值推出存在性。
- 会用 `uniformOn Set.univ` 把概率写成基数之比（`uniformOn_apply_finset`），并证明
  `∫ f ∂uniformOn Set.univ = 𝔼 ω, f ω`，从而把两种语言互相翻译。
- 会用联合界 `measureReal_biUnion_finset_le` 与 `MeasureTheory.exists_le_integral`。
- 会把「某个模式出现的概率」归结为一个计数引理，并用它完成拉姆齐下界（把解析估计单独写成引理）。
- 会用 `setBer(u, p)` 谈随机子集，并读 `setBernoulli_real_singleton`。

## 前置知识
第 11 章（`ℝ` 上的不等式）；第 12 章（`Finset`、`Nat.choose`、`Fintype.card`、`card_filter`、`sum_boole`）；
第 16 章（`uniformOn`、`μ.real`、`integral_fintype`、`measure_biUnion_finset_le`）；第 17 章
（`IsProbabilityMeasure`、`unitInterval`、`Bin`）；第 18 章（`SimpleGraph`、`CliqueFree`、`Sym2`）。
-/

@[expose] public section

namespace Lean4Learn.Ch19

/-!
## 1. 有限平均 `𝔼`

`Finset.expect s f` 是 `f` 在有限集 `s` 上的算术平均：`(#s)⁻¹ • ∑ i ∈ s, f i`。记号 `𝔼 i ∈ s, f i`，省略
`∈ s` 就是对整个有限类型（`Finset.univ`）取平均。记号是 `scoped` 的（`Mathlib/Algebra/BigOperators/Expect.lean`
第 77 行：`scoped syntax … "𝔼 " …`），所以要先 `open scoped BigOperators`。

平均要除以 `#s`。`Finset.expect` 的定义要求值域 `M` 满足 `[AddCommMonoid M] [Module ℚ≥0 M]`：
能求和，并且 `(#s)⁻¹ : ℚ≥0`（`NNRat`，nonnegative rational numbers（非负有理数））能作为**数乘**作用在
和上（下面第一例用 `rfl` 展开的就是它）。`Module ℚ≥0 M` 说 `M` 是 `ℚ≥0` 上的 module（模；代数里的
模，与 Lean 的「模块」无关）：`ℝ` 是，`ℕ` 不是（见「常见错误」1）。

> **撞词提示。** 本章的 `𝔼 i, f i` 是 `Finset.expect`（需要 `open scoped BigOperators`）；第 17 章的
> `𝔼[X]` 是对 `volume` 的积分 `∫ a, X a`（需要 `open ProbabilityTheory`）。符号相同、含义不同。
-/

section Finitary

open scoped BigOperators

variable {ι : Type} [Fintype ι]

example (s : Finset ι) (f : ι → ℝ) : 𝔼 i ∈ s, f i = (s.card : NNRat)⁻¹ • ∑ i ∈ s, f i := rfl
example (f : ι → ℝ) : 𝔼 i, f i = (∑ i, f i) / Fintype.card ι := Fintype.expect_eq_sum_div_card f
example : 𝔼 i : Fin 3, ((i : ℕ) : ℝ) = 1 := by
  rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_three]
  norm_num

/-!
linearity of expectation（期望的线性性）：`expect_add_distrib` 是加法，`mul_expect` 是数乘，
`expect_sum_comm` 说两层「平均 + 求和」可以交换（对指标求和的期望等于期望的求和）。常数的平均是常数，
**但要求非空**：空集上的平均是 `0`（`expect_empty`，又一个 junk value（垃圾值），见第 2 章）。
-/

example (f g : ι → ℝ) : 𝔼 i, (f i + g i) = 𝔼 i, f i + 𝔼 i, g i := Finset.expect_add_distrib _ _ _
example (f : ι → ℝ) (c : ℝ) : c * 𝔼 i, f i = 𝔼 i, c * f i := Finset.mul_expect _ _ _
example {κ : Type} (s : Finset κ) (f : ι → κ → ℝ) :
    𝔼 i, ∑ j ∈ s, f i j = ∑ j ∈ s, 𝔼 i, f i j := Finset.expect_sum_comm _ _ _
example [Nonempty ι] (a : ℝ) : 𝔼 _i : ι, a = a := Fintype.expect_const a
example : 𝔼 _i : Fin 0, (1 : ℝ) = 0 := by simp

/-!
**事件的概率是指示函数的平均。** indicator function（指示函数）`if p i then 1 else 0` 的平均就是 `p` 成立的比例，
这是 `Fintype.expect_eq_sum_div_card` 加上第 12 章的 `Finset.sum_boole`：
-/

theorem expect_boole_eq (p : ι → Prop) [DecidablePred p] :
    𝔼 i, (if p i then (1 : ℝ) else 0) = (Finset.univ.filter p).card / Fintype.card ι := by
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole]

/-!
## 2. 一阶矩方法

平均值不会比所有取值都大，也不会比所有取值都小。这就是 first-moment method（一阶矩方法）的全部逻辑：
**若 `𝔼 f ≥ a`，则存在点使 `f ≥ a`**。Mathlib 的命名规则是 `exists_R_of_H`：`R` 是结论里的比较
（`le` 或 `lt`），`H` 是假设；`le_expect`、`lt_expect` 表示「`a` 在平均之下」（`a ≤ 𝔼 f`、`a < 𝔼 f`），
`expect_le`、`expect_lt` 表示「平均在 `a` 之下」。常数界的四个版本都要求 `s.Nonempty`（前四例）。
把两个平均互相比较的另有 `exists_le_of_expect_le_expect` 与 `exists_lt_of_expect_lt_expect`；后者不要
`s.Nonempty`（第五例）：空集上两个平均都是 `0`，严格不等式的假设已经排除了 `s = ∅`。
-/

section FirstMoment

variable (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (a : ℝ)

example (h : a ≤ 𝔼 i ∈ s, f i) : ∃ x ∈ s, a ≤ f x := Finset.exists_le_of_le_expect hs h
example (h : a < 𝔼 i ∈ s, f i) : ∃ x ∈ s, a < f x := Finset.exists_lt_of_lt_expect hs h
example (h : 𝔼 i ∈ s, f i ≤ a) : ∃ x ∈ s, f x ≤ a := Finset.exists_le_of_expect_le hs h
example (h : 𝔼 i ∈ s, f i < a) : ∃ x ∈ s, f x < a := Finset.exists_lt_of_expect_lt hs h
example (g : ι → ℝ) (h : 𝔼 i ∈ s, g i < 𝔼 i ∈ s, f i) : ∃ x ∈ s, g x < f x :=
  Finset.exists_lt_of_expect_lt_expect h

end FirstMoment

/-!
最常用的是 `a = 1`、`f` 取非负整数值（「坏事件的个数」）：期望小于 `1`，则存在一个点，坏事件一个也不发生。
下面把它写成一般的形式：给定一族「坏事件」`A i`，**若它们的概率之和小于 `1`，则存在一个点避开全部坏事件**。
证明的三步是：线性性把「个数的期望」换成「概率之和」，`exists_lt_of_expect_lt` 取出一个点，
再用「单项不超过总和」排除每个坏事件：
-/

theorem exists_avoid_expect {Ω κ : Type} [Fintype Ω] [Nonempty Ω] (I : Finset κ) (A : κ → Ω → Prop)
    [∀ i, DecidablePred (A i)] (h : ∑ i ∈ I, 𝔼 ω, (if A i ω then (1 : ℝ) else 0) < 1) :
    ∃ ω, ∀ i ∈ I, ¬ A i ω := by
  rw [← Finset.expect_sum_comm] at h
  -- h : (𝔼 i, ∑ j ∈ I, if A j i then 1 else 0) < 1
  obtain ⟨ω, -, hω⟩ := Finset.exists_lt_of_expect_lt Finset.univ_nonempty h
  -- hω : (∑ j ∈ I, if A j ω then 1 else 0) < 1
  refine ⟨ω, fun i hi hA ↦ ?_⟩
  -- hi : i ∈ I，hA : A i ω ⊢ False
  have h1 : (if A i ω then (1 : ℝ) else 0) ≤ ∑ j ∈ I, if A j ω then (1 : ℝ) else 0 :=
    Finset.single_le_sum (f := fun j ↦ if A j ω then (1 : ℝ) else 0)
      (fun j _ ↦ by split_ifs <;> norm_num) hi
  have h2 : (1 : ℝ) = if A i ω then 1 else 0 := by simp [hA]
  linarith

/-!
## 3. 一个计数引理：「指定的坐标取指定的值」

本章所有具体概率都来自同一个事实。样本空间是 `ι → Bool`（每个坐标 independent（独立）地、均匀地取
`true` 或 `false`），事件是「`T` 里的每个坐标都等于 `b`」：它的概率是 `(1/2) ^ #T`，其中 `#T` 是 `T` 的
cardinality（基数）。证明：满足条件的函数恰好是 `Fintype.piFinset` 里「`T` 中的坐标限制为 `{b}`，
其余不限」的那一个（第 16 章 `card_heads` 的做法），个数是 `2 ^ (card ι - #T)`；除以总数 `2 ^ card ι`。
这里需要 `DecidableEq ι`，因为 `ι → Bool` 的 `Fintype` 实例（`Pi.fintype`）要用它（见「常见错误」5）。

怎么找到这些名字：`Fintype.piFinset` 是「`Fintype`、`Pi`、`Finset`」三个词拼起来的；确认它的计数引理，
在 Mathlib 源码里 `rg "card_piFinset"` 即可。
-/

variable [DecidableEq ι]

theorem card_agree (T : Finset ι) (b : Bool) :
    (Finset.univ.filter fun c : ι → Bool ↦ ∀ i ∈ T, c i = b).card =
      2 ^ (Fintype.card ι - T.card) := by
  have h : (Finset.univ.filter fun c : ι → Bool ↦ ∀ i ∈ T, c i = b) =
      Fintype.piFinset (fun i ↦ if i ∈ T then {b} else Finset.univ) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      by_cases hi : i ∈ T
      · simp [hi, h i hi]
      · simp [hi]
    · intro h i hi
      simpa [hi] using h i
  rw [h, Fintype.card_piFinset]
  -- ⊢ ∏ i, (if i ∈ T then {b} else Finset.univ).card = 2 ^ (Fintype.card ι - T.card)
  have h2 : ∀ i, (if i ∈ T then ({b} : Finset Bool) else Finset.univ).card =
      if i ∈ T then 1 else 2 := by
    intro i
    by_cases hi : i ∈ T <;> simp [hi]
  simp only [h2]
  -- ⊢ (∏ x, if x ∈ T then 1 else 2) = 2 ^ (Fintype.card ι - T.card)
  have hc : (Finset.univ.filter fun x ↦ x ∉ T) = Tᶜ := by
    ext x
    simp
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, hc, Finset.card_compl]

theorem expect_agree (T : Finset ι) (b : Bool) :
    𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then (1 : ℝ) else 0) = (1 / 2) ^ T.card := by
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_boole, card_agree, Fintype.card_fun,
    Fintype.card_bool]
  -- ⊢ ↑(2 ^ (Fintype.card ι - T.card)) / ↑(2 ^ Fintype.card ι) = (1 / 2) ^ T.card
  obtain ⟨d, hd⟩ : ∃ d, Fintype.card ι = T.card + d :=
    ⟨Fintype.card ι - T.card, by have := Finset.card_le_univ T; omega⟩
  rw [hd, Nat.add_sub_cancel_left]
  -- ⊢ ↑(2 ^ d) / ↑(2 ^ (T.card + d)) = (1 / 2) ^ T.card
  push_cast
  rw [one_div, inv_pow, pow_add]
  field_simp

/-!
第一个应用，也是线性性的第一个完整例子：`n` 枚公平硬币的正面个数是 `∑ i, 1_{ω i = true}`，每一项
是 `T = {i}` 的情形，期望 `1/2`，所以总期望是 `n / 2`（第 16 章用积分算过同一件事）。
-/

theorem expect_heads (n : ℕ) :
    𝔼 ω : Fin n → Bool, ∑ i, (if ω i = true then (1 : ℝ) else 0) = n / 2 := by
  rw [Finset.expect_sum_comm]
  have h : ∀ i : Fin n, 𝔼 ω : Fin n → Bool, (if ω i = true then (1 : ℝ) else 0) = 1 / 2 := by
    intro i
    simpa using expect_agree ({i} : Finset (Fin n)) true
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

example : ∃ ω : Fin 5 → Bool, 5 / 2 ≤ ∑ i, (if ω i = true then (1 : ℝ) else 0) := by
  obtain ⟨ω, -, hω⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty
    (show 5 / 2 ≤ 𝔼 ω : Fin 5 → Bool, ∑ i, (if ω i = true then (1 : ℝ) else 0) by
      rw [expect_heads]; norm_num)
  exact ⟨ω, hω⟩

end Finitary

/-!
## 4. 同一件事的测度语言：`uniformOn Set.univ`

第二种写法：样本空间 `Ω` 有限非空，取 `μ = uniformOn Set.univ`。Mathlib 为它提供 `IsProbabilityMeasure`
实例（第 16 章），所以第 17 章的全套工具可用。概率是基数之比：`uniformOn_apply_finset` 在 `ℝ≥0∞` 里
给出 `#(s ∩ t) / #s`，取 `s = univ` 就是 `#A / card Ω`；再用 `ENNReal.toReal_div` 与
`ENNReal.toReal_natCast` 落回 `ℝ`（第 16 章 `prob_head` 的步骤，这次一次写成引理）。
-/

section Measure

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

example [Nonempty Ω] : IsProbabilityMeasure (uniformOn (Set.univ : Set Ω)) := inferInstance

theorem uniformOn_univ_apply_finset (A : Finset Ω) :
    uniformOn (Set.univ : Set Ω) (A : Set Ω) = (A.card : ℝ≥0∞) / (Fintype.card Ω : ℝ≥0∞) := by
  classical
  rw [← Finset.coe_univ, uniformOn_apply_finset, Finset.univ_inter, Finset.card_univ]

theorem uniformOn_univ_real_finset (A : Finset Ω) :
    (uniformOn (Set.univ : Set Ω)).real (A : Set Ω) = A.card / Fintype.card Ω := by
  rw [measureReal_def, uniformOn_univ_apply_finset, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

/-!
**两种语言一致。** 积分是加权和（`integral_fintype`），权重是每个点的概率 `1 / card Ω`，所以均匀分布下的
积分就是有限平均。于是「概率 = 指示函数的积分 = 指示函数的平均」：
-/

theorem integral_uniformOn_univ [Nonempty Ω] (f : Ω → ℝ) :
    ∫ ω, f ω ∂(uniformOn (Set.univ : Set Ω)) = 𝔼 ω, f ω := by
  rw [integral_fintype Integrable.of_finite, Fintype.expect_eq_sum_div_card, Finset.sum_div]
  -- ⊢ ∑ x, (uniformOn Set.univ).real {x} • f x = ∑ i, f i / ↑(Fintype.card Ω)
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  -- ⊢ (uniformOn Set.univ).real {x} • f x = f x / ↑(Fintype.card Ω)
  have h := uniformOn_univ_real_finset ({x} : Finset Ω)
  rw [Finset.coe_singleton, Finset.card_singleton] at h
  rw [h, smul_eq_mul]
  push_cast
  ring

theorem real_eq_expect_indicator [Nonempty Ω] (A : Set Ω) :
    (uniformOn (Set.univ : Set Ω)).real A = 𝔼 ω, A.indicator (1 : Ω → ℝ) ω := by
  rw [← integral_uniformOn_univ, integral_indicator_one (Set.toFinite A).measurableSet]

/-!
指示函数有两种写法：§1 用 `if p i then 1 else 0`，第 16、17 章用 `A.indicator 1`。`Set.indicator_apply`
说它们是同一个东西：
-/

example (A : Set Ω) (ω : Ω) [Decidable (ω ∈ A)] :
    A.indicator (1 : Ω → ℝ) ω = if ω ∈ A then 1 else 0 := by
  simp [Set.indicator_apply]

/-!
**一阶矩方法的测度版本**是 `exists_le_integral`（对任意概率测度；要求 `Integrable`）：
存在点使 `f ω ≤ ∫ f`。有限样本空间上 `Integrable.of_finite` 自动成立。在均匀分布下，它就是 §2 的
`exists_le_of_expect_le` 取 `a = 𝔼 f` 的特例：
-/

example {Ω' : Type} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ] (f : Ω' → ℝ)
    (hf : Integrable f μ) : ∃ ω, f ω ≤ ∫ ω, f ω ∂μ := exists_le_integral hf

example [Nonempty Ω] (f : Ω → ℝ) : ∃ ω, f ω ≤ ∫ ω, f ω ∂(uniformOn (Set.univ : Set Ω)) :=
  exists_le_integral Integrable.of_finite

example [Nonempty Ω] (f : Ω → ℝ) : ∃ ω, f ω ≤ 𝔼 ω, f ω := by
  rw [← integral_uniformOn_univ]
  exact exists_le_integral Integrable.of_finite

/-!
union bound（联合界）：并集的概率不超过概率之和。实数版本是 `measureReal_biUnion_finset_le`
（第 16 章的 `measure_biUnion_finset_le` 取 `ℝ≥0∞` 值）。把它翻成存在性：**坏事件的概率之和小于 `1`，
则存在点避开所有坏事件**，因为否则坏事件的并是全空间，概率为 `1`。这是 `exists_avoid_expect` 的测度版：
-/

theorem exists_avoid_measure {Ω' κ : Type} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsProbabilityMeasure μ] (I : Finset κ) (A : κ → Set Ω') (h : ∑ i ∈ I, μ.real (A i) < 1) :
    ∃ ω, ∀ i ∈ I, ω ∉ A i := by
  by_contra hne
  push Not at hne
  have hU : (⋃ i ∈ I, A i) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi, hω⟩ := hne ω
    exact ⟨i, hi, hω⟩
  have h2 := measureReal_biUnion_finset_le (μ := μ) I A
  rw [hU, probReal_univ] at h2
  linarith

end Measure

/-!
## 5. 案例（一）：拉姆齐下界的模型

**Ramsey number（拉姆齐数）** `R(k, k)` 是最小的 `n`，使得 `n` 个顶点的每个图都含 `k`-团或 `k`-独立集。
Erdős（1947）用概率方法证明：当 `k ≥ 3` 且 `n² ≤ 2 ^ k` 时存在 `n` 个顶点的图，既无 `k`-团也无
`k`-独立集。条件 `n² ≤ 2 ^ k` 等价于 `n ≤ 2 ^ (k/2)`，其中 `k/2` 是**实数**除法而不是 `ℕ` 上的整除
（见练习 19.11）；这里用 `n² ≤ 2 ^ k` 的写法，免得谈分数次幂。这样的图存在，就推出 `R(k, k) > n`：
`R(k, k) ≤ n` 会蕴含 `n` 个顶点的每个图都含 `k`-团或 `k`-独立集（多出的顶点丢掉即可）。取 `n` 为
`2 ^ (k/2)` 的整数部分，就是 `R(k, k) > 2 ^ (k/2)`。证明按下面五步，每个解析估计单独成引理：

1. **模型**：把完全图 `K_n` 的每条边独立均匀地着红色或蓝色（coloring（着色）），即样本空间
   `Sym2 (Fin n) → Bool`（对角线上的无序对 `s(a, a)` 也有颜色，但从不被用到，不影响结论）。
2. **坏事件**：对 `k` 元子集 `S` 与颜色 `b`，「`S` 的所有边都着 `b` 色」。
3. **计数引理**（§3）：`S` 有 `C(k, 2)` 条边，「这组边全取同一个颜色」的概率是 `(1/2) ^ C(k, 2)`。
4. **联合界 / 一阶矩**（§6）：坏事件共 `C(n, k) * 2` 个，概率之和 `< 1`（解析估计），故存在不含坏事件的着色。
5. **着色变图**（§6）：红边组成的图 `G` 无 `k`-团，`Gᶜ` 也无 `k`-团。

### 5.1 模型与坏事件

用 `abbrev`（可约的 `def`，实例合成会看穿它）给样本空间起名，`Fintype` 等实例才会从
`Sym2 (Fin n) → Bool` 自动传过来。`Sym2.mk.uncurry : α × α → Sym2 α` 把有序对 `(x, y)` 送到无序对
`s(x, y)`；`Mono` 的 `Decidable` 实例让 `if Mono c S b then 1 else 0`（§5.3 的指示函数）能写出来，
也让 `decide` 能对具体例子求值。
-/

/-- 完全图 `K_n` 的二着色：每个无序对一个颜色。 -/
abbrev EdgeColoring (n : ℕ) : Type := Sym2 (Fin n) → Bool

/-- 顶点集 `S` 内部的全部边：`S` 里相异两点的无序对。 -/
def edgesOf {n : ℕ} (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  S.offDiag.image Sym2.mk.uncurry

/-- `S` 是 `b` 色的单色集：`S` 内部的每条边都着 `b` 色。 -/
def Mono {n : ℕ} (c : EdgeColoring n) (S : Finset (Fin n)) (b : Bool) : Prop :=
  ∀ e ∈ edgesOf S, c e = b

instance {n : ℕ} (c : EdgeColoring n) (S : Finset (Fin n)) (b : Bool) : Decidable (Mono c S b) :=
  inferInstanceAs (Decidable (∀ e ∈ edgesOf S, c e = b))

-- 例：`{0, 1, 2}` 里相异两点的无序对共 `C(3, 2) = 3` 条边；全红着色下它是红色单色集
example : (edgesOf ({0, 1, 2} : Finset (Fin 5))).card = 3 := by decide +kernel
example : Mono (fun _ : Sym2 (Fin 5) ↦ true) ({0, 1, 2} : Finset (Fin 5)) true := by decide +kernel

/-!
`card_edgesOf` 的右边是 `Sym2.card_image_offDiag`：在 `Mathlib/Data/Sym` 里 `rg "offDiag"` 就能找到。
-/

theorem card_edgesOf {n : ℕ} (S : Finset (Fin n)) : (edgesOf S).card = S.card.choose 2 :=
  Sym2.card_image_offDiag S

theorem mem_edgesOf {n : ℕ} (S : Finset (Fin n)) (a b : Fin n) :
    s(a, b) ∈ edgesOf S ↔ a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, he⟩ := Finset.mem_image.1 h
    rw [Finset.mem_offDiag] at hxy
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hxy.1, hxy.2.1, hxy.2.2⟩
    · exact ⟨hxy.2.1, hxy.1, hxy.2.2.symm⟩
  · rintro ⟨ha, hb, hab⟩
    exact Finset.mem_image.2 ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩, rfl⟩

theorem mono_iff {n : ℕ} (c : EdgeColoring n) (S : Finset (Fin n)) (b : Bool) :
    Mono c S b ↔ ∀ a ∈ S, ∀ a' ∈ S, a ≠ a' → c s(a, a') = b := by
  constructor
  · intro h a ha a' ha' haa'
    exact h _ ((mem_edgesOf S a a').2 ⟨ha, ha', haa'⟩)
  · intro h e he
    induction e using Sym2.ind with
    | _ a a' =>
      obtain ⟨ha, ha', haa'⟩ := (mem_edgesOf S a a').1 he
      exact h a ha a' ha' haa'

/-!
### 5.2 一个坏事件的概率，两种语言

`Mono c S b` 就是 §3 的「`T = edgesOf S` 里的坐标都等于 `b`」，`#T = C(k, 2)`。有限平均版直接套
`expect_agree`；测度版先用 `real_eq_expect_indicator` 把概率化成平均，再套同一条引理：
-/

section Ramsey

open scoped BigOperators
open MeasureTheory ProbabilityTheory

theorem expect_mono {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) (b : Bool) :
    𝔼 c : EdgeColoring n, (if Mono c S b then (1 : ℝ) else 0) = (1 / 2) ^ k.choose 2 := by
  have h := expect_agree (ι := Sym2 (Fin n)) (edgesOf S) b
  rw [card_edgesOf, hS] at h
  exact h

theorem real_mono {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k) (b : Bool) :
    (uniformOn (Set.univ : Set (EdgeColoring n))).real {c | Mono c S b} =
      (1 / 2) ^ k.choose 2 := by
  rw [real_eq_expect_indicator, ← expect_mono S hS b]
  refine Finset.expect_congr rfl fun c _ ↦ ?_
  by_cases h : Mono c S b <;> simp [Set.indicator, h]

example (n : ℕ) : IsProbabilityMeasure (uniformOn (Set.univ : Set (EdgeColoring n))) :=
  inferInstance
example (n : ℕ) : MeasurableSingletonClass (EdgeColoring n) := inferInstance

/-!
上面两个 `example`：`uniformOn` 的 `IsProbabilityMeasure` 实例（`Nonempty`）与
`MeasurableSingletonClass` 实例（`Pi`，下标 `Countable`，有限当然成立，第 16 章）都由 Lean 自己找到，
`real_mono` 因此不需要任何额外假设。

### 5.3 下标集与总和

坏事件的下标是 `(S, b)`，`S` 取遍 `k` 元子集（`Finset.powersetCard`，基数 `C(n, k)`，第 12 章），
`b` 取两种颜色。两种证明共用同一个求和：
-/

/-- 坏事件的下标集：`k` 元子集配上颜色。 -/
def badIdx (n k : ℕ) : Finset (Finset (Fin n) × Bool) :=
  (Finset.powersetCard k (Finset.univ : Finset (Fin n))) ×ˢ (Finset.univ : Finset Bool)

theorem mem_badIdx {n k : ℕ} {x : Finset (Fin n) × Bool} : x ∈ badIdx n k ↔ x.1.card = k := by
  simp [badIdx, Finset.mem_powersetCard]

theorem sum_badIdx (n k : ℕ) (a : ℝ) : ∑ _x ∈ badIdx n k, a = n.choose k * (2 * a) := by
  simp only [Finset.sum_const, badIdx, Finset.card_product, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- （单色 `k` 元子集, 颜色）对的个数：一个取值于 `ℝ` 的 random variable（随机变量），由指示函数求和。
没有边的集合（`k ≤ 1`）对两种颜色都单色（下例），所以 `k ≥ 2` 时它才等于单色 `k` 元子集数。 -/
def numMono (n k : ℕ) (c : EdgeColoring n) : ℝ :=
  ∑ x ∈ badIdx n k, if Mono c x.1 x.2 then (1 : ℝ) else 0

example : Mono (fun _ : Sym2 (Fin 5) ↦ true) ({0} : Finset (Fin 5)) false := by decide +kernel

/-- 期望的线性性：`𝔼 numMono = C(n, k) * 2 * (1/2) ^ C(k, 2)`。 -/
theorem expect_numMono (n k : ℕ) :
    𝔼 c : EdgeColoring n, numMono n k c = n.choose k * (2 * (1 / 2) ^ k.choose 2) := by
  unfold numMono
  rw [Finset.expect_sum_comm, ← sum_badIdx]
  exact Finset.sum_congr rfl fun x hx ↦ expect_mono x.1 (mem_badIdx.1 hx) x.2

/-!
## 6. 案例（二）：解析估计与定理

### 6.1 解析估计

下面三个 `ℕ` 引理加一个转到 `ℝ` 的引理只涉及数的大小，没有概率。要证的是期望
`C(n, k) * 2 * (1/2) ^ C(k, 2) < 1`，即 `2 * C(n, k) < 2 ^ C(k, 2)`。条件 `n ^ 2 ≤ 2 ^ k` 让我们不必谈
分数次幂。只用 `Nat.choose_le_pow : C(n, k) ≤ n ^ k` 不够：`n = 16`、`k = 8` 时 `n ^ k = 2 ^ 32`，
而 `2 ^ C(8, 2) = 2 ^ 28`；必须保留分母 `k!`，用 `k! * C(n, k) ≤ n ^ k`（`Nat.descFactorial_le_pow`）。
两边平方后，`(n ^ k) ^ 2 = (n ^ 2) ^ k ≤ 2 ^ (k * k)`，而 `k * k = k + 2 * C(k, 2)`；
还差 `4 * 2 ^ k < (k!) ^ 2`。

**引理 1（阶乘）：** `k ≥ 3` 时 `4 * 2 ^ k < (k!) ^ 2`。归纳，底是 `32 < 36`，每步乘 `(k + 1) ^ 2 ≥ 2`。
-/

example (n k : ℕ) : n.choose k ≤ n ^ k := Nat.choose_le_pow n k

theorem four_mul_two_pow_lt (k : ℕ) (hk : 3 ≤ k) : 4 * 2 ^ k < k.factorial ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide -- ⊢ 4 * 2 ^ 3 < Nat.factorial 3 ^ 2
  | succ k hk ih =>
    -- ih : 4 * 2 ^ k < k.factorial ^ 2
    -- ⊢ 4 * 2 ^ (k + 1) < (k + 1).factorial ^ 2
    have h : 2 ≤ (k + 1) ^ 2 := by nlinarith
    calc 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by ring
      _ < 2 * k.factorial ^ 2 := by omega
      _ ≤ (k + 1) ^ 2 * k.factorial ^ 2 := Nat.mul_le_mul_right _ h
      _ = (k + 1).factorial ^ 2 := by rw [Nat.factorial_succ]; ring

/-- **引理 2（纯算术）：** `F * C ≤ N`、`N² ≤ P * B²`、`4P < F²`、`0 < B` 推出 `2 * C < B`。
假设反面 `B ≤ 2C`，得到 `F²B² ≤ 4(FC)² ≤ 4N² ≤ 4PB² < F²B²`。 -/
theorem aux_lt (F C N P B : ℕ) (hFC : F * C ≤ N) (hN : N ^ 2 ≤ P * B ^ 2) (hF : 4 * P < F ^ 2)
    (hB : 0 < B) : 2 * C < B := by
  by_contra h
  push Not at h
  have h1 : F ^ 2 * B ^ 2 ≤ F ^ 2 * (2 * C) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
  have h2 : (F * C) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hFC 2
  have h3 : 4 * P * B ^ 2 < F ^ 2 * B ^ 2 := Nat.mul_lt_mul_of_pos_right hF (by positivity)
  nlinarith

/-- **引理 3（拉姆齐的计数不等式）：** `k ≥ 3`、`n² ≤ 2 ^ k` 推出 `2 * C(n, k) < 2 ^ C(k, 2)`。 -/
theorem choose_mul_two_lt (n k : ℕ) (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ k.choose 2 := by
  have h1 : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  have h3 : k.choose 2 * 2 + k = k * k := by
    rw [Nat.choose_two_right, Nat.div_mul_cancel (Nat.even_mul_pred_self k).two_dvd]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  have h2 : (n ^ k) ^ 2 ≤ 2 ^ k * (2 ^ k.choose 2) ^ 2 := by
    calc (n ^ k) ^ 2 = (n ^ 2) ^ k := by ring
      _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hn k
      _ = 2 ^ (k * k) := (pow_mul 2 k k).symm
      _ = 2 ^ (k + k.choose 2 * 2) := by rw [← h3, add_comm]
      _ = 2 ^ k * (2 ^ k.choose 2) ^ 2 := by rw [pow_add, pow_mul]
  exact aux_lt _ _ _ _ _ h1 h2 (four_mul_two_pow_lt k hk) (by positivity)

/-- 同一个不等式写成实数形式：期望 `< 1`。 -/
theorem expected_lt_one {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    (n.choose k : ℝ) * (2 * (1 / 2) ^ k.choose 2) < 1 := by
  have h : (2 * n.choose k : ℝ) < 2 ^ k.choose 2 := by exact_mod_cast choose_mul_two_lt n k hk hn
  have hp : (0 : ℝ) < 2 ^ k.choose 2 := by positivity
  have e : (n.choose k : ℝ) * (2 * (1 / 2) ^ k.choose 2) = 2 * n.choose k / 2 ^ k.choose 2 := by
    rw [one_div, inv_pow]
    ring
  rwa [e, div_lt_one hp]

/-!
### 6.2 两个证明

有限平均的证明：`exists_avoid_expect` 加上 `expect_mono` 与 `sum_badIdx` 算出的同一个求和；
测度的证明：`exists_avoid_measure` 加上 `real_mono`。两个证明的骨架完全一样，只是「概率之和」在第一个里是
`∑ 𝔼 (指示函数)`，在第二个里是 `∑ μ.real (事件)`；`real_eq_expect_indicator` 保证它们是同一个数。
-/

theorem ramsey_finitary {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    ∃ c : EdgeColoring n, ∀ S : Finset (Fin n), S.card = k → ∀ b, ¬ Mono c S b := by
  obtain ⟨c, hc⟩ := exists_avoid_expect (badIdx n k)
    (fun (x : Finset (Fin n) × Bool) (c : EdgeColoring n) ↦ Mono c x.1 x.2) (by
      have h : ∑ x ∈ badIdx n k, 𝔼 c : EdgeColoring n, (if Mono c x.1 x.2 then (1 : ℝ) else 0) =
          ∑ _x ∈ badIdx n k, (1 / 2 : ℝ) ^ k.choose 2 :=
        Finset.sum_congr rfl fun x hx ↦ expect_mono x.1 (mem_badIdx.1 hx) x.2
      rw [h, sum_badIdx]
      exact expected_lt_one hk hn)
  -- hc : ∀ i ∈ badIdx n k, ¬Mono c i.1 i.2
  exact ⟨c, fun S hS b ↦ hc (S, b) (mem_badIdx.2 hS)⟩

theorem ramsey_measure {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    ∃ c : EdgeColoring n, ∀ S : Finset (Fin n), S.card = k → ∀ b, ¬ Mono c S b := by
  obtain ⟨c, hc⟩ := exists_avoid_measure (uniformOn (Set.univ : Set (EdgeColoring n)))
    (badIdx n k) (fun x ↦ {c : EdgeColoring n | Mono c x.1 x.2}) (by
      have h : ∑ x ∈ badIdx n k,
          (uniformOn (Set.univ : Set (EdgeColoring n))).real {c | Mono c x.1 x.2} =
          ∑ _x ∈ badIdx n k, (1 / 2 : ℝ) ^ k.choose 2 :=
        Finset.sum_congr rfl fun x hx ↦ real_mono x.1 (mem_badIdx.1 hx) x.2
      rw [h, sum_badIdx]
      exact expected_lt_one hk hn)
  exact ⟨c, fun S hS b hb ↦ hc (S, b) (mem_badIdx.2 hS) hb⟩

/-!
### 6.3 回到图

红边（颜色 `true` 的无序对）组成图 `colorGraph c`（`SimpleGraph.fromEdgeSet`，第 18 章）。
`k`-团是 `k` 个两两相邻的顶点，于是 `colorGraph c` 的团一定是红色单色集，补图的团一定是蓝色单色集
（这是下面 `cliqueFree_of_noMono` 用到的方向；反方向也对，但不需要）。
-/

/-- 红边组成的图。 -/
def colorGraph {n : ℕ} (c : EdgeColoring n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | c e = true}

theorem cliqueFree_of_noMono {n k : ℕ} (c : EdgeColoring n)
    (h : ∀ S : Finset (Fin n), S.card = k → ∀ b, ¬ Mono c S b) :
    (colorGraph c).CliqueFree k ∧ (colorGraph c)ᶜ.CliqueFree k := by
  constructor
  · intro S hS
    refine h S hS.card_eq true ?_
    rw [mono_iff]
    intro a ha a' ha' haa'
    have hadj := hS.isClique ha ha' haa'
    simp only [colorGraph, SimpleGraph.fromEdgeSet_adj] at hadj
    exact hadj.1
  · intro S hS
    refine h S hS.card_eq false ?_
    rw [mono_iff]
    intro a ha a' ha' haa'
    have hadj := hS.isClique ha ha' haa'
    simp only [SimpleGraph.compl_adj, colorGraph, SimpleGraph.fromEdgeSet_adj] at hadj
    cases hc : c s(a, a') with
    | false => rfl
    | true => exact absurd ⟨hc, haa'⟩ hadj.2

/-- **Erdős 的拉姆齐下界。** `k ≥ 3` 且 `n² ≤ 2 ^ k` 时，存在 `n` 个顶点的图，
既没有 `k`-团，补图也没有 `k`-团（即没有 `k`-独立集）。因此 `R(k, k) > n`。 -/
theorem ramsey_graph {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
  obtain ⟨c, hc⟩ := ramsey_finitary hk hn
  exact ⟨colorGraph c, cliqueFree_of_noMono c hc⟩

-- `k = 6`：`8² = 64 = 2 ^ 6`，所以 8 个顶点的图可以既无 6-团也无 6-独立集
example : ∃ G : SimpleGraph (Fin 8), G.CliqueFree 6 ∧ Gᶜ.CliqueFree 6 :=
  ramsey_graph (by norm_num) (by norm_num)

end Ramsey

/-!
## 7. 随机子集：`setBer`

上面的模型只有 `p = 1/2`。第 20 章的 `G(V, p)` 里每条边独立地以概率 `p` 入选，一般的 `p` 要用
`setBer(u, p)`（`ProbabilityTheory.setBernoulli u p`，`scoped` 记号，需要 `open ProbabilityTheory`）：
它是 `Set ι` 上的测度，`u` 里的每个元素独立地以概率 `p` 入选，`p : unitInterval`。对有限的 `u`，单点集的概率是
`setBernoulli_real_singleton : setBer(u, p).real {s} = p ^ s.ncard * (1 - p) ^ (u \ s).ncard`
（`s ⊆ u`，`u.Finite`）。取 `p = 1/2`、`u = Set.univ`，每个子集的概率是 `(1/2) ^ n`，和 `Set (Fin n)` 上的
均匀分布在每个单点集上一致：所以前面的均匀模型就是 `p = 1/2` 的独立模型。

`unitInterval` 是子类型 `Set.Icc 0 1`（第 17 章），不能直接把 `1 / 2` 当作它的元素，要手写成
`⟨1 / 2, 证明⟩`，证明是 `0 ≤ 1/2 ∧ 1/2 ≤ 1`：
-/

section RandomSubset

open MeasureTheory ProbabilityTheory

/-- 一枚公平硬币的偏置 `1/2 : unitInterval`。 -/
noncomputable def half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

example (n : ℕ) : IsProbabilityMeasure (setBer((Set.univ : Set (Fin n)), half)) := inferInstance

/-- `↑half` 是子类型的第一投影，按定义就是 `1 / 2`，所以 `rfl` 成立。 -/
theorem coe_half : ((half : unitInterval) : ℝ) = 1 / 2 := rfl

theorem setBer_half_real_singleton (n : ℕ) (s : Set (Fin n)) :
    (setBer((Set.univ : Set (Fin n)), half)).real {s} = (1 / 2) ^ n := by
  rw [setBernoulli_real_singleton half (Set.subset_univ s) Set.finite_univ]
  have h2 : (1 - (half : ℝ)) = 1 / 2 := by rw [coe_half]; norm_num
  rw [h2, coe_half, ← pow_add, add_comm, Set.ncard_sdiff_add_ncard_of_subset (Set.subset_univ s),
    Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- 公平的 `setBer` 与 `Set (Fin n)` 上的均匀分布，在每个单点集上给出同样的概率。 -/
theorem setBer_half_eq_uniform (n : ℕ) (s : Set (Fin n)) :
    (setBer((Set.univ : Set (Fin n)), half)).real {s} =
      (uniformOn (Set.univ : Set (Set (Fin n)))).real {s} := by
  have h := uniformOn_univ_real_finset ({s} : Finset (Set (Fin n)))
  rw [Finset.coe_singleton, Finset.card_singleton, Fintype.card_set, Fintype.card_fin] at h
  rw [setBer_half_real_singleton, h]
  push_cast
  rw [one_div_pow]

/-!
`setBer(u, p).map Set.ncard` 是「被选中元素个数」的分布。Mathlib 给出它在单点 `k` 处的值
`map_ncard_setBernoulli_real_singleton : (setBer(u, p).map Set.ncard).real {k} =
C(u.ncard, k) * p ^ k * (1 - p) ^ (u.ncard - k)`（`u.Finite`）：这就是 binomial distribution（二项分布）
的概率，`n = u.ncard`（第 17 章的 `Bin(n, p)`）。例：3 个元素里恰好选中 1 个的概率是
`3 * (1/2)^1 * (1/2)^2 = 3/8`：
-/

example : (setBer((Set.univ : Set (Fin 3)), half).map Set.ncard).real {1} = 3 / 8 := by
  rw [map_ncard_setBernoulli_real_singleton Set.finite_univ]
  norm_num [half]

end RandomSubset

/-!
## 常见错误

**1. 在 `ℕ` 上取平均。** `𝔼` 要求值域是 `ℚ≥0`-模，`ℕ` 不是（平均值不一定是自然数）。先转到 `ℝ`：
-/

/--
error: failed to synthesize instance of type class
  Module ℚ≥0 ℕ

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
open scoped BigOperators in
example : 𝔼 i : Fin 2, (i : ℕ) = 0 := sorry

/-!
**2. 记错一阶矩引理的名字。** 引理叫 `exists_le_of_le_expect`，不是 `exists_le_expect`：
-/

/--
error: Unknown constant `Finset.exists_le_expect`
-/
#guard_msgs in
open scoped BigOperators in
example (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) (a : ℝ) (h : a ≤ 𝔼 i ∈ s, f i) :
    ∃ x ∈ s, a ≤ f x := Finset.exists_le_expect hs h

/-!
**3. 记错一阶矩引理的方向。** `exists_le_of_le_expect` 的假设是「下界 `≤` 平均」；要从「平均 `≤` 上界」
出发，用 `exists_le_of_expect_le`。下面的报错末尾有一行 `Note: … not exposed`，这是模块系统的附注：
Lean 想展开 `Real.instLE` 来判断两个不等式是否相同，但它的定义体没有 `@[expose]`，不能展开
（见第 1 章第 8 节）。错误本身的原因仍是方向写反。
-/

/--
error: Application type mismatch: The argument
  h
has type
  𝔼 i ∈ s, f i ≤ a
but is expected to have type
  a ≤ 𝔼 i ∈ s, f i
in the application
  Finset.exists_le_of_le_expect hs h

Note: The following definitions were not unfolded because their definition is not exposed:
  Real.instLE ↦ 4
-/
#guard_msgs in
open scoped BigOperators in
example (s : Finset ℕ) (hs : s.Nonempty) (f : ℕ → ℝ) (a : ℝ) (h : 𝔼 i ∈ s, f i ≤ a) :
    ∃ x ∈ s, a ≤ f x := Finset.exists_le_of_le_expect hs h

/-!
**4. 空样本空间上的均匀分布不是概率测度。** `uniformOn Set.univ` 的概率测度实例需要 `Nonempty`
（空集上没有概率可分）；`Fin 0` 没有元素，Lean 找不到实例：
-/

/--
error: failed to synthesize instance of type class
  MeasureTheory.IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : MeasureTheory.IsProbabilityMeasure
    (ProbabilityTheory.uniformOn (Set.univ : Set (Fin 0))) := inferInstance

/-!
**5. 忘了 `DecidableEq`。** `ι → Bool` 的 `Fintype` 实例需要 `ι` 上的判等（§3），只有 `Fintype ι` 不够：
-/

/--
error: failed to synthesize instance of type class
  Fintype (ι → Bool)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {ι : Type} [Fintype ι] : Fintype (ι → Bool) := inferInstance

/-!
**6. 把概率写在 `ℕ` 里。** `(1 / 2 : ℕ)` 是整除，等于 `0`（第 2 章的垃圾值），`(1/2) ^ n` 悄悄变成
`0 ^ n`，Lean 不报错。本章的概率一律写在 `ℝ` 里（`(1 / 2 : ℝ) ^ 3 = 1 / 8`）：
-/

example : (1 / 2 : ℕ) ^ 3 = 0 := by norm_num

/-!
## 练习

练习大致按节的顺序。重温前面章节的有：19.1（第 12 章的 `Fin` 求和）、19.7（第 18 章的 `CliqueFree`）、
19.9（第 17 章的马尔可夫不等式，这里是有限版本）、19.10（第 12 章的 `Nat.choose`）、19.11（第 11 章的实数
不等式）。19.6、19.8 复习本章 §4。19.13、19.14 用到本章的引理，提示里把引理的陈述写出来；答案文件不导入
章节文件，所以在那里把它们重新证明。
-/

section Exercises

open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- 练习 19.1（★）：`Fin 4` 上 `i.val` 的平均是 `3 / 2`（§1）。用 `Fintype.expect_eq_sum_div_card` 与
`Fin.sum_univ_four`（第 12 章 `Fin.sum_univ_three` 的四元素版本），最后 `norm_num`。 -/
theorem ex_19_1 : 𝔼 i : Fin 4, ((i : ℕ) : ℝ) = 3 / 2 := by sorry

/-- 练习 19.2（★）：期望的线性性（§1）。用 `Finset.expect_add_distrib` 与 `Finset.mul_expect`。 -/
theorem ex_19_2 {ι : Type} [Fintype ι] (f g : ι → ℝ) :
    𝔼 i, (f i + 2 * g i) = 𝔼 i, f i + 2 * 𝔼 i, g i := by sorry

/-- 练习 19.3（★）：平均值夹在最小值与最大值之间（§2）：既有点不超过平均，也有点不低于平均。
用 `Finset.exists_le_of_expect_le` 与 `Finset.exists_le_of_le_expect`，`s := Finset.univ`。 -/
theorem ex_19_3 {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∃ i, f i ≤ 𝔼 j, f j) ∧ ∃ i, 𝔼 j, f j ≤ f i := by sorry

/-- 练习 19.4（★）：两个函数之和的一阶矩（§2）：存在点使 `f i + g i` 不超过两个平均之和。
先用线性性把右端写成 `𝔼 j, (f j + g j)`。 -/
theorem ex_19_4 {ι : Type} [Fintype ι] [Nonempty ι] (f g : ι → ℝ) :
    ∃ i, f i + g i ≤ 𝔼 j, f j + 𝔼 j, g j := by sorry

/-- 练习 19.5（★★）：有限平均版的联合界（§1）：并事件的指示函数不超过两个指示函数之和，
再用 `Finset.expect_le_expect` 与 `Finset.expect_add_distrib`。 -/
theorem ex_19_5 {ι : Type} [Fintype ι] (p q : ι → Prop) [DecidablePred p] [DecidablePred q] :
    𝔼 i, (if p i ∨ q i then (1 : ℝ) else 0) ≤
      𝔼 i, (if p i then (1 : ℝ) else 0) + 𝔼 i, (if q i then (1 : ℝ) else 0) := by sorry

/-- 练习 19.6（★★）：均匀分布下的积分就是概率（§4）。三枚公平硬币里第一枚是正面的概率是 `1/2`，
写成积分：指示函数 `if ω 0 = true then 1 else 0` 关于 `uniformOn Set.univ` 的积分是 `1/2`。
提示：先用 `integral_uniformOn_univ`（`∫ ω, f ω ∂uniformOn Set.univ = 𝔼 ω, f ω`）换成有限平均，
再用 `expect_agree`（`𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then 1 else 0) = (1/2) ^ #T`），
取 `T = {0}`。 -/
theorem ex_19_6 :
    ∫ ω : Fin 3 → Bool, (if ω 0 = true then (1 : ℝ) else 0)
      ∂(uniformOn (Set.univ : Set (Fin 3 → Bool))) = 1 / 2 := by
  sorry

/-- 练习 19.7（★）：`5` 个顶点的图没有 `6`-团，补图也没有（§6.3，第 18 章）。
用 `SimpleGraph.cliqueFree_of_card_lt` 与 `Fintype.card_fin`。 -/
theorem ex_19_7 (G : SimpleGraph (Fin 5)) : G.CliqueFree 6 ∧ Gᶜ.CliqueFree 6 := by sorry

/-- 练习 19.8（★）：均匀分布下的一阶矩，另一个方向（§4）：存在点使 `f ω` 不小于积分。
用 `exists_integral_le`（与 `exists_le_integral` 成对）与 `Integrable.of_finite`。 -/
theorem ex_19_8 {Ω : Type} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (f : Ω → ℝ) : ∃ ω, ∫ ω, f ω ∂(uniformOn (Set.univ : Set Ω)) ≤ f ω := by sorry

/-- 练习 19.9（★★）：有限样本空间上的马尔可夫不等式（§1）。非负函数 `f`，任意实数 `a`：
`a * P(f ≥ a) ≤ 𝔼 f`。用 `Finset.mul_expect` 与 `Finset.expect_le_expect`，逐点 `split_ifs`。 -/
theorem ex_19_9 {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (a : ℝ) :
    a * 𝔼 i, (if a ≤ f i then (1 : ℝ) else 0) ≤ 𝔼 i, f i := by sorry

/-- 练习 19.10（★）：拉姆齐下界在 `n = 16`、`k = 8` 时的数值验证（§6.1）：`16² = 2 ^ 8`，
`2 * C(16, 8) < 2 ^ C(8, 2)`。用 `decide +kernel`（第 5 章）。 -/
theorem ex_19_10 : 2 * Nat.choose 16 8 < 2 ^ Nat.choose 8 2 := by sorry

/-- 练习 19.11（★★）：`n ≤ 2 ^ (k / 2)` 与 `n ^ 2 ≤ 2 ^ k` 等价（§5 开头）。右边的 `2 ^ (k / 2)` 是实数
幂 `Real.rpow`，`k / 2` 是实数除法。提示：先证 `(2 ^ ((k : ℝ) / 2)) ^ 2 = 2 ^ k`
（`Real.rpow_natCast`、`Real.rpow_mul`，这两个名字是新的，用 `rw [← Real.rpow_natCast]` 的方向把 `^ 2`
变成实数幂再合并），再用第 11 章的 `sq_le_sq₀`（两边非负时 `a ^ 2 ≤ b ^ 2 ↔ a ≤ b`）。 -/
theorem ex_19_11 (n k : ℕ) : ((n : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2)) ↔ n ^ 2 ≤ 2 ^ k := by sorry

/-- 练习 19.12（★）：`setBer(u, p)` 取到空集的概率是 `(1 - p) ^ u.ncard`（§7）。用
`setBernoulli_real_singleton`，`p ^ 0 = 1`，`u \ ∅ = u`（`Set.diff_empty`），`Set.ncard_empty`。 -/
theorem ex_19_12 (u : Set (Fin 5)) (p : unitInterval) :
    (setBer(u, p)).real {∅} = (1 - p : ℝ) ^ u.ncard := by sorry

/-- 练习 19.13（★★）：坐标集不相交的两个事件在均匀平均下独立（§3，`expect_agree`）。
`T` 与 `U` 不相交时，「`T` 全取 `b`」与「`U` 全取 `b`」的指示函数乘积的平均等于平均的乘积。
提示：两个条件合起来就是「`T ∪ U` 全取 `b`」（`Finset.forall_mem_union`），三次用
`expect_agree`（`𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then 1 else 0) = (1/2) ^ #T`），
基数用 `Finset.card_union_of_disjoint`。拉姆齐问题里算单色集个数的协方差时，第一步就是它。 -/
theorem ex_19_13 {ι : Type} [Fintype ι] [DecidableEq ι] (T U : Finset ι) (hTU : Disjoint T U)
    (b : Bool) :
    𝔼 c : ι → Bool, (if (∀ i ∈ T, c i = b) ∧ (∀ i ∈ U, c i = b) then (1 : ℝ) else 0) =
      (𝔼 c : ι → Bool, if ∀ i ∈ T, c i = b then (1 : ℝ) else 0) *
        𝔼 c : ι → Bool, if ∀ i ∈ U, c i = b then (1 : ℝ) else 0 := by sorry

/-- 练习 19.14（★★★）：存在长为 20 的 0-1 序列，其中任何 6 个相邻位置都不全相同（概率方法的联合界）。
坏事件 `A (i, b)`：位置 `i, …, i + 5` 全取 `b`，共 `15 * 2 = 30` 个，每个概率 `(1/2) ^ 6`，总和 `30/64 < 1`。
用 `exists_avoid_expect`（`∑ i ∈ I, 𝔼 ω, (if A i ω then 1 else 0) < 1` 推出 `∃ ω, ∀ i ∈ I, ¬ A i ω`）
和 `expect_agree`（`𝔼 c : ι → Bool, (if ∀ i ∈ T, c i = b then 1 else 0) = (1/2) ^ #T`）；窗口写成
`T i := Finset.univ.filter fun j : Fin 20 ↦ i.val ≤ j.val ∧ j.val < i.val + 6`，
`(T i).card = 6` 可以对 `i : Fin 15` 用 `decide +kernel`。答案文件先证了一个一般的引理（`#I` 个窗口，
每个窗口大小为 `m`，`#I * (1/2) ^ m < 1`，则存在函数避开全部窗口），再套用它。 -/
theorem ex_19_14 : ∃ ω : Fin 20 → Bool, ∀ i : Fin 15, ∀ b : Bool,
    ¬ ∀ j : Fin 20, i.val ≤ j.val → j.val < i.val + 6 → ω j = b := by sorry

/-- 练习 19.15（★★）：`4` 个元素的随机子集恰有 `2` 个元素的概率是 `6 * p ^ 2 * (1 - p) ^ 2`
（§7，二项分布）。用 `map_ncard_setBernoulli_real_singleton`（`u.Finite`）、`Set.ncard_univ`，
`Nat.choose 4 2 = 6` 用 `decide`。 -/
theorem ex_19_15 (p : unitInterval) :
    (setBer((Set.univ : Set (Fin 4)), p).map Set.ncard).real {2} =
      6 * (p : ℝ) ^ 2 * (1 - p : ℝ) ^ 2 := by sorry

end Exercises

/-!
## 小结

| 概念 | 写法 | 何时用 |
|---|---|---|
| 有限平均 | `𝔼 i ∈ s, f i`、`Fintype.expect_eq_sum_div_card` | 纯有限的概率方法（`open scoped BigOperators`） |
| 期望的线性性 | `Finset.expect_add_distrib`、`mul_expect`、`expect_sum_comm` | 把计数量拆成指示函数之和 |
| 空平均与常数 | `expect_empty`（`= 0`）、`Fintype.expect_const`（要 `Nonempty`） | 防止把空集当作有定义的平均 |
| 事件的概率 | `expect_boole_eq`、`real_eq_expect_indicator` | 概率 = 指示函数的平均 |
| 一阶矩方法（有限） | `Finset.exists_le_of_le_expect`、`exists_lt_of_expect_lt` 一族（要 `Nonempty`） | 从平均值推存在性 |
| 一阶矩方法（测度） | `MeasureTheory.exists_le_integral`、`exists_integral_le` | 概率测度下的同一句话 |
| 均匀分布 | `uniformOn Set.univ`、`uniformOn_apply_finset`、`integral_fintype` | 样本空间有限非空 |
| 两种语言一致 | `integral_uniformOn_univ : ∫ f ∂uniformOn univ = 𝔼 ω, f ω` | 在两种写法之间翻译 |
| 联合界 | `measureReal_biUnion_finset_le`、`exists_avoid_measure/expect` | 坏事件概率之和 `< 1` ⟹ 存在避开者 |
| 「坐标取定值」计数 | `card_agree`、`expect_agree : 𝔼 = (1/2)^#T` | 具体事件的概率 |
| 拉姆齐下界 | `ramsey_graph : k ≥ 3 → n² ≤ 2^k → ∃ G, G.CliqueFree k ∧ Gᶜ.CliqueFree k` | 概率方法的标准案例 |
| 随机子集 | `setBer(u, p)`、`setBernoulli_real_singleton` | 每个元素独立入选 |
-/

/-!
## 延伸阅读

- Mathlib 源码：`Mathlib/Algebra/BigOperators/Expect.lean`（`𝔼`、线性性）、
  `Mathlib/Algebra/Order/BigOperators/Expect.lean`（`exists_le_of_le_expect` 一族）、
  `Mathlib/Probability/UniformOn.lean`（`uniformOn`、`uniformOn_apply_finset`）、
  `Mathlib/MeasureTheory/Integral/Average.lean` 的「First moment method」一节（`exists_le_integral`）、
  `Mathlib/Probability/Distributions/SetBernoulli.lean`（`setBer`）。
- v4.35.0 的本地 Mathlib 里没有拉姆齐数的概率下界，也没有图的拉姆齐定理：`rg -i ramsey` 的数学内容只
  命中 `Combinatorics/Hindman.lean`、`Combinatorics/HalesJewett.lean`（拉姆齐型的组合定理）和
  `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`（Erdős–Szekeres，序列定理），其余命中是
  Hopf 代数文件里的人名；`Archive/Wiedijk100Theorems/BirthdayProblem.lean` 是同一模型
  （`Fin n → Fin m` 上的均匀分布）的官方范例。
- Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947)；
  Alon–Spencer, *The Probabilistic Method*, 第 1 章（基本方法，含 `R(k, k) > ⌊2^{k/2}⌋`，`k ≥ 3`）。
- 本书：第 16 章（`uniformOn`、`integral_fintype`）、第 17 章（`Bin`）、第 18 章
  （`CliqueFree`）、第 20 章（把同样的一阶矩论证搬到 `SimpleGraph.binomialRandom` 上，边有概率 `p`）。
-/

end Lean4Learn.Ch19

end
