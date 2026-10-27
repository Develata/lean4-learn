module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Finiteness
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Measurability
public import Mathlib.Tactic.NormNum

/-!
# 第 16 章　测度论基础

概率论的对象在 Mathlib 里都是测度论的对象：事件是 measurable set（可测集），random variable（随机变量）
是 measurable function（可测函数），概率是 measure（测度）的值，expectation（期望）是积分。本章一次讲完
这套语言（可测性、`Measure` 与 `ℝ≥0∞`、`∀ᵐ`、常用测度、`∫⁻` 与 `∫`），最后在 `Fin n → Bool`（抛硬币）
上全部用一遍。读完后你能读懂第 17–22 章的陈述，也能自己证明「某个集合可测」「某个测度不等式」
「某个有限空间上的概率」这三类最常见的小引理。

## 学习目标
- 会用 `MeasurableSet.compl/union/inter/iUnion` 与离散、Borel、积三类内置 σ-代数；认识 `setOfPred`。
- 会用 `fun_prop` 与 `measurability` 证可测性，并知道各自能证什么、不能证什么。
- 会用 `measure_mono`、`measure_union_le`、带可测性假设的 `measure_union`、`finiteness`。
- 会处理 `ℝ≥0∞`：认识 `∞ - ∞ = 0`、`toReal ∞ = 0`、`0⁻¹ = ∞` 这些 junk value（垃圾值），会用 `μ.real`。
- 会读写 `∀ᵐ x ∂μ, p x`、`f =ᵐ[μ] g`；认识 `Measure.dirac/count/map/pi`、`volume`、`uniformOn`。
- 会用 `∫⁻` 与 `∫`（`Integrable`、`MemLp`、积分的线性性、有限空间上的 `integral_fintype`）。
- 会在 `Fin (n + 1) → Bool` 上算出「第 `i` 枚硬币是正面」的概率 `1/2` 与正面个数的期望 `(n + 1) / 2`。

## 前置知识
第 7 章（集合、原像、`Set.ofPred`）；第 8 章（类型类实例、`ℝ`、强制转换 `↑`）；第 10 章（`fun_prop`、
`measurability`、`finiteness` 的一行速览，本章展开）；第 11 章（`ℝ` 上的不等式）；第 12 章（`Finset`、
`Fintype.card`、`∑ i ∈ s`）；第 14 章（滤子、`∀ᶠ`、`filter_upwards`：`∀ᵐ` 就是沿「几乎处处」滤子最终成立）。
-/

@[expose] public section

namespace Lean4Learn.Ch16

/-!
## 1. σ-代数：`MeasurableSpace` 与 `MeasurableSet`

测度论从一个集合族开始：σ-algebra（σ-代数）是 `α` 的一族子集，含全集，对补集和可数并封闭。
Mathlib 把「选定一个 σ-代数」做成类型类 `MeasurableSpace α`，即 measurable space（可测空间），
其中的集合叫可测集，谓词是 `MeasurableSet s`。它是类型的**附加结构**，像第 8 章的 `Group G`：
Mathlib 对每个常用类型选定一个典范实例，`MeasurableSet` 靠实例找到 σ-代数，所以不带参数。
-/

section Main

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

example : MeasurableSet (∅ : Set α) := MeasurableSet.empty
example : MeasurableSet (Set.univ : Set α) := MeasurableSet.univ
example (s : Set α) (hs : MeasurableSet s) : MeasurableSet sᶜ := hs.compl
example (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) : MeasurableSet (s ∪ t) :=
  hs.union ht
example (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) : MeasurableSet (s ∩ t) :=
  hs.inter ht

/-!
可数并是 σ-代数的公理，所以 `MeasurableSet.iUnion` 要求指标类型 `Countable`（任意并一般不可测）；
`biUnion` 要求指标集是可数集：
-/

example (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) : MeasurableSet (⋃ n, s n) :=
  MeasurableSet.iUnion hs
example (s : ℕ → Set α) (hs : ∀ n, MeasurableSet (s n)) (T : Set ℕ) (hT : T.Countable) :
    MeasurableSet (⋃ n ∈ T, s n) :=
  MeasurableSet.biUnion hT (fun n _ ↦ hs n)

/-!
**三种内置的 σ-代数。**（1）**离散**：`Bool`、`Fin n`、`ℕ`、`ℤ`、`ℚ` 上的实例直接定义为 `⊤`
（`Mathlib/MeasureTheory/MeasurableSpace/Instances.lean`），即每个集合都可测。这被打包成类型类
`DiscreteMeasurableSpace`，`MeasurableSet.of_discrete` 与 `Measurable.of_discrete` 利用它。
（2）**积**：`α × β`、`∀ i, X i` 的 σ-代数是由「坐标投影可测」生成的最小 σ-代数；有限个离散空间的积
仍离散，所以 `Fin n → Bool` 上也是每个集合都可测（§8 要用）。（3）**Borel**：拓扑空间的 σ-代数是
由开集生成的 `borel α`，`[BorelSpace α]` 断言实例就是它。`ℝ` 上的开集、区间、单点集都可测：
-/

example (s : Set Bool) : MeasurableSet s := .of_discrete
example (s : Set ℤ) : MeasurableSet s := .of_discrete
example (s : Set ℚ) : MeasurableSet s := .of_discrete
example : DiscreteMeasurableSpace (Fin 3 → Bool) := inferInstance
example : BorelSpace ℝ := inferInstance
example (U : Set ℝ) (hU : IsOpen U) : MeasurableSet U := hU.measurableSet
example (a b : ℝ) : MeasurableSet (Set.Icc a b) := measurableSet_Icc
example (a : ℝ) : MeasurableSet ({a} : Set ℝ) := measurableSet_singleton a

/-!
**谓词与集合：`setOf` 改名为 `setOfPred`**（第 7 章）。测度论里的例子是 `measurableSet_setOf` →
`measurableSet_setOfPred`：集合 `{a | p a}` 可测当且仅当谓词 `p : α → Prop` 作为函数可测。
旧名（2026-07-09 起弃用）只发出警告：
-/

/--
warning: `measurableSet_setOf` has been deprecated: Use `measurableSet_setOfPred` instead

Hint: Replace the deprecated name:
  measurableSet_setOfP̲r̲e̲d̲
-/
#guard_msgs in
example (p : α → Prop) (h : Measurable p) : MeasurableSet {x | p x} := measurableSet_setOf.2 h

example (p : α → Prop) (h : Measurable p) : MeasurableSet {x | p x} := measurableSet_setOfPred.2 h

/-!
## 2. 可测函数：`Measurable`、`fun_prop` 与 `measurability`

`f : α → β` 是 measurable function（可测函数），如果每个可测集的原像可测。定义就是这句话（`Iff.rfl`，
和第 7 章一样，只用来做一次性检查）；用的时候直接把 `hf` 当函数应用到可测集的证明上。
-/

example (f : α → β) : Measurable f ↔ ∀ t, MeasurableSet t → MeasurableSet (f ⁻¹' t) := Iff.rfl
example (f : α → β) (hf : Measurable f) (t : Set β) (ht : MeasurableSet t) :
    MeasurableSet (f ⁻¹' t) := hf ht

/-!
基本引理：常函数、恒等、复合、坐标投影，以及算术运算保持可测。`Measurable.add` 是由 `to_additive` 从
`Measurable.mul` 生成的，所以 `rg "theorem Measurable.add"` 找不到，只能找到 `mul`；`add` 版本用
`#check` 或 `exact?` 找。同一个属性还生成 `fun_add`/`fun_mul`，结论写成 `fun x ↦ f x + g x` 的形状：
-/

example (c : β) : Measurable fun _ : α ↦ c := measurable_const
example (f : α → β) (g : β → ℝ) (hf : Measurable f) (hg : Measurable g) : Measurable (g ∘ f) :=
  hg.comp hf
example (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) : Measurable (f + g) := hf.add hg
example (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) : Measurable fun x ↦ f x + g x :=
  hf.fun_add hg
example (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x ≤ g x} :=
  measurableSet_le hf hg
example (ι : Type) (i : ι) : Measurable fun ω : ι → ℝ ↦ ω i := measurable_pi_apply i

/-!
手工组装很快就烦了，Mathlib 提供两个策略（第 10 章）。**`fun_prop`** 沿 `fun` 的语法递归，用标了
`@[fun_prop]` 的引理证函数性质（`Measurable` 是其一）；**`measurability`** 基于 `aesop`，对函数目标
直接调用 `fun_prop`（`Mathlib/Tactic/Measurability.lean` 的文档）。所以函数目标两者都成功；
`fun_prop` **不**接受 `MeasurableSet` 目标（报错见下），`measurability` 接受。
-/

example : Measurable fun x : ℝ ↦ x ^ 2 + 3 := by fun_prop
example : Measurable fun x : ℝ ↦ x ^ 2 + 3 := by measurability
example : Measurable fun ω : ℕ → ℝ ↦ ω 0 + ω 1 := by fun_prop

example : MeasurableSet {x : ℝ | 0 ≤ x} := by measurability
example : MeasurableSet {ω : ℕ → ℝ | ω 0 ≤ ω 1} := by measurability

/--
error: `MeasurableSet {x | 0 ≤ x}` is not a `fun_prop` goal! Consider marking `MeasurableSet` with `@[fun_prop]`.
-/
#guard_msgs in
example : MeasurableSet {x : ℝ | 0 ≤ x} := by fun_prop

/-!
要让 `fun_prop` 帮忙，先用 `measurableSet_le` 把集合目标化成 `f`、`g` 的可测性。`fun_prop` 可以把
上下文里的 `hs : MeasurableSet s` 当已知条件（`Measurable.indicator`，第二个例子）：
-/

example : MeasurableSet {x : ℝ | 0 ≤ x} := measurableSet_le (by fun_prop) (by fun_prop)
example (s : Set ℝ) (hs : MeasurableSet s) : Measurable (s.indicator fun x : ℝ ↦ x) := by
  fun_prop

/-!
## 3. 测度：`Measure`

`Measure α` 本质上是函数 `Set α → ℝ≥0∞`，以 outer measure（外测度）为底定义：**`μ s` 对每个集合
都有值**，只在可测集上可数可加。所以有些引理不要可测性（`measure_mono`、`measure_union_le`），有些要
（`measure_union`）。`ℝ≥0∞` 即 `[0, ∞]`，见 §4。（「测度」与第 6 章的终止度量、度量空间的「度量」无关。）
直到 `end Main`，`μ`、`s`、`t` 是下面这行声明的 `variable`（第 15 章）：
-/

variable (μ : Measure α) (s t : Set α)

example : μ ∅ = 0 := measure_empty
example (h : s ⊆ t) : μ s ≤ μ t := measure_mono h
example : μ (s ∪ t) ≤ μ s + μ t := measure_union_le s t
example (u : ℕ → Set α) : μ (⋃ n, u n) ≤ ∑' n, μ (u n) := measure_iUnion_le u
example (I : Finset ℕ) (u : ℕ → Set α) : μ (⋃ i ∈ I, u i) ≤ ∑ i ∈ I, μ (u i) :=
  measure_biUnion_finset_le I u

/-!
后两条是 union bound（联合界）。可数次可加的右边是 `ℝ≥0∞` 里的 `∑'`（第 14 章的 `tsum`；在 `ℝ≥0∞` 里
总是可和的，`ENNReal.summable`）；有限版本用 `Finset.sum`（第 12 章），第 19 章的概率方法反复用它。

**可加性需要可测性。** `measure_union` 要求第二个集合可测，对应的引理 `measure_compl` 同样要
`MeasurableSet`，并且还要有限性：右边是 `ℝ≥0∞` 里的 truncated subtraction（截断减法），`∞ - ∞ = 0`，
没有 `μ s ≠ ∞` 这条等式会出错（§4）：
-/

example (hd : Disjoint s t) (ht : MeasurableSet t) : μ (s ∪ t) = μ s + μ t := measure_union hd ht
example (hs : MeasurableSet s) (hfin : μ s ≠ ∞) : μ sᶜ = μ Set.univ - μ s := measure_compl hs hfin

/-!
**finite measure（有限测度）** `IsFiniteMeasure μ`（`μ univ < ∞`）下每个集合测度有限（`measure_ne_top`）；
probability measure（概率测度）`IsProbabilityMeasure μ` 是其特例（第 17 章）。测度还可以相加、数乘：
-/

example [IsFiniteMeasure μ] : μ s ≠ ∞ := measure_ne_top μ s
example [IsProbabilityMeasure μ] : IsFiniteMeasure μ := inferInstance
example [IsProbabilityMeasure μ] : μ s ≤ 1 := prob_le_one
example (ν : Measure α) : (μ + ν) s = μ s + ν s := by simp
example (c : ℝ≥0∞) : (c • μ) s = c * μ s := by simp
example (f : ℕ → ℝ≥0∞) : Summable f := ENNReal.summable

/-!
## 4. `ℝ≥0∞` 的生存指南

`ℝ≥0∞`（`ENNReal`，extended non-negative reals（扩展非负实数））是 `[0, ∞]`，装得下**每个**测度值。
代价是没有负数、减法截断、倒数在 `0` 与 `∞` 处取约定值，这些垃圾值要记住（同第 2 章 `ℕ` 的减法）：
-/

example : (∞ : ℝ≥0∞) - ∞ = 0 := ENNReal.sub_top  -- 截断减法：`∞ - ∞` 取 `0`
example : (1 : ℝ≥0∞) - 2 = 0 := tsub_eq_zero_of_le (by norm_num)  -- 截断减法：小减大取 `0`
example : (0 : ℝ≥0∞)⁻¹ = ∞ := ENNReal.inv_zero  -- 倒数在 `0` 处是 `∞`
example : (∞ : ℝ≥0∞)⁻¹ = 0 := ENNReal.inv_top  -- 倒数在 `∞` 处是 `0`
example : (∞ : ℝ≥0∞) * 0 = 0 := mul_zero _  -- `0` 吸收一切，包括 `∞`
example : (∞ : ℝ≥0∞).toReal = 0 := ENNReal.toReal_top  -- `toReal` 把 `∞` 压成 `0`
example : ENNReal.ofReal (-1) = 0 := ENNReal.ofReal_of_nonpos (by norm_num)  -- `ofReal` 把负数压成 `0`

/-!
所以 `ℝ≥0∞` 上减法与除法的许多引理都带 `≠ ∞` 或 `≠ 0` 的假设。**`decide` 对 `ℝ≥0∞` 没用**
（相等是经典的、不可计算的，见「常见错误」）；具体数的等式用 `norm_num`：
-/

example : (1 : ℝ≥0∞) + 1 = 2 := by norm_num

/-!
**`ℝ≥0∞` ↔ `ℝ`。** 实数运算比 `ℝ≥0∞` 方便得多（`linarith`、`field_simp`）。`ENNReal.toReal : ℝ≥0∞ → ℝ`
把 `∞` 送到 `0`，`ENNReal.ofReal : ℝ → ℝ≥0∞` 把负数送到 `0`。因此两个方向的往返引理都带条件：
-/

example (a : ℝ≥0∞) (ha : a ≠ ∞) : ENNReal.ofReal a.toReal = a := ENNReal.ofReal_toReal ha
example (r : ℝ) (hr : 0 ≤ r) : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr
example (r : ℝ) : (ENNReal.ofReal r).toReal = max r 0 := ENNReal.toReal_ofReal'
example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal :=
  ENNReal.toReal_add ha hb
example (n : ℕ) : (n : ℝ≥0∞).toReal = n := ENNReal.toReal_natCast n

/-!
**`finiteness`** 证 `≠ ∞` 和 `< ∞` 的目标（第 10 章只给了一行速览）。它从假设里读出各个量有限，
再用加法、乘法、有限测度的 `measure_ne_top` 拼起来：
-/

example (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) : a + 2 * b ≠ ∞ := by finiteness
example [IsFiniteMeasure μ] : μ s + 2 * μ t ≠ ∞ := by finiteness

/-!
**`μ.real`。** `Measure.real μ s := (μ s).toReal`（展开用 `measureReal_def`）。有限测度下 `toReal` 不丢
信息，所以概率方面的现代引理（Chernoff、Hoeffding，第 21 章）大多写 `μ.real {ω | …}`。所需的有限性有三种
写法：`measureReal_mono` 把 `μ t ≠ ∞` 做成默认值 `by finiteness` 的参数（有 `[IsFiniteMeasure μ]` 时自动
填好）；`measureReal_compl` 直接要 `[IsFiniteMeasure μ]`；`measureReal_union_le` 什么也不要：
-/

example : μ.real s = (μ s).toReal := measureReal_def μ s
example : 0 ≤ μ.real s := measureReal_nonneg
example (h : s ⊆ t) [IsFiniteMeasure μ] : μ.real s ≤ μ.real t := measureReal_mono h
example : μ.real (s ∪ t) ≤ μ.real s + μ.real t := measureReal_union_le s t
example [IsFiniteMeasure μ] (hs : MeasurableSet s) : μ.real sᶜ = μ.real Set.univ - μ.real s :=
  measureReal_compl hs
example [IsFiniteMeasure μ] : ENNReal.ofReal (μ.real s) = μ s := ofReal_measureReal
example [IsProbabilityMeasure μ] : μ.real s ≤ 1 := measureReal_le_one

/-!
## 5. 几乎处处：`ae`、`∀ᵐ` 与 `=ᵐ`

测度为 `0` 的集合叫 null set（零测集）。「除一个零测集外成立」称 almost everywhere（几乎处处）：`ae μ`
是 `α` 上的**滤子**（第 14 章），成员是补集零测的集合（`mem_ae_iff`），`∀ᵐ x ∂μ, p x` 就是沿 `ae μ`
最终成立（概率测度下读作 almost surely（几乎必然）），第 14 章的 `filter_upwards` 等工具直接可用。
-/

example (p : α → Prop) : (∀ᵐ x ∂μ, p x) ↔ μ {x | ¬ p x} = 0 := ae_iff
example : s ∈ ae μ ↔ μ sᶜ = 0 := mem_ae_iff
example (p : α → Prop) (h : ∀ x, p x) : ∀ᵐ x ∂μ, p x := ae_of_all μ h

example (f g h : α → ℝ) (h₁ : ∀ᵐ x ∂μ, f x ≤ g x) (h₂ : ∀ᵐ x ∂μ, g x ≤ h x) :
    ∀ᵐ x ∂μ, f x ≤ h x := by
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  exact hx₁.trans hx₂

/-!
`f =ᵐ[μ] g` 是 `Filter.EventuallyEq (ae μ) f g`，即 `∀ᵐ x ∂μ, f x = g x`，它是等价关系（`trans`、`symm`），
并且是积分真正看到的相等：几乎处处相等的函数有相同的积分（`integral_congr_ae`，§7）。
-/

example (f g h : α → ℝ) (h₁ : f =ᵐ[μ] g) (h₂ : g =ᵐ[μ] h) : f =ᵐ[μ] h := h₁.trans h₂

/-!
**勒贝格测度下的例子。** `volume` 是 `ℝ` 上的勒贝格测度（§6）。单点集测度 `0`，所以「`x ≠ 0` 几乎处处成立」：
-/

example : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
  rw [ae_iff]
  simp

/-!
## 6. 常用测度

后面反复出现的几个测度：`dirac`（集中在一点）、`count`（数元素，§8 要用）、`volume`（长度）、
`map`（沿函数搬运测度，第 17 章用它定义分布）、`pi`（独立的积）、`uniformOn`（有限集上的均匀分布）。

**Dirac measure（狄拉克测度）** `Measure.dirac a`：含 `a` 的集合测度为 `1`（`dirac_apply_of_mem`）；
可测集 `s` 上值是 `s.indicator 1 a`（`dirac_apply'`），在 `[MeasurableSingletonClass α]`（每个单点集
可测）的空间上对任意 `s` 都对（`dirac_apply`）。**counting measure（计数测度）** `Measure.count`：有限集
（可测，或单点集可测）的测度是元素个数。**Lebesgue measure（勒贝格测度）**：`ℝ` 上的 `volume`（在 `MeasureTheory`
命名空间里，见「常见错误」第 1 条），区间的测度是长度。
-/

example (a : ℝ) (t : Set ℝ) (h : a ∈ t) : Measure.dirac a t = 1 := Measure.dirac_apply_of_mem h
example (a : ℝ) (t : Set ℝ) (ht : MeasurableSet t) : Measure.dirac a t = t.indicator 1 a :=
  Measure.dirac_apply' a ht
example (a : ℝ) (t : Set ℝ) : Measure.dirac a t = t.indicator 1 a := Measure.dirac_apply a t
example : (Measure.count : Measure ℕ) (({1, 2, 3} : Finset ℕ) : Set ℕ) = 3 := by
  rw [Measure.count_apply_finset]; rfl
example (a b : ℝ) : volume (Set.Icc a b) = ENNReal.ofReal (b - a) := Real.volume_Icc
example : volume (Set.Icc (0 : ℝ) 1) = 1 := by simp

/-!
**push-forward（前推）测度** `μ.map f`：对可测的 `f` 与可测的 `s`，`μ.map f s = μ (f ⁻¹' s)`
（`Measure.map_apply`）；`f` 只是几乎处处可测（`AEMeasurable f μ`）时用 `Measure.map_apply₀`。
**垃圾值：** `f` 不是几乎处处可测、`μ ≠ 0` 时，`μ.map f` 被定义为某个点上的狄拉克测度；按
`Measure.map` 的文档（`Mathlib/MeasureTheory/Measure/Map.lean`），这样概率测度的前推永远是概率测度：
-/

example (f : α → β) (hf : Measurable f) (u : Set β) (hu : MeasurableSet u) :
    μ.map f u = μ (f ⁻¹' u) := Measure.map_apply hf hu

example (f : α → β) (hf : AEMeasurable f μ) (u : Set β) (hu : MeasurableSet u) :
    μ.map f u = μ (f ⁻¹' u) := Measure.map_apply₀ hf hu.nullMeasurableSet

example [Nonempty β] (f : α → β) (hf : ¬ AEMeasurable f μ) (hμ : μ ≠ 0) :
    μ.map f = Measure.dirac Classical.ofNonempty :=
  Measure.map_of_not_aemeasurable_of_ne_zero hf hμ

example [Nonempty β] [IsProbabilityMeasure μ] (f : α → β) (hf : ¬ AEMeasurable f μ) :
    IsProbabilityMeasure (μ.map f) := by
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hf (IsProbabilityMeasure.ne_zero μ)]
  infer_instance

/-!
**product measure（积测度）** `Measure.pi μ`（有限个因子）：在 `∀ i, X i` 上，满足
`Measure.pi_pi : Measure.pi μ (Set.univ.pi s) = ∏ i, μ i (s i)`（要求每个因子是 σ-finite（σ-有限测度），
`SigmaFinite`：空间可分成可数个测度有限的块）。勒贝格测度本身在 `Fin 2 → ℝ` 上按定义就是 `ℝ` 上勒贝格测度的积
（`volume_pi`），所以单位方块的测度是 `1`：
-/

example (ι : Type) [Fintype ι] (ν : ι → Measure ℝ) [∀ i, SigmaFinite (ν i)] (s : ι → Set ℝ) :
    Measure.pi ν (Set.univ.pi s) = ∏ i, ν i (s i) := Measure.pi_pi ν s
example :
    (Measure.pi fun _ : Fin 2 ↦ (volume : Measure ℝ)) (Set.univ.pi fun _ ↦ Set.Icc 0 1) = 1 := by
  rw [Measure.pi_pi]; simp
example : (volume : Measure (Fin 2 → ℝ)) = Measure.pi fun _ ↦ volume := volume_pi

/-!
**均匀测度** `ProbabilityTheory.uniformOn s = Measure.count[|s]`：计数测度条件在 `s` 上。在有限非空
的 `s` 上它是概率测度（要求单点集可测，或 `s` 本身可测）；对有限非空类型 `uniformOn Set.univ` 是实例（§8）：
-/

example (s : Set α) : uniformOn s = Measure.count[|s] := rfl
example : IsProbabilityMeasure (uniformOn ({0, 1, 2} : Set ℕ)) :=
  isProbabilityMeasure_uniformOn (Set.toFinite _) ⟨0, by simp⟩

/-!
## 7. 积分

**`∫⁻`**（`lintegral`，Lebesgue integral（勒贝格积分））：`ℝ≥0∞` 值函数的积分，**总有定义**。
**`∫`**（`integral`，Bochner integral（Bochner 积分））：取值于 `ℝ` 等 Banach 空间的函数的积分，只有
函数 integrable（可积，`Integrable`）时才是真积分。两者的联系要可积与几乎处处非负（最后一个例子）。
-/

example (c : ℝ≥0∞) : ∫⁻ _, c ∂μ = c * μ Set.univ := lintegral_const c
example (f g : α → ℝ≥0∞) (h : f ≤ g) : ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ := lintegral_mono h
example (hs : MeasurableSet s) : ∫⁻ x, s.indicator 1 x ∂μ = μ s := lintegral_indicator_one hs
example (f : α → ℝ) (hf : Integrable f μ) (h0 : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal hf h0

/-!
`∫` 的**垃圾值**：不可积时积分为 `0`（`integral_undef`），不报错。因此 `integral_add` 等等式必须带
`Integrable` 假设，而 `integral_const_mul` 不用：`r ≠ 0` 时 `r * f` 与 `f` 同时可积或同时不可积
（`integral_smul` 的文档注释），不可积时两边都是 `0`；`r = 0` 时两边也都是 `0`。`ℝ` 上的常函数 `1`
在勒贝格测度下不可积（`integrable_const_iff_isFiniteMeasure` 化为 `volume` 不是有限测度），积分是
`0`（`volume univ = ∞`，`toReal ∞ = 0`），而不是「`∞`」：
-/

example (f : α → ℝ) (h : ¬ Integrable f μ) : ∫ x, f x ∂μ = 0 := integral_undef h
example : ¬ Integrable (fun _ : ℝ ↦ (1 : ℝ)) := by
  rw [integrable_const_iff_isFiniteMeasure one_ne_zero]
  intro h
  exact measure_ne_top volume Set.univ Real.volume_univ
example : ∫ _ : ℝ, (1 : ℝ) = 0 := by
  rw [integral_const, measureReal_def, Real.volume_univ]; simp
example (f : α → ℝ) (r : ℝ) : ∫ x, r * f x ∂μ = r * ∫ x, f x ∂μ := integral_const_mul r f

/-!
可积性的来源：有限测度下常函数可积；可积函数对加法、数乘封闭；有限空间上，若每个单点集可测且
测度有限，则一切函数可积（见下）。
-/

section Integral

variable (f g : α → ℝ)

example [IsFiniteMeasure μ] (c : ℝ) : Integrable (fun _ : α ↦ c) μ := integrable_const c
example (hf : Integrable f μ) (hg : Integrable g μ) : Integrable (fun x ↦ f x + g x) μ := hf.add hg
example (hf : Integrable f μ) (c : ℝ) : Integrable (fun x ↦ c * f x) μ := hf.const_mul c

example (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, (f x + g x) ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ := integral_add hf hg
example (c : ℝ) : ∫ _ : α, c ∂μ = μ.real Set.univ • c := integral_const c
example (ι : Type) (I : Finset ι) (F : ι → α → ℝ) (hF : ∀ i ∈ I, Integrable (F i) μ) :
    ∫ x, ∑ i ∈ I, F i x ∂μ = ∑ i ∈ I, ∫ x, F i x ∂μ := integral_finsetSum I hF

example (hf : Integrable f μ) (hg : Integrable g μ) (h : f ≤ g) :
    ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ := integral_mono hf hg h
example (h : f =ᵐ[μ] g) : ∫ x, f x ∂μ = ∫ x, g x ∂μ := integral_congr_ae h
example (hs : MeasurableSet s) : ∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x ∂μ = μ.real s :=
  integral_indicator_one hs

end Integral

/-!
**`MemLp`** 是 Lp space（Lp 空间）的成员关系：`MemLp f p μ` 读作「`f` 属于 Lp(μ)」，说 `f` 可测（几乎处处）且
`‖f‖ₚ` 有限，`p : ℝ≥0∞`。`p = 1` 就是可积（`memLp_one_iff_integrable`）；`p = 2` 在第 17 章定义方差时要用。
在有限测度下 `MemLp f p` 蕴含 `Integrable f`（`p ≥ 1`）；对几乎处处强可测（`AEStronglyMeasurable`，
对 `ℝ` 值函数就是几乎处处可测）的 `f`，`p = 2` 时 `MemLp` 等价于 `f ^ 2` 可积：
-/

example (f : α → ℝ) : MemLp f 1 μ ↔ Integrable f μ := memLp_one_iff_integrable
example [IsFiniteMeasure μ] (f : α → ℝ) (hf : MemLp f 2 μ) : Integrable f μ :=
  hf.integrable (by norm_num)
example (f : α → ℝ) (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x ↦ f x ^ 2) μ := memLp_two_iff_integrable_sq hf

/-!
**有限空间与有限测度：不需要可积性假设。** 若 `X` 有限（`Finite`）、测度有限，且每个单点集可测
（`MeasurableSingletonClass`），则每个函数可积（`Integrable.of_finite`）；若 σ-代数离散
（`DiscreteMeasurableSpace`），则每个函数对每个 `p` 属于 Lp（`MemLp.of_discrete`）。测度有限不能省
（`integral_fintype` 的文档注释）。积分是加权和 `∫ f ∂μ = ∑ x, μ.real {x} • f x`
（`integral_fintype`），对计数测度权重全是 `1`（`integral_count`）。这是 §8 的主要工具：
-/

example (X : Type) [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ) :
    ∫ x, f x ∂ν = ∑ x, ν.real {x} • f x := integral_fintype Integrable.of_finite
example (X : Type) [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] (f : X → ℝ) :
    ∫ x, f x ∂(Measure.count : Measure X) = ∑ x, f x := integral_count f
example (X : Type) [Finite X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ) (p : ℝ≥0∞) : MemLp f p ν := MemLp.of_discrete

/-!
## 8. 案例：抛硬币

样本空间是 `Fin n → Bool`（`ω i = true` 表示第 `i` 枚是正面），共 `2 ^ n` 个点，取均匀测度；第 17 章
用 `Measure.pi` 推广到有偏硬币。类型用 `abbrev` 起别名，`Fin n → Bool` 上的实例原样穿过别名。
-/

/-- `n` 次抛硬币的样本空间。 -/
abbrev Coins (n : ℕ) : Type := Fin n → Bool

/-- 均匀测度：每个配置概率 `1 / 2 ^ n`。 -/
noncomputable abbrev P (n : ℕ) : Measure (Coins n) := uniformOn (Set.univ : Set (Coins n))

/-!
三条实例都由 Lean 自己找到：积 σ-代数是离散的，单点集可测，`uniformOn Set.univ` 是概率测度（只需要
`Finite` 与 `Nonempty`）。所以 `Integrable.of_finite` 在这个空间上随时可用，积分的可积性不必手证：
-/

example (n : ℕ) : DiscreteMeasurableSpace (Coins n) := inferInstance
example (n : ℕ) : MeasurableSingletonClass (Coins n) := inferInstance
example (n : ℕ) : IsProbabilityMeasure (P n) := inferInstance

theorem card_coins (n : ℕ) : Fintype.card (Coins n) = 2 ^ n := by simp [Coins]

/-!
**事件「第 `i` 枚硬币是正面」。** 写成 `n + 1` 枚硬币，避开 `Fin 0` 与 `ℕ` 的截断减法 `n - 1`（第 2 章）。
把集合写成 `Finset` 的 coercion（强制转换），就能用 `Measure.count_apply_finset`（计数测度等于基数）。
关键事实：这样的 `ω` 共 `2 ^ n` 个，它们恰是 `Fintype.piFinset`（各坐标各自在一个 `Finset` 里取值的
函数之集）里「第 `i` 个坐标限制为 `{true}`」的那一个，基数是各坐标候选数之积（`Fintype.card_piFinset`；
基数是积，名字里就有 `card_pi`，再 `rg "card_piFinset"` 确认）。
-/

theorem card_heads (n : ℕ) (i : Fin (n + 1)) :
    (Finset.univ.filter fun ω : Coins (n + 1) ↦ ω i = true).card = 2 ^ n := by
  have h : (Finset.univ.filter fun ω : Coins (n + 1) ↦ ω i = true) =
      Fintype.piFinset (fun j ↦ if j = i then {true} else Finset.univ) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj; simp [h]
      · simp [hj]
    · intro h
      simpa using h i
  rw [h, Fintype.card_piFinset]
  -- ⊢ ∏ i_1, (if i_1 = i then {true} else Finset.univ).card = 2 ^ n
  -- 把第 `i` 个因子单独拿出来，其余因子每个都是 `2`
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have h2 : ∀ x ∈ Finset.univ.erase i,
      (if x = i then ({true} : Finset Bool) else Finset.univ).card = 2 := by
    intro x hx
    simp [Finset.ne_of_mem_erase hx]
  rw [Finset.prod_congr rfl h2]
  simp

/-!
**概率是 `1 / 2`。** 先写成实数 `μ.real`，逐步改写（关键步骤后的目标写在注释里；注释里的
`{ω | ω i = true}.card` 是 `Finset.filter` 的基数，`Finset` 的 `filter` 显示成集合记号）：
-/

theorem prob_head (n : ℕ) (i : Fin (n + 1)) :
    (P (n + 1)).real {ω | ω i = true} = 1 / 2 := by
  have h : {ω : Coins (n + 1) | ω i = true} =
      ((Finset.univ.filter fun ω : Coins (n + 1) ↦ ω i = true : Finset _) : Set _) := by
    ext ω; simp
  rw [h, measureReal_def, uniformOn_univ, Measure.count_apply_finset]
  -- ⊢ (↑{ω | ω i = true}.card / ↑(Fintype.card (Coins (n + 1)))).toReal = 1 / 2
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, card_heads, card_coins]
  -- ⊢ ↑(2 ^ n) / ↑(2 ^ (n + 1)) = 1 / 2   （已在 `ℝ` 里）
  push_cast
  -- ⊢ 2 ^ n / 2 ^ (n + 1) = 1 / 2
  rw [pow_succ]
  field_simp

/-!
**期望是 `(n + 1) / 2`。** `n + 1` 枚硬币的「正面个数」`∑ i, (if ω i = true then 1 else 0)` 的期望
由积分的线性（`integral_finsetSum`）加上每一项的期望算出。每一项是事件的 indicator function
（指示函数），积分等于概率（`integral_indicator_one`），即 `prob_head`；可积性由 `Integrable.of_finite` 给出：
-/

theorem integral_head (n : ℕ) (i : Fin (n + 1)) :
    ∫ ω, (if ω i = true then (1 : ℝ) else 0) ∂(P (n + 1)) = 1 / 2 := by
  have h : (fun ω : Coins (n + 1) ↦ if ω i = true then (1 : ℝ) else 0) =
      Set.indicator {ω | ω i = true} 1 := by
    ext ω; simp [Set.indicator_apply]
  rw [h, integral_indicator_one .of_discrete, prob_head]

theorem integral_heads (n : ℕ) :
    ∫ ω, ∑ i : Fin (n + 1), (if ω i = true then (1 : ℝ) else 0) ∂(P (n + 1)) = (n + 1) / 2 := by
  rw [integral_finsetSum _ (fun i _ ↦ Integrable.of_finite)]
  simp only [integral_head]
  -- ⊢ ∑ x, 1 / 2 = (↑n + 1) / 2
  simp
  ring

end Main

/-!
## 9. 常见错误

这一节在 `section Main` 之外，没有 `open MeasureTheory`，第 1 条就是为此而设。

**1. 忘记 `open MeasureTheory`。** `volume`、`Measure`、`ae`、`MemLp` 等都在 `MeasureTheory` 命名空间里
（要么 `open MeasureTheory`，要么写全名）：
-/

/--
error: Unknown identifier `volume`

Note: It is not possible to treat `volume` as an implicitly bound variable here because the `autoImplicit` option is set to `false`.
-/
#guard_msgs in
example : volume (Set.Icc (0 : ℝ) 1) = 1 := by sorry

/-!
**2. 给 `measure_union` 漏掉可测性。** 没有 `MeasurableSet` 参数，它只是一个函数。读 `has type` 那一行：
`MeasurableSet t → …` 的箭头左边就是缺的参数。如果想要不带假设的版本，用不等式 `measure_union_le`（§3）：
-/

set_option pp.mvars false in
/--
error: Type mismatch
  MeasureTheory.measure_union hd
has type
  MeasurableSet t → ?_ (s ∪ t) = ?_ s + ?_ t
but is expected to have type
  μ (s ∪ t) = μ s + μ t
-/
#guard_msgs in
example (μ : MeasureTheory.Measure ℝ) (s t : Set ℝ) (hd : Disjoint s t) :
    μ (s ∪ t) = μ s + μ t :=
  MeasureTheory.measure_union hd

/-!
**3. 对 `ℝ≥0∞` 用 `decide`。** `ℝ≥0∞` 的 `DecidableEq` 是经典的（走 `Classical.choice`），`decide` 的归约
卡在它上面。这类等式用 `norm_num`（§4）。对 `MeasurableSet` 目标用 `fun_prop` 的报错见 §2：
-/

/--
error: Tactic `decide` failed to reduce
  @decide (1 + 1 = 2) (LinearOrder.toDecidableEq (1 + 1) 2)
to `true` or `false`.

After unfolding the instances `Classical.propDecidable`, `CompleteLinearOrder.toDecidableEq`, `ConditionallyCompleteLinearOrder.toDecidableEq`, `LinearOrder.toDecidableEq`, `Option.instDecidableEq`, `WithTop.decidableEq`, `ENNReal.instCompleteLinearOrder._aux_24`, `Nonneg.conditionallyCompleteLinearOrder._aux_8`, and `WithTop.decidableEq._aux_1`, reduction got stuck at
  Classical.choice ⋯

Hint: Reduction got stuck on `Classical.choice`, which indicates that a `Decidable` instance is defined using classical reasoning, proving an instance exists rather than giving a concrete construction. The `decide` tactic works by evaluating a decision procedure via reduction, and it cannot make progress with such instances. This can occur due to the `open scoped Classical` command, which enables the instance `Classical.propDecidable`.
-/
#guard_msgs in
example : (1 : ENNReal) + 1 = 2 := by decide

/-!
**4. 忘记有限性。** `measure_ne_top` 需要 `IsFiniteMeasure`（一般的测度可以取 `∞`），补救是加上实例假设：
-/

/--
error: failed to synthesize instance of type class
  MeasureTheory.IsFiniteMeasure ν

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (ν : MeasureTheory.Measure ℝ) (s : Set ℝ) : ν s ≠ ⊤ :=
  MeasureTheory.measure_ne_top ν s

/-!
## 练习

16.2 回到第 7 章（集合外延），16.6、16.7 用第 5、11 章的 `calc` 与 `linarith`，16.9 是第 14 章的
`filter_upwards`，16.14、16.15 用第 12 章的有限和与计数。引理名在本章出现，或由题面给出。
-/

section Exercises

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- 练习 16.1（★）：可测集对补、并、交封闭；用 `MeasurableSet.compl/union/inter`。 -/
theorem ex_16_1 {α : Type*} [MeasurableSpace α] (s t u : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hu : MeasurableSet u) : MeasurableSet ((sᶜ ∪ t) ∩ u) := by
  sorry

/-- 练习 16.2（★）：`{x | 1 < x ∧ x ≤ 3}` 可测。两种做法：`measurability`；或者先用
`Set.ext`（第 7 章）证它等于 `Set.Ioc 1 3`，再用 `measurableSet_Ioc`。 -/
theorem ex_16_2 : MeasurableSet {x : ℝ | 1 < x ∧ x ≤ 3} := by sorry

/-- 练习 16.3（★）：可测函数的多项式组合可测；用 `fun_prop`。 -/
theorem ex_16_3 (f : ℝ → ℝ) (hf : Measurable f) : Measurable fun x ↦ (x ^ 2 + 1) * f x - 3 := by
  sorry

/-- 练习 16.4（★★）：`{x | f x ≤ 3 ∧ 0 ≤ f x}` 可测；用 `measurableSet_le`、`measurable_const` 与
`MeasurableSet.inter`（`measurability` 也行）。 -/
theorem ex_16_4 (f : ℝ → ℝ) (hf : Measurable f) : MeasurableSet {x | f x ≤ 3 ∧ 0 ≤ f x} := by
  sorry

/-- 练习 16.5（★★）：`ℕ → ℝ` 上由前两个坐标定义的事件可测；用 `measurableSet_lt`、
`measurable_pi_apply`，或把集合写成 `{ω | p ω}` 后用 `measurableSet_setOfPred.2` 与 `fun_prop`。 -/
theorem ex_16_5 : MeasurableSet {ω : ℕ → ℝ | ω 0 + ω 1 < 1} := by sorry

/-- 练习 16.6（★★）：三个集合的联合界；对 `μ ((s ∪ t) ∪ u)` 用两次 `measure_union_le`，
中间用 `calc` 与 `gcongr`（第 11 章）。 -/
theorem ex_16_6 {α : Type*} [MeasurableSpace α] (μ : Measure α) (s t u : Set α) :
    μ (s ∪ t ∪ u) ≤ μ s + μ t + μ u := by sorry

/-- 练习 16.7（★★）：有限测度的容斥；先用 `measureReal_union_add_inter`（注意它的可测性假设落在
哪个集合上；不确定名字时用 `exact?` 找），再用 `linarith`。 -/
theorem ex_16_7 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (s t : Set α)
    (ht : MeasurableSet t) : μ.real (s ∪ t) = μ.real s + μ.real t - μ.real (s ∩ t) := by
  sorry

/-- 练习 16.8（★）：有限测度下，`ℝ≥0∞` 里的和读成实数就是 `μ.real` 的和。用 `ENNReal.toReal_add`
（两个有限性假设由 `measure_ne_top` 或 `finiteness` 给出）与 `measureReal_def`。 -/
theorem ex_16_8 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (s t : Set α) :
    (μ s + μ t).toReal = μ.real s + μ.real t := by sorry

/-- 练习 16.9（★）：几乎处处的传递；用 `filter_upwards [h₁, h₂] with x hx₁ hx₂`（第 14 章）。 -/
theorem ex_16_9 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g h : α → ℝ)
    (h₁ : ∀ᵐ x ∂μ, f x ≤ g x) (h₂ : ∀ᵐ x ∂μ, g x < h x) : ∀ᵐ x ∂μ, f x < h x := by
  sorry

/-- 练习 16.10（★★）：几乎处处相等给出积分的比例关系。先用 `integral_congr_ae` 把 `f` 换成
`fun x ↦ 2 * g x`（需要 `f =ᵐ[μ] fun x ↦ 2 * g x`，就是 `h`），再用 `integral_const_mul`。 -/
theorem ex_16_10 {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (h : ∀ᵐ x ∂μ, f x = 2 * g x) : ∫ x, f x ∂μ = 2 * ∫ x, g x ∂μ := by sorry

/-- 练习 16.11（★★）：狄拉克测度加勒贝格测度。用 `Measure.add_apply`、`Measure.dirac_apply_of_mem`、
`Real.volume_Icc` 与 `ENNReal.ofReal` 的数值化简（`norm_num`）。 -/
theorem ex_16_11 : (Measure.dirac (2 : ℝ) + volume : Measure ℝ) (Set.Icc 0 3) = 4 := by sorry

/-- 练习 16.12（★★）：积分的线性。用 `integral_add`（可积性：`hf.const_mul`、`integrable_const`）、
`integral_const_mul`、`integral_const`。 -/
theorem ex_16_12 {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) :
    ∫ x, (3 * f x + 2) ∂μ = 3 * ∫ x, f x ∂μ + 2 * μ.real Set.univ := by sorry

/-- 练习 16.13（★★）：前推测度。狄拉克测度沿 `x ↦ 2 * x` 前推，仍是狄拉克测度。用
`Measure.map_dirac'`（需要 `Measurable`，交给 `fun_prop`）。 -/
theorem ex_16_13 (a : ℝ) :
    (Measure.dirac a).map (fun x : ℝ ↦ 2 * x) = Measure.dirac (2 * a) := by sorry

/-- 练习 16.14（★★）：`Fin 3` 上计数测度的积分是有限和。用 `integral_count`、`Fin.sum_univ_three`
（第 12 章），再 `norm_num`。 -/
theorem ex_16_14 : ∫ x : Fin 3, ((x : ℕ) : ℝ) ∂(Measure.count : Measure (Fin 3)) = 3 := by
  sorry

/-- 练习 16.15（★★）：两次抛硬币都是正面的概率是 `1 / 4`。把集合写成 `Finset.filter` 的强制转换
（像 `prob_head` 的证明），基数用 `decide` 算；这里的样本空间就是 `Coins 2`。 -/
theorem ex_16_15 :
    (uniformOn (Set.univ : Set (Fin 2 → Bool))).real {ω | ω 0 = true ∧ ω 1 = true} = 1 / 4 := by
  sorry

end Exercises

/-!
## 小结

| 概念 | 写法 | 何时用 |
|---|---|---|
| σ-代数、可测集 | `MeasurableSpace α`、`MeasurableSet s`、`.compl/.union/.inter/.iUnion` | 离散、积、Borel |
| 谓词与集合 | `measurableSet_setOfPred`（旧名 `measurableSet_setOf` 已弃用） | `{x \| p x}` 可测 |
| 可测函数 | `Measurable f`、`.comp/.add`、`measurableSet_le` | 随机变量、指示函数 |
| 证可测 | `fun_prop`（函数）、`measurability`（函数与集合） | 集合目标先化成函数目标 |
| 测度 | `μ s : ℝ≥0∞`、`measure_mono`、`measure_union_le`、`measure_biUnion_finset_le` | 不要可测性 |
| 可加性 | `measure_union`、`measure_compl` | 要可测（与有限）假设 |
| 有限测度 | `IsFiniteMeasure`、`measure_ne_top`、`finiteness` | 证 `≠ ∞` |
| `ℝ≥0∞` 垃圾值 | `∞ - ∞ = 0`、`toReal ∞ = 0`、`0⁻¹ = ∞`；`decide` 无效 | 往返要 `≠ ∞`、`0 ≤` |
| 回到 `ℝ` | `μ.real s`、`measureReal_def`、`ENNReal.toReal_add` | 做算术与不等式 |
| 几乎处处 | `∀ᵐ x ∂μ, p x`、`ae_iff`、`filter_upwards`、`f =ᵐ[μ] g` | 沿滤子 `ae μ` |
| 常用测度 | `Measure.dirac/count/pi/map`、`volume`、`uniformOn` | 非可测 `f` 的 `map` 是狄拉克 |
| 积分 | `∫⁻`（总有定义）；`∫`、`Integrable`、`integral_add/finsetSum` | `∫` 不可积时为 `0` |
| Lp | `MemLp f p μ`、`memLp_two_iff_integrable_sq` | `p = 2` 用于方差 |
| 有限空间 | `Integrable.of_finite`、`MemLp.of_discrete`、`integral_fintype` | 有限、测度有限、点可测 |
-/

/-!
## 延伸阅读

- 可测性：`Mathlib/MeasureTheory/MeasurableSpace/Defs.lean`（`MeasurableSet`、`Measurable`、
  `generateFrom`）、`Mathlib/Tactic/Measurability.lean`、`Mathlib/Tactic/Finiteness.lean`。
- 测度与 `ℝ≥0∞`：`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`、
  `Mathlib/MeasureTheory/Measure/Real.lean`（`measureReal_*`）、`Mathlib/Basic/ENNReal/`
  （旧路径 `Mathlib/Data/ENNReal/` 是弃用的转发文件）。
- 积分：`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`、`.../Bochner/SumMeasure.lean`
  （`integral_fintype`）、`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`。
- 有限概率空间：`Mathlib/Probability/UniformOn.lean`；`Archive/Wiedijk100Theorems/BirthdayProblem.lean`
  是 `uniformOn` 的官方范例；《Lean 形式化数学》（Mathematics in Lean，
  <https://leanprover-community.github.io/mathematics_in_lean/>）的 Integration and Measure Theory 一章。
- 本书第 7 章（`Set.ofPred`）、第 14 章（滤子）、第 17 章（概率测度与独立）、第 19 章（概率方法）。
-/

end Lean4Learn.Ch16

end
