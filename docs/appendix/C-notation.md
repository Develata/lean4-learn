# 附录 C　记号 → 所需 `open` 对照表

本附录回答一个问题：某个记号要写什么 `open` 才能用。每行给出记号、它展开成什么、需要什么、定义处（锁定版本里的
文件与行号）、本书演示它的章节（「12 §3」即第 12 章 §3）。内容对应 Lean `v4.35.0` + Mathlib `v4.35.0`（commit `56a0058`）。路径
`Mathlib/…` 指 `.lake/packages/mathlib/Mathlib/…`，`Init/…` 指 Lean 核心源码（`src/lean/Init/…`）。

**读法。**

- 「需要 `open N`」指 `open N` 或 `open scoped N` 都可以：两者都会激活命名空间 `N` 里的 `scoped` 记号，
  后者不把 `N` 里的名字带进来（`docs/style.md` §5；第 12 章 §1 的 `#s`、第 17 章「常见错误」1 的概率记号都这样演示）。
  一次性用法写 `open N in` 放在声明前（第 8 章 §12）。
- 「全局」指记号不是 `scoped` 的，导入定义它的模块即可用。但记号里出现的**名字**另算：`∀ᶠ` 是全局记号，
  `atTop` 却是 `Filter.atTop`，不 `open Filter` 就要写全名（第 14 章「常见错误」1）。
- 「本书未演示」的行只有源码定位作证，没有编译过的例子。

## 1. 有限和、有限集与组合

| 记号 | 含义 | 需要 | 定义处 | 本书 |
|---|---|---|---|---|
| `∑ x ∈ s, f x`、`∏ x ∈ s, f x`、`∑ x, f x`、`∑ x ∈ s with p x, f x` | `Finset.sum`、`Finset.prod`（无 `∈ s` 时对 `Finset.univ`） | 全局 | `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:180`（`∑`）、`:195`（`∏`） | 12 §3 |
| 旧写法 `∑ x in s, f x` | 不再被接受：约束子语法只有 `x`、`x : T` 与 `x ∈ s` 一类谓词形式 | — | 同上 `:108`（`bigOpBinder`）、`:180` | 12 §3（断言为解析错误，未编译演示，见附录 D） |
| `𝔼 i ∈ s, f i`、`𝔼 i, f i` | `Finset.expect`，有限平均 | `open BigOperators` | `Mathlib/Algebra/BigOperators/Expect.lean:77`（`scoped syntax`） | 19 §1（与概率的 `𝔼[X]` 撞词） |
| `#s` | `Finset.card s` | `open Finset` | `Mathlib/Data/Finset/Card.lean:50`（`scoped prefix`） | 12 §1；18 文件头 |
| `{x ∈ s \| p x}` | `Finset.filter p s`（`s` 是 `Finset` 时） | 全局 | `Mathlib/Data/Finset/Filter.lean:94` | 12 §2 |
| `{x \| p x}` | `Set.ofPred p` | 全局 | `Mathlib/Data/Set/Defs.lean:114` | 7 §1 |
| `n.choose k` | `Nat.choose n k`；**没有**专门记号 | — | — | 12 §8；19 §5 |
| `n !` | `Nat.factorial n` | `open Nat` | `Mathlib/Data/Nat/Factorial/Basic.lean:47`（`scoped notation`） | 本书未演示，一律写 `Nat.factorial n`（1 §8）；`open Nat` 带来同名歧义（9 §15 ③） |

## 2. 数系与范数

| 记号 | 含义 | 需要 | 定义处 | 本书 |
|---|---|---|---|---|
| `ℝ≥0` | `NNReal` | `open NNReal` | `Mathlib/Basic/NNReal/Defs.lean:64` | 17 §7；21 §4 |
| `ℝ≥0∞` | `ENNReal` | `open ENNReal` | `Mathlib/Basic/ENNReal/Basic.lean:107`（`scoped[ENNReal]`） | 16 §4；10 §8 |
| `∞` | `(⊤ : ENNReal)` | `open ENNReal` | `Mathlib/Basic/ENNReal/Basic.lean:112` | 16 §4；10 §8 |
| `ℕ∞` | `ENat` | 全局 | `Mathlib/Data/ENat/Defs.lean:20` | 18 §11（色数） |
| `ℚ≥0` | `NNRat` | 全局 | `Mathlib/Data/Rat/Init.lean:26` | 19 §1 |
| `‖x‖`、`‖x‖₊`、`‖x‖ₑ` | `norm`、`nnnorm`、`enorm` | 全局 | `Mathlib/Analysis/Normed/Group/Defs.lean:82`–`84` | 14 §10；21 §5（`‖x‖₊`）；17 §5（`‖·‖ₑ`） |
| `π` | `Real.pi` | `open Real` | `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean:132`（`scoped notation`） | 本书未演示 |
| `⌊x⌋`、`⌈x⌉` | `Int.floor`、`Int.ceil` | 全局 | `Mathlib/Algebra/Order/Floor/Defs.lean:280`、`:283` | 本书未演示 |
| `⌊x⌋₊`、`⌈x⌉₊` | `Nat.floor`、`Nat.ceil` | 全局 | 同上 `:141`、`:144` | 本书未演示 |

## 3. 代数与图

| 记号 | 含义 | 需要 | 定义处 | 本书 |
|---|---|---|---|---|
| `M →+ N`、`M →* N`、`R →+* S` | `AddMonoidHom`、`MonoidHom`、`RingHom` | 全局 | `Mathlib/Algebra/Group/Hom/Defs.lean:151`、`:373`；`Mathlib/Algebra/Ring/Hom/Defs.lean:312` | 15 §6 |
| `G ⧸ N` | `HasQuotient.Quotient G N` | 全局 | `Mathlib/Algebra/Quotient.lean:53` | 15 §7 |
| `s(a, b)` | `Sym2.mk a b`，无序对 | 全局 | `Mathlib/Data/Sym/Sym2.lean:111`（在 `namespace Sym2` 之外） | 18 §3 |
| `G →g H`、`G ↪g H`、`G ≃g H` | `SimpleGraph.Hom`、`Embedding`、`Iso` | 全局 | `Mathlib/Combinatorics/SimpleGraph/Maps.lean:310`–`312` | 18 §12 |

## 4. 滤子、极限与渐近

| 记号 | 含义 | 需要 | 定义处 | 本书 |
|---|---|---|---|---|
| `∀ᶠ x in l, p x` | `Filter.Eventually` | 全局 | `Mathlib/Order/Filter/Defs.lean:284` | 14 §3 |
| `∃ᶠ x in l, p x` | `Filter.Frequently` | 全局 | `Mathlib/Order/Filter/Defs.lean:292` | 本书未演示 |
| `𝓟 s` | `Filter.principal s` | `open Filter` | `Mathlib/Order/Filter/Defs.lean:154`（`scoped notation`） | 14 §2 |
| `𝓝 x`、`𝓝[s] x` | `nhds x`、`nhdsWithin x s` | `open Topology` | `Mathlib/Topology/Defs/Filter.lean:134`、`:142`（`scoped[Topology]`） | 14 §2 |
| `atTop`、`Tendsto`（名字，不是记号） | `Filter.atTop`、`Filter.Tendsto` | `open Filter` 或写全名 | `Mathlib/Order/Filter/AtTopBot/Defs.lean:40`；`Mathlib/Order/Filter/Defs.lean:421` | 14「常见错误」1 |
| `f =O[l] g`、`f =o[l] g` | `Asymptotics.IsBigO`、`IsLittleO` | 全局 | `Mathlib/Analysis/Asymptotics/Defs.lean:89`、`:173` | 14 §10 |
| `∑' i, f i` | `tsum f` | 全局 | `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean:161` | 14 §9；16 §3 |

## 5. 测度与积分

| 记号 | 含义 | 需要 | 定义处 | 本书 |
|---|---|---|---|---|
| `∫ x, f x ∂μ`、`∫ x in s, f x ∂μ` | `MeasureTheory.integral` | 全局 | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:168`、`:174` | 16 §7；17「常见错误」1（不 `open MeasureTheory` 照样可用） |
| `∫ x, f x`（省略 `∂μ`） | 对 `volume` 积分 | 全局；要 `MeasureSpace` 实例 | 同上 `:171` | 17「常见错误」1 |
| `∫⁻ x, f x ∂μ` | `lintegral`，取值于 `ℝ≥0∞` | 全局 | `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean:56` | 16 §7 |
| `∀ᵐ x ∂μ, p x`、`∃ᵐ x ∂μ, p x` | 沿 `ae μ` 的 `Eventually`、`Frequently` | 全局 | `Mathlib/MeasureTheory/OuterMeasure/AE.lean:56`、`:62` | 16 §5（`∃ᵐ` 未演示） |
| `f =ᵐ[μ] g`、`f ≤ᵐ[μ] g` | 几乎处处相等 / 不超过 | 全局 | `Mathlib/MeasureTheory/OuterMeasure/AE.lean:69`、`:76` | 16 §5 |
| `volume`、`Measure`、`ae`（名字） | `MeasureTheory.MeasureSpace.volume` 等 | `open MeasureTheory` 或写全名 | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:359`（`export MeasureSpace (volume)`） | 16 §9 第 1 条 |

`∂μ` 不是单独的记号，而是 `∫`、`∀ᵐ` 语法的一部分。

## 6. 概率

下表的记号都在 `ProbabilityTheory`（`G(V, p)` 在 `SimpleGraph`，`I`、`σ` 在 `unitInterval`，`μ[X | m]` 在 `MeasureTheory`）里限定作用域。
第 17 章「常见错误」1 用一条 `open scoped ProbabilityTheory in` 同时演示了前七个。

| 记号 | 含义 | 需要 | 定义处 | 本书 |
|---|---|---|---|---|
| `μ[X]` | `∫ x, ↑(X x) ∂μ`（`scoped macro`） | `open ProbabilityTheory` | `Mathlib/Probability/Notation.lean:53` | 17 §2；不打开时被当成下标 `GetElem`（17「常见错误」1） |
| `𝔼[X]` | `∫ a, X a`，对 `volume` | `open ProbabilityTheory` | `Mathlib/Probability/Notation.lean:57` | 17「常见错误」1（与有限平均 `𝔼 i, f i` 撞词，19 §1） |
| `ℙ` | `volume` | `open ProbabilityTheory` | `Mathlib/Probability/Notation.lean:73` | 17 §1 |
| `Var[X; μ]`、`Var[X]` | `variance X μ`；后者取 `volume` | `open ProbabilityTheory` | `Mathlib/Probability/Moments/Variance.lean:80`、`:85` | 17 §5 |
| `X ⟂ᵢ[μ] Y`、`X ⟂ᵢ Y` | `IndepFun X Y μ`；后者取 `volume` | `open ProbabilityTheory` | `Mathlib/Probability/Independence/Basic.lean:150`、`:153` | 17 §4 |
| `Ber(x, y, p)` | `bernoulliMeasure x y p` | `open ProbabilityTheory` | `Mathlib/Probability/Distributions/Bernoulli.lean:49` | 17 §7 |
| `Bin(n, p)`、`Bin(R, n, p)` | `binomial n p`；后者是它在 `R` 里的像 | `open ProbabilityTheory` | `Mathlib/Probability/Distributions/Binomial.lean:59`、`:62` | 17 §7；21 §7 |
| `setBer(u, p)` | `setBernoulli u p`，随机子集 | `open ProbabilityTheory` | `Mathlib/Probability/Distributions/SetBernoulli.lean:47` | 19 §7 |
| `G(V, p)` | `SimpleGraph.binomialRandom V p` | `open SimpleGraph` | `Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean:50` | 20 §2 |
| `I`、`σ p` | `unitInterval`、`unitInterval.symm p` | `open unitInterval` | `Mathlib/Topology/UnitInterval.lean:36`、`:78` | 20 §3；17 §7 |
| `𝔼[X \| m]` | 对 `volume` 的条件期望 `condExp m volume X` | `open ProbabilityTheory` | `Mathlib/Probability/Notation.lean:43` | 本书未演示 |
| `μ[X \| m]` | 条件期望 `condExp m μ X`（`scoped macro`） | `open MeasureTheory` | `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:110` | 本书未演示 |

## 7. 经典逻辑

| 写法 | 作用 | 定义处 | 本书 |
|---|---|---|---|
| `open Classical in`、`open scoped Classical in` | 激活 `scoped` 实例 `Classical.propDecidable`（优先级 `low`），让任意命题有 `Decidable` 实例 | `Init/Classical.lean:81` | 8 §12；12 §11；18 §4；20 §7；21 §8 |
| `classical`（策略） | 只在一个证明内部启用同一实例 | — | 8 §12；12 §11 |

用法约定（第 8 章 §12）：证明里用 `classical`；定义或陈述需要可判定性时，在那一条声明前写 `open Classical in`
（第 20 章 §7 把它写在文档注释之前）。整文件的 `open Classical` 会让陈述悄悄带上不可计算的实例，本书不用。
`classical` 救不了陈述，见第 12 章 §12 第 4 条。
