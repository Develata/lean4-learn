module

public import Mathlib.Basic.Nonempty
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.TypeStar

/-!
# 第 7 章　集合、函数与子类型

前六章的对象大多是数、命题和自己定义的归纳类型。从本章起，你开始使用 Mathlib 里真正的数学对象：
set（集合）、function（函数）的 injective（单射）、surjective（满射）与 bijective（双射）、subtype（子类型）、
`Equiv`（等价对应）。它们是之后所有章节的底座：filter（滤子）是集合的集合，measure（测度）定义在集合上，
随机变量是函数。读完本章，你能读懂并写出集合恒等式与单射、满射的证明，知道每个断言在 Mathlib 里叫什么名字，
也知道怎样从 `∃` 的证明里取出数据。

## 学习目标
- 说出 `Set α` 在本书的 Mathlib 版本里就是谓词 `α → Prop`，会在 `x ∈ {y | p y}` 与 `p x` 之间互相转换，知道 2026 年
  `setOf` 改名为 `Set.ofPred`（以及 `*_setOfPred`）的规则；
- 用 `ext`（`Set.ext`）与 `intro x hx` 证明集合恒等式，认得 `∩ ∪ ᶜ \ univ ∅` 的 `mem_` 引理；
- 使用 image（像）`f '' s` 与 preimage（原像）`f ⁻¹' s`，认得 `⋃ i, s i`；
- 证明 `Function.Injective`、`Function.Surjective`、`Function.Bijective` 的常见命题（复合、`of_comp`、
  `Function.LeftInverse`），注意 `Injective` 的 strict-implicit argument（严格隐式参数）；
- 用 `{x // p x}` 和 `↥s` 造子类型的元素，造 `Equiv`；区分 `Nonempty` 与 `Inhabited`，用 `choose`
  策略和 `Classical.choose` 从 `∃` 取出数据，知道它们为什么是 `noncomputable` 的。

## 前置知识
第 2 章的 `omega`；第 3 章的 anonymous constructor（匿名构造子）`⟨_, _⟩`、`∃`、`Type*` 与 β 规约；第 4 章的
`intro/rcases/rintro/obtain`、`constructor`、`by_cases`、`tauto` 与 `∃!`；第 5 章的 `ext`、`simp only`、
`calc`、`congrArg`、`decide +revert` 与 definitional equality（定义相等）；第 6 章的 `structure` 与
projection（投影）。
-/

@[expose] public section

namespace Lean4Learn.Ch07

/-!
## 1. 集合就是谓词

在本书固定的 Mathlib 版本里，`Set α` 定义为 `α → Prop`：一个集合就是「元素是否属于它」的谓词。写成
`{x | p x}` 的集合记号造出的是 `Set.ofPred p`，它就是 `p` 本身，只是类型改成了 `Set α`；`x ∈ s` 则是把
谓词作用到 `x` 上。不过 `Mathlib/Data/Set/Defs.lean` 的文档注释明说：这个定义是实现细节，不应依赖，
谓词与集合之间请用 `Set.ofPred`（即 `{x | p x}`）和 `∈` 转换。

2026-07-09 起 `setOf` 改名为 `Set.ofPred`，记号 `{x | p x}` 不变。引理名里的 `setOf` 大多按所在命名空间
机械改写（并非穷尽）：写在 `namespace Set` 里的（全名以 `Set.` 开头）改为 `ofPred`，如 `Set.mem_setOf_eq`
变成 `Set.mem_ofPred_eq`（§11.1 演示旧名的弃用警告）；其他命名空间的改为 `setOfPred`，如
`measurableSet_setOf` 变成 `measurableSet_setOfPred`（读源码
`Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean` 核实；本章不 import 测度论，没有编译演示）。
没有改的有点记号别名 `Measurable.setOf` 和实例 `Set.decidableSetOf` 等。旧名仍是带弃用警告的别名。
-/

example (p : ℕ → Prop) : {x | p x} = Set.ofPred p := rfl

/-- 偶数集：一个谓词，但类型是 `Set ℕ`。 -/
def evens : Set ℕ := {n | n % 2 = 0}

/-!
判断 `x ∈ evens` 有四种写法，都能证明「成员关系就是谓词成立」：`Iff.rfl`（两边定义相等）、
`rw [Set.mem_ofPred_eq]`、`simp`、以及直接用引理 `Set.mem_ofPred`；`show` 把目标改成定义相等的形式。
本章统一的做法：`Iff.rfl` 与 `show` 靠的是 `Set` 的定义，随版本易碎，只用来对刚写下的定义做一次性检查；
写进引理的证明，走 `Set.mem_ofPred_eq`、`simp` 或 `Set.mem_ofPred`。
-/

example (x : ℕ) : x ∈ evens ↔ x % 2 = 0 := Iff.rfl
example (x : ℕ) : x ∈ evens ↔ x % 2 = 0 := by rw [evens, Set.mem_ofPred_eq]
example (x : ℕ) : x ∈ evens ↔ x % 2 = 0 := by simp [evens]
example (x : ℕ) : x ∈ evens ↔ x % 2 = 0 := Set.mem_ofPred

example : (4 : ℕ) ∈ evens := by
  show 4 % 2 = 0       -- 成员关系就是把谓词用到 4 上
  rfl

/-!
`Set.mem_ofPred_eq` 是一个**等式**（两个命题相等，也是 `simp` 引理）；`Set.mem_ofPred` 是 `↔`，
适合 `.mp`、`.mpr` 与 `exact`。带限制的记号 `{x ∈ s | p x}` 是 `{x | x ∈ s ∧ p x}`：
-/

example (s : Set ℕ) (x : ℕ) : x ∈ {y ∈ s | 2 < y} ↔ x ∈ s ∧ 2 < x := Set.mem_sep_iff

/-!
## 2. 子集与外延性

subset（子集）`s ⊆ t` 的意思是 `∀ x, x ∈ s → x ∈ t`，所以证明它就是 `intro x hx`。注意其中的 `x` 是
strict-implicit（严格隐式）的 `⦃x⦄`（见 `Mathlib/Data/Set/Defs.lean` 里 `Set.Subset` 的定义）：已知
`h : s ⊆ t` 与 `hx : x ∈ s`，写 `h hx`，不要像普通 `∀` 那样写 `h x hx`（§11.3 对 `Injective` 演示了
同一种报错）。（2026-05 起 `⊆` 在 `Set` 上展开为序关系 `≤`，两者定义相等：`s ⊆ t ↔ s ≤ t` 由 `Iff.rfl`
证明；`Set.subset_def` 给出展开形式。）
-/

example (s t : Set ℕ) : s ∩ t ⊆ s := by
  intro x hx          -- hx : x ∈ s ∩ t
  exact hx.1          -- `x ∈ s ∩ t` 就是 `x ∈ s ∧ x ∈ t`

example (s t : Set ℕ) : s ∩ t ⊆ s := fun _ hx ↦ hx.1       -- 项模式

example (s t : Set ℕ) : s ⊆ t ↔ s ≤ t := Iff.rfl
example (s t : Set ℕ) : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := Set.subset_def
example (s t : Set ℕ) (h : s ⊆ t) (x : ℕ) (hx : x ∈ s) : x ∈ t := h hx       -- ⦃x⦄ 自动补全

/-!
证明两个集合**相等**用 extensionality（外延性）：两个集合有相同的元素就相等，即
`Set.ext : (∀ x, x ∈ a ↔ x ∈ b) → a = b`。策略 `ext x` 应用它并引入 `x`。得到的是 `↔`，用
`constructor` 拆成两个方向。另一条路是 `Set.Subset.antisymm`：证两个方向的 `⊆`。
-/

example (s t : Set ℕ) : s ∩ t = t ∩ s := by
  ext x                        -- ⊢ x ∈ s ∩ t ↔ x ∈ t ∩ s
  constructor                  -- 第一个目标 ⊢ x ∈ s ∩ t → x ∈ t ∩ s
  · rintro ⟨hs, ht⟩            -- hs : x ∈ s，ht : x ∈ t，⊢ x ∈ t ∩ s
    exact ⟨ht, hs⟩
  · rintro ⟨ht, hs⟩
    exact ⟨hs, ht⟩

example (s t : Set ℕ) : s ∩ t = t ∩ s := Set.ext fun _ ↦ and_comm      -- `Set.ext` 的项模式

example (s t : Set ℕ) : s ∩ t = t ∩ s :=
  Set.Subset.antisymm (fun _ ⟨hs, ht⟩ ↦ ⟨ht, hs⟩) (fun _ ⟨ht, hs⟩ ↦ ⟨hs, ht⟩)

example (s t : Set ℕ) (h : s = t) (x : ℕ) : x ∈ s ↔ x ∈ t := Set.ext_iff.mp h x

/-!
## 3. 运算与它们的 `mem_` 引理

| 记号 | 名字 | 成员关系 |
|---|---|---|
| `s ∩ t` | 交 | `Set.mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t` |
| `s ∪ t` | 并 | `Set.mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t` |
| `sᶜ` | 补集 | `Set.mem_compl_iff s x : x ∈ sᶜ ↔ x ∉ s` |
| `s \ t` | 差集 | `Set.mem_sdiff x : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t` |
| `Set.univ` | 全集 | `Set.mem_univ x : x ∈ Set.univ` |
| `∅` | 空集 | `Set.notMem_empty x : x ∉ ∅` |

引理名很有规律：`mem_` 加运算名（第 9 章细讲），记不住时先 `exact?`（第 2 章）。各引理的参数显式程度
不同（上表照源码写出），拿不准就 `#check @Set.mem_union`。差集旧名里的 `diff` 在 2026-06-03 改成了
`sdiff`（§11.1）。
-/

example (s t : Set ℕ) (x : ℕ) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := Set.mem_inter_iff x s t
example (s t : Set ℕ) (x : ℕ) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := Set.mem_union x s t
example (s : Set ℕ) (x : ℕ) : x ∈ sᶜ ↔ x ∉ s := Set.mem_compl_iff s x
example (s t : Set ℕ) (x : ℕ) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Set.mem_sdiff x
example (x : ℕ) : x ∈ (Set.univ : Set ℕ) := Set.mem_univ x
example (x : ℕ) : x ∉ (∅ : Set ℕ) := Set.notMem_empty x

/-!
把这些 `mem_` 引理交给 `simp only`，成员关系就化成了命题逻辑，剩下的交给第 4 章的 `tauto`。这是
集合恒等式最常用的三步：`ext x`，`simp only [...]`，`tauto`。
-/

example (s t : Set ℕ) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]
  -- ⊢ ¬(x ∈ s ∨ x ∈ t) ↔ x ∉ s ∧ x ∉ t
  tauto

example (s t : Set ℕ) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := Set.compl_union s t     -- Mathlib 里已有

/-!
下面是分配律的手工证明，同样的形状：`ext`，`constructor`，`rintro` 拆开假设，再 `exact` 重新拼起来。
-/

example (s t u : Set ℕ) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u := by
  ext x
  constructor
  · rintro ⟨hs, ht | hu⟩
    · exact Or.inl ⟨hs, ht⟩
    · exact Or.inr ⟨hs, hu⟩
  · rintro (⟨hs, ht⟩ | ⟨hs, hu⟩)
    · exact ⟨hs, Or.inl ht⟩
    · exact ⟨hs, Or.inr hu⟩

/-!
`Set.univ` 是最大的集合：`Set.subset_univ s : s ⊆ Set.univ`；证明某个集合是空集，用
`Set.eq_empty_iff_forall_notMem`。
-/

example (s : Set ℕ) : s ⊆ Set.univ := Set.subset_univ s
example (s : Set ℕ) : s ∩ sᶜ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxc⟩
  exact hxc hx

/-!
## 4. 像与原像

给定 `f : α → β`：

- 集合 `s : Set α` 的 image（像）是 `f '' s = {y | ∃ x ∈ s, f x = y}`；
- 集合 `t : Set β` 的 preimage（原像）是 `f ⁻¹' t = {x | f x ∈ t}`。

两个记号的优先级是 `infixr:80`，所以 `f '' f ⁻¹' t` 解析成 `f '' (f ⁻¹' t)`。

像的成员关系 `Set.mem_image f s y : y ∈ f '' s ↔ ∃ x ∈ s, f x = y` 有三个**显式**参数。原像的
`Set.mem_preimage` 参数全是隐式，它由 `Iff.rfl` 证明。因为 `∃ x ∈ s, f x = y` 展开是
`∃ x, x ∈ s ∧ f x = y`，所以用匿名构造子造成员：**witness（见证）** `x`，加 `x ∈ s` 的证明，再加
`f x = y` 的证明，即 `⟨x, hx, rfl⟩`；拆开时用 `rintro _ ⟨x, hx, rfl⟩`，`rfl` 把 `y` 换成 `f x`。
-/

example (f : ℕ → ℕ) (s : Set ℕ) (a : ℕ) (h : a ∈ s) : f a ∈ f '' s := ⟨a, h, rfl⟩
example (f : ℕ → ℕ) (s : Set ℕ) (y : ℕ) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y := Set.mem_image f s y
example (f : ℕ → ℕ) (t : Set ℕ) (a : ℕ) : a ∈ f ⁻¹' t ↔ f a ∈ t := Set.mem_preimage
example (f : ℕ → ℕ) (t : Set ℕ) : f '' f ⁻¹' t = f '' (f ⁻¹' t) := rfl     -- 优先级

example (s : Set ℕ) : (fun n : ℕ ↦ n + 1) '' s ⊆ {m | 1 ≤ m} := by
  rintro _ ⟨x, hx, rfl⟩          -- ⊢ (fun n ↦ n + 1) x ∈ {m | 1 ≤ m}，尚未 β 规约
  show 1 ≤ x + 1                 -- 用 `show` 写出 β 规约且展开成员关系后的目标
  omega

/-!
下面这条等价是 `Set.image_subset_iff`。方向 `→` 用「构造」，方向 `←` 用「拆开」：
-/

example {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h hx

example {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
  Set.image_subset_iff

/-!
像与并集可交换（`Set.image_union`）；对交集只有一个方向的包含（`Set.image_inter_subset`）。
反方向一般不成立（反例见下），在 `f` 单射时成立（练习 7.7）：
-/

example {α β : Type*} (f : α → β) (s t : Set α) : f '' (s ∪ t) = f '' s ∪ f '' t :=
  Set.image_union f s t

example {α β : Type*} (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
  Set.image_inter_subset f s t

example : ¬ ∀ (f : ℕ → ℕ) (s t : Set ℕ), f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro h
  -- 取 f = 0、s = {0}、t = {1}：0 在两个像里，但 s ∩ t 空（`Set.mem_singleton a : a ∈ {a}`）
  have h0 : (0 : ℕ) ∈ (fun _ : ℕ ↦ (0 : ℕ)) '' ({0} : Set ℕ) ∩
      (fun _ : ℕ ↦ (0 : ℕ)) '' ({1} : Set ℕ) :=
    ⟨⟨0, Set.mem_singleton 0, rfl⟩, ⟨1, Set.mem_singleton 1, rfl⟩⟩
  obtain ⟨x, ⟨hx0, hx1⟩, -⟩ := h (fun _ ↦ 0) {0} {1} h0
  rw [Set.mem_singleton_iff] at hx0 hx1
  omega

/-!
像与原像互相抵消，需要单射或满射：

- `Set.preimage_image_eq s (h : Function.Injective f) : f ⁻¹' (f '' s) = s`；
- `Set.image_preimage_eq t (h : Function.Surjective f) : f '' (f ⁻¹' t) = t`。
-/

example {α β : Type*} (f : α → β) (hf : Function.Injective f) (s : Set α) :
    f ⁻¹' (f '' s) = s := Set.preimage_image_eq s hf
example {α β : Type*} (f : α → β) (hf : Function.Surjective f) (t : Set β) :
    f '' (f ⁻¹' t) = t := Set.image_preimage_eq t hf

/-!
## 5. 指标并与指标交

对一族集合 `s : ι → Set α`，`⋃ i, s i` 是并集，`⋂ i, s i` 是交集。可数个事件的并与交（概率论里的
σ-代数、Borel–Cantelli 引理）都写成这种形式。成员关系是
`Set.mem_iUnion : x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i` 与 `Set.mem_iInter : x ∈ ⋂ i, s i ↔ ∀ i, x ∈ s i`：
并集是「存在某个 `i`」，交集是「对所有 `i`」。常用的还有 `Set.subset_iUnion s j : s j ⊆ ⋃ i, s i` 与
`Set.iUnion_subset (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t`。
-/

example {α ι : Type*} (s : ι → Set α) (x : α) : x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i := Set.mem_iUnion
example {α ι : Type*} (s : ι → Set α) (x : α) : x ∈ ⋂ i, s i ↔ ∀ i, x ∈ s i := Set.mem_iInter
example {α ι : Type*} (s : ι → Set α) (j : ι) : s j ⊆ ⋃ i, s i := Set.subset_iUnion s j
example {α ι : Type*} (s : ι → Set α) (t : Set α) (h : ∀ i, s i ⊆ t) : ⋃ i, s i ⊆ t :=
  Set.iUnion_subset h

-- `⋃ i, …` 的体一直延伸到右边：`⋃ i, s i ∩ t` 就是 `⋃ i, (s i ∩ t)`
example {α ι : Type*} (s : ι → Set α) (t : Set α) : (⋃ i, s i) ∩ t = ⋃ i, s i ∩ t := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i, hi⟩, ht⟩
    exact ⟨i, hi, ht⟩
  · rintro ⟨i, hi, ht⟩
    exact ⟨⟨i, hi⟩, ht⟩

/-!
## 6. 单射、满射与双射

三个概念都是返回命题的定义：

- `Function.Injective f := ∀ ⦃a b⦄, f a = f b → a = b`（单射）；
- `Function.Surjective f := ∀ b, ∃ a, f a = b`（满射）；
- `Function.Bijective f := Function.Injective f ∧ Function.Surjective f`（双射）。

`Injective` 的 `a b` 用的是 strict-implicit（严格隐式）括号 `⦃ ⦄`：只有当后面的显式参数出现时，
它们才被推断出来。结果是：从 `hf : Function.Injective f` 和 `h : f a = f b` 得到 `a = b`，写
`hf h`，不写 `hf a b h`（§11.3）。满射是 `∀ ∃`，用 `obtain ⟨a, rfl⟩ := hs b` 取出原像。

下面的函数是用 `fun` 写出的，`intro` 之后假设里留着没有 β 规约的 `(fun n ↦ 2 * n + 1) a`，而 `omega`
把它当作不透明的原子（§11.5 演示报错）。本章的做法：假设用 `dsimp only at h`（不带引理的 `dsimp`，只做
β 规约一类的基本化简），目标用 `show` 写出规约后的形式。
-/

example {α β : Type*} (f : α → β) :
    Function.Injective f ↔ ∀ a b, f a = f b → a = b := Iff.rfl

example (f : ℕ → ℕ) (hf : Function.Injective f) (a b : ℕ) (h : f a = f b) : a = b := hf h

example : Function.Injective (fun n : ℕ ↦ 2 * n + 1) := by
  intro a b h
  dsimp only at h          -- h : 2 * a + 1 = 2 * b + 1
  omega

example : Function.Surjective (fun n : ℤ ↦ n + 1) := by
  intro y
  refine ⟨y - 1, ?_⟩         -- 见证 y - 1
  show y - 1 + 1 = y         -- 目标 `(fun n ↦ n + 1) (y - 1) = y` 的 β 规约形式
  omega

example : ¬ Function.Surjective (fun n : ℕ ↦ n + 1) := by
  intro h
  obtain ⟨a, ha⟩ := h 0     -- ha : (fun n ↦ n + 1) a = 0
  dsimp only at ha
  omega

/-!
复合 `g ∘ f` 定义为 `fun x ↦ g (f x)`（读作「g 复合 f」，先 `f` 后 `g`），所以 `(g ∘ f) a` 与 `g (f a)`
定义相等，下面的证明靠这一点。复合保持单射与满射（核心库里的 `Function.Injective.comp`、
`Function.Surjective.comp`）。先手工证明一遍，再看两条反方向的引理 `Function.Injective.of_comp`、
`Function.Surjective.of_comp`。
-/

example {α β γ : Type*} (g : β → γ) (f : α → β) (a : α) : (g ∘ f) a = g (f a) := rfl

theorem injective_comp {α β γ : Type*} {g : β → γ} {f : α → β}
    (hg : Function.Injective g) (hf : Function.Injective f) : Function.Injective (g ∘ f) := by
  intro a b h              -- h : (g ∘ f) a = (g ∘ f) b
  exact hf (hg h)

theorem surjective_comp {α β γ : Type*} {g : β → γ} {f : α → β}
    (hg : Function.Surjective g) (hf : Function.Surjective f) : Function.Surjective (g ∘ f) := by
  intro c
  obtain ⟨b, rfl⟩ := hg c
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, rfl⟩

example {α β γ : Type*} {g : β → γ} {f : α → β} (hinj : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  intro a b h
  exact hinj (congrArg g h)       -- 把 f a = f b 两边套上 g

example {α β γ : Type*} {g : β → γ} {f : α → β} (hsurj : Function.Surjective (g ∘ f)) :
    Function.Surjective g := by
  intro c
  obtain ⟨a, ha⟩ := hsurj c
  exact ⟨f a, ha⟩                 -- g (f a) = c 正是 ha

example {α β γ : Type*} {g : β → γ} {f : α → β} (hg : Function.Injective g)
    (hf : Function.Injective f) : Function.Injective (g ∘ f) := Function.Injective.comp hg hf
example {α β γ : Type*} {g : β → γ} {f : α → β} (hg : Function.Surjective g)
    (hf : Function.Surjective f) : Function.Surjective (g ∘ f) := Function.Surjective.comp hg hf
example {α β γ : Type*} {g : β → γ} {f : α → β} (h : Function.Injective (g ∘ f)) :
    Function.Injective f := Function.Injective.of_comp h
example {α β γ : Type*} {g : β → γ} {f : α → β} (h : Function.Surjective (g ∘ f)) :
    Function.Surjective g := Function.Surjective.of_comp h

/-!
注意方向：`g ∘ f` 单射推出**内层** `f` 单射，`g ∘ f` 满射推出**外层** `g` 满射。Mathlib 的 `of_comp`
把内层写成 `g`、外层写成 `f`，字母与这里相反，命题相同（`Surjective.of_comp` 同样）：
-/

/--
info: @Function.Injective.of_comp : ∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} {f : α → β}
  {g : γ → α}, Function.Injective (f ∘ g) → Function.Injective g
-/
#guard_msgs (whitespace := lax) in
#check @Function.Injective.of_comp

/-!
`Function.Bijective f` 是合取 `Injective f ∧ Surjective f`（一个命题），所以 `⟨hinj, hsurj⟩` 造出它。
`Function.bijective_iff_existsUnique` 把它改写成「每个 `b` 恰有一个原像」，正好用到第 4 章的 `∃!`：
-/

theorem succ_bijective : Function.Bijective (fun n : ℤ ↦ n + 1) := by
  refine ⟨fun a b h ↦ ?_, fun y ↦ ⟨y - 1, ?_⟩⟩
  · dsimp only at h
    omega
  · show y - 1 + 1 = y
    omega

example : ∀ y : ℤ, ∃! x : ℤ, x + 1 = y :=
  (Function.bijective_iff_existsUnique (fun n : ℤ ↦ n + 1)).mp succ_bijective

/-!
左逆：`Function.LeftInverse g f := ∀ x, g (f x) = x`，即 `g` 把 `f` 的结果还原；`Function.RightInverse g f`
是 `LeftInverse f g`。有左逆则单射，有右逆则满射；反过来，满射必有右逆（§10 用 `choose` 构造）。
`Function.bijective_iff_has_inverse` 说双射恰是有两侧逆的函数。
-/

theorem pred_leftInverse : Function.LeftInverse (fun n : ℤ ↦ n - 1) (fun n : ℤ ↦ n + 1) := by
  intro n
  show n + 1 - 1 = n
  omega

example : Function.Injective (fun n : ℤ ↦ n + 1) := pred_leftInverse.injective
example : Function.Surjective (fun n : ℤ ↦ n - 1) :=
  Function.RightInverse.surjective pred_leftInverse

example (f : ℤ → ℤ) :
    Function.Bijective f ↔ ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f :=
  Function.bijective_iff_has_inverse

/-!
## 7. 子类型

给定类型 `α` 与谓词 `p : α → Prop`，subtype（子类型）`{x // p x}` 是「满足 `p` 的 `x`」构成的**类型**。
它是一个 structure（结构体，第 6 章），有两个 field（字段）：`val : α` 与 `property : p val`。造一个元素要同时给出值与
证明，即匿名构造子 `⟨x, hx⟩`；取回时 `.1`（即 `.val`）取值，`.2`（即 `.property`）取证明（`x.f` 这种写法叫 dot notation（点记号））。
把 `x : {x // p x}` 当作 `α` 的元素用时，Lean 自动插入 coercion（强制转换）`↑x`（第 8 章详述），它就是 `x.val`。
-/

def one' : {n : ℕ // 0 < n} := ⟨1, by decide⟩

example : one'.1 = 1 := rfl
example : (one' : ℕ) = 1 := rfl
example : 0 < one'.1 := one'.2
example (x : {n : ℕ // 0 < n}) : (x : ℕ) = x.val := rfl
example (a : ℕ) (h h' : 0 < a) : (⟨a, h⟩ : {n : ℕ // 0 < n}) = ⟨a, h'⟩ := rfl   -- 证明无关性

/-- 子类型上的函数：`n ↦ n - 1`，这里 `0 < n` 保证了减法不被截断。 -/
def pred' (n : {n : ℕ // 0 < n}) : ℕ := n.1 - 1

/-!
两个子类型元素只要值相等就相等（证明部分由 proof irrelevance（证明无关性）自动一致，如上面最后一行）：
`Subtype.ext : a.1 = b.1 → a = b`，策略 `ext` 同样可用。
-/

theorem pred'_injective : Function.Injective pred' := by
  intro a b h
  apply Subtype.ext          -- 目标变成 `↑a = ↑b`
  have ha := a.2             -- ha : 0 < ↑a
  have hb := b.2
  have h' : a.1 - 1 = b.1 - 1 := h
  omega

example (a b : {n : ℕ // 0 < n}) (h : a.1 = b.1) : a = b := by
  ext
  exact h

/-!
集合也可以当类型用：`s : Set α` 在需要类型的地方被自动转成 `↥s`（读作「`s` 的底层类型」），它
就是 `{x // x ∈ s}`（定义 `Set.Elem s`，源码 `Mathlib/Data/Set/CoeSort.lean`，下面的 `rfl` 例子验证）。
所以集合 `evens` 的元素是 `⟨4, h⟩`，其中
`h : 4 ∈ evens`；`.2 : ↑x ∈ evens` 的类型是成员关系，可当作 `↑x % 2 = 0` 来用（§1 的定义相等）。
-/

example : ↥evens = {x // x ∈ evens} := rfl

def four : evens := ⟨4, by show 4 % 2 = 0; rfl⟩

example : (four : ℕ) = 4 := rfl

example (x : evens) : (x : ℕ) % 2 = 0 := x.2
example (x : evens) : (x : ℕ) ∈ evens := Subtype.coe_prop x

/-!
## 8. `Equiv`：自带逆映射的双射

`Function.Bijective f` 只是一个命题，逆映射藏在存在量词后面。`α ≃ β`（`Equiv`，等价对应）把数据**打包**：
正向 `toFun`，逆向 `invFun`，以及两条证明 `left_inv`、`right_inv`。
这里的「等价对应」既不是逻辑等价 `↔`，也不是等价关系；「等价」一词只用于后两者（附录 B 的表 D 区分了它们）。

造一个 `Equiv` 用结构体语法。两条证明的类型是 `left_inv : Function.LeftInverse invFun toFun`（§6），
即 `∀ i, invFun (toFun i) = i`，以及 `right_inv : Function.RightInverse invFun toFun`，即
`∀ b, toFun (invFun b) = b`。下面是 `Fin 2 ≃ Bool`（Mathlib 里已有同样的对应 `finTwoEquiv`，逆映射写法略有
不同，我们手写一次）。`i == 1` 是返回 `Bool` 的比较，`if b then …` 里的 `b : Bool` 被当作命题
`b = true`；`left_inv` 用 `decide +revert`，因为 `Fin 2` 有限、命题可判定（第 5 章）：
-/

def fin2Bool : Fin 2 ≃ Bool where
  toFun i := i == 1
  invFun b := if b then 1 else 0
  left_inv i := by decide +revert
  right_inv b := by cases b <;> rfl

/-!
`e x` 是正向（它是 `⇑e x`，一个自动插入的 coercion，第 8 章），`e.symm y` 是逆向，
`Equiv.symm_apply_apply` 与 `Equiv.apply_symm_apply` 是两条逆律，
`e.bijective` 把它变回前面的概念。
-/

example : fin2Bool 0 = false := rfl
example : fin2Bool.symm true = 1 := rfl
example (i : Fin 2) : fin2Bool.symm (fin2Bool i) = i := fin2Bool.symm_apply_apply i
example (b : Bool) : fin2Bool (fin2Bool.symm b) = b := fin2Bool.apply_symm_apply b
example : Function.Bijective fin2Bool := fin2Bool.bijective
example : Fin 2 ≃ Bool := finTwoEquiv

/-!
反过来，已知双射要得到 `Equiv`：`Equiv.ofBijective f hf`。它的逆映射要从「存在」里取出数据，用到
选择公理（§10），因此是 `noncomputable`（不可计算）的：选择公理不提供算法，Lean 也就没有可运行的代码可
生成（源码 `Mathlib/Logic/Equiv/Defs.lean`；§11.6 演示忘记标注的报错）。但
`(Equiv.ofBijective f hf) x = f x` 总是 `rfl`。
`e₁.trans e₂` 说明等价对应本身可以复合：
-/

noncomputable def succEquiv : ℤ ≃ ℤ := Equiv.ofBijective (fun n : ℤ ↦ n + 1) succ_bijective

example (n : ℤ) : succEquiv n = n + 1 := rfl
example : (succEquiv.trans succEquiv) 0 = 2 := by
  show (0 : ℤ) + 1 + 1 = 2
  rfl

/-!
## 9. `Nonempty` 与 `Inhabited`

两者都说「类型 `α` 里有元素」，区别在于 `Nonempty α` 是 `Prop`（只断言存在，不给出元素），
`Inhabited α` 是 `Type` 里的类，带着一个具体元素 `default`。有 `Inhabited` 必有 `Nonempty`
（方括号 `[Inhabited α]` 是 instance-implicit argument（实例隐式参数），由 Lean 自动提供，第 8 章详述）；
反过来要从 `Nonempty` 取出元素，必须用 axiom of choice（选择公理）`Classical.choice`，所以 `Nonempty.some` 是
`noncomputable` 的（源码 `Mathlib/Basic/Nonempty.lean`；§11.6 的报错是同一类）。
集合上的 `Set.Nonempty s`（即 `∃ x, x ∈ s`）与 `Nonempty ↥s` 等价
（`Set.nonempty_coe_sort`）。
-/

example : Prop := Nonempty ℕ            -- `Nonempty α` 是命题
example : Type := Inhabited ℕ           -- `Inhabited α` 是类型
example : Nonempty ℕ := ⟨0⟩
example (α : Type) [Inhabited α] : Nonempty α := ⟨default⟩
noncomputable example (α : Type) (h : Nonempty α) : α := h.some
example (s : Set ℕ) : s.Nonempty ↔ ∃ x, x ∈ s := Iff.rfl
example (s : Set ℕ) : Nonempty ↥s ↔ s.Nonempty := Set.nonempty_coe_sort
example (s : Set ℕ) (h : s.Nonempty) : h.some ∈ s := h.some_mem

/-!
## 10. 选择公理：`Classical.choose` 与 `choose`

有 `h : ∃ x, p x` 并不能「取出」`x` 做数据：`∃` 住在 `Prop`，而 `Prop` 的消去只能得到 `Prop`
（第 3 章 §9；§11.4 展示报错）。
选择公理给出例外：`Classical.choose h : α` 是某个满足 `p` 的 `x`（具体是哪个无从知道），
`Classical.choose_spec h : p (Classical.choose h)` 证明它满足 `p`。点记号 `h.choose`、`h.choose_spec`
实际解析为核心库的 `Exists.choose`、`Exists.choose_spec`（`Classical.choose` 的可约化包装），作用相同。
数据依赖 `Classical.choose` 的 `def` 必须标 `noncomputable`：选择公理只断言存在、不给算法，所以没有可
执行的代码（§11.6）。
-/

noncomputable def pick (h : ∃ n : ℕ, 5 < n) : ℕ := Classical.choose h

theorem pick_spec (h : ∃ n : ℕ, 5 < n) : 5 < pick h := Classical.choose_spec h

example (h : ∃ n : ℕ, 5 < n) : 5 < h.choose := h.choose_spec

/-!
对 `∀ a, ∃ b, r a b` 这种形状，`choose f hf using h` 把全部取好：新增函数 `f : α → β` 与性质
`hf : ∀ a, r a (f a)`。（外层的 `∀` 变成函数参数，这叫 Skolem 化。）下面用它证明满射有右逆；
`Function.Surjective f` 展开就是 `∀ b, ∃ a, f a = b`，所以 `choose` 直接认得：
-/

theorem surjective_rightInverse {α β : Type*} {f : α → β} (hf : Function.Surjective f) :
    ∃ g : β → α, ∀ b, f (g b) = b := by
  choose g hg using hf       -- g : β → α，hg : ∀ b, f (g b) = b
  exact ⟨g, hg⟩

example {α β : Type*} {f : α → β} (hf : Function.Surjective f) (b : β) :
    f (Function.surjInv hf b) = b := Function.surjInv_eq hf b

/-!
Mathlib 的 `Function.surjInv h` 用同样的办法定义了这个右逆，性质是 `surjInv_eq`。
结论：从 `∃` 到数据要付出代价——选择公理，以及丢掉可计算性。能给出显式见证时（如上面 `y - 1`），
总是优先用见证。

## 11. 常见错误

**1. 弃用的名字。** 旧教程里到处是 `Set.mem_setOf_eq`，它现在是弃用别名，警告里给出了新名字。差集的
`Set.mem_diff` 也一样：`diff` 在 2026-06-03 改成了 `sdiff`：
-/

/-- warning: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead -/
#guard_msgs (substring := true) in
example (p : ℕ → Prop) (x : ℕ) : x ∈ {y | p y} ↔ p x := by
  rw [Set.mem_setOf_eq]

/-- warning: `Set.mem_diff` has been deprecated: Use `Set.mem_sdiff` instead -/
#guard_msgs (substring := true) in
example (s t : Set ℕ) (x : ℕ) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Set.mem_diff x

/-!
**2. 想当然的 `Set.mem_def`。** 它不存在（`Set.mem_ofPred_eq`、`Iff.rfl` 或 `show` 才是办法）：
-/

/-- error: Unknown constant `Set.mem_def` -/
#guard_msgs in
example (x : ℕ) : x ∈ evens ↔ x % 2 = 0 := Set.mem_def

/-!
**3. 对 `Injective` 假设显式传 `a b`。** 它们是严格隐式参数，写 `hf a b h` 会把 `a` 当成 `f a = f b`
的证明（`⊆` 的假设也一样，`h x hx` 同理）：
-/

/--
error: Application type mismatch: The argument
  a
has type
  ℕ
of sort `Type` but is expected to have type
  f ?_ = f ?_
of sort `Prop` in the application
  hf a
-/
#guard_msgs in
set_option pp.mvars false in
example (f : ℕ → ℕ) (hf : Function.Injective f) (a b : ℕ) (h : f a = f b) : a = b :=
  hf a b h

/-!
**4. 用 `obtain` 从 `∃` 取数据。** `∃` 只能消去到 `Prop`（第 3 章 §9）；要构造 `Type` 里的东西，改用
`Classical.choose` 或 `choose`：
-/

/--
error: Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`

h : ∃ n, 5 < n
⊢ ℕ
-/
#guard_msgs in
def bad (h : ∃ n : ℕ, 5 < n) : ℕ := by
  obtain ⟨n, _⟩ := h
  exact n

/-!
**5. `omega` 看不见没有 β 规约的函数应用。** 假设里的 `(fun n ↦ 2 * n + 1) a` 被当成原子 `c`，
反例里 `a`、`b` 与它没有任何关系。先 `dsimp only at h`（目标里则用 `show`）：
-/

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  e ≥ 0
  d ≥ 0
  d - e ≥ 1
  c ≥ 0
where
 c := ↑((fun n ↦ 2 * n + 1) b)
 d := ↑b
 e := ↑a
-/
#guard_msgs (whitespace := lax) in
example : Function.Injective (fun n : ℕ ↦ 2 * n + 1) := by
  intro a b h
  omega

/-!
**6. 忘记 `noncomputable`。** 数据依赖 `Classical.choose` 的 `def` 无法编译成代码：
-/

/-- error: failed to compile definition, consider marking it as 'noncomputable' -/
#guard_msgs (substring := true) in
def pick2 (h : ∃ n : ℕ, 5 < n) : ℕ := Classical.choose h

/-!
## 练习

复习前面章节的题在题干里写明章号。
-/

/-- 练习 7.1（★）：复习第 3 章的项模式。交集包含于并集。提示：`fun x hx ↦ Or.inl hx.1`。 -/
theorem ex_7_1 {α : Type*} (s t : Set α) : s ∩ t ⊆ s ∪ t := sorry

/-- 练习 7.2（★）：差集 `s \ t` 与被减去的集合 `t` 的交为空。
提示：`Set.eq_empty_iff_forall_notMem`，再 `rintro`。 -/
theorem ex_7_2 {α : Type*} (s t : Set α) : (s \ t) ∩ t = ∅ := sorry

/-- 练习 7.3（★）：复习第 4 章的 `tauto`。De Morgan 律。提示：`ext x`，`simp only` 化成命题，`tauto`。 -/
theorem ex_7_3 {α : Type*} (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := sorry

/-- 练习 7.4（★★）：并集的泛性质。提示：`constructor`；`→` 用 `fun x hx ↦ h (Or.inl hx)`，`←` 用 `rintro`。 -/
theorem ex_7_4 {α : Type*} (s t u : Set α) : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u := sorry

/-- 练习 7.5（★★）：像对交集的包含。不要直接用 `Set.image_inter_subset`。
提示：`rintro _ ⟨x, ⟨hs, ht⟩, rfl⟩`。 -/
theorem ex_7_5 {α β : Type*} (f : α → β) (s t : Set α) : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := sorry

/-- 练习 7.6（★★）：单射时，`s` 的像的原像还在 `s` 里（`f ⁻¹' (f '' s) ⊆ s`）。
提示：`rintro x ⟨y, hy, hxy⟩`，再用 `hf hxy` 得到 `y = x`，然后 `obtain rfl`（或 `subst`）。 -/
theorem ex_7_6 {α β : Type*} (f : α → β) (hf : Function.Injective f) (s : Set α) :
    f ⁻¹' (f '' s) ⊆ s := sorry

/-- 练习 7.7（★★）：单射时像对交集的包含反向也成立（§4 的反例说明一般情形不成立）。
提示：`rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩`，再用 `hf hxy` 得到 `y = x`。 -/
theorem ex_7_7 {α β : Type*} (f : α → β) (hf : Function.Injective f) (s t : Set α) :
    f '' s ∩ f '' t ⊆ f '' (s ∩ t) := sorry

/-- 练习 7.8（★）：复习第 2 章的 `omega`。`x ↦ 3x + 1` 在 `ℤ` 上是单射。
提示：`intro a b h`，`dsimp only at h`，`omega`。 -/
theorem ex_7_8 : Function.Injective (fun x : ℤ ↦ 3 * x + 1) := sorry

/-- 练习 7.9（★）：复习第 2、4 章。`n ↦ 2n` 不是 `ℕ → ℕ` 的满射。
提示：取 `1` 的原像，`dsimp only at ha`，`omega`。 -/
theorem ex_7_9 : ¬ Function.Surjective (fun n : ℕ ↦ 2 * n) := sorry

/-- 练习 7.10（★★）：§5 的指标并。`⋃ i, s i ⊆ t` 当且仅当每个 `s i ⊆ t`。
不要直接用 `Set.iUnion_subset`。提示：`constructor`；两个方向各用 `Set.mem_iUnion.mpr`、`.mp`。 -/
theorem ex_7_10 {α ι : Type*} (s : ι → Set α) (t : Set α) :
    ⋃ i, s i ⊆ t ↔ ∀ i, s i ⊆ t := sorry

/-- 练习 7.11（★★）：复习第 5 章的 `calc`。有左逆则单射。不要直接用
`Function.LeftInverse.injective`。提示：`h a : g (f a) = a`，`calc a = g (f a) = g (f b) = b`。 -/
theorem ex_7_11 {α β : Type*} (f : α → β) (g : β → α) (h : Function.LeftInverse g f) :
    Function.Injective f := sorry

/-- 练习 7.12（★）：`choose`。逐点的存在性给出一个函数。提示：`choose f hf using h`。 -/
theorem ex_7_12 {α β : Type*} (r : α → β → Prop) (h : ∀ a, ∃ b, r a b) :
    ∃ f : α → β, ∀ a, r a (f a) := sorry

/-- 练习 7.13（★★）：集合上的 `Nonempty`（§7、§9）。不要直接用 `Set.nonempty_coe_sort`。
提示：`constructor`；`rintro ⟨x, hx⟩` 拆开 `∃`，`⟨⟨x, hx⟩⟩` 造出 `Nonempty ↥s`。 -/
theorem ex_7_13 {α : Type*} (s : Set α) : s.Nonempty ↔ Nonempty ↥s := sorry

/-- 练习 7.14（★★）：造一个 `ℤ ≃ ℤ`，它是 `n ↦ 5 - n`。
提示：`⟨⟨fun n ↦ 5 - n, fun n ↦ 5 - n, ?_, ?_⟩, fun n ↦ rfl⟩`，两条逆律各 `intro n`，`show`，`omega`。 -/
theorem ex_7_14 : ∃ e : ℤ ≃ ℤ, ∀ n, e n = 5 - n := sorry

/-- 练习 7.15（★★★）：复习第 4 章的 `by_cases`。Cantor：没有从 `ℕ` 到它的幂集的满射。
提示：对满射 `f` 取集合 `{k | k ∉ f k}`，设 `n` 是它的原像，问 `n ∈ f n` 是否成立。 -/
theorem ex_7_15 (f : ℕ → Set ℕ) : ¬ Function.Surjective f := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 集合是谓词 | `{x \| p x}`、`Set.mem_ofPred_eq`、`Set.mem_ofPred` | 成员关系与谓词互相转换；`setOf` 已弃用 |
| 子集 | `intro x hx`、`Set.Subset.antisymm` | 证明 `⊆` 与相等的双向包含 |
| 外延性 | `ext x`、`Set.ext`、`Set.ext_iff` | 证明集合相等：化成 `x ∈ s ↔ x ∈ t` |
| 运算 | `∩ ∪ ᶜ \ univ ∅`；`Set.mem_inter_iff` 等 | `ext x; simp only [mem_…]; tauto` |
| 像与原像 | `f '' s`、`f ⁻¹' t`、`⟨x, hx, rfl⟩`、`rintro _ ⟨x, hx, rfl⟩` | 构造或拆开像的成员 |
| 指标并交 | `⋃ i, s i`、`Set.mem_iUnion`、`Set.iUnion_subset` | 并是 `∃ i`，交是 `∀ i` |
| 单射、满射、双射 | `Injective`（`hf h`）、`Surjective`、`Bijective` | `intro a b h`；复合、`of_comp` |
| 子类型 | `{x // p x}`、`⟨x, hx⟩`、`.1/.2`、`↑x`、`Subtype.ext` | 值加证明打包；集合当类型是 `↥s` |
| 等价对应 | `α ≃ β`、`e x`、`e.symm`、`symm_apply_apply`、`Equiv.ofBijective` | 带逆映射的双射，数据而非命题 |
| 选择 | `Classical.choose`、`choose f hf using h`、`noncomputable` | 从 `∃` 取数据，付出不可计算的代价 |
| `Nonempty` / `Inhabited` | `h.some`、`default`、`Set.Nonempty` | `Prop` 的存在 vs 带元素的类 |

## 延伸阅读

- *Mathematics in Lean*：第 4 章「Sets and Functions」（Sets、Functions、The Schröder–Bernstein Theorem）。
- *Theorem Proving in Lean 4*：「Axioms and Computation」中「Choice」一节的 `Classical.choice`。
- Mathlib 源码：`Mathlib/Data/Set/Defs.lean`（`Set`、`Set.ofPred`）、`Mathlib/Data/Set/Operations.lean`
  （`mem_ofPred_eq`、`mem_image`、`mem_preimage`）、`Mathlib/Data/Set/Image.lean`（像与原像）、
  `Mathlib/Logic/Function/Basic.lean`（`surjInv`、`bijective_iff_existsUnique`）、
  `Mathlib/Logic/Function/Defs.lean`（`Bijective`）、
  `Mathlib/Logic/Equiv/Defs.lean`（`Equiv`、`ofBijective`、`finTwoEquiv`）、`Mathlib/Tactic/Choose.lean`。
- 核心库：`Init/Data/Function.lean`（`Injective`、`LeftInverse`、`Injective.comp`）、
  `Init/Classical.lean`（`Classical.choose`、`Exists.choose`）。
- 本书第 8 章（强制转换 `↑`）、第 9 章（怎样查到引理名）、第 12 章（`Finset`）、第 15 章（`SetLike`、
  打包映射）、第 28 章（`Classical.choice` 作为公理，`#print axioms`）。
-/

end Lean4Learn.Ch07

end
