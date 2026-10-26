module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Common
public meta import Lean.Linter.Deprecated
public meta import Mathlib.Tactic.ToAdditive

/-!
# 第 9 章　在 Mathlib 中找到你要的引理

前八章里，引理的名字大多由题面或本书给出。从本章起你要自己找：Mathlib 的定理多到无法逐条背下来，名字遵守一套近乎
机械的 naming convention（命名规范），搜索工具各有适用范围，而且库每个月都在改名。本章把「数学陈述 → 猜名字
→ `#check` 核对 → `exact?` 兜底 → 站外搜索 → 读源码确认」这条链走通，读完后你不再依赖别人告诉你名字。

## 学习目标
- 把一个引理名当句子读：大小写、结论优先、`_of_`、`_iff`、`pos`/`nonneg`、`₀`、撇号、`_left`/`_right`、
  `cast`/`mem`/`apply`/`ext`/`inj`，以及点记号背后的 namespace（命名空间）；
- 按「猜名字 → `#check` → `exact?`」的流程，从一句数学陈述找到引理，并知道每一步在什么时候失败；
- 用 `exact?`、`apply?`、`rw?`、`simp?`、`hint`、`try?` 搜索，读懂 `Try this` 报告；知道 `#loogle`、
  `#leansearch`、Loogle 网页、文档站各自适合什么查询，以及它们为什么领先于本书锁定的版本；
- 读一个真实的 Mathlib 源文件，认出 `to_additive` 孪生名字，解释为什么 `grep` 会漏掉它们；
- 读懂 deprecation（弃用）警告与 `since` 日期，用 `#min_imports` 选最窄的导入，带着 MWE 在 Zulip 提问。

## 前置知识
第 2 章（`exact?` 初体验：它报告 `Right.mul_pos`，日常写 `mul_pos`）；第 3 章（点记号 `h.left`）；第 5 章（`rw`、
`simp`、`simp?`）；第 7 章（`Set`、`Function.Injective`）；第 8 章（type class（类型类）、`Nat.cast`）；第 1 章的 MWE
与 `extract_goal`。点记号用到的 `And.symm`、`Or.resolve_left` 等引理在本章首次出现。`Finset`（有限集）与 `∑ i ∈ s, f i`
（有限和）要到第 12 章才系统讲，这里只把它们当作带命名规律的例子；`|a|` 是绝对值（第 11 章）。
-/

@[expose] public section

namespace Lean4Learn.Ch09

/-!
## 1. 名字的大小写

Mathlib 的规则只有三条：**证明**（类型是某个命题的项，即定理）用 `snake_case`；**类型与命题**（由 `structure`、
`class`、`inductive` 或 `def … : Prop` 定义出来的东西，如 `NeZero`、`Function.Injective`）用 `UpperCamelCase`；
**其余的数据**（函数、`Type` 中的项）用 `lowerCamelCase`。`UpperCamelCase` 的名字嵌进 `snake_case` 的名字时，首字母改成
小写：`NeZero` 变成 `neZero_iff` 里的 `neZero`。`#check` 用同一行打印名字、参数与类型（名字后的 `.{u_1}` 是 universe
level（宇宙层级）参数，读名字时可以忽略；`[CommMagma G]` 是 instance-implicit argument（实例隐式参数），由实例合成填入，
第 8 章）：
-/

/-- info: mul_comm.{u_1} {G : Type u_1} [CommMagma G] (a b : G) : a * b = b * a -/
#guard_msgs in #check mul_comm

/-- info: NeZero.{u_1} {R : Type u_1} [Zero R] (n : R) : Prop -/
#guard_msgs in #check NeZero

/-- info: neZero_iff.{u_1} {R : Type u_1} [Zero R] {n : R} : NeZero n ↔ n ≠ 0 -/
#guard_msgs in #check neZero_iff

/-- info: Set.ofPred.{u} {α : Type u} (p : α → Prop) : Set α -/
#guard_msgs in #check Set.ofPred

/-!
`mul_comm` 是定理（`snake_case`）；`NeZero` 是一个以 `Prop` 为目标类型的类（`UpperCamelCase`）；`neZero_iff`
是关于它的定理；`Set.ofPred` 返回一个 `Set`（数据），所以是 `lowerCamelCase`（第 7 章的 `{x | p x}`）。

## 2. 结论优先与符号词典

定理名描述的是**结论**（不是证明过程），并按结论里符号出现的**书写顺序**排列。把符号换成英文词即可：
`+` `add`、`-`（二元）`sub`、`-`（一元）`neg`、`*` `mul`、`/` `div`、`⁻¹` `inv`、`^` `pow`（`x ^ 2` 常写作
`sq`）、`∣` `dvd`、`≤` `le`、`<` `lt`、`≠` `ne`、`∈` `mem`、`∩` `inter`、`∪` `union`、`∑` `sum`、`∏` `prod`、
`∘` `comp`、`∧` `and`、`∨` `or`、`↔` `iff`、`¬` `not`；`0` `zero`、`1` `one`。下面两个例子，等号两边各读一遍：
-/

/-- info: neg_mul_neg.{u} {α : Type u} [Mul α] [HasDistribNeg α] (a b : α) : -a * -b = a * b -/
#guard_msgs in #check neg_mul_neg

/--
info: sub_add_eq_add_sub.{u_1} {α : Type u_1} [SubtractionCommMonoid α] (a b c : α) :
  a - b + c = a + c - b
-/
#guard_msgs (whitespace := lax) in #check sub_add_eq_add_sub

/-!
`neg_mul_neg` 是 `-a * -b`（先 `neg`，再 `mul`，再 `neg`），而不是 `mul_neg_neg`；`sub_add_eq_add_sub` 的
左边是「减、加」（`a - b + c`），右边是「加、减」（`a + c - b`），等号读作 `eq`。
-/

/-!
## 3. `_of_` 与 `_iff`

`_of_` 隔开 hypothesis（假设），按假设在类型里出现的顺序列出：`A → B → C` 叫 `C_of_A_of_B`。名字常常只写主要的假设，
`0 < n` 这类旁支条件往往不进名字（第 8 节会遇到）。`_iff` 或 `_iff_` 表示结论是 `↔`。`a ≥ b` 只是 `b ≤ a` 的另一种写法；
名字里出现 `ge`、`gt`，说明那个比较的两边相对前面的 `le`、`lt` 调换了。
-/

/--
info: lt_of_le_of_lt.{u_1} {α : Type u_1} [Preorder α] {a b c : α} (hab : a ≤ b) (hbc : b < c) :
  a < c
-/
#guard_msgs (whitespace := lax) in #check lt_of_le_of_lt

/-- info: Nat.succ_le_iff {m n : ℕ} : m.succ ≤ n ↔ m < n -/
#guard_msgs in #check Nat.succ_le_iff

/--
info: lt_iff_le_not_ge.{u_1} {α : Type u_1} [Preorder α] {a b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a
-/
#guard_msgs in #check lt_iff_le_not_ge

/-!
`lt_of_le_of_lt` 的两条假设依次是 `≤` 与 `<`；`lt_iff_le_not_ge` 里的 `ge` 指第二个比较 `b ≤ a` 把参数
调换了（读作 `a ≥ b`）。`↔` 要用 `.mp`（正向）与 `.mpr`（反向）拆开（`m.succ` 即 `m + 1`）：
-/

example (a b : ℕ) (h : a < b) : a.succ ≤ b := Nat.succ_le_iff.mpr h     -- h : a < b ⊢ a.succ ≤ b
example (a b : ℝ) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := le_antisymm_iff.mpr ⟨h₁, h₂⟩
-- 目标 `a = b`；`le_antisymm_iff : a = b ↔ a ≤ b ∧ b ≤ a`，`.mpr` 收下一对不等式

/-!
## 4. `pos`/`nonneg`、`₀` 与撇号

变量 `a` 与 `0` 比较时用 `pos`（`0 < a`）、`nonneg`（`0 ≤ a`）、`neg`（`a < 0`，与第 2 节的一元负号无关）、
`nonpos`（`a ≤ 0`），不写 `zero_lt`、`lt_zero`：`mul_pos`、`mul_nonneg`、`sq_nonneg`（常量 `0 < 1` 仍按书写顺序叫
`zero_lt_one`，第 11 节用到它）。同一结论在群、环、域里各有一条，而名字里又没有 `zero`、`pos` 这类「零」的原子时，
**带零的结构**（`GroupWithZero`、域）的那条加后缀 `₀`，通常多一个 `≠ 0` 或 `0 < c` 的前提：
-/

example (G : Type*) [Group G] (a : G) : a * a⁻¹ = 1 := mul_inv_cancel a
example (x : ℝ) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ hx   -- `ℝ` 不是群，要 `x ≠ 0`

/-!
`div_le_iff₀` 是同类的例子（第 8 章已见过 `mul_inv_cancel₀`）：
-/

/--
info: mul_pos.{u_1} {α : Type u_1} [MulZeroClass α] {a b : α} [Preorder α] [PosMulStrictMono α]
  (ha : 0 < a)
  (hb : 0 < b) : 0 < a * b
-/
#guard_msgs (whitespace := lax) in #check mul_pos

/--
info: sub_nonneg.{u} {α : Type u} [AddGroup α] [LE α] [AddRightMono α] {a b : α} : 0 ≤ a - b ↔ b ≤ a
-/
#guard_msgs in #check sub_nonneg

/--
info: div_le_iff₀.{u_3} {G₀ : Type u_3} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀]
  {a b c : G₀}
  (hc : 0 < c) : b / c ≤ a ↔ b ≤ a * c
-/
#guard_msgs (whitespace := lax) in #check div_le_iff₀

/-!
**名字只决定语句的形状，不决定细节**：
`add_pos` 的陈述是更一般的 `b < c → 0 < a → b < c + a`（取 `b := 0` 才是你熟悉的形式），所以永远以 `#check` 为准：
-/

/--
info: add_pos.{u_1} {α : Type u_1} {a b c : α} [AddZeroClass α] [Preorder α] [AddLeftStrictMono α]
  (hbc : b < c)
  (ha : 0 < a) : b < c + a
-/
#guard_msgs (whitespace := lax) in #check add_pos

example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y := add_pos hx hy

/-!
**撇号**（`'`）没有统一含义，常表示「同一件事的另一个版本」。`pow_succ` 与 `pow_succ'` 把新因子放在
右边或左边；第 11 节会看到另一种撇号：把 implicit argument（隐式参数）变成 explicit argument（显式参数）。
-/

/-- info: pow_succ.{u_2} {M : Type u_2} [Monoid M] (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a -/
#guard_msgs in #check pow_succ

/-- info: pow_succ'.{u_2} {M : Type u_2} [Monoid M] (a : M) (n : ℕ) : a ^ (n + 1) = a * a ^ n -/
#guard_msgs in #check pow_succ'

/-!
## 5. `_left`/`_right`、`_comm`/`_assoc` 与方向陷阱

`_comm`、`_assoc`、`_left_comm` 是代数定律的名字（交换、结合、左交换）：`mul_comm a b : a * b = b * a`，
`add_left_comm a b c` 把 `a` 与 `b` 对调。`_left`、`_right` 区分同一结论的两个变体，但**不要凭直觉记左右**——这是最容易
踩的坑。
在本书锁定的版本里，`add_le_add_left bc a` 把 `a` 加在**右边**，`add_le_add_right bc a` 把 `a` 加在**左边**：
-/

/--
info: add_le_add_left.{u_1} {α : Type u_1} {b c : α} [Add α] [LE α] [i : AddRightMono α] (bc : b ≤
  c)
  (a : α) : b + a ≤ c + a
-/
#guard_msgs (whitespace := lax) in #check add_le_add_left

/--
info: add_le_add_right.{u_1} {α : Type u_1} {b c : α} [Add α] [LE α] [AddLeftMono α] (bc : b ≤ c)
  (a : α) : a + b ≤ a + c
-/
#guard_msgs (whitespace := lax) in #check add_le_add_right

/--
info: mul_le_mul_left.{u_1} {α : Type u_1} {b c : α} [Mul α] [LE α] [i : MulRightMono α] (bc : b ≤
  c)
  (a : α) : b * a ≤ c * a
-/
#guard_msgs (whitespace := lax) in #check mul_le_mul_left

/-- info: Nat.mul_le_mul_left {n m : ℕ} (k : ℕ) (h : n ≤ m) : k * n ≤ k * m -/
#guard_msgs in #check Nat.mul_le_mul_left

/-!
最后一条是 Lean 核心库里 `ℕ` 专用的版本，方向和参数顺序都与 Mathlib 的 `mul_le_mul_left` **相反**。
下面的例子依次用到 `mul_assoc`、`add_left_comm`、`add_le_add_right`、`mul_le_mul_left`、`Nat.mul_le_mul_left`、
`mul_le_mul_of_nonneg_left`；注意 `mul_le_mul_left` 的 `[MulRightMono α]` 要求乘法本身保序，`ℕ` 满足而 `ℝ`
不满足（负数），`ℝ` 上要用带 `0 ≤ c` 假设的 `mul_le_mul_of_nonneg_left`：
-/

example (a b c : ℝ) : a * b * c = a * (b * c) := mul_assoc a b c
example (a b c : ℕ) : a + (b + c) = b + (a + c) := add_left_comm a b c   -- 把 `a` 与 `b` 对调
example (a b c : ℝ) (h : a ≤ b) : c + a ≤ c + b := add_le_add_right h c   -- `_right`：`c` 加在左边
example (a b c : ℕ) (h : a ≤ b) : a * c ≤ b * c := mul_le_mul_left h c
example (a b c : ℕ) (h : a ≤ b) : c * a ≤ c * b := Nat.mul_le_mul_left c h
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := mul_le_mul_of_nonneg_left h hc

/-!
## 6. 名字里的函数：`cast`、`mem`、`apply`、`ext`、`inj`

引理若谈论某个函数，名字里就写它：`Nat.cast_add` 是 `Nat.cast` 对 `+` 的结论（`↑(m + n) = ↑m + ↑n`，
`↑` 是第 2 章的 coercion（强制转换），`Nat.cast` 是 cast（类型转换）函数，这一族引理见第 8 章）。
`map_` 前缀用于「任意一个保持结构的映射 `f`」（`f` 是自由变量）作用在具体对象上：`map_natCast f n : f ↑n = ↑n`。
-/

/-- info: Nat.cast_add.{u_1} {R : Type u_1} [AddMonoidWithOne R] (m n : ℕ) : ↑(m + n) = ↑m + ↑n -/
#guard_msgs in #check Nat.cast_add

/--
info: Nat.cast_le.{u_1} {α : Type u_1} [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α]
  [ZeroLEOneClass α]
  [CharZero α] {m n : ℕ} : ↑m ≤ ↑n ↔ m ≤ n
-/
#guard_msgs (whitespace := lax) in #check Nat.cast_le

/--
info: map_natCast.{u_3, u_4, u_5} {R : Type u_3} {S : Type u_4} {F : Type u_5} [NonAssocSemiring R]
  [NonAssocSemiring S] [FunLike F R S] [RingHomClass F R S] (f : F) (n : ℕ) : f ↑n = ↑n
-/
#guard_msgs (whitespace := lax) in #check map_natCast

/-!
**`mem`** 与别的符号一样按书写顺序出现；最常见的形状是 `a ∈ xxx ↔ …`，可以直接 `rw`（`Finset.filter` 是有限集的
过滤，第 12 章）。**`_apply`**：函数本身是由运算构造的（如 `f + g`），自变量是自由变量，`Pi.add_apply` 把
`(f + g) i` 展开成 `f i + g i`。
-/

example (s t : Set ℕ) (a : ℕ) : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t := by rw [Set.mem_inter_iff]

/--
info: Finset.mem_filter.{u_1} {α : Type u_1} {p : α → Prop} [DecidablePred p] {s : Finset α} {a :
  α} :
  a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
#guard_msgs (whitespace := lax) in #check Finset.mem_filter

/--
info: Pi.add_apply.{u_1, u_5} {ι : Type u_1} {M : ι → Type u_5} [(i : ι) → Add (M i)] (f g : (i :
  ι) → M i)
  (i : ι) : (f + g) i = f i + g i
-/
#guard_msgs (whitespace := lax) in #check Pi.add_apply

/--
info: Prod.ext_iff.{u, v} {α : Type u} {β : Type v} {x y : α × β} : x = y ↔ x.1 = y.1 ∧ x.2 = y.2
-/
#guard_msgs in #check Prod.ext_iff

/--
info: Nat.cast_inj.{u_1} {R : Type u_1} [AddMonoidWithOne R] [CharZero R] {m n : ℕ} : ↑m = ↑n ↔ m
  = n
-/
#guard_msgs (whitespace := lax) in #check Nat.cast_inj

/--
info: Nat.cast_injective.{u_1} {R : Type u_1} [AddMonoidWithOne R] [CharZero R] :
  Function.Injective Nat.cast
-/
#guard_msgs (whitespace := lax) in #check Nat.cast_injective

/-!
**`ext`**：extensionality（外延性），用 `@[ext]` attribute（属性）标记的结构与类型会自动得到 `Foo.ext`：各分量
（各点）相等 → 相等；`Foo.ext_iff` 是对应的 `↔`。**`inj` 与 `injective`**：`f_injective` 是 `Function.Injective f`
本身，`f_inj` 是 `f x = f y ↔ x = y`（上面的 `Nat.cast_injective` 与 `Nat.cast_inj`）。
-/

example (p q : ℕ × ℕ) (h₁ : p.1 = q.1) (h₂ : p.2 = q.2) : p = q := Prod.ext h₁ h₂
example (f g : ℕ → ℕ) (h : ∀ x, f x = g x) : f = g := funext h

/-!
## 7. 命名空间与点记号

`h : x < y` 的类型以 `LT.lt` 开头，所以 `h.le` 就是 `LT.lt.le h`：Lean 在类型的头部常量所在的命名空间里
找 `le`（点记号，第 3 章）。这条规则（Lean 手册称 generalized field notation）让 `LT.lt.le`、`LE.le.trans`、
`Or.resolve_left`、`And.symm` 都可以写成点的形式。新的只有命名上的推论：名字里带命名空间的定理，往往就是为点记号
而存在的：
-/

/-- info: LT.lt.le.{u_1} {α : Type u_1} [Preorder α] {a b : α} (hab : a < b) : a ≤ b -/
#guard_msgs in #check LT.lt.le

/-- info: Or.resolve_left {a b : Prop} (h : a ∨ b) (na : ¬a) : b -/
#guard_msgs in #check Or.resolve_left

example (x y : ℝ) (h : x < y) : x ≤ y := h.le                      -- 即 `LT.lt.le h`
example (x y z : ℝ) (h₁ : x ≤ y) (h₂ : y < z) : x < z := h₁.trans_lt h₂
example (p q : Prop) (h : p ∨ q) (hp : ¬p) : q := h.resolve_left hp

/-!
## 8. 工作流：从数学陈述到引理名

先把整条链走一遍，各工具的细节在第 9–11 节。要证：若 `a ∣ b` 且 `b > 0`，则 `a ≤ b`（`ℕ` 上）。分四步。
**第一步，把陈述读成名字**：结论是 `≤`，假设是 `∣` 与 `0 <`，按「结论优先、`_of_` 列假设」猜 `le_of_dvd`；`ℕ` 上的
版本放在 `Nat.` 下。注意这只是猜测，不是推导：名字常常只写主要假设，`0 < b` 没有进名字，所以名字规则不能替代下一步。
**第二步，`#check` 核对**：不但看名字存不存在，还要看假设的顺序和形状（这里 `0 < n` 在 `∣` **之前**）：
-/

/-- info: Nat.le_of_dvd {m n : ℕ} (h : 0 < n) : m ∣ n → m ≤ n -/
#guard_msgs in #check Nat.le_of_dvd

example (a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b := Nat.le_of_dvd hb h

/-!
**第三步，没猜中就问 `exact?`**，它在已导入的全部声明里找一个能直接关闭 goal（目标）的项（可含短的回溯）。这里它给出
同一条：
-/

/--
info: Try this:
  [apply] exact Nat.le_of_dvd hb h
-/
#guard_msgs in
example (a b : ℕ) (h : a ∣ b) (hb : 0 < b) : a ≤ b := by exact?

/-!
**第四步，去文档站或源码确认**（第 10、11 节）：看假设是否多余、是否有更通用的版本、有没有别的名字。
`exact?` 报告的是它**第一个**找到的名字，未必是日常写法。从报告的名字回到日常名字：去掉 `Left.`、`Right.` 这类
限定（它们说明用了哪一侧的假设），试根名字，再用 `example` 或 `#check` 确认陈述一致。第 2 章的 `Right.mul_pos` 就是
这样：根名字 `mul_pos` 是 `Left.mul_pos` 的别名（alias），这些名字在 `ℝ` 上证同一个目标：
-/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := Right.mul_pos ha hb
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb

/-!
下面的目标里，`exact?` 甚至报告了类的字段 `Semigroup.mul_assoc`，而日常名字是 `mul_assoc`：
-/

/--
info: Try this:
  [apply] exact Eq.symm (Semigroup.mul_assoc a b x)
-/
#guard_msgs in
example (a b x : ℝ) : a * (b * x) = (a * b) * x := by exact?

example (a b x : ℝ) : a * (b * x) = (a * b) * x := (mul_assoc a b x).symm

/-!
## 9. 编辑器里的搜索：`exact?` 一族

这些策略都在 Lean 核心库里（`exact?`、`apply?`、`rw?`、`simp?`、`try?`）或 `Mathlib.Tactic.Common` 里
（`hint`），搜索的范围是**当前文件已导入的**声明。它们是调试工具：找到后把建议复制进证明，把搜索删掉。
`exact?` 只找能直接关闭目标的项（它失败时的报错见第 2 章）；`apply?` 用 `apply` 代替 `exact` 去找；`rw?` 找能改写目标的
等式。下面两个例子里 `apply?` 与 `rw?` 分别找到 `Nat.le_add_right_of_le` 与 `Nat.add_comm`；`rw?` 报告的
`-- no goals` 说明改写之后目标已被 `rfl` 关闭：
-/

/--
info: Try this:
  [apply] exact Nat.le_add_right_of_le h
-/
#guard_msgs in
example (a b c : ℕ) (h : a ≤ b) : a ≤ b + c := by apply?

/--
info: Try this:
  [apply] rw [Nat.add_comm]
  -- no goals
-/
#guard_msgs in
example (a b : ℕ) : a + b = b + a := by rw?

/-!
`simp?`（第 5 章已见）把 `simp` 实际用到的 simp lemma（simp 引理）写成 `simp only [...]`，这样证明更稳定（不再依赖 simp 集合日后的变化）：
-/

/--
info: Try this:
  [apply] simp only [add_zero, mul_one, Nat.add_left_cancel_iff]
-/
#guard_msgs in
example (a b : ℕ) : a + 0 + b * 1 = a + b := by simp?

/-!
不知道该用哪个策略时用 `hint`，要找引理时用 `exact?`。`hint` 按优先级依次试一批已登记的策略（`simp_all?`、`exact?`、
`grind`、`omega`、`gcongr`……，见 `Mathlib/Tactic/Common.lean` 与 `GCongr.lean` 里的 `register_hint`），遇到第一个
能关闭目标的就停下，再把成功的结果列出来，剩余目标少的排在前面；`🎉️` 表示这一条关闭了目标（`Mathlib/Tactic/Hint.lean`）。
`try?` 是核心库的同类。输出可能有多行，所以这里只钉住其中一行（`substring := true`）；`gcongr` 见第 10 章：
-/

/-- info: Try these: [apply] 🎉️ gcongr -/
#guard_msgs (whitespace := lax, substring := true) in
example (a b : ℕ) (h : a < b) : a ≤ b := by hint

/-- info: Try these: [apply] simp +arith -/
#guard_msgs (whitespace := lax, substring := true) in
example (a b : ℕ) : a + b = b + a := by try?

/-!
## 10. 站外搜索：Loogle、LeanSearch、文档站

下面的内容**不能**放进编译过的代码：`#loogle` 与 `#leansearch` 要联网，输出随服务器变化，所以这里只用文字讲清楚
（语法的原文在 `.lake/packages/LeanSearchClient/LeanSearchClient/` 下的 `LoogleSyntax.lean` 与 `Syntax.lean`）。

**Loogle**（<https://loogle.lean-lang.org>）按**形状**搜索。查询由若干过滤器组成，用逗号分隔，表示「且」：
- 常量名：`Real.sin`；名字子串（加引号）：`"differ"`；
- 子表达式模式，`_` 是通配符，`?a` 是 metavariable（元变量，同一个 `?a` 必须匹配同一个子项）：`_ * (_ ^ _)`、
  `Real.sqrt ?a * Real.sqrt ?a`；
- 结论模式，用 `⊢`（或 `|-`）开头，只看定理的**结论**（`→` 与 `∀` 右边的部分），假设按任意顺序匹配：
  `⊢ _ < _ → tsum _ < tsum _`；
- 组合：`Real.sin, "two", tsum, _ * _, _ ^ _, ⊢ _ < _ → _`。

在编辑器里可以写 `#loogle Nat.succ_le_succ`（命令、项、策略三种位置都行），结果以可点击的 `Try this` 给出；
`#loogle` 通过 `curl` 把查询发给外部服务器。**LeanSearch**（<https://leansearch.net>）按**自然语言**搜索：
`#leansearch "the sum of two even numbers is even."` ——查询字符串必须以 `.` 或 `?` 结尾，否则只给警告；
它同样把你的查询发给外部服务器。写在这类命令里的内容会离开你的机器，别放没公开的东西。

**文档站**（<https://leanprover-community.github.io/mathlib4_docs/>）是 Mathlib 的 API 文档：URL 与模块路径一一
对应（`Mathlib/Algebra/NeZero.lean` 对应 `…/Mathlib/Algebra/NeZero.html`），每条声明都带 `source` 链接，有 docstring
（文档注释）的会显示出来，页面顶部有搜索框。社区站点根上另有两页：overview 页
<https://leanprover-community.github.io/mathlib-overview.html> 与 undergrad 页
<https://leanprover-community.github.io/undergrad.html>，后者是「本科数学主题 → Mathlib 名字」的对照表，数据在本地的
`.lake/packages/mathlib/docs/undergrad.yaml`（前者对应 `overview.yaml`）。

**版本偏差。** 文档站、Loogle、LeanSearch 都跟随 Mathlib 的较新版本，而本书锁定在 `v4.35.0`。写作时（2026-10）
我们量过文档站与 Loogle：文档站比锁定版本多 51 个提交，Loogle 多 90 个；LeanSearch 的偏差没有量过。网上找到的名字可能
在锁定版本里已被改名或尚未存在：**把站外搜索当作线索，一律用本地 `#check` 或本地源码
（`.lake/packages/mathlib/Mathlib/`）确认**。

**求助。** 站内站外都没找到，就去问（第 1 章讲过 MWE 流程）。针对「找引理」再补三条：(1) 先在 Zulip 的
`Is there code for X?` 频道搜关键词，旧帖是最好的文档；(2) 给出陈述本身（`example … := by sorry`，用 `extract_goal`
取得，第 13 章），写明试过什么（`exact?` 的输出、猜过的名字）与 Lean/Mathlib 版本；(3) 不要把作业当问题发，也不要
用大模型代写帖子（社区的发帖约定，见第 23 章）。

## 11. 读一个真实的 Mathlib 源文件：`Algebra/NeZero.lean`

这个文件只有 64 行，却集中了本章的多数约定。在文档站上打开 `Mathlib/Algebra/NeZero.html`，或在本地打开
`.lake/packages/mathlib/Mathlib/Algebra/NeZero.lean`，从上往下读：

1. **文件头**：版权块、`module`、`public import Mathlib.Order.Defs.PartialOrder`（公开导入，下游文件也会看到它）、
   两行不带 `public` 的 `import`（只在证明里用到，不进入公开接口，第 28 章讲机制）。
2. **module docstring（模块文档注释）**：一句话说明文件主题；文档站上它就是页面的开头。
3. **`public section`**（没有 `@[expose]`，因为没有需要展开的 `def`），随后 `variable {R : Type*} [Zero R]`
   提供公共参数。`theorem not_neZero` 与 `lemma two_ne_zero` 混用两个关键字（Mathlib 里等价），`@[simp]`
   标出会被 `simp` 自动使用的引理。
4. **撇号 = 显式类型**：`one_ne_zero` 的类型参数 `α` 隐式，`one_ne_zero'` 在 `variable (α)` 之后声明，`α` 显式。
5. **文件末尾的 `namespace NeZero`**：构造类实例的引理 `NeZero.of_pos` 放在类名之下。

每一条都可以用 `#check` 核对：
-/

/-- info: one_ne_zero.{u_2} {α : Type u_2} [Zero α] [One α] [NeZero 1] : 1 ≠ 0 -/
#guard_msgs in #check one_ne_zero

/-- info: one_ne_zero'.{u_2} (α : Type u_2) [Zero α] [One α] [NeZero 1] : 1 ≠ 0 -/
#guard_msgs in #check one_ne_zero'

/-- info: not_neZero.{u_1} {R : Type u_1} [Zero R] {n : R} : ¬NeZero n ↔ n = 0 -/
#guard_msgs in #check not_neZero

/--
info: NeZero.of_pos.{u_2} {M : Type u_2} {x : M} [Preorder M] [Zero M] (h : 0 < x) : NeZero x
-/
#guard_msgs in #check NeZero.of_pos

example : (1 : ℝ) ≠ 0 := one_ne_zero
example : (1 : ℝ) ≠ 0 := one_ne_zero' ℝ
example : NeZero (1 : ℝ) := NeZero.of_pos zero_lt_one

/-!
回顾第 8 节的四步各自怎样失败：猜错名字是 `Unknown identifier`（第 15 节①）；`#check` 的陈述不符预期，回到名字规则；
`exact?` 报错，改用 `apply?`、`rw?` 或站外搜索；站外名字在本地找不到，多半是版本偏差。
-/

/-!
## 12. `to_additive` 孪生与 `grep` 的盲区

Mathlib 的 `@[to_additive]` 属性从一条乘法版本的声明**自动生成**加法版本，名字按规则翻译（`mul` → `add`，
`prod` → `sum`，`one` → `zero`，`inv` → `neg` 等）。生成的声明没有自己的 `theorem` 行，所以
`rg "theorem sum_comm"` 在 `Mathlib/Algebra/BigOperators` 下**一无所获**，而 `rg "theorem prod_comm"` 能找到
`Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:121`。两者在 Lean 里都存在：
-/

/--
info: Finset.sum_comm.{u_3, u_4, u_5} {α : Type u_3} {β : Type u_4} {γ : Type u_5} [AddCommMonoid
  β] {s : Finset γ}
  {t : Finset α} {f : γ → α → β} : ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y
-/
#guard_msgs (whitespace := lax) in #check Finset.sum_comm

/--
info: Finset.sum_le_sum.{u_1, u_5} {ι : Type u_1} {N : Type u_5} [AddCommMonoid N] [Preorder N] {f
  g : ι → N}
  {s : Finset ι} [AddLeftMono N] (h : ∀ i ∈ s, f i ≤ g i) : ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
-/
#guard_msgs (whitespace := lax) in #check Finset.sum_le_sum

/-!
用 Lean 自己的记录来验证孪生关系。`to_additive` 把「乘法名 → 加法名」存在一个环境扩展里，下面用元编程接口
（第 27 章）把它读出来。**这个代码块初读可以跳过**：`#eval` 在编译期运行 `CoreM` 程序，所以文件头多了两行
`public meta import`（模块系统，第 28 章），你只需看输出。翻译并不总是字面的：`abs_sub_comm` 的乘法原型是
`mabs_div_comm`，`sub_nonneg` 的原型是 `one_le_div'`，只靠 `grep` 无从猜起：
-/

open Lean Mathlib.Tactic in
/--
info: (some Finset.sum_comm)
(some Finset.sum_le_sum)
(some abs_sub_comm)
(some sub_nonneg)
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  for n in [``Finset.prod_comm, ``Finset.prod_le_prod, ``mabs_div_comm, ``one_le_div'] do
    IO.println s!"{(Translate.findTranslationName? env ToAdditive.data n).map (·.toString)}"

/-!
所以找名字应当用 `#check`、`exact?`、Loogle、文档站（它们看环境，不看文本）；用 `rg` 时先搜**乘法版本**
（`prod_comm`、`mul_comm`）。`@[to_additive]` 的使用见第 15 章，原理见第 27 章。

## 13. 弃用警告

Mathlib 每个月有数百条弃用与改名。改名时旧名不会立刻消失，而是变成带 `@[deprecated]` 属性的别名：用它得到一条
warning（警告），告诉你新名字；库的政策是弃用的声明在大约 **6 个月后可以被删除**。`Set.mem_setOf_eq` 是
2026-07-09 的改名（第 7 章的 `setOf` 变成 `ofPred`）：
-/

/-- warning: `Set.mem_setOf_eq` has been deprecated: Use `Set.mem_ofPred_eq` instead -/
#guard_msgs (substring := true) in
example (p : ℕ → Prop) (a : ℕ) : (a ∈ {x | p x}) = p a := Set.mem_setOf_eq

example (p : ℕ → Prop) (a : ℕ) : (a ∈ {x | p x}) = p a := Set.mem_ofPred_eq

/-!
警告的正文就是新名字。`since` 日期不出现在警告里，要从源码里读：
`@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq`
（`Mathlib/Data/Set/Operations.lean`）。也可以让 Lean 自己说（同样可以跳过代码，看输出）：
-/

open Lean in
/-- info: new name: (some Set.mem_ofPred_eq), since: (some 2026-07-09) -/
#guard_msgs in
#eval show CoreM Unit from do
  match Linter.deprecatedAttr.getParam? (← getEnv) ``Set.mem_setOf_eq with
  | some e => IO.println s!"new name: {e.newName?}, since: {e.since?}"
  | none => IO.println "not deprecated"

/-!
读法：(1) 新名字在 `Use … instead` 里；(2) `since` 距今接近 6 个月的名字很快会被删，立刻改；(3) 网上教程、LLM、
旧项目里的名字常已弃用甚至删除，遇到「Unknown identifier」先怀疑改名，再回到本章第 8 节的流程；(4) 整个**模块**
也会弃用：`Mathlib/Data/Real/Basic.lean` 现在只剩一行 `public import` 和
`deprecated_module (since := "2026-08-27")`，把你转到 `Mathlib.Basic.Real.Basic`；(5) 弃用警告由 linter（代码检查器）
`linter.deprecated` 产生，默认开启；本节的示例用 `#guard_msgs` 吸收它。

## 14. `#min_imports`：最窄的导入

Mathlib 要求每个文件只导入真正需要的模块；本书也是。`#min_imports in <命令>` 计算该命令需要的最少模块
（命令由 `Mathlib.Init` 提供，所有导入了 Mathlib 的文件都有）。它的输出可以直接贴进文件头
（本书的文件头用 `public import`，输出里已经带着 `public`）。例如第 2 章的 `mul_pos` 例子在 `ℝ` 上需要：
-/

/-- info: public import Mathlib.Basic.Real.Basic -/
#guard_msgs in
#min_imports in
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb

/-!
## 15. 常见错误

**① 用旧名字。** 教程与 LLM 常给出已改名的引理。`div_le_iff` 在锁定版本里已经不存在，新名字带 `₀`：
-/

/-- error: Unknown identifier `div_le_iff` -/
#guard_msgs in
example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := (div_le_iff hc).mpr h

example (a b c : ℝ) (hc : 0 < c) (h : a ≤ b * c) : a / c ≤ b := (div_le_iff₀ hc).mpr h

/-!
**② 方向与类型类。** 把 `mul_le_mul_left` 用在 `ℝ` 上：它要求 `MulRightMono ℝ`（乘法保序），`ℝ` 没有这个
instance（实例），错误信息指向的是类型类而不是你的参数顺序。读到 `MulRightMono`、`AddLeftMono` 这类名字，想一想
「这个结构上到底需要什么」，再换成 `mul_le_mul_of_nonneg_left`：
-/

/--
error: failed to synthesize instance of type class
  MulRightMono ℝ

Hint: Type class instance resolution failures can be inspected with the `set_option
  trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example (a b c : ℝ) (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := mul_le_mul_left h c

/-!
**③ `open Nat` 之后同名歧义。** `Nat.mul_le_mul_left` 与根命名空间的 `mul_le_mul_left` 参数顺序不同，打开
`Nat` 后两个都候选，Lean 报告 overloaded（重载）并列出两边的失败（这里只钉住第一条）：
-/

/--
error: overloaded, errors Type mismatch _root_.mul_le_mul_left h c has type a * c ≤ b * c but is
expected to have type c * a ≤ c * b
-/
#guard_msgs (whitespace := lax, substring := true) in
open Nat in
example (a b c : ℕ) (h : a ≤ b) : c * a ≤ c * b := mul_le_mul_left h c

/-!
## 练习

下列练习都是「找名字」：陈述已给出，证明是**一行**，里面是你找到的引理名。先猜名字、`#check` 核对，猜不出再用
`exact?`、Loogle。★ 直接应用，★★ 要读懂 `↔`、点记号或方向，★★★ 需要搜索（名字不好猜）。`ex_9_3`、`ex_9_4`、`ex_9_8`、
`ex_9_10`、`ex_9_11`、`ex_9_12`、`ex_9_14` 复习第 2、3、4、7、8 章。
-/

/-- 练习 9.1（★）：按 `nonneg` 的命名规则猜名字。 -/
theorem ex_9_1 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := sorry

/-- 练习 9.2（★）：平方非负；`x ^ 2` 在名字里怎么写，见第 2 节的词典。 -/
theorem ex_9_2 (x : ℝ) : 0 ≤ x ^ 2 := sorry

/-- 练习 9.3（★）：第 3 章的合取；点记号。 -/
theorem ex_9_3 (p q : Prop) (h : p ∧ q) : q ∧ p := sorry

/-- 练习 9.4（★★）：第 2 章的不等式；点记号，名字里有 `not` 与 `ge`。 -/
theorem ex_9_4 (a b : ℝ) (h : a < b) : ¬b ≤ a := sorry

/-- 练习 9.5（★★）：读成名字：`0 < x⁻¹` 是一个 `↔` 的一边，用 `.mpr`。 -/
theorem ex_9_5 (x : ℝ) (hx : 0 < x) : 0 < x⁻¹ := sorry

/-- 练习 9.6（★★）：`_left` 还是 `_right`？用 `#check` 看方向。 -/
theorem ex_9_6 (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := sorry

/-- 练习 9.7（★★★）：绝对值的三角不等式；加法名字由 `to_additive` 生成（第 12 节），先试 `exact?`。 -/
theorem ex_9_7 (a b : ℝ) : |a + b| ≤ |a| + |b| := sorry

/-- 练习 9.8（★★）：第 8 章的 cast（类型转换）；`cast`、`le`，用 `↔`。 -/
theorem ex_9_8 (a b : ℕ) (h : a ≤ b) : (a : ℝ) ≤ b := sorry

/-- 练习 9.9（★★★）：有限和非负；这个加法名字也由 `to_additive` 生成，`rg` 搜不到它的声明。 -/
theorem ex_9_9 (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) : 0 ≤ ∑ i ∈ s, f i := sorry

/-- 练习 9.10（★）：第 7 章的集合；`inter`、`subset`、`left`。 -/
theorem ex_9_10 (s t : Set ℕ) : s ∩ t ⊆ s := sorry

/-- 练习 9.11（★★）：第 8 章的 cast；`inj` 与 `injective` 哪一个是 `↔`？ -/
theorem ex_9_11 (a b : ℕ) (h : (a : ℝ) = b) : a = b := sorry

/-- 练习 9.12（★）：第 7 章的集合；旧名 `Set.eq_mem_setOf` 已弃用，用它的新名字（`setOf` 变成了 `ofPred`）。 -/
theorem ex_9_12 (p : ℕ → Prop) : p = (· ∈ {a | p a}) := sorry

/-- 练习 9.13（★★）：整除与乘法；用 `exact?` 找，再找一个点记号形式的写法。 -/
theorem ex_9_13 (a b c : ℕ) (h : a ∣ b) : a ∣ b * c := sorry

/-- 练习 9.14（★★）：乘积为零；先拆成析取，再用第 4 章的消去。 -/
theorem ex_9_14 (a b : ℝ) (h : a * b = 0) (ha : a ≠ 0) : b = 0 := sorry

/-- 练习 9.15（★★）：除法与不等式；`₀` 版本，注意假设顺序。 -/
theorem ex_9_15 (a b c : ℝ) (hc : 0 < c) (h : a * c ≤ b) : a ≤ b / c := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 大小写 | 证明 `snake_case`，类型 `UpperCamelCase`，数据 `lowerCamelCase` | 判断一个名字是定理、类型还是函数 |
| 结论优先 | `neg_mul_neg`、`sub_add_eq_add_sub` | 按结论里符号的书写顺序猜名字 |
| `_of_`、`_iff` | `lt_of_le_of_lt`、`Nat.succ_le_iff` | 假设按顺序列出；`↔` 用 `.mp`/`.mpr` |
| `pos`、`nonneg`、`₀` | `mul_pos`、`div_le_iff₀` | 与 `0` 比较；同一结论的带零结构版本 |
| 撇号、`_left`/`_right` | `pow_succ'`、`add_le_add_left` | 先 `#check` 方向，不凭直觉 |
| 函数名 | `cast_`、`map_`、`mem_`、`_apply`、`ext`、`inj` | 引理谈论的函数写进名字 |
| 点记号 | `h.le`、`h.trans_lt`、`h.resolve_left` | 类型的头部常量决定命名空间 |
| 找引理 | `#check`、`exact?`、`apply?`、`rw?`、`simp?`、`hint`、`try?` | 猜名字之后核对与兜底 |
| 站外搜索 | Loogle（形状）、`#leansearch`（自然语言）、文档站 | 线索；以本地 `#check` 为准 |
| `to_additive` | `prod_comm` ↔ `sum_comm` | `grep` 找不到加法名时搜乘法名 |
| 弃用 | `@[deprecated (since := …)]`，约 6 个月后删除 | 读警告里的新名字，立刻替换 |
| 导入 | `#min_imports in …` | 选最窄的导入 |

## 延伸阅读

- Mathlib 命名规范 <https://leanprover-community.github.io/contribute/naming.html>（符号词典与 `_of_`、`₀`、
  `ext`、`inj` 规则的原文）；风格指南 <https://leanprover-community.github.io/contribute/style.html> 的
  Deprecation 一节。
- 本地源码：`Mathlib/Algebra/NeZero.lean`（第 11 节通读的文件）；`Mathlib/Order/Defs/PartialOrder.lean`
  （`NeZero.lean` 公开导入的文件）；
  `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`（`add_le_add_left`、`add_pos` 的来源）；
  `Mathlib/Data/Set/Operations.lean`（弃用别名）；`Mathlib/Tactic/Translate/ToAdditive.lean`；
  `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean`（`prod_comm`）；`Mathlib/Tactic/Hint.lean`。
- 搜索工具：`.lake/packages/LeanSearchClient/LeanSearchClient/LoogleSyntax.lean`（Loogle 查询语法的文档注释）；
  核心库 `Init/Tactics.lean` 里 `exact?`、`apply?`、`rw?` 的文档注释；`.lake/packages/mathlib/docs/` 下的
  `undergrad.yaml`、`overview.yaml`。
- 本书第 10 章（自动化策略）、第 13 章（风格与代码检查器）、第 23 章（贡献 Mathlib：`deprecate`、
  `lake exe lint-style`、Zulip 礼仪）。
-/

end Lean4Learn.Ch09

end
