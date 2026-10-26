module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 12 章　有限和、计数与组合

随机图、概率方法与大偏差的下一步几乎都落在「数有限个东西」上：边的条数、三角形的个数、某个事件包含多少个
结果。本章整理 Mathlib 里处理有限对象的整套工具：finset（有限集）`Finset α` 与它的元素个数、big operator
（大算子）`∑`/`∏`、用 `Finset.induction_on` 做归纳、double counting（双重计数）、pigeonhole principle
（抽屉原理）、binomial coefficient（二项式系数）与 `Finset.powersetCard`，以及四种 cardinality（基数）
`Finset.card`、`Fintype.card`、`Nat.card`、`Set.ncard` 之间的换算。读完后你能把一个手写的计数论证翻译成
Mathlib 的引理调用，并知道小情形何时可以交给 `decide`。

## 学习目标
- 区分 `Finset α` 与 `Set α`，会写 `{a, b}`、`Finset.range`、`Finset.univ`，会用 filter（过滤）`{x ∈ s | p x}`、
  image（像）`Finset.image`，会用 `#s`（需要 `open scoped Finset`）。
- 会读写 `∑ i ∈ s, f i` 的各种形态，知道函数体的优先级，会用 `Finset.sum_range_succ`、`Fin.sum_univ_succ`、
  `Finset.sum_add_distrib`、`Finset.mul_sum`、`Finset.sum_comm`、`Finset.sum_congr`。
- 会用 `Finset.card_eq_sum_ones`、`Finset.card_filter`、`Finset.sum_boole` 在「个数」与「求和」之间转换。
- 会用 `induction s using Finset.induction_on with | empty | insert a s ha ih` 证明关于任意有限集的命题，
  知道什么时候要先写 `classical`。
- 会用 `Finset.card_eq_sum_card_fiberwise` 与 `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`
  做双重计数；会用三个抽屉原理的引理，并处理 `Set.MapsTo` 形式的假设。
- 会用 `Nat.choose`、`Finset.powersetCard`、`Nat.sum_range_choose`、`add_pow` 证明组合恒等式。
- 会用 `decide`、`simp [Finset.sum_range_succ]`、`decide +kernel` 验证小情形，知道它们的边界。
- 会在 `Finset.card`、`Fintype.card`、`Nat.card`、`Set.ncard` 之间选择并换算；会处理「谓词不可判定」。

## 前置知识
第 5 章（`decide`、`simp`、`rw`）；第 6 章（`induction … with`、`Decidable`）；第 7 章（`Set`、单射、像）；
第 8 章（`DecidableEq`、`classical`、coercion（强制转换）`↑`）；第 9 章（找引理的方法）；第 10 章（`omega`、`nlinarith`）；
第 11 章 §8（`Finset.sum_le_sum`）。
-/

@[expose] public section

namespace Lean4Learn.Ch12

/-!
## 1. `Finset α`：有限集

`Finset α` 是「元素类型为 `α` 的有限集合」的数据类型（底层是去掉重复的多重集）。它与第 7 章的 `Set α`
不同：`Set α` 是谓词 `α → Prop`，可以无限，没有「元素个数」；`Finset α` 一定有限，有 `Finset.card`。
字面量 `{a, b, c}` 是 `insert a (insert b {c})`，`insert` 要判断元素是否已在集合里，所以需要 `DecidableEq α`
（`ℕ`、`Fin n` 都有）。成员关系 `∈` 也可判定，所以小例子可以直接交给 `decide`（第 5 章）：
-/

example : (3 : ℕ) ∈ ({1, 2, 3} : Finset ℕ) := by decide
example : ({1, 2, 3, 2} : Finset ℕ) = {3, 1, 2} := by decide   -- 去重，且与顺序无关

/-!
带变量的成员关系用 `Finset.mem_insert` 与 `Finset.mem_singleton` 展开。`Finset.range n` 是 `{0, …, n - 1}`；
`Finset.univ` 是「整个类型」，要求 fintype（有限类型）`Fintype α`，即类型自带元素的枚举（`Fin n`、`Bool`、
`Fin n → Bool` 都有）：
-/

example (a b c : ℕ) : a ∈ ({b, c} : Finset ℕ) ↔ a = b ∨ a = c := by
  rw [Finset.mem_insert, Finset.mem_singleton]
example (m n : ℕ) : m ∈ Finset.range n ↔ m < n := Finset.mem_range
example : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide

/-!
**元素个数与记号 `#s`。** `s.card` 是 `Finset.card s`。Mathlib 为它定义了限定作用域（scoped）的记号 `#s`：
scoped 记号只在 `open scoped Finset`（或 `open Finset`）之后才生效，此后直到文件结束都有效；这与只管紧跟的
一条命令的 `open … in`（第 8 章 §12 的 `open Classical in`）不同。不打开时 `#s` 不是合法的项（这是解析阶段的
语法错误，`#guard_msgs` 捕获不到，不演示）。打开之后，`#` 的优先级使 `#s + 1` 读作 `(#s) + 1`：
-/

open scoped Finset

example (s : Finset ℕ) : #s = s.card ∧ #s + 1 = s.card + 1 := ⟨rfl, rfl⟩
example (n : ℕ) : #(Finset.range n) = n := Finset.card_range n
example (s t : Finset ℕ) (h : s ⊆ t) : #s ≤ #t := Finset.card_le_card h

/-!
**`Finset` 与 `Set` 的关系。** 每个 `s : Finset α` 可以强制转换成集合 `(s : Set α)`（写作 `↑s`），两边的成员关系
由 `Finset.mem_coe` 对接。把一个 `Finset` 当 `Set` 用之后，就要用 `Set.ncard` 之类的 `Set` 版本来数个数（§10）：
-/

example (s : Finset ℕ) (a : ℕ) : a ∈ (s : Set ℕ) ↔ a ∈ s := Finset.mem_coe

/-!
## 2. 过滤、像与集合运算

**过滤（filter）。** `{x ∈ s | p x}` 是 `s.filter p`，需要谓词可判定 `DecidablePred p`（§11）。这里的过滤
是 `Finset` 的运算，与第 14 章的 filter（滤子）`Filter` 无关。成员关系由 `Finset.mem_filter` 给出：
-/

example (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (a : ℕ) :
    a ∈ {x ∈ s | p x} ↔ a ∈ s ∧ p a := Finset.mem_filter
example (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] : {x ∈ s | p x} = s.filter p := rfl
example : {x ∈ Finset.range 10 | x % 3 = 0} = {0, 3, 6, 9} := by decide

/-!
**像（image）。** `s.image f` 是 `{f a | a ∈ s}`，需要 `β` 上有 `DecidableEq`（去重）。`f` 是 injective（单射）时个数不变，
这里的 `Function.Injective` 来自第 7 章：
-/

example (s : Finset ℕ) (f : ℕ → ℕ) (b : ℕ) : b ∈ s.image f ↔ ∃ a ∈ s, f a = b :=
  Finset.mem_image
example : (Finset.range 5).image (fun x ↦ x * x) = {0, 1, 4, 9, 16} := by decide
example (s : Finset ℕ) : #(s.image (fun x ↦ 2 * x)) = #s :=
  Finset.card_image_of_injective s (fun a b h ↦ by simpa using h)

/-!
**并、交、乘积与个数。** inclusion–exclusion principle（容斥原理）的最简形式 `Finset.card_union_add_card_inter`，以及它的推论
`Finset.card_union_le`；笛卡儿积的个数是乘积（`Finset.card_product`）：
-/

example (s t : Finset ℕ) : #(s ∪ t) + #(s ∩ t) = #s + #t := Finset.card_union_add_card_inter s t
example (s t : Finset ℕ) : #(s ∪ t) ≤ #s + #t := Finset.card_union_le s t
example (s t : Finset ℕ) : #(s ×ˢ t) = #s * #t := Finset.card_product s t

/-!
## 3. 大算子 `∑` 与 `∏`

`∑ i ∈ s, f i` 是 `Finset.sum s f`，`∏` 同理；它们在这个版本里是全局记号，不需要 `open BigOperators`。
旧写法 `∑ i in s, f i` 已不合法（解析错误，同样不演示）。
常用形态：`∑ i ∈ s, f i`；`∑ i, f i`（对整个有限类型，即 `Finset.univ`）；`∑ i ∈ s with p i, f i`
（先过滤）：
-/

example (f : Fin 3 → ℕ) : ∑ i, f i = ∑ i ∈ Finset.univ, f i := rfl
example (s : Finset ℕ) (f : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ∑ i ∈ s with p i, f i = ∑ i ∈ s.filter p, f i := rfl

/-!
**函数体的优先级是 67**，比 `+`（65）高：`∑ i ∈ s, f i + 1` 读作 `(∑ i ∈ s, f i) + 1`。要把 `+ 1` 放进
函数体必须加括号。这是最常见的静默错误，因为两种写法都能通过编译：
-/

example : ∑ i ∈ Finset.range 3, i + 1 = 4 := by decide      -- (0 + 1 + 2) + 1
example : ∑ i ∈ Finset.range 3, (i + 1) = 6 := by decide    -- 1 + 2 + 3

/-!
**递推。** `Finset.sum_range_succ` 把 `range (n + 1)` 上的和拆成 `range n` 的和加最后
一项；配合第 6 章的归纳，就是证明「公式对一切 `n` 成立」的标准做法。例：高斯求和。注意 `rw` 之后目标里
只剩 `ih` 里已有的和，剩下是线性算术：
-/

example (f : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), f i = ∑ i ∈ Finset.range n, f i + f n :=
  Finset.sum_range_succ f n

theorem gauss_sum (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    -- ⊢ 2 * (∑ i ∈ Finset.range (n + 1), i + (n + 1)) = (n + 1) * (n + 1 + 1)
    linarith

/-!
Mathlib 里已有现成的版本，注意它用的是 `ℕ` 的截断减法（第 2 章）：
-/

example (n : ℕ) : (∑ i ∈ Finset.range n, i) * 2 = n * (n - 1) := Finset.sum_range_id_mul_two n
example (n : ℕ) : ∏ i ∈ Finset.range n, (i + 1) = n.factorial :=
  Finset.prod_range_add_one_eq_factorial n

/-!
**`Fin n` 上的和。** `Fin.sum_univ_succ` 把 `Fin (n + 1)` 上的和拆成第 `0` 项加其余（其余用 `Fin.succ` 取下标）；
小的固定 `n` 有 `Fin.sum_univ_three` 一类：
-/

example (n : ℕ) (f : Fin (n + 1) → ℕ) : ∑ i, f i = f 0 + ∑ i : Fin n, f i.succ :=
  Fin.sum_univ_succ f
example (f : Fin 3 → ℕ) : ∑ i, f i = f 0 + f 1 + f 2 := Fin.sum_univ_three f

/-!
**线性性与交换求和。** 常数求和是 `Finset.sum_const`（得到 `#s • c`，其中 `•` 是 `ℕ` 的数乘，用
`smul_eq_mul` 变成乘法）；`Finset.sum_add_distrib` 拆和；`Finset.mul_sum` 提出常数（注意最后一个显式参数是
那个常数）；`Finset.sum_comm` 交换两层求和的次序；`Finset.sum_congr` 在**绑定变量底下**替换函数体，这是
`rw` 做不到的（第 5 章已演示），要把 `s₁ = s₂` 写成 `rfl`：
-/

example (s : Finset ℕ) (c : ℕ) : ∑ _i ∈ s, c = #s * c := by
  rw [Finset.sum_const, smul_eq_mul]
example (s : Finset ℕ) (f g : ℕ → ℕ) :
    ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i := Finset.sum_add_distrib
example (s : Finset ℕ) (f : ℕ → ℕ) (a : ℕ) : a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i :=
  Finset.mul_sum s f a
example (s t : Finset ℕ) (f : ℕ → ℕ → ℕ) :
    ∑ i ∈ s, ∑ j ∈ t, f i j = ∑ j ∈ t, ∑ i ∈ s, f i j := Finset.sum_comm
example (s : Finset ℕ) (f g : ℕ → ℕ) (h : ∀ i ∈ s, f i = g i) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := Finset.sum_congr rfl h

/-!
逐项比较推出和的比较见第 11 章 §8（`Finset.sum_le_sum`，假设的形状同样是 `∀ i ∈ s, …`）。

## 4. 用求和计数

「数个数」与「求和」之间有三座桥。`Finset.card_eq_sum_ones`：个数是 `1` 的和；`Finset.card_filter`：满足
`p` 的个数是 indicator function（指示函数）`if p i then 1 else 0` 的和；`Finset.sum_boole` 是同一件事在任意带
`1` 的加法交换幺半群 `R`（`AddCommMonoidWithOne`，如 `ℝ`）中的版本（右边多了一个强制转换，这正是它在实数里
更好用的原因）：
-/

example (s : Finset ℕ) : #s = ∑ _i ∈ s, 1 := Finset.card_eq_sum_ones s
example (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    #{i ∈ s | p i} = ∑ i ∈ s, if p i then 1 else 0 := Finset.card_filter p s
example (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ i ∈ s, if p i then (1 : ℝ) else 0) = (#{i ∈ s | p i} : ℝ) := Finset.sum_boole p s

/-!
一个完整的用法：先用 `Finset.sum_boole` 把实数和变成个数，再用 `decide` 数出个数，最后 `norm_num` 处理
`ℕ → ℝ` 的强制转换（第 8 章）：
-/

example : (∑ i ∈ Finset.range 10, if i % 2 = 0 then (1 : ℝ) else 0) = 5 := by
  rw [Finset.sum_boole, show #{i ∈ Finset.range 10 | i % 2 = 0} = 5 by decide]
  norm_num

/-!
## 5. `Finset` 上的归纳

要对「任意有限集」证明命题，用归纳原理 `Finset.induction_on`：空集成立；若对 `s` 成立且 `a ∉ s`，则对
`insert a s` 成立。写全名 `Finset.induction_on`，有两个分支，**分支名是 `empty` 与 `insert`**，
`insert` 分支带四个名字 `a s ha ih`。本书统一的写法是
`induction s using Finset.induction_on with | empty => … | insert a s ha ih => …`。下面证明
一个 Bernoulli 型的
下界 `1 + ∑ i ≤ ∏ (1 + i)`（自然数版本）。`Finset.sum_insert` 与 `Finset.prod_insert` 都要假设 `a ∉ s`，
这正是归纳分支给出的 `ha`：
-/

theorem one_add_sum_le_prod (s : Finset ℕ) : 1 + ∑ i ∈ s, i ≤ ∏ i ∈ s, (1 + i) := by
  induction s using Finset.induction_on with
  | empty => simp   -- ⊢ 1 + ∑ i ∈ ∅, i ≤ ∏ i ∈ ∅, (1 + i)
  | insert a s ha ih =>
    -- ha : a ∉ s,  ih : 1 + ∑ i ∈ s, i ≤ ∏ i ∈ s, (1 + i)
    -- ⊢ 1 + ∑ i ∈ insert a s, i ≤ ∏ i ∈ insert a s, (1 + i)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [Nat.zero_le (∑ i ∈ s, i), Nat.zero_le a]

/-!
**`[DecidableEq α]` 是前提。** `Finset.induction_on` 的 `insert a s` 要求 `α` 上能判定相等。`α = ℕ` 时自动
满足；`α` 是一般类型时，先写 `classical`（第 8 章），否则目标里会多出一个 `case inst`，见「常见错误」。
下面的 `sum_const_two` 就是任意类型 `α` 上的例子，所以第一行是 `classical`（`Finset.card_insert_of_notMem`
是 `a ∉ s` 时 `insert` 的个数引理；旧资料里的 `card_insert_of_not_mem` 在这个版本里已不存在）：
-/

theorem sum_const_two {α : Type*} (s : Finset α) : ∑ _a ∈ s, 2 = 2 * #s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, Finset.card_insert_of_notMem ha]
    ring

/-!
不想要这个假设时可以用 `Finset.cons_induction`，它的第二个分支用 `Finset.cons`（带 `a ∉ s` 证据的插入），
对应的求和引理是 `Finset.sum_cons`。下面的例子对任意类型 `α` 的有限集，没有 `classical`：
-/

example {α : Type*} (s : Finset α) (f : α → ℕ) : ∑ i ∈ s, 2 * f i = 2 * ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih]; ring

/-!
## 6. 双重计数

双重计数（double counting）就是用两种方式数同一个量。Mathlib 里有两个基本工具。

**按纤维分拆。** 把 `s` 按 `f` 的取值分成若干块，每一块 `{x ∈ s | f x = y}` 叫 fiber（纤维），个数是各块
个数之和。假设写成 `Set.MapsTo f ↑s ↑t`，即
「`s` 的像落在 `t` 里」；`Set.MapsTo` 展开是 `∀ ⦃x⦄, x ∈ ↑s → f x ∈ ↑t`，所以可以直接写 `fun n _ ↦ …`，
证明目标里的 `∈ ↑t` 用 `Finset.mem_coe` 换回 `∈ t`。`(f := e)` 是按名字给隐式参数 `f` 赋值，用在推断不出 `f`
的地方。例：`{0, …, 11}` 按模 3 分成三块，每块四个：
-/

theorem range_twelve_mod_three :
    #(Finset.range 12) = ∑ r ∈ Finset.range 3, #{n ∈ Finset.range 12 | n % 3 = r} :=
  Finset.card_eq_sum_card_fiberwise (f := fun n ↦ n % 3)
    (fun n _ ↦ Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ (by norm_num))))

example (r : ℕ) (hr : r < 3) : #{n ∈ Finset.range 12 | n % 3 = r} = 4 := by
  have h3 : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  rcases h3 with rfl | rfl | rfl <;> decide

/-!
**关系的两种数法。** 对关系 `r : α → β → Prop` 与 `s : Finset α`、`t : Finset β`，先对每个 `a ∈ s` 数有多少个
`b ∈ t` 满足 `r a b`，再对 `a` 求和；与先对每个 `b ∈ t` 数有多少个 `a ∈ s` 满足 `r a b`、再对 `b` 求和，
结果相同。这就是 `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`（`bipartiteAbove` 与
`bipartiteBelow` 只是 `{b ∈ t | r a b}` 与 `{a ∈ s | r a b}` 的名字，默认透明度下可展开，所以直接写项即可）：
-/

example (s t : Finset ℕ) :
    ∑ a ∈ s, #{b ∈ t | a ∣ b} = ∑ b ∈ t, #{a ∈ s | a ∣ b} :=
  Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun a b ↦ a ∣ b)

/-!
特别地取 `s = t = {1, …, N}`、`r = (· ∣ ·)`：左边是「每个 `a` 有多少个倍数」之和，右边是「每个 `b` 有多少个
约数」之和。`a` 的倍数个数是 `N / a`，所以两边都等于 `∑ a, N / a`。下面只对 `N = 10` 做数值核对
（不是上面引理的应用）：约数个数之和等于 `∑ a, 10 / a`，且都是 `27`：
-/

example : ∑ b ∈ Finset.Icc 1 10, #{a ∈ Finset.Icc 1 10 | a ∣ b}
    = ∑ a ∈ Finset.Icc 1 10, 10 / a := by decide
example : ∑ a ∈ Finset.Icc 1 10, 10 / a = 27 := by decide

/-!
## 7. 抽屉原理

pigeonhole principle（抽屉原理）在 Mathlib 里有三种形态，按「物品装在哪」选：

- `Fintype.exists_ne_map_eq_of_card_lt`：整个类型到整个类型，`f : α → β`，`Fintype.card β < Fintype.card α`，
  结论 `∃ x y, x ≠ y ∧ f x = f y`；
- `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`：`s` 到 `t`，假设 `#t < #s` 与 `Set.MapsTo f ↑s ↑t`；
- `Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to`：推广版，`#t * n < #s` 推出某个纤维的个数 `> n`；
  这里的映射假设是 `∀ a ∈ s, f a ∈ t`，与上一条的 `Set.MapsTo` 写法不同，抄用法时要看清楚。

第一种：13 个人里有两个人同月生日。
-/

example (birth : Fin 13 → Fin 12) : ∃ i j, i ≠ j ∧ birth i = birth j :=
  Fintype.exists_ne_map_eq_of_card_lt birth (by simp)

/-!
第三种：把 7 个物品放进 3 个抽屉，必有一个抽屉里至少有 3 个（`3 * 2 < 7`）。`obtain ⟨y, -, hy⟩` 里的
`-` 丢掉 `y ∈ t` 这条已无用的信息：
-/

example (f : Fin 7 → Fin 3) : ∃ y : Fin 3, 2 < #{x ∈ (Finset.univ : Finset (Fin 7)) | f x = y} := by
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (f := f) (n := 2) (fun a _ ↦ Finset.mem_univ _)
    (by simp)
  exact ⟨y, hy⟩

/-!
**经典应用。** 从 `{1, …, 2n}` 里任取 `n + 1` 个数，其中必有两个相邻。抽屉是 `{1, …, n}`，映射是
`x ↦ (x + 1) / 2`（`2k - 1` 与 `2k` 进同一个抽屉）。证明的三步：验证 `Set.MapsTo`（`show` 把
`∈ ↑(Finset.Icc 1 n)` 换成 `∈ Finset.Icc 1 n`，两者定义相等）、验证个数（`Nat.card_Icc`）、套用引理后用
`omega` 收尾。引理给出的 `heq` 里 `f` 是未化简的 `fun`，先 `have` 成化简后的形式：
-/

theorem exists_consecutive (n : ℕ) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 (2 * n)) (hc : n < #s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ (x = y + 1 ∨ y = x + 1) := by
  have hmaps : Set.MapsTo (fun x ↦ (x + 1) / 2) ↑s ↑(Finset.Icc 1 n) := by
    intro x hx
    -- hx : x ∈ ↑s
    have hx' := Finset.mem_Icc.1 (hs hx)   -- hx' : 1 ≤ x ∧ x ≤ 2 * n
    show (x + 1) / 2 ∈ Finset.Icc 1 n
    rw [Finset.mem_Icc]
    omega
  have hcard : #(Finset.Icc 1 n) < #s := by
    rw [Nat.card_Icc]
    omega
  obtain ⟨x, hx, y, hy, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  -- heq : (fun x ↦ (x + 1) / 2) x = (fun x ↦ (x + 1) / 2) y
  have heq' : (x + 1) / 2 = (y + 1) / 2 := heq
  exact ⟨x, hx, y, hy, hne, by omega⟩

/-!
## 8. 二项式系数与 `Finset.powersetCard`

`Nat.choose n k`（写作 `n.choose k`）是二项式系数，递归定义，所以小情形可以直接 `decide`。它满足帕斯卡
恒等式 `Nat.choose_succ_succ'`，以及 `Nat.choose_two_right`
（`n.choose 2` 是 `n * (n - 1) / 2`，图上最多有多少条边）：
-/

example : Nat.choose 5 2 = 10 := by decide
example (n k : ℕ) : (n + 1).choose (k + 1) = n.choose k + n.choose (k + 1) :=
  Nat.choose_succ_succ' n k
example (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n

/-!
**组合意义。** `s.powersetCard k` 是 `s` 的全部 `k` 元子集构成的 `Finset (Finset α)`；
`Finset.mem_powersetCard` 说「`t` 属于它当且仅当 `t ⊆ s` 且 `#t = k`」，
`Finset.card_powersetCard` 说它的个数是 `(#s).choose k`。全体子集构成 power set（幂集），个数是
`Finset.card_powerset`：
-/

example (s t : Finset ℕ) (k : ℕ) : t ∈ s.powersetCard k ↔ t ⊆ s ∧ #t = k :=
  Finset.mem_powersetCard
example (s : Finset ℕ) (k : ℕ) : #(s.powersetCard k) = (#s).choose k :=
  Finset.card_powersetCard k s
example : #((Finset.range 6).powersetCard 3) = 20 := by decide
example (s : Finset ℕ) : #s.powerset = 2 ^ #s := Finset.card_powerset s

/-!
**二项式定理。** `add_pow x y n` 在任意交换半环里展开 `(x + y) ^ n`，系数是 `n.choose m`（以强制转换的
形式出现）。取 `x = y = 1` 就得到 Pascal 三角形一行之和 `Nat.sum_range_choose`，Mathlib 自己就是这样证明
它的：
-/

example (x y n : ℕ) :
    (x + y) ^ n = ∑ m ∈ Finset.range (n + 1), x ^ m * y ^ (n - m) * n.choose m := add_pow x y n
example (n : ℕ) : ∑ m ∈ Finset.range (n + 1), n.choose m = 2 ^ n := Nat.sum_range_choose n
example (n : ℕ) : ∑ m ∈ Finset.range (n + 1), n.choose m = 2 ^ n := by
  simpa [one_add_one_eq_two] using (add_pow (1 : ℕ) 1 n).symm

/-!
## 9. 小情形：`decide` 与 `simp`

固定的小数据不必推导，直接计算。三种办法各有边界：

- `decide`：把 `Decidable` 实例规约成 `true`（第 6 章）。`Finset.range`、`Fin n` 上的有界量词和求和都能算。
  但它在 elaborator（精译器；另译繁饰器）里规约，递归深度有限；
- `decide +kernel`：交给内核规约，不受 `maxRecDepth` 限制（但仍受时间和栈限制），数据再大一点也行
  （第 5 章 §3，规模边界见第 10 章 §4）；
- `simp [Finset.sum_range_succ]` 或 `norm_num [Finset.sum_range_succ]`：把 `range` 上的和逐项展开成数字相加，
  适合项数不多但 `decide` 不能用的场合（例如项里有实数，第 5 章 §3）。
-/

example : ∑ i ∈ Finset.range 10, i ^ 2 = 285 := by decide
example : ∑ i ∈ Finset.range 10, i ^ 2 = 285 := by simp [Finset.sum_range_succ]
example : ∑ i ∈ Finset.range 4, ((i : ℝ) + 1) = 10 := by
  norm_num [Finset.sum_range_succ]
example : ∀ a ∈ Finset.range 10, a ^ 2 % 4 ≤ 1 := by decide
example : #{x ∈ Finset.range 30 | x % 7 = 0} = 5 := by decide
example : ∑ i ∈ Finset.range 2000, i = 1999000 := by decide +kernel

/-!
## 10. 四种基数

「集合有多大」（cardinality，基数，即元素个数）在 Mathlib 里有四个入口，输入对象不同：

| 写法 | 输入 | 需要 | 无限时 | 何时用 |
|---|---|---|---|---|
| `#s`（`Finset.card`） | `s : Finset α` | 无 | 不会发生 | 手里有具体的 `Finset`，引理最全 |
| `Fintype.card α` | 类型 `α` | `[Fintype α]` | 不适用 | 整个类型有限，如 `Fin n`、`Bool` |
| `Nat.card α` | 类型 `α` | 无 | `0` | 不想携带 `Fintype` 实例 |
| `s.ncard` | `s : Set α` | 无 | `0` | 对象是 `Set`，可能无限 |

对无限对象，`Nat.card` 与 `Set.ncard` 返回 junk value（垃圾值）`0`，不会报错，因此使用前要另外证明有限。
换算引理：`Finset.card_univ`（`rfl`）、`Fintype.card_fin`、`Nat.card_eq_fintype_card`、
`Set.ncard_coe_finset`、`Nat.card_coe_set_eq`、`Nat.card_eq_finsetCard`、`Fintype.card_coe`：
-/

example (n : ℕ) : #(Finset.univ : Finset (Fin n)) = Fintype.card (Fin n) := Finset.card_univ
example (n : ℕ) : Fintype.card (Fin n) = n := Fintype.card_fin n
example (α : Type) [Fintype α] : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
example (s : Finset ℕ) : (s : Set ℕ).ncard = #s := Set.ncard_coe_finset s
example (s : Set ℕ) : Nat.card s = s.ncard := Nat.card_coe_set_eq s
example (s : Finset ℕ) : Nat.card s = #s := Nat.card_eq_finsetCard s
example (s : Finset ℕ) : Fintype.card s = #s := Fintype.card_coe s

/-!
无限情形的垃圾值（`Nat.card_eq_zero_of_infinite`、`Set.Infinite.ncard`）：
-/

example : Nat.card ℕ = 0 := Nat.card_eq_zero_of_infinite
example : (Set.univ : Set ℕ).ncard = 0 := Set.infinite_univ.ncard

/-!
**`Finite` 与 `Fintype`。** `Finite α` 是命题（`α` 与某个 `Fin n` 之间存在等价对应），`Fintype α` 是数据
（一份具体的枚举）。从 `Finite α` 造 `Fintype α` 要选取枚举，所以 `Fintype.ofFinite` 是 `def` 而不是
实例；需要 `Finset` 版本的引理时，先 `have := Fintype.ofFinite α`。许多 `Nat.card` 引理只要 `Finite α`，不需要这一步（下面第一个例子）：
-/

example (α : Type) [Finite α] [Nonempty α] : 0 < Nat.card α := Nat.card_pos

example (α : Type) : Prop × Type := (Finite α, Fintype α)
example (α : Type) [Finite α] : ∃ s : Finset α, ∀ a, a ∈ s := by
  have := Fintype.ofFinite α
  exact ⟨Finset.univ, Finset.mem_univ⟩

/-!
## 11. 可判定性与 `classical`

`Finset.filter p s` 需要 `DecidablePred p`。`ℕ`、`Fin n` 上的算术谓词自带；`ℝ` 上的 `<`、`≤` 也有
（由经典逻辑给出的不可计算实例，所以能写 `Finset.filter`，但 `decide` 卡在实例里无法规约，见第 5 章 §3、
第 8 章 §13）；而像 `x ∈ S`（`S : Set ℕ`）这样的谓词没有。下面用到 `Finset.card_filter_le`（过滤只会变小）。
三种处理方式：

1. 把 `[DecidablePred …]` 写成假设，调用者提供；
2. 对一次性的定义用 `open scoped Classical in` 加 `noncomputable`，让经典逻辑提供实例（第 8 章）；
3. 在证明里写 `classical`。它只对当前策略块有效，**救不了定理的陈述**：陈述里的实例必须在陈述处就找得到。
-/

example (s : Finset ℝ) : #{x ∈ s | x < 1} ≤ #s := Finset.card_filter_le _ _

example (S : Set ℕ) [DecidablePred (· ∈ S)] (s : Finset ℕ) : #{x ∈ s | x ∈ S} ≤ #s :=
  Finset.card_filter_le s _

open scoped Classical in
noncomputable def meet (S : Set ℕ) (s : Finset ℕ) : Finset ℕ := {x ∈ s | x ∈ S}

theorem card_meet_le (S : Set ℕ) (s : Finset ℕ) : #(meet S s) ≤ #s := by
  classical
  unfold meet
  exact Finset.card_filter_le _ _

/-!
## 12. 常见错误

**1. 用了旧名。** `Finset.card_le_of_subset` 是旧资料里的名字，在这个版本里已经不存在（连弃用别名也没有）；
现在叫 `Finset.card_le_card`。遇到「Unknown constant」先用第 9 章的方法查名字。另外，§3 的优先级陷阱不报错，
所以不在本节：
-/

/-- error: Unknown constant `Finset.card_le_of_subset` -/
#guard_msgs in
example (s t : Finset ℕ) (h : s ⊆ t) : #s ≤ #t := Finset.card_le_of_subset h

/-!
**2. 一般类型上归纳却没有 `classical`。** `Finset.induction_on` 要 `DecidableEq α`。`α` 是任意类型时它不会
自动出现，目标里多出一个 `case inst`，写 `classical` 即可（对比 §5 的 `sum_const_two`）：
-/

/--
error: unsolved goals
case inst
α : Type u_1
s : Finset α
⊢ DecidableEq α
-/
#guard_msgs in
example {α : Type*} (s : Finset α) : #s = #s := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rfl

/-!
**3. 过滤一个不可判定的谓词。** `x ∈ S` 对 `S : Set ℕ` 没有 `Decidable` 实例，`Finset.filter` 找不到
`DecidablePred`。按 §11 选一种办法：
-/

/--
error: failed to synthesize instance of type class
  DecidablePred fun x ↦ x ∈ S

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (S : Set ℕ) (s : Finset ℕ) : Finset ℕ := s.filter (· ∈ S)

/-!
**4. `classical` 救不了陈述。** 把 `classical` 写在证明里，定理的陈述仍然在没有它的环境里被 elaborator 处理，
同样报找不到实例（只截取开头一句）：
-/

/-- error: failed to synthesize instance of type class DecidablePred fun x ↦ x ∈ S -/
#guard_msgs (whitespace := lax, substring := true) in
example (S : Set ℕ) (s : Finset ℕ) : #{x ∈ s | x ∈ S} ≤ #s := by
  classical
  exact Finset.card_filter_le _ _

/-!
**5. `decide` 遇到大数据。** `decide` 在 elaborator 里规约，数据一大就超出递归深度；换成 `decide +kernel`
（§9 末尾有成功的例子）或者先化简：
-/

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ∑ i ∈ Finset.range 2000, i = 1999000 := by decide

/-!
**6. 对 `Set` 用 `Finset` 的方法。** `Set` 没有 `card`；要么先有 `Finset`，要么用 `Set.ncard`（§10）：
-/

/--
error: Invalid field `card`: The environment does not contain `Function.card`, so it is not possible to project the field `card` from an expression
  s
of type `ℕ → Prop`
-/
#guard_msgs in
example (s : Set ℕ) : ℕ := s.card

/-!
## 练习

练习大致按小节顺序排列。12.1、12.2 是第 6 章的归纳，12.3 回到第 7 章的单射，12.5 回到第 11 章的
`Finset.sum_le_sum` 与第 8 章的强制转换，12.6 有第 8 章的 `ℤ` 强制转换，12.15 用第 4 章的 `by_cases`。
引理名在本章出现，或由题面的提示给出。
-/

/-- 练习 12.1（★）：前 `n` 个奇数之和是 `n ^ 2`。对 `n` 归纳，用 `Finset.sum_range_succ`（§3）。 -/
theorem ex_12_1 (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by sorry

/-- 练习 12.2（★★）：阶乘的乘积表示。对 `n` 归纳，用 `Finset.prod_range_succ` 与 `Nat.factorial_succ`。
不许直接用 `Finset.prod_range_add_one_eq_factorial`（§3）。 -/
theorem ex_12_2 (n : ℕ) : ∏ i ∈ Finset.range n, (i + 1) = n.factorial := by sorry

/-- 练习 12.3（★★）：像的个数（§2）。先证 `fun x ↦ 3 * x` 单射（第 7 章；`simpa using h` 或 `omega`），
再用 `Finset.card_image_of_injective` 与 `Finset.card_range`。 -/
theorem ex_12_3 (n : ℕ) : #((Finset.range n).image (fun x ↦ 3 * x)) = n := by sorry

/-- 练习 12.4（★★）：容斥原理的减法形式。用 `Finset.card_union_add_card_inter`（§2）加 `omega`；
`ℕ` 的减法是截断的（第 2 章），`omega` 能处理。 -/
theorem ex_12_4 (s t : Finset ℕ) : #(s ∪ t) = #s + #t - #(s ∩ t) := by sorry

/-- 练习 12.5（★★）：调和和不超过项数。用 `Finset.sum_le_sum`（第 11 章 §8）逐项比较成常数 `1`，
再用 `Finset.sum_const`（§3）；每项 `1 / (i + 1) ≤ 1` 用 `div_le_one₀` 与 `positivity`。 -/
theorem ex_12_5 (n : ℕ) : ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) ≤ n := by sorry

/-- 练习 12.6（★★）：整数上的裂项求和。注意函数体要加括号（§3）。对 `n` 归纳，归纳步里
`rw [Finset.sum_range_succ, ih]`，再 `push_cast` 与 `ring`。 -/
theorem ex_12_6 (n : ℕ) :
    ∑ i ∈ Finset.range n, (((i : ℤ) + 1) ^ 2 - (i : ℤ) ^ 2) = (n : ℤ) ^ 2 := by sorry

/-- 练习 12.7（★★）：用 `Finset.induction_on`（§5）证明积与和的关系：
`∏ i ∈ s, 2 ^ f i = 2 ^ ∑ i ∈ s, f i`。注意 `α` 是任意类型，要先 `classical`（§5、§11）。
归纳步用 `Finset.prod_insert`、`Finset.sum_insert` 与 `pow_add`；不许直接用 `Finset.prod_pow_eq_pow_sum`。 -/
theorem ex_12_7 {α : Type*} (s : Finset α) (f : α → ℕ) :
    ∏ i ∈ s, 2 ^ f i = 2 ^ ∑ i ∈ s, f i := by sorry

/-- 练习 12.8（★）：对严格小于关系做双重计数（§6）：
`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow`，关系取 `fun a b ↦ a < b`。 -/
theorem ex_12_8 (s : Finset ℕ) :
    ∑ a ∈ s, #{b ∈ s | a < b} = ∑ b ∈ s, #{a ∈ s | a < b} := by sorry

/-- 练习 12.9（★★）：抽屉原理（§7）。五个自然数里有两个模 `4` 同余。把 `i` 映到
`(⟨f i % 4, _⟩ : Fin 4)`，用 `Fintype.exists_ne_map_eq_of_card_lt`；`Nat.mod_lt` 给出 `f i % 4 < 4`。 -/
theorem ex_12_9 (f : Fin 5 → ℕ) : ∃ i j, i ≠ j ∧ f i % 4 = f j % 4 := by sorry

/-- 练习 12.10（★★）：`{0, …, 9}` 的任意 `6` 元子集里有两个数之和为 `9`。抽屉是 `Finset.range 5`，
映射是 `fun x ↦ min x (9 - x)`（`{k, 9 - k}` 进同一个抽屉）。仿 §7 的 `exists_consecutive`：
先验证 `Set.MapsTo`（`omega` 认得 `min`），再 `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`。 -/
theorem ex_12_10 (s : Finset ℕ) (hs : s ⊆ Finset.range 10) (hc : 5 < #s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ x + y = 9 := by sorry

/-- 练习 12.11（★）：帕斯卡恒等式的一个特例（§8）。`Nat.choose_succ_succ' n 1` 给出
`(n + 1).choose 2 = n.choose 1 + n.choose 2`（`1 + 1` 与 `2` 定义相等，可以用类型标注写成后者），
再用 `Nat.choose_one_right` 与 `omega`。 -/
theorem ex_12_11 (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by sorry

/-- 练习 12.12（★★）：`∑ 2 ^ m * C(n, m) = 3 ^ n`。取 `x = 2`、`y = 1` 套 `add_pow`（§8），
再用 `simp` 化简 `1 ^ (n - m)` 与强制转换。 -/
theorem ex_12_12 (n : ℕ) : ∑ m ∈ Finset.range (n + 1), 2 ^ m * n.choose m = 3 ^ n := by sorry

/-- 练习 12.13（★）：五元集有十个三元子集。`Finset.card_powersetCard`（§8），再 `decide`。 -/
theorem ex_12_13 {α : Type*} (s : Finset α) (h : #s = 5) : #(s.powersetCard 3) = 10 := by sorry

/-- 练习 12.14（★★）：`Set.Iio n` 的 `Set.ncard`（§10）。把 `Set.Iio n` 改写成 `↑(Finset.range n)`
（`Finset.coe_range`），再用 `Set.ncard_coe_finset` 与 `Finset.card_range`。 -/
theorem ex_12_14 (n : ℕ) : (Set.Iio n).ncard = n := by sorry

/-- 练习 12.15（★★★）：指示函数之和等于总数。思路：把两个和并成一个，证明每一项都是 `1`，再数项数。
每项需要对 `p i` 分情形（`by_cases`，第 4 章）；会用到 `Finset.sum_add_distrib`、`Finset.sum_congr`
（§3）与常数求和。 -/
theorem ex_12_15 (p : ℕ → Prop) [DecidablePred p] (s : Finset ℕ) :
    (∑ i ∈ s, if p i then (1 : ℝ) else 0) + ∑ i ∈ s, (if p i then (0 : ℝ) else 1) = #s := by
  sorry

/-!
## 小结

| 概念 | 写法 | 何时用 |
|---|---|---|
| 有限集 | `Finset α`、`{a, b}`、`Finset.range n`、`Finset.univ` | 手里是具体的有限对象；`univ` 要 `Fintype` |
| 个数 | `#s`（`open scoped Finset`）、`s.card` | `Finset` 的元素个数 |
| 集合运算与 `Set` | `Finset.card_union_add_card_inter`、`card_union_le`、`card_product`、`↑s`、`Finset.mem_coe` | 并 / 交 / 积的个数；`Finset` ⇄ `Set` |
| 过滤 / 像 | `{x ∈ s \| p x}`、`s.image f`、`Finset.mem_filter`、`Finset.mem_image` | 谓词要可判定；`image` 要 `DecidableEq` |
| 求和 / 求积 | `∑ i ∈ s, f i`、`∏`、`∑ i, f i`、`∑ i ∈ s with p i, f i` | 函数体优先级 67，含 `+` 要加括号 |
| 递推与拆分 | `Finset.sum_range_succ`、`Fin.sum_univ_succ`、`Finset.sum_insert` | 对 `n` 或 `Finset` 归纳 |
| 变形 | `Finset.sum_add_distrib`、`Finset.mul_sum`、`Finset.sum_comm`、`Finset.sum_congr` | `sum_congr` 在绑定变量底下替换 |
| 个数与和 | `Finset.card_eq_sum_ones`、`Finset.card_filter`、`Finset.sum_boole` | 数个数 ⇄ 指示函数求和 |
| 有限集归纳 | `induction s using Finset.induction_on with \| empty \| insert a s ha ih`、`Finset.cons_induction` | `induction_on` 在一般类型上要先 `classical`；`cons_induction` 不要 |
| 双重计数 | `Finset.card_eq_sum_card_fiberwise`、`Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` | 两种方式数同一个量 |
| 抽屉原理 | `Fintype.exists_ne_map_eq_of_card_lt`、`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`、`Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` | 注意 `Set.MapsTo` 与 `∀ a ∈ s` 两种假设 |
| 组合数 | `Nat.choose`、`Finset.powersetCard`、`Finset.card_powersetCard`、`Nat.sum_range_choose`、`add_pow` | `k` 元子集、二项式定理 |
| 小情形 | `decide`、`decide +kernel`、`simp [Finset.sum_range_succ]` | 数据小；大了换 `+kernel` |
| 四种基数 | `Finset.card`、`Fintype.card`、`Nat.card`、`Set.ncard` | `Nat.card`/`ncard` 对无限对象给 `0` |
| 不可判定谓词 | `[DecidablePred p]`、`open scoped Classical in`、`classical` | `classical` 救不了陈述 |
-/

/-!
## 延伸阅读

- Mathlib 源码，Finset：`Mathlib/Data/Finset/Card.lean`（`card_le_card`、`card_image_of_injective`、
  `exists_ne_map_eq_of_card_lt_of_maps_to`、`card_nbij`）、`Mathlib/Data/Finset/Filter.lean`
  （`{x ∈ s | p x}` 的语法与显示）、`Mathlib/Data/Finset/Powerset.lean`（`powersetCard`）。
- 大算子：`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`（`∑`/`∏` 的语法与文档注释）、
  `.../Group/Finset/Basic.lean`（`prod_range_succ`、`prod_const`、`card_eq_sum_card_fiberwise`）、
  `Mathlib/Algebra/BigOperators/Ring/Finset.lean`（`sum_boole`、`mul_sum`）、`.../BigOperators/Fin.lean`。
- 组合：`Mathlib/Combinatorics/Pigeonhole.lean`、`Mathlib/Combinatorics/Enumerative/DoubleCounting.lean`、
  `Mathlib/Data/Nat/Choose/Sum.lean`（`add_pow`、`sum_range_choose`）、`Mathlib/Data/Fintype/Pigeonhole.lean`。
- 基数：`Mathlib/Data/Set/Card.lean`（`Set.ncard`）、`Mathlib/SetTheory/Cardinal/Finite.lean`（`Nat.card`）、
  `Mathlib/Data/Fintype/Card.lean`。
- 本书：第 6 章（`Decidable`、归纳）、第 11 章 §8（有限和的比较）、第 18 章（图论里的 `edgeFinset` 与握手引理，
  是本章双重计数的直接应用）、第 19 章（`Finset.expect`、有限概率空间）。
-/

end Lean4Learn.Ch12

end
