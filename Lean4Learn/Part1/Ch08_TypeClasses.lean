module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 8 章　类型类与代数结构（使用者视角）

前七章里你一直在用 `a + b`、`mul_comm`、`(n : ℝ)`，却没问过它们为什么对 `ℕ`、`ℤ`、`ℝ` 同时成立。答案是
type class（类型类）：「`G` 是群」「`R` 是交换环」这类数学陈述在 Lean 里是一个个类，定理的方括号
`[Group G]` 要求调用者出示证据，证据由 Lean 自动查找。本章从使用者一侧讲清这套机制，再讲与它绑在一起的
两件事：coercion（强制转换）`↑`（以及 `norm_cast` 一族策略），和 `Decidable`、`classical`、`noncomputable`
（即为什么 `ℝ` 上的判断不能用 `decide` 算）。设计者一侧（自己声明类、`extends`、实例优先级）留到第 15 章。

## 学习目标
- 读懂 `[Group G]`、`[Field K] [LinearOrder K] [IsStrictOrderedRing K]`，用 `#synth` 查看、用
  `inferInstance` 取用 instance synthesis（实例合成）的结果，知道 Mathlib 里没有 `LinearOrderedField`；
- 认识 `Monoid`、`Group`、`CommRing`、`Field`、`LinearOrder`、lattice（格）的 hierarchy（层次结构），写一条
  对 `[CommRing R]` 成立的引理，选对够用的最弱的类；
- 为自己的结构体定义 `Mul`、`One` 实例，再证三条公理得到 `Monoid` 实例；
- 读懂强制转换 `↑`，会用 `Nat.cast_*`、`push_cast`、`norm_cast`、`exact_mod_cast` 处理 `ℕ → ℤ → ℝ`；
- 说清 `^` 的规则：指数不会被自动转换，`x ^ (1 / 2)` 里的 `1 / 2` 是 `ℕ`；
- 区分 decidable（可判定）的各种来源、`classical` 策略与 `open Classical`，说明 noncomputable（不可计算）
  与 `ℝ` 上 `decide` 失败的原因。

## 前置知识
第 2 章的 `ring`、`linarith`、`positivity` 与 `↑` 初识；第 3 章的隐式参数；第 5 章 `decide` 的边界；
第 6 章的 `structure` 与 `Decidable`。第 7 章的 `↥` 在 §8 只提一次。
-/

@[expose] public section

namespace Lean4Learn.Ch08

/-!
## 1. `[Group G]` 是什么意思

读 Mathlib 定理的第一步是读方括号。`mul_inv_cancel` 的类型：
-/

/-- info: @mul_inv_cancel : ∀ {G : Type u_1} [inst : Group G] (a : G), a * a⁻¹ = 1 -/
#guard_msgs in #check @mul_inv_cancel

/-!
三种括号各管一件事（前两种见第 3 章）：`{G : Type u_1}` 隐式，由 `a` 的类型推出；`(a : G)` 显式；
`[inst : Group G]` 是 instance-implicit argument（实例隐式参数）：调用者不写它，Lean 在每次使用处做
instance synthesis（实例合成），找一个 `Group G` 的 instance（实例）填进去，找不到就报错。整条定理读作：
对任意类型 `G`，只要它带有群结构，对任意 `a : G` 有 `a * a⁻¹ = 1`。

下面包一层自己的定理，用到两个类型上。`ℝˣ` 是 `ℝ` 的可逆元素构成的群（`Units`），`add_neg_cancel`
是同一条定理的加法版本（`AddGroup`）。Mathlib 的乘法类都有加法孪生（`Monoid` 对 `AddMonoid`，`CommGroup`
对 `AddCommGroup`），由 `@[to_additive]` 一次生成两套（第 15 章）。`inferInstance` 在 §2 解释：
-/

theorem my_mul_inv {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := mul_inv_cancel a

example (u : ℝˣ) : u * u⁻¹ = 1 := my_mul_inv u
example (u : ℝˣ) : u * u⁻¹ = 1 := @my_mul_inv ℝˣ inferInstance u   -- 手动给出实例，效果相同
example (x : ℝ) : x + -x = 0 := add_neg_cancel x

/-!
`ℝ` 对乘法不是群，因为 `0` 没有逆。套用群的定理，实例合成失败，报错就是 `failed to synthesize` 加上缺的类。
带零群（`GroupWithZero`，域是其特例）的版本 `mul_inv_cancel₀` 多要一个 `x ≠ 0`：
-/

/-- error: failed to synthesize instance of type class
  Group ℝ -/
#guard_msgs (substring := true) in
example (x : ℝ) : x * x⁻¹ = 1 := mul_inv_cancel x

example (x : ℝ) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ hx

/-!
这个名字怎么找到？第 2 章的 `exact?`（命名规律第 9 章系统讲：后缀 `₀` 表示「需要 `≠ 0` 前提」）：
-/

/--
info: Try this:
  [apply] exact CommGroupWithZero.mul_inv_cancel x hx
-/
#guard_msgs in
example (x : ℝ) (hx : x ≠ 0) : x * x⁻¹ = 1 := by exact?

/-!
报告的是更具体的 `CommGroupWithZero.mul_inv_cancel`，日常写法是上面的 `mul_inv_cancel₀ hx`（第 2 章
`Right.mul_pos` 与 `mul_pos` 同理）。
-/

/-!
## 2. 实例是数据加证明

类和结构体一样是若干 field（字段）的打包，实例就是这些字段的一组取值。`Semigroup G` 的构造子说明了它的
组成：一个乘法 `Mul G`（数据），加上结合律（证明）。

> 撞词提示：这里的「字段」是结构体的成员，代数里的「域」`Field` 是另一回事；§1 的「群结构」是数学里的
> structure，与 Lean 的结构体 `structure` 也无关（第 6 章）。
-/

/-- info: @Semigroup.mk : {G : Type u_1} → [toMul : Mul G] →
  (∀ (a b c : G), a * b * c = a * (b * c)) → Semigroup G -/
#guard_msgs (whitespace := lax) in #check @Semigroup.mk

/-!
`#synth C` 打印实例合成为 `C` 找到的实例名。Mathlib 里的实例大多显式命名（如 `Nat.instMonoid`）；
自己写的 `instance` 不给名字时，Lean 按类和类型自动取名（§7 的 `instMonoidAff`）：
-/

/-- info: Nat.instMonoid -/
#guard_msgs in #synth Monoid ℕ
/-- info: Int.instCommRing -/
#guard_msgs in #synth CommRing ℤ
/-- info: Rat.instField -/
#guard_msgs in #synth Field ℚ
/-- info: Real.instField -/
#guard_msgs in #synth Field ℝ

/-!
`inferInstance` 是项模式的写法：「请 Lean 合成出期望类型的实例」。它也展示类之间的继承：每个 `extends`
的父类对应一个投影，投影本身是实例，所以子类的实例自动是父类的实例：
-/

example : Monoid ℕ := inferInstance
example (G : Type*) [Group G] : Monoid G := inferInstance
example (K : Type*) [Field K] : CommRing K := inferInstance

/-!
（`Group → Monoid` 在 Mathlib 里要经过中间的 `DivInvMonoid`，这一步 Lean 替你走。）

## 3. Mathlib 的层次结构

Mathlib 的代数类按「逐步加公理」排成一个 hierarchy（层次结构），每个父类是一个 `extends`：
`Semigroup → Monoid → Group`（乘法一侧），`Semiring → Ring → CommRing`，`Ring → DivisionRing`，而 `Field`
同时继承 `CommRing` 与 `DivisionRing`。monoid（幺半群）、group（群）、ring（环）、commutative ring
（交换环）、field（域）主要多了什么：

| 类 | 在父类之上主要新增 | 例子 |
|---|---|---|
| `Semigroup` | 结合律 `mul_assoc` | `ℕ` 的乘法 |
| `Monoid` | `1`、`one_mul`、`mul_one`、幂 `^` | 矩阵乘法、函数复合 |
| `Group` | 逆 `⁻¹`、`inv_mul_cancel` | `ℝˣ`、置换群 |
| `Semiring` | 加法交换幺半群、乘法幺半群、分配律、`0 * a = 0` | `ℕ` |
| `Ring` | 加法逆（一元 `-` 与减法） | `ℤ`、矩阵环 |
| `CommRing` | 乘法交换 | `ℤ`、`ℝ` |
| `DivisionRing` | 非零元素有逆（`⁻¹`、`/`；`mul_inv_cancel`、`inv_zero`） | `ℚ`、`ℝ` |
| `Field` | 无新公理，只是 `CommRing` 加 `DivisionRing` | `ℚ`、`ℝ` |

一个类的实例自动是所有祖先的实例，所以一条用最弱的类写的引理对所有后代都可用。`mul_one` 只要
`MulOneClass`（`Monoid` 的祖先），在 `Monoid`、`Group`、`Ring`、`Field` 里都能用；`mul_comm` 只要
`CommMagma`（有乘法和交换律），只在乘法交换的类里能用（`CommMonoid`、`CommGroup`、`CommRing`、`Field`），
一般的 `Group` 不行：
-/

/-- info: @mul_one : ∀ {M : Type u_1} [inst : MulOneClass M] (a : M), a * 1 = a -/
#guard_msgs in #check @mul_one
/-- info: @mul_comm : ∀ {G : Type u_1} [inst : CommMagma G] (a b : G), a * b = b * a -/
#guard_msgs in #check @mul_comm

example (M : Type*) [Monoid M] (a : M) : a * 1 = a := mul_one a
example (G : Type*) [Group G] (a : G) : a * 1 = a := mul_one a
example (R : Type*) [Ring R] (a b c : R) : a * (b - c) = a * b - a * c := mul_sub a b c
example (R : Type*) [CommRing R] (a b : R) : a * b = b * a := mul_comm a b
-- junk value（垃圾值，第 2 章）约定写在 `DivisionRing` 的公理里
example (K : Type*) [Field K] : (0 : K)⁻¹ = 0 := inv_zero

/-- error: failed to synthesize instance of type class
  CommMagma G -/
#guard_msgs (substring := true) in
example (G : Type*) [Group G] (a b : G) : a * b = b * a := mul_comm a b

/-!
## 4. `ℕ ℤ ℚ ℝ` 的实例从哪来

`ℕ` 是 commutative semiring（交换半环），`ℤ` 是交换环，`ℚ` 与 `ℝ` 是域。`ℕ` 没有加法逆，向它要
`CommRing` 会失败（§14 第 1 条）。实例分散在 Mathlib 各处，用 `#synth` 打印的名字去源码里找：
`Nat.instCommSemiring` 在 `Mathlib/Algebra/Ring/Nat.lean`，`Int.instCommRing` 在
`Mathlib/Algebra/Ring/Int/Defs.lean`，`Rat.instField` 在 `Mathlib/Algebra/Field/Rat.lean`；`ℝ` 的代数与序
实例集中在 `Mathlib/Basic/Real/Basic.lean`：
-/

/-- info: Nat.instCommSemiring -/
#guard_msgs in #synth CommSemiring ℕ
/-- info: Real.commRing -/
#guard_msgs in #synth CommRing ℝ

/-!
## 5. 序与 mixin

ordered field（有序域）在 Mathlib 里不是一个类。数据（序 `≤`）与性质（`≤` 与 `+`、`*` 相容）分开声明，
三个实例隐式参数并列：`[Field K] [LinearOrder K] [IsStrictOrderedRing K]`。`LinearOrder K` 是 linear order
（全序），携带数据（`≤`、`<`、`min`、`max` 与它们的可判定性）；`IsStrictOrderedRing K` 是只含性质的类
（类型是 `Prop`，这种类称 mixin（只含性质的类）），说加法保序、乘以正数严格保序，外加 `0 ≤ 1` 与非平凡。
同一个 `K` 上的 `≤` 只有一份，mixin 只是附上性质。

旧教程里的 `LinearOrderedField` 在锁定版本中已不存在，要写成上面三个假设：
-/

/-- info: IsStrictOrderedRing.{u_1} (R : Type u_1) [Semiring R] [PartialOrder R] : Prop -/
#guard_msgs in #check IsStrictOrderedRing

/-- error: Unknown identifier `LinearOrderedField` -/
#guard_msgs (substring := true) in
example (K : Type*) [LinearOrderedField K] : True := trivial

/-- info: Real.instIsStrictOrderedRing -/
#guard_msgs in #synth IsStrictOrderedRing ℝ

example (K : Type*) [LinearOrder K] : DecidableLE K := inferInstance   -- 可判定性来自 `LinearOrder`

/-!
另一个常遇到的类是 `Lattice`（格）：有 `a ⊔ b`（supremum（上确界））与 `a ⊓ b`（infimum（下确界））。每个
全序都是格。`⊔` 只是 `max` 的记号（`Mathlib/Order/Notation.lean`），在全序上两者是同一个项，所以 `rfl`
成立，这只演示记号，不证明格的性质。格的引理对所有 `Lattice` 实例有效：
-/

/-- info: Real.lattice -/
#guard_msgs in #synth Lattice ℝ

example (a b : ℝ) : a ⊔ b = max a b := rfl
example {α : Type*} [LinearOrder α] : Lattice α := inferInstance
example {α : Type*} [Lattice α] (a b : α) : a ⊓ b ≤ a ⊔ b := inf_le_left.trans le_sup_left

/-!
## 6. 写泛型引理

把定理写在最弱的类上，就一次证明了所有实例。名字加前缀 `gen_`，避免与 Mathlib 的同名定理混淆：
-/

theorem gen_diff_sq {R : Type*} [CommRing R] (a b : R) :
    (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (x y : ℝ) : (x + y) * (x - y) = x ^ 2 - y ^ 2 := gen_diff_sq x y
example : ((3 : ℤ) + 2) * (3 - 2) = 3 ^ 2 - 2 ^ 2 := gen_diff_sq 3 2

theorem gen_add_sq {R : Type*} [CommSemiring R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := gen_add_sq x y
example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := gen_add_sq x y

/-!
`gen_diff_sq` 不能用在 `ℕ` 上（`ℕ` 不是 `CommRing`，§14）；`gen_add_sq` 的类弱一档，`ℕ`、`ℤ`、`ℝ` 都行
（见下）。**经验：证明用到哪些运算，就只要那个类。** 有序域上的例子：`2 ≤ a + a⁻¹`。先用 `field_simp`
（清分母，第 10 章详讲，这里当黑箱）与 `ring` 证 `a + a⁻¹ - 2 = (a - 1) ^ 2 / a`，再用 `positivity` 得右边
非负，最后 `linarith`：
-/

theorem gen_inv_add {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (a : K)
    (ha : 0 < a) : 2 ≤ a + a⁻¹ := by
  have h : a + a⁻¹ - 2 = (a - 1) ^ 2 / a := by
    field_simp
    ring
  have h2 : 0 ≤ (a - 1) ^ 2 / a := by positivity
  linarith

example (x : ℝ) (hx : 0 < x) : 2 ≤ x + x⁻¹ := gen_inv_add x hx

/-!
## 7. 为自己的类型定义实例

结构体 `Aff` 表示直线上的仿射映射 `x ↦ a * x + b`。复合 `f ∘ g` 是 `x ↦ f.a * (g.a * x + g.b) + f.b`，系数
为 `(f.a * g.a, f.a * g.b + f.b)`。把复合当作乘法，恒等映射 `(1, 0)` 当作 `1`。动机：给出 `*`、`1`
再证三条公理，Mathlib 里所有 `Monoid` 引理就对 `Aff` 可用。先用两个 `instance` 给出运算（数据）：
-/

@[ext] structure Aff where
  a : ℤ
  b : ℤ
  deriving Repr, DecidableEq

instance : Mul Aff where
  mul f g := ⟨f.a * g.a, f.a * g.b + f.b⟩

instance : One Aff where
  one := ⟨1, 0⟩

theorem Aff.mul_def (f g : Aff) : f * g = ⟨f.a * g.a, f.a * g.b + f.b⟩ := rfl
theorem Aff.one_def : (1 : Aff) = ⟨1, 0⟩ := rfl

/-!
再给出公理（证明）。`Monoid` 要三条：结合律、`1 * f = f`、`f * 1 = f`。`Mul` 与 `One` 两个字段不必重写，
`instance : Monoid Aff` 构造时到上下文里找已有的实例；`^` 对应的 `npow` 字段有默认值。三条证明都以 `ext`
开头（`Aff` 带 `@[ext]`，第 6 章），把结构体等式拆成 `a`、`b` 两个整数等式；`simp [Aff.mul_def]` 展开乘法。
结合律展开后剩两个整数环恒等式，要 `ring` 收尾（`trace_state` 看到的就是 `ring` 的两个目标），两条单位律
`simp` 就关闭了：
-/

/--
trace: case a
f g h : Aff
⊢ f.a * g.a * h.a = f.a * (g.a * h.a)

case b
f g h : Aff
⊢ f.a * g.a * h.b + (f.a * g.b + f.b) = f.a * (g.a * h.b + g.b) + f.b
-/
#guard_msgs in
example (f g h : Aff) : f * g * h = f * (g * h) := by
  ext <;> simp [Aff.mul_def]
  trace_state
  all_goals ring

/-!
合起来就是 `Monoid` 实例：
-/

instance : Monoid Aff where
  mul_assoc f g h := by
    ext <;> simp [Aff.mul_def] <;> ring
  one_mul f := by
    ext <;> simp [Aff.mul_def, Aff.one_def]
  mul_one f := by
    ext <;> simp [Aff.mul_def, Aff.one_def]

/-- info: instMonoidAff -/
#guard_msgs in #synth Monoid Aff

/-!
有了实例，Mathlib 里所有关于 `Monoid` 的引理立刻适用于 `Aff`（`pow_two`、`pow_add` 等）。
`Monoid` 里的乘法就是我们的 `Mul`（`rfl`）。`Aff` 派生了 `DecidableEq`，所以 `^` 的值与反例都能 `decide`
（`Aff` 不交换）：
-/

example (f g : Aff) : f * g = ⟨f.a * g.a, f.a * g.b + f.b⟩ := rfl
example (f : Aff) : f ^ 2 = f * f := pow_two f
example (f : Aff) (m n : ℕ) : f ^ (m + n) = f ^ m * f ^ n := pow_add f m n
example : (⟨2, 1⟩ : Aff) ^ 3 = ⟨8, 7⟩ := by decide
example : (⟨1, 1⟩ : Aff) * ⟨2, 0⟩ ≠ ⟨2, 0⟩ * ⟨1, 1⟩ := by decide

/-!
## 8. 强制转换 `↑`

`n : ℕ` 出现在需要 `ℝ` 的位置时，elaborator（精译器；另译繁饰器）插入 coercion（强制转换）：函数 `Nat.cast`，
由类 `NatCast ℝ` 提供，infoview（信息视图）显示成 `↑n`。关掉 `pp.coercions` 能看到真名：
-/

/-- info: fun n ↦ ↑n : ℕ → ℝ -/
#guard_msgs in #check fun n : ℕ ↦ (n : ℝ)

set_option pp.coercions false in
/-- info: fun n ↦ n.cast : ℕ → ℝ -/
#guard_msgs in #check fun n : ℕ ↦ (n : ℝ)

/-!
`ℕ → ℤ → ℚ → ℝ` 可以连续转换，每步一个 `↑`；中间的 `ℤ` 能省掉（`Int.cast_natCast`）：
-/

/-- info: fun n ↦ ↑↑↑n : ℕ → ℝ -/
#guard_msgs in #check fun n : ℕ ↦ (((n : ℤ) : ℚ) : ℝ)

example (n : ℕ) : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n

/-!
**转换插在叶子上。** 精译器处理 `+ * -` 这类二元运算时，先把整棵运算树的叶子统一到目标类型，再对每片叶子
转换。所以 `(a + b : ℝ)` 是 `↑a + ↑b`，而 `((a + b : ℕ) : ℝ)` 是先在 `ℕ` 里加、再整体转换 `↑(a + b)`。两者
在 `ℝ` 里相等，但不是同一个项：
-/

/-- info: fun a b ↦ ↑a + ↑b : ℕ → ℕ → ℝ -/
#guard_msgs in #check fun (a b : ℕ) ↦ (a + b : ℝ)
/-- info: fun a b ↦ ↑(a + b) : ℕ → ℕ → ℝ -/
#guard_msgs in #check fun (a b : ℕ) ↦ ((a + b : ℕ) : ℝ)
/-- info: fun n x ↦ x * ↑n : ℕ → ℝ → ℝ -/
#guard_msgs in #check fun (n : ℕ) (x : ℝ) ↦ x * n

/-!
`Nat.cast` 的基本引理绝大多数带 `@[simp, norm_cast]`，下一节的策略靠它们工作。`Nat.cast_sub` 要前提
`m ≤ n`，因为 `ℕ` 是 truncated subtraction（截断减法，第 2 章），`ℝ` 的减法不截断：
-/

/-- info: @Nat.cast_add : ∀ {R : Type u_1} [inst : AddMonoidWithOne R] (m n : ℕ),
  ↑(m + n) = ↑m + ↑n -/
#guard_msgs (whitespace := lax) in #check @Nat.cast_add
/-- info: @Nat.cast_sub : ∀ {R : Type u_1} [inst : AddGroupWithOne R] {m n : ℕ},
  m ≤ n → ↑(n - m) = ↑n - ↑m -/
#guard_msgs (whitespace := lax) in #check @Nat.cast_sub

example (a b : ℕ) : ((a * b : ℕ) : ℝ) = a * b := Nat.cast_mul a b
example (a b : ℕ) (h : a < b) : (a : ℝ) < b := Nat.cast_lt.2 h
example (a b : ℕ) (h : (a : ℝ) ≤ b) : a ≤ b := Nat.cast_le.1 h

/-!
另外两个箭头与它同源，本章不展开：`⇑f` 把打包的映射当函数用（第 15 章），`↥s` 把集合当类型用（第 7 章）。

## 9. `push_cast`、`norm_cast`、`exact_mod_cast`

三个策略读取同一批 `@[norm_cast]` 引理，方向不同：`push_cast` 把 `↑` 推向叶子（`↑(m + n)` 变 `↑m + ↑n`），
`norm_cast` 把 `↑` 拉到外面再消去（`↑m < ↑n` 变 `m < n`），`exact_mod_cast h` 把 `h` 与目标都 `norm_cast`
之后再 `exact`。纪律：**已知事实留在 `ℕ` 里，需要时再转换。**

1. `ℕ` 的不等式搬到 `ℝ` 用 `exact_mod_cast`，反方向也行，或者对假设 `norm_cast at`；带数字的等式同理
   （数字字面量两侧的转换由策略自己处理）：
-/

example (a b : ℕ) (h : a < b) : (a : ℝ) < b := by exact_mod_cast h
example (a b : ℕ) (h : (a : ℝ) < b) : a < b := by norm_cast at h
example (a b : ℕ) (h : (a : ℝ) + b = 10) : a + b = 10 := by exact_mod_cast h

/-!
2. `push_cast` 把转换推到叶子，再交给 `ring`；`trace_state` 看到推完之后的目标：
-/

/--
trace: n : ℕ
⊢ (↑n + 1) ^ 2 = ↑n ^ 2 + 2 * ↑n + 1
-/
#guard_msgs in
example (n : ℕ) : (((n + 1) ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 + 2 * n + 1 := by
  push_cast
  trace_state
  ring

example (n : ℕ) : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by norm_cast

/-!
3. `ℕ` 的减法：`push_cast` 单独不动它（`Nat.cast_sub` 有前提 `b ≤ a`，§14）。把前提传进去
   （`push_cast [h]`），或 `rw [Nat.cast_sub h]`；`ℤ` 上 `omega` 也行（第 2 章）：
-/

example (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) = a - b := Nat.cast_sub h
example (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) = a - b := by push_cast [h]; rfl
example (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℤ) = a - b := by omega

/-!
4. 正性与非负性：`Nat.cast_pos`、`Nat.cast_nonneg`；`positivity` 认识 `Nat.cast`（`↑n` 非负，所以
   `↑n + 1` 为正）：
-/

example (n : ℕ) (hn : 0 < n) : (1 : ℝ) ≤ n := by exact_mod_cast hn
example (n : ℕ) (hn : 0 < n) : (0 : ℝ) < n := Nat.cast_pos.2 hn
example (n : ℕ) : (0 : ℝ) < n + 1 := by positivity

/-!
## 10. `^` 的规则：指数不转换

`x ^ n` 的指数不参与「叶子统一」。精译器把 `^` 当作右作用（核心库里的 `rightact%` 规则）：只有底数 `x` 随整棵运算树统一类型，指数单独精译。
结果是：数字指数是 `ℕ`，变量指数保持自己的类型，永不自动转换。`x : ℝ` 时 `x ^ 2` 的 `2` 是 `ℕ`，实例是
`Monoid` 里的 `npow`（实例名 `NPow.toPow`）：
-/

set_option pp.numericTypes true in
/-- info: fun x ↦ x ^ (2 : ℕ) : ℝ → ℝ -/
#guard_msgs in #check fun x : ℝ ↦ x ^ 2

/-- info: NPow.toPow -/
#guard_msgs in #synth Pow ℝ ℕ

/-!
底数被转换，指数不动：下面 `a ^ b` 的底数 `a : ℕ` 成了 `↑a`，指数 `b : ℕ` 原样：
-/

/-- info: fun x a b ↦ x * ↑a ^ b : ℝ → ℕ → ℕ → ℝ -/
#guard_msgs in #check fun (x : ℝ) (a b : ℕ) ↦ x * a ^ b

/-!
指数的类型决定用哪个实例：`ℤ` 指数走 `zpow`，`(-1 : ℤ)` 次幂是倒数：
-/

example (x : ℝ) : x ^ (-1 : ℤ) = x⁻¹ := zpow_neg_one x

/-!
**一个经典的坑。** 指数 `1 / 2` 独立精译，是 `ℕ` 里的 `1 / 2 = 0`，所以 `x ^ (1 / 2)` 是 `x ^ 0 = 1`，
不是平方根：
-/

example (x : ℝ) : x ^ (1 / 2) = 1 := by norm_num

/-!
想要平方根，要用别的函数，不能靠整数除法的指数。具体写法与引理需要本章没有导入的模块，留到第 11 章，
那里导入并演示。

## 11. `Decidable` 与 `DecidableEq`

第 6 章讲过 `Decidable p` 是一个类（一个 `Bool` 加对应 `p` 的证明），同样走实例合成。`if p then a else b`
要在运行时判断 `p`，所以需要 `Decidable p`：
-/

/-- error: failed to synthesize instance of type class
  Decidable p -/
#guard_msgs (substring := true) in
example (p : Prop) (a b : ℕ) : ℕ := if p then a else b

/-!
修法之一：把 `Decidable p` 作为假设，由调用者提供（另一种见 §12）：
-/

def pick2 (p : Prop) [Decidable p] (a b : ℕ) : ℕ := if p then a else b

/-- info: 10 -/
#guard_msgs in #eval pick2 (3 < 5) 10 20

/-!
`3 < 5` 的实例是 `Nat.decLt 3 5`。`DecidableEq α` 只是 `∀ a b : α, Decidable (a = b)` 的简写，
`DecidablePred P` 是 `∀ a, Decidable (P a)`：
-/

/-- info: Nat.decLt 3 5 -/
#guard_msgs in #synth Decidable ((3 : ℕ) < 5)

example : DecidableEq ℕ = (∀ a b : ℕ, Decidable (a = b)) := rfl

example (p : Prop) : p ∨ ¬p := by by_cases h : p <;> simp [h]

/-!
证明里用不着它：`by_cases`（第 4 章）对任意命题都能用。需要 `Decidable` 的是出现在语句或定义里的
`if`、`Nat.find`（以及第 12 章的 `Finset.filter`）一类。

## 12. `classical` 策略与 `open Classical`

`Nat.find h`（`h : ∃ n, P n`）给出最小的满足 `P` 的数，要逐个判断 `P n`，所以需要 `DecidablePred P`。
对任意的 `P`，实例合成找不到：
-/

/-- error: failed to synthesize instance of type class
  DecidablePred P -/
#guard_msgs (substring := true) in
example (P : ℕ → Prop) (h : ∃ n, P n) : ∃ m, P m := ⟨Nat.find h, Nat.find_spec h⟩

/-!
`classical` 策略在其后的证明里临时加入 `Classical.propDecidable`，让任何命题可判定；它只在这个策略块里有效
（上面不带它的同一写法失败）：
-/

example (P : ℕ → Prop) (h : ∃ n, P n) : ∃ m, P m ∧ ∀ k < m, ¬ P k := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun k hk ↦ Nat.find_min h hk⟩

/-!
`open Classical` 打开命名空间里的 scoped instance `Classical.propDecidable`，它的优先级是 `low`：有可计算
实例的命题（如 `3 < 5`）仍用原来的，没有别的实例可用的命题才退到它。文件范围的 `open Classical` 会让语句
里悄悄带上不可计算的实例，所以 Mathlib 的风格是：证明里用 `classical`，定义前用 `open Classical in`。用了
它的 `def` 必须标 `noncomputable`：
-/

/-- info: Nat.decLt 3 5 -/
#guard_msgs in
open Classical in
#synth Decidable ((3 : ℕ) < 5)

/-- info: propDecidable (∀ (n : ℕ), n = n) -/
#guard_msgs in
open Classical in
#synth Decidable (∀ n : ℕ, n = n)

/-- error: failed to synthesize
  Decidable (∀ (n : ℕ), n = n) -/
#guard_msgs (substring := true) in #synth Decidable (∀ n : ℕ, n = n)

/-- error: failed to compile definition, consider marking it as 'noncomputable' because it
depends on 'propDecidable', which is 'noncomputable' -/
#guard_msgs (whitespace := lax) in
open Classical in
def pick3 (p : Prop) (a b : ℕ) : ℕ := if p then a else b

open Classical in
noncomputable def pick3' (p : Prop) (a b : ℕ) : ℕ := if p then a else b

/-!
## 13. `noncomputable` 与 `ℝ`

`noncomputable` 的意思是：这个定义不生成可执行代码，所以不能直接用 `#eval` 执行；但它照常通过类型检查，
照常用在定理里，也随所在模块一起构建（本文件含有 `noncomputable def`，整体仍然能编译）。`ℝ` 的序是
经典的：`Real.decidableLT` 本身是 `noncomputable`，`(1 : ℝ) < 2` 的 `Decidable` 实例最终归结到
`Classical.choice`，所以 `decide` 失败（第 5 章已见），要用 `norm_num`：
-/

/-- info: Real.decidableLT 1 2 -/
#guard_msgs in #synth Decidable ((1 : ℝ) < 2)

/-- error: Tactic `decide` failed to reduce -/
#guard_msgs (whitespace := lax, substring := true) in
example : (1 : ℝ) < 2 := by decide

example : (1 : ℝ) < 2 := by norm_num

/-!
定义里用了 `ℝ` 上的 `if` 同样必须标 `noncomputable`，报错指向那个不可计算的实例；标了之后证明照常进行：
-/

/-- error: failed to compile definition, consider marking it as 'noncomputable' because it
depends on 'Real.decidableLT', which is 'noncomputable' -/
#guard_msgs (whitespace := lax) in
def sgn (x : ℝ) : ℤ := if x < 0 then -1 else 1

noncomputable def sgn' (x : ℝ) : ℤ := if x < 0 then -1 else 1

example : sgn' 3 = 1 := by simp [sgn']

-- 没有可执行代码：`#eval` 要先生成代码，于是报错（`sgn'` 本身在定理里照常可用，见上面的 `example`）
/-- error: failed to compile definition, consider marking it as 'noncomputable' because it
depends on 'sgn'', which is 'noncomputable' -/
#guard_msgs (whitespace := lax) in
#eval sgn' 3

/-!
## 14. 常见错误

**1. 把需要 `CommRing` 的引理用在 `ℕ` 上。** `ℕ` 只是交换半环，报错落在实例合成。改法：换成 `ℤ`，或者改用只要
`CommSemiring` 的引理（`gen_add_sq`）：
-/

/-- error: failed to synthesize instance of type class
  CommRing ℕ -/
#guard_msgs (substring := true) in
example (x y : ℕ) : (x + y) * (x - y) = x ^ 2 - y ^ 2 := gen_diff_sq x y

/-!
**2. 转换方向写反。** `h : (a : ℝ) < b` 与 `a < b` 长得像，类型却不同，不能直接 `exact`；用
`exact_mod_cast h` 或 `norm_cast at h`：
-/

/-- error: Type mismatch
  h
has type
  ↑a < ↑b
but is expected to have type
  a < b -/
#guard_msgs (substring := true) in
example (a b : ℕ) (h : (a : ℝ) < b) : a < b := h

/-!
**3. `push_cast` 不会去上下文里找前提。** `↑(a - b) = ↑a - ↑b` 要 `b ≤ a` 才成立（`a = 2`、`b = 3` 时
不成立）。即使上下文里有 `h : b ≤ a`，单独的 `push_cast` 也不用它，什么也不做，linter（代码检查器）会提醒；
要写 `push_cast [h]` 或 `rw [Nat.cast_sub h]`（§9 第 3 条）：
-/

/--
warning: Unused tactic linter: `push_cast` does nothing.

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) = a - b := by
  push_cast
  exact Nat.cast_sub h

/-!
**4. 忘了 `instance`。** 写了加法函数 `Pt.add`，`+` 却找不到它：普通 `def` 不会自动登记到实例库，
要用 `instance`（或 `attribute [instance]`）：
-/

structure Pt where
  x : ℤ
  y : ℤ

def Pt.add (p q : Pt) : Pt := ⟨p.x + q.x, p.y + q.y⟩

set_option pp.mvars false in
/-- error: failed to synthesize instance of type class
  HAdd Pt Pt ?_ -/
#guard_msgs (substring := true) in
example (p q : Pt) : Pt := p + q

instance : Add Pt := ⟨Pt.add⟩

example (p q : Pt) : Pt := p + q

/-!
## 练习

练习 8.7 用到结构体 `MaxNat`（取较大者作乘法，`0` 作单位元），练习 8.14 用到 `ℝ` 上的 `step`。练习 8.1、8.7
的结论是一个类的值。用 `def` 声明这样的值会触发 `warn.classDefReducibility` 警告：
-/

/-- warning: Definition `Lean4Learn.Ch08.monoidOfField` of class type is semireducible. -/
#guard_msgs (substring := true) in
def monoidOfField (K : Type*) [Field K] : Monoid K := inferInstance

/-!
所以这两题用 `abbrev`：8.1 把 `sorry` 换成 `inferInstance`，8.7 手写各字段。平时自己写实例用 `instance`。
-/

structure MaxNat where
  val : ℕ

instance : Mul MaxNat := ⟨fun x y ↦ ⟨max x.val y.val⟩⟩
instance : One MaxNat := ⟨⟨0⟩⟩

noncomputable def step (x : ℝ) : ℕ := if 0 ≤ x then 1 else 0

/-- 练习 8.1（★）：把 `Field` 降成 `Monoid`。不写证明，让实例合成完成。 -/
abbrev ex_8_1 (K : Type*) [Field K] : Monoid K := sorry

/-- 练习 8.2（★）：交换环里 `a * b = 1` 则 `a ^ 2 * b ^ 2 = 1`。提示：`mul_pow` 是 `CommMonoid` 的引理。 -/
theorem ex_8_2 {R : Type*} [CommRing R] (a b : R) (h : a * b = 1) : a ^ 2 * b ^ 2 = 1 := sorry

/-- 练习 8.3（★）：域里的通分。提示：`field_simp`（第 10 章详讲）。 -/
theorem ex_8_3 {K : Type*} [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := sorry

/-- 练习 8.4（★★）：有序域里的平均值不等式。提示：先证
`a / b + b / a - 2 = (a - b) ^ 2 / (a * b)`，再 `positivity`。 -/
theorem ex_8_4 {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (a b : K)
    (ha : 0 < a) (hb : 0 < b) : 2 ≤ a / b + b / a := sorry

/-- 练习 8.5（★★）：复习第 3、4 章。群里 `(a * b)⁻¹ = b⁻¹ * a⁻¹`，不直接用 `mul_inv_rev`。
提示：`inv_eq_of_mul_eq_one_right : a * b = 1 → a⁻¹ = b`，再用 `mul_assoc`、`mul_inv_cancel`。 -/
theorem ex_8_5 {G : Type*} [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := sorry

/-- 练习 8.6（★）：复习第 3 章的项模式。格里的不等式。提示：`inf_le_left`、`le_sup_left`。 -/
theorem ex_8_6 {α : Type*} [Lattice α] (a b c : α) (h : a ≤ c) : a ⊓ b ≤ c ⊔ b := sorry

/-- 练习 8.7（★★）：为 `MaxNat` 定义 `Monoid` 实例。提示：每条公理写成 `fun ⟨x⟩ ⟨y⟩ ⟨z⟩ ↦ …`，
再用 `congrArg MaxNat.mk` 配 `max_assoc`、`Nat.zero_max`、`Nat.max_zero`。 -/
abbrev ex_8_7 : Monoid MaxNat := sorry

/-- 练习 8.8（★）：复习第 5、6 章。`Aff` 的平方有显式公式。提示：`pow_two`、`Aff.mul_def`。 -/
theorem ex_8_8 (f : Aff) : f ^ 2 = ⟨f.a * f.a, f.a * f.b + f.b⟩ := sorry

/-- 练习 8.9（★）：`ℕ` 的严格不等式给出 `ℝ` 里的 `+ 1` 不等式。提示：`Nat.succ_le_of_lt`。 -/
theorem ex_8_9 (n m : ℕ) (h : n < m) : (n : ℝ) + 1 ≤ m := sorry

/-- 练习 8.10（★★）：被减数更大时，截断减法与转换。提示：`Nat.cast_sub`。 -/
theorem ex_8_10 (a b : ℕ) (h : b ≤ a) : ((a - b : ℕ) : ℝ) + b = a := sorry

/-- 练习 8.11（★★）：复习第 2 章的 `linarith`。提示：先在 `ℝ` 里得到 `(a : ℝ) = 2 * b`，
再 `exact_mod_cast`。 -/
theorem ex_8_11 (a b : ℕ) (h : (a : ℝ) / 2 = b) : a = 2 * b := sorry

/-- 练习 8.12（★）：`^` 的陷阱。指数 `1 / 2 + 1` 是 `ℕ`，值为 `1`。提示：`norm_num`。 -/
theorem ex_8_12 (x : ℝ) : x ^ (1 / 2 + 1) = x := sorry

/-- 练习 8.13（★）：复习第 2 章的 `simp [h]`。`if` 与可判定性（§11）。提示：`simp [h]`。 -/
theorem ex_8_13 (p : Prop) [Decidable p] (a b : ℕ) (h : ¬ p) : (if p then a else b) = b := sorry

/-- 练习 8.14（★★）：`step`（见上）在 `ℝ` 上用了 `if`，所以是 `noncomputable`，`decide` 用不了。
提示：`norm_num [step]`。 -/
theorem ex_8_14 : step 2 = 1 ∧ step (-1) = 0 := sorry

/-- 练习 8.15（★★★）：整除时 `ℕ` 的除法与转换交换。
提示：`Nat.even_mul_succ_self`、`Nat.cast_div`、`push_cast`。 -/
theorem ex_8_15 (n : ℕ) : ((n * (n + 1) / 2 : ℕ) : ℝ) = n * (n + 1) / 2 := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 实例隐式参数 | `[Group G]`、`[Field K] [LinearOrder K] [IsStrictOrderedRing K]` | 读定理假设；调用时自动合成 |
| 查看实例 | `#synth C`、`inferInstance`、`@f _ inferInstance x` | 排错；手动指定实例 |
| 层次结构 | `Monoid → Group`，`Semiring → Ring → CommRing`，`CommRing`+`DivisionRing` → `Field` | 写最弱的类 |
| 序的 mixin | `[LinearOrder K] [IsStrictOrderedRing K]`（没有 `LinearOrderedField`） | 有序域/环上的引理 |
| 自定义实例 | `instance : Mul T`、`instance : Monoid T where …` | 先给运算，再证公理 |
| 强制转换 | `(n : ℝ)`、`↑n`、`⇑f`、`↥s` | 把 `ℕ`、`ℤ` 的项放进 `ℝ`；转换插在叶子上 |
| 类型转换策略 | `push_cast`、`norm_cast (at)`、`exact_mod_cast` | 推进/拉出转换；`ℕ` 减法带前提 |
| `^` 规则 | `x ^ (n : ℕ)`、`x ^ (-1 : ℤ)`；`x ^ (1 / 2)` 是 `x ^ 0` | 指数永不自动转换 |
| 可判定性 | `[Decidable p]`、`DecidableEq`、`#synth Decidable p` | `if`、`Nat.find` |
| 经典逻辑 | `classical`（证明）、`open Classical in`（定义）、`noncomputable` | `ℝ` 上用 `norm_num` 代替 `decide` |

## 延伸阅读

- *Theorem Proving in Lean 4*：第 10 章「Type Classes」；*Functional Programming in Lean*：
  「Overloading and Type Classes」。
- *Lean Language Reference* 4.35.0：第 10 章「Type Classes」的 10.2「Instance Declarations」与 10.3
  「Instance Synthesis」，以及第 11 章「Coercions」。
- *Mathematics in Lean*：「Hierarchies」一章（用 `class` 与 `extends` 自建代数层次，对应本书第 15 章）。
- Mathlib 源码：`Mathlib/Algebra/Group/Semigroup.lean`（`Semigroup`）、`Group/Monoid.lean`（`MulOneClass`、
  `Monoid`）、`Group/DivInvMonoid.lean`、`Group/Defs.lean`（`Group`）、`Algebra/Ring/Defs.lean`、
  `Algebra/Field/Defs.lean`（`DivisionRing`、`Field`）、
  `Algebra/Order/Ring/Defs.lean`（`IsStrictOrderedRing`，文件头有层次结构表）、
  `Mathlib/Basic/Real/Basic.lean`（`ℝ` 的代数与序实例）、
  `Mathlib/Algebra/HierarchyDesign.lean`（设计说明）。
- 核心库：`Init/Coe.lean`（`Coe` 一族与 `↑`）、`Init/Classical.lean`（`propDecidable` 的 scoped 声明）；
  `Mathlib/Tactic/Linter/Style.lean`（`openClassical` 检查）；`cast_*` 引理在
  `Mathlib/Data/Nat/Cast/Defs.lean`、`Mathlib/Data/Int/Cast/Basic.lean`。
- 本书第 15 章（设计类层次、实例优先级）、第 9 章（`Nat.cast_*` 的命名规律）、第 11 章（`ℝ` 上的不等式）、
  第 24 章（给程序里的类型写 `instance`）。
-/

end Lean4Learn.Ch08

end
