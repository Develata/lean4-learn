module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ToAdditive

/-!
# 第 15 章　构造结构与层次结构（设计者视角）

第 8 章是使用者的一侧（读 `[Group G]`、`#synth`、写 `Monoid` 实例）。本章换到设计者的一侧：何时用 `class`，
`extends` 怎样拼接父结构，实例冲突时谁赢；搭一条小小的类链并对照 Mathlib 的真实层次结构；子群这类
subobject（子结构）为什么用 `SetLike`，同态为什么是 bundled map（打包映射）、用 `FunLike` 收拢；
quotient type（商类型）的构造；最后用一个加权图结构体把这些东西走一遍。

## 学习目标
- 区分 `structure` 与 `class`，写出带 `extends` 的声明；用 `priority` 控制实例顺序，说明 `outParam` 的用途；
- 写出 `MyMulOne → MyMonoid → MyGroup` 并与 Mathlib 的 `Semigroup → Monoid → Group`、序 mixin 对照，
  用 `with_reducible_and_instances rfl` 检查 diamond（菱形）；用 `@[to_additive]` 生成加法版本；
- 为自己的结构写 `SetLike` 实例，使用 Mathlib 的 `Subgroup`；
- 用 `→+`、`→*`、`→+*`、`⇑f`、`map_add`、`map_mul` 处理打包映射，照 `FunLike` 模板写自己的映射类型；
- 用 `Setoid`、`Quotient.lift`/`ind`/`sound` 构造商类型，认识 `QuotientGroup`；
- 说出 `variable` 进入定理签名的四条规则，会用 `include`、`omit`；
- 为带约束的数据（加权图）设计结构体并写实例。

## 前置知识
第 2 章的 `omega`；第 3 章的隐式参数与宇宙；第 5 章的 `calc`、`simp`；第 6 章的 `structure`、`induction`；
第 7 章的 `Set`、`↥`；第 8 章的类型类使用者视角、`#synth`、`Monoid` 实例；第 9 章的 `to_additive` 命名对应；
第 12 章的 `Finset`、`∑`；第 13 章 `variable` 的初步。
-/

@[expose] public section

namespace Lean4Learn.Ch15

/-!
## 1. `structure`、`class` 与 `extends`

两者都是「一组字段的打包」，区别在于使用方式：`structure` 的字段取出需要一个显式的对象，`class` 的字段
取出需要一个由 instance synthesis（实例合成）自动找到的对象。下面的 `Rect` 是结构体，`HasArea` 是类；
注意 `HasArea.area` 的实例参数是 `[self : HasArea α]`，而 `Rect.w` 的参数是显式的 `Rect`：
-/

structure Rect where
  w : ℕ
  h : ℕ

class HasArea (α : Type) where
  area : α → ℕ

instance : HasArea Rect where
  area r := r.w * r.h

/-- info: @HasArea.area : {α : Type} → [self : HasArea α] → α → ℕ -/
#guard_msgs in
#check @HasArea.area

/-- info: Rect.w : Rect → ℕ -/
#guard_msgs in
#check @Rect.w

/-!
选择的标准：对象需要被**查找**（一个类型上约定只用一份这套结构，调用者不想传它）用 `class`，其余用
`structure`。Mathlib 为 `ℕ` 固定了唯一一个 `Monoid ℕ` 实例（乘法），所以 `Monoid` 是类；一个具体的矩形
属于后者。方括号 `[…]` 里只能放类；把结构体放进去，报错如下：
-/

/--
error: invalid binder annotation, type is not a class instance
  Rect

Note: Use the command `set_option checkBinderAnnotations false` to disable the check
-/
#guard_msgs in
example [Rect] : ℕ := 0

/-!
**`extends`。** `structure B extends A` 让 `B` 带有 `A` 的全部字段。`A` 作为一个字段 `B.toA` 嵌入，所以 `B`
的项可以直接用 `A` 的字段名，也能取出 `toA`；匿名构造子的第一个参数就是这个 `A`。Lean 4.18 起还可以给父结构
起名：`extends r : Rect` 把嵌入字段命名为 `r` 而不是 `toRect`：
-/

structure ColoredRect extends Rect where
  color : String

/-- info: ColoredRect.mk : Rect → String → ColoredRect -/
#guard_msgs in
#check @ColoredRect.mk

def redSquare : ColoredRect := { w := 2, h := 2, color := "red" }

example : redSquare.w = 2 ∧ redSquare.toRect.w = 2 := ⟨rfl, rfl⟩

structure ColoredRect' extends r : Rect where
  color : String

/-- info: ColoredRect'.r : ColoredRect' → Rect -/
#guard_msgs in
#check @ColoredRect'.r

/-!
`class` 的 `extends` 多一层含义：**父类的投影自动成为实例**，所以 `[C α]` 就蕴含它的所有父类。
`MyMulOne` 是 §3 要搭的链的第一环，它只带两个数据字段、没有公理：
-/

class MyMulOne (M : Type*) extends One M, Mul M

example (M : Type*) [MyMulOne M] : Mul M := inferInstance

/-!
## 2. 实例：优先级与 `outParam`

同一个目标上有多个实例时，Lean 先试 instance priority（实例优先级）高的；同优先级时，**后声明的先试**；
第一个成功的被采用。`instance (priority := …)` 指定优先级，数值越大越先试；`default` 是 1000，`low`、
`high` 分别低于、高于它（数值见 Lean 参考手册，本章只用「`high` 先试、`low` 后试」）。
先声明 A、B 两个 `Greeting ℕ` 实例，`#synth` 报告的是胜出的那个：
-/

class Greeting (α : Type) where
  greet : α → String

instance instGreetA : Greeting ℕ := ⟨fun _ ↦ "A"⟩
instance instGreetB : Greeting ℕ := ⟨fun _ ↦ "B"⟩

/-- info: instGreetB -/
#guard_msgs in
#synth Greeting ℕ

/-!
`high` 的实例不论声明早晚都先试；`low` 的实例即使声明在最后也排在后面：
-/

instance (priority := high) instGreetC : Greeting ℕ := ⟨fun _ ↦ "C"⟩
instance (priority := low) instGreetD : Greeting ℕ := ⟨fun _ ↦ "D"⟩

/-- info: instGreetC -/
#guard_msgs in
#synth Greeting ℕ

/-!
Mathlib 怎样用优先级？一个惯例是：**对任意类型都适用**的实例（如「`Group` 是 `DivisionMonoid`」）调低
优先级（低于 1000 的若干个值），因为它们在搜索里几乎总是被试到，失败的搜索很贵（`HierarchyDesign.lean`
的 library note «lower instance priority»）。

**`outParam`。** 有些类的某些参数是**输出**：给定其余参数，答案唯一，调用者不应当也不必须提供。标成
`outParam` 后，实例合成在其余参数已知时就启动，并把结果写回。`Container c elem` 说「`c` 是装着 `elem` 的容器」：
-/

class Container (c : Type) (elem : outParam Type) where
  first? : c → Option elem

instance {α : Type} : Container (List α) α where
  first? xs := xs.head?

/-- info: Container.first? ["a", "b"] : Option String -/
#guard_msgs in
#check Container.first? ["a", "b"]

/-!
不标 `outParam`，`elem` 是普通输入参数，表达式 `Container'.first? ["a", "b"]` 的 `elem` 还是未知的
元变量，实例合成因此卡住。给出期望类型（`elem` 由 unification（合一）得到）可以绕过，但调用者每次都得知道答案：
-/

class Container' (c : Type) (elem : Type) where
  first? : c → Option elem

instance {α : Type} : Container' (List α) α where
  first? xs := xs.head?

/--
error: typeclass instance problem is stuck
  Container' (List String) ?_
-/
#guard_msgs (substring := true) in
set_option pp.mvars false in
example := Container'.first? ["a", "b"]

example : Option String := Container'.first? ["a", "b"]

/-!
Mathlib 里随处可见，例如 `SetLike A B` 的 `B`（§5）：
-/

/-- info: SetLike : Type u_1 → outParam (Type u_2) → Type (max u_1 u_2) -/
#guard_msgs in
#check @SetLike

/-!
## 3. 层次结构：自己搭一条，再看 Mathlib 的

Mathlib 的设计原则：数据（运算）放在底层的类里，上层的类用 `extends` 叠加**公理**。`MyMulOne` 只有数据；
`MyMonoid` 加三条公理；`MyGroup` 再加一个逆运算 `Inv` 和一条公理 `a⁻¹ * a = 1`：
-/

class MyMonoid (M : Type*) extends MyMulOne M where
  mul_assoc : ∀ a b c : M, a * b * c = a * (b * c)
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

class MyGroup (G : Type*) extends MyMonoid G, Inv G where
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

/-!
在这条链上证明引理，每一步只用类里的字段（`MyMonoid.mul_assoc` 等，带全名，因为我们在本章的命名空间里，
不与 Mathlib 的同名引理冲突）。第一个引理用群论的经典技巧 `a * a⁻¹ = (a⁻¹)⁻¹ * a⁻¹ * (a * a⁻¹)`：
-/

namespace MyGroup
variable {G : Type*} [MyGroup G]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  calc a * a⁻¹ = 1 * (a * a⁻¹) := (MyMonoid.one_mul _).symm
    _ = (a⁻¹)⁻¹ * a⁻¹ * (a * a⁻¹) := by rw [inv_mul_cancel]
    _ = (a⁻¹)⁻¹ * ((a⁻¹ * a) * a⁻¹) := by
        rw [MyMonoid.mul_assoc, MyMonoid.mul_assoc, ← MyMonoid.mul_assoc a⁻¹]
    _ = 1 := by rw [inv_mul_cancel, MyMonoid.one_mul, inv_mul_cancel]

theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  calc b = 1 * b := (MyMonoid.one_mul b).symm
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel]
    _ = a⁻¹ * (a * b) := MyMonoid.mul_assoc _ _ _
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = (a⁻¹ * a) * c := (MyMonoid.mul_assoc _ _ _).symm
    _ = c := by rw [inv_mul_cancel, MyMonoid.one_mul]

end MyGroup

/-!
最小的实例是平凡群 `Unit`：字段 `one`、`mul`、`inv` 是平铺的数据字段（来自底层的 `One`、`Mul`、`Inv`），
四条公理都是 `rfl`：
-/

instance : MyGroup Unit where
  one := ()
  mul _ _ := ()
  inv _ := ()
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel _ := rfl

/-!
**Mathlib 的真实类链**比这复杂一点：`Monoid` 有**两个**父类，`Semigroup`（结合律）和 `MulOneClass`
（`1 * a = a`、`a * 1 = a`，它又以 `MulOne` 为父类），再加幂 `npow`；`Group` 的父类是 `DivInvMonoid`
（在 `Monoid` 上加 `Inv`、`Div` 与整数幂），自己只加一条公理 `inv_mul_cancel`。父类投影都能 `#check`
（第 8 章已列过整条链）：
-/

/-- info: @Monoid.toSemigroup : {M : Type u_1} → [self : Monoid M] → Semigroup M -/
#guard_msgs in
#check @Monoid.toSemigroup

/-- info: @Group.toDivInvMonoid : {G : Type u_1} → [self : Group G] → DivInvMonoid G -/
#guard_msgs in
#check @Group.toDivInvMonoid

/-!
**序不在链里。** 第 8 章讲过没有 `LinearOrderedField`：序是另外一个类，序与代数的相容性是 `Prop` 类
（mixin，混入类：只加性质、不加数据的类）。`IsStrictOrderedRing R` 带 `[Semiring R] [PartialOrder R]`
两个实例参数，类型是 `Prop`，所以同一个 `ℝ` 上的 `+` 与 `≤` 都只有一份：
-/

/-- info: IsStrictOrderedRing : (R : Type u_1) → [Semiring R] → [PartialOrder R] → Prop -/
#guard_msgs in
#check @IsStrictOrderedRing

/-- info: Real.instIsStrictOrderedRing -/
#guard_msgs in
#synth IsStrictOrderedRing ℝ

/-!
这是 Mathlib 的设计规则（`Mathlib/Algebra/Group/Monoid.lean` 里的 library note «forgetful inheritance»）：
富结构的类要 `extends` 贫结构的类，再加一个字段说明两者相容，**不要**另写一个「从富到贫」的实例。
违反它就会得到 diamond：同一个类型经由两条路径得到同一个父类，两条路径给出的**数据**却不是 defeq。
`Prop` 部分的菱形无害，因为 proof irrelevance（证明无关性）使同一命题的两个证明 defeq。Mathlib 写完一个新实例后，
会用 `rfl` 做「无菱形」的检查（例如 `Mathlib/RingTheory/Ideal/Quotient/Defs.lean` 里的 `Sanity test`），
并把透明度限制在 `with_reducible_and_instances`，模拟类型类搜索实际能展开的深度。下面检查 `CommGroup G`
里从 `Group` 出发和从 `CommMonoid` 出发得到的 `Mul G` 是同一个：
-/

example (G : Type*) [CommGroup G] :
    (CommGroup.toGroup.toDivInvMonoid.toMonoid.toSemigroup.toMul : Mul G) =
      CommGroup.toCommMonoid.toMonoid.toSemigroup.toMul := by
  with_reducible_and_instances rfl

/-!
## 4. `@[to_additive]`：一份定义，两套名字

Mathlib 的乘法类都有加法孪生（`Monoid`/`AddMonoid`、`CommMonoid`/`AddCommMonoid`）。给乘法版本的定理加
`@[to_additive]`，加法版本自动生成，名字由规则猜出（如 `mul → add`）。下面对 `CommMonoid` 的
引理生成 `AddCommMonoid` 的版本 `my_add_left_comm`。第 9 章里读过的「乘法名对加法名」的对应表，就是这个
机制的产物；原理留到第 27 章：
-/

@[to_additive]
theorem my_mul_left_comm {M : Type*} [CommMonoid M] (a b c : M) : a * (b * c) = b * (a * c) :=
  mul_left_comm a b c

/--
info: @my_add_left_comm : ∀ {M : Type u_1} [inst : AddCommMonoid M] (a b c : M), a + (b + c) = b
  + (a + c)
-/
#guard_msgs (whitespace := lax) in
#check @my_add_left_comm

example (x y z : ℤ) : x + (y + z) = y + (x + z) := my_add_left_comm x y z

/-!
## 5. 子结构与 `SetLike`

子群、子环、子空间这类子结构有共同的接口 `SetLike A B`：「`A` 的每个项对应 `B` 的一个子集，且该对应是单射」。
有了它，`x ∈ S` 与 `↥S`（把 `S` 当类型）自动可用。按 `SetLike` 源码里的模板，自己的子幺半群这样写：
数据字段 `carrier`，闭包条件用后缀 `'`：
-/

structure MySubmonoid (M : Type*) [Monoid M] where
  carrier : Set M
  mul_mem' : ∀ {a b : M}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  one_mem' : (1 : M) ∈ carrier

namespace MySubmonoid
variable {M : Type*} [Monoid M]

instance : SetLike (MySubmonoid M) M where
  coe S := S.carrier
  coe_injective S T h := by cases S; cases T; congr

instance : PartialOrder (MySubmonoid M) := .ofSetLike (MySubmonoid M)

/-!
模板还包括：一条 `mem_carrier` 的 simp 引理把底层字段与 `∈` 接起来；一条 `@[ext]` 引理（`SetLike` 的实现者
必须自己复制它，`ext` 策略才认得）；以及去掉撇号的闭包引理，以便写 `S.mul_mem ha hb`：
-/

@[simp] theorem mem_carrier {S : MySubmonoid M} {x : M} : x ∈ S.carrier ↔ x ∈ S := Iff.rfl

@[ext] theorem ext {S T : MySubmonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

protected theorem mul_mem (S : MySubmonoid M) {a b : M} (ha : a ∈ S) (hb : b ∈ S) : a * b ∈ S :=
  S.mul_mem' ha hb

protected theorem one_mem (S : MySubmonoid M) : (1 : M) ∈ S := S.one_mem'

/-!
两个子幺半群的交仍是子幺半群。`Min` 给出记号 `⊓`；序的展开引理是 `le_iff`，它是 `rfl`，因为
`PartialOrder.ofSetLike` 把 `≤` 定义成成员关系的包含：
-/

instance : Min (MySubmonoid M) where
  min S T := ⟨(S : Set M) ∩ T, fun ha hb ↦ ⟨S.mul_mem ha.1 hb.1, T.mul_mem ha.2 hb.2⟩,
    ⟨S.one_mem, T.one_mem⟩⟩

theorem mem_inf {S T : MySubmonoid M} {x : M} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Iff.rfl

theorem le_iff {S T : MySubmonoid M} : S ≤ T ↔ ∀ x, x ∈ S → x ∈ T := Iff.rfl

end MySubmonoid

/-!
`SetLike` 让 `(S : Set M)`（底层集合）与 `↥S`（子类型）自动可用，`≤` 与集合包含互译（Mathlib 的公共引理
`SetLike.coe_subset_coe`）：
-/

example (S T : MySubmonoid ℕ) : S ≤ T ↔ (S : Set ℕ) ⊆ T := SetLike.coe_subset_coe.symm

/-!
Mathlib 的 `Subgroup G` 就是同样的设计，外加 `inv_mem'`。成员引理有两种写法：点记号 `H.mul_mem`，或者
对所有子结构共用的 `mul_mem`（要求 `MulMemClass`，`SubgroupClass` 扩展了它）；`↥H` 自动是群：
-/

section Subgroups
variable {G : Type*} [Group G] (H : Subgroup G)

example (x y : G) (hx : x ∈ H) (hy : y ∈ H) : x * y⁻¹ ∈ H := H.mul_mem hx (H.inv_mem hy)
example (x y : G) (hx : x ∈ H) (hy : y ∈ H) : x * y⁻¹ ∈ H := mul_mem hx (inv_mem hy)
example : Group H := inferInstance

end Subgroups

/-!
**什么时候不用 `SetLike`？** 当对象不由一个载体集合决定。例如 `SimpleGraph.Subgraph` 除了顶点集还有边集，
同一个顶点集对应许多子图，「`Subgraph` ↪ `Set V`」不是单射（`Mathlib/Combinatorics/SimpleGraph/
Subgraph.lean` 的文件头明确说了这一点），所以它走自己的 `Adj` 接口。§9 的加权图也不是 `SetLike`。

## 6. 打包映射：`→+`、`→*`、`→+*` 与 `FunLike`

同态要么是一个函数加一堆性质的散件（`f : G → H` 与 `hf : ∀ a b, f (a * b) = …`），要么是**打包**的：数据与
性质放进一个结构体。Mathlib 选后者：`M →* N`（`MonoidHom`）、`M →+ N`（`AddMonoidHom`）、`R →+* S`
（`RingHom`）。一个同态的定义要给出函数 `toFun` 与两条性质，字段名带撇号：
-/

def double : ℤ →+ ℤ where
  toFun x := 2 * x
  map_zero' := by simp
  map_add' x y := by ring

/-!
`double x` 能当函数用，靠的是 `FunLike` 提供的 coercion（强制转换），infoview 里显示成 `⇑double`（第 8 章已提到）。
`⇑double` 是函数，`double` 是同态：
-/

/-- info: ⇑double : ℤ → ℤ -/
#guard_msgs in
#check (double : ℤ → ℤ)

@[simp] theorem double_apply (x : ℤ) : double x = 2 * x := rfl

/-!
`FunLike F α β` 是「`F` 的项可以当 `α → β` 用」：它有一个**单射**的强制转换 `F → (α → β)`（单射保证外延性）。
所有打包映射都有 `FunLike` 实例，所以通用引理对它们一律适用，只要映射类与引理匹配：`→+` 上有 `map_add`、
`map_zero`，`→+*` 上还有 `map_mul`（下面的例子）；泛型的前提类见练习 15.6 的 `RingHomClass`。
所以你不需要 `double.map_add`：
-/

example (x y : ℤ) : double (x + y) = double x + double y := map_add double x y
example : double 0 = 0 := map_zero double
example (n x : ℤ) : double (n • x) = n • double x := map_zsmul double n x

/-!
乘法一侧是 `M →* N`（字段 `map_one'`、`map_mul'`）；环同态 `R →+* S` 同时保持加法、乘法与 `0`、`1`，
还能当 `MonoidHom` 或 `AddMonoidHom` 用（强制转换到父结构）。对一切保持环结构的 `F` 成立的
通用引理要 `[RingHomClass F R S]`，它给出 `map_pow` 等（见练习 15.6）：
-/

example (f : ℤ →+* ℝ) (a b : ℤ) : f (a * b) = f a * f b := map_mul f a b
example (f : ℤ →+* ℝ) : ℤ →* ℝ := f
example (f : ℤ →+* ℝ) : ℤ →+ ℝ := f

/-!
**自己写一个。** 照 `Mathlib/Basic/FunLike/Basic.lean` 的模板：结构体存函数与性质；`FunLike` 实例
（`coe_injective` 说：两个映射若作为函数相等则相等）；`@[ext]` 引理（用 `DFunLike.ext`）；`MyHomClass`
刻画「`F` 里的项保持乘法」，其中 `A B` 是 `outParam`（与 §2 同一理由：`F` 已知时 `A B` 唯一）；
通用引理对任何 `F` 成立：
-/

structure MyHom (A B : Type*) [Mul A] [Mul B] where
  toFun : A → B
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

namespace MyHom
variable {A B C : Type*} [Mul A] [Mul B] [Mul C]

instance : FunLike (MyHom A B) A B where
  coe := MyHom.toFun
  coe_injective f g h := by cases f; cases g; congr

@[ext] theorem ext {f g : MyHom A B} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

def comp (g : MyHom B C) (f : MyHom A B) : MyHom A C where
  toFun x := g (f x)
  map_mul' x y := (congrArg g (f.map_mul' x y)).trans (g.map_mul' _ _)

@[simp] theorem comp_apply (g : MyHom B C) (f : MyHom A B) (x : A) : g.comp f x = g (f x) := rfl

end MyHom

class MyHomClass (F : Type*) (A B : outParam Type*) [Mul A] [Mul B] [FunLike F A B] : Prop where
  map_mul : ∀ (f : F) x y, f (x * y) = f x * f y

instance {A B : Type*} [Mul A] [Mul B] : MyHomClass (MyHom A B) A B where
  map_mul f := f.map_mul'

theorem my_map_mul3 {F A B : Type*} [Mul A] [Mul B] [FunLike F A B] [MyHomClass F A B] (f : F)
    (x y z : A) : f (x * y * z) = f x * f y * f z := by
  rw [MyHomClass.map_mul, MyHomClass.map_mul]

example {A B : Type*} [Mul A] [Mul B] (f : MyHom A B) (x y z : A) :
    f (x * y * z) = f x * f y * f z := my_map_mul3 f x y z

/-!
`my_map_mul3` 是对 `F` 泛型的，所以同一条引理对 `MyHom` 适用；Mathlib 里 `map_mul` 对 `MonoidHom`、
`RingHom`、`MulEquiv` 一律适用，原因相同。

只想让结构体「能被应用」，并不需要 `FunLike`：核心库的 `CoeFun` 实例就够了。
`FunLike` 多给的是单射性，从而有外延性和上面这些通用引理：
-/

structure Affine where
  a : ℕ
  b : ℕ

instance : CoeFun Affine (fun _ ↦ ℕ → ℕ) where
  coe f x := f.a * x + f.b

/-- info: 11 -/
#guard_msgs in
#eval (⟨2, 1⟩ : Affine) 5

/-!
## 7. `Setoid` 与商类型

当「相等」不是你想要的相等：整数是自然数对 `(a, b)`（代表 `a - b`）模去等价关系：`(a, b) ~ (c, d)`
当且仅当 `a + d = c + b`。Lean 的做法分两步：先给出 setoid（广集）：带等价关系的类型，再取 `Quotient`。
等价关系的三条性质装在 `iseqv` 里，关系自己写 `r`；`≈` 就是 `Setoid.r`：
-/

instance natPairSetoid : Setoid (ℕ × ℕ) where
  r p q := p.1 + q.2 = q.1 + p.2
  iseqv := ⟨fun p ↦ rfl, fun h ↦ h.symm,
    fun {p q r} (h₁ : p.1 + q.2 = q.1 + p.2) (h₂ : q.1 + r.2 = r.1 + q.2) ↦ by omega⟩

def MyInt : Type := Quotient natPairSetoid

namespace MyInt

def mk (p : ℕ × ℕ) : MyInt := Quotient.mk natPairSetoid p

/-!
商类型有三个基本工具，各管一件事：

- `Quotient.sound : a ≈ b → ⟦a⟧ = ⟦b⟧`：等价的代表给出相等的元素（`⟦a⟧` 是
  `Quotient.mk _ a` 的记号，下面的 `mk` 同义）；
- `Quotient.lift f h`：从代表上的函数 `f` 造商上的函数，必须附上证明 `h`：等价的输入给出相等的输出；
- `Quotient.ind`（`induction … using Quotient.ind`）：关于商上元素的命题，只需对代表证明。
-/

example : mk (3, 1) = mk (2, 0) := Quotient.sound (show 3 + 0 = 2 + 1 from rfl)

/-!
`lift` 的证明义务是「良定义性」：结果不依赖于代表的选择。取负、加法的证明归结为一个 `omega`（先 `show`
把 `≈` 展开成等式，`have` 把假设展开；`omega` 看不见没展开的 `≈`）。`Quotient.lift₂` 是两个参数的版本：
-/

instance : Neg MyInt where
  neg := Quotient.lift (fun p ↦ mk (p.2, p.1)) (by
    intro p q h
    apply Quotient.sound
    show p.2 + q.1 = q.2 + p.1
    have h' : p.1 + q.2 = q.1 + p.2 := h
    omega)

instance : Add MyInt where
  add := Quotient.lift₂ (fun p q ↦ mk (p.1 + q.1, p.2 + q.2)) (by
    intro p₁ q₁ p₂ q₂ h₁ h₂
    apply Quotient.sound
    show p₁.1 + q₁.1 + (p₂.2 + q₂.2) = p₂.1 + q₂.1 + (p₁.2 + q₁.2)
    have h₁' : p₁.1 + p₂.2 = p₂.1 + p₁.2 := h₁
    have h₂' : q₁.1 + q₂.2 = q₂.1 + q₁.2 := h₂
    omega)

/-!
`Quotient.lift` 在代表上**按定义规约**，所以运算在代表上的公式是 `rfl`：
-/

theorem add_mk (p q : ℕ × ℕ) : mk p + mk q = mk (p.1 + q.1, p.2 + q.2) := rfl
theorem neg_mk (p : ℕ × ℕ) : -mk p = mk (p.2, p.1) := rfl

/-!
证明商上的性质：用 `induction … using Quotient.ind` 对每个变量取代表。`with | _ p` 里的 `_` 是该情形的
名字（`Quotient.ind` 只有一个假设）。`trace_state` 看看取代表之后的目标：
-/

/--
trace: case a.a
p q : ℕ × ℕ
⊢ ⟦p⟧ + ⟦q⟧ = ⟦q⟧ + ⟦p⟧
-/
#guard_msgs in
protected theorem add_comm (a b : MyInt) : a + b = b + a := by
  induction a using Quotient.ind with
  | _ p =>
    induction b using Quotient.ind with
    | _ q =>
      trace_state   -- ⊢ ⟦p⟧ + ⟦q⟧ = ⟦q⟧ + ⟦p⟧
      show mk _ = mk _
      rw [Nat.add_comm p.1 q.1, Nat.add_comm p.2 q.2]

/-- 到 `ℤ` 的映射也是 `lift`，良定义性仍是 `omega`。 -/
def toInt : MyInt → ℤ := Quotient.lift (fun p ↦ (p.1 : ℤ) - p.2) (by
  intro p q h
  have h' : p.1 + q.2 = q.1 + p.2 := h
  show (p.1 : ℤ) - p.2 = q.1 - q.2
  omega)

example : toInt (mk (5, 2)) = 3 := rfl

end MyInt

/-!
Mathlib 里的「ℤ 模 n」是 `ZMod n`（`ZMod 5` 的元素可判定地计算），一般的群商是 `QuotientGroup`：
对子群 `N`，类型 `G ⧸ N`（记号 `⧸` 与除号 `/` 是不同的字符）是左陪集构成的商类型。Mathlib 只在
`[N.Normal]` 下提供实例 `Group (G ⧸ N)`（缺了它的报错见 §10）；数学上，使投影成为同态的群结构存在当且仅当
`N` 正规。`QuotientGroup.mk_mul` 说投影保持乘法，`QuotientGroup.eq` 说 `a`、`b` 在同一陪集的条件：
-/

example : (3 : ZMod 5) + 4 = 2 := by decide

section Quotients
variable {G : Type*} [Group G] (N : Subgroup G)

example [N.Normal] : Group (G ⧸ N) := inferInstance
example [N.Normal] (a b : G) : ((a * b : G) : G ⧸ N) = (a : G ⧸ N) * (b : G ⧸ N) :=
  QuotientGroup.mk_mul N a b
example [N.Normal] (a : G) : (a : G ⧸ N) = 1 ↔ a ∈ N := QuotientGroup.eq_one_iff a
example (a b : G) : (a : G ⧸ N) = b ↔ a⁻¹ * b ∈ N := QuotientGroup.eq

end Quotients

/-!
## 8. `variable`、`include`、`omit`

Lean 4.11 起，`theorem` 的签名不再由证明决定。区段变量进入定理签名，当且仅当它属于下面四类之一：

1. 在定理的**陈述**里被提到（证明里用到不算）；
2. 被 `include` 点名（`include x` 管到区段结束；`include x in` 只管下一条声明，见第 13 章；`omit` 见下）；
3. 是实例隐式变量（`[…]`），且它依赖的变量全都已被包含；
4. 被前三类变量（递归地）提到的变量，例如 `(hab : a = b)` 被包含时，`a`、`b` 及其类型 `α` 也随之进入。

`example` 与 `def` 不受这些限制，按使用决定。第 3 条是陷阱：实例变量即使用不上也会被拉进签名，代码检查器
`linter.unusedSectionVars` 提醒你，`omit` 把它去掉；没用到的实例变量则不进 `def` 的签名：
-/

section VarRules
variable {α : Type*} [Inhabited α] [Monoid α]

/--
warning: automatically included section variable(s) unused in theorem
  `Lean4Learn.Ch15.one_mul_demo`:
  [Inhabited α]
consider restructuring your `variable` declarations so that the variables are not in scope or
  explicitly omit them:
  omit [Inhabited α] in theorem ...
Note: This linter can be disabled with `set_option linter.unusedSectionVars false`
-/
#guard_msgs (whitespace := lax) in
theorem one_mul_demo (a : α) : 1 * a = a := one_mul a

/-- info: @one_mul_demo : ∀ {α : Type u_2} [Inhabited α] [inst : Monoid α] (a : α), 1 * a = a -/
#guard_msgs in
#check @one_mul_demo

omit [Inhabited α] in
theorem one_mul_demo' (a : α) : 1 * a = a := one_mul a

/-- info: @one_mul_demo' : ∀ {α : Type u_2} [inst : Monoid α] (a : α), 1 * a = a -/
#guard_msgs in
#check @one_mul_demo'

def inhabited_demo (a : α) : α := a

/-- info: @inhabited_demo : {α : Type u_2} → α → α -/
#guard_msgs in
#check @inhabited_demo

end VarRules

/-!
规则 1 的反面：陈述没提到的**假设**不会因为证明用到它就进入定理。下面 `refl_demo` 的陈述只提到 `a`，
`fail_if_success` 断言证明里看不见 `hab`，`#check` 显示签名里也没有 `b` 与 `hab`；同样的 `hab` 在 `example` 里
可以直接用。`include hab` 之后，`exists_eq_demo` 的陈述只提到 `α`，签名却多出 `a`、`b`（规则 2 与 4）：
-/

section IncludeRules
variable {α : Type*} (a b : α) (hab : a = b)

example : b = a := hab.symm

theorem refl_demo : a = a := by
  fail_if_success have := hab
  rfl

/-- info: @refl_demo : ∀ {α : Type u_2} (a : α), a = a -/
#guard_msgs in
#check @refl_demo

include hab

theorem exists_eq_demo : ∃ x y : α, x = y := ⟨a, b, hab⟩

/-- info: @exists_eq_demo : ∀ {α : Type u_2} (a b : α), a = b → ∃ x y, x = y -/
#guard_msgs in
#check @exists_eq_demo

end IncludeRules

/-!
在定理里直接写 `hab.symm` 这类引用，报的是 unknown identifier，和名字根本不存在时一样。下面在区段之外
（`hab` 确实不存在）用一个匿名 `example` 看这条消息：
-/

/-- error: Unknown identifier `hab.symm` -/
#guard_msgs in
example {α : Type*} (a b : α) : b = a := hab.symm

/-!
## 9. 案例：加权图结构体 `WGraph`

设计一个有限加权图：顶点是 `Fin n`，边权是自然数，权函数对称（无向图）。三种可选设计：(a) 一个函数
`weight : Fin n → Fin n → ℕ` 加对称性证明，这是本节的选择，代数友好（它就是一个对称矩阵）；
(b) `extends SimpleGraph V` 再加 `Sym2 V → W`，可复用图论 API，但非边上的权重是垃圾值；(c) 对固定的图 `G`
取 `G.edgeSet → W`（Mathlib 的 `EdgeLabeling`，
`Mathlib/Combinatorics/SimpleGraph/Coloring/EdgeLabeling.lean`），不需要新结构体，但只对固定的 `G`。选 (a)，是因为我们想要一个能逐边相加的对象，权 `0` 表示无边。

约定：结构体**不要求**对角线为零，`weight v v ≠ 0` 表示 `v` 上有一个自环。`@[ext]` 生成外延性引理：
因为证明字段 `symm` 是 `Prop`，两个图相等只需权函数相等：
-/

@[ext]
structure WGraph (n : ℕ) where
  weight : Fin n → Fin n → ℕ
  symm : ∀ u v, weight u v = weight v u

namespace WGraph
variable {n : ℕ}

/-!
实例逐个写。`Inhabited`：全零图。`Repr`：字段是函数，我们手写成权重矩阵（第 `u` 行第 `v` 列是
`weight u v`）；`Add`：逐边相加，对称性由两个图的对称性推出，再用 `@[ext]` 证明交换律：
-/

instance : Inhabited (WGraph n) := ⟨⟨fun _ _ ↦ 0, fun _ _ ↦ rfl⟩⟩

instance : Repr (WGraph n) where
  reprPrec G _ := repr (List.ofFn fun u : Fin n ↦ List.ofFn fun v : Fin n ↦ G.weight u v)

instance : Add (WGraph n) where
  add G H := ⟨fun u v ↦ G.weight u v + H.weight u v, fun u v ↦ by rw [G.symm u v, H.symm u v]⟩

theorem add_comm_graph (G H : WGraph n) : G + H = H + G := by
  ext u v
  exact Nat.add_comm _ _

/-- 完全图：任意两个不同顶点之间权为 `1`，没有自环。 -/
def complete (n : ℕ) : WGraph n where
  weight u v := if u = v then 0 else 1
  symm u v := by simp [eq_comm]

/-- info: [[0, 1, 1], [1, 0, 1], [1, 1, 0]] -/
#guard_msgs in
#eval complete 3

/-!
度与强度。`degree v` 数的是权非零的 `u`（包括 `u = v`），所以**自环只算一次**，不同于图论里自环贡献 2 的
常见约定；`strength v` 是边权之和：
-/

def degree (G : WGraph n) (v : Fin n) : ℕ := (Finset.univ.filter fun u ↦ G.weight v u ≠ 0).card

def strength (G : WGraph n) (v : Fin n) : ℕ := ∑ u, G.weight v u

example : (complete 4).degree 0 = 3 := by decide
example : (complete 4).strength 0 = 3 := by decide

/-- 一个顶点、带一个权为 `5` 的自环。 -/
def loop1 : WGraph 1 := ⟨fun _ _ ↦ 5, fun _ _ ↦ rfl⟩

example : loop1.degree 0 = 1 := by decide
example : loop1.strength 0 = 5 := by decide

/-! 两条引理：度不超过顶点数（`Finset.card_filter_le`）；强度能从另一端数（对称性）。 -/

theorem degree_le (G : WGraph n) (v : Fin n) : G.degree v ≤ n := by
  calc G.degree v ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem sum_weight_comm (G : WGraph n) (v : Fin n) :
    ∑ u, G.weight v u = ∑ u, G.weight u v :=
  Finset.sum_congr rfl fun u _ ↦ G.symm v u

end WGraph

/-!
## 10. 常见错误

**1. 少写一个字段。** 实例要给出类的所有没有默认值的字段，缺哪个报哪个：
-/

/-- error: Fields missing: `inv_mul_cancel` -/
#guard_msgs in
example : MyGroup Unit where
  one := ()
  mul _ _ := ()
  inv _ := ()
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-!
**2. `Quotient.lift` 的函数不良定义。** 取 `(a, b)` 的第一分量不是 `MyInt` 上的函数，因为 `(3, 1)` 与
`(2, 0)` 等价却给出 `3` 与 `2`。展开假设之后，证明义务 `p.1 = q.1` 是假的，`omega` 给出反例：
-/

/-- error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
-/
#guard_msgs (substring := true) in
example : MyInt → ℕ := Quotient.lift (fun p ↦ p.1) (by
  intro p q h
  have h' : p.1 + q.2 = q.1 + p.2 := h
  omega)

/-!
**3. 商群需要正规性。** 没有 `[N.Normal]`，Mathlib 不提供 `Group (G ⧸ N)` 实例：
-/

section NormalMissing
variable {G : Type*} [Group G] (N : Subgroup G)

/--
error: failed to synthesize instance of type class
  Group (G ⧸ N)

Hint: Type class instance resolution failures can be inspected with the `set_option
  trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example : Group (G ⧸ N) := inferInstance

end NormalMissing

/-!
**4. 把结构体当函数用。** 这里的 `Rect` 没有函数强制转换，所以不能直接应用。补救是给它一个强制转换：
最简单的是 §6 `Affine` 那样的 `CoeFun` 实例；本章用 `FunLike` 为 `MyHom` 提供它，同时得到外延性。
另外两类常见问题见 §2 的 `Container'`（实例合成卡住）与 §8（实例变量被拉进定理）：
-/

/--
error: Function expected at
  r
but this term has type
  Rect

Note: Expected a function because this term is being applied to the argument
  1
-/
#guard_msgs in
example (r : Rect) : ℕ := r 1

/-!
## 练习

练习 15.1–15.3 在 §3 的 `MyGroup` 链上做（15.2 回到第 5 章的 `rw`/`calc` 技巧，15.3 是自己写实例）；
15.5 用第 6 章的归纳；15.8 回到第 7 章的 `Set` 与成员关系；15.11 回到第 9 章的 `to_additive` 命名；
15.13 用第 2 章的 `omega`；15.15 回到第 12 章的 `Finset`/`∑`。引理名在本章出现。
-/

section Exercises

/-- 练习 15.1（★★）：逆元唯一。若 `a * b = 1`，则 `b = a⁻¹`；对 `b` 与 `a⁻¹` 用
`MyGroup.mul_left_cancel`（`a * b = a * a⁻¹`）。 -/
theorem ex_15_1 {G : Type*} [MyGroup G] {a b : G} (h : a * b = 1) : b = a⁻¹ := by sorry

/-- 练习 15.2（★★★）：`(a * b)⁻¹ = b⁻¹ * a⁻¹`。先用结合律与 `MyGroup.mul_inv_cancel` 证明
`a * b * (b⁻¹ * a⁻¹) = 1`，再用 15.1。 -/
theorem ex_15_2 {G : Type*} [MyGroup G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by sorry

/-- 练习 15.3（★★）：`Bool` 上存在一个 `MyGroup` 结构：单位元 `false`，乘法 `xor`，逆元是恒等；
四条公理对 `Bool` 穷举（`cases`）。 -/
theorem ex_15_3 : Nonempty (MyGroup Bool) := by sorry

/-- 练习 15.4（★）：存在同态 `f : ℤ →+ ℤ` 使 `f x = 3 * x`；仿照 `double`，用匿名构造子给出
`⟨{ toFun := …, map_zero' := …, map_add' := … }, …⟩`。 -/
theorem ex_15_4 : ∃ f : ℤ →+ ℤ, ∀ x, f x = 3 * x := by sorry

/-- 练习 15.5（★★）：两个 `ℤ →+ ℤ` 若在 `1` 处相等，则在每个自然数处相等。对 `n` 归纳（第 6 章），
后继情形用 `push_cast`、`map_add`。 -/
theorem ex_15_5 (f g : ℤ →+ ℤ) (h : f 1 = g 1) (n : ℕ) : f n = g n := by sorry

/-- 练习 15.6（★）：对一切保持环结构的映射类型 `F`，`f (x ^ 2 + 1) = f x ^ 2 + 1`；
`simp` 用 `map_add`、`map_pow`、`map_one`。 -/
theorem ex_15_6 {F : Type*} [FunLike F ℝ ℝ] [RingHomClass F ℝ ℝ] (f : F) (x : ℝ) :
    f (x ^ 2 + 1) = f x ^ 2 + 1 := by sorry

/-- 练习 15.7（★★）：`MyHom` 的复合保持三个元素的乘积。把 `my_map_mul3` 用在 `g.comp f` 上。 -/
theorem ex_15_7 {A B C : Type*} [Mul A] [Mul B] [Mul C] (f : MyHom A B) (g : MyHom B C)
    (x y z : A) : (g.comp f) (x * y * z) = g (f x) * g (f y) * g (f z) := by sorry

/-- 练习 15.8（★★）：造一个子幺半群。存在 `ℕ` 的子幺半群 `S`，其成员恰是非零数。取载体
`{x | x ≠ 0}`，闭包用 `Nat.mul_ne_zero`，最后的等价是 `Iff.rfl`（第 7 章的 `Set`）。 -/
theorem ex_15_8 : ∃ S : MySubmonoid ℕ, ∀ x, x ∈ S ↔ x ≠ 0 := by sorry

/-- 练习 15.9（★★）：交的泛性质。若 `U ≤ S` 且 `U ≤ T`，则 `U ≤ S ⊓ T`；
用 `MySubmonoid.le_iff` 与 `MySubmonoid.mem_inf`。 -/
theorem ex_15_9 {M : Type*} [Monoid M] (S T U : MySubmonoid M) (hS : U ≤ S) (hT : U ≤ T) :
    U ≤ S ⊓ T := by sorry

/-- 练习 15.10（★）：交是交换的：`S ⊓ T = T ⊓ S`。用 `ext`（即 `MySubmonoid.ext`），
不要用 `le_antisymm`。 -/
theorem ex_15_10 {M : Type*} [Monoid M] (S T : MySubmonoid M) : S ⊓ T = T ⊓ S := by sorry

/-- 练习 15.11（★）：用 §4 的 `my_add_left_comm`（`@[to_additive]` 生成）证明
`x + (y + (z + w)) = y + (z + (x + w))`；用两次，每次 `rw` 时给出前两个参数。 -/
theorem ex_15_11 (x y z w : ℤ) : x + (y + (z + w)) = y + (z + (x + w)) := by sorry

/-- 练习 15.12（★）：`MyInt` 上 `- -a = a`。对 `a` 用 `induction … using Quotient.ind`，
再试 `rfl`（`neg_mk` 是 `rfl`）。 -/
theorem ex_15_12 (a : MyInt) : - -a = a := by sorry

/-- 练习 15.13（★★）：`MyInt.toInt` 是单射。对 `a`、`b` 各取代表，用 `Quotient.sound`；`h` 可以用
`have h' : … := h` 重述成 `ℤ` 里的等式（二者定义相等），然后用 `omega`（第 2 章）。 -/
theorem ex_15_13 (a b : MyInt) (h : MyInt.toInt a = MyInt.toInt b) : a = b := by sorry

/-- 练习 15.14（★★）：若 `a⁻¹ * b ∈ N`，则 `a * a` 与 `b * b` 在 `G ⧸ N` 中相等；用 `QuotientGroup.eq`
把 `a`、`b` 化为同一陪集，再用 `QuotientGroup.mk_mul`。 -/
theorem ex_15_14 {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (a b : G)
    (hab : a⁻¹ * b ∈ N) : ((a * a : G) : G ⧸ N) = ((b * b : G) : G ⧸ N) := by sorry

/-- 练习 15.15（★★）：所有顶点的强度之和，等于把双重和交换次序后的和（第 12 章的 `Finset.sum_comm`）；
先展开 `WGraph.strength`。 -/
theorem ex_15_15 {n : ℕ} (G : WGraph n) :
    ∑ v, G.strength v = ∑ u, ∑ v, G.weight v u := by sorry

end Exercises

/-!
## 小结

| 概念 | 语法 / 名字 | 何时用 |
|---|---|---|
| `structure` / `class` | `structure S where …`；`class C (α) where …` | 要被查找、全局唯一用 `class`；其余 `structure` |
| 继承 | `extends A`；`extends r : A`（4.18 起可命名） | 叠加字段；`class` 的父类投影自动成实例 |
| 实例 | `(priority := high/low/N)`；`#synth`；`outParam` | 先优先级、后「后声明先试」；输出参数由其余参数决定 |
| 层次结构 | 数据放底层，公理用 `extends` 叠加；序是 `Prop` mixin | 不能「重新定义数据」，用 `with_reducible_and_instances rfl` 查菱形 |
| 加法孪生 | `@[to_additive]` 于乘法版定理 | 一份证明两套名字 |
| 子结构 | `SetLike A B`；`carrier`、`mul_mem'`；`PartialOrder.ofSetLike`；`SetLike.ext` | 由载体集合决定的对象；`Subgraph` 不是 |
| 打包映射 | `→+`、`→*`、`→+*`；`⇑f`；`map_add`、`map_mul`；`FunLike`、`*HomClass`；`CoeFun` | 同态；泛型引理对一切匹配的 `F` 成立 |
| 商 | `Setoid`；`Quotient.lift/ind/sound`；`⧸`；`QuotientGroup.eq`、`mk_mul` | 良定义性是证明义务；商群要 `[N.Normal]` |
| `variable` | `include`、`omit`；四条规则 | 陈述提到的、`include` 的、依赖已含的实例、以及它们提到的 |
-/

/-!
## 延伸阅读

- 设计指南：`Mathlib/Algebra/HierarchyDesign.lean`（library note «the algebraic hierarchy»、«lower instance
  priority»）；«forgetful inheritance» 与 `Monoid` 在 `Mathlib/Algebra/Group/Monoid.lean`，`Group` 在
  `Mathlib/Algebra/Group/Defs.lean`，`IsStrictOrderedRing` 在 `Mathlib/Algebra/Order/Ring/Defs.lean`。
- 打包映射与子结构：`Mathlib/Basic/FunLike/Basic.lean`、`Mathlib/Basic/SetLike/Basic.lean` 的文件头模板；
  `Mathlib/Algebra/Group/Hom/Defs.lean`、`Mathlib/Algebra/Group/Subgroup/Defs.lean`；函数强制转换：核心库
  `Init/Coe.lean` 的 `CoeFun`。商：核心库 `Init/Core.lean`（`Quotient.lift`、`Quotient.sound`）、
  `Mathlib/GroupTheory/QuotientGroup/Defs.lean`。
- `variable` 的四条规则：Lean v4.11.0 发布说明
  （`https://lean-lang.org/doc/reference/latest/releases/v4.11.0/`）。
- *Mathematics in Lean*（《Lean 形式化数学》）第 7、8 章 *Structures*、*Hierarchies*：同一条路线的
  另一种讲法；网页版代码有部分是旧版 Mathlib 的写法（如 `LinearOrderedRing`），以本书的锁定版本为准。
- 本书第 8 章（使用者视角）、第 9 章（`to_additive` 的命名对应）、第 18 章（`SimpleGraph`）、
  第 27、28 章（`to_additive` 的原理、实例合成与内核机制）。
-/

end Lean4Learn.Ch15

end
