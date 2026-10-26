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
# 第 15 章　答案

`Lean4Learn/Part2/Ch15_Hierarchies.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；练习用到的
`MyMulOne → MyMonoid → MyGroup` 链（及两条引理）、`my_mul_left_comm`、`MyHom`、`MySubmonoid`、`MyInt` 与 `WGraph` 在这里原样重述一遍，
使本文件自成一体。
-/

@[expose] public section

namespace Solutions.Ch15

class MyMulOne (M : Type*) extends One M, Mul M

class MyMonoid (M : Type*) extends MyMulOne M where
  mul_assoc : ∀ a b c : M, a * b * c = a * (b * c)
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

class MyGroup (G : Type*) extends MyMonoid G, Inv G where
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

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

@[ext] theorem ext {S T : MySubmonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := SetLike.ext h

protected theorem mul_mem (S : MySubmonoid M) {a b : M} (ha : a ∈ S) (hb : b ∈ S) : a * b ∈ S :=
  S.mul_mem' ha hb

protected theorem one_mem (S : MySubmonoid M) : (1 : M) ∈ S := S.one_mem'

instance : Min (MySubmonoid M) where
  min S T := ⟨(S : Set M) ∩ T, fun ha hb ↦ ⟨S.mul_mem ha.1 hb.1, T.mul_mem ha.2 hb.2⟩,
    ⟨S.one_mem, T.one_mem⟩⟩

theorem mem_inf {S T : MySubmonoid M} {x : M} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Iff.rfl

theorem le_iff {S T : MySubmonoid M} : S ≤ T ↔ ∀ x, x ∈ S → x ∈ T := Iff.rfl

end MySubmonoid

@[to_additive]
theorem my_mul_left_comm {M : Type*} [CommMonoid M] (a b c : M) : a * (b * c) = b * (a * c) :=
  mul_left_comm a b c

structure MyHom (A B : Type*) [Mul A] [Mul B] where
  toFun : A → B
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

namespace MyHom
variable {A B C : Type*} [Mul A] [Mul B] [Mul C]

instance : FunLike (MyHom A B) A B where
  coe := MyHom.toFun
  coe_injective f g h := by cases f; cases g; congr

def comp (g : MyHom B C) (f : MyHom A B) : MyHom A C where
  toFun x := g (f x)
  map_mul' x y := (congrArg g (f.map_mul' x y)).trans (g.map_mul' _ _)

end MyHom

class MyHomClass (F : Type*) (A B : outParam Type*) [Mul A] [Mul B] [FunLike F A B] : Prop where
  map_mul : ∀ (f : F) x y, f (x * y) = f x * f y

instance {A B : Type*} [Mul A] [Mul B] : MyHomClass (MyHom A B) A B where
  map_mul f := f.map_mul'

theorem my_map_mul3 {F A B : Type*} [Mul A] [Mul B] [FunLike F A B] [MyHomClass F A B] (f : F)
    (x y z : A) : f (x * y * z) = f x * f y * f z := by
  rw [MyHomClass.map_mul, MyHomClass.map_mul]

instance natPairSetoid : Setoid (ℕ × ℕ) where
  r p q := p.1 + q.2 = q.1 + p.2
  iseqv := ⟨fun p ↦ rfl, fun h ↦ h.symm,
    fun {p q r} (h₁ : p.1 + q.2 = q.1 + p.2) (h₂ : q.1 + r.2 = r.1 + q.2) ↦ by omega⟩

def MyInt : Type := Quotient natPairSetoid

namespace MyInt

def mk (p : ℕ × ℕ) : MyInt := Quotient.mk natPairSetoid p

instance : Neg MyInt where
  neg := Quotient.lift (fun p ↦ mk (p.2, p.1)) (by
    intro p q h
    apply Quotient.sound
    show p.2 + q.1 = q.2 + p.1
    have h' : p.1 + q.2 = q.1 + p.2 := h
    omega)

def toInt : MyInt → ℤ := Quotient.lift (fun p ↦ (p.1 : ℤ) - p.2) (by
  intro p q h
  have h' : p.1 + q.2 = q.1 + p.2 := h
  show (p.1 : ℤ) - p.2 = q.1 - q.2
  omega)

end MyInt

@[ext]
structure WGraph (n : ℕ) where
  weight : Fin n → Fin n → ℕ
  symm : ∀ u v, weight u v = weight v u

namespace WGraph
variable {n : ℕ}

def strength (G : WGraph n) (v : Fin n) : ℕ := ∑ u, G.weight v u

theorem sum_weight_comm (G : WGraph n) (v : Fin n) :
    ∑ u, G.weight v u = ∑ u, G.weight u v :=
  Finset.sum_congr rfl fun u _ ↦ G.symm v u

end WGraph

section Exercises

/-- 练习 15.1（★★）：逆元唯一。若 `a * b = 1`，则 `b = a⁻¹`；对 `b` 与 `a⁻¹` 用
`MyGroup.mul_left_cancel`（`a * b = a * a⁻¹`）。 -/
theorem ex_15_1 {G : Type*} [MyGroup G] {a b : G} (h : a * b = 1) : b = a⁻¹ := by
  refine MyGroup.mul_left_cancel (a := a) ?_
  rw [h, MyGroup.mul_inv_cancel]

/-- 练习 15.2（★★★）：`(a * b)⁻¹ = b⁻¹ * a⁻¹`。先用结合律与 `MyGroup.mul_inv_cancel` 证明
`a * b * (b⁻¹ * a⁻¹) = 1`，再用 15.1。 -/
theorem ex_15_2 {G : Type*} [MyGroup G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : a * b * (b⁻¹ * a⁻¹) = 1 := by
    rw [MyMonoid.mul_assoc, ← MyMonoid.mul_assoc b, MyGroup.mul_inv_cancel, MyMonoid.one_mul,
      MyGroup.mul_inv_cancel]
  exact (ex_15_1 h).symm

/-- 练习 15.3（★★）：`Bool` 上存在一个 `MyGroup` 结构：单位元 `false`，乘法 `xor`，逆元是恒等；
四条公理对 `Bool` 穷举（`cases`）。 -/
theorem ex_15_3 : Nonempty (MyGroup Bool) := by
  refine ⟨{ one := false, mul := xor, inv := id, mul_assoc := ?_, one_mul := ?_,
            mul_one := ?_, inv_mul_cancel := ?_ }⟩
  · intro a b c; cases a <;> cases b <;> cases c <;> rfl
  · intro a; cases a <;> rfl
  · intro a; cases a <;> rfl
  · intro a; cases a <;> rfl

/-- 练习 15.4（★）：存在同态 `f : ℤ →+ ℤ` 使 `f x = 3 * x`；仿照 `double`，用匿名构造子给出
`⟨{ toFun := …, map_zero' := …, map_add' := … }, …⟩`。 -/
theorem ex_15_4 : ∃ f : ℤ →+ ℤ, ∀ x, f x = 3 * x := by
  refine ⟨{ toFun := fun x ↦ 3 * x, map_zero' := by simp, map_add' := fun x y ↦ by ring }, ?_⟩
  intro x
  rfl

/-- 练习 15.5（★★）：两个 `ℤ →+ ℤ` 若在 `1` 处相等，则在每个自然数处相等。对 `n` 归纳（第 6 章），
后继情形用 `push_cast`、`map_add`。 -/
theorem ex_15_5 (f g : ℤ →+ ℤ) (h : f 1 = g 1) (n : ℕ) : f n = g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [map_add, map_add, ih, h]

/-- 练习 15.6（★）：对一切保持环结构的映射类型 `F`，`f (x ^ 2 + 1) = f x ^ 2 + 1`；
`simp` 用 `map_add`、`map_pow`、`map_one`。 -/
theorem ex_15_6 {F : Type*} [FunLike F ℝ ℝ] [RingHomClass F ℝ ℝ] (f : F) (x : ℝ) :
    f (x ^ 2 + 1) = f x ^ 2 + 1 := by
  simp

/-- 练习 15.7（★★）：`MyHom` 的复合保持三个元素的乘积。把 `my_map_mul3` 用在 `g.comp f` 上。 -/
theorem ex_15_7 {A B C : Type*} [Mul A] [Mul B] [Mul C] (f : MyHom A B) (g : MyHom B C)
    (x y z : A) : (g.comp f) (x * y * z) = g (f x) * g (f y) * g (f z) := my_map_mul3 (g.comp f) x y z

/-- 练习 15.8（★★）：造一个子幺半群。存在 `ℕ` 的子幺半群 `S`，其成员恰是非零数。取载体
`{x | x ≠ 0}`，闭包用 `Nat.mul_ne_zero`，最后的等价是 `Iff.rfl`（第 7 章的 `Set`）。 -/
theorem ex_15_8 : ∃ S : MySubmonoid ℕ, ∀ x, x ∈ S ↔ x ≠ 0 := by
  refine ⟨⟨{x | x ≠ 0}, fun {a b} ha hb ↦ Nat.mul_ne_zero ha hb, one_ne_zero⟩, ?_⟩
  intro x
  exact Iff.rfl

/-- 练习 15.9（★★）：交的泛性质。若 `U ≤ S` 且 `U ≤ T`，则 `U ≤ S ⊓ T`；
用 `MySubmonoid.le_iff` 与 `MySubmonoid.mem_inf`。 -/
theorem ex_15_9 {M : Type*} [Monoid M] (S T U : MySubmonoid M) (hS : U ≤ S) (hT : U ≤ T) :
    U ≤ S ⊓ T := by
  rw [MySubmonoid.le_iff] at hS hT ⊢
  intro x hx
  exact MySubmonoid.mem_inf.2 ⟨hS x hx, hT x hx⟩

/-- 练习 15.10（★）：交是交换的：`S ⊓ T = T ⊓ S`。用 `ext`（即 `MySubmonoid.ext`），
不要用 `le_antisymm`。 -/
theorem ex_15_10 {M : Type*} [Monoid M] (S T : MySubmonoid M) : S ⊓ T = T ⊓ S := by
  ext x
  rw [MySubmonoid.mem_inf, MySubmonoid.mem_inf]
  exact and_comm

/-- 练习 15.11（★）：用 §4 的 `my_add_left_comm`（`@[to_additive]` 生成）证明
`x + (y + (z + w)) = y + (z + (x + w))`；用两次，每次 `rw` 时给出前两个参数。 -/
theorem ex_15_11 (x y z w : ℤ) : x + (y + (z + w)) = y + (z + (x + w)) := by
  rw [my_add_left_comm x y, my_add_left_comm x z]

/-- 练习 15.12（★）：`MyInt` 上 `- -a = a`。对 `a` 用 `induction … using Quotient.ind`，
再试 `rfl`（`neg_mk` 是 `rfl`）。 -/
theorem ex_15_12 (a : MyInt) : - -a = a := by
  induction a using Quotient.ind with
  | _ p => rfl

/-- 练习 15.13（★★）：`MyInt.toInt` 是单射。对 `a`、`b` 各取代表，用 `Quotient.sound`；`h` 可以用
`have h' : … := h` 重述成 `ℤ` 里的等式（二者定义相等），然后用 `omega`（第 2 章）。 -/
theorem ex_15_13 (a b : MyInt) (h : MyInt.toInt a = MyInt.toInt b) : a = b := by
  induction a using Quotient.ind with
  | _ p =>
    induction b using Quotient.ind with
    | _ q =>
      apply Quotient.sound
      have h' : (p.1 : ℤ) - p.2 = q.1 - q.2 := h
      show p.1 + q.2 = q.1 + p.2
      omega

/-- 练习 15.14（★★）：若 `a⁻¹ * b ∈ N`，则 `a * a` 与 `b * b` 在 `G ⧸ N` 中相等；用 `QuotientGroup.eq`
把 `a`、`b` 化为同一陪集，再用 `QuotientGroup.mk_mul`。 -/
theorem ex_15_14 {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (a b : G)
    (hab : a⁻¹ * b ∈ N) : ((a * a : G) : G ⧸ N) = ((b * b : G) : G ⧸ N) := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.eq.2 hab]

/-- 练习 15.15（★★）：所有顶点的强度之和，等于把双重和交换次序后的和（第 12 章的 `Finset.sum_comm`）；
先展开 `WGraph.strength`。 -/
theorem ex_15_15 {n : ℕ} (G : WGraph n) :
    ∑ v, G.strength v = ∑ u, ∑ v, G.weight v u := by
  exact Finset.sum_comm

end Exercises

end Solutions.Ch15

end
