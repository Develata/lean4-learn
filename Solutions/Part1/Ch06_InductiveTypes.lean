module

public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.Linarith

/-!
# 第 6 章　答案

`Lean4Learn/Part1/Ch06_InductiveTypes.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；
章节里定义的类型与函数中，只把练习用到的部分（`Weekday`、`MyNat`、`Tree`、`app`、`Point`、`Point3`、
`myGcd`、`log2'` 等）在这里原样重述一遍，使本文件自成一体。
-/

@[expose] public section

namespace Solutions.Ch06

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun
  deriving Repr, DecidableEq

def Weekday.next : Weekday → Weekday
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

def MyNat.add : MyNat → MyNat → MyNat
  | n, .zero => n
  | n, .succ m => .succ (MyNat.add n m)

def MyNat.toNat : MyNat → ℕ
  | .zero => 0
  | .succ n => n.toNat + 1

theorem MyNat.add_succ (n m : MyNat) : n.add m.succ = (n.add m).succ := rfl

inductive Tree (α : Type) where
  | leaf : Tree α
  | node (l : Tree α) (v : α) (r : Tree α) : Tree α

def Tree.mirror {α : Type} : Tree α → Tree α
  | leaf => leaf
  | node l v r => node r.mirror v l.mirror

def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

def app {α : Type} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys

theorem length_app {α : Type} (xs ys : List α) :
    (app xs ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [app]
  | cons x xs ih =>
    simp [app, ih]
    omega

def safeDiv (a b : ℕ) : Option ℕ :=
  match b with
  | 0 => none
  | b + 1 => some (a / (b + 1))

@[ext] structure Point where
  x : ℕ
  y : ℕ

structure Point3 extends base : Point where
  z : ℕ

def myGcd (a b : ℕ) : ℕ :=
  if b = 0 then a else myGcd b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

def log2' (n : ℕ) : ℕ :=
  if n < 2 then 0 else log2' (n / 2) + 1
termination_by n
decreasing_by omega

def rev {α : Type} : List α → List α
  | [] => []
  | x :: xs => app (rev xs) [x]

def sumSq : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumSq n + (n + 1) * (n + 1)

/-- 练习 6.1（★）：一周七天后回到原处。提示：`cases d` 后每个分支 `rfl`。 -/
theorem ex_6_1 (d : Weekday) : d.next.next.next.next.next.next.next = d := by
  cases d <;> rfl

/-- 练习 6.2（★★）：`MyNat` 加法的结合律。提示：对 `c` 归纳，`succ` 分支反复用 `MyNat.add_succ`，最后用 `ih`。 -/
theorem ex_6_2 (a b c : MyNat) : (a.add b).add c = a.add (b.add c) := by
  induction c with
  | zero => rfl
  | succ c ih => rw [MyNat.add_succ, MyNat.add_succ, MyNat.add_succ, ih]

/-- 练习 6.3（★★）：`toNat` 保持加法。提示：对 `b` 归纳，`simp only [MyNat.add, MyNat.toNat]` 展开后用 `omega` 收尾。 -/
theorem ex_6_3 (a b : MyNat) : (a.add b).toNat = a.toNat + b.toNat := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [MyNat.add, MyNat.toNat]
    omega

/-- 练习 6.4（★）：列表拼接的结合律（`app` 见 §6）。 -/
theorem ex_6_4 {α : Type} (xs ys zs : List α) :
    app (app xs ys) zs = app xs (app ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [app, ih]

/-- 练习 6.5（★★）：反转不改变长度。提示：对 `xs` 归纳，用 `length_app` 与 `ih`。 -/
theorem ex_6_5 {α : Type} (xs : List α) : (rev xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rev, length_app, ih]

/-- 练习 6.6（★）：镜像两次得到原树（`Tree.mirror` 见 §3）。提示：对 `t` 归纳，`simp [Tree.mirror, ihl, ihr]`。 -/
theorem ex_6_6 {α : Type} (t : Tree α) : t.mirror.mirror = t := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [Tree.mirror, ihl, ihr]

/-- 练习 6.7（★★）：用 `fun_induction`（§5）证明 `sumTo n ≤ n * n`。提示：两个情形分别用 `decide` 与 `linarith`。 -/
theorem ex_6_7 (n : ℕ) : sumTo n ≤ n * n := by
  fun_induction sumTo n with
  | case1 => decide
  | case2 n ih => linarith

/-- 练习 6.8（★）：复习第 3 章的 `absurd`。除数非零时 `safeDiv` 给出商。提示：对 `b` 分情况，零的情形用 `exact absurd rfl h`。 -/
theorem ex_6_8 (a b : ℕ) (h : b ≠ 0) : safeDiv a b = some (a / b) := by
  cases b with
  | zero => exact absurd rfl h
  | succ b => rfl

/-- 练习 6.9（★★）：复习第 4 章的 `rcases` 与第 5 章的 `subst`。`Point3` 没有 `@[ext]`，要把两个点拆开。
提示：`rcases a with ⟨⟨x, y⟩, z⟩`，`b` 同理，用 `simp only at h₁ h₂ h₃` 化简投影，再 `subst`。 -/
theorem ex_6_9 (a b : Point3) (h₁ : a.x = b.x) (h₂ : a.y = b.y) (h₃ : a.z = b.z) :
    a = b := by
  rcases a with ⟨⟨x, y⟩, z⟩
  rcases b with ⟨⟨x', y'⟩, z'⟩
  simp only at h₁ h₂ h₃
  subst h₁ h₂ h₃
  rfl

/-- 练习 6.10（★★）：复习第 4 章的 `by_cases`。`myGcd 0 b = b`。提示：对 `b = 0` 分情况，再用 `simp [myGcd]`。 -/
theorem ex_6_10 (b : ℕ) : myGcd 0 b = b := by
  by_cases h : b = 0
  · subst h
    simp [myGcd]
  · simp [myGcd, h]

/-- 练习 6.11（★★）：`log2'` 小于 `n`。提示：`revert h` 把假设放回目标（与 `intro` 相反），目标变成
`1 ≤ n → log2' n < n`，这样 `fun_induction log2' n` 的归纳假设也带条件；每个情形先 `intro` 再 `omega`。 -/
theorem ex_6_11 (n : ℕ) (h : 1 ≤ n) : log2' n < n := by
  revert h
  fun_induction log2' n <;> intro h <;> omega

/-- 练习 6.12（★）：复习第 3 章的 `∨` 与项模式。不用策略：用 `fun` 加嵌套模式写出证明项。 -/
theorem ex_6_12 (p q r : Prop) : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
  fun
  | .inl (.inl hp) => .inl hp
  | .inl (.inr hq) => .inr (.inl hq)
  | .inr hr => .inr (.inr hr)

/-- 练习 6.13（★★）：复习第 2 章的 `nlinarith`。平方和公式。提示：归纳，`simp [sumSq]` 展开，再 `nlinarith [ih]`。 -/
theorem ex_6_13 (n : ℕ) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [sumSq]
    nlinarith [ih]

/-- 练习 6.14（★）：复习第 3 章的 `∃`。证明 `∃ k, n = 3 * k` 与 `n % 3 = 0` 等价。
提示：两个方向都用 `omega`；第二个方向要自己给出 `k`。 -/
theorem ex_6_14 (n : ℕ) : (∃ k, n = 3 * k) ↔ n % 3 = 0 :=
  ⟨fun ⟨k, hk⟩ ↦ by omega, fun h ↦ ⟨n / 3, by omega⟩⟩

/-- 练习 6.15（★★）：给 `∃ k, n = 3 * k` 提供可判定性实例（§10）。
提示：`decidable_of_iff (n % 3 = 0)`，需要的等价式是练习 6.14 的 `.symm`。 -/
def ex_6_15 (n : ℕ) : Decidable (∃ k, n = 3 * k) :=
  decidable_of_iff (n % 3 = 0) (ex_6_14 n).symm

end Solutions.Ch06

end
