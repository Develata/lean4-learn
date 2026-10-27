module

public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Defs

/-!
# 第 28 章　答案

`Lean4Learn/Part5/Ch28_Internals.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同。
练习用到的定义（`kk`、`Lst`、`Tag` 及其实例、探针 `pD`、`pX`）在这里重新给出，使本文件自成一体；
练习 28.9 与 28.11 后面各附一条检查命令，用 `#guard_msgs` 固定输出。
-/

@[expose] public section

namespace Solutions.Ch28

def kk : ℕ := 3

structure Lst where
  hd : ℕ
  tl : Option Lst

class Tag (α : Type) where
  name : String

instance (priority := low) : Tag ℕ := ⟨"low"⟩
instance : Tag ℕ := ⟨"mid"⟩
instance (priority := high) : Tag ℕ := ⟨"high1"⟩
instance (priority := high) : Tag ℕ := ⟨"high2"⟩
instance : Tag ℕ := ⟨"mid2"⟩

/-- 练习 28.1（★）：依值对 `p` 的第二个分量是 `Fin (p.1 + 1)` 的元素，所以它的值不超过第一个分量（§1）。
提示：`p.2.isLt`、`omega`。 -/
theorem ex_28_1 (p : (n : ℕ) × Fin (n + 1)) : p.2.val ≤ p.1 := by
  have := p.2.isLt
  omega

/-- 练习 28.2（★）：抬升到 `Type 1` 不丢信息（§2）。提示：`ULift.down`、`congrArg`。 -/
theorem ex_28_2 (α : Type) (a b : α) (h : ULift.up.{1} a = ULift.up b) : a = b := congrArg ULift.down h

/-- 练习 28.3（★★）：`∀ α : Type 3, Nonempty α` 是命题（非直谓性，§2），而且是假命题。
提示：取一个空类型，注意它要住在 `Type 3`（`PEmpty.{4}`），消去用 `PEmpty.elim`。 -/
theorem ex_28_3 : ¬ ∀ α : Type 3, Nonempty α := by
  intro h
  obtain ⟨x⟩ := h PEmpty.{4}
  exact x.elim

/-- 练习 28.4（★）：正整数的子类型里，值相等就相等（证明无关性，§3）。 -/
theorem ex_28_4 (a b : {n : ℕ // 0 < n}) (h : a.1 = b.1) : a = b := Subtype.ext h

/-- 练习 28.5（★★）：对任意谓词 `p`，`∃ n, p n` 的见证不能直接取出（§3），但「存在一个选择函数」是个
`Prop`，可以证明。提示：`Classical.choose`、`Classical.choose_spec`。 -/
theorem ex_28_5 (p : ℕ → Prop) : ∃ f : (∃ n, p n) → ℕ, ∀ h, p (f h) := ⟨Classical.choose, Classical.choose_spec⟩

/-- 练习 28.6（★★）：用 `Nat.rec` 直接定义的「加 2」递推，在每个 `n` 上都等于 `2 * n`（ι 规约，§4）。
提示：对 `n` 归纳；归纳步先用 `show` 把 `Nat.rec` 在 `k + 1` 上的值写成 `… + 2`，再 `omega`。 -/
theorem ex_28_6 (n : ℕ) :
    (Nat.rec (motive := fun _ ↦ ℕ) 0 (fun _ ih ↦ ih + 2) n : ℕ) = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show (Nat.rec (motive := fun _ ↦ ℕ) 0 (fun _ ih ↦ ih + 2) k : ℕ) + 2 = 2 * (k + 1)
    omega

/-- 练习 28.7（★）：递归结构体没有 eta（§4），但对任何函数 `f`，`f` 作用在重新拼好的 `Lst.mk x.hd x.tl`
上仍等于 `f x`。提示：先分情况。 -/
theorem ex_28_7 (f : Lst → ℕ) (x : Lst) : f (Lst.mk x.hd x.tl) = f x := by
  cases x
  rfl

/-- 练习 28.8（★）：用 `Quot.sound` 证明模 3 余数相同的任意两个数在商里相等（§5）。 -/
theorem ex_28_8 (a b : ℕ) (h : a % 3 = b % 3) :
    Quot.mk (fun a b : ℕ ↦ a % 3 = b % 3) a = Quot.mk _ b := Quot.sound h

/-- 练习 28.9（★）：两个二元函数逐点相等则相等（函数外延性，§6）。证明之后运行
`#print axioms ex_28_9`，对照 §6 说明为什么只有一条公理（答案文件里有这条命令）。 -/
theorem ex_28_9 (f g : ℕ → ℕ → ℕ) (h : ∀ a b, f a b = g a b) : f = g := funext fun a ↦ funext fun b ↦ h a b

/-- info: 'Solutions.Ch28.ex_28_9' depends on axioms: [Quot.sound] -/
#guard_msgs in #print axioms ex_28_9

/-- 练习 28.10（★）：§7 的 `kk` 是 `def`。`simp only [h]` 用不上 `h : P kk`，但 `exact` 在默认透明度下
可以。选对工具完成证明。 -/
theorem ex_28_10 (P : ℕ → Prop) (h : P kk) : P 3 := h

def pD : Bool := true
@[irreducible] def pX : Bool := true

section MetaExercise
public meta section

open Lean Meta

/-- 练习 28.11（★★）：对常量 `c`，依次在 `none`、`reducible`、`instances`、`implicit`、`default`、
`all` 六种透明度下对 `mkConst c` 做 `whnf`，返回「结果与 `mkConst c` 不同」（即被展开了）的布尔值
列表。提示：`withTransparency`、`whnf`；`Expr` 有 `!=`。用 §8 的探针 `pD`、`pX` 检验。 -/
def ex_28_11 (c : Name) : MetaM (List Bool) := do
  let mut out : List Bool := []
  for m in [TransparencyMode.none, .reducible, .instances, .implicit, .default, .all] do
    let r ← withTransparency m (whnf (mkConst c))
    out := out ++ [r != mkConst c]
  return out

end
end MetaExercise

/--
info: pD: [false, false, false, false, true, true]
---
info: pX: [false, false, false, false, false, true]
-/
#guard_msgs in
#eval show Lean.MetaM Unit from do
  Lean.logInfo m!"pD: {← ex_28_11 ``pD}"
  Lean.logInfo m!"pX: {← ex_28_11 ``pX}"

/-- 练习 28.12（★）：`Nat.log2` 不在加速表里（§10），普通 `decide` 在 700 位上撞上递归深度。
换一个策略。 -/
theorem ex_28_12 : Nat.log2 (Nat.shiftLeft 1 700) = 700 := by decide +kernel

/-- 练习 28.13（★★）：`Equiv` 的函数形式展开成字段 `toFun`（§13）；利用这一点和 `Equiv` 的
引理证明：先走 `e`、再走 `e.symm` 回到原点。 -/
theorem ex_28_13 (e : ℕ ≃ ℤ) (n : ℕ) : (e.trans e.symm) n = n := by simp

/-- 练习 28.14（★★★）：§3 的直观原因，写成定理：没有函数能在 `True ∨ True` 上区分 `Or.inl` 与 `Or.inr`
给出的两个证明。提示：证明无关性让 `f (Or.inl trivial) = f (Or.inr trivial)` 成立，且是 `rfl`。 -/
theorem ex_28_14 :
    ¬ ∃ f : (True ∨ True) → Bool, f (Or.inl trivial) = true ∧ f (Or.inr trivial) = false := by
  rintro ⟨f, h1, h2⟩
  have h : f (Or.inl trivial) = f (Or.inr trivial) := rfl
  exact absurd (h1.symm.trans (h.trans h2)) (by decide)

/-- 练习 28.15（★★）：先不运行，按 §12 的规则（优先级，同优先级后声明的先试）预测 `Tag.name ℕ` 是哪个
字符串，再验证下面的陈述；然后设想删掉 `"high2"` 那个实例，预测新的值。 -/
theorem ex_28_15 : Tag.name ℕ = "high2" := rfl

end Solutions.Ch28

end
