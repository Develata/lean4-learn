module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.ToExpr
public meta import Qq
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Tactic.Positivity.Basic

/-!
# 第 27 章　答案

`Lean4Learn/Part5/Ch27_Metaprogramming.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同。
练习用到的定义（`sq1`、`double`、`twice`）和 `positivity` 扩展、`dsimproc` 在这里重新给出，使本文件
自成一体；写策略、项精译器、simproc 的练习后面各附一个小测试，测试通过说明函数体可用。
-/

@[expose] public section

namespace Solutions.Ch27

/-- `n * n + 1`。 -/
def sq1 (n : ℕ) : ℕ := n * n + 1

theorem sq1_pos (n : ℕ) : 0 < sq1 n := by unfold sq1; exact Nat.succ_pos _

/-- `2 * n`。 -/
def double (n : ℕ) : ℕ := 2 * n

theorem double_pos (n : ℕ) (h : 0 < n) : 0 < double n := by unfold double; omega

@[to_additive twice]
def sqr {G : Type*} [Mul G] (a : G) : G := a * a

end Solutions.Ch27

end

public meta section

namespace Solutions.Ch27

open Lean Meta Elab Tactic Qq

/-- 把 `double k`（`k` 是字面量）化简成字面量 `2 * k`。 -/
dsimproc reduceDouble (double _) := fun e => do
  let_expr double n := e | return .continue
  let some v ← getNatValue? n | return .continue
  return .done (toExpr (2 * v))

open Mathlib.Meta.Positivity in
/-- `positivity` 扩展：`sq1 a` 总是正的。 -/
@[positivity sq1 _]
def evalSq1 : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with
  | none => throwError "not PartialOrder ℕ"
  | some _ => do
    match u, α, e with
    | 0, ~q(ℕ), ~q(sq1 $a) =>
      assertInstancesCommute
      pure (.positive q(sq1_pos $a))
    | _, _, _ => throwError "not sq1"

/-- 练习 27.1（★）：`fun x₁ … xₙ ↦ b` 开头有多少个 `lam`？不是 `lam` 的返回 0。
提示：对 `Expr` 做模式匹配，`.lam _ _ b _ => …`（第 6 章）。 -/
def ex_27_1 : Expr → Nat := fun e =>
  match e with
  | .lam _ _ b _ => ex_27_1 b + 1
  | _ => 0

/-- 练习 27.2（★）：用 `mkAppM` 造出 `Nat.add_comm a b` 的表达式，使 `inferType` 给出
`a + b = b + a`。 -/
def ex_27_2 (a b : ℕ) : MetaM Expr :=
  mkAppM ``Nat.add_comm #[mkNatLit a, mkNatLit b]

/-- 练习 27.3（★★）：对声明 `declName`，返回其类型开头的 `∀` 约束变量个数，以及结论（去掉全部
`∀`）是否是等式 `Eq`。例如 `Nat.add_comm` 给出 `(2, true)`。提示：`getConstInfo`、
`forallTelescope`、`Expr.isAppOfArity`（`Eq` 有 3 个参数）。 -/
def ex_27_3 (declName : Name) : MetaM (Nat × Bool) := do
  let ci ← getConstInfo declName
  forallTelescope ci.type fun xs body => return (xs.size, body.isAppOfArity ``Eq 3)

/-- 练习 27.4（★）：用 §10 的 `twice` 证明（第 15 章）。提示：`two_nsmul`。 -/
theorem ex_27_4 {G : Type*} [AddMonoid G] (a : G) : twice a = 2 • a := by
  simp [twice, two_nsmul]

/-- 练习 27.5（★）：用本章的 `split_and` 与 `omega` 证明（其他证法也接受）。 -/
theorem ex_27_5 (n : ℕ) (h : 2 ≤ n) : 1 < n ∧ 3 ≤ n + 1 ∧ n ≠ 0 :=
  ⟨by omega, by omega, by omega⟩

/-- 练习 27.6（★）：用 §7 的 `reduceDouble`（即 `simp`）证明。注意嵌套：内层先被化简。 -/
theorem ex_27_6 : double (double 2) + 1 = 9 := by
  simp

/-- 练习 27.7（★★）：写策略 `symm_assumption`：目标是 `a = b`，上下文里有 `h : b = a` 时
用 `h.symm` 关闭目标。提示：`withMainContext`、`getMainTarget`、`Expr.eq?`（把 `a = b` 拆成
`(类型, a, b)`）、`getLCtx`、`isDefEq`、`mkEqSymm`、`closeMainGoal`；找不到时 `throwTacticEx`。 -/
def ex_27_7 : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← getMainTarget).eq?
    | throwTacticEx `symm_assumption goal "the goal is not an equation"
  -- 每个候选只调用一次 `isDefEq`，比较整条反向等式：失败的 `isDefEq` 会撤销自己做的元变量
  -- 赋值，但先后两次调用时，第一次成功的赋值不会因第二次失败而撤销，会挡住后面的正确候选。
  for ldecl in ← getLCtx do
    unless ldecl.isImplementationDetail do
      if (← isDefEq ldecl.type (← mkEq rhs lhs)) then
        closeMainGoal `symm_assumption (← mkEqSymm ldecl.toExpr)
        return
  throwTacticEx `symm_assumption goal "no hypothesis states the symmetric equation"

elab "symm_assumption" : tactic => ex_27_7

example (a b : ℕ) (h : b = a) : a = b := by symm_assumption

-- 目标含元变量 `?w`：`_hbad` 不匹配且不能留下 `?w := x`，`hgood` 随后才能把 `?w` 定成 `z`。
example (x y z w : ℕ) (_hbad : x = y) (hgood : z = w) : ∃ m, w = m := by
  apply Exists.intro
  symm_assumption

/-- 练习 27.8（★★）：写策略 `last_hyp`：用**最后一个**非实现细节的局部假设关闭目标
（类型要定义相等，用默认透明度）。提示：`getLocalHyps`（已去掉实现细节）、`Array.back?`。 -/
def ex_27_8 : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some h := (← getLocalHyps).back?
    | throwTacticEx `last_hyp goal "there are no hypotheses"
  unless (← isDefEq (← inferType h) (← getMainTarget)) do
    throwTacticEx `last_hyp goal m!"the last hypothesis has type {← inferType h}"
  closeMainGoal `last_hyp h

elab "last_hyp" : tactic => ex_27_8

example (p q : Prop) (_hp : p) (hq : q) : q := by last_hyp

/-- 练习 27.9（★）：返回 `a`、`b` 在可约透明度与默认透明度下是否定义相等。 -/
def ex_27_9 (a b : Expr) : MetaM (Bool × Bool) := do
  return (← withReducible (isDefEq a b), ← withDefault (isDefEq a b))

/-- 练习 27.10（★）：写 `sq1 k`（`k` 是字面量）的 `dsimproc` 函数体：化简为字面量 `k * k + 1`。
参考 §7 的 `reduceDouble`。写完后取消注释下一行。 -/
def ex_27_10 : Simp.DSimproc := fun e => do
  let_expr sq1 n := e | return .continue
  let some v ← getNatValue? n | return .continue
  return .done (toExpr (v * v + 1))

dsimproc reduceSq1 (sq1 _) := ex_27_10

example : sq1 3 = 10 := by simp

/-- 练习 27.11（★）：用 Qq 的 `~q` 匹配：`e` 形如 `a + b` 时返回 `b + a`，否则返回 `none`。 -/
def ex_27_11 (e : Q(ℕ)) : MetaM (Option Q(ℕ)) :=
  match e with
  | ~q($a + $b) => return some q($b + $a)
  | _ => return none

/-- 练习 27.12（★★）：返回命名空间 `ns` 下所有常量的名字，按 `Name.quickLt` 排序（第 24 章的
`Array`）。提示：`getEnv`、`env.constants.fold`、`Array.qsort`。 -/
def ex_27_12 (ns : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n _ =>
    if ns.isPrefixOf n then acc.push n else acc
  return names.qsort Name.quickLt

/-- 练习 27.13（★★）：写项精译器 `num_hyps`：返回当前上下文里局部假设的个数（作为 `ℕ` 字面量）。
提示：`getLocalHyps`、`mkNatLit`。 -/
def ex_27_13 : TermElabM Expr := return mkNatLit (← getLocalHyps).size

elab "num_hyps" : term => ex_27_13

example (a b : ℕ) (_h : a = b) : num_hyps = (3 : ℕ) := rfl

/-- 练习 27.14（★）：用 `positivity`（有了 §8 的扩展）证明；也可以先 `unfold sq1` 再 `omega`。 -/
theorem ex_27_14 (n : ℕ) : sq1 n ≠ 0 ∧ 0 < sq1 (n + 1) :=
  ⟨by positivity, by positivity⟩

/-- 练习 27.15（★★★）：写 `double` 的 `positivity` 扩展：参数为正时 `double a` 为正（用
`double_pos`），否则为非负。提示：照 §8 的 `evalSq1`，用 `Mathlib.Meta.Positivity.core` 取得
参数的 `Strictness`（`Mathlib/Tactic/Positivity/Core.lean` 第 60、438 行）；`match pα? with` 之后
用 `some pα` 这个名字，调用 `core zα (some pα) a`，结果的类型才对得上。写完后取消注释下一行。 -/
def ex_27_15 : Mathlib.Meta.Positivity.PositivityExt :=
  { eval := fun {u α} zα pα? e =>
      match pα? with
      | none => throwError "not PartialOrder ℕ"
      | some pα => do
        match u, α, e with
        | 0, ~q(ℕ), ~q(double $a) =>
          assertInstancesCommute
          match ← Mathlib.Meta.Positivity.core zα (some pα) a with
          | .positive pa =>
            assertInstancesCommute
            pure (.positive q(double_pos $a $pa))
          | _ => pure (.nonnegative q(Nat.zero_le (double $a)))
        | _, _, _ => throwError "not double" }

attribute [positivity double _] ex_27_15

example (n : ℕ) (h : 0 < n) : 0 < double n := by positivity

example (n : ℕ) : 0 ≤ double n := by positivity

-- 上面几道不带 `elab` 的练习的检查：失败时抛错，成功则没有输出。
#guard_msgs in
#eval show MetaM Unit from do
  unless ex_27_1 (.lam `x (mkConst ``Nat) (.lam `y (mkConst ``Nat) (mkNatLit 0) .default)
      .default) == 2 do throwError "27.1"
  unless (← ex_27_3 ``Nat.add_comm) == (2, true) do throwError "27.3"
  let some r ← ex_27_11 q(1 + 2) | throwError "27.11: none"
  unless (← isDefEq r q(2 + 1)) do throwError "27.11: wrong"

end Solutions.Ch27

end
