module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Extension
public meta import Lean.PrettyPrinter.Delaborator.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# 第 26 章　答案

`Lean4Learn/Part5/Ch26_Macros.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同。
练习用到的记号、DSL 与宏（`⊞`、`⊠`、`⇄`、`Arith` 与 `[Arith| …]`、`graph%`、`graphOn%`、
`const!`、`const_bad!`、`close_goal`）在这里重新给出，使本文件自成一体。
练习 26.3、26.10、26.12 要在定理之前自己写记号或宏，答案里就在定理上方。
-/

@[expose] public section

namespace Solutions.Ch26

/-! ## 章节里的定义与语法（从章节文件复制） -/

/-- 模 5 加法。 -/
def addMod5 (a b : ℕ) : ℕ := (a + b) % 5

/-- 模 5 乘法。 -/
def mulMod5 (a b : ℕ) : ℕ := (a * b) % 5

/-- 模 5 减法：加上 `b` 的模 5 相反数。 -/
def subMod5 (a b : ℕ) : ℕ := (a + (5 - b % 5)) % 5

infixl:65 " ⊞ " => addMod5
infixl:70 " ⊠ " => mulMod5

/-- 交换序对的两个分量。 -/
def swapPair (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1)

postfix:max "⇄" => swapPair

/-- 一个很小的算术表达式语言。 -/
inductive Arith where
  | num : ℕ → Arith
  | var : String → Arith
  | add : Arith → Arith → Arith
  | mul : Arith → Arith → Arith

namespace Arith

/-- 在环境 `ρ` 下求值。 -/
def eval (ρ : String → ℕ) : Arith → ℕ
  | num n => n
  | var s => ρ s
  | add a b => a.eval ρ + b.eval ρ
  | mul a b => a.eval ρ * b.eval ρ

/-- 交换所有加法与乘法的两个操作数。 -/
def mirror : Arith → Arith
  | num n => num n
  | var s => var s
  | add a b => add b.mirror a.mirror
  | mul a b => mul b.mirror a.mirror

end Arith

declare_syntax_cat arith

syntax num : arith
syntax ident : arith
syntax:60 arith:60 " + " arith:61 : arith
syntax:70 arith:70 " * " arith:71 : arith
syntax "(" arith ")" : arith

syntax:max "[Arith|" arith "]" : term

macro_rules
  | `([Arith| $n:num]) => `(Arith.num $n)
  | `([Arith| $x:ident]) => `(Arith.var $(Lean.quote x.getId.toString))
  | `([Arith| $a + $b]) => `(Arith.add [Arith| $a] [Arith| $b])
  | `([Arith| $a * $b]) => `(Arith.mul [Arith| $a] [Arith| $b])
  | `([Arith| ($a)]) => `([Arith| $a])

/-- 一条边：端点序对。 -/
def edge (u v : ℕ) : ℕ × ℕ := (u, v)

/-- 边表对应的 `Bool` 谓词。 -/
def edgeB (es : List (ℕ × ℕ)) (a b : ℕ) : Bool := es.contains (a, b)

/-- 由边表生成 `Fin n` 上的简单图。 -/
def toGraph (n : ℕ) (es : List (ℕ × ℕ)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b ↦ edgeB es a b = true

instance (n : ℕ) (es : List (ℕ × ℕ)) : DecidableRel (toGraph n es).Adj := fun a b ↦
  inferInstanceAs
    (Decidable ((SimpleGraph.fromRel fun a b : Fin n ↦ edgeB es a b = true).Adj a b))

theorem toGraph_adj (n : ℕ) (es : List (ℕ × ℕ)) (a b : Fin n) :
    (toGraph n es).Adj a b ↔ a ≠ b ∧ (edgeB es a b = true ∨ edgeB es b a = true) := by
  simp [toGraph]

declare_syntax_cat gedge

syntax num " ~~ " num : gedge

syntax:max "graph% " "[" gedge,* "]" : term
syntax:max "graphOn% " num " [" gedge,* "]" : term

/-- 把一条 `u ~~ v` 翻译成 `edge u v`。 -/
meta def expandEdge : Lean.TSyntax `gedge → Lean.MacroM Lean.Term
  | `(gedge| $a:num ~~ $b:num) => `(edge $a $b)
  | stx => Lean.Macro.throwErrorAt stx "graph%: an edge must look like `u ~~ v`"

macro_rules
  | `(graph% [$es,*]) => do
    let pairs ← es.getElems.mapM expandEdge
    `(([$pairs,*] : List (ℕ × ℕ)))

macro_rules
  | `(graphOn% $n [$es,*]) => do
    for e in es.getElems do
      match e with
      | `(gedge| $a:num ~~ $b:num) =>
        for v in [a, b] do
          if v.getNat ≥ n.getNat then
            Lean.Macro.throwErrorAt v
              s!"graphOn%: vertex {v.getNat} is out of range (n = {n.getNat})"
      | _ => Lean.Macro.throwUnsupported
    `(toGraph $n (graph% [$es,*]))

macro "const! " e:term:max : term => `(fun x ↦ $e)

set_option hygiene false in
macro "const_bad! " e:term:max : term => `(fun x ↦ $e)

syntax "close_goal" : tactic

macro_rules | `(tactic| close_goal) => `(tactic| rfl)
macro_rules | `(tactic| close_goal) => `(tactic| omega)
macro_rules | `(tactic| close_goal) => `(tactic| assumption)

/-! ## 练习答案 -/

/-- 练习 26.1（★）：`⊞` 是交换的，也是结合的。提示：`unfold addMod5` 后用 `omega`（第 2 章）。 -/
theorem ex_26_1 (a b c : ℕ) : a ⊞ b = b ⊞ a ∧ (a ⊞ b) ⊞ c = a ⊞ (b ⊞ c) := by
  constructor
  · unfold addMod5
    omega
  · unfold addMod5
    omega

/-- 练习 26.2（★）：读优先级。`⊠` 比 `⊞` 结合得更紧，所以这里的括号可以省略。 -/
theorem ex_26_2 (a b c : ℕ) : a ⊞ b ⊠ c = a ⊞ (b ⊠ c) := rfl

infixl:65 " ⊟ " => subMod5

#guard 3 ⊟ 4 == 4

/-- 练习 26.3（★★）：先在定理之前为 `subMod5` 写 `infixl:65 " ⊟ " => subMod5`，并用
`#guard 3 ⊟ 4 == 4` 检查记号；再证明下面的等式。提示：`unfold subMod5 addMod5` 后用 `omega`。 -/
theorem ex_26_3 (a b : ℕ) : subMod5 (a ⊞ b) b = a % 5 := by
  unfold subMod5 addMod5
  omega

/-- 练习 26.4（★）：`⇄` 是对合。提示：`rfl`，结构 eta（第 6 章）。 -/
theorem ex_26_4 (p : ℕ × ℕ) : p⇄⇄ = p := rfl

/-- 练习 26.5（★）：在常值环境下用 `decide` 计算一个 DSL 表达式。 -/
theorem ex_26_5 : Arith.eval (fun _ ↦ 2) [Arith| x * (y + 3)] = 10 := by decide

/-- 练习 26.6（★★）：`mirror` 不改变求值结果。提示：对 `a` 做结构归纳（第 6 章），
再用 `Nat.add_comm`、`Nat.mul_comm`。 -/
theorem ex_26_6 (ρ : String → ℕ) (a : Arith) : a.mirror.eval ρ = a.eval ρ := by
  induction a with
  | num _ => rfl
  | var _ => rfl
  | add a b iha ihb =>
    simp only [Arith.mirror, Arith.eval, iha, ihb]
    exact Nat.add_comm _ _
  | mul a b iha ihb =>
    simp only [Arith.mirror, Arith.eval, iha, ihb]
    exact Nat.mul_comm _ _

/-- 练习 26.7（★★）：`mirror` 是对合。提示：结构归纳加 `simp only [Arith.mirror, …]`。 -/
theorem ex_26_7 (a : Arith) : a.mirror.mirror = a := by
  induction a with
  | num _ => rfl
  | var _ => rfl
  | add a b iha ihb => simp only [Arith.mirror, iha, ihb]
  | mul a b iha ihb => simp only [Arith.mirror, iha, ihb]

/-- 练习 26.8（★★）：路径图上的邻接。提示：`decide`（第 25 章），把合取拆开或直接整个 `decide`。 -/
theorem ex_26_8 :
    (graphOn% 4 [0 ~~ 1, 1 ~~ 2, 2 ~~ 3]).Adj 1 0 ∧
      ¬ (graphOn% 4 [0 ~~ 1, 1 ~~ 2, 2 ~~ 3]).Adj 0 3 := by decide

/-- 练习 26.9（★★）：`toGraph` 没有自环。提示：`toGraph_adj`（§10）或 `SimpleGraph.irrefl`。 -/
theorem ex_26_9 (n : ℕ) (es : List (ℕ × ℕ)) (a : Fin n) :
    ¬ (toGraph n es).Adj a a :=
  fun h ↦ ((toGraph_adj n es a a).1 h).1 rfl

macro_rules | `(tactic| close_goal) => `(tactic| simp)

/-- 练习 26.10（★★）：`close_goal` 目前只有 `rfl`、`omega`、`assumption` 三条规则，
解不了下面的目标（§8）。在定理之前自己再加一条 `macro_rules`（用 `simp`），然后用 `close_goal`
证明它。 -/
theorem ex_26_10 (xs : List ℕ) : (xs ++ []).length = xs.length := by close_goal

/-- 练习 26.11（★）：卫生性。§6 的 `const_bad!` 关掉了卫生性，`const!` 没有。判断两个宏
对 `(…) 10` 的结果，然后用 `rfl` 证明。 -/
theorem ex_26_11 (x : ℕ) : (const_bad! x) 10 = 10 ∧ (const! x) 10 = x := ⟨rfl, rfl⟩

macro "simp_with " t:term:max : tactic => `(tactic| simp [$t:term])

/-- 练习 26.12（★★）：在定理之前写一个策略宏 `simp_with t`，展开成 `simp [t]`（参数 `t` 的
语法范畴是 `term:max`，引用写 `` `(tactic| simp [$t:term]) ``），然后用它证明下面的等式。 -/
theorem ex_26_12 (xs ys : List ℕ) : (xs ++ ys).length = ys.length + xs.length := by
  simp_with Nat.add_comm

end Solutions.Ch26

end
