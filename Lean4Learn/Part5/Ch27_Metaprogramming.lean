module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.LitValues
public meta import Lean.Meta.Tactic.Apply
public meta import Lean.Meta.Tactic.Intro
public meta import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.PrettyPrinter.Delaborator.Basic
public meta import Lean.ToExpr
public meta import Qq
public import Aesop
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Use

/-!
# 第 27 章　元编程：Expr、MetaM 与策略编写

前一章（第 26 章）用 `notation`、`syntax`、`macro` 改写了**语法**；本章往下一层，直接操作
**表达式**。读完后你能：读懂 Lean 内部表示项的数据结构 `Expr`；在 `MetaM` 里推断类型、
规约、判定定义相等；写自己的项、命令和策略的 elaborator（精译器；另译繁饰器）；写一个
simproc（简化过程）、一个 `positivity` 扩展和一个 pretty printing（美观打印）规则；并且知道 Mathlib 里的策略文件
是怎样组织的。

## 学习目标
- 认识 `Expr` 的十二个构造子，会用 `mkConst`、`mkApp`、`mkNatLit`、`toExpr` 构造表达式（§1）；
- 在 `MetaM` 里使用 `inferType`、`whnf`、`isDefEq`、`mkAppM`、`forallTelescope`、
  `instantiateMVars`，并理解 transparency（透明度）的作用（§2）；
- 写项精译器 `elab … : term`（可读期望类型）和命令精译器 `elab … : command`（§3）；
- 写策略：`getMainGoal`、`withMainContext`、`closeMainGoal`、`liftMetaTactic`、`evalTactic`，
  并正确报告错误（§4、§5）；
- 用 Qq 写带类型的表达式（§6），写 `simproc`（§7）、`positivity` 扩展与其他扩展属性（§8）、
  `@[app_delab]`（§9），知道 `@[to_additive]` 在做什么（§10）；
- 读 Mathlib 的 `Use.lean` 与 `ByContra.lean`（§11），并把 §4 的 `split_and` 扩成一个带错误报告和
  测试的完整策略 `split_all`（§12）。

## 前置知识
第 24 章的 monad（单子）与 `do` 记号（`MetaM` 就是叠起来的单子），第 6 章的模式匹配；
第 26 章的 `syntax`、`macro`、quotation（引用）与 antiquotation（反引用）、hygiene（卫生性）、
`meta` 阶段与 `@[app_unexpander]`（本章只回顾要点）；第 4、5 章的策略与 `simp`；
第 10 章的 `positivity`、`aesop`；第 13 章的 `set_option` 与linter（代码检查器）；
第 15 章的 `@[to_additive]`；第 25 章的 simproc 初识。内核、`whnf` 与透明度的机制留给第 28 章，
本章只讲怎样用。
-/

/-!
## 0. 文件头与「两个阶段」

文件头与前面各章不同，原因见第 26 章 §1：宏、精译器、策略、simproc、美观打印器是在**编译期**
（meta 阶段）运行的程序，必须标 `meta`；`public meta section` 里的 `def`、`syntax`、`macro`、
`elab` 自动按 `meta` 处理，Mathlib 的策略文件几乎都这样写。阶段限制只管**可执行代码里的引用**：
`meta` 函数的函数体不能调用普通函数（下文 `callsPlain`；导入的普通定义要靠 `meta import` 补标，
所以本章的 import 写成 `public meta import`），只能提到它们的名字（如 ``mkConst ``box``）；
反过来，普通 `def` 也不能调用 `meta` 函数（下面的 `useMeta`）。证明不受限制：下面的 `example`
用 `rfl` 和 `simp` 展开了 `meta` 函数 `mdouble`；导出的定理能否展开某个定义，取决于它是否暴露
（`@[expose]`，见第 28 章），是另一个问题。`meta` 标记不能撤销，两边都可能用到的定义应写成普通
定义（`Lean/Parser/Command.lean` 中 `meta` 修饰符的文档注释），所以本章演示用的定义除 `mdouble`
外都是普通定义，集中放在下面的普通区段里（注释标出用到它的节）。
-/

@[expose] public section

namespace Lean4Learn.Ch27

def five : ℕ := 5                          -- §2：def 与 abbrev 的透明度
abbrev five' : ℕ := 5                      -- §2
def Same (a b : ℕ) : Prop := a = b         -- §4：`my_assumption` 的试验品
abbrev Same' (a b : ℕ) : Prop := a = b     -- §4
abbrev Both (p q : Prop) : Prop := p ∧ q   -- §4：`split_and` 要看穿的包装
def sq1 (n : ℕ) : ℕ := n * n + 1           -- §8：`positivity` 扩展要识别的函数
theorem sq1_pos (n : ℕ) : 0 < sq1 n := by unfold sq1; exact Nat.succ_pos _
def double (n : ℕ) : ℕ := 2 * n            -- §7：`dsimproc`；练习 27.6、27.15
theorem double_pos (n : ℕ) (h : 0 < n) : 0 < double n := by unfold double; omega
def box (n : ℕ) : ℕ := n                   -- §7：`simproc`；§9：美观打印
theorem box_eq (n : ℕ) : box n = n := rfl  -- §7
def plainHelper (n : ℕ) : ℕ := n + 1       -- §0：一个普通函数
meta def mdouble (n : ℕ) : ℕ := 2 * n      -- §0：一个 `meta` 函数

example : mdouble 3 = 6 := rfl
example : mdouble 3 = 6 := by simp [mdouble]

/-- error: Invalid definition `useMeta`, may not access declaration
`mdouble` marked as `meta` -/
#guard_msgs in
def useMeta : ℕ := mdouble 2

@[to_additive twice]                       -- §10、练习 27.4
def sqr {G : Type*} [Mul G] (a : G) : G := a * a

@[to_additive twice_zero]
theorem sqr_one {G : Type*} [MulOneClass G] : sqr (1 : G) = 1 := by simp [sqr]

end Lean4Learn.Ch27

end

public meta section

namespace Lean4Learn.Ch27

open Lean Meta Elab Tactic

-- §0：这个区段里的 `def` 都是 `meta`，调用普通函数会报错。
/-- error: Invalid `meta` definition `callsPlain`, `plainHelper` not marked `meta` -/
#guard_msgs in
def callsPlain : ℕ := plainHelper 2

/-!
## 1. 表达式 `Expr`

`Expr` 是 Lean 内部表示项和类型的归纳类型，每个值就是一棵语法树。它有十二个构造子：

| 构造子 | 含义 | 例 |
|---|---|---|
| `bvar i` | 被绑定变量，de Bruijn 下标（从内向外数） | `fun x ↦ x` 里的 `x` 是 `bvar 0` |
| `fvar id` | 上下文里的自由变量 | 证明状态里的假设 `h` |
| `mvar id` | metavariable（元变量）`?m` | 尚未确定的参数、尚未证明的目标 |
| `sort u` | 宇宙 `Sort u` | `Prop`、`Type` |
| `const n us` | 全局常量及其宇宙实参 | `Nat.add` |
| `app f a` | 单参数应用 | `f a b` 是 `app (app f a) b` |
| `lam n t b bi` | `fun (n : t) ↦ b` | 变量名只用于显示 |
| `forallE n t b bi` | `(n : t) → b`，即 Π 类型与 `∀` | 蕴含 `p → q` 是不用变量的 `forallE` |
| `letE n t v b nd` | `let n : t := v; b` | |
| `lit l` | 自然数或字符串的原始字面量 | `Literal.natVal 3` |
| `mdata d e` | 带元数据的表达式，内核检查时忽略元数据 | |
| `proj s i e` | 结构体的第 `i` 个投影 | |

本章的实验都写成 `#eval show MetaM Unit from do …`：`MetaM` 是 §2 的主角，`logInfo` 把值作为
消息显示出来，`m!"…"` 构造带表达式的消息（§5）。下面的 `sexp` 把 `Expr` 打印成 S 表达式，
只细看本章用到的五个构造子，其余交给默认的 `toString`：应用被摊平成 `(f a b …)`
（`getAppFn`、`getAppArgs`），`eraseMacroScopes` 去掉卫生性附加的后缀（第 26 章 §6）。
它写成 `partial`，省去终止性证明。
-/

/-- 把 `Expr` 打印成 S 表达式。 -/
partial def sexp : Expr → String
  | .bvar i => s!"#{i}"
  | .const n _ => n.toString
  | e@(.app ..) => "(" ++ " ".intercalate ((e.getAppFn :: e.getAppArgs.toList).map sexp) ++ ")"
  | .lam n t b _ => s!"(fun {n.eraseMacroScopes} : {sexp t} => {sexp b})"
  | .lit (.natVal k) => toString k
  | e => toString e

/-!
手工构造表达式用 `mkConst`（常量，需要给出宇宙实参列表）、`mkApp`/`mkApp2`/…（应用）、
`mkNatLit`（自然数字面量）。**两个字面量要分清**：`mkRawNatLit 3` 是裸的 `lit (natVal 3)`，
`mkNatLit 3` 是我们在源文件里写 `3 : ℕ` 时真正得到的 `OfNat.ofNat ℕ 3 _`。
-/

/--
info: (Nat.add (OfNat.ofNat Nat 1 (instOfNatNat 1)) 2)
---
info: Nat.add 1 2
---
info: 3 与 3
---
info: (OfNat.ofNat Nat 3 (instOfNatNat 3))
---
info: 3
-/
#guard_msgs in
#eval show MetaM Unit from do
  let e := mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkRawNatLit 2)
  logInfo (sexp e)
  logInfo m!"{e}"
  logInfo m!"{mkNatLit 3} 与 {mkRawNatLit 3}"
  logInfo (sexp (mkNatLit 3))
  logInfo (sexp (mkRawNatLit 3))

/-!
想把 Lean 的**值**变成 `Expr`，用 `ToExpr` 类的 `toExpr`（`ℕ`、`List` 等都有实例）。不要把它和
`quote` 混起来：`quote` 把值变成**语法** `Syntax`，`toExpr` 把值变成**表达式** `Expr`。
-/

/--
info: [1, 2]
---
info: true
---
info: 5
-/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo m!"{toExpr [1, 2]}"
  logInfo m!"{toExpr (3 : ℕ) == mkNatLit 3}"
  logInfo m!"{(quote (5 : ℕ) : Term)}"

/-!
最常见的来源是**精译**：把你写的源文件语法交给精译器，得到的 `Expr` 才是 Lean 真正处理的
对象。下面精译 `fun x : ℕ ↦ x + 1`，看到 `x` 在函数体里是 `#0`，`+` 展开成带实例参数的
`HAdd.hAdd`：
-/

/--
info: (fun x : Nat => (HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) #0 (OfNat.ofNat Nat 1
(instOfNatNat 1))))
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let e ← Term.elabTermAndSynthesize (← `(fun x : ℕ ↦ x + 1)) none
  logInfo (sexp (← instantiateMVars e))

/-!
## 2. `MetaM`：推断、规约与合一

`MetaM` 是元编程里最基本的单子，它在 `CoreM`（环境、选项、消息）之上又带着**上下文**与
**元变量上下文**。

| 函数 | 作用 |
|---|---|
| `inferType e` | 推断 `e` 的类型 |
| `whnf e` | 规约到 weak head normal form（弱头正规形，whnf） |
| `isDefEq a b` | 判定定义相等，**可能给元变量赋值** |
| `mkAppM n args` | 以常量 `n` 为头造应用，自动补隐式参数与实例参数，并检查类型 |
| `forallTelescope ty k` | 把 `∀ x y, b` 的约束变量换成新自由变量，在 `k` 里使用 |
| `instantiateMVars e` | 把已赋值的元变量替换成它们的值 |
-/

/--
info: inferType: ℕ
---
info: whnf: 3
---
info: mkAppM: 2 + 2，类型 ℕ
---
info: isDefEq: true
-/
#guard_msgs in
#eval show MetaM Unit from do
  let e := mkApp2 (mkConst ``Nat.add) (mkNatLit 1) (mkNatLit 2)
  logInfo m!"inferType: {← inferType e}"
  logInfo m!"whnf: {← whnf e}"
  let four ← mkAppM ``HAdd.hAdd #[mkNatLit 2, mkNatLit 2]
  logInfo m!"mkAppM: {four}，类型 {← inferType four}"
  logInfo m!"isDefEq: {← isDefEq four (mkNatLit 4)}"

/-!
**元变量与 `isDefEq`。** `mkFreshExprMVar` 造一个新的元变量；`isDefEq` 在判定相等的同时可以
给它赋值，这就是 unification（合一）。赋值之后元变量表达式本身没变，要用 `instantiateMVars`
把值代入：
-/

/--
info: 赋值前：false
---
info: isDefEq：true
---
info: 赋值后：true
---
info: instantiateMVars：3 + 1
-/
#guard_msgs in
#eval show MetaM Unit from do
  let m ← mkFreshExprMVar (some (mkConst ``Nat))
  let e ← mkAppM ``HAdd.hAdd #[m, mkNatLit 1]
  logInfo m!"赋值前：{← m.mvarId!.isAssigned}"
  logInfo m!"isDefEq：{← isDefEq e (mkNatLit 4)}"
  logInfo m!"赋值后：{← m.mvarId!.isAssigned}"
  logInfo m!"instantiateMVars：{← instantiateMVars e}"

/-!
**`forallTelescope`** 是读定理陈述的标准办法。`Nat.add_comm : ∀ (n m : ℕ), n + m = m + n`：
-/

/--
info: 2 个约束变量，结论 n + m = m + n
---
info: n : ℕ
---
info: m : ℕ
-/
#guard_msgs in
#eval show MetaM Unit from do
  let ci ← getConstInfo ``Nat.add_comm
  forallTelescope ci.type fun xs body => do
    logInfo m!"{xs.size} 个约束变量，结论 {body}"
    for x in xs do
      logInfo m!"{x} : {← inferType x}"

/-!
**透明度。** `isDefEq` 与 `whnf` 能展开多少定义取决于当前透明度：默认的
`default` 展开一般的 `def`，更弱的 `reducible` 只展开带 `@[reducible]` 的（`abbrev` 就是）。
`withReducible`、`withDefault`、`withTransparency` 切换等级；`simp` 在 discrimination tree
（判别树，按表达式头部形状索引的查找表）里查找引理时和实例合成时，通常都在更弱的等级上工作
（`TransparencyMode` 的文档注释），六级透明度与机制见第 28 章。`five` 是 `def`，`five'` 是 `abbrev`：
-/

/--
info: reducible, def：false
---
info: default, def：true
---
info: reducible, abbrev：true
---
info: whnf reducible：five
---
info: whnf default：5
-/
#guard_msgs in
#eval show MetaM Unit from do
  let five := mkConst ``five
  let five' := mkConst ``five'
  logInfo m!"reducible, def：{← withReducible (isDefEq five (mkNatLit 5))}"
  logInfo m!"default, def：{← withDefault (isDefEq five (mkNatLit 5))}"
  logInfo m!"reducible, abbrev：{← withReducible (isDefEq five' (mkNatLit 5))}"
  logInfo m!"whnf reducible：{← withReducible (whnf five)}"
  logInfo m!"whnf default：{← withTransparency .default (whnf five)}"

/-!
## 3. 项精译器与命令精译器

**项精译器**的类型是 `Syntax → Option Expr → TermElabM Expr`，第二个参数是**期望类型**。
`elab "k" : term <= ty => …` 一次完成两件事：声明语法 `k`，并注册一个精译函数，`ty` 就是期望类型
（一个 `Expr`）。下面的 `anything!` 在局部假设里找一个类型与期望类型定义相等的，找到就返回它；
从最后引入的假设开始找：
-/

/-- 返回类型与期望类型匹配的最近一个局部假设。 -/
elab "anything!" : term <= ty => do
  let hyps ← getLocalHyps
  for h in hyps.reverse do
    if (← isDefEq (← inferType h) ty) then return h
  throwError m!"No assumption in {hyps} has type {ty}"

/-- info: 2 -/
#guard_msgs in
#eval (fun (_a b : ℕ) ↦ (anything! : ℕ)) 1 2

/-- error: No assumption in [n] has type String -/
#guard_msgs in
example (n : ℕ) : String := anything!

/-!
`throwError` 抛出一个错误，错误位置默认是正在精译的那段语法。

**命令精译器**的类型是 `Syntax → CommandElabM Unit`。`CommandElabM` **不是** `MetaM` 的扩展，
它不带元变量上下文；要用 `MetaM` 的功能，包一层 `liftTermElabM`。`#infer t` 精译 `t` 并报告
它的类型：
-/

/-- `#infer t` 精译项 `t`，报告 `t : 类型`。 -/
elab "#infer " t:term : command => Command.liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  logInfo m!"{e} : {← inferType e}"

/-- info: 1 + 2 : ℕ -/
#guard_msgs in
#infer 1 + 2

/-!
## 4. `TacticM` 与策略

`TacticM` 叠在 `TermElabM` 上，多了**目标列表**。策略的基本动作：

| 函数 | 作用 |
|---|---|
| `getMainGoal` / `getGoals` / `setGoals` | 取主目标 / 取全部目标 / 设置目标列表 |
| `withMainContext x` | 在主目标的上下文里运行 `x`；读假设、做 `isDefEq`、打印含自由变量的表达式前必须先进入 |
| `getMainTarget` | 主目标的类型（已实例化） |
| `closeMainGoal tac e` | 用 `e` 关闭主目标并把它从目标列表去掉；**不检查 `e` 的类型**（常见错误 2） |
| `MVarId.assign e` | 给目标（一个元变量）赋值 |
| `replaceMainGoal gs` | 用 `gs` 替换主目标 |
| `liftMetaTactic f` | 把 `MVarId → MetaM (List MVarId)` 升格成策略，产生的目标替换主目标 |
| `evalTactic stx` | 执行一段策略语法 |

第一个策略 `my_assumption`：在局部假设里找类型与目标**在 `reducible` 透明度下**定义相等的，
用它关闭目标。内置的 `assumption` 在默认透明度下比较，所以会展开 `def`；这里故意用
`withReducible`，这样 `Same a b`（`def`）与 `a = b` 不被认为相同，而 `Same' a b`（`abbrev`）被认为
相同。
-/

/-- 用类型在可约透明度下与目标定义相等的局部假设关闭目标。 -/
elab "my_assumption" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  for ldecl in ← getLCtx do
    unless ldecl.isImplementationDetail do
      if (← withReducible (isDefEq ldecl.type target)) then
        closeMainGoal `my_assumption ldecl.toExpr
        return
  throwTacticEx `my_assumption goal "no hypothesis matches the goal up to reducible defeq"

example (p q : Prop) (_hp : p) (hq : q) : q := by
  my_assumption  -- ⊢ q 被 `hq` 关闭，目标列表变空

example (a b : ℕ) (h : a = b) : Same' a b := by my_assumption

example (a b : ℕ) (h : a = b) : Same a b := by assumption

/--
error: Tactic `my_assumption` failed: no hypothesis matches the goal up to reducible defeq

a b : ℕ
h : a = b
⊢ Same a b
-/
#guard_msgs in
example (a b : ℕ) (h : a = b) : Same a b := by my_assumption

/-!
最后一个例子失败，而内置的 `assumption` 成功（上一个例子）：这就是透明度的差别。失败时
`throwTacticEx` 给出的信息包含策略名、我们写的说明和当时的目标。

**案例：`split_and`。** 第二个策略把形如 `p ∧ q ∧ r` 的目标反复拆成最简单的子目标。算法放进
一个 `MetaM` 函数（递归，所以 `partial`），策略本身只负责用 `liftMetaTactic` 接上去。
`MVarId.apply` 对目标用一个引理，返回新产生的目标；`whnfR` 在 `reducible` 透明度下规约，
使得 `abbrev` 包装的合取也能被识别。
-/

/-- 把目标上的 `∧` 反复用 `And.intro` 拆开，返回剩下的目标。 -/
partial def splitAnd (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let target ← whnfR (← g.getType)
  if target.isAppOfArity ``And 2 then
    let gs ← g.apply (mkConst ``And.intro)
    return (← gs.mapM splitAnd).flatten
  else
    return [g]

/-- `split_and`：把 `∧` 目标拆成不含 `∧` 的目标。 -/
elab "split_and" : tactic => liftMetaTactic splitAnd

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  split_and
  -- 拆之前是 ⊢ p ∧ q ∧ r；现在三个目标：⊢ p，⊢ q，⊢ r
  · exact hp
  · exact hq
  · exact hr

example (p q : Prop) (hp : p) (hq : q) : Both p q := by
  split_and
  · exact hp
  · exact hq

/-!
## 5. 报告信息与错误

| 函数 | 效果 |
|---|---|
| `logInfo m` / `logWarning m` / `logError m` | 记录一条消息，**继续**运行 |
| `throwError m` | 抛异常，中止当前策略或精译 |
| `throwTacticEx name goal msg` | 抛出带策略名和目标的标准策略错误 |
| `try … catch e => …` | 捕获异常；`e.toMessageData` 取出消息 |

消息是 `MessageData`，用 `m!"…{e}…"` 构造，花括号里的 `Expr` 会按当前上下文美观打印。
下面的 `try_report` 用 `evalTactic` 执行传进来的策略，失败时只给警告。`contradiction` 在这里失败后，代码检查器
`linter.unusedTactic` 会再警告「这行策略没起作用」，我们只想捕获自己的警告，所以先关掉它：
-/

/-- 执行策略 `t`；失败时只给警告并保持目标不变。 -/
elab "try_report " t:tactic : tactic => do
  try evalTactic t
  catch e => logWarning m!"失败了：{e.toMessageData}"

set_option linter.unusedTactic false in
/--
warning: 失败了：Tactic `contradiction` failed

⊢ 1 = 2 ∨ True
-/
#guard_msgs in
example : 1 = 2 ∨ True := by
  try_report contradiction
  right
  trivial

/-!
## 6. Qq：带类型的表达式

`Q(α)` 与 `q(e)` 来自 Qq 包。`Q(ℕ)` 在运行时就是 `Expr`，但类型检查器知道它「是一个 `ℕ` 的表达式」，
于是表达式拼错类型会在**写策略时**而不是运行时报错。`$a` 把一个 `Q(…)` 值嵌进去。
-/

open Qq

/-- `a + b = b + a` 的证明，类型由 Qq 检查。 -/
def addCommQ (a b : Q(ℕ)) : Q($a + $b = $b + $a) := q(Nat.add_comm $a $b)

/-- info: Nat.add_comm 1 2 : 1 + 2 = 2 + 1 -/
#guard_msgs in
#eval show MetaM Unit from do
  let p := addCommQ q(1) q(2)
  logInfo m!"{p} : {← inferType p}"

/--
error: Type mismatch
  Nat.mul_comm «$a» «$b»
has type
  «$a» * «$b» = «$b» * «$a»
but is expected to have type
  «$a» + «$b» = «$b» + «$a»
-/
#guard_msgs in
example (a b : Q(ℕ)) : Q($a + $b = $b + $a) := q(Nat.mul_comm $a $b)

/-!
`~q(…)` 是反过来的用法：对 `Expr` 做模式匹配，同时把子表达式绑定成带类型的变量。
匹配是在**定义相等**意义下进行的：模式 `$n + 1` 与自然数字面量 `7` 合一，得到 `n := 6`；
而 `0` 写不成 `?n + 1`，匹配失败。
-/

/-- 若 `e` 与 `n + 1` 合一则返回 `n`。 -/
def predQ? (e : Q(ℕ)) : MetaM (Option Q(ℕ)) := do
  match e with
  | ~q($n + 1) => return some n
  | _ => return none

/--
info: some (5)
---
info: some (6)
---
info: none
-/
#guard_msgs in
#eval show MetaM Unit from do
  logInfo m!"{← predQ? q(5 + 1)}"
  logInfo m!"{← predQ? q(7)}"
  logInfo m!"{← predQ? q(0)}"

/-!
## 7. `simproc`

simproc（简化过程）是挂到 `simp` 上的 `Expr` 变换：`Simproc := Expr → SimpM Step`。`Step` 有三种：
`.done r`（结果就是 `r`，不再继续）、`.visit r`（用 `r` 重新化简）、`.continue`（我不管，交给别的
规则）；`r` 是 `Simp.Result`，字段 `expr` 是新表达式，`proof?` 是 `e = expr` 的证明（`none` 表示
`rfl`）。`dsimproc` 是结果与原式**定义相等**的版本，类型 `Simp.DSimproc`，返回的 `DStep` 里直接
放 `Expr`，不需要证明。`double n` 展开成 `2 * n`，`simp` 默认不知道；先看没有 simproc 时 `simp`
停在哪里：
-/

/--
error: unsolved goals
⊢ double 3 = 6
-/
#guard_msgs in
example : double 3 + 1 = 7 := by simp

/-- 把 `double k`（`k` 是字面量）化简成字面量 `2 * k`。 -/
dsimproc reduceDouble (double _) := fun e => do
  let_expr double n := e | return .continue
  let some v ← getNatValue? n | return .continue
  return .done (toExpr (2 * v))

example : double 3 + 1 = 7 := by simp

/-!
模式 `double _` 只用于粗筛（simproc 登记在判别树里，按表达式头部形状调度），保险起见在
函数体里再用 `let_expr` 检查形状，不匹配就返回 `.continue`；`getNatValue?` 识别字面量。

需要证明的版本用 `simproc`。默认的 `simp` 不展开 `box`（它是普通 `def`，没有 simp 引理），
所以下面的 `simp` 停住。`box n = n` 其实是定义相等（§0 的 `box_eq` 就是 `rfl`）；这里用 `simproc`
是为了演示怎样把证明 `box_eq` 交给 `simp`，结果与原式不定义相等时就必须这样提供证明：
-/

/--
error: unsolved goals
⊢ box 3 = 3
-/
#guard_msgs in
example : box 3 + 1 = 4 := by simp

/-- 把 `box n` 化简成 `n`，证明是 `box_eq n`。 -/
simproc reduceBox (box _) := fun e => do
  let_expr box n := e | return .continue
  return .done { expr := n, proof? := some (mkApp (mkConst ``box_eq) n) }

example : box 3 + 1 = 4 := by simp

/-!
## 8. 扩展属性：`@[positivity]`、`@[norm_num]`、`@[aesop]`

Mathlib 里很多策略是**驱动 + 插件**：驱动（`positivity`、`norm_num`、`gcongr`）遍历表达式，
插件由 `@[attr]` 注册，按表达式的形状（判别树）调度；`aesop` 同理，是按规则集做搜索。你写一个新
函数，就可以给它配一条插件，而不用改驱动。

| 属性 | 插件类型 | 注册位置（前三行在 `Mathlib/Tactic/` 下） |
|---|---|---|
| `@[positivity pat]` | `PositivityExt`（证 `0 < e`、`0 ≤ e`、`e ≠ 0`） | `Positivity/Core.lean:92` |
| `@[norm_num pat]` | `NormNumExt`（计算数值） | `NormNum/Core.lean:54` |
| `@[gcongr]` | 广义同余引理（单调性引理），`gcongr` 按它们递归下降 | `GCongr/Core.lean:385` |
| `@[aesop safe apply]` 等 | aesop 规则 | `aesop/Aesop/Frontend/Attribute.lean:25` |

`sq1 n` 其实是 `n * n + 1`，但 `positivity` 看不见展开，对 `0 < sq1 n` 失败：
-/

/--
error: failed to prove strict positivity, but it would be possible to prove nonnegativity if
desired
-/
#guard_msgs in
example (n : ℕ) : 0 < sq1 n := by positivity

/-!
写一个 `PositivityExt`：它接受表达式 `e : α`，返回 `.positive` / `.nonnegative` / `.nonzero` 加证明，
或 `.none`。下面照 Mathlib 里 `Nat.succ` 的扩展（`Mathlib/Tactic/Positivity/Basic.lean:514-522`）
写。`~q(…)` 匹配表达式，`q(sq1_pos $a)` 是证明。
-/

open Mathlib.Meta.Positivity in
/-- `positivity` 扩展：`sq1 a` 总是正的。 -/
@[positivity sq1 _]
def evalSq1 : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with  -- `pα?`：`α` 上可选的偏序实例，没有就无法谈论 `0 < e`
  | none => throwError "not PartialOrder ℕ"
  | some _ => do
    match u, α, e with
    | 0, ~q(ℕ), ~q(sq1 $a) =>  -- `u` 是宇宙层级，`0` 表示 `α : Type`
      assertInstancesCommute  -- 检查 `α` 上的偏序等实例与 `ℕ` 的标准实例定义相等，之后 `q(…)` 才能混用
      pure (.positive q(sq1_pos $a))
    | _, _, _ => throwError "not sq1"

example (n : ℕ) : 0 < sq1 n := by positivity

example (n m : ℕ) : 0 < sq1 n + 2 * sq1 m := by positivity

/-!
`@[aesop safe apply]` 把一条引理登记为 aesop 的安全规则：
-/

/--
error: Tactic `aesop` failed, made no progress
Initial goal:
  m : ℕ
  ⊢ 0 < sq1 m
-/
#guard_msgs in
example (m : ℕ) : 0 < sq1 m := by aesop

attribute [aesop safe apply] sq1_pos

example (m : ℕ) : 0 < sq1 m := by aesop

/-!
`@[norm_num]` 的结构与 `@[positivity]` 类似，扩展的类型是 `NormNumExt`，`eval` 返回一个
`Result`（例如 `.isNat` 附带证明）。本章不再演示它；要写这类扩展，先读
`Mathlib/Tactic/NormNum/Core.lean` 开头的文档注释，再读 `Mathlib/Tactic/NormNum/Basic.lean:58`
的 `evalZero`。
-/

/-!
## 9. `@[app_delab]`：改变美观打印

第 26 章 §9 用 `@[app_unexpander]` 改写显示（unexpander，反展开器）；`@[app_delab c]` 更一般：它拿到整个 `Expr`，
可以读隐式参数和类型（两者都要 `meta`）。规则是 `Delab := DelabM Term` 类型的函数，
`DelabM` 记着当前在 `Expr` 的哪个位置，`getExpr` 取当前子表达式，`withAppArg` 进入最后一个参数，
`delab` 递归地美观打印它。先声明一个记号作为输出的语法，再写 delab；`guard` 失败时 delab
放弃，回到默认显示：
-/

syntax "【" term "】" : term

macro_rules
  | `(【$a】) => `(box $a)

open PrettyPrinter Delaborator SubExpr in
/-- 把 `box a` 显示成 `【a】`。 -/
@[app_delab box]
def delabBox : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``box 1
  let a ← withAppArg delab
  `(【$a】)

/-- info: 【3】 : ℕ -/
#guard_msgs in
#check box 3

/-- info: fun n ↦ 【n + 1】 : ℕ → ℕ -/
#guard_msgs in
#check fun n : ℕ ↦ box (n + 1)

/-!
## 10. `@[to_additive]` 的原理

用法见第 15 章 §4，这里只讲原理。`@[to_additive]` 遍历定义的类型和体，把其中的常量按对照表
（`Mul → Add`、`One → Zero`……）替换，再用翻译后的名字登记一个新声明；§0 里对 `sqr` 使用了它：
-/

/--
info: @[expose] def Lean4Learn.Ch27.twice.{u_1} : {G : Type u_1} → [Add G] → G → G :=
fun {G} [Add G] a ↦ a + a
-/
#guard_msgs in
#print twice

/-!
名字可以省略，让工具按词典去猜；猜得不合意就像 §0 那样显式给名。翻译的规则与排错办法
（`set_option trace.translate_detail true`）在 `to_additive` 属性的文档注释里
（`Mathlib/Tactic/Translate/ToAdditive.lean` 第 247 行 `syntax (name := to_additive)` 之前）。
-/

/-!
## 11. Mathlib 策略文件的解剖

**`Mathlib/Tactic/ByContra.lean`（73 行）以宏为主。** 文件头是两行 `public import`
（`Batteries.Tactic.Init`、`Mathlib.Tactic.Push`）和 `public meta section`，主体三部分：一条带文档
注释的 `syntax (name := byContra!) "by_contra!" …`；两个只在本文件可见的 `local elab`
（`try_push_neg_at`、`try_push_neg`），函数体直接调用 `Push.push` 与 `Push.elabPushConfig`，
没有另写核心函数；一条 `macro_rules`，把 `by_contra! …` 展开成
`by_contra h; try_push_neg_at …; revert h; rintro …`。元程序调用 `Push.push` 却不用 `meta import`，
是因为它本身定义在 `Push.lean` 的 `public meta section` 里，已经是 `meta`；`meta import` 只在
要把**普通**定义拿进元程序时才需要（§0）。本文件 import 了它，本节末尾的 `by_contra!` 例子
就会运行这两个 `elab`。**选宏还是选 `elab`：** 行为能写成「改写成别的策略」就用宏，它自动卫生；
要读目标、检查假设、构造证明项或需要错误处理时才用 `elab`。

**`Mathlib/Tactic/Use.lean`（226 行）是 `elab` 式策略。** 文件头是两行 `public meta import` 加
`public import Mathlib.Init`，然后 `public meta section`，主体按顺序：

1. `initialize registerTraceClass `tactic.use`（第 30 行）：注册追踪类，`trace[tactic.use] …` 才有输出；
2. `def applyTheConstructor (mvarId : MVarId) : MetaM …`（第 44 行）：纯 `MetaM` 的核心步骤，
   用的是 `forallMetaTelescopeReducing`（`forallTelescope` 的元变量版本）和本章 §2、§4 的工具；
3. `partial def useLoop …`（第 85–86 行，`TermElabM`）与 `def runUse …`（第 121 行，`TacticM` 入口）；
4. `syntax "use_discharger" : tactic` 加五条 `macro_rules`（第 150–156 行）：**可扩展**的
   discharger（副条件处理器）；
5. 前端 `elab (name := useSyntax) "use" … : tactic => …`，以及用 `@[tactic_alt useSyntax]` 登记的
   变体 `use!`（第 218–226 行）。

第 4 点的「可扩展」可以亲手验证：`use 3` 之后剩下的 `3 + m = m + 3` 默认处理器解决不了；给
`use_discharger` 追加一条 `macro_rules`（`local` 让它只在本文件生效）就行：
-/

/--
error: unsolved goals
case h
m : ℕ
⊢ 3 + m = m + 3
-/
#guard_msgs in
example (m : ℕ) : ∃ n : ℕ, n + m = m + 3 := by use 3

local macro_rules
  | `(tactic| use_discharger) => `(tactic| omega)

example (m : ℕ) : ∃ n : ℕ, n + m = m + 3 := by use 3

example (a b : ℕ) : a ≤ b ∨ b < a := by
  by_contra! h
  omega

/-!
两个文件的共同点：对外的策略都有带例子的文档注释，测试在 `MathlibTest/Tactic/` 下的同名文件里。
不同点：`Use.lean` 把核心步骤写成独立的 `MetaM` 函数，`elab` 只做接线；`ByContra.lean` 用宏组合
现成策略，两个小 `elab` 只包装 `Push.push`。

## 12. 案例：写一个真正的策略 `split_all`

把 §4 的 `splitAnd` 扩成一个别人也能用的策略：除了拆 `∧`，还对 `∀`/`→` 做 `intro`、对 `↔` 用
`Iff.intro`，并在无事可做时给出清楚的错误，而不是悄悄成功。算法仍在 `MetaM` 函数里（可单独测试），
策略只做接线与错误报告：
-/

/-- 反复 `intro` 并拆开 `∧`、`↔`，返回剩下的目标。 -/
partial def splitAll (g : MVarId) : MetaM (List MVarId) := g.withContext do
  let target ← whnfR (← g.getType)
  if target.isForall then
    let (_, g') ← g.intro1
    splitAll g'
  else if target.isAppOfArity ``And 2 then
    return (← (← g.apply (mkConst ``And.intro)).mapM splitAll).flatten
  else if target.isAppOfArity ``Iff 2 then
    return (← (← g.apply (mkConst ``Iff.intro)).mapM splitAll).flatten
  else
    return [g]

/-- `split_all`：对 `∀`/`→` 目标 `intro`，并拆开 `∧` 与 `↔`；没有可做的事时报错。 -/
elab "split_all" : tactic => do
  let g ← getMainGoal
  match ← splitAll g with
  | [g'] =>
    if g' == g then throwTacticEx `split_all g "nothing to split" else replaceMainGoal [g']
  | gs => replaceMainGoal gs

example (p q : Prop) (_hp : p) (hq : q) : p → (q ∧ p) ∧ (p ↔ p) := by
  split_all
  all_goals assumption

/--
error: Tactic `split_all` failed: nothing to split

p : Prop
hp : p
⊢ p
-/
#guard_msgs in
example (p : Prop) (hp : p) : p := by split_all

/-!
## 常见错误

**1. 用 `mkApp` 而不用 `mkAppM`。** `mkApp2 (mkConst ``HAdd.hAdd) a b` 缺少宇宙实参、类型实参
和实例实参，是一个坏表达式；`inferType` 会发现：
-/

/-- error: incorrect number of universe levels HAdd.hAdd -/
#guard_msgs in
#eval show MetaM Unit from do
  let e := mkApp2 (mkConst ``HAdd.hAdd) (mkNatLit 1) (mkNatLit 2)
  logInfo m!"{← inferType e}"

/-!
**2. 以为 `closeMainGoal` 会检查类型。** 它不检查：下面的策略把 `0` 当作 `1 = 2` 的证明，
策略毫无怨言，直到内核检查整个证明项时才报错。要在策略里提前报错，自己用 `isDefEq` 比较类型：
-/

/-- 错误示范：直接关闭。 -/
elab "bad_close" : tactic => closeMainGoal `bad_close (mkNatLit 0)

/--
error: (kernel) declaration type mismatch, 'Lean4Learn.Ch27._example' has type
  ℕ
but it is expected to have type
  1 = 2
-/
#guard_msgs in
example : 1 = 2 := by bad_close

/-- 先比较类型再关闭目标。 -/
elab "safe_close" : tactic => withMainContext do
  let g ← getMainGoal
  let v := mkNatLit 0
  unless (← isDefEq (← inferType v) (← g.getType)) do
    throwTacticEx `safe_close g m!"{v} has type {← inferType v}"
  closeMainGoal `safe_close v

/--
error: Tactic `safe_close` failed: 0 has type ℕ

⊢ 1 = 2
-/
#guard_msgs in
example : 1 = 2 := by safe_close

/-!
**3. 在 `meta` 声明里调用普通函数**（§0 的 `callsPlain`），以及 **4. 用 Qq 写错类型**
（§6 的 `q(Nat.mul_comm $a $b)`）：两者的报错都在各自的节里捕获过。

## 练习

练习 27.1、27.4、27.5、27.6、27.12、27.14 复习第 6、15、2、5、24、10 章。其中 27.7、27.8、27.13
要求你**写策略或项精译器**：写出 `def` 的函数体，章节里已经为它们配好了 `elab`；27.10、27.15 的
注册行在注释里，写完后取消注释。★ 直接应用，★★ 综合两个想法，★★★ 需要新想法。
-/

/-- 练习 27.1（★）：`fun x₁ … xₙ ↦ b` 开头有多少个 `lam`？不是 `lam` 的返回 0。
提示：对 `Expr` 做模式匹配，`.lam _ _ b _ => …`（第 6 章）。 -/
def ex_27_1 : Expr → Nat := sorry

/-- 练习 27.2（★）：用 `mkAppM` 造出 `Nat.add_comm a b` 的表达式，使 `inferType` 给出
`a + b = b + a`。 -/
def ex_27_2 (a b : ℕ) : MetaM Expr := sorry

/-- 练习 27.3（★★）：对声明 `declName`，返回其类型开头的 `∀` 约束变量个数，以及结论（去掉全部
`∀`）是否是等式 `Eq`。例如 `Nat.add_comm` 给出 `(2, true)`。提示：`getConstInfo`、
`forallTelescope`、`Expr.isAppOfArity`（`Eq` 有 3 个参数）。 -/
def ex_27_3 (declName : Name) : MetaM (Nat × Bool) := sorry

/-- 练习 27.4（★）：用 §10 的 `twice` 证明（第 15 章）。提示：`two_nsmul`。 -/
theorem ex_27_4 {G : Type*} [AddMonoid G] (a : G) : twice a = 2 • a := sorry

/-- 练习 27.5（★）：用本章的 `split_and` 与 `omega` 证明（其他证法也接受）。 -/
theorem ex_27_5 (n : ℕ) (h : 2 ≤ n) : 1 < n ∧ 3 ≤ n + 1 ∧ n ≠ 0 := sorry

/-- 练习 27.6（★）：用 §7 的 `reduceDouble`（即 `simp`）证明。注意嵌套：内层先被化简。 -/
theorem ex_27_6 : double (double 2) + 1 = 9 := sorry

/-- 练习 27.7（★★）：写策略 `symm_assumption`：目标是 `a = b`，上下文里有 `h : b = a` 时
用 `h.symm` 关闭目标。提示：`withMainContext`、`getMainTarget`、`Expr.eq?`（把 `a = b` 拆成
`(类型, a, b)`）、`getLCtx`、`isDefEq`、`mkEqSymm`、`closeMainGoal`；找不到时 `throwTacticEx`。 -/
def ex_27_7 : TacticM Unit := sorry

elab "symm_assumption" : tactic => ex_27_7

/-- 练习 27.8（★★）：写策略 `last_hyp`：用**最后一个**非实现细节的局部假设关闭目标
（类型要定义相等，用默认透明度）。提示：`getLocalHyps`（已去掉实现细节）、`Array.back?`。 -/
def ex_27_8 : TacticM Unit := sorry

elab "last_hyp" : tactic => ex_27_8

/-- 练习 27.9（★）：返回 `a`、`b` 在可约透明度与默认透明度下是否定义相等。 -/
def ex_27_9 (a b : Expr) : MetaM (Bool × Bool) := sorry

/-- 练习 27.10（★）：写 `sq1 k`（`k` 是字面量）的 `dsimproc` 函数体：化简为字面量 `k * k + 1`。
参考 §7 的 `reduceDouble`。写完后取消注释下一行。 -/
def ex_27_10 : Simp.DSimproc := sorry

-- dsimproc reduceSq1 (sq1 _) := ex_27_10

/-- 练习 27.11（★）：用 Qq 的 `~q` 匹配：`e` 形如 `a + b` 时返回 `b + a`，否则返回 `none`。 -/
def ex_27_11 (e : Q(ℕ)) : MetaM (Option Q(ℕ)) := sorry

/-- 练习 27.12（★★）：返回命名空间 `ns` 下所有常量的名字，按 `Name.quickLt` 排序（第 24 章的
`Array`）。提示：`getEnv`、`env.constants.fold`、`Array.qsort`。 -/
def ex_27_12 (ns : Name) : CoreM (Array Name) := sorry

/-- 练习 27.13（★★）：写项精译器 `num_hyps`：返回当前上下文里局部假设的个数（作为 `ℕ` 字面量）。
提示：`getLocalHyps`、`mkNatLit`。 -/
def ex_27_13 : TermElabM Expr := sorry

elab "num_hyps" : term => ex_27_13

/-- 练习 27.14（★）：用 `positivity`（有了 §8 的扩展）证明；也可以先 `unfold sq1` 再 `omega`。 -/
theorem ex_27_14 (n : ℕ) : sq1 n ≠ 0 ∧ 0 < sq1 (n + 1) := sorry

/-- 练习 27.15（★★★）：写 `double` 的 `positivity` 扩展：参数为正时 `double a` 为正（用
`double_pos`），否则为非负。提示：照 §8 的 `evalSq1`，用 `Mathlib.Meta.Positivity.core` 取得
参数的 `Strictness`（`Mathlib/Tactic/Positivity/Core.lean` 第 60、438 行）；`match pα? with` 之后
用 `some pα` 这个名字，调用 `core zα (some pα) a`，结果的类型才对得上。写完后取消注释下一行。 -/
def ex_27_15 : Mathlib.Meta.Positivity.PositivityExt := sorry

-- attribute [positivity double _] ex_27_15

/-!
## 小结

| 概念 | 语法 / API | 何时使用 |
|---|---|---|
| 表达式 | `Expr`；`mkConst`、`mkApp`、`mkNatLit`、`toExpr` | 内部表示；`toExpr` 把值变表达式，`quote` 把值变语法 |
| 推断与规约 | `inferType`、`whnf`、`isDefEq`、`mkAppM`、`instantiateMVars` | `MetaM` 里读写表达式 |
| 透明度 | `withReducible`、`withDefault`、`withTransparency` | 控制 `isDefEq`/`whnf` 展开多少定义 |
| 运行 | `#eval show MetaM Unit from do …`，`logInfo` | 实验 |
| 项精译器 | `elab "k" : term <= ty => …` | 需要读期望类型的项 |
| 命令精译器 | `elab "#k" … : command => …`，`Command.liftTermElabM` | 读环境、跑 `MetaM` |
| 策略 | `elab "k" : tactic => withMainContext do …` | 读目标和假设、构造证明 |
| 目标操作 | `getMainGoal`、`closeMainGoal`、`liftMetaTactic`、`setGoals` | 关闭、替换、重排目标 |
| 错误 | `throwError`、`throwTacticEx`、`logInfo`、`try … catch` | 失败要抛异常，提示用日志 |
| Qq | `Q(α)`、`q(e)`、`~q(p)` | 带类型的表达式与模式匹配 |
| simproc | `dsimproc`/`simproc`，`.done`/`.visit`/`.continue` | 给 `simp` 加计算规则 |
| 扩展属性 | `@[positivity pat]`、`@[norm_num pat]`、`@[aesop …]` | 给驱动策略加插件 |
| 美观打印 | `@[app_delab c] def … : Delab` | 改变某个函数的显示 |
| 翻译 | `@[to_additive name]` | 乘法 ⇒ 加法 |
| 模块系统 | `public meta import`、`public meta section`、`meta def` | 编译期执行的代码 |
| 案例 | `MetaM` 函数 + `elab` 接线 + 错误报告 + 测试（§12 `split_all`） | 写一个可交付的策略 |

怎样选择：能用宏就用宏；要读目标或假设才写 `elab`；算法放进 `MetaM` 函数，策略只做接线，
这样既可测试又能复用；先用 `#eval show MetaM Unit from do …` 在小例子上试 API，再写策略。

## 延伸阅读

- *Lean Language Reference* 4.35.0：「Notations and Macros」一章的 Elaborators 与
  Extending Lean's Output 两节；「Source Files and Modules」里的 The Meta Phase；
  「Definitions」里的 Controlling Reduction（透明度）
  （`https://lean-lang.org/doc/reference/4.35.0/`）。
- *Metaprogramming in Lean 4*（lean4-metaprogramming-book）：关于 `Expr`、`MetaM`、精译器、
  `TacticM` 的几章；`my_assumption` 的原型是「Tactics」一章里的 `custom_assump_1`。
- Lean 核心源码：`Lean/Elab/Tactic/Basic.lean`（`getMainGoal`、`closeMainGoal`、
  `liftMetaTactic`）、`Lean/Meta/Tactic/Simp/Types.lean`（`Simproc`、`Step`）、
  `Lean/PrettyPrinter/Delaborator/Basic.lean`（`delabAttribute`、`app_delab`）。
- Mathlib：`Mathlib/Tactic/Use.lean`、`Mathlib/Tactic/ByContra.lean`（§11）；
  `Mathlib/Tactic/Positivity/Core.lean` 与 `Basic.lean`（§8）；`Mathlib/Tactic/NormNum/Core.lean`；
  `Mathlib/Tactic/Translate/ToAdditive.lean` 中 `to_additive` 属性的文档注释（§10）。
- Qq：`.lake/packages/Qq/Qq/Macro.lean`（`q(…)` 与 `Q(…)`）。
- 本书第 26 章（宏与语法）、第 28 章（内核、透明度、模块系统内部）。
-/

end Lean4Learn.Ch27

end
