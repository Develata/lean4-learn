module

public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.TypeStar

/-!
# 第 6 章　归纳类型、结构体与递归

NNG 里的 `ℕ` 只有两条规则：`0 : ℕ`，以及「`n : ℕ` 则 `n + 1 : ℕ`」。本章把它推广：任何 inductive
type（归纳类型）都是「一组 constructor（构造子）加上由它们生成的类型」，而 `match`、`cases`、
`induction`、递归函数是同一件事的不同侧面。读完本章，你能定义自己的枚举、树与 `MyNat`，写递归函数并
证明它们的性质，也能读懂 `decide` 为什么有时失败。

## 学习目标
- 用 `inductive` 定义枚举与递归类型，说出构造子与 recursor（递归子）的关系；
- 用 pattern matching（模式匹配）与 structural recursion（结构递归）写函数，会读 `ℕ` 目标里的 `0` 与
  `n + 1`；
- 用 `cases`、`induction` 证明归纳类型上的命题，会用 induction hypothesis（归纳假设）；项模式下，递归
  调用就是归纳假设；
- 证明递归函数的性质：`simp [f]`、`rw [f.eq_2]`（equation lemma，等式引理）、`unfold f`、
  `fun_induction`；
- 认识 `List`、`Option`，以及 `∨`、`∧`、`=` 都是归纳类型；
- 用 `structure`（结构体）定义带 field（字段）、projection（投影）、dot notation（点记号）与
  `deriving`（派生）的结构体，会用 4.18 的 `extends`；
- 用 `termination_by` 与 `decreasing_by` 写 well-founded recursion（良基递归），知道 `decide` 为什么
  对它失效，以及 `simp [f]`、`decide +kernel`、`@[semireducible]` 各解决什么；
- 说清 4.35 版 `Decidable`（一个 `Bool` 加一个证明），会用 `decidable_of_iff` 提供 decidable（可判定）
  的实例。

## 前置知识
第 2 章的 `omega`、`linarith`、`nlinarith` 与 `induction`；第 3 章的项模式与 `fun`；第 4 章的 `rcases`、
`<;>`、`by_cases`、`left`/`right`；第 5 章的 `rw`、`simp`、`ext`、`subst`、`decide` 与定义相等。
-/

@[expose] public section

namespace Lean4Learn.Ch06

/-!
## 1. 枚举类型

最简单的 inductive type 只有一组彼此不同的常量。`inductive` 声明一个类型和它的全部构造子：每个元素都
由某个构造子造出，不同构造子造出的元素互不相等。`deriving Repr, DecidableEq` 自动生成两个 instance
（实例）：`Repr` 管 `#eval` 的打印，`DecidableEq` 让 `=` 可以被 `decide` 判定（§10）。
-/

inductive Weekday where
  | mon | tue | wed | thu | fri | sat | sun
  deriving Repr, DecidableEq

/-!
在 `def Weekday.next` 的体内，namespace（命名空间）`Weekday` 已经打开，所以构造子可以直接写 `mon`。
一行一条等式：左边是模式，右边是结果；模式必须穷尽所有构造子，漏掉一个就报错（§11）。
-/

def Weekday.next : Weekday → Weekday
  | mon => tue
  | tue => wed
  | wed => thu
  | thu => fri
  | fri => sat
  | sat => sun
  | sun => mon

example : Weekday.sun.next = Weekday.mon := rfl            -- 按定义算出来
example : Weekday.mon ≠ Weekday.tue := by decide           -- `DecidableEq` 让 `decide` 能判定

/-!
证明一个关于所有 `Weekday` 的命题，就是对 7 个构造子各证一次。`cases d` 把目标拆成 7 个，每个构造子
一个；`<;>`（第 4 章）对每个目标运行同一个策略：
-/

theorem Weekday.next_ne (d : Weekday) : d.next ≠ d := by
  cases d <;> decide     -- 7 个目标：`mon.next ≠ mon`、`tue.next ≠ tue`、…，各自判定

/-!
## 2. 递归类型：自己的 `MyNat`

构造子可以以类型本身为参数，这样的类型就是递归的。下面是 `ℕ` 的逐字翻版（与 NNG 里的 `MyNat` 同形）：
`zero` 是一个元素；给定 `n`，`succ n` 也是。
-/

inductive MyNat where
  | zero : MyNat
  | succ (n : MyNat) : MyNat

/-!
每个 `inductive` 声明都会自动生成 `T.rec`，它就是这个类型的 induction principle（归纳原理）：要对所有
`t : MyNat` 证明 `motive t`，只需证 `motive zero`，并证明对任意 `n`，由 `motive n` 推出
`motive (succ n)`。`motive` 是你要证明（或要构造）的、依赖于 `t` 的那个陈述，值域是 `Sort u`（第 3 章；
`#check @…` 把宇宙变量重命名为 `u_1`）：取 `Prop` 时 `rec` 是数学归纳法，取 `Type` 时它是递归定义的
原料。`cases` 与 `induction` 就是在把目标套进它的 eliminator（消去子，`rec` 一类函数的统称）。
-/

/-- info: @MyNat.rec : {motive : MyNat → Sort u_1} →
  motive MyNat.zero → ((n : MyNat) → motive n → motive n.succ) → (t : MyNat) → motive t -/
#guard_msgs in #check @MyNat.rec

/-!
真正的 `ℕ` 是同样的两个构造子 `Nat.zero` 与 `Nat.succ`。`0` 与 `n + 1` 是 `OfNat` 字面量与加法，它们与
构造子 definitional equality（定义相等），如下面的 `rfl` 所示；为什么证明里的目标显示 `0` 与 `n + 1`，
见 §4：
-/

example : Nat.zero = 0 := rfl
example (n : ℕ) : Nat.succ n = n + 1 := rfl

/-!
加法对第二个参数递归，与 NNG 的定义相同。`add_succ` 是定义本身，所以证明就是 `rfl`（NNG 里它是给定的
引理）：
-/

def MyNat.add : MyNat → MyNat → MyNat
  | n, .zero => n
  | n, .succ m => .succ (MyNat.add n m)

theorem MyNat.add_succ (n m : MyNat) : n.add m.succ = (n.add m).succ := rfl

/-!
`zero_add` 不是定义本身，所以要对 `n` 归纳。
`induction n with | zero => … | succ n ih => …` 对每个构造子给一个分支，分支里的变量名依次对应构造子
的字段，递归字段额外带来一个归纳假设 `ih`：
-/

/--
trace: case succ
n : MyNat
ih : zero.add n = n
⊢ zero.add n.succ = n.succ
-/
#guard_msgs in
theorem MyNat.zero_add (n : MyNat) : MyNat.zero.add n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    trace_state
    rw [MyNat.add_succ, ih]

/-!
同一个定理的项模式写法：递归调用 `MyNat.zero_add' n` 就是归纳假设 `ih`（`zero.add n.succ` 与
`(zero.add n).succ` 定义相等，所以用 `congrArg MyNat.succ` 接上）：
-/

theorem MyNat.zero_add' : ∀ n : MyNat, MyNat.zero.add n = n
  | .zero => rfl
  | .succ n => congrArg MyNat.succ (MyNat.zero_add' n)

def MyNat.toNat : MyNat → ℕ
  | .zero => 0
  | .succ n => n.toNat + 1

/-!
## 3. 结构递归：树

构造子的字段可以不止一个，也可以带参数。二叉树：叶子没有数据，结点带左子树、值与右子树；
`(α : Type*)` 是类型参数，`Tree ℕ`、`Tree String` 是不同的类型。（`Type*` 让定义对所有宇宙层级成立，
见第 3 章 §7；下面 `#print`、`trace_state` 里因此会出现自动生成的宇宙变量 `u_1`。）
-/

inductive Tree (α : Type*) where
  | leaf : Tree α
  | node (l : Tree α) (v : α) (r : Tree α) : Tree α

def Tree.size {α : Type*} : Tree α → ℕ
  | leaf => 0
  | node l _ r => l.size + 1 + r.size

def Tree.mirror {α : Type*} : Tree α → Tree α
  | leaf => leaf
  | node l v r => node r.mirror v l.mirror

/-!
递归调用都作用在参数的直接子项（`l`、`r`）上，这叫结构递归，Lean 自动判定它终止，闭项上可以靠定义
相等直接算。证明性质时，对树做 `induction`：两个构造子，`node` 分支有两个递归字段，所以有两个
归纳假设。
-/

example : (Tree.node .leaf 1 .leaf).size = 1 := rfl

/--
trace: case node
α : Type u_1
l : Tree α
v : α
r : Tree α
ihl : l.mirror.size = l.size
ihr : r.mirror.size = r.size
⊢ (l.node v r).mirror.size = (l.node v r).size
-/
#guard_msgs in
theorem Tree.size_mirror {α : Type*} (t : Tree α) : t.mirror.size = t.size := by
  induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
    trace_state
    simp only [Tree.mirror, Tree.size, ihl, ihr]
    omega

/-!
## 4. `ℕ` 上的自定义消去子

对 `ℕ` 用 `cases`/`induction` 时，目标显示 `0` 与 `n + 1`，而不是 `Nat.zero` 与 `Nat.succ n`。原因是
`Nat` 另外登记了自定义 eliminator（`@[induction_eliminator]`、`@[cases_eliminator]`，v4.8 起，见
`Nat.recAux`、`Nat.casesAuxOn`），它们的陈述直接写 `0` 与 `n + 1`。二者的区别：`induction` 的递归字段
带 `ih`；`cases` 只分情况，没有 `ih`，想给新变量起名就写 `| succ m`。下面 `succ` 分支的目标里只有
`m + 1`，没有归纳假设：
-/

/--
trace: case succ
m : ℕ
⊢ m + 1 = 0 ∨ ∃ k, m + 1 = k + 1
-/
#guard_msgs in
example (n : ℕ) : n = 0 ∨ ∃ k, n = k + 1 := by
  cases n with
  | zero => left; rfl
  | succ m => trace_state; right; exact ⟨m, rfl⟩

/-!
下一节的 `sumTo.eq_2` 与 `fun_induction` 的目标仍按函数定义里的模式显示 `n.succ`；它与 `n + 1` 定义
相等，`omega`、`simp` 都认得（`linarith` 见下）：
-/

example (n : ℕ) : n.succ = n + 1 := by omega

/-!
## 5. 证明递归函数的性质

`simp` 与 `rw` 不会自动展开递归函数的定义。要证明性质，需要工具把 `f` 换成它的定义，这些工具都依赖
equation lemma（等式引理）：对每条模式等式生成一条定理 `f.eq_1`、`f.eq_2`、…，它们是自动生成的，
不用声明：
-/

def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- info: sumTo.eq_2 : ∀ (n : ℕ), sumTo n.succ = sumTo n + (n + 1) -/
#guard_msgs in #check @sumTo.eq_2

/-!
`simp [f]` 反复用等式引理改写，省事但可能改写过头；`rw [f.eq_2]` 手动改写一次，最精确；
`unfold f`（第 5 章）展开 `f` 的出现，不必记等式的编号。两种写法证同一个等式（高斯求和），都在归纳步里
先展开 `sumTo (n + 1)`，再用 `linarith`（第 2 章）完成。第一种写法打出 `simp` 之后的目标：`linarith`
把两边的乘积展开，成为 `sumTo n` 与 `n`、`n * n` 的线性组合，再用 `ih` 验证：
-/

/--
trace: case succ
n : ℕ
ih : 2 * sumTo n = n * (n + 1)
⊢ 2 * (sumTo n + (n + 1)) = (n + 1) * (n + 1 + 1)
-/
#guard_msgs in
theorem sumTo_formula (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumTo]; trace_state; linarith

example (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo.eq_2]; linarith

/-!
`fun_induction f x` 按 `f` 自己的递归结构做归纳：`f` 有几个分支就有几个情形，每个递归调用带一个归纳
假设，而且目标里的 `f` 已经展开。分支名是 `case1`、`case2`、…；目标按函数的模式书写，所以是
`n.succ` 而不是 `n + 1`（§4）。对 `sumTo`：
-/

/--
trace: case case2
n : ℕ
ih : 2 * sumTo n = n * (n + 1)
⊢ 2 * (sumTo n + (n + 1)) = n.succ * (n.succ + 1)
-/
#guard_msgs in
example (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  fun_induction sumTo n with
  | case1 => rfl
  | case2 n ih => trace_state; linarith

/-!
## 6. `List` 与 `Option` 也是归纳类型

`List` 与 `Option` 是后面所有章节的主要数据结构。`List α` 有两个构造子：`nil`（空列表，写 `[]`）与
`cons`（`x :: xs`）。`Option α` 表示「可能没有结果」，也是两个构造子：`none` 与 `some a`，用 `match` 或
`cases` 处理。（撞词提示：`Option` 类型与
`set_option` 的「选项」无关，本书称 `Option` 类型。）
-/

/--
info: inductive Option.{u} : Type u → Type u
number of parameters: 1
constructors:
Option.none : {α : Type u} → Option α
Option.some : {α : Type u} → α → Option α
-/
#guard_msgs in #print Option

/-!
自己写一个 `app`（拼接），再证明它的长度公式：对第一个列表归纳，`cons` 分支恰有一个归纳假设。
这就是库里的 `List.length_append`：
-/

def app {α : Type*} : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys

theorem length_app {α : Type*} (xs ys : List α) :
    (app xs ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp [app]
  | cons x xs ih =>
    simp [app, ih]      -- 把两边化成 `xs.length` 与 `ys.length` 的线性式
    omega               -- 线性算术，交给 `omega`

example {α : Type*} (xs ys : List α) : (xs ++ ys).length = xs.length + ys.length :=
  List.length_append

def safeDiv (a b : ℕ) : Option ℕ :=
  match b with
  | 0 => none
  | b + 1 => some (a / (b + 1))

example (o : Option ℕ) : o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => left; rfl
  | some a => right; exact ⟨a, rfl⟩

/-!
## 7. `Or`、`And`、`Eq` 也是归纳类型

第 3、5 章已经说过 `Or`、`And`、`Eq` 是归纳类型，这里补上两件事。一是它们和 `Weekday` 一样可以直接
`match`：`Or` 有两个构造子，对 `h : p ∨ q` 分情况：
-/

example (p q : Prop) (h : p ∨ q) : q ∨ p :=
  match h with
  | .inl hp => .inr hp
  | .inr hq => .inl hq

/-!
二是 `Eq` 的消去子。`Eq` 的唯一构造子是 `Eq.refl a : a = a`，它的递归子 `Eq.rec` 就是「相等的两边
可以互相替换」；第 5 章的 `h ▸ ha` 展开就是这样一次替换：
-/

example (P : ℕ → Prop) (a b : ℕ) (h : a = b) (ha : P a) : P b :=
  Eq.rec (motive := fun x _ ↦ P x) ha h

/-!
## 8. 结构体

用 `structure` 声明的、只有一个构造子的归纳类型叫结构体，它的构造子参数叫字段；Lean 为每个字段
自动生成一个投影函数 `Point.x`。（撞词提示：Lean 的结构体不是数学里的「结构」；字段也不是代数里的
「域」。）`@[ext]` 生成 extensionality（外延性）引理（第 5 章的 `ext`）：
-/

@[ext] structure Point where
  x : ℕ
  y : ℕ
  deriving Repr, DecidableEq

/-- info: { x := 1, y := 2 } -/
#guard_msgs in #eval ({ x := 1, y := 2 } : Point)

/-!
`Point.ext` 里的 `x`、`y` 是两个 `Point`（不是坐标），`x.x` 是第一个点的 `x` 坐标：
-/

/-- info: @Point.ext : ∀ {x y : Point}, x.x = y.x → x.y = y.y → x = y -/
#guard_msgs in #check @Point.ext

/-!
构造一个结构体：构造子 `Point.mk 1 2`；匿名构造子 `⟨1, 2⟩`（需要期望类型）；记录语法
`{ x := 1, y := 2 }`；`{ p with x := 5 }` 复制 `p` 并改一个字段。`p.x` 是投影的 dot notation
（点记号）。结构 eta 使 `⟨p.x, p.y⟩ = p` 定义相等。
-/

example (p : Point) : Point.mk p.x p.y = p := rfl
example (p : Point) : { p with x := 5 }.y = p.y := rfl

/-!
`extends` 表示继承。4.18 起可以写 `extends base : Point` 给父结构体取字段名，
`p.base` 就是 `Point3` 里的 `Point` 部分；父结构体的字段 `x`、`y` 仍可直接访问。
`structure … where` 是现行写法（旧的 `:=` 已弃用，§11）。
-/

structure Point3 extends base : Point where
  z : ℕ

example (p : Point3) : p.x = p.base.x := rfl

/-!
字段的类型可以依赖前面的字段，包括命题：这样的字段是一个「附带的证明」。第 7 章的 subtype（子类型）
`{x // p x}` 就是这种结构体的一般形式。
-/

structure PosNat where
  val : ℕ
  pos : 0 < val

example : PosNat := ⟨3, by decide⟩
example (p : PosNat) : 0 < p.val := p.pos

/-!
## 9. 良基递归：`termination_by` 与 `decreasing_by`

欧几里得算法的递归调用 `myGcd b (a % b)` 不在参数的子项上，不是结构递归。Lean 对递归定义先试结构
递归，不行就自己猜一个 termination measure（度量，即终止度量；与测度论的「测度」无关），并用默认策略
证明每次递归调用时度量严格变小。猜不出度量，或默认策略证不出来，就要自己写 `termination_by`（给出
度量）与 `decreasing_by`（给出证明），它们是终止性的证明接口（缺了哪个会怎样，见 §11 第 3 条）。度量取
`ℕ` 值、每次调用严格变小，就没有无限递降的链，函数因此终止：这叫 well-founded recursion（良基递归）。
`if` 的条件 `¬b = 0` 自动进入 `decreasing_by` 的上下文（`trace_state` 打印此刻的目标）：
-/

/--
trace: a b : ℕ
h✝ : ¬b = 0
⊢ a % b < b
-/
#guard_msgs in
def myGcd (a b : ℕ) : ℕ :=
  if b = 0 then a else myGcd b (a % b)
termination_by b
decreasing_by
  trace_state
  exact Nat.mod_lt _ (by omega)

/-- info: 6 -/
#guard_msgs in #eval myGcd 12 18

/-!
良基递归的函数默认带 `@[irreducible]`；reducibility（可约性）决定 `decide`、`rfl` 能展开哪些定义，
所以即使参数是具体的数，`decide` 也不会展开 `myGcd`。报错里的 `(myGcd 12 18).beq 6` 就是卡住的地方：
`myGcd` 不可约，`Nat.beq` 无法求值：
-/

/--
error: Tactic `decide` failed to reduce
  @decide (myGcd 12 18 = 6) (instDecidableEqNat (myGcd 12 18) 6)
to `true` or `false`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at
  (myGcd 12 18).beq 6
-/
#guard_msgs in
example : myGcd 12 18 = 6 := by decide

/-!
绕过的办法有三种。（1）`simp [myGcd]` 反复用等式引理，得到的是证明而不是计算；适合一般的证明：
-/

example : myGcd 12 18 = 6 := by simp [myGcd]

/-!
（2）`decide +kernel` 让 kernel（内核）而不是 elaborator（精译器；另译繁饰器）去规约；reducibility
属性只约束 elaborator，内核不看它。度量是 `ℕ` 值时，这个定义编译成内核能规约的形式，所以内核能算出
这个值；输入很大时用它：
-/

example : myGcd 12 18 = 6 := by decide +kernel

/-!
（3）在定义前加 `@[semireducible]`，函数回到默认的 semireducible（可展开）级别，`decide` 与 `rfl`
重新有效。它只在度量是 `ℕ` 值时起作用（v4.27 起；其他度量下它不起作用，Lean 会发出警告，见下面的对照），
适合小的辅助函数：
-/

@[semireducible] def myGcd' (a b : ℕ) : ℕ :=
  if b = 0 then a else myGcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

example : myGcd' 12 18 = 6 := by decide
example : myGcd' 12 18 = 6 := rfl

/-!
对照：度量不是 `ℕ` 值时，同样的 `@[semireducible]` 无效，Lean 在属性处发警告。下面按列表本身的大小递归
（`termination_by xs` 用的是 `sizeOf` 的良基关系，不是 `ℕ` 的 `<`），`decide` 照样卡住：
-/

/--
warning: marking functions defined by well-founded recursion as `semireducible` is not effective
-/
#guard_msgs in
@[semireducible] def sumList (xs : List ℕ) : ℕ :=
  match xs with
  | [] => 0
  | x :: rest => x + sumList rest
termination_by xs

/--
error: Tactic `decide` failed to reduce
  @decide (sumList [1, 2] = 3) (instDecidableEqNat (sumList [1, 2]) 3)
to `true` or `false`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at
  (sumList [1, 2]).beq 3
-/
#guard_msgs in
example : sumList [1, 2] = 3 := by decide

/-!
## 10. `Decidable` 与 `decide`

`decide` 的用法与边界（含「目标不能含自由变量」的报错）见第 5 章。这里讲它背后的 `Decidable`。
4.35 里 `Decidable p` 是一个类：一个 `Bool` 加上它与 `p` 的对应证明（以前它是带 `isFalse`/`isTrue`
两个构造子的归纳类型）：
-/

/--
info: class Decidable (p : Prop) : Type
number of parameters: 1
fields:
  Decidable.decide : Bool
  Decidable.reflects_decide : (decide p).Reflects p
constructor:
  Decidable.intro {p : Prop} (decide : Bool) (reflects_decide : decide.Reflects p) :
Decidable p
-/
#guard_msgs in #print Decidable

/-!
`decide` 先找 `Decidable p` 的实例，把它规约成 `true`；找不到实例就报错。§1、§8 的
`deriving DecidableEq` 生成的就是 `a = b` 的实例。自定义谓词想用 `decide`，可能被两道**互相独立**的障碍
挡住，下面分开看。

**障碍一：实例合成不展开 `def`。** 谓词 `IsEvenMod` 的内容是 `n % 2 = 0`，而 `n % 2 = 0` 本身是可判定的；
但 `IsEvenMod 10` 在实例合成的眼里是一个陌生的常量应用，`def` 不会被自动展开，找不到实例。把 `def` 换成
`abbrev`（可约的缩写）后，实例合成能看穿它，`decide` 就成功了：
-/

def IsEvenMod (n : ℕ) : Prop := n % 2 = 0

/-- error: failed to synthesize
  Decidable (IsEvenMod 10)

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command. -/
#guard_msgs in
example : IsEvenMod 10 := by decide

abbrev IsEvenAbbrev (n : ℕ) : Prop := n % 2 = 0

example : IsEvenAbbrev 10 := by decide

/-!
**障碍二：存在量词没有通用的判定算法。** `IsEvenEx` 的内容是 `∃ k, n = 2 * k`，`k` 在 `ℕ` 里无界地
取值，库里没有对它的通用实例（只有有界量词的实例）。所以即使展开定义（下面第二个例子把它写成 `abbrev`），
实例仍然找不到；两个障碍都在，原例的报错只是第一个障碍的样子，换成 `abbrev` 并不能修好它：
-/

def IsEvenEx (n : ℕ) : Prop := ∃ k, n = 2 * k

/-- error: failed to synthesize
  Decidable (IsEvenEx 10)

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command. -/
#guard_msgs in
example : IsEvenEx 10 := by decide

abbrev IsEvenEx' (n : ℕ) : Prop := ∃ k, n = 2 * k

/-- error: failed to synthesize
  Decidable (IsEvenEx' 10)

Hint: Additional diagnostic information may be available using the
`set_option diagnostics true` command. -/
#guard_msgs in
example : IsEvenEx' 10 := by decide

/-!
这时要自己提供算法：`instance` 登记一个实例（第 8 章系统讲）；`DecidablePred p` 就是 `∀ a, Decidable (p a)`。
`decidable_of_iff` 用一个等价式把实例从另一个命题 `n % 2 = 0` 搬过来，等价式有两个方向：
-/

instance : DecidablePred IsEvenEx := fun n ↦
  decidable_of_iff (n % 2 = 0)
    ⟨fun h ↦ ⟨n / 2, by omega⟩,       -- `n % 2 = 0 → ∃ k, n = 2 * k`
     fun ⟨k, hk⟩ ↦ by omega⟩          -- 反方向

example : IsEvenEx 10 := by decide
example : ¬ IsEvenEx 7 := by decide

/-!
## 11. 常见错误

**1. `match` 漏了构造子。** 报错列出缺的情形：
-/

/--
error: Missing cases:
Weekday.wed
Weekday.thu
Weekday.fri
Weekday.sat
Weekday.sun
-/
#guard_msgs in
example : Weekday → ℕ
  | .mon => 1
  | .tue => 2

/-!
**2. `induction` 的分支名写错或漏写。** 分支名是所用 eliminator 的分支名：普通归纳类型（包括 `ℕ`
的 `induction`/`cases`）用构造子名（`ℕ` 是 `zero` 与 `succ`）；用 `using` 或 `fun_induction`
换了归纳原理，就要看它自己的分支名（`fun_induction` 是 `case1`、`case2`，§5；`using` 的例子见第 13 章）：
-/

/--
error: Invalid alternative name `succ'`: Expected `succ`
---
error: Alternative `succ` has not been provided
-/
#guard_msgs in
example (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ' n ih => rfl

/-!
**3. Lean 猜不出终止性。** 把 §9 的 `myGcd` 去掉 `decreasing_by`：度量 `b` 是对的，但默认策略证不出
`a % b < b`。报错很长，用 `substring := true` 只核对第一句。注意 `#guard_msgs` 不会撤销失败的
定义：报错的 `def` 仍会带着一个 `sorry` 留在环境里。所以本节会报错的反例都写成不留名字的
`example`；`example` 没有名字可供递归调用，递归函数就放进 `where` 子句（`where` 后面定义的辅助
函数可以在 `:=` 的右边使用）：
-/

/-- error: failed to prove termination, possible solutions: -/
#guard_msgs (substring := true) in
example : ℕ := myGcd2 12 18
where
  myGcd2 (a b : ℕ) : ℕ := if b = 0 then a else myGcd2 b (a % b)
  termination_by b

/-!
修法就是写出 `decreasing_by`（§9）。像 `bad` 这样根本不终止的函数没有修法，只能改算法或改成对子项
递归，Lean 的第一句报错不同：
-/

/-- error: fail to show termination for -/
#guard_msgs (substring := true) in
example : ℕ := bad 0
where bad (n : ℕ) : ℕ := bad (n + 1)

/-!
**4. 旧的 `structure … :=` 写法。** 4.14 起弃用，改用 `where`：
-/

/--
warning: `structure ... :=` has been deprecated in favor of `structure ... where`.

Note: This linter can be disabled with `set_option linter.deprecated false`
-/
#guard_msgs in
structure Old :=
  a : ℕ

/-!
## 练习

先给出练习要用的定义：列表反转 `rev`、平方和 `sumSq`，以及 `log2'`（`n` 除以 2 直到小于 2 的次数；
`decreasing_by` 只是一个 `omega`：目标 `n / 2 < n` 带条件 `¬n < 2`，`omega` 懂除以常数）。
复习前面章节的题在题干里写明章号。
-/

def rev {α : Type*} : List α → List α
  | [] => []
  | x :: xs => app (rev xs) [x]

def sumSq : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumSq n + (n + 1) * (n + 1)

def log2' (n : ℕ) : ℕ :=
  if n < 2 then 0 else log2' (n / 2) + 1
termination_by n
decreasing_by omega

/-- 练习 6.1（★）：一周七天后回到原处。提示：`cases d` 后每个分支 `rfl`。 -/
theorem ex_6_1 (d : Weekday) : d.next.next.next.next.next.next.next = d := sorry

/-- 练习 6.2（★★）：`MyNat` 加法的结合律。提示：对 `c` 归纳，`succ` 分支反复用 `MyNat.add_succ`，最后用 `ih`。 -/
theorem ex_6_2 (a b c : MyNat) : (a.add b).add c = a.add (b.add c) := sorry

/-- 练习 6.3（★★）：`toNat` 保持加法。提示：对 `b` 归纳，`simp only [MyNat.add, MyNat.toNat]` 展开后用 `omega` 收尾。 -/
theorem ex_6_3 (a b : MyNat) : (a.add b).toNat = a.toNat + b.toNat := sorry

/-- 练习 6.4（★）：列表拼接的结合律（`app` 见 §6）。 -/
theorem ex_6_4 {α : Type*} (xs ys zs : List α) :
    app (app xs ys) zs = app xs (app ys zs) := sorry

/-- 练习 6.5（★★）：反转不改变长度。提示：对 `xs` 归纳，用 `length_app` 与 `ih`。 -/
theorem ex_6_5 {α : Type*} (xs : List α) : (rev xs).length = xs.length := sorry

/-- 练习 6.6（★）：镜像两次得到原树（`Tree.mirror` 见 §3）。提示：对 `t` 归纳，`simp [Tree.mirror, ihl, ihr]`。 -/
theorem ex_6_6 {α : Type*} (t : Tree α) : t.mirror.mirror = t := sorry

/-- 练习 6.7（★★）：用 `fun_induction`（§5）证明 `sumTo n ≤ n * n`。提示：两个情形分别用 `decide` 与 `linarith`。 -/
theorem ex_6_7 (n : ℕ) : sumTo n ≤ n * n := sorry

/-- 练习 6.8（★）：复习第 3 章的 `absurd`。除数非零时 `safeDiv` 给出商。提示：对 `b` 分情况，零的情形用 `exact absurd rfl h`。 -/
theorem ex_6_8 (a b : ℕ) (h : b ≠ 0) : safeDiv a b = some (a / b) := sorry

/-- 练习 6.9（★★）：复习第 4 章的 `rcases` 与第 5 章的 `subst`。`Point3` 没有 `@[ext]`，要把两个点拆开。
提示：`rcases a with ⟨⟨x, y⟩, z⟩`，`b` 同理，用 `simp only at h₁ h₂ h₃` 化简投影，再 `subst`。 -/
theorem ex_6_9 (a b : Point3) (h₁ : a.x = b.x) (h₂ : a.y = b.y) (h₃ : a.z = b.z) :
    a = b := sorry

/-- 练习 6.10（★★）：复习第 4 章的 `by_cases`。`myGcd 0 b = b`。提示：对 `b = 0` 分情况，再用 `simp [myGcd]`。 -/
theorem ex_6_10 (b : ℕ) : myGcd 0 b = b := sorry

/-- 练习 6.11（★★）：`log2'` 小于 `n`。提示：`revert h` 把假设放回目标（与 `intro` 相反），目标变成
`1 ≤ n → log2' n < n`，这样 `fun_induction log2' n` 的归纳假设也带条件；每个情形先 `intro` 再 `omega`。 -/
theorem ex_6_11 (n : ℕ) (h : 1 ≤ n) : log2' n < n := sorry

/-- 练习 6.12（★）：复习第 3 章的 `∨` 与项模式。不用策略：用 `fun` 加嵌套模式写出证明项。 -/
theorem ex_6_12 (p q r : Prop) : (p ∨ q) ∨ r → p ∨ (q ∨ r) := sorry

/-- 练习 6.13（★★）：复习第 2 章的 `nlinarith`。平方和公式。提示：归纳，`simp [sumSq]` 展开，再 `nlinarith [ih]`。 -/
theorem ex_6_13 (n : ℕ) : 6 * sumSq n = n * (n + 1) * (2 * n + 1) := sorry

/-- 练习 6.14（★）：复习第 3 章的 `∃`。证明 `∃ k, n = 3 * k` 与 `n % 3 = 0` 等价。
提示：两个方向都用 `omega`；第二个方向要自己给出 `k`。 -/
theorem ex_6_14 (n : ℕ) : (∃ k, n = 3 * k) ↔ n % 3 = 0 := sorry

/-- 练习 6.15（★★）：给 `∃ k, n = 3 * k` 提供可判定性实例（§10）。
提示：`decidable_of_iff (n % 3 = 0)`，需要的等价式是练习 6.14 的 `.symm`。 -/
def ex_6_15 (n : ℕ) : Decidable (∃ k, n = 3 * k) := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 归纳类型 | `inductive T where \| c₁ … \| c₂ …` | 定义枚举、递归数据；自动得到 `T.rec` |
| 模式匹配、结构递归 | `match x with \| pat => rhs` | 按构造子拆开，须穷尽；调用在子项上则 `rfl`/`decide` 能算 |
| `cases` / `induction` | `induction t with \| c x ih => …` | 对构造子分情况；递归字段带归纳假设；`ℕ` 显示 `0`、`n + 1` |
| 递归函数的性质 | `f.eq_1`、`simp [f]`、`unfold f`；`fun_induction f x`（分支 `case1`…） | 展开定义；按 `f` 的递归结构归纳 |
| 命题的归纳本质 | `match h with \| .inl … \| .inr …`，`Eq.rec` | `∨` 的分情况；`=` 的替换 |
| 结构体 | `structure S where … deriving Repr`；`extends b : P` | 投影、`⟨⟩`、`{ p with }`、`@[ext]`、继承 |
| 良基递归 | `termination_by b` + `decreasing_by` | 递归不在子项上；默认不可约，`decide` 失效 |
| 绕过不可约 | `simp [f]`、`decide +kernel`、`@[semireducible]` | 后两者须度量是 `ℕ` 值 |
| `Decidable` | `decide`、`decidable_of_iff`、`deriving DecidableEq` | 判定闭命题；为自定义谓词提供实例 |

## 延伸阅读

- *Theorem Proving in Lean 4*：第 7 章「Inductive Types」、第 8 章「Induction and Recursion」、
  第 9 章「Structures and Records」。
- *Functional Programming in Lean*：第 1 章「Structures」与「Datatypes, Patterns and Recursion」。
- *Lean Language Reference* 4.35.0：「Definitions → Recursive Definitions」
  （`https://lean-lang.org/doc/reference/4.35.0/Definitions/Recursive-Definitions/`），含结构递归、
  良基递归、终止性证明与可约性；「The Type System → Inductive Types」。
- 源码：`Init/Prelude.lean`（`Nat`、`List`、`Option`、`Decidable`、`Bool.Reflects`）、
  `Init/Data/Nat/Basic.lean`（`Nat.recAux`、`Nat.casesAuxOn`）。
- 本书第 5 章（`simp`、`decide` 的边界与定义相等）、第 8 章（`Decidable` 与经典逻辑）、
  第 13 章（强归纳与 `induction … generalizing`）、第 25 章（`fun_induction`、`decide +kernel` 与程序验证）、
  第 28 章（归纳类型与递归子的内核机制）。
-/

end Lean4Learn.Ch06

end
