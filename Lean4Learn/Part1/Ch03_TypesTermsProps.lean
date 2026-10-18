module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-!
# 第 3 章　类型、项与命题

本章讲清 Lean 最小必要的底层图景：一切对象都是 term（项），每个项都有一个 type（类型）；
proposition（命题）本身也是类型，proof（证明）就是这个类型的项。这条原则叫
Curry–Howard correspondence（柯里–霍华德对应），*Hitchhiker's Guide to Logical Verification*
（§4.7）称之为 PAT 原则。读完本章，你能直接写出 proof term（证明项）来证明命题逻辑与谓词逻辑
的基本定理，也能读懂 `#check` 打印出来的类型。

本章以 term-mode（项模式）为主：证明是一个直接写下的项。tactic-mode（策略模式）即 `by …`
从 §4 末尾起零星出现（嵌在项里，或作为同一证明的对照写法），第 4 章系统讲解。

## 学习目标
- 用 `#check` 查看项的类型，区分「项」「类型」「命题」「证明」；会写 lambda abstraction（λ 抽象）
  `fun x ↦ …`，理解函数应用与 currying（柯里化）；
- 区分 `Prop` 与 `Type`，知道 `Sort`、`Type*` 与 `Type u` 的最小必要含义；理解 `theorem` 与 `def`
  都是「名字 + 类型 + 项」的声明；会用 implicit argument（隐式参数）`{}` 与 `@`；
- 对 `→ ∧ ∨ ¬ ↔ ∀ ∃ True False` 各写出 introduction（引入）与 elimination（消去）的证明项；
- 在项里用 `have`、`show … from`、`‹p›`，知道 `by` 只是构造项的另一种写法，会用 `show_term`
  看策略证明拼出的项，用 `#print axioms` 看依赖的公理（预览）；
- 用 proof irrelevance（证明无关性）解释「同一命题的两个证明可以互换」，以及为什么命题的
  证明不能用来产出数据。

## 前置知识
第 1 章（`#check`、`#eval`、文件头与 `#guard_msgs`）；Natural Number Game 里的 `rfl`；第 2 章的
`omega`、`norm_num`、`ring`（练习会回头用到）。
-/

@[expose] public section

namespace Lean4Learn.Ch03

/-!
## 1. 一切皆有类型

Lean 里写出的每个式子，经 elaborator（精译器；另译繁饰器）补全并检查——这一过程叫
elaboration（精译）——之后都是一个项，每个项都有一个类型。`e : T` 读作「`e` 的类型是 `T`」。
`#check` 把得到的类型打印到 infoview（信息视图）中；`#guard_msgs` 在编译时核对这段输出，
所以下面每个 `/-- info: … -/` 在空白归一化后都与真实输出一致。

> 撞词提示：这里的「项」是类型论的 term，与级数的「通项」「第 n 项」无关；元编程里的
> `Expr` 称「表达式」（第 27 章）。
-/

/-- info: 1 : ℕ -/ #guard_msgs in #check 1
/-- info: (1, "a") : ℕ × String -/ #guard_msgs in #check (1, "a")
/-- info: Bool.true : Bool -/ #guard_msgs in #check true

/-!
没有写类型时，数字 `1` 默认是 `ℕ`（`ℕ` 是 Mathlib 为 `Nat` 引入的记号，来自
`Mathlib.Data.Nat.Notation`）；`ℕ × String` 是数对的类型。用 type ascription（类型标注）
`(e : T)` 可以要求精译器把 `e` 当作 `T` 的项；同一个数字字面量在不同类型里是不同的项。
-/

/-- info: 1 : Float -/ #guard_msgs in #check (1 : Float)

/-!
`#check c` 对标识符按声明的签名显示全名：`#check true` 打印 `Bool.true`，`#check Nat` 打印
`Nat`（常量名不套用 `ℕ` 记号）。加括号 `#check (c)` 则把它当普通项，打印 `c : T`（§4 用到）。

类型也是项：`ℕ : Type`，`Type : Type 1`，……（原因见 §4）；命题的类型则是 `Prop`。
`Prop` 是装「命题」的那个 universe（宇宙）：`1 + 1 = 2` 是一个项，它的类型是 `Prop`——它是
一个命题，而不是一个数。命题可以是假的：`1 + 1 = 3` 同样是 `Prop` 的项。
-/

/-- info: Nat : Type -/ #guard_msgs in #check Nat
/-- info: Type : Type 1 -/ #guard_msgs in #check Type
/-- info: Prop : Type -/ #guard_msgs in #check Prop
/-- info: 1 + 1 = 2 : Prop -/ #guard_msgs in #check (1 + 1 = 2)
/-- info: 1 + 1 = 3 : Prop -/ #guard_msgs in #check (1 + 1 = 3)

/-!
## 2. 函数类型、应用与柯里化

从 `α` 到 `β` 的函数的类型写作 `α → β`。写出一个函数用 `fun x ↦ e`（`↦` 的输入方法见第 1 章，
也可写 `=>`；本书源码一律不写 `λ`）。把函数作用在参数上只需并排书写 `f a`，不加括号。函数本身
也是值，可以当参数传递（第二个 `#check`）。
-/

/-- info: fun x ↦ x + 1 : ℕ → ℕ -/
#guard_msgs in #check fun (x : ℕ) ↦ x + 1
/-- info: fun f ↦ f 0 : (ℕ → ℕ) → ℕ -/
#guard_msgs in #check fun (f : ℕ → ℕ) ↦ f 0

/-!
应用一个 `fun`，得到代入后的结果，这一步叫 β-reduction（β 规约）。`rfl` 是 `a = a` 的证明：
精译器检查 `=` 两边是否 definitional equality（定义相等，第 5 章详讲），相等才接受 `rfl`。
定义相等包括 β 规约，也包括具体数值的计算：第一个例子要先 β 规约成 `2 + 1 = 3` 再算出 `2 + 1`；
第二个例子两边展开后是同一个 `fun`（`(· + 1)` 是 `fun x ↦ x + 1` 的简写，这里的 `·` 与第 4 章
聚焦用的 `·` 无关）：
-/

example : (fun x : ℕ ↦ x + 1) 2 = 3 := rfl
example : (· + 1 : ℕ → ℕ) = fun x ↦ x + 1 := rfl

/-!
**柯里化**：在类型论层面 Lean 没有「多参数函数」，`ℕ → ℕ → ℕ` 读作 `ℕ → (ℕ → ℕ)`（`→` 右结合）：
接收一个数，返回「再接收一个数的函数」。因此只给部分参数就得到一个函数。
-/

example : (ℕ → ℕ → ℕ) = (ℕ → (ℕ → ℕ)) := rfl

-- 冒号左边的 `(a b c : ℕ)` 是右边 `fun a b c ↦ …` 的简写：
def addThree (a b c : ℕ) : ℕ := a + b + c

/-- info: Lean4Learn.Ch03.addThree (a b c : ℕ) : ℕ -/ #guard_msgs in #check addThree
example : addThree = fun a b c ↦ a + b + c := rfl

/-- info: addThree 1 2 : ℕ → ℕ -/ #guard_msgs in #check addThree 1 2

-- 对照：「取一个数对」的函数类型是 `ℕ × ℕ → ℕ`，与 `ℕ → ℕ → ℕ` 不同；
-- 数对的两个 field（字段）是 `Prod.fst`、`Prod.snd`，简写为 `p.1`、`p.2`（`And` 的 `.1/.2` 见 §8.2）：
def addPair (p : ℕ × ℕ) : ℕ := p.1 + p.2

/-!
## 3. `def`、`theorem`、`example` 与 `lemma`

`def` 给一个项起名字；`example` 检查一个项但不留名字；`theorem` 同样给项起名字，但要求类型
必须是命题，证明本身仍是一个项。因为证明就是项，给证明起名、反复引用，与给数据起名、反复引用
是同一件事。Mathlib 提供的 `lemma` 与 `theorem` 同义。`theorem` 的类型不是命题时，精译器报错：
-/

/--
error: type of theorem `Lean4Learn.Ch03.bad` is not a proposition
  ℕ
-/
#guard_msgs in theorem bad : ℕ := 3

theorem two_eq_thm : 1 + 1 = 2 := rfl

lemma two_eq_lemma : 1 + 1 = 2 := rfl

/-!
`#print` 把声明的「名字 + 类型 + 值」并排打印：`def` 的值是一个函数，`theorem` 的值是一个证明，
`lemma` 与 `theorem` 打印出来相同。方括号里是自动加上的 attribute（属性）：`defeq` 通常因值
写作 `:= rfl` 而加，`expose` 来自文件头的 `@[expose] public section`（第 1 章）；这里不需要理解它们。
-/

/-- info: @[expose] def Lean4Learn.Ch03.addThree : ℕ → ℕ → ℕ → ℕ := fun a b c ↦ a + b + c -/
#guard_msgs in #print addThree
/-- info: @[defeq] theorem Lean4Learn.Ch03.two_eq_thm : 1 + 1 = 2 := rfl -/
#guard_msgs in #print two_eq_thm
/-- info: @[defeq] theorem Lean4Learn.Ch03.two_eq_lemma : 1 + 1 = 2 := rfl -/
#guard_msgs in #print two_eq_lemma

/-!
## 4. `Prop` 与 `Type`

读完这一节，你要能对任意式子说出它属于哪一层。下面的表把本章会遇到的四个层次排在一起。

| 层次 | 例子 | 它的类型 |
|---|---|---|
| 证明 | `rfl : 1 + 1 = 2` | 命题 `1 + 1 = 2` |
| 命题 | `1 + 1 = 2` | `Prop` |
| 数据 | `(3 : ℕ)` | 类型 `ℕ` |
| 类型 | `ℕ` | `Type` |

表里是两条链：证明的类型是命题，命题的类型是 `Prop`；数据的类型是类型，类型的类型是 `Type`。

`Prop`、`Type` 都是 `Sort u` 的特例，`u` 是 universe level（宇宙层级）：一个自然数，或 §6、§7
里的层级变量。`Prop` 就是 `Sort 0`，`Type u` 就是 `Sort (u + 1)`，所以 `Type` 是 `Sort 1`；
每一层又是下一层的项：`Sort u : Sort (u + 1)`，这就是 §1 里 `Prop : Type`、`Type : Type 1` 的来由。
-/

example : Prop = Sort 0 := rfl

/-- info: Type 2 : Type 3 -/ #guard_msgs in #check Sort 3      -- `Sort 3` 就是 `Type 2`

/-!
凡是 `α : Sort u` 的 `α` 都可以叫类型；当 `u = 0`（即 `α : Prop`）时它叫命题。一个类型的项
叫它的 inhabitant（居留者），命题的居留者叫证明。所以命题本身是类型，证明是这个类型的项
（`two_eq_thm` 是 §3 里的定理）：
-/

/-- info: two_eq_thm : 1 + 1 = 2 -/ #guard_msgs in #check (two_eq_thm)

-- 带参数的命题就是「谓词」，其类型是 `ℕ → Prop`：
def IsPos (n : ℕ) : Prop := 0 < n

/-- info: IsPos : ℕ → Prop -/ #guard_msgs in #check (IsPos : ℕ → Prop)

/-!
精译器检查类型时比较的是定义相等，不是字面相同：
`IsPos 3` 展开后就是 `0 < 3`，所以 `0 < 3` 的证明也被接受为 `IsPos 3` 的证明，反过来也一样。
-/

example : IsPos 3 := (by norm_num : 0 < 3)
example (h : IsPos 3) : 0 < 3 := h

/-!
## 5. 命题即类型，证明即项（Curry–Howard）

先看想法本身。constructive logic（构造性逻辑）这样解读联结词（BHK 解释，即
Brouwer–Heyting–Kolmogorov 解释）：`p → q` 的证明是一个规则，把 `p` 的证明变成 `q` 的证明；
`p ∧ q` 的证明是一对证明；`p ∨ q` 的证明是 `p` 的证明或 `q` 的证明，并标明是哪一边。把「规则」
看作函数，「一对」看作 product type（积类型），「标明哪一边」看作 sum type（和类型），命题就
成了类型。（Lean 里 `∨` 是 `Prop` 中的 `Or`，不是 `Sum`：证明无关性使得无法从证明里读出是
哪一边，见 §9 与 §12 第 3 条。）

对每个联结词要会两件事：introduction（引入）是怎样造出它的证明，elimination（消去）是怎样
使用它的证明。下面是最小的例子：**hypothesis（假设）就是变量**，证明 `p → q` 时，`hp : p` 是一个
类型为命题 `p` 的局部变量；调用假设 `hpq : p → q` 就是函数应用。于是肯定前件（modus ponens）
不是推理规则，只是函数调用：
-/

example (p q : Prop) (hp : p) (hpq : p → q) : q := hpq hp
-- 上下文：hp : p, hpq : p → q    ⊢ q

-- 同一个命题的 term-mode 与 tactic-mode 版本。`by` 之后的写法第 4 章细讲：
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  -- hp : p, hpq : p → q
  -- ⊢ q
  exact hpq hp

/-!
各联结词的引入与消去在 §8 逐条写出，汇总见「小结」。

本章为讲解而重写的逻辑定理，名字带一撇 `'`（如 `and_comm'` 对应核心库里的 `and_comm`）：
这是本书的约定，免得在本命名空间里遮蔽库里的同名定理，并非推荐的命名方式。

## 6. 隐式参数与 `@`

如果每次调用 `id` 都要手写类型 `α`，既啰嗦又多余；隐式参数让精译器去推。`id (3 : ℕ)` 并不需要
写出类型：`id : α → α` 的类型参数 `α` 由参数 `(3 : ℕ)` 的类型推出。花括号
`{α : Sort u}` 绑定的是 implicit argument（隐式参数），圆括号 `(x : α)` 绑定的是 explicit
argument（显式参数）。在函数名前加 `@` 让所有参数都变成显式：
-/

/-- info: @id : {α : Sort u_1} → α → α -/ #guard_msgs in #check @id
/-- info: id 3 : ℕ -/ #guard_msgs in #check id (3 : ℕ)
/-- info: id 3 : ℕ -/ #guard_msgs in #check @id ℕ 3   -- 与上一行是同一个项

/-!
（`#check @id` 里的 `u_1` 是 `#check` 重新取的名字，核心库里声明的是 `u`，见 §7。）
`id` 的 `α` 是 `Sort _`，所以对命题也适用：`h : p` 经 `id` 仍是 `p` 的证明。自己写定理时，
`{p q : Prop}` 同理：`p q` 由后面显式参数的类型或期望类型推出，使用时不必传入。再用 `@` 看一次
`Eq.symm` 的参数顺序（练习 3.3 用到）：
-/

example (p : Prop) (h : p) : p := id h

theorem imp_refl' {p : Prop} : p → p := fun hp ↦ hp

/-- info: @imp_refl' : ∀ {p : Prop}, p → p -/ #guard_msgs in #check @imp_refl'
/-- info: @Eq.symm : ∀ {α : Sort u_1} {a b : α}, a = b → b = a -/ #guard_msgs in #check @Eq.symm

/-!
方括号 `[ ]` 绑定的是 instance-implicit argument（实例隐式参数），第 8 章讲。

## 7. 宇宙：`Type u` 与 `Type*`

Mathlib 里几乎每个泛型定义都写 `{α : Type*}`，本节解释它；`Sort`、层级与 `Type u = Sort (u + 1)`
已在 §4 讲过，更细的性质（`Prop` 是 impredicative（非直谓的）等）留到第 28 章。
Lean 没有 cumulativity：`ℕ : Type` 不会自动变成 `Type 1` 的项，层级必须对得上：
-/

/--
error: Type mismatch
  ℕ
has type
  Type
of sort `Type 1` but is expected to have type
  Type 1
of sort `Type 2`
-/
#guard_msgs in
example : Type 1 := ℕ

/-!
要写对所有宇宙层级都成立的定义，就要 universe polymorphism（宇宙多态）：先写 `universe u` 再用
`Type u`，或用 Mathlib 的 `Type*`（展开成一个新的宇宙变量，不必声明）。本书统一用 `Type*`。
裸标识符的 `#check` 把宇宙参数写在名字后面：`myId` 得到自动生成的 `u_1`，核心库的 `id` 是 `u`：
-/

def myId {α : Type*} (a : α) : α := a

/-- info: Lean4Learn.Ch03.myId.{u_1} {α : Type u_1} (a : α) : α -/ #guard_msgs in #check myId
/-- info: id.{u} {α : Sort u} (a : α) : α -/ #guard_msgs in #check id

/-!
`myId` 能用在 `α := ℕ` 上，但 `Type u` 里的每个类型都不是命题（命题 `p : Prop = Sort 0`，而
`Type u = Sort (u + 1)`），所以 `α := p` 不合法，`myId` 不能用在证明上；`id` 的 `Sort u` 可以
（§6）。下面是失败的例子。输出里的 `?_` 是 metavariable（元变量），即精译器还没确定的部分（与
第 4 章 `refine` 里手写的 `?_` 洞共用符号，别混淆）；`set_option pp.mvars false in` 只是为了让
输出里没有元变量的编号：
-/

example : myId (3 : ℕ) = 3 := rfl

/--
error: Type mismatch
  myId ?_
has type
  ?_
of sort `Type _` but is expected to have type
  p
of sort `Prop`
-/
#guard_msgs in
set_option pp.mvars false in
example {p : Prop} (h : p) : p := myId h

/-!
## 8. 项模式证明各联结词

写证明项，就是回答两个问题：这个联结词的证明怎样造，又怎样用。证明里经常出现的 `p q r : Prop` 用 `{}` 绑定，使用时由后面显式参数的类型或期望类型推出。`∧ ∨ ¬ ↔ ∃`
的策略写法见第 4 章 §3–§6，那里的练习 4.1–4.5 就是本章练习的策略版；这里只对 `→`（§5）与 `∀`
（§8.6）并排给出策略版。

### 8.1 蕴含 `→`
**引入**：`fun h ↦ …`；**消去**：函数应用。term 版本里没有目标可看，所以在注释里手写 `fun` 的
主体要证的 goal（目标）：`⊢` 右边是目标，左边是 (local) context（上下文）里的假设（第 4 章系统讲）：
-/

theorem imp_trans' {p q r : Prop} : (p → q) → (q → r) → p → r :=
  fun hpq hqr hp ↦ hqr (hpq hp)
  -- 在 `fun` 的主体里：hpq : p → q, hqr : q → r, hp : p
  -- ⊢ r

/-!
### 8.2 合取 `∧`
`And` 是 structure（结构体），有一个 constructor（构造子）`And.intro` 和两个 field（字段）`left`、
`right`。**引入**：anonymous constructor（匿名构造子）`⟨hp, hq⟩`，它依赖期望类型来决定具体的构造子
（反例见 §12 第 2 条）；
**消去**：projection（投影）`h.1`、`h.2`（第一、第二个字段，即 `h.left`、`h.right`），或在
`fun` 里直接写模式 `fun ⟨hp, hq⟩ ↦ …`。后者是 pattern matching（模式匹配）：把参数按构造子拆开并给
各部分命名，第 6 章系统讲。

`h.left` 这类写法叫 dot notation（点记号）：`h : And p q` 的类型头部是 `And`，所以 `h.left`
去 `And.` 命名空间里找 `left`，即 `And.left h`。同理 `h : a < b` 的头部是 `LT.lt`，`h.le` 即
`LT.lt.le h`（第 2 章用过）。一般地，`h` 被放进 `T.f` 的第一个类型头部为 `T` 的显式参数。
-/

/-- info: @And.intro : ∀ {a b : Prop}, a → b → a ∧ b -/ #guard_msgs in #check @And.intro

example {p q : Prop} (h : p ∧ q) : p := h.left
example (a b : ℕ) (h : a < b) : a ≤ b := h.le

theorem and_swap' {p q : Prop} : p ∧ q → q ∧ p :=
  fun h ↦ ⟨h.2, h.1⟩
  -- 在 `fun` 的主体里：h : p ∧ q
  -- ⊢ q ∧ p

-- 模式 `⟨hp, hq⟩` 把参数拆开；多层合取向右嵌套，`⟨a, b, c⟩` 是 `⟨a, ⟨b, c⟩⟩` 的简写：
theorem and_assoc' {p q r : Prop} : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun ⟨⟨hp, hq⟩, hr⟩ ↦ ⟨hp, hq, hr⟩
  -- 在 `fun` 的主体里：hp : p, hq : q, hr : r
  -- ⊢ p ∧ q ∧ r

/-!
### 8.3 析取 `∨`
`Or` 是有两个构造子的 inductive type（归纳类型）。**引入**：`Or.inl hp`、`Or.inr hq`；**消去**：
`Or.elim h f g`（两个分支都要处理），或 `match`。
-/

-- `h.elim` 需要 `p → q ∨ p` 与 `q → q ∨ p`，恰好是 `Or.inr` 与 `Or.inl`：
theorem or_swap' {p q : Prop} : p ∨ q → q ∨ p :=
  fun h ↦ h.elim Or.inr Or.inl
  -- 在 `fun` 的主体里：h : p ∨ q
  -- ⊢ q ∨ p

/-!
`match h with | Or.inl hp => … | Or.inr hq => …` 对每个构造子写一种情形，模式可以嵌套
（第 6 章系统讲；策略版是 `rcases h with hp | hq`，第 4 章讲）：
-/

theorem or_assoc' {p q r : Prop} : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
  fun h ↦ match h with
    -- h : (p ∨ q) ∨ r，每个分支各有一个假设，目标都是 p ∨ (q ∨ r)：
    | Or.inl (Or.inl hp) => Or.inl hp          -- hp : p
    | Or.inl (Or.inr hq) => Or.inr (Or.inl hq) -- hq : q
    | Or.inr hr => Or.inr (Or.inr hr)          -- hr : r

/-!
### 8.4 `True`、`False` 与否定 `¬`
`True` 有一个构造子 `True.intro`，核心库另给了同类型的定理 `trivial`（下面两个 `#check`）；
`False` 没有构造子，因此没有直接造出它的证明的办法。若 Lean 的逻辑一致，则不含 `sorry`、
不加额外公理的封闭证明不存在（这是元定理，这里不演示）。`¬p` 就是 `p → False`，
所以**引入**是 `fun hp ↦ …`（假设 `p` 推出矛盾），**消去**是把 `hnp : ¬p` 应用到 `hp : p` 上得到
`False`。从 `False` 可推出任何东西：`False.elim`；`absurd hp hnp` 是同一件事的两参数写法。
-/

/-- info: True.intro : True -/ #guard_msgs in #check True.intro
/-- info: trivial : True -/ #guard_msgs in #check trivial

example (p : Prop) : (¬p) = (p → False) := rfl
example {p q : Prop} (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- `False.elim` 可以消去到任意 `Sort`，包括数据类型：
example (h : False) : ℕ := h.elim

theorem not_not_intro' {p : Prop} : p → ¬¬p :=
  fun hp hnp ↦ hnp hp
  -- 在 `fun` 的主体里：hp : p, hnp : ¬p
  -- ⊢ False

/-!
### 8.5 双向蕴含 `↔`
`Iff` 是有两个字段 `mp`、`mpr` 的结构体（`mp` 即 modus ponens，`mpr` 是反方向），
**引入** `⟨mp, mpr⟩`，**消去** `h.mp`、`h.mpr`。
-/

theorem and_comm' {p q : Prop} : p ∧ q ↔ q ∧ p :=
  ⟨fun ⟨hp, hq⟩ ↦ ⟨hq, hp⟩, fun ⟨hq, hp⟩ ↦ ⟨hp, hq⟩⟩
  -- 两个分支的目标：⊢ p ∧ q → q ∧ p 与 ⊢ q ∧ p → p ∧ q

example {p q : Prop} (h : p ↔ q) (hp : p) : q := h.mp hp

-- 逻辑等价 `↔` 与相等 `=` 的桥梁是公理 propositional extensionality（命题外延性）`propext`：
example {p q : Prop} (h : p ↔ q) : p = q := propext h

/-!
### 8.6 全称量词 `∀`
`∀ x : α, p x` 就是函数类型 `(x : α) → p x`：返回类型 `p x` 依赖于参数 `x`，这叫 dependent
function type（依值函数类型，也叫 Π 类型，细节第 28 章）。
**引入**：`fun x ↦ …`；**消去**：应用 `h a`（把一般结论特化到 `a`）。蕴含 `p → q` 是
`∀ _ : p, q` 的特例，两者定义相等（见下面的 `rfl`）。
-/

example : ∀ n : ℕ, n + 0 = n := fun n ↦ Nat.add_zero n

example : ∀ n : ℕ, n + 0 = n := by
  intro n
  -- n : ℕ
  -- ⊢ n + 0 = n
  exact Nat.add_zero n

example (p q : Prop) : (∀ _ : p, q) = (p → q) := rfl
example (p q : ℕ → Prop) (h : ∀ x, p x → q x) (hp : p 3) : q 3 := h 3 hp

/-!
### 8.7 存在量词 `∃`
`Exists` 是归纳类型，只有一个构造子 `Exists.intro`，带两个字段：witness（见证）`w : α` 与证明 `h : p w`。
**引入**：`⟨w, h⟩`（或 `Exists.intro w h`）；**消去**：`Exists.elim`，或对 `fun`/`match` 使用模式
`⟨w, hw⟩`。第 4 章的 `obtain ⟨w, hw⟩ := h` 与 `use w` 是它的策略版本。`Exists.elim` 的结论必须
是命题，原因见 §9。
-/

example : ∃ n : ℕ, n + 3 = 5 := ⟨2, rfl⟩

theorem exists_imp' {α : Type*} {p : α → Prop} {q : Prop} :
    (∃ x, p x) → (∀ x, p x → q) → q :=
  fun h h' ↦ h.elim h'
  -- h : ∃ x, p x, h' : ∀ x, p x → q；`h.elim` 即 `Exists.elim h`，要的第二个参数正是 `h'` 的类型
  -- ⊢ q

-- 同一个命题，用模式 `⟨w, hw⟩` 拆开 `∃`：
example {α : Type*} {p : α → Prop} {q : Prop} : (∃ x, p x) → (∀ x, p x → q) → q :=
  fun ⟨w, hw⟩ h ↦ h w hw
-- 在 `fun` 的主体里：w : α, hw : p w, h : ∀ x, p x → q
-- ⊢ q

/-!
### 8.8 经典逻辑与公理
`¬¬p → p` 要用 classical logic（经典逻辑），它借助 axiom（公理）：`Classical.byContradiction`
（把 `¬p → False` 变成 `p`，见 `dne'`）是一条由公理推出的定理（第 4 章 §7 系统讲）。
`#print axioms` 列出一个定理依赖的全部公理（预览，机制见第 28 章）：`not_not_intro'` 不依赖
任何公理，`dne'` 依赖三条，其中 `propext` 见 §8.5。
-/

theorem dne' {p : Prop} : ¬¬p → p :=
  fun h ↦ Classical.byContradiction h

/-- info: 'Lean4Learn.Ch03.not_not_intro'' does not depend on any axioms -/
#guard_msgs in #print axioms not_not_intro'
/-- info: 'Lean4Learn.Ch03.dne'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms dne'

/-!
## 9. 证明无关性

**proof irrelevance**：同一命题的任意两个证明定义相等，所以证明可以互换，具体是哪一个证明不重要。
-/

example {p : Prop} (h₁ h₂ : p) : h₁ = h₂ := rfl

theorem pf₁ : 1 + 1 = 2 := rfl

theorem pf₂ : 1 + 1 = 2 := by norm_num

example : pf₁ = pf₂ := rfl

/-!
**命题只能消去到命题。** `Exists.elim` 的结论 `b` 必须是命题（`{b : Prop}`，见下面的 `#check`）：
一般地，不能凭一个命题的证明去产生数据。`False`、`And` 是少数例外（至多一个构造子、字段全是证明，
精确条件见第 28 章），见 §8.4 的 `h.elim : ℕ` 与下面的 `match`。`Or`（两个构造子）与 `Exists`
（字段 `w : α` 不是证明）不是例外，后果见 §12 第 3 条。
-/

/--
info: @Exists.elim : ∀ {α : Sort u_1} {p : α → Prop} {b : Prop},
(∃ x, p x) → (∀ (a : α), p a → b) → b
-/
#guard_msgs in #check @Exists.elim

example {p q : Prop} (h : p ∧ q) : ℕ :=
  match h with
  | ⟨_, _⟩ => 5

/-!
## 10. 项模式的工具箱

长一点的证明项需要局部命名与类型提示：`have` 在项里引入局部假设，`show T from e` 与
`(e : T)` 标注类型，`show T by tac` 把目标改写成同样定义相等的 `T` 再用策略证明，`‹p›`
按类型从上下文取假设，`by` 可以嵌在项里处理计算性的细节。
-/

example {p q : Prop} (hp : p) (hq : q) : p ∧ q :=
  have h : q ∧ p := ⟨hq, hp⟩
  -- 此后上下文里多了 h : q ∧ p
  ⟨h.2, h.1⟩

example {p q : Prop} (hp : p) (hq : q) : p ∧ q := show p ∧ q from ⟨hp, hq⟩
example {p q : Prop} (hp : p) (hq : q) : p ∧ q := ⟨‹p›, ‹q›⟩
example : ∀ n : ℕ, (fun m : ℕ ↦ m + 0) n = n := fun n ↦ show n + 0 = n by omega

-- 项里嵌 `by`：结构用项写，计算细节交给第 2 章的工具。
example : ∀ a b : ℕ, (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := fun a b ↦ by ring

/-!
## 11. 策略证明就是在构造项

`by` 引入的策略模式里，策略一步步改写 goal，最终拼成一个项。`show_term` 把拼出来的项
打印出来（`Try this:` 是建议信息的前缀，不是错误）：
-/

/--
info: Try this:
  [apply] exact fun h ↦ ⟨h.right, h.left⟩
-/
#guard_msgs in
example {p q : Prop} : p ∧ q → q ∧ p := by
  show_term
    intro h
    exact ⟨h.2, h.1⟩

/-!
打印出的项与 §8.2 手写的 `fun h ↦ ⟨h.2, h.1⟩` 相同，只是 `.2` 显示成 `.right`（同一个项）。
所以「用策略证明」和「写项」不是两种东西：前者是构造后者的另一种写法。

## 12. 常见错误

**1. 假设的类型对不上。** 精译器检查的是定义相等：`IsPos 3` 与 `0 < 3` 因为 `IsPos` 可展开
而相等（§4）；但 `p` 与 `q` 是两个不同的变量，不相等。两个典型的错误信息（项的类型不符；函数
应用中参数的类型不符）：
-/

/--
error: Type mismatch
  hp
has type
  p
but is expected to have type
  q
-/
#guard_msgs in
example {p q : Prop} (hp : p) : q := hp

/--
error: Application type mismatch: The argument
  hr
has type
  r
but is expected to have type
  p
in the application
  hpq hr
-/
#guard_msgs in
example {p q r : Prop} (hpq : p → q) (hr : r) : q := hpq hr

/-!
**2. 匿名构造子没有期望类型。** `⟨1, 2⟩` 本身不说明它是积还是别的结构：
-/

/-- error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined -/
#guard_msgs in
example := ⟨1, 2⟩

/-!
**3. 用命题的证明去产出数据。** 假如能凭 `h : p ∨ q` 返回 `Bool`，函数就能「看出」`h` 是
`Or.inl` 还是 `Or.inr`。但当 `hp : p` 与 `hq : q` 同时成立时，`Or.inl hp` 与 `Or.inr hq` 是
同一命题的两个证明，由证明无关性（§9）它们定义相等，函数却要对它们返回 `true` 与 `false`，
矛盾。所以 Lean 禁止 `Or` 消去到数据（`Exists` 同理，§9 的 `Exists.elim`）。完整的错误信息以
`Tactic `cases` failed with a nested error:` 开头，内层是 `Tactic `induction` failed:` 加下面
的关键一句，后面还跟着当前 goal，很长；`substring := true` 只要求下面这两行出现在输出里：
-/

/--
Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Or.casesOn` can only eliminate into `Prop`
-/
#guard_msgs (substring := true) in
def whichSide {p q : Prop} (h : p ∨ q) : Bool :=
  match h with
  | Or.inl _ => true
  | Or.inr _ => false

/-!
## 练习

下列各题用项模式完成（计算细节可以嵌 `by`）。★ 直接应用，★★ 综合两个想法，★★★ 需要新想法。
`ex_3_1` 至 `ex_3_9` 练习本章的逻辑与函数（其中 `ex_3_3` 回顾第 1 章的 `#check`），`ex_3_10`
至 `ex_3_14` 回顾第 2 章的计算工具，`ex_3_15` 是经典逻辑。
-/

/-- 练习 3.1（★）：函数复合（柯里化的形式）。提示：三个 `fun` 参数。 -/
def ex_3_1 {α β γ : Type*} : (β → γ) → (α → β) → α → γ := sorry

/-- 练习 3.2（★）：蕴含与合取。 -/
theorem ex_3_2 {p q r : Prop} : (p → q) → (p → r) → p → q ∧ r := sorry

/-- 练习 3.3（★）：回顾第 1 章的 `#check`：用 `@Eq.symm` 并显式写出全部参数来证明。提示：先查签名。 -/
theorem ex_3_3 (a b : ℕ) (h : a = b) : b = a := sorry

/-- 练习 3.4（★）：把「取两个参数」的函数改成「取一个数对」的函数。提示：见 §2 的 `p.1`、`p.2`。 -/
def ex_3_4 {α β γ : Type*} : (α → β → γ) → α × β → γ := sorry

/-- 练习 3.5（★）：析取的结合律（另一个方向）。 -/
theorem ex_3_5 {p q r : Prop} : p ∨ (q ∨ r) → (p ∨ q) ∨ r := sorry

/-- 练习 3.6（★★）：析取三段论。提示：对 `Or.elim` 的第一个分支用 `absurd`（§8.4）。 -/
theorem ex_3_6 {p q : Prop} : ¬p → p ∨ q → q := sorry

/-- 练习 3.7（★★）：合取对析取的分配律。 -/
theorem ex_3_7 {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry

/-- 练习 3.8（★★）：双向蕴含的消去与否定。提示：先用 `have` 得到 `¬p`。 -/
theorem ex_3_8 {p : Prop} : ¬(p ↔ ¬p) := sorry

/-- 练习 3.9（★★）：存在量词与析取。 -/
theorem ex_3_9 {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

/-- 练习 3.10（★）：回顾第 2 章：给出见证，等式用 `norm_num`。 -/
theorem ex_3_10 : ∃ n : ℕ, n * n = 49 ∧ n + 1 = 8 := sorry

/-- 练习 3.11（★★）：回顾第 2 章的 `omega`：否定与存在量词。提示：`¬` 是函数，见证用模式拆开（§8.7）。 -/
theorem ex_3_11 : ¬∃ n : ℕ, n + 1 = 0 := sorry

/-- 练习 3.12（★★）：回顾第 2 章的 `ring`：β 规约。提示：用项 `show … by ring`（§10）。 -/
theorem ex_3_12 : ∀ a : ℕ, (fun f : ℕ → ℕ ↦ f (f a)) (· * 3) = 9 * a := sorry

/-- 练习 3.13（★★）：回顾第 2 章的 `omega`：先假设再构造见证。 -/
theorem ex_3_13 : ∀ n : ℕ, n < 5 → ∃ k : ℕ, k + n = 5 := sorry

/-- 练习 3.14（★★）：回顾第 2 章的 `omega`，并练习 ∀ 消去。提示：把 `h` 特化到 `0` 与 `1`。 -/
theorem ex_3_14 (f : ℕ → ℕ) (h : ∀ n, f (n + 1) = f n + 2) : f 2 = f 0 + 4 := sorry

/-- 练习 3.15（★★★）：经典逻辑，提示：`Classical.byContradiction`（§8.8），要用两次，一层套一层。 -/
theorem ex_3_15 {α : Type*} {p : α → Prop} : ¬(∀ x, p x) → ∃ x, ¬p x := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 类型与项 | `e : T`，`#check e` | 查看任何东西的类型；`(e : T)` 要求精译器按 `T` 理解 |
| 函数 | `fun x ↦ e`，`f a`，`α → β` | 构造与应用函数；多参数即柯里化，可只给部分参数 |
| `Prop` / `Type` | `Sort 0` / `Sort (u+1)` | 命题放 `Prop`，数据放 `Type`；`Sort u : Sort (u+1)` |
| `theorem` | `theorem T : P := proof` | 给命题的证明起名；类型不是命题时用 `def`；`lemma` 同义 |
| 点记号 | `h : T …` 时 `h.f` 找 `T.f`（§8.2） | 取字段或套用同名定理：`h.left`、`h.elim`、`h.le` |
| 隐式参数 | `{α}`，`@f` | 参数可由后文推出时用 `{}`；想看或手填全部参数时用 `@` |
| 宇宙 | `Type*`，`universe u` 加 `Type u` | 定义要对所有宇宙层级成立时 |
| `→` | `fun h ↦ …`；`h a` | 证 `p → q` 就 `fun`；用 `h : p → q` 就应用 |
| `∧` | `⟨a, b⟩`；`h.1`，`h.2` | 证 `p ∧ q` 用匿名构造子；用 `h : p ∧ q` 用投影 |
| `∨` | `Or.inl`，`Or.inr`；`h.elim f g`，`match` | 证只需选一边；用 `h : p ∨ q` 必须两边都处理 |
| `¬` | `fun h ↦ …`；`hnp hp` | `¬p` 就是 `p → False`：证它就假设 `p` 推出 `False` |
| `True`、`False` | `trivial`；`False.elim`，`absurd` | `True` 用 `trivial`；有矛盾就 `absurd`（能证任何结论） |
| `↔` | `⟨mp, mpr⟩`；`h.mp`，`h.mpr` | 证两个方向；用时选方向 |
| `∀`、`∃` | `fun x ↦ …`，`h a`；`⟨w, h⟩`，`h.elim f` | `∀` 引入是 `fun`；`∃` 要给见证，用 `∃` 要拆开 |
| `have`、`show`、`‹p›` | `have h : T := e`，`show T from e` | 长项里命名中间结果、标注类型、按类型取假设 |
| `show_term` | `by show_term …` | 想看策略证明拼出的项 |
| 证明无关性 | `example {p : Prop} (h₁ h₂ : p) : h₁ = h₂ := rfl` | 证明可互换；一般地证明不能产出数据（§9） |
| 经典逻辑 | `Classical.byContradiction`，`#print axioms` | 构造性证明不够时（§8.8）；检查依赖 |

## 延伸阅读

- *Theorem Proving in Lean 4*：第 2 章「Dependent Type Theory」§2.1–2.3、§2.9（Implicit
  Arguments）；第 3 章「Propositions and Proofs」§3.1–3.3；第 4 章 §4.1、§4.4（量词）。
- *Lean Language Reference* 4.35.0：「The Type System」下的 Propositions 与 Universes 两节
  （`https://lean-lang.org/doc/reference/4.35.0/The-Type-System/`）。
- *Hitchhiker's Guide to Logical Verification*（2026）：第 1 章「Types and Terms」；第 4 章
  「Forward Proofs」中 §4.7「The PAT Principle」。
- 源码：`Init/Prelude.lean`、`Init/Core.lean`（`And`、`Or`、`False.elim`、`absurd`、`Iff`、
  `Exists`、`propext`）；`Mathlib/Tactic/TypeStar.lean`、`Mathlib/Tactic/Lemma.lean`。
- 本书第 4 章（同一批证明的策略写法）、第 5 章（定义相等）、第 28 章（宇宙与证明无关性的机制）。
-/

end Lean4Learn.Ch03

end
