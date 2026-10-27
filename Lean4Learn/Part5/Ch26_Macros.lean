module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Extension
public meta import Lean.PrettyPrinter.Delaborator.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# 第 26 章　记号、宏与语法扩展

前面所有章节都在「用」Lean 已有的语法；本章教你自己加语法。Lean 的 notation（记号）、macro（宏）
和 syntax（语法）三个层次是一条链：`infixl` 一类命令生成 `notation`，`notation` 生成 `syntax` 加
`macro_rules`，`macro_rules` 是一个把语法树改写成另一棵语法树的函数。读完本章，你能写自己的运算符
并让它在目标里正确显示，能定义一个小语言（DSL）并让宏把它翻译成 Lean 的项，能写带参数的
tactic（策略）宏，也知道在 `module` 文件里哪些元程序必须标 `meta`。

## 学习目标
- 用 `infixl`、`infixr`、`infix`、`prefix`、`postfix` 与 `notation` 定义记号，读懂 precedence
  （优先级）并用 `pp.parens` 检查解析结果；知道 unexpander（反展开器：打印时把 `f a b` 的语法
  改写回记号的函数）何时由命令自动生成（§2、§3）；
- 区分全局、`scoped`（限定作用域）、`local` 三种作用域的记号（§3）；
- 用 `syntax` 加 `macro_rules` 或一行的 `macro` 定义新语法，说清多条规则的先后次序（§4、§5）；
- 读写 quotation（引用）与 antiquotation（反引用），会用 `$x`、`$(e)`、`$xs,*`、`$[…]?`（§5）；
- 解释 hygiene（卫生性），并用 `set_option hygiene false` 看到被捕获的情形（§6）；
- 用 `declare_syntax_cat` 开一个新的 syntax category（语法范畴），写一个算术 DSL（§7）；
- 写策略宏与小的策略组合子，包括可被后续规则扩展的策略（§8）；
- 用 `@[app_unexpander]` 控制 pretty printing（美观打印），分清它与 delaborator（反精译器）的能力（§9）；
- 完成案例：`graph% [0 ~~ 1, 1 ~~ 2]` 生成边表，`graphOn% 3 [...]` 生成 `SimpleGraph (Fin 3)`，并让
  越界的顶点在宏展开期报错（§10）；
- 在 module（模块）文件里正确放置 `meta`（§1）。

## 前置知识
第 1 章（`module`、`public section`、`@[expose]`），第 2 章（`omega`），第 3 章（`fun`、项），
第 4、5 章（`simp`、`<;>`、`try`），第 6 章（归纳类型、结构递归、`induction`），第 24 章
（`do` 记号、`Option`、`#guard`；宏的函数体就是 `do` 代码）。§10 的 `SimpleGraph` 只用到第 18 章的
`Adj` 与 `fromRel`，用到第 25 章的 `decide`。`first` 与 `fail` 在 §8 现讲。
-/

@[expose] public section

namespace Lean4Learn.Ch26

/-!
## 1. 文件头与 `meta` 阶段

本章文件头有三行 `public meta import …`（第 24 章的 `Std.HashMap` 也是这样导入的）。原因：宏、
elaborator（精译器；另译繁饰器）和美观打印函数是在 Lean **编译你的文件的时候**运行的程序，称为
metaprogram（元程序），它们运行的时期叫 meta 阶段。`module` 文件的规则（参考手册 5.4.1 节）：
要在 meta 阶段执行的定义标成 `meta`，它的代码**调用**的函数也必须是 `meta`；import（导入）也要写成
`meta import`，被导入模块的函数才能在 meta 阶段调用。限制只针对编译出来要执行的代码：只在类型或
证明里提到的名字不算。Mathlib 的策略文件大多这样写（例如 `Mathlib/Tactic/Use.lean`）；第 27 章同样。

**本章的做法**：数据类型、递归函数与定理放在文件开头的 `@[expose] public section` 里（section（区段）
与 expose（暴露）见第 1 章；这样它们能被 `rfl`、`decide`、`simp [f]` 展开）。`notation`、`syntax`、
`macro`、`macro_rules` 这些命令可以直接写在这个区段里，Lean 会替你标 `meta`（实测可行，后面每一节
都是例子）。唯独宏的函数体里调用的**辅助函数**要自己标 `meta`，或者放进
`public meta section 名字 … end 名字`（里面的 `def` 自动是 `meta`）。调用普通 `def` 不行
（用 `meta example` 演示，`example` 不进环境）：
-/

/-- 一个普通的辅助函数（非 `meta`）。 -/
def plainId (t : Lean.Term) : Lean.Term := t

/-- error: Invalid `meta` definition `_example`, `plainId` not marked `meta` -/
#guard_msgs in
meta example (t : Lean.Term) : Lean.Term := plainId t

/-!
只在命题里提到 `plainId` 则可以：下面子类型里的等式是证明的一部分，编译出的代码用不到它。反过来，
证明也可以提到并展开 `meta` 定义（这里是同一文件；跨模块时能否展开取决于 expose，见第 28 章）：
-/

/-- 返回 `t` 本身，附带一个提到 `plainId` 的证明。 -/
meta def metaId (t : Lean.Term) : {u : Lean.Term // u = plainId t} := ⟨t, rfl⟩

/-- 一个 `meta` 常量。 -/
meta def metaTwo : ℕ := 2

example : metaTwo = 2 := rfl

/-!
宏里调用辅助函数的正确写法见 §10 的 `meta def expandEdge`。用 attribute（属性）手写的元程序
（`@[app_unexpander]` 等）也必须是 `meta` 声明，见 §9。

先认识本章反复出现的几个名字：`Lean.Syntax` 是语法树；`Lean.TSyntax k` 是「已知属于语法范畴 `k`」
的语法树；`Lean.Term` 就是 ``TSyntax `term``。宏是 `Lean.MacroM`（一个单子，第 24 章）里的函数，
输入一棵语法树，输出另一棵。`Lean.CoreM` 是更大的单子，`#eval` 可以在其中运行元程序，
`Lean.logInfo` 在其中打印消息。

## 2. 自定义运算符：`infixl`、`infixr`、`infix`、`prefix`、`postfix`

记号让公式读起来像数学；Mathlib 里的 `∑`、`𝓝`、`μ[X]` 都是记号。我们用玩具对象来练习，这样新记号
不会和 Mathlib 自己的撞车。（定义记号之前先在 Mathlib 里 `rg` 一下这个符号：例如
`Mathlib/Algebra/Notation.lean` 已经有 `postfix:max "⁺"`，表示正部。）

先造三个玩具运算：模 5 的加法、乘法和减法，然后给它们配运算符。命令的一般形式是
`infixl:优先级 "符号" => 函数`；优先级是数字，越大结合得越紧，`+` 是 65，`*` 是 70
（`Init/Notation.lean`）。符号字符串两侧的空格只影响显示，不影响解析。
-/

/-- 模 5 加法。 -/
def addMod5 (a b : ℕ) : ℕ := (a + b) % 5

/-- 模 5 乘法。 -/
def mulMod5 (a b : ℕ) : ℕ := (a * b) % 5

/-- 模 5 减法：加上 `b` 的模 5 相反数。 -/
def subMod5 (a b : ℕ) : ℕ := (a + (5 - b % 5)) % 5

infixl:65 " ⊞ " => addMod5
infixl:70 " ⊠ " => mulMod5

#guard 3 ⊞ 4 == 2
#guard 3 ⊠ 4 == 2
#guard 3⊞4 == 2  -- 符号两侧的空格只影响显示，不影响解析

/-!
怎样看出解析结果？`set_option pp.parens true` 让显示的项带上全部括号。`infixl` 是左结合，
`⊠` 的优先级更高，所以 `a ⊞ b ⊞ c` 是 `(a ⊞ b) ⊞ c`，而 `a ⊞ b ⊠ c` 是 `a ⊞ (b ⊠ c)`：
-/

/-- info: fun a b c ↦ ((a ⊞ b) ⊞ c) : ℕ → (ℕ → (ℕ → ℕ)) -/
#guard_msgs in
set_option pp.parens true in
#check fun (a b c : ℕ) ↦ a ⊞ b ⊞ c

/-- info: fun a b c ↦ (a ⊞ (b ⊠ c)) : ℕ → (ℕ → (ℕ → ℕ)) -/
#guard_msgs in
set_option pp.parens true in
#check fun (a b c : ℕ) ↦ a ⊞ b ⊠ c

/-!
`infixr` 是右结合，`infix` 不结合。不结合的运算符连写两次会被解析器拒绝。为了观察「某个字符串能不能被
某个语法范畴解析」，先写一个小工具 `tryParse`：`Parser.runParserCategory` 用范畴 `cat` 解析字符串，
`logInfo` 把结果打印成 `info:` 消息，方便用 `#guard_msgs` 固定下来。它是元程序的辅助函数，所以放进
`public meta section`。本章凡是要展示「这样写会解析失败」的地方都用它。
-/

public meta section Tools

open Lean in
/-- 用语法范畴 `cat` 解析字符串 `s`，成功打印 `ok`，失败打印解析器的错误信息。 -/
def tryParse (cat : Name) (s : String) : CoreM Unit := do
  match Parser.runParserCategory (← getEnv) cat s with
  | .ok _ => logInfo "ok"
  | .error e => logInfo m!"parse error: {e}"

end Tools

infixr:80 " ⤊ " => Nat.pow
infix:50 " ◁ " => Nat.lt

/-- info: fun a b c ↦ (a ⤊ (b ⤊ c)) : ℕ → (ℕ → (ℕ → ℕ)) -/
#guard_msgs in
set_option pp.parens true in
#check fun (a b c : ℕ) ↦ a ⤊ b ⤊ c

/--
info: ok
---
info: parse error: <input>:1:6: expected end of input
-/
#guard_msgs in
#eval show Lean.CoreM Unit from do  -- `show T from e` 同 `(e : T)`；在编译期运行
  tryParse `term "1 ◁ 2"
  tryParse `term "1 ◁ 2 ◁ 3"

/-!
`prefix` 与 `postfix` 各带一个参数。下面的 `⇄` 交换二元组的两个分量，`☆` 加一：
-/

/-- 交换序对的两个分量。 -/
def swapPair (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1)

/-- 加一。 -/
def bump (n : ℕ) : ℕ := n + 1

postfix:max "⇄" => swapPair
prefix:max "☆" => bump

#guard (1, 2)⇄ == (2, 1)
#guard ☆ 4 == 5

/-!
**优先级没有默认值。** 漏掉 `:优先级` 是解析错误；用 `tryParse` 在 `command` 范畴里试一下：
-/

/-- info: parse error: <input>:1:7: expected ':' -/
#guard_msgs in
#eval tryParse `command "infixl \" ⊟ \" => addMod5"

/-!
**自动生成的 unexpander。** 记号命令除了加解析规则，还会登记一个 unexpander，使 `addMod5 1 2`
显示成 `1 ⊞ 2`。条件是右端是全局函数的应用，且每个变量不重复出现（§3 有反例）。用
`set_option pp.notation false` 可以关掉这个行为（`ℕ` 本身也是记号，所以同时变回 `Nat`）：
-/

/-- info: 1 ⊞ 2 : ℕ -/
#guard_msgs in
#check addMod5 1 2

/-- info: addMod5 1 2 : Nat -/
#guard_msgs in
set_option pp.notation false in
#check addMod5 1 2

/-!
## 3. 一般的 `notation`，以及 `scoped` 与 `local`

`infixl` 等是 `notation` 的特例，它们本身就是宏：`infixl:65 " ⊞ " => f` 展开成
`notation:65 lhs:65 " ⊞ " rhs:66 => f lhs rhs`（读自源码 `Lean/Elab/Mixfix.lean` 的 `expandMixfix`，
未另行实测）。左操作数允许同级 65、右操作数要求 66，这就是 §2 看到的左结合。一般的 `notation`
把「文字」和「带优先级的变量」交替排列，变量可以夹在文字中间：
-/

/-- 两个自然数的距离。 -/
def dist2 (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

notation:max "dist₂(" a ", " b ")" => dist2 a b

#guard dist₂(3, 5) == 2

/-- info: dist₂(3, 5) : ℕ -/
#guard_msgs in
#check dist2 3 5

/-!
变量在右端出现两次的记号没有 unexpander。用一个新函数 `f3` 做试验：`1 ⊛ 2` 展开成
`f3 1 (f3 2 1)`，目标里显示的就是展开后的项：
-/

/-- 三元的玩具函数。 -/
def f3 (a b : ℕ) : ℕ := a + b + a

notation:65 a:65 " ⊛ " b:66 => f3 a (f3 b a)

/-- info: f3 1 (f3 2 1) : ℕ -/
#guard_msgs in
#check 1 ⊛ 2

/-!
**scope（作用域）。** 默认的记号全局生效：只要导入了这个模块，记号就在。`scoped` 记号只在其所在
namespace（命名空间）被 `open`（或 `open scoped`）时生效；`local` 记号只在当前 `section`（或文件）内
生效。Mathlib 的 `open Finset`（`#s`）与 `open scoped BigOperators`（`𝔼`）就是这个机制。
scoped 记号连同它的 unexpander 一起受作用域控制。在 `namespace Shapes` 内部，scoped 记号已经生效：
-/

namespace Shapes

/-- 一个玩具运算。 -/
def tensor (a b : ℕ) : ℕ := a * b + 1

scoped infixl:70 " ⊗ " => tensor

/-- info: 1 ⊗ 2 : ℕ -/
#guard_msgs in
#check tensor 1 2

end Shapes

/-- info: Shapes.tensor 1 2 : ℕ -/
#guard_msgs in
#check Shapes.tensor 1 2

/-!
解析规则也受作用域控制：`⊗` 没被打开时，`tryParse` 解析失败；`open … in` 之后成功：
-/

/-- info: parse error: <input>:1:2: expected end of input -/
#guard_msgs in
#eval tryParse `term "1 ⊗ 2"

open Shapes in
/-- info: ok -/
#guard_msgs in
#eval tryParse `term "1 ⊗ 2"

/-!
`local notation` 在 `section` 结束时消失，连它的符号（token）一起：
-/

section LocalDemo

local notation "ⓛ" => (100 : ℕ)

#guard ⓛ == 100

/-- info: ok -/
#guard_msgs in
#eval tryParse `term "ⓛ"

end LocalDemo

/-- info: parse error: <input>:1:0: expected token -/
#guard_msgs in
#eval tryParse `term "ⓛ"

/-!
## 4. `syntax` 加 `macro_rules`

`notation` 能做的只是「文字加变量」。要自定义更复杂的形状，就把两件事拆开：`syntax` 声明
**长什么样**，即 grammar（文法），`macro_rules` 声明**展开成什么**。macro（宏）是语法树到语法树
的函数。展开发生在精译途中，一次一个节点：精译器处理一个语法节点时先看有没有适用的宏，有就展开，
再精译展开的结果；结果里的子节点等精译器走到它们时才展开（读自源码：项是
`Lean/Elab/Term/TermElabM.lean` 的 `elabTermAux`，策略是 `Lean/Elab/Tactic/Basic.lean` 的
`evalTactic`）。项的情形本章不另行实测；策略的情形 §8 能直接看到。

下面是最小的例子，同时是本节的第一个坑：`syntax "twice! " term : term` 里的 `term` 没有写
优先级，等于 0，它会吃掉后面所有能吃的东西，于是 `twice! 3 == 6` 被解析成 `twice! (3 == 6)`：
-/

syntax "twice! " term : term

macro_rules
  | `(twice! $t) => `($t + $t)

/--
error: failed to synthesize instance of type class
  HAdd Bool Bool ?_

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
set_option pp.mvars false in
#check twice! 3 == 6

/-!
给参数加上 `:max`，它就只吃优先级为 `max` 的项（数字、标识符、括号表达式等），后面的 `== 6` 留给外层：
-/

syntax "twice2! " term:max : term

macro_rules
  | `(twice2! $t) => `($t + $t)

#guard (twice2! 3) == 6
#guard twice2! 3 == 6

/-!
**多条规则的先后次序。** 对同一个语法可以有很多条 `macro_rules`。规则是这样挑的：

1. **后写的命令先试**；
2. 同一个命令里的各条规则**从上到下**，第一条模式匹配成功的就用它；
3. 如果选中的规则抛出 `Macro.throwUnsupported`，Lean 认为「这条规则不处理」，转去试**更早的命令**
   （同一个命令里排在后面的规则不再试）。

下面一组规则三件事都演示到。`pick! 1` 命中第二个（后写的）命令里的字面量规则，尽管第一个命令里的
通用规则也能匹配它；`pick! 2` 命中第二个命令里的 `throwUnsupported` 规则，于是该命令里后面的通用规则
被跳过，落到第一个命令；`pick! 5` 命中第二个命令的最后一条规则（同一命令内自上而下）：
-/

syntax "pick! " term:max : term

macro_rules
  | `(pick! $n) => `($n + 1)

macro_rules
  | `(pick! 1) => `(2000)
  | `(pick! 2) => Lean.Macro.throwUnsupported
  | `(pick! $n) => `($n + 100)

#guard (pick! 1) == 2000
#guard (pick! 2) == 3
#guard (pick! 5) == 105

/-!
没有宏规则时，语法节点原样留下，精译器随后报错，见 §11。
策略宏用同样的机制做成「可扩展的策略」，见 §8。

## 5. 一行的 `macro`、引用与反引用

`macro` 命令把 `syntax` 和 `macro_rules` 合成一条：参数写成 `名字:语法说明`，右边是展开结果。
单个规则的宏几乎总是这样写：
-/

macro "swap! " p:term:max : term => `(Prod.swap $p)

#guard (swap! (1, 2)) == (2, 1)

/-!
`` `( … ) `` 是 quotation（引用）：括号里是要构造的语法。`$p` 是 antiquotation（反引用）：
在引用里插入一个已有的语法片段。反引用的写法：

| 写法 | 含义 |
|---|---|
| `$x` | 插入变量 `x`（类型 `TSyntax k`） |
| `$n:num` | 同上，同时指定语法范畴（匹配模式里常用，见 §10 的 `expandEdge`） |
| `$(e)` | 插入计算出来的语法 `e` |
| `$xs,*` | 插入以逗号分隔的列表（`xs : TSepArray`；`Array` 会自动转换） |
| `$xs*` | 插入用空白分隔的列表（`xs : TSyntaxArray`） |
| `$[…]?` | 可选部分（`Option`） |

`$` 与名字之间、`:` 两侧不能有空格（参考手册 24.5.3 节）。**宏不自动生成 unexpander**，所以展开后的
项按它自己的形状显示，而 `notation` 版本会还原成记号：
-/

/-- info: (1, 2).swap : ℕ × ℕ -/
#guard_msgs in
#check swap! (1, 2)

/-!
带可选部分的语法。`(" : " term)?` 是可选的类型标注，匹配时用 `$[: $ty]?`，展开时原样放回：
-/

syntax "mylet " ident (" : " term)? " := " term " in " term : term

macro_rules
  | `(mylet $x $[: $ty]? := $val in $body) => `(let $x $[: $ty]? := $val; $body)

#guard (mylet x : Int := 5 in x - 10) == -5
#guard (mylet y := 2 in y * y) == 4

/-!
逗号分隔的列表。`xs.getElems` 取出数组，反转后用 `$ys,*` 放回列表字面量：
-/

macro "rev_list! " "[" xs:term,* "]" : term => do
  let ys := xs.getElems.reverse
  `([$ys,*])

#guard (rev_list! [1, 2, 3]) == [3, 2, 1]

/-!
空白分隔的列表。参数写成 `term:max*`（每个参数都是一个优先级为 `max` 的项），用 `$xs*` 逐个放回，
就得到把函数作用到任意多个参数上的宏：
-/

macro "apply! " f:term:max xs:term:max* : term => `($f $xs*)

#guard (apply! Nat.add 1 2) == 3

/-!
## 6. 卫生性（hygiene）

宏在语法树里引入的名字可能和用户的名字重合。Lean 的 hygiene（卫生性）机制给引用里引入的绑定名
打上一个只属于这次展开的标记，所以不会捕获用户的同名变量。

下面的宏在 `fun` 里引入一个叫 `x` 的绑定。用户传进来的也是 `x`，却没有被捕获：
`(const! x) 10` 返回用户的 `x`，不是 `10`。
-/

macro "const! " e:term:max : term => `(fun x ↦ $e)

example (x : ℕ) : (const! x) 10 = x := rfl

/-- info: fun x x_1 ↦ x : ℕ → ℕ → ℕ -/
#guard_msgs in
#check fun (x : ℕ) ↦ (const! x : ℕ → ℕ)

/-!
显示里第二个 `x` 被改名为 `x_1`，说明两个 `x` 是不同的变量，返回的是第一个（用户的）。
`set_option hygiene false` 关掉标记；此时宏的 `x` 与用户的 `x` 同名，被捕获了，所以 `(const_bad! x) 10`
等于 `10`，而且显示里返回的是第二个（宏的）`x_1`（对比上面）：
-/

set_option hygiene false in
macro "const_bad! " e:term:max : term => `(fun x ↦ $e)

example (x : ℕ) : (const_bad! x) 10 = 10 ∧ x = x := ⟨rfl, rfl⟩

/-- info: fun x x_1 ↦ x_1 : ℕ → ℕ → ℕ -/
#guard_msgs in
set_option linter.unusedVariables false in
#check fun (x : ℕ) ↦ (const_bad! x : ℕ → ℕ)

/-!
需要故意引入用户可见的名字时（例如生成给用户复制的代码）才关 hygiene；其余情况保持默认。

## 7. 语法范畴与一个算术 DSL

`term`、`tactic`、`command` 都是 syntax category（语法范畴）：每个范畴有自己的一组解析规则，
`syntax … : term` 里冒号后面的名字说明新规则加进哪个范畴。`declare_syntax_cat` 开一个新范畴，
用它可以做一个嵌入的小语言（DSL，domain-specific language）。步骤总是三步：

1. 在普通区段里写**抽象语法**（一个归纳类型）和它的**语义**（求值函数）；
2. 声明范畴与文法；
3. 写 `macro_rules`，把范畴里的语法翻译成抽象语法的项。

第一步。`Arith` 是带变量的加法乘法表达式，`Arith.eval` 在环境 `ρ` 下求值：
-/

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

/-!
第二、三步。范畴 `arith` 里有数字、标识符、括号以及两个二元运算；`+` 是 60 且左结合
（`arith:60 " + " arith:61`），`*` 是 70。范畴 `arith` 的规则只在引用它的地方才会被解析，这里是
`term` 范畴的新规则 `[Arith| … ]`；每条 `macro_rules` 把一种形状翻译成构造子，递归地翻译子表达式：
-/

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

/-!
现在使用它。`[Arith| …]` 展开成构造子，并且 `*` 比 `+` 紧、`+` 左结合：
-/

example : [Arith| 1 + 2 * 3] = .add (.num 1) (.mul (.num 2) (.num 3)) := rfl
example : [Arith| 1 + 2 + 3] = .add (.add (.num 1) (.num 2)) (.num 3) := rfl
example : [Arith| (1 + 2) * 3] = .mul (.add (.num 1) (.num 2)) (.num 3) := rfl

/-- 标识符变成变量；语义是在环境里取值。 -/
example (ρ : String → ℕ) : Arith.eval ρ [Arith| x * x + y] = ρ "x" * ρ "x" + ρ "y" := rfl

/-!
## 8. 策略宏

策略也是一个语法范畴（`tactic`），所以宏的写法完全一样，只是引用写成 `` `(tactic| … ) ``。
最简单的是给一串策略起名字：
-/

macro "my_simp" : tactic => `(tactic| simp)

example (xs : List ℕ) : (xs ++ []).length = xs.length := by my_simp

/-!
带参数的策略宏：参数的类型是 `tactic`。先认识两个本章要用的策略。`first | t₁ | t₂` 依次尝试各个
策略，第一个成功的生效，全部失败则整体失败（下面的例子里 `rfl` 解决第一个目标，`omega` 解决第二个）；
`fail "信息"` 永远失败并给出这条信息；`fail_if_success t` 在 `t` 成功时失败（本节末尾用到）：
-/

example (a b : ℕ) (h : a < b) : a = a ∧ a ≤ b := by
  constructor <;> first | rfl | omega

/-!
下面的组合子 `try_all [t₁, t₂, …]` 是 `first` 的列表版：依次尝试各个策略，第一个成功的生效，
全部失败时给出自己的错误信息。它用三条规则**递归**地定义：空列表就是 `fail`；单元素列表是
`first | t | fail …`；否则试头一个，失败了对其余的递归。
-/

syntax "try_all " "[" tactic,* "]" : tactic

macro_rules
  | `(tactic| try_all []) => `(tactic| fail "try_all: no tactic succeeded")
  | `(tactic| try_all [$t]) =>
    `(tactic| first | $t:tactic | fail "try_all: no tactic succeeded")
  | `(tactic| try_all [$t, $ts,*]) => `(tactic| first | $t:tactic | try_all [$ts,*])

/-!
Mathlib 的 linter（代码检查器）`linter.unusedTactic` 把没有起作用的策略标出来；失败的分支就是这样的
策略，所以下面的成功例子（`rfl` 失败，递归到 `omega`）会收到一条警告：
-/

/--
warning: Unused tactic linter: `rfl` does nothing.

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example (a b : ℕ) (h : a < b) : a ≤ b := by try_all [rfl, omega]

/-!
展开是按需的（§4）。执行 `try_all [rfl, t]` 时，宏只改写这一个节点，得到 `first | rfl | try_all [t]`
交给策略执行器；里面的 `try_all [t]` 要等 `first` 真去试第二个分支时才展开。用一个一展开就报错的宏
`boom` 可以看到：第一个分支成功时没有 `boom` 的错误，只有两条 linter 警告，说 `boom` 从未执行：
-/

macro "boom" : tactic => Lean.Macro.throwError "boom was expanded"

/--
warning: Unused tactic linter: `boom` does nothing.

Note: This linter can be disabled with `set_option linter.unusedTactic false`
---
warning: this tactic is never executed

Note: This linter can be disabled with `set_option linter.unreachableTactic false`
-/
#guard_msgs in
example : 1 = 1 := by try_all [rfl, boom]

/-!
全部分支失败时，报的是 `try_all` 自己的信息：
-/

/--
error: try_all: no tactic succeeded
⊢ 1 = 2
-/
#guard_msgs in
example : 1 = 2 := by try_all [rfl, decide]

/-!
**可扩展的策略。** 核心库的 `trivial`、`rfl` 都是这样做的：声明语法，再给出多条 `macro_rules`。
对策略来说，宏展开的结果如果执行失败，Lean 会退回去试更早的规则（§4 的规则次序在这里仍然适用，
并多一层「失败回退」）。下面三条规则分三次给出，所以从新到旧的试探顺序是 `assumption`、`omega`、
`rfl`，第一条展开后能成功的规则生效。三个例子各落在不同的规则上；`fail_if_success` 证明排在前面的
规则确实解决不了：
-/

syntax "close_goal" : tactic

macro_rules | `(tactic| close_goal) => `(tactic| rfl)
macro_rules | `(tactic| close_goal) => `(tactic| omega)
macro_rules | `(tactic| close_goal) => `(tactic| assumption)

example : (true && false) = false := by
  fail_if_success assumption
  fail_if_success omega
  close_goal  -- 落在 `rfl` 规则上

example (a : ℕ) (h : a < 3) : a < 5 := by
  fail_if_success assumption
  close_goal  -- 落在 `omega` 规则上

example (p : Prop) (h : p) : p := by close_goal  -- 落在 `assumption` 规则上

/-!
三条规则都解决不了的目标，`close_goal` 就失败，错误信息来自最后试的（最早写的）规则：
-/

/--
error: Tactic `rfl` failed: The left-hand side
  (xs ++ []).length
is not definitionally equal to the right-hand side
  xs.length

xs : List ℕ
⊢ (xs ++ []).length = xs.length
-/
#guard_msgs in
example (xs : List ℕ) : (xs ++ []).length = xs.length := by close_goal

/-!
以后任何地方都可以再追加一条规则（练习 26.10 就是这样做的）。

## 9. 美观打印：`@[app_unexpander]`

打印走精译的反方向，分两步。先由 delaborator（`delab`）把表达式（`Expr`）变回语法树；
遇到常量 `c` 的应用时，再看 `c` 有没有登记 unexpander，有就把已经生成的语法（如 `edge 1 2`）
改写一次（如改成 `1 ⇢ 2`）。unexpander 只拿到语法，拿不到 `Expr`（见
`Lean/PrettyPrinter/Delaborator/Basic.lean` 里 `app_unexpander` 的文档）。`notation` 命令会自动登记
unexpander；用 `macro` 或 `syntax` 定义的语法没有，需要自己写。下面给一个表示边的函数配上 `⇢`
记号：宏负责「读」，`@[app_unexpander edge]` 的函数负责「显示」。

属性形式的元程序必须是 `meta` 声明（§1）。不标 `meta` 会被拒绝（同样用 `example` 演示）：
-/

/--
error: Cannot add attribute `[Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute]`:
Declaration `_example` must be marked as `meta`
-/
#guard_msgs in
@[app_unexpander Nat.succ] example : Lean.PrettyPrinter.Unexpander := fun _ => throw ()

/-- 一条边：端点序对。 -/
def edge (u v : ℕ) : ℕ × ℕ := (u, v)

macro:65 a:term:66 " ⇢ " b:term:66 : term => `(edge $a $b)

/-- info: edge 1 2 : ℕ × ℕ -/
#guard_msgs in
#check edge 1 2

@[app_unexpander edge] meta def unexpandEdge : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a ⇢ $b)
  | _ => throw ()

/-- info: 1 ⇢ 2 : ℕ × ℕ -/
#guard_msgs in
#check edge 1 2

/-!
`throw ()` 表示「这个应用我不处理」，回到默认显示（例如只给了一个参数的 `edge 1`）。
`pp.notation false` 同样让 unexpander 不再被调用：
-/

/-- info: edge 1 : ℕ → ℕ × ℕ -/
#guard_msgs in
#check edge 1

/-- info: edge 1 2 : Prod Nat Nat -/
#guard_msgs in
set_option pp.notation false in
#check edge 1 2

/-!
要按类型或隐式参数决定显示，就得写 delaborator：`@[app_delab c]` 拿到整个 `Expr`，写法见第 27 章
§9。Mathlib 的 `Order/Notation.lean` 里 `@[delab app.Max.max] meta def delabSup` 先查类型有没有全序，
没有才把 `max s t` 显示成 `s ⊔ t`。unexpander 看不到类型，做不了这件事：
-/

/-- info: fun a b s t ↦ (max a b, s ⊔ t) : ℕ → ℕ → Set ℕ → Set ℕ → ℕ × Set ℕ -/
#guard_msgs in
#check fun (a b : ℕ) (s t : Set ℕ) ↦ (max a b, max s t)

/-!
## 10. 案例：一个图的 DSL

目标：写 `graph% [0 ~~ 1, 1 ~~ 2]` 得到边表，写 `graphOn% 3 [0 ~~ 1, 1 ~~ 2]` 得到
`SimpleGraph (Fin 3)`，并让越界的顶点在宏展开期报错。边的连接符本来想写 `--`，但 `--` 在 Lean 里
是行注释，词法分析器在认符号之前就把它当注释吞掉了（§11 有演示），所以改用 `~~`。

按 §7 的三步走。语义：边表转成 `Bool` 谓词 `edgeB`，再用 Mathlib 的 `SimpleGraph.fromRel` 造图；
`fromRel r` 是 `a ≠ b ∧ (r a b ∨ r b a)`，自动对称化并去掉自环（`toGraph_adj`）。谓词是 `Bool`，
邻接可判定，`decide` 能直接验证（第 25 章）；`toGraph` 是普通 `def`，所以实例用 `inferInstanceAs`
把目标类型换成它展开后的 `fromRel`：
-/

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

/-!
语法：边是新范畴 `gedge`；宏调用的辅助函数 `expandEdge` 把一条边翻译成 §9 的 `edge`（所以显示回
`⇢`），它在 meta 阶段运行，标成 `meta def`（§1）。`graphOn%` 先检查每个顶点是否小于 `n`，
否则用 `Lean.Macro.throwErrorAt` 在那个顶点处报错：
-/

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

/-! 边表就是一个 `List (ℕ × ℕ)`，显示时 `edge` 被还原成 `⇢`： -/

/-- info: [0 ⇢ 1, 1 ⇢ 2] : List (ℕ × ℕ) -/
#guard_msgs in
#check graph% [0 ~~ 1, 1 ~~ 2]

/-!
`graphOn%` 的图可以直接用 `decide` 验证邻接。图是无向的（`fromRel` 对称化），自环被丢弃：
-/

example : (graphOn% 3 [0 ~~ 1, 1 ~~ 2]).Adj 0 1 := by decide
example : (graphOn% 3 [0 ~~ 1, 1 ~~ 2]).Adj 1 0 := by decide
example : ¬ (graphOn% 3 [1 ~~ 1]).Adj 1 1 := by decide

/-! 越界的顶点在宏展开期报错： -/

/-- error: graphOn%: vertex 5 is out of range (n = 2) -/
#guard_msgs in
#check graphOn% 2 [0 ~~ 5]

/-!
## 11. 常见错误

**1. 只写 `syntax`，忘了展开规则。** 解析通过，精译器找不到处理这个语法的函数：
-/

syntax "unfinished! " : term

/--
error: elaboration function for `Lean4Learn.Ch26.termUnfinished!` has not been implemented
  unfinished!
-/
#guard_msgs in
#check unfinished!

/-!
**2. 用 `--` 当符号。** `syntax num " -- " num : gedge2` 能通过声明，但词法分析器读到
`--` 就把它和行尾一起当成注释，范畴 `gedge2` 永远等不到这个符号：
-/

declare_syntax_cat gedge2

syntax num " -- " num : gedge2

/-- info: parse error: <input>:1:6: unexpected end of input; expected '--' -/
#guard_msgs in
#eval tryParse `gedge2 "1 -- 2"

/-!
**3. 新记号的文字本身变成关键字。** 像标识符的符号一旦出现在 `syntax` 或 `notation` 里，同名的
标识符就不能再用了。下面的 `local syntax` 只在这个区段里生效，区段里 `edge` 就不能当函数名：
-/

section Reserved

local syntax "edge" : term

/-- info: parse error: <input>:1:9: expected identifier -/
#guard_msgs in
#eval tryParse `command "def edge : ℕ := 1"

end Reserved

/-!
所以符号要么带上标点（`twice! `、`dist₂(`），要么用 `local`/`scoped` 限制范围。

## 练习

练习的陈述用到本章定义的记号、DSL 与宏。第 3 题和第 10、12 题要你在定理之前自己写记号或宏
（`Solutions` 里给出）。
-/

/-- 练习 26.1（★）：`⊞` 是交换的，也是结合的。提示：`unfold addMod5` 后用 `omega`（第 2 章）。 -/
theorem ex_26_1 (a b c : ℕ) : a ⊞ b = b ⊞ a ∧ (a ⊞ b) ⊞ c = a ⊞ (b ⊞ c) := sorry

/-- 练习 26.2（★）：读优先级。`⊠` 比 `⊞` 结合得更紧，所以这里的括号可以省略。 -/
theorem ex_26_2 (a b c : ℕ) : a ⊞ b ⊠ c = a ⊞ (b ⊠ c) := sorry

/-- 练习 26.3（★★）：先在定理之前为 `subMod5` 写 `infixl:65 " ⊟ " => subMod5`，并用
`#guard 3 ⊟ 4 == 4` 检查记号；再证明下面的等式。提示：`unfold subMod5 addMod5` 后用 `omega`。 -/
theorem ex_26_3 (a b : ℕ) : subMod5 (a ⊞ b) b = a % 5 := sorry

/-- 练习 26.4（★）：`⇄` 是对合。提示：`rfl`，结构 eta（第 6 章）。 -/
theorem ex_26_4 (p : ℕ × ℕ) : p⇄⇄ = p := sorry

/-- 练习 26.5（★）：在常值环境下用 `decide` 计算一个 DSL 表达式。 -/
theorem ex_26_5 : Arith.eval (fun _ ↦ 2) [Arith| x * (y + 3)] = 10 := sorry

/-- 练习 26.6（★★）：`mirror` 不改变求值结果。提示：对 `a` 做结构归纳（第 6 章），
再用 `Nat.add_comm`、`Nat.mul_comm`。 -/
theorem ex_26_6 (ρ : String → ℕ) (a : Arith) : a.mirror.eval ρ = a.eval ρ := sorry

/-- 练习 26.7（★★）：`mirror` 是对合。提示：结构归纳加 `simp only [Arith.mirror, …]`。 -/
theorem ex_26_7 (a : Arith) : a.mirror.mirror = a := sorry

/-- 练习 26.8（★★）：路径图上的邻接。提示：`decide`（第 25 章），把合取拆开或直接整个 `decide`。 -/
theorem ex_26_8 :
    (graphOn% 4 [0 ~~ 1, 1 ~~ 2, 2 ~~ 3]).Adj 1 0 ∧
      ¬ (graphOn% 4 [0 ~~ 1, 1 ~~ 2, 2 ~~ 3]).Adj 0 3 := sorry

/-- 练习 26.9（★★）：`toGraph` 没有自环。提示：`toGraph_adj`（§10）或 `SimpleGraph.irrefl`。 -/
theorem ex_26_9 (n : ℕ) (es : List (ℕ × ℕ)) (a : Fin n) :
    ¬ (toGraph n es).Adj a a := sorry

/-- 练习 26.10（★★）：`close_goal` 目前只有 `rfl`、`omega`、`assumption` 三条规则，
解不了下面的目标（§8）。在定理之前自己再加一条 `macro_rules`（用 `simp`），然后用 `close_goal`
证明它。 -/
theorem ex_26_10 (xs : List ℕ) : (xs ++ []).length = xs.length := sorry

/-- 练习 26.11（★）：卫生性。§6 的 `const_bad!` 关掉了卫生性，`const!` 没有。判断两个宏
对 `(…) 10` 的结果，然后用 `rfl` 证明。 -/
theorem ex_26_11 (x : ℕ) : (const_bad! x) 10 = 10 ∧ (const! x) 10 = x := sorry

/-- 练习 26.12（★★）：在定理之前写一个策略宏 `simp_with t`，展开成 `simp [t]`（参数 `t` 的
语法范畴是 `term:max`，引用写 `` `(tactic| simp [$t:term]) ``），然后用它证明下面的等式。 -/
theorem ex_26_12 (xs ys : List ℕ) : (xs ++ ys).length = ys.length + xs.length := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 运算符 | `infixl:65 " ⊞ " => f`，`infixr`，`infix`，`prefix`，`postfix` | 二元、一元运算；必须写优先级 |
| 一般记号 | `notation:max "dist₂(" a ", " b ")" => f a b` | 文字与变量交替；变量不重复出现时有自动 unexpander |
| 作用域 | `scoped notation`，`local notation`，`open scoped` | 避免全局记号冲突 |
| 检查解析 | `pp.parens true`，`pp.notation false`，`runParserCategory` | 看清优先级、unexpander 是否生效 |
| 新语法 | `syntax … : term` 加 `macro_rules` | 复杂形状；参数一般写 `term:max` |
| 一行宏 | `macro "name " x:term:max : term => `(…)` | 单规则展开；没有 unexpander |
| 规则次序 | 后写的命令先试；同一命令自上而下；`throwUnsupported` 回退到更早的命令 | 扩展已有语法 |
| 反引用 | `$x`，`$n:num`，`$(e)`，`$xs,*`，`$xs*`，`$[…]?` | 在引用里插入、匹配语法 |
| 卫生性 | 默认开启；`set_option hygiene false in` | 不捕获用户变量；仅在有意生成可见名字时关闭 |
| 语法范畴 | `declare_syntax_cat c`，`(c| …)` 引用 | 嵌入 DSL |
| 展开期计算 | 宏里的 `do` 代码，`meta def` 辅助函数，`Lean.Macro.throwErrorAt` | 宏里递归、检查、报错 |
| 策略宏 | `macro "t" : tactic => `(tactic| …)`，多条 `macro_rules` | 命名策略序列、组合子、可扩展策略 |
| 美观打印 | `@[app_unexpander c] meta def f : Unexpander` | 改写 `c` 的应用生成的语法；看不到 `Expr` |
| `meta` | `meta def`，`public meta section`，`public meta import` | 宏的辅助函数、属性形式的元程序 |

怎样选：只是「记号换函数」用 `infixl`/`notation`，显示自动还原；形状复杂或要在展开时计算用
`syntax` 加 `macro_rules`；展开结果需要显示成原来的形状时再写 `@[app_unexpander]`。
想检查元程序的行为，先写 `#check`/`#guard_msgs`，再写定理。

## 延伸阅读

- *Lean Language Reference* 4.35.0，第 24 章「Notations and Macros」
  （`https://lean-lang.org/doc/reference/4.35.0/Notations-and-Macros/`）：24.1 Custom
  Operators、24.2 Precedence、24.5 Macros（含卫生性与规则次序）、24.8 Extending Lean's Output；
  第 5 章「Source Files and Modules」5.4.1 The Meta Phase 解释了 `meta` 的规则。
- *Metaprogramming in Lean 4*（`https://github.com/leanprover-community/lean4-metaprogramming-book`，
  与 Lean v4.35.0 对应的提交 `206e866399`）：`lean/main/05_syntax.lean`、`06_macros.lean`、
  `08_dsls.lean`、`09_tactics.lean`（本章的 `mylet` 取自 06，算术 DSL 参考了 08）。
- Lean 核心源码（`src/lean/`）：`Init/Notation.lean`（`+`、`*` 的优先级）、`Lean/Elab/Mixfix.lean`
  （`infixl` 等展开成 `notation`）、`Lean/Elab/Term/TermElabM.lean` 与 `Lean/Elab/Tactic/Basic.lean`
  （宏在精译途中逐节点展开）、`Lean/PrettyPrinter/Delaborator/Basic.lean`（`@[app_unexpander]`、
  `@[app_delab]`）。
- Mathlib：`Mathlib/Tactic/Use.lean`（`public meta section` 的真实用法）、
  `Mathlib/Order/Notation.lean`（`delabSup`）、`Mathlib/Util/Notation3.lean`（带绑定变量的 `notation3`）。
- 本书第 1 章（`module` 文件头）、第 24 章（`do` 记号、`Option`、`#guard`）、第 27 章（`Expr`、
  `MetaM` 与用 `elab` 写策略）、第 28 章（`meta` 阶段与模块系统的机制）。
-/

end Lean4Learn.Ch26

end
