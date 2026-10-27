module

public meta import Std.Data.HashMap
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.TypeStar
public import Std.Data.HashMap

/-!
# 第 24 章　Lean 作为函数式编程语言

Lean 4 首先是一门编程语言，定理证明器本身就是用它写的。本章是压缩版的《Lean 函数式编程》
（*Functional Programming in Lean*，下称 FPIL）：写 pure function（纯函数），用 `Option` 与
`Except` 表示失败，用 `String`、`List`、`Array`、`Std.HashMap` 处理数据，用 do-notation
（do 记号）写带 side effect（副作用）的程序，把 `Option`、`Except`、`StateM`、`IO` 统一看成
monad（单子）；最后用 `StdGen` 模拟 binomial random graph（二项随机图），统计 degree（度）与
三角形个数，并接到 Mathlib 的 `SimpleGraph`。

## 学习目标
- 用 pattern matching（模式匹配）与 structural recursion（结构递归）在 `List`、`Option` 上定义
  函数，区分「返回 `none`」与「抛错」；
- 知道 4.27 起 `String.take`/`drop` 等返回 string slice（字符串切片）`String.Slice`，会用 `.copy`；
- 会用 `xs[i]?`、`xs[i]!`、带证明的 `xs[i]`，会写 `for i in 0...n`，知道 `0...n` 不含 `n`；
- 会用 `Std.HashMap`，会写 `do` 块，并把 `Option`、`Except`、`StateM` 看成同一个 `Monad` 接口；
- 会写并运行 `IO` 动作，会用 `deriving` 生成常用 instance（实例）；
- 区分结构递归、well-founded recursion（良基递归）与 `partial` 对证明的后果；
- 会用 `mkStdGen`、`randNat` 写可复现的随机程序，说明采样器与概率模型（第 17、20 章）的差别，
  并把计算出的数据接到 `SimpleGraph` 上用 `decide` 核对。

## 前置知识
第 3 章（类型、`fun`、`def`）、第 5 章（`decide`）、第 6 章（`inductive`、`match`、结构递归、
§9 的 `termination_by`、`deriving`）、第 8 章（`instance`）。§10 用到第 2 章的 junk value（垃圾值）
与 truncated subtraction（截断减法）；§11 用到第 12 章的 `Finset`、`Fin n` 与第 18 章 §1 的
`SimpleGraph`、`DecidableRel`；练习 24.15 用到强归纳与 `omega`（第 13、10 章）。第 17、20 章的
概率模型只作对照。文件头多一行 `public meta import Std.Data.HashMap`，原因见 §5 末尾。
-/

@[expose] public section

namespace Lean4Learn.Ch24

/-!
## 1. 函数、模式匹配与结构递归

`def` 定义函数，`match` 或多条 `|` 分支做模式匹配。递归调用作用在子项 `xs` 上是结构递归，不需要
termination（终止性）注解，并在 reduction（规约）中按定义展开，所以 `rfl` 与 `decide` 都能算它
（第 6 章 §3；equation lemma（等式引理）见第 6 章 §5）。
-/

def sumList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sumList xs

/-- info: 6 -/
#guard_msgs in
#eval sumList [1, 2, 3]

example : sumList [1, 2, 3] = 6 := rfl
example : sumList [1, 2, 3] = 6 := by decide

/-!
**失败用 `Option`。** 不是每个输入都有输出时返回 `Option α`，`none` 表示没有（第 6 章 §6）。
调用方用 `match`、`getD`、`map` 处理两种情况：
-/

def lastOpt {α : Type*} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => lastOpt xs

/-!
**测试用 `#guard`。** 它在编译时求值，结果为 `false` 就报错；它只是运行程序，**不是**证明
（证明见第 25 章）。`#guard` 接受 `Bool` 或 decidable（可判定）的命题。`&&`、`==` 是 `Bool` 上的与和相等，
`∧`、`=` 是 `Prop` 上的；`&&` 两侧写 `=` 这样的命题时，Lean 自动用 `decide` 把它们变成
`Bool`，本章的测试常这样写：
-/

#guard lastOpt [1, 2, 3] = some 3
#guard lastOpt ([] : List ℕ) = none
#guard (lastOpt [1, 2, 3]).getD 0 = 3 && (lastOpt [1, 2, 3]).map (· + 1) = some 4

/-!
失败的 `#guard` 报错，并给出被求值的表达式：
-/

/--
error: Expression
  decide (sumList [1, 2] = 4)
did not evaluate to `true`
-/
#guard_msgs in
#guard sumList [1, 2] = 4

/-!
## 2. 字符串与 `String.Slice`

处理文本的程序要截取、切分、拼接字符串。4.27 起，`String.take`、`drop`、`trimAscii` 这类取子串
的函数**不再返回 `String`**，而是返回 `String.Slice`：它只记录原字符串与起止位置。
`#eval` 打印切片时没有引号。需要真正的 `String` 时用 `.copy`。
-/

/-- info: llo -/
#guard_msgs in
#eval "hello".drop 2

/-- info: "hello".drop 2 : String.Slice -/
#guard_msgs in
#check "hello".drop 2

#guard ("hello".drop 2).copy = "llo" && ("hello".take 2).copy = "he"
#guard "hello".drop 2 == "llo".toSlice       -- 切片之间用 `==` 比较
#guard "  hi there ".trimAscii.copy = "hi there"

/-!
旧资料里去掉首尾空白的 `String.trim` 已不存在，改用返回切片的 `trimAscii`，再 `.copy`：
-/

/--
error: Invalid field `trim`: The environment does not contain `String.trim`, so it is not possible
to project the field `trim` from an expression
  "  a "
of type `String`
-/
#guard_msgs in
#eval "  a ".trim

/-!
`++`、`replace`、`intercalate` 仍返回 `String`，`toNat?` 解析自然数。`split` 现在返回惰性的分割
结果，要 `toStringList` 才得到 `List String`；本章用返回 `List String` 的旧式接口 `splitOn`（核心库
文档称 legacy）。`length` 数 Unicode 标量值，`utf8ByteSize` 数字节；`s!"…{x}…"` 做插值（切片也能）。
-/

#guard "a,b,c".splitOn "," = ["a", "b", "c"] && ", ".intercalate ["a", "b"] = "a, b"
#guard ("a b c".split ' ').toStringList = ["a", "b", "c"]   -- `split` 返回惰性结果
#guard "12".toNat? = some 12 && "x".toNat? = none && "a" ++ "b" = "ab"
#guard "héllo".length = 5 && "héllo".utf8ByteSize = 6 && "hello".replace "l" "L" = "heLLo"
#guard s!"{"hello".take 2}!" = "he!"

/-!
## 3. `List` 与 `Array`

`List` 是单向链表，适合模式匹配与递归；`Array` 是连续数组，适合随机访问与 `push`。
两者的高阶函数同名，例如 `map`、`filter`、`foldl`。
-/

#guard [1, 2, 3, 4].map (· * 2) = [2, 4, 6, 8] && [1, 2, 3, 4].filter (· % 2 = 0) = [2, 4]
#guard [1, 2, 3, 4].foldl (· + ·) 0 = 10
#guard #[1, 2, 3].map (· + 1) = #[2, 3, 4] && (#[1, 2, 3].push 4).size = 4
#guard #[1, 2, 3].set! 1 9 = #[1, 9, 3] && #[1, 2, 3].modify 1 (· * 10) = #[1, 20, 3]
#guard Array.replicate 3 false = #[false, false, false] && Array.range 4 = #[0, 1, 2, 3]
#guard (Array.ofFn (n := 4) fun i ↦ i.val * i.val) = #[0, 1, 4, 9]

/-!
**三种下标。** `xs[i]?` 返回 `Option`；`xs[i]!` 越界时报 panic 并返回 `default`；`xs[i]` 要求
**证明** `i < xs.size`，Lean 先试 `get_elem_tactic`，它认得字面量下标、上下文里的 `h : i < xs.size`、
`if h : … then` 分支，以及 `for h : i in 0...xs.size` 带来的 `h`（§4）。显式给证明写 `xs[i]'h`。
证明写不出来就是错误（§12）。
-/

#guard [1, 2, 3][1]? = some 2 && [1, 2, 3][5]? = none
#guard #[1, 2, 3][1]! = 2 && #[1, 2, 3][7]? = none

example : #[1, 2, 3][1] = 2 := rfl          -- 字面量下标，证明自动给出

example (xs : Array ℕ) (i : ℕ) (h : i < xs.size) : ℕ := xs[i]    -- 上下文里的 `h`

def getOr (xs : Array ℕ) (i : ℕ) : ℕ :=
  if h : i < xs.size then xs[i] else 0       -- `h` 让 `xs[i]` 通过检查

#guard getOr #[5, 6, 7] 1 = 6 && getOr #[5, 6, 7] 9 = 0

/--
info: Error: index out of bounds
---
info: 0
-/
#guard_msgs in
#eval #[1, 2, 3][5]!

/-!
## 4. 循环与可变局部变量

`for x in xs do` 遍历任何有 `ForIn` 实例的集合，`for c in s do` 逐字符遍历字符串。整数区间写
`a...b`，它是**半开**区间 `[a, b)`，所以 `0...n` 不含 `n`；闭区间写 `a...=b`。旧资料里的
`[0:n]` 在核心库源码里仍保留，本章未实测。循环里要修改的变量用 `let mut` 声明、`:=` 赋值。

纯函数里想写循环，就用 `Id.run do`。`do` 是书写顺序步骤的语法（§6 解释它背后的单子接口）；
`Id` 是什么副作用也没有的单子，`Id.run` 把它的结果取出来，所以整体仍是纯函数。4.32 起 `do` 由
新的 elaborator（精译器；另译繁饰器）处理；日常写法不变，本章所有 `do` 代码都在它下面通过，
§12 第 3 条的报错文字也出自它。
-/

def sumBelow (n : ℕ) : ℕ := Id.run do
  let mut s := 0
  for i in 0...n do
    s := s + i
  return s
-- sumBelow 3：s 依次为 0（初值）→ 0（i = 0 后）→ 1（i = 1 后）→ 3（i = 2 后）

def sumUpTo (n : ℕ) : ℕ := Id.run do
  let mut s := 0
  for i in 0...=n do
    s := s + i
  return s

def countVowels (s : String) : ℕ := Id.run do
  let mut n := 0
  for c in s do
    if "aeiou".contains c then n := n + 1
  return n

#guard sumBelow 5 = 10 && sumUpTo 5 = 15
#guard countVowels "functional programming" = 7

/-!
`break` 结束当前循环，`continue` 进入下一轮，`while` 同理。`return e` 让它所属的 `do` 块立即以
`pure e` 结束，跳过其余语句。`for … do` 里的 `do` 不另成一块，所以 `firstAbove` 的 `return` 结束的是
整个 `Id.run do`；另写的 `do` 项（如 `show Id ℕ from do …`）自成一块，其中的 `return` 只结束这个
内层块，外层循环照常继续（`capAll` 遇到 `9` 之后还处理了 `3`）：
-/

def firstAbove (xs : List ℕ) (b : ℕ) : Option ℕ := Id.run do
  for x in xs do
    if x > b then return some x
  return none

def capAll (xs : List ℕ) (b : ℕ) : List ℕ := Id.run do
  let mut out := []
  for x in xs do
    let y ← show Id ℕ from do
      if x > b then return b         -- 只结束内层 `do`
      return x
    out := y :: out
  return out.reverse

#guard firstAbove [1, 5, 9] 4 = some 5 && firstAbove [1, 2] 4 = none
#guard capAll [1, 9, 3] 5 = [1, 5, 3]

def oddSumUntil7 : ℕ := Id.run do
  let mut i := 0
  let mut acc := 0
  while i < 10 do
    i := i + 1
    if i % 2 = 0 then continue
    if i > 7 then break
    acc := acc + i
  return acc

#guard oddSumUntil7 = 16        -- 1 + 3 + 5 + 7

/-!
**带证明的下标循环。** `for h : i in 0...xs.size do` 把 `h : i ∈ 0...xs.size` 带进循环体，
`get_elem_tactic` 认得它，所以直接写 `xs[i]`，不必用 `!`：
-/

def sumArray (xs : Array ℕ) : ℕ := Id.run do
  let mut s := 0
  for h : i in 0...xs.size do
    s := s + xs[i]
  return s

#guard sumArray #[1, 2, 3, 4] = 10

/-!
## 5. `Std.HashMap`

统计每个词出现了几次、每条 edge（边）出现了几次，都需要「键 → 值」的表。`Std.HashMap α β` 是
hash map（哈希表），要求键类型有 `BEq` 与 `Hashable` 实例（§8 用 `deriving` 得到）。
常用操作：`{}`（空表；也可写 `Std.HashMap.emptyWithCapacity n`）、`insert`、`m[k]?`、`getD`、
`contains`、`erase`、`size`。遍历顺序是实现细节（文档只说「in some order」），要稳定输出就先
排序（下面的 `sortedPairs`）。`wordCount` 只按 ASCII 空格 `" "` 切分；`splitOn` 在连续或首尾
空格处留下空串 `""`，所以要跳过空片段，否则空串也会被当成一个词。
-/

def wordCount (s : String) : Std.HashMap String ℕ := Id.run do
  let mut m : Std.HashMap String ℕ := {}
  for w in s.splitOn " " do
    if w.isEmpty then continue
    m := m.insert w (m.getD w 0 + 1)
  return m

def sortedPairs (m : Std.HashMap String ℕ) : List (String × ℕ) :=
  m.toList.mergeSort fun a b ↦ a.1 ≤ b.1

#guard " a  b".splitOn " " = ["", "a", "", "b"]                  -- 空片段
#guard (wordCount "").isEmpty && (wordCount " a  b a ").size = 2
#guard (wordCount "a b a c a b")["a"]? = some 3 && (wordCount "a b a c a b")["z"]? = none
#guard (wordCount "a b").contains "b" && ((wordCount "a b").erase "a").size = 1
#guard (Std.HashMap.emptyWithCapacity 8 : Std.HashMap ℕ ℕ).isEmpty
#guard sortedPairs (wordCount " a b  a c a b ") = [("a", 3), ("b", 2), ("c", 1)]

/-!
> 模块系统提示：`module` 文件里的 `#eval` 与 `#guard` 先把表达式编译成 `meta` 定义，其中用到的
> 导入定义必须在元阶段可用。`Std.HashMap` 的函数需要这一点，所以文件头多了
> `public meta import Std.Data.HashMap`。（只有 `public import` 时的报错「… is not accessible
> here」出自另一个试验文件，本文件不重现；同类报错见 §12 第 5 条。）`meta` 见第 26、28 章。
-/

/-!
## 6. 单子：`do` 记号背后的公共接口

`do` 块不是魔法：`let x ← e; rest` 是 `e >>= fun x ↦ rest`（`bind`），`return a` 是 `pure a`。
任何有 `Monad` 实例的类型都能用 `do`、`for`、`mapM`。单子的用途是把「带上下文的步骤」串起来：
上下文可以是可能的失败（`Option`、`Except`）、一份状态（`StateM`）或外部世界（`IO`），`bind`
规定上下文如何在两步之间传递。第一个例子是 `Option`：「任何一步是 `none`，整体就是 `none`」
成了默认行为。functor（函子）的 `<$>` 是 `map`。
-/

#guard ((· + 1) <$> some 2) = some 3
#guard (some 3 >>= fun x ↦ if x > 2 then some (x * 2) else none) = some 6

def addOpt (a b : Option ℕ) : Option ℕ := do
  let x ← a
  let y ← b
  return x + y

-- `do` 块就是 `bind` 链：
example : addOpt = fun a b ↦ a >>= fun x ↦ b >>= fun y ↦ pure (x + y) := rfl

#guard addOpt (some 1) (some 2) = some 3 && addOpt (some 1) none = none
#guard [1, 2, 3].mapM (fun x ↦ if x > 0 then some x else none) = some [1, 2, 3]
#guard [1, 0, 3].mapM (fun x ↦ if x > 0 then some x else none) = none

/-!
**自己的单子。** 下面的 `Maybe` 与 `Option` 同构。只要给出 `pure` 与 `bind`，`Monad` 的其余部分
（包括 `Functor` 的 `map`）都有默认实现，`do` 立刻可用：
-/

inductive Maybe (α : Type) where
  | nothing : Maybe α
  | just : α → Maybe α
  deriving DecidableEq

instance : Monad Maybe where
  pure := .just
  bind m f := match m with
    | .nothing => .nothing
    | .just a => f a

def Maybe.div (a b : ℕ) : Maybe ℕ := if b = 0 then .nothing else .just (a / b)

def Maybe.twice (a b : ℕ) : Maybe ℕ := do
  let x ← Maybe.div a b
  let y ← Maybe.div x b
  return x + y

#guard Maybe.twice 8 2 = .just 6 && Maybe.twice 8 0 = .nothing
#guard ((· + 1) <$> Maybe.div 8 2) = .just 5      -- `map` 来自 `bind` 的默认实现

/-!
**错误用 `Except`。** `Except ε α` 是 `ok a` 或 `error e`；`throw` 抛出，`try … catch` 捕获，
`match` 直接拆开。与 `Option` 相比它保留了出错原因（对照第 6 章 `Option` 版的 `safeDiv`：
那里只能返回 `none`）。同一个 `mapM` 换到 `Except` 上照样工作：
-/

def safeDiv (a b : ℕ) : Except String ℕ :=
  if b = 0 then throw "division by zero" else pure (a / b)

def divTwice (a b : ℕ) : Except String ℕ := do
  let x ← safeDiv a b
  let y ← safeDiv x b
  return x + y

/-- info: Except.ok 6 -/
#guard_msgs in
#eval divTwice 8 2

/-- info: Except.error "division by zero" -/
#guard_msgs in
#eval divTwice 8 0

/-- info: Except.error "division by zero" -/
#guard_msgs in
#eval [1, 0, 3].mapM (safeDiv 6)

#guard (match safeDiv 6 3 with | .ok v => v | .error _ => 0) = 2

def recovered : Except String ℕ := do
  try
    throw "x"
  catch _ =>
    pure 1

#guard recovered.toOption = some 1               -- `catch` 吃掉了错误

/-!
**状态用 `StateM`。** `StateM σ α` 是 monad transformer（单子转换器）`StateT σ` 套在 `Id` 上；
转换器本书不展开（FPIL 的「Monad Transformers」一章详述）。它表示读写一个类型为 `σ` 的状态的
计算：`get` 读状态，`modify` 改状态，`.run s` 返回 `(结果, 末状态)`。程序仍是纯函数，状态由
单子悄悄传递，这正是 §10 线程化随机数发生器的做法。
-/

example : StateM ℕ Unit = StateT ℕ Id Unit := rfl

def tick : StateM ℕ Unit := modify (· + 1)

def labelAll (xs : List String) : StateM ℕ (List (ℕ × String)) := do
  let mut out := []
  for x in xs do
    out := ((← get), x) :: out
    tick
  return out.reverse
-- labelAll ["a", "b", "c"] 从状态 10 开始：状态 10 →（a）11 →（b）12 →（c）13

/-- info: ([(10, "a"), (11, "b"), (12, "c")], 13) -/
#guard_msgs in
#eval (labelAll ["a", "b", "c"]).run 10

/-!
## 7. `IO`、`main` 与读一行输入

`IO α` 是会与外界交互的计算，`IO.println` 打印；`#eval` 一个 `IO` 动作就是运行它，打印的内容成为
消息。编译成可执行文件时入口是根命名空间下的 `main`（据 FPIL「Hello, World!」，类型可以是
`IO Unit`，也可以带参数 `List String` 并返回 `IO UInt32`；本章未实测）。本章的函数都在命名空间
里，这里不定义根命名空间的 `main`，而是用 `#eval` 调用。
-/

def hello : IO Unit := do
  IO.println "Hello, world!"
  IO.println s!"1 + 1 = {1 + 1}"

/--
info: Hello, world!
1 + 1 = 2
-/
#guard_msgs in
#eval hello

/-!
读一行输入：`IO.getStdin` 取标准输入流，`getLine` 读到换行并连换行一起返回。为了让 `#eval`
可复现，`withInput` 用 `IO.withStdin` 把标准输入临时换成内存缓冲区（`IO.mkRef` 造一个可变引用）。
它只为本章的测试与练习服务：用法是 `withInput "文本" 动作`，让动作读到这段文本。
-/

def readLine : IO String := do
  let stdin ← IO.getStdin
  stdin.getLine

def withInput {α : Type} (input : String) (act : IO α) : IO α := do
  let buf ← IO.mkRef ({ data := input.toUTF8 } : IO.FS.Stream.Buffer)
  IO.withStdin (IO.FS.Stream.ofBuffer buf) act

/-- info: "Lean\n" -/
#guard_msgs in
#eval withInput "Lean\n" readLine

/-!
`throw (IO.userError msg)` 抛错，`try … catch` 捕获；不捕获则 `#eval` 报错：
-/

/-- info: caught: boom -/
#guard_msgs in
#eval show IO Unit from do
  try
    throw (IO.userError "boom")
  catch e =>
    IO.println s!"caught: {e}"

/-- error: boom -/
#guard_msgs in
#eval (throw (IO.userError "boom") : IO Unit)

/-!
## 8. `deriving`：让 Lean 写实例

比较、打印、作哈希表的键，都要求类型有对应实例，手写很繁。`structure` 与 `inductive` 之后的
`deriving` 子句自动生成：`Repr`（`repr` 与 `#eval` 的标准打印）、`BEq`（`==`）、`Hashable`
（能作 `HashMap` 的键）、`DecidableEq`（命题 `=` 可判定，`decide` 能用）、`Inhabited`（有
`default`）、`Ord`（`compare`，按字段字典序）。`#eval` 遇到没有 `Repr` 的类型会自动派生一个
（选项 `eval.derive.repr`），所以只想看值时可以不写。
-/

structure Plain where
  x : ℕ

/-- info: { x := 1 } -/
#guard_msgs in
#eval ({ x := 1 } : Plain)

structure Edge where
  src : ℕ
  dst : ℕ
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Ord

/-- info: { src := 0, dst := 1 } -/
#guard_msgs in
#eval ({ src := 0, dst := 1 } : Edge)

/-- info: { src := 0, dst := 0 } -/
#guard_msgs in
#eval (default : Edge)

#guard compare ({ src := 0, dst := 1 } : Edge) { src := 0, dst := 2 } == .lt
#guard compare ({ src := 1, dst := 0 } : Edge) { src := 0, dst := 5 } == .gt
example : ({ src := 0, dst := 1 } : Edge) ≠ { src := 1, dst := 0 } := by decide

-- 有了 `Hashable`，`Edge` 就能作键：
def edgeMultiplicity (es : List Edge) : Std.HashMap Edge ℕ := Id.run do
  let mut m : Std.HashMap Edge ℕ := {}
  for e in es do
    m := m.insert e (m.getD e 0 + 1)
  return m

#guard (edgeMultiplicity [⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩])[(⟨0, 1⟩ : Edge)]? = some 2

/-!
## 9. 递归的三种形态：结构、良基、`partial`

**结构递归**见 §1。**良基递归**用 `termination_by` 给 termination measure（度量），定义默认
`@[irreducible]`，`decide` 卡住，要用 `simp [f]`（第 6 章 §9；机制见第 28 章）。本章只补一个新工具：
4.30 起正式可用的 `cbv`（按值调用式化简，4.29 引入时为实验性），它也适用于良基递归：
-/

def log2' (n : ℕ) : ℕ :=
  if n < 2 then 0 else log2' (n / 2) + 1
termination_by n

#guard log2' 1000 = 9

example : log2' 8 = 3 := by simp [log2']
example : log2' 8 = 3 := by cbv

/-!
**`partial def`** 定义 partial function（偏函数）：不要求终止证明，代价是它在 kernel（内核）里是
不透明常量，不能通过展开实现来证明它的计算结果（自反等式 `collatz 6 0 = collatz 6 0` 当然仍可证）。
Collatz 序列是否总停止至今未知，不知道终止性时这是最直接的写法：`#eval` 能跑，`decide` 卡住，
`simp [collatz]` 也没有进展。要验证这类函数，可以改写成带 fuel（燃料）参数的版本（第 25 章），
或者用参考手册里的 `partial_fixpoint`（本章未实测）。
-/

partial def collatz (n steps : ℕ) : ℕ :=
  if n ≤ 1 then steps
  else if n % 2 = 0 then collatz (n / 2) (steps + 1)
  else collatz (3 * n + 1) (steps + 1)

#guard collatz 27 0 = 111

/--
error: Tactic `decide` failed to reduce
  @decide (collatz 6 0 = 8) (instDecidableEqNat (collatz 6 0) 8)
to `true` or `false`.

After unfolding the instances `instDecidableEqNat` and `Nat.decEq`, reduction got stuck at
  (collatz 6 0).beq 8
-/
#guard_msgs in
example : collatz 6 0 = 8 := by decide

/-- error: `simp` made no progress -/
#guard_msgs in
example : collatz 6 0 = 8 := by simp [collatz]

example : collatz 6 0 = collatz 6 0 := rfl

/-!
## 10. 随机数：`StdGen` 与可复现的采样

核心库的随机数是纯函数式的：`mkStdGen seed : StdGen` 造发生器；在 `lo ≤ hi` 时，`randNat g lo hi`
返回**闭区间** `[lo, hi]` 里的一个自然数和**新的**发生器（`lo > hi` 时实现先交换两端，下面的
`#guard` 在 20 个种子上核对了这一点）。同一个种子永远给出同一串数，所以输出可以固定。
每次抽样都要把新发生器接着传下去，这正是 `StateM StdGen` 的工作。
-/

/-- info: (9, ⟨1720602, 40692⟩) -/
#guard_msgs in
#eval randNat (mkStdGen 42) 0 9

#guard (List.range 20).all fun s ↦ (randNat (mkStdGen s) 9 0).1 == (randNat (mkStdGen s) 0 9).1

def draw (lo hi : ℕ) : StateM StdGen ℕ := modifyGet fun g ↦ randNat g lo hi

def draws (n lo hi : ℕ) : StateM StdGen (List ℕ) := do
  let mut out := []
  for _ in 0...n do
    out := (← draw lo hi) :: out
  return out.reverse

/-- 用发生器 `g` 运行，丢掉末状态。 -/
def runWith {α : Type} (x : StateM StdGen α) (g : StdGen) : α := (Id.run (x.run g)).1

#guard runWith (draws 10 0 9) (mkStdGen 42) = [9, 9, 5, 2, 4, 9, 6, 9, 6, 3]
#guard runWith (draws 10 1 6) (mkStdGen 2026) = [6, 1, 2, 2, 4, 2, 6, 1, 2, 5]

/-!
**坑：小种子的第一个数有明显规律。** 种子 `0` 到 `9` 的第一次抽样依次是
`3, 5, 9, 3, 7, 1, 5, 9, 3, 7`：在这十个种子里，从种子 `1` 起每 5 个重复一次（这是所列样本的现象，
不是对所有种子的周期断言）。补救是抽样前先丢掉几个数：下面的 `seeded` 用 `stdNext` 把发生器推进
8 步，同样十个种子的结果里不再出现这种重复。这只是教学级补救，不保证消除别的相关性。
-/

#guard (List.range 10).map (fun s ↦ (randNat (mkStdGen s) 0 9).1) = [3, 5, 9, 3, 7, 1, 5, 9, 3, 7]

def seeded (seed : ℕ) : StdGen :=
  (List.range 8).foldl (fun g _ ↦ (stdNext g).2) (mkStdGen seed)

#guard (List.range 10).map (fun s ↦ (randNat (seeded s) 0 9).1) = [1, 0, 1, 0, 9, 8, 7, 7, 6, 5]

/-!
这个发生器只是教学用品：`stdNext` 的输出落在 `[1, 2147483562]`，约 31 位；`randNat` 只是近似
均匀（源码注释：假定底层发生器均匀，则各结果的概率至多相差因子 `1 ± 1/1000`）。认真的
Monte Carlo 模拟（尤其稀有事件、大偏差）请用专门的工具。
-/

#guard stdRange = (1, 2147483562)

/-!
**伯努利变量。** 为避开浮点数，用有理概率 `p = num/den`：抽 `x ∈ {0, …, den - 1}`，`x < num`
时成功。这要求 `0 < den` 且 `num ≤ den`：
-/

def bernoulli (num den : ℕ) : StateM StdGen Bool :=
  modifyGet fun g ↦
    let (x, g') := randNat g 0 (den - 1)
    (decide (x < num), g')

#guard runWith (bernoulli 1 2) (mkStdGen 42) = false
#guard runWith (bernoulli 0 7) (mkStdGen 42) = false && runWith (bernoulli 7 7) (mkStdGen 42) = true

/-!
**坑：`den = 0`。** 此时 `den - 1` 被 `ℕ` 的截断减法吃成 `0`（第 2 章的垃圾值），抽到的永远是
`0`，于是任何 `num > 0` 都「成功」：
-/

#guard runWith (bernoulli 3 0) (mkStdGen 42) = true

/-!
**全局发生器。** `IO.setRandSeed n` 把它设为 `mkStdGen n`，`IO.rand lo hi` 从中取数；它藏在 `IO`
里，不如显式线程化的 `StateM StdGen` 好测试：
-/

/-- info: 9 -/
#guard_msgs in
#eval show IO ℕ from do
  IO.setRandSeed 42
  IO.rand 0 9

/-!
## 11. 案例：模拟 G(n,p)，统计度与三角形

二项随机图（第 20 章）：`n` 个 vertex（顶点），每对顶点独立地以概率 `p` 连边。下面把它写成程序：邻接矩阵用
`Array (Array Bool)`，每对 `j < i` 抽一次伯努利变量。**注意**：这是一个可计算的采样器；第 20 章的
`SimpleGraph.binomialRandom` 是 `SimpleGraph V` 上的**测度**，二者不是同一类对象，桥梁见本节后半。
下标由循环范围保证在界内，所以这里用 `!` 与 `set!`，让循环体保持简短。`gnp` 输出的矩阵是对称的，
对角线全为 `false`。
-/

def gnp (n num den : ℕ) : StateM StdGen (Array (Array Bool)) := do
  let mut A := Array.replicate n (Array.replicate n false)
  for i in 0...n do
    for j in 0...i do
      if (← bernoulli num den) then
        A := A.modify i (·.set! j true)
        A := A.modify j (·.set! i true)
  return A

def degrees (A : Array (Array Bool)) : Array ℕ :=
  A.map fun row ↦ row.foldl (fun c b ↦ if b then c + 1 else c) 0

def triangles (A : Array (Array Bool)) : ℕ := Id.run do
  let mut t := 0
  for i in 0...A.size do
    for j in 0...i do
      for k in 0...j do
        if A[i]![j]! && A[i]![k]! && A[j]![k]! then t := t + 1
  return t

def sample6 : Array (Array Bool) := runWith (gnp 6 1 2) (seeded 2026)

#guard degrees sample6 = #[4, 3, 5, 5, 4, 3] && triangles sample6 = 10

/-!
**Monte Carlo 检查。** 第 20 章会证明三角形个数的 expectation（期望）是 `C(n,3) p³`。取 `n = 10`、`p = 1/2`：
`C(10,3) = 120`，每个图期望 15 个三角形，200 个图合计期望 3000。把同一个发生器线程化地传过
200 次模拟，数出实际总数：
-/

example : Nat.choose 10 3 = 120 := by decide

def triangleTotal (n num den trials : ℕ) : StateM StdGen ℕ := do
  let mut total := 0
  for _ in 0...trials do
    total := total + triangles (← gnp n num den)
  return total

/-- info: 3032 -/
#guard_msgs in
#eval runWith (triangleTotal 10 1 2 200) (seeded 1)

/-!
这只是一个具体种子下的一条样本路径，说明采样器没有明显写错，并不证明任何概率命题。

**桥接到 `SimpleGraph (Fin n)`。** 目标：让 Mathlib 一侧的 `degree`、`cliqueFinset` 也能在
邻接矩阵上被 `decide` 算出来，与程序一侧的数字对照。分三步。

第一步，造图。`SimpleGraph.fromRel r` 把任意关系 `r` 对称化并去掉自环：
`Adj a b ↔ a ≠ b ∧ (r a b ∨ r b a)`。`adjAt` 对越界下标返回 `false`：
-/

def adjAt (A : Array (Array Bool)) (n : ℕ) (i j : Fin n) : Bool :=
  (A[i.val]?.bind (·[j.val]?)).getD false

def toSimpleGraph (A : Array (Array Bool)) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ adjAt A n i j = true

/-!
第二步，补实例。`degree`、`edgeFinset`、`cliqueFinset` 需要 `DecidableRel G.Adj`。`toSimpleGraph`
是普通 `def`，实例搜索默认不展开它，所以像第 18 章 §1 那样用 `inferInstanceAs` 把 `fromRel` 的
实例重新声明给它（`r` 是 `Bool` 判等，故可判定）：
-/

instance (A : Array (Array Bool)) (n : ℕ) : DecidableRel (toSimpleGraph A n).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ adjAt A n i j = true).Adj)

/-!
第三步，核对。在完全图 `K₄` 与路径图 `0 - 1 - 2` 上比较两侧：程序一侧是 `degrees`、`triangles`
（`#guard`），Mathlib 一侧是 `degree`、`cliqueFinset`、`edgeFinset`（`decide`）。这是在两个具体图上
核对，不是证明。`triangles` 数 `i > j > k` 且三个邻接位同时为真的三元组，`is3Clique_triple_iff`
（第 18 章）说三元集合是 3-clique（3-团）当且仅当三对顶点两两 adjacent（相邻），正是这三个条件。一般情形下，
三角形个数一致要求矩阵是对称的 `n × n` 矩阵；`degrees` 之和等于边数的两倍还要求对角线全为
`false`（`fromRel` 去掉了自环）。handshaking lemma（握手引理）`∑ v, G.degree v = 2 * G.edgeFinset.card`
对任意有限图成立（需要 `Fintype V` 与 `DecidableRel G.Adj`，第 18 章）。
-/

def k4 : Array (Array Bool) := Array.ofFn (n := 4) fun i ↦ Array.ofFn (n := 4) fun j ↦ i != j

def path3 : Array (Array Bool) :=
  Array.ofFn (n := 3) fun i ↦ Array.ofFn (n := 3) fun j ↦ i.val + 1 == j.val || j.val + 1 == i.val

example : (toSimpleGraph k4 4).degree 0 = 3 := by decide
example : ((toSimpleGraph k4 4).cliqueFinset 3).card = 4 := by decide
#guard degrees k4 = #[3, 3, 3, 3] && triangles k4 = 4

example : (toSimpleGraph path3 3).edgeFinset.card = 2 := by decide
example : ((toSimpleGraph path3 3).cliqueFinset 3).card = 0 := by decide
#guard degrees path3 = #[1, 2, 1] && triangles path3 = 0

example (G : SimpleGraph (Fin 6)) (a b c : Fin 6) :
    G.IsNClique 3 {a, b, c} ↔ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c :=
  SimpleGraph.is3Clique_triple_iff

example (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj] :
    ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

/-!
## 12. 常见错误

不会留下名字的反例都写成 `example`，因为 `#guard_msgs` 只检查消息、不撤销声明，报错的 `def`
可能带着 `sorry` 留在环境里（第 6 章 §11）。

**1. 把切片当字符串。** `"hello".drop 2` 的类型是 `String.Slice`；需要 `String` 的地方要 `.copy`：
-/

/--
error: Type mismatch
  "hello".drop 2
has type
  String.Slice
but is expected to have type
  String
-/
#guard_msgs in
example : String := "hello".drop 2

/-!
**2. 下标没有证明。** `xs[i]` 里 `i` 是任意变量时，Lean 找不到 `i < xs.size` 的证明，报错并列出
四条出路：
-/

/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is
produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
xs : Array ℕ
i : ℕ
⊢ i < xs.size
-/
#guard_msgs in
example (xs : Array ℕ) (i : ℕ) : ℕ := xs[i]

/-!
**3. 忘了 `mut`。** 循环里给没有 `let mut` 的变量赋值：
-/

/--
error: Variable `s` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `s`, consider using `let s` instead
-/
#guard_msgs in
example (n : ℕ) : ℕ := Id.run do
  let s := 0
  for i in 0...n do
    s := s + i
  return s

/-!
**4. `deriving ToString`。** 核心库没有它的派生处理器，`ToString` 实例要自己写：
-/

/-- error: No deriving handlers have been implemented for class `ToString` -/
#guard_msgs in
deriving instance ToString for Plain

/-!
**5. 对 Mathlib 对象 `#eval`。** 在 `module` 文件里，`#eval` 用到的、尚未 `meta` 导入的定义不可访问。
报错点名了该加的导入；本章不加，改用 `decide`（它在精译器里规约，不经过编译出的 `meta` 代码）：
-/

/--
error: Invalid `meta` definition `_eval`, `Subtype.fintype` is not accessible here; consider adding
`public meta import Mathlib.Data.Fintype.Sets`
-/
#guard_msgs in
#eval (toSimpleGraph k4 4).degree 0

/-!
递归调用不递减时的终止性报错见第 6 章 §11 与第 25 章 §4，这里不重复。
-/

/-!
## 练习

下列各题的测试写在文档注释里，请把它们抄成 `#guard`（或 `#eval`）放在你的答案之后；
`Solutions/Part5/Ch24_Programming.lean` 里的测试与之等价。题目用到的辅助定义（`sumList`、
`log2'`、`withInput`、`Edge`、`runWith`、`toSimpleGraph`、`path3`、`Maybe` 等）都在本章前面。
ex_24_4 与 ex_24_12 到 ex_24_15 是定理，其余是程序。★ 直接应用，★★ 综合两个想法，★★★ 需要新想法。
其中 ex_24_3、ex_24_4、ex_24_12 到 ex_24_15 复习前面的章节（第 5、6、12、13、18 章）。
-/

/-- 练习 24.1（★）：把边列表按派生的 `Ord`（先比 `src`，再比 `dst`）从小到大排序，用 `compare`
与 `mergeSort`（§5、§8）。
`ex_24_1 [⟨1, 0⟩, ⟨0, 2⟩, ⟨0, 1⟩] = [⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩]`。 -/
def ex_24_1 (es : List Edge) : List Edge := sorry

/-- 练习 24.2（★）：把字符串循环左移一个字符，用 `drop`、`take` 与 `.copy`。
`ex_24_2 "hello" = "elloh"`，`ex_24_2 "a" = "a"`，`ex_24_2 "" = ""`。 -/
def ex_24_2 (s : String) : String := sorry

/-- 练习 24.3（★）：二进制位数，用 `termination_by`（第 6 章）。
`ex_24_3 0 = 0`，`ex_24_3 1 = 1`，`ex_24_3 8 = 4`，`ex_24_3 255 = 8`。 -/
def ex_24_3 (n : ℕ) : ℕ := sorry

/-- 练习 24.4（★）：复习第 18 章：`toSimpleGraph` 中每个顶点的度小于 `n`。
提示：`SimpleGraph.degree_lt_card_verts` 与 `Fintype.card_fin`。 -/
theorem ex_24_4 (A : Array (Array Bool)) (n : ℕ) (v : Fin n) :
    (toSimpleGraph A n).degree v < n := sorry

/-- 练习 24.5（★★）：解析形如 `"1+2+3"` 的和，任一段不是自然数则 `none`。
提示：`splitOn`、`toNat?`、`mapM`、`foldl`。
`ex_24_5 "1+2+3" = some 6`，`ex_24_5 "1+x" = none`。 -/
def ex_24_5 (s : String) : Option ℕ := sorry

/-- 练习 24.6（★★）：第一个偶数元素的下标，没有则 `none`；用 `for h : i in …` 与提前 `return`。
`ex_24_6 #[1, 3, 4, 6] = some 2`，`ex_24_6 #[1, 3] = none`。 -/
def ex_24_6 (xs : Array ℕ) : Option ℕ := sorry

/-- 练习 24.7（★★）：列表之和，但任一元素大于 `100` 就抛出 `"too large"`，用 `Except`。
`(ex_24_7 [1, 2, 3]).toOption = some 6`；对 `[1, 200]` 用 `match` 取出的错误信息是 `"too large"`。 -/
def ex_24_7 (xs : List ℕ) : Except String ℕ := sorry

/-- 练习 24.8（★★）：给每个非空字符串加上序号前缀 `"k:x"`，序号取自状态并在每次使用后加一；
空字符串原样保留且不消耗序号。
`Id.run ((ex_24_8 ["a", "", "b"]).run 1) = (["1:a", "", "2:b"], 3)`。 -/
def ex_24_8 (xs : List String) : StateM ℕ (List String) := sorry

/-- 练习 24.9（★★）：无向边的不同个数：`⟨0, 1⟩` 与 `⟨1, 0⟩` 算同一条。用 `HashMap`。
`ex_24_9 [⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩] = 2`，`ex_24_9 [] = 0`。 -/
def ex_24_9 (es : List Edge) : ℕ := sorry

/-- 练习 24.10（★★）：读两行标准输入，各应是一个自然数，打印它们的和；任一行不是自然数就
`throw (IO.userError "not a number")`。用 `readLine` 与 `withInput` 测试：
`withInput "3\n4\n" ex_24_10` 打印 `7`，`withInput "3\nx\n" ex_24_10` 报错 `not a number`。
提示：`getLine` 连换行一起返回（§7），先 `trimAscii.copy`（§2）再 `toNat?`。 -/
def ex_24_10 : IO Unit := sorry

/-- 练习 24.11（★★）：掷 `n` 次骰子（取值 `1` 到 `6`），返回 `6` 出现的次数；发生器必须线程化。
测试：对若干种子 `g = mkStdGen s`，`runWith (ex_24_11 n) g = (runWith (draws n 1 6) g).count 6`。 -/
def ex_24_11 (n : ℕ) : StateM StdGen ℕ := sorry

/-- 练习 24.12（★）：复习第 6 章的 `cases` 与 `rfl`，作用于本章 §6 的 `Maybe`：
`bind` 满足结合律。 -/
theorem ex_24_12 {α β γ : Type} (m : Maybe α) (f : α → Maybe β) (g : β → Maybe γ) :
    (m >>= f) >>= g = m >>= fun a ↦ f a >>= g := sorry

/-- 练习 24.13（★★）：复习第 6 章：`sumList` 与列表拼接可交换。 -/
theorem ex_24_13 (xs ys : List ℕ) : sumList (xs ++ ys) = sumList xs + sumList ys := sorry

/-- 练习 24.14（★★）：复习第 12、18 章：路径图 `0 - 1 - 2`（本章的 `path3`）转成
`SimpleGraph` 后有 `2` 条边，且中间顶点的度为 `2`。提示：`decide`。 -/
theorem ex_24_14 :
    (toSimpleGraph path3 3).edgeFinset.card = 2 ∧ (toSimpleGraph path3 3).degree 1 = 2 := sorry

/-- 练习 24.15（★★★）：复习第 5、6、13 章：`log2' n` 是满足 `2 ^ k ≤ n < 2 ^ (k + 1)` 的 `k`。
提示：对 `n` 强归纳（第 13 章 §3 的写法），展开 `log2'`，把 `2 ^ (k + 1)` 改写成 `2 ^ k * 2`
后用 `omega`。 -/
theorem ex_24_15 (n : ℕ) (h : 0 < n) : 2 ^ log2' n ≤ n ∧ n < 2 ^ (log2' n + 1) := sorry

/-!
## 小结

| 概念 | 语法 | 何时使用 |
|---|---|---|
| 结构递归 | `def f : List α → β \| [] => … \| x :: xs => … f xs …` | 递归调用作用在子项上；`rfl`/`decide` 可算 |
| 测试 | `#guard`（`Bool` 或可判定命题）；`#guard_msgs` 固定 `#eval` 输出 | 只运行程序，不是证明 |
| 失败 | `Option α`（`none`）；`Except ε α`（`throw`、`try … catch`、`.toOption`） | 不需原因用前者，需要原因用后者 |
| 字符串 | `drop`/`take`/`trimAscii`（返回 `Slice`）、`.copy`；`splitOn`、`toNat?` | 4.27 起；无 `String.trim` |
| 集合与下标 | `map`、`filter`、`foldl`；`xs[i]?`、`xs[i]!`、`xs[i]`（需证明） | 默认用 `?`；已知在界内用带证明的 |
| 循环 | `Id.run do`、`let mut`、`for i in 0...n`（不含 `n`）、`break`、`continue` | `return` 结束所属的 `do` 块 |
| 哈希表 | `{}`、`insert`、`m[k]?`、`getD`、`erase` | 键需 `BEq` 与 `Hashable`；先排序再输出 |
| 单子 | `pure`/`bind`、`do`、`mapM`、`<$>`；自定义时给出 `pure` 与 `bind` | `Option`、`Except`、`StateM`、`IO` 共用 |
| 状态 | `StateM σ`：`get`、`modify`、`modifyGet`、`.run s` | 线程化状态，如随机数发生器 |
| `IO` | `IO.println`、`IO.getStdin`、`getLine`、`try … catch` | 与外界交互；入口 `main`（本章未实测） |
| 派生 | `deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Ord` | 没有 `ToString` 派生 |
| 终止性 | 结构递归 / `termination_by` / `partial` | 良基：`simp [f]`、`cbv`；`partial`：不能靠展开证计算结果 |
| 随机数 | `mkStdGen`、`randNat g lo hi`（`lo ≤ hi`）、`seeded`、`IO.rand` | 可复现；教学用 |
| 桥接 | `SimpleGraph.fromRel` + `DecidableRel` + `decide` | 把可计算数据接到 Mathlib 的 `Prop` 世界 |

## 延伸阅读

- 《Lean 函数式编程》*Functional Programming in Lean*
  （`https://lean-lang.org/functional_programming_in_lean/`）：「Getting to Know Lean」「Hello, World!」
  「Monads」「Monad Transformers」等章（章名取自目录页，未逐节核对）；API 名以本章（4.35）为准。
- *Lean Language Reference* 4.35.0（`https://lean-lang.org/doc/reference/4.35.0/`）：「Basic Types」
  「Functors, Monads and `do`-Notation」「IO」「Definitions」（`partial_fixpoint` 在此查；小节名未核对）。
- Lean 核心源码：`Init/Data/Random.lean`（`StdGen`、`mkStdGen`、`randNat`、`IO.rand`）、
  `Init/Data/String/TakeDrop.lean`（切片版 `take`/`drop`）、
  `Init/Data/Range/Polymorphic/PRange.lean`（`a...b` 区间）、`Std/Data/HashMap/Basic.lean`。
- Mathlib：`Mathlib/Combinatorics/SimpleGraph/Basic.lean`（`fromRel`）、`Finite.lean`（`degree`）、
  `DegreeSum.lean`（握手引理）、`Clique.lean`（`cliqueFinset`、`is3Clique_triple_iff`）。
- 本书第 6 章（递归与 `deriving`）、第 18 章（`SimpleGraph`）、第 20 章（`binomialRandom` 与三角形
  的期望）、第 25 章（证明程序的性质、`fun_induction`）、第 26 章（`meta` 与模块系统）。
-/

end Lean4Learn.Ch24

end
