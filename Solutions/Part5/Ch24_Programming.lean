module

public meta import Std.Data.HashMap
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.TypeStar
public import Std.Data.HashMap

/-!
# 第 24 章　答案

`Lean4Learn/Part5/Ch24_Programming.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同；
每个程序后面的 `#guard`（或 `#eval`）与题目文档注释里的测试等价。章节里的辅助定义（`sumList`、
`log2'`、`Maybe`、`Edge`、`draw`、`draws`、`runWith`、`readLine`、`withInput`、`adjAt`、
`toSimpleGraph`、`path3`）在这里原样重复，使本文件自成一体。
-/

@[expose] public section

namespace Solutions.Ch24

def sumList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sumList xs

def log2' (n : ℕ) : ℕ :=
  if n < 2 then 0 else log2' (n / 2) + 1
termination_by n

inductive Maybe (α : Type) where
  | nothing : Maybe α
  | just : α → Maybe α
  deriving DecidableEq

instance : Monad Maybe where
  pure := .just
  bind m f := match m with
    | .nothing => .nothing
    | .just a => f a

structure Edge where
  src : ℕ
  dst : ℕ
  deriving Repr, BEq, Hashable, DecidableEq, Inhabited, Ord

def draw (lo hi : ℕ) : StateM StdGen ℕ := modifyGet fun g ↦ randNat g lo hi

def draws (n lo hi : ℕ) : StateM StdGen (List ℕ) := do
  let mut out := []
  for _ in 0...n do
    out := (← draw lo hi) :: out
  return out.reverse

def runWith {α : Type} (x : StateM StdGen α) (g : StdGen) : α := (Id.run (x.run g)).1

def readLine : IO String := do
  let stdin ← IO.getStdin
  stdin.getLine

def withInput {α : Type} (input : String) (act : IO α) : IO α := do
  let buf ← IO.mkRef ({ data := input.toUTF8 } : IO.FS.Stream.Buffer)
  IO.withStdin (IO.FS.Stream.ofBuffer buf) act

def adjAt (A : Array (Array Bool)) (n : ℕ) (i j : Fin n) : Bool :=
  (A[i.val]?.bind (·[j.val]?)).getD false

def toSimpleGraph (A : Array (Array Bool)) (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j ↦ adjAt A n i j = true

instance (A : Array (Array Bool)) (n : ℕ) : DecidableRel (toSimpleGraph A n).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ adjAt A n i j = true).Adj)

def path3 : Array (Array Bool) :=
  Array.ofFn (n := 3) fun i ↦ Array.ofFn (n := 3) fun j ↦ i.val + 1 == j.val || j.val + 1 == i.val

/-- 练习 24.1（★）：把边列表按派生的 `Ord`（先比 `src`，再比 `dst`）从小到大排序，用 `compare`
与 `mergeSort`（§5、§8）。
`ex_24_1 [⟨1, 0⟩, ⟨0, 2⟩, ⟨0, 1⟩] = [⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩]`。 -/
def ex_24_1 (es : List Edge) : List Edge := es.mergeSort fun a b ↦ compare a b != .gt
-- `mergeSort` 要一个 `Bool` 值的 `≤`：「不大于」就是 `compare a b != .gt`。
#guard ex_24_1 [⟨1, 0⟩, ⟨0, 2⟩, ⟨0, 1⟩] = [⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 0⟩] && ex_24_1 [] = []

/-- 练习 24.2（★）：把字符串循环左移一个字符，用 `drop`、`take` 与 `.copy`。
`ex_24_2 "hello" = "elloh"`，`ex_24_2 "a" = "a"`，`ex_24_2 "" = ""`。 -/
def ex_24_2 (s : String) : String := (s.drop 1).copy ++ (s.take 1).copy
-- `drop`/`take` 返回切片，`.copy` 变回 `String` 再用 `++` 拼接。
#guard ex_24_2 "hello" = "elloh" && ex_24_2 "a" = "a" && ex_24_2 "" = ""

/-- 练习 24.3（★）：二进制位数，用 `termination_by`（第 6 章）。
`ex_24_3 0 = 0`，`ex_24_3 1 = 1`，`ex_24_3 8 = 4`，`ex_24_3 255 = 8`。 -/
def ex_24_3 (n : ℕ) : ℕ := if n = 0 then 0 else 1 + ex_24_3 (n / 2)
termination_by n
-- 度量下降 `n / 2 < n`（在 `n ≠ 0` 时）由默认策略自动证明，不必写 `decreasing_by`。
#guard ex_24_3 0 = 0 && ex_24_3 1 = 1 && ex_24_3 8 = 4 && ex_24_3 255 = 8

/-- 练习 24.4（★）：复习第 18 章：`toSimpleGraph` 中每个顶点的度小于 `n`。
提示：`SimpleGraph.degree_lt_card_verts` 与 `Fintype.card_fin`。 -/
theorem ex_24_4 (A : Array (Array Bool)) (n : ℕ) (v : Fin n) :
    (toSimpleGraph A n).degree v < n := by
  have := (toSimpleGraph A n).degree_lt_card_verts v
  simpa using this
-- `degree_lt_card_verts` 给出 `< Fintype.card (Fin n)`，`simp` 化成 `< n`。

/-- 练习 24.5（★★）：解析形如 `"1+2+3"` 的和，任一段不是自然数则 `none`。
提示：`splitOn`、`toNat?`、`mapM`、`foldl`。
`ex_24_5 "1+2+3" = some 6`，`ex_24_5 "1+x" = none`。 -/
def ex_24_5 (s : String) : Option ℕ :=
  ((s.splitOn "+").mapM String.toNat?).map (·.foldl (· + ·) 0)
-- `mapM` 在 `Option` 里：任何一段 `toNat?` 失败则整体 `none`。
#guard ex_24_5 "1+2+3" = some 6 && ex_24_5 "1+x" = none && ex_24_5 "7" = some 7

/-- 练习 24.6（★★）：第一个偶数元素的下标，没有则 `none`；用 `for h : i in …` 与提前 `return`。
`ex_24_6 #[1, 3, 4, 6] = some 2`，`ex_24_6 #[1, 3] = none`。 -/
def ex_24_6 (xs : Array ℕ) : Option ℕ := Id.run do
  for h : i in 0...xs.size do
    if xs[i] % 2 = 0 then return some i
  return none
-- 带证明的下标循环（§4）；`return` 提前结束。
#guard ex_24_6 #[1, 3, 4, 6] = some 2 && ex_24_6 #[1, 3] = none

/-- 练习 24.7（★★）：列表之和，但任一元素大于 `100` 就抛出 `"too large"`，用 `Except`。
`(ex_24_7 [1, 2, 3]).toOption = some 6`；对 `[1, 200]` 用 `match` 取出的错误信息是 `"too large"`。 -/
def ex_24_7 (xs : List ℕ) : Except String ℕ := do
  let mut total := 0
  for x in xs do
    if x > 100 then throw "too large"
    total := total + x
  return total
-- `throw` 在 `for` 里也能用；`Except` 的 `do` 一遇到 `throw` 就终止。
#guard (ex_24_7 [1, 2, 3]).toOption = some 6
#guard (match ex_24_7 [1, 200] with | .error e => e == "too large" | .ok _ => false)

/-- 练习 24.8（★★）：给每个非空字符串加上序号前缀 `"k:x"`，序号取自状态并在每次使用后加一；
空字符串原样保留且不消耗序号。
`Id.run ((ex_24_8 ["a", "", "b"]).run 1) = (["1:a", "", "2:b"], 3)`。 -/
def ex_24_8 (xs : List String) : StateM ℕ (List String) := do
  let mut out : List String := []
  for x in xs do
    if x.isEmpty then
      out := x :: out
    else
      let k ← get
      out := s!"{k}:{x}" :: out
      modify (· + 1)
  return out.reverse
-- 状态 `ℕ` 同时是序号；只有非空字符串才 `modify`。
#guard Id.run ((ex_24_8 ["a", "", "b"]).run 1) = (["1:a", "", "2:b"], 3)

/-- 练习 24.9（★★）：无向边的不同个数：`⟨0, 1⟩` 与 `⟨1, 0⟩` 算同一条。用 `HashMap`。
`ex_24_9 [⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩] = 2`，`ex_24_9 [] = 0`。 -/
def ex_24_9 (es : List Edge) : ℕ := Id.run do
  let mut m : Std.HashMap Edge Unit := {}
  for e in es do
    m := m.insert (if e.src ≤ e.dst then e else ⟨e.dst, e.src⟩) ()
  return m.size
-- 先把每条边规范成 `src ≤ dst`，再用表的键去重。
#guard ex_24_9 [⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩] = 2 && ex_24_9 [] = 0

/-- 练习 24.10（★★）：读两行标准输入，各应是一个自然数，打印它们的和；任一行不是自然数就
`throw (IO.userError "not a number")`。用 `readLine` 与 `withInput` 测试：
`withInput "3\n4\n" ex_24_10` 打印 `7`，`withInput "3\nx\n" ex_24_10` 报错 `not a number`。
提示：`getLine` 连换行一起返回（§7），先 `trimAscii.copy`（§2）再 `toNat?`。 -/
def ex_24_10 : IO Unit := do
  let a ← readLine
  let b ← readLine
  match a.trimAscii.copy.toNat?, b.trimAscii.copy.toNat? with
  | some x, some y => IO.println s!"{x + y}"
  | _, _ => throw (IO.userError "not a number")

/-- info: 7 -/
#guard_msgs in
#eval withInput "3\n4\n" ex_24_10

/-- error: not a number -/
#guard_msgs in
#eval withInput "3\nx\n" ex_24_10

/-- 练习 24.11（★★）：掷 `n` 次骰子（取值 `1` 到 `6`），返回 `6` 出现的次数；发生器必须线程化。
测试：对若干种子 `g = mkStdGen s`，`runWith (ex_24_11 n) g = (runWith (draws n 1 6) g).count 6`。 -/
def ex_24_11 (n : ℕ) : StateM StdGen ℕ := do
  let mut c := 0
  for _ in 0...n do
    if (← draw 1 6) = 6 then c := c + 1
  return c
-- 每次 `draw` 都从状态里取新发生器；若每次重造发生器，计数会与 `draws` 不一致。
#guard (List.range 8).all fun s ↦
  runWith (ex_24_11 50) (mkStdGen s) = (runWith (draws 50 1 6) (mkStdGen s)).count 6
#guard runWith (ex_24_11 0) (mkStdGen 7) = 0

/-- 练习 24.12（★）：复习第 6 章的 `cases` 与 `rfl`，作用于本章 §6 的 `Maybe`：
`bind` 满足结合律。 -/
theorem ex_24_12 {α β γ : Type} (m : Maybe α) (f : α → Maybe β) (g : β → Maybe γ) :
    (m >>= f) >>= g = m >>= fun a ↦ f a >>= g := by
  cases m <;> rfl
-- 两个分支两边都按 `bind` 的定义规约到同一项。

/-- 练习 24.13（★★）：复习第 6 章：`sumList` 与列表拼接可交换。 -/
theorem ex_24_13 (xs ys : List ℕ) : sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih =>
    simp only [List.cons_append, sumList, ih]
    omega
-- 对 `xs` 归纳；两个分支都只需展开 `sumList` 与线性算术。

/-- 练习 24.14（★★）：复习第 12、18 章：路径图 `0 - 1 - 2`（本章的 `path3`）转成
`SimpleGraph` 后有 `2` 条边，且中间顶点的度为 `2`。提示：`decide`。 -/
theorem ex_24_14 :
    (toSimpleGraph path3 3).edgeFinset.card = 2 ∧ (toSimpleGraph path3 3).degree 1 = 2 := by
  decide
-- 小图上两侧都可判定，`decide` 直接算；一般情形需要对 `A` 的条件。

/-- 练习 24.15（★★★）：复习第 5、6、13 章：`log2' n` 是满足 `2 ^ k ≤ n < 2 ^ (k + 1)` 的 `k`。
提示：对 `n` 强归纳（第 13 章 §3 的写法），展开 `log2'`，把 `2 ^ (k + 1)` 改写成 `2 ^ k * 2`
后用 `omega`。 -/
theorem ex_24_15 (n : ℕ) (h : 0 < n) : 2 ^ log2' n ≤ n ∧ n < 2 ^ (log2' n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [log2']
    by_cases h2 : n < 2
    · simp [h2]
      omega
    · have ih' := ih (n / 2) (by omega) (by omega)
      simp only [h2, ↓reduceIte]
      simp only [pow_succ] at ih' ⊢
      omega
-- 把 `2 ^ log2' (n / 2)` 当作原子，剩下的是线性算术（`omega` 也懂 `n / 2`）。

end Solutions.Ch24

end
