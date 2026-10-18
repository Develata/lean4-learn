module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# 第 2 章　从 NNG 到 Mathlib：计算与重写

Natural Number Game（NNG）里你用 `rw` 和 `induction` 从头证明了加法交换律。本章把这些动作搬到真正的 `ℕ`
上，认识 Lean 里几条违背直觉的约定（junk value（垃圾值）、truncated subtraction（截断减法）），再沿一条
「自动化阶梯」往上走：`norm_num`（数值）、`ring`（环里的恒等式）、`omega`（`ℕ` 与 `ℤ` 上的线性算术）、
`linarith` 与 `nlinarith`（不等式）、`positivity`（正性）、simplifier（简化器）`simp`。最后用 `calc` 把多步
推理串成一条链，用 `exact?` 找 lemma（引理），并认识 coercion（强制转换）`↑n`。大多数 tactic（策略）除了成功的
例子，还配一个由 `#guard_msgs` 固定下来的失败例子，让你知道它的边界。读完后你能为一个代数或不等式计算选对
工具，并看懂它失败时的 error message（错误信息）。

## 学习目标
- 会用 `theorem` 给结论起名并在之后的证明里引用它，会用 term-mode（项模式）与 tactic-mode（策略模式）写同一个
  等式证明；认得 `ℕ` 专用的 `Nat.add_comm` 与通用版本 `add_comm`。
- 会用 `rw` 和归纳；会读归纳产生的两个 goal（目标）里的 `0` 与 `n + 1`。
- 按「数值 → 环恒等式 → 线性算术 → 不等式 → 正性」的顺序选择 `norm_num`、`ring`、`omega`、`linarith`、
  `nlinarith`、`positivity`，并说出每个策略的失败边界。
- 区分垃圾值（数学里没有定义的运算取的值，如 `x / 0 = 0`）与其他违背直觉的约定（截断减法 `8 - 20 = 0`、
  向下取整除法 `5 / 2 = 2`、`0 ^ 0 = 1`）。
- 会用 `simp`、`simp [h]`、`simp +arith`；初步见到 simp normal form（simp 正规形）里 `a ≠ b` 与 `Nat.succ n`
  的写法（完整机制在第 5 章）。
- 会写 `calc` 链，会用 `exact?` 找引理，会读强制转换 `↑n`，并用 `push_cast` 与 `norm_cast` 处理最简单的
  cast（类型转换）。

## 前置知识
第 1 章（会编译、会读 infoview（信息视图）、会用 `#guard_msgs`、见过第 7 节那几个策略）；以及 Natural Number
Game 里的 `rw`、`rfl`、`induction`。

**本章用到的 import。** `omega`、`simp`、`calc`、`rw`、`decide`、`exact?` 是 Lean 核心自带的，不需要 import。
`ring` 来自 `Mathlib.Tactic.Ring`，`linarith` 与 `nlinarith` 来自 `Mathlib.Tactic.Linarith`，`norm_num` 来自
`Mathlib.Tactic.NormNum`，`positivity` 来自 `Mathlib.Tactic.Positivity`；`ℝ` 来自 `Mathlib.Basic.Real.Basic`，
练习 2.14 的 `Nat.factorial` 来自 `Mathlib.Data.Nat.Factorial.Basic`。它们都列在本文件开头的 import 里。在你自己的
文件里要写上对应的 import（文件头见第 1 章第 8 节）。
-/

@[expose] public section

namespace Lean4Learn.Ch02

/-!
## 1. 从 NNG 的自然数到真正的 `ℕ`

NNG 里的自然数是游戏自己定义的类型，定理一条一条从头证。这里的 `ℕ` 是 Lean 核心库里的 `Nat`，它的
引理已经由别人证好，放在 namespace（命名空间）`Nat` 里：`Nat.add_comm`、`Nat.add_assoc`、
`Nat.add_zero` 等都是现成的（名字和 NNG 里自己造的那一套类似，但不是同一批定理）。`example` 是不起名字的
声明（第 1 章第 1 节），`theorem` 还给 proposition（命题）起一个名字，之后的证明就能引用它（二者的完整比较见
第 3 章第 3 节）。proof term（证明项）直接写出来就是项模式；策略模式用 `by` 引入一串策略。下面是同一个命题的
两种证明写法，加一种命名方式。项模式里，`Nat.add_comm` 本身是一条证明，它接受参数 `a b`，`Nat.add_comm a b`
把它们填进去，得到 `a + b = b + a` 的证明（函数应用的机制在第 3 章）：
-/

example (a b : ℕ) : a + b = b + a := Nat.add_comm a b        -- 项模式

example (a b : ℕ) : a + b = b + a := by                      -- 策略模式
  rw [Nat.add_comm]                                          -- ⊢ b + a = b + a，由 rfl 关闭

theorem my_add_comm (a b : ℕ) : a + b = b + a := Nat.add_comm a b   -- 有名字的定理

-- 有了名字，之后的证明就能引用它。`rw [h₁, h₂]` 从左到右依次重写：
example (a b : ℕ) : a + b + 0 = b + a := by
  rw [Nat.add_zero, my_add_comm]
  -- 第一步之后 ⊢ a + b = b + a；第二步之后 ⊢ b + a = b + a，由 rfl 关闭

/-!
`Nat.add_comm` 只对 `ℕ` 有效（第 14 节第 2 条有对 `ℝ` 误用它的后果）。Mathlib 里还有通用版本，放在根命名空间：
`add_comm`、`mul_comm`、`add_mul`、`mul_add`、`two_mul`……它们对任何带有相应运算与定律的代数结构成立；这样的
结构由 type class（类型类）表达，第 8 章讲。现在只需知道下面的 `add_comm a b` 对 `ℕ`、`ℤ`、`ℝ` 都成立：
-/

example (a b : ℤ) : a + b = b + a := add_comm a b
example (a b c : ℝ) : a * (b + c) = a * b + a * c := mul_add a b c
example (a b c : ℝ) : (a + b) * c = a * c + b * c := add_mul a b c
example (a : ℝ) : 2 * a = a + a := two_mul a

/-!
## 2. `rw` 与归纳：把 NNG 的动作搬过来

`rw` 与 `induction` 的项模式写法（`▸`、`congrArg`、递归函数）见第 5、6 章。

**`rw`。** NNG 里的 rewriting（重写）`rw` 在这里照常工作。`rw [mul_comm]` 在目标里找第一个匹配 `?a * ?b`
的子项。`?a`、`?b` 是 metavariable（元变量）：引理里尚未确定的参数，`rw` 用第一个匹配的子项把它们填上，
再把目标里所有与它相同的出现一起重写；之后 `rw` 会再试一次 `rfl`（只在最低的 transparency（透明度）
reducible 下比较，所以通常要两边写法完全一致才关得上，反例见第 14 节第 1 条），能关闭目标就关闭。想指定重写哪一处时，把参数写出来：
-/

example (a b c : ℝ) : a * b * c = c * (a * b) := by
  rw [mul_comm]
  -- 匹配的是外层乘法：?a := a * b，?b := c
  -- ⊢ c * (a * b) = c * (a * b)，由 rfl 关闭

example (a b : ℝ) : a * b + a * b = b * a + b * a := by
  rw [mul_comm]
  -- ⊢ b * a + b * a = b * a + b * a，两处 `a * b` 一起重写

example (a b c : ℝ) : a * b * c = b * a * c := by
  rw [mul_comm a b]   -- 显式给出参数，只改 `a * b`

/-!
**读证明状态。** proof state（证明状态）的读法见第 1 章第 4 节。`trace_state` 把它作为一条消息打印出来，
于是可以用 `#guard_msgs` 固定。归纳的两个目标里出现的是 `0` 与 `n + 1`，不是旧教程里的 `Nat.zero`
与 `Nat.succ n`；`ih` 是 induction hypothesis（归纳假设），也是一条 hypothesis（假设）。`induction` 的完整
讲解见第 6 章，这里先用起来：
-/

/--
trace: case zero
⊢ 0 + 0 = 0
---
trace: case succ
n : ℕ
ih : 0 + n = n
⊢ 0 + (n + 1) = n + 1
-/
#guard_msgs in
theorem my_zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero =>
    trace_state
    rfl
  | succ n ih =>
    trace_state
    rw [← Nat.add_assoc]   -- ⊢ 0 + n + 1 = n + 1
    rw [ih]

/-!
NNG 里写的是 `induction n with d hd`（用 `d`、`hd` 给变量和归纳假设起名）；在这里，`with` 之后要写 `| zero =>`
与 `| succ n ih =>` 两个分支，就像上面那样。照搬 NNG 的写法是语法错误：Lean 在 `d` 处报
`error(lean.inductionWithNoAlts)`，大意是 `with` 之后必须跟一个策略或一个分支（例如 `| zero =>`），而这里跟的是标识符 `d`。
语法错误发生在解析阶段，`#guard_msgs` 捕获不到，所以这里不放可编译的例子。

## 3. `norm_num`：数值计算

要检查 `7 / 3 < 5 / 2` 这样的数值事实，用 `norm_num`（第 1 章第 7 节见过，这里讲它的边界）。它在 `ℕ`、`ℤ`、
`ℚ`、`ℝ` 上都能用，对整数、分数、乘方都给出精确结果，不做浮点近似。
-/

example : (2 : ℕ) + 2 = 4 := by norm_num
example : (4 : ℤ) - 9 = -5 := by norm_num
example : (3 : ℚ) / 4 + 1 / 6 = 11 / 12 := by norm_num
example : (3 : ℝ) / 4 * 8 = 6 := by norm_num
example : (2 : ℝ) ^ 10 = 1024 := by norm_num
example : (7 : ℝ) / 3 < 5 / 2 := by norm_num

/-!
**边界。** `norm_num` 不是代数恒等式的证明器：它不会展开 `(a + b) ^ 2` 这样的乘方。下面这个恒等式是对的，
`ring`（第 5 节）能证，但 `norm_num` 没能证出来，于是 `by` 报 `unsolved goals`，打印的是 `norm_num` 收工时的目标（与题目写法相同：`norm_num` 一步也没改动它）：
-/

/--
error: unsolved goals
a b : ℝ
⊢ (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
-/
#guard_msgs in
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by norm_num

/-!
## 4. 垃圾值与约定：`ℕ` 的减法与除法

数学里没有定义的运算，Lean 里是全函数：它必须给出一个值，这个值就是垃圾值。此外还有几条
不是垃圾值、但同样违背直觉的约定。两类都会让很多「看起来对」的等式变成假的，所以先于 `ring`、`omega` 讲：

| 表达式 | 值 | 类别 | 说明 |
|---|---|---|---|
| `a - b : ℕ`，`a < b` | `0` | 约定（截断减法） | `ℕ` 里没有负数，减法在 `0` 处截断 |
| `a / b : ℕ` | 向下取整 | 约定 | `5 / 2 = 2` |
| `a / 0 : ℕ`，`a % 0 : ℕ` | `0`，`a` | 垃圾值 | 这样 `b * (a / b) + a % b = a` 对 `b = 0` 也成立 |
| `x / 0 : ℝ` | `0` | 垃圾值 | field（域）里除以零取 `0` |
| `(-5 : ℤ) / 2`，`(-5 : ℤ) % 2` | `-3`，`1` | 约定 | `ℤ` 的除法是欧几里得除法（余数非负） |
| `0 ^ 0` | `1` | 约定 | 空积，`pow_zero` |

`ℝ` 的减法不截断。（这里的「域」是代数里的 field，不是结构体的「字段」。）每一行都有可编译的例子：
-/

example : (8 : ℕ) - 20 = 0 := rfl                                      -- 截断减法
example : (5 : ℕ) / 2 = 2 := by norm_num                               -- 向下取整
example : (5 : ℕ) / 0 = 0 ∧ (5 : ℕ) % 0 = 5 := by norm_num             -- `/ 0` 与 `% 0`
example (a b : ℕ) : b * (a / b) + a % b = a := Nat.div_add_mod a b     -- 对 `b = 0` 也成立
example : (-5 : ℤ) / 2 = -3 ∧ (-5 : ℤ) % 2 = 1 := by norm_num          -- 欧几里得除法
example (x : ℝ) : x / 0 = 0 := div_zero x                              -- 域里除以零
example : (0 : ℝ) ^ 0 = 1 := by norm_num                               -- `0 ^ 0`
example (a : ℝ) : a ^ 0 = 1 := pow_zero a                              -- 对任意 `a`
example : (2 : ℝ) - 3 = -1 := by norm_num                              -- `ℝ` 的减法不截断

/-!
一个后果：`n - 1 + 1 = n` 在 `n = 0` 时是假的，因为 `0 - 1 = 0`。证明在某步卡住时，先把变量代成 `0`、`1`
试一试。
-/

/-!
## 5. `ring`：交换环里的恒等式

两边含变量、展开之后相同的等式，交给 `ring`：它把两边都化成多项式的 normal form（正规形），再比较。它
适用于 commutative ring（交换环）和 commutative semiring（交换半环）：`ℤ`、`ℚ`、`ℝ` 是前者，`ℕ` 是后者。
对 `ℚ` 与 `ℝ` 这样的域，`ring` 也接受「除以数字」。
-/

example (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
example (a b : ℤ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring
example (a b : ℚ) : (a + b) / 2 + (a - b) / 2 = a := by ring
example (a b : ℝ) : (a + b) / 2 + (a - b) / 2 = a := by ring

/-!
**边界一：`ℕ` 的减法。** 截断减法（第 4 节）让 `ring` 无从下手：它不会替你分情况，所以连 `a + b - b = a`
这样总是对的等式它都证不了（`omega` 可以，见下一节）。失败时 `ring` 先退回 `ring_nf`（把两边各自化成正规形、
不要求相等），所以输出有两条消息：一条 `info`（建议改用 `ring_nf`），一条 `error`（正规形化完之后目标没有关上）。
下面第一次用到 `#guard_msgs` 的两个选项（基本用法见第 1 章第 6 节）：`whitespace := lax` 把连续空白折成一个空格再
比较（`ring` 的消息里有只含缩进空格的行）；`substring := true` 只要求 docstring（文档注释）是消息的一个子串，
所以有时只录消息的开头一段：
-/

/--
info: Try this:
  [apply] ring_nf

  The `ring` tactic failed to close the goal. Use `ring_nf` to obtain a normal form.

  Note that `ring` works primarily in *commutative* rings. If you have a noncommutative ring,
  abelian group or module, consider using `noncomm_ring`, `abel` or `module` instead.
---
error: unsolved goals
a b : ℕ
⊢ a + b - b = a
-/
#guard_msgs (whitespace := lax) in
example (a b : ℕ) : a + b - b = a := by ring

/-!
**边界二：除法。** 在 `ℝ` 里 `x / 0 = 0`（第 4 节），所以 `x / x = 1` 对 `x = 0` 是**假**的。`ring` 不知道
`x ≠ 0`，当然证不了；留下的目标是 `ring_nf` 把除法写成逆元之后的样子（`x⁻¹` 是 `x` 的倒数）：
-/

/--
error: unsolved goals
x : ℝ
⊢ x * x⁻¹ = 1
-/
#guard_msgs (whitespace := lax, substring := true) in
example (x : ℝ) : x / x = 1 := by ring

/-!
**边界三：不读假设。** `ring` 只做恒等式，context（上下文）里的 `h : a = b` 它不用。要用假设，写 `rw [h]` 或交给
`linarith`（第 7 节）。除法需要 `x ≠ 0` 时，见第 10 章的 `field_simp` 与 `field`：
-/

/--
error: unsolved goals
a b : ℝ
h : a = b
⊢ 1 + a = 1 + b
-/
#guard_msgs (whitespace := lax, substring := true) in
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by ring

example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by rw [h]
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by linarith

/-!
## 6. `omega`：`ℕ` 与 `ℤ` 上的线性算术

`ℕ`、`ℤ` 上的线性等式与不等式，尤其含截断减法、整除、取余的，用 `omega`（第 1 章第 7 节见过）。它允许
`+`、乘以数字、对**数字**取的 `/` 与 `%`、`k ∣ x`（`k` 为数字），以及 `∧`、`∨`、`¬`、`→`；下面的例子里各出现
一次，`/`、`%` 的除数不是数字时怎样，见边界三。它自动读取上下文里所有相关的假设，也自动处理 `ℕ` 的截断减法。
-/

example (a b : ℕ) (h : b ≤ a) : a - b + b = a := by omega
example (a b : ℕ) : a + b - b = a := by omega
example (a b : ℕ) : a - b ≤ a := by omega
example (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by omega
example (x y : ℤ) (h1 : 2 * x + 1 = y) (h2 : y < 7) : x < 3 := by omega
example (x : ℕ) (h : x / 2 = 3) : x ≤ 7 := by omega
example (x : ℕ) (h : 3 ∣ x) (h2 : x < 5) (h3 : 0 < x) : x = 3 := by omega
example (n : ℕ) (h : 0 < n) : n - 1 + 1 = n := by omega
example (x : ℕ) (h : 2 ≤ x ∧ x ≤ 3) (h2 : x % 2 = 1) : x = 3 := by omega
example (x y : ℕ) (h : x < y → y < 3) (h2 : ¬ y < 3) : y ≤ x := by omega
example (n : ℕ) (h : n + 1 ≤ 2 ^ n) : n + 2 ≤ 2 ^ n * 2 := by omega   -- `2 ^ n` 当作一个整体

/-!
**边界一：非线性。** 两个变量相乘 `x * y` 在 `omega` 眼里是一个不透明的 atom（原子），`x * y` 与 `y * x`
是两个不同的原子，所以连乘法交换律都证不了（输出里的 `where` 部分列出了它看到的原子）：
-/

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  b ≥ 0
  a ≥ 0
  a - b ≥ 1
where
 a := ↑y * ↑x
 b := ↑x * ↑y
-/
#guard_msgs in
example (x y : ℕ) : x * y = y * x := by omega

/-!
**边界二：缺假设。** 上面 `n - 1 + 1 = n` 的例子里 `0 < n` 不能少：没有它，`n = 0` 就是反例（第 4 节），但这条
信息没有把反例列出来，只说没有可用的约束。所以 `omega` 失败又看不出原因时，把变量代成 `0`、`1` 试一试
（第 4 节），再补上缺的假设：
-/

/-- error: omega could not prove the goal: No usable constraints found. -/
#guard_msgs (substring := true) in
example (n : ℕ) : n - 1 + 1 = n := by omega

/-!
**边界三：除数不是数字。** `x / y` 的除数 `y` 是变量时，整个 `x / y` 成了不透明的原子，`h` 只是把这个原子定为
`3`，与 `x` 没有联系，所以反例里只剩 `x ≤ 2`。下面的命题是真的（`y = 0` 时 `x / y = 0 ≠ 3`，所以 `y ≥ 1`，
从而 `x ≥ 3`），但 `omega` 看不出这一点：
-/

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  0 ≤ a ≤ 2
where
 a := ↑x
-/
#guard_msgs in
example (x y : ℕ) (h : x / y = 3) : 3 ≤ x := by omega

/-!
## 7. `linarith`：线性不等式

要从几条线性不等式推出另一条，用 `linarith`。它在 `ℚ`、`ℝ` 这样的 ordered field（有序域）上工作，也能用在 `ℤ` 与 `ℕ` 上：
把上下文里所有的假设和被否定的目标当作线性不等式，找一个矛盾。它自动读取上下文；方括号里写的是**额外**
的项（上下文里没有的事实）。
-/

example (x y : ℝ) (h1 : x < y) (h2 : y < 3) : x < 3 := by linarith
example (x y : ℚ) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by linarith   -- 等式目标
example (a b : ℤ) (h : a < b) : a + 1 ≤ b := by linarith
example (a b : ℕ) (h : a + 2 ≤ b) : a < b := by linarith
example (x : ℝ) : 0 ≤ x ^ 2 + 1 := by linarith [sq_nonneg x]

/-!
**边界一：非线性。** `linarith` 把 `a * b`、`a ^ 2` 当作不同的原子，不会自己想到平方非负。`2 * a * b ≤
a ^ 2 + b ^ 2` 是真命题，但需要事实 `0 ≤ (a - b) ^ 2`，你得把它作为额外的项交给 `linarith`。失败信息里的
`a✝` 就是被否定的目标（`✝` 见第 1 章第 4 节），`⊢ False` 表示 `linarith` 要从假设里推出矛盾，没找到：
-/

/--
error: linarith failed to find a contradiction
a b : ℝ
a✝ : a ^ 2 + b ^ 2 < 2 * a * b
⊢ False
failed
-/
#guard_msgs in
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by linarith

example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by linarith [sq_nonneg (a - b)]

/-!
**边界二：`ℕ` 的截断减法。** `linarith` 把 `a - b` 当作一个原子，不会分情况，所以 `a - b ≤ a`
这个总成立的不等式它证不了；这是 `omega` 的用武之地：
-/

/-- error: linarith failed to find a contradiction -/
#guard_msgs (substring := true) in
example (a b : ℕ) : a - b ≤ a := by linarith

/-!
## 8. `nlinarith`：要乘积的不等式

推理需要把两个量相乘时，用 `nlinarith`。它先把假设与目标里出现的平方 `t ^ 2`、`t * t` 的非负性加进来，
再把所有比较（含被否定的目标与刚加进来的平方非负性）两两相乘，最后交给 `linarith`（见
`Mathlib/Tactic/Linarith/Preprocessing.lean` 里的 `nlinarithExtras`，更多用法见第 10 章）。下面的
`a ^ 2 ≤ b ^ 2` 需要诸如 `(b - a) * a ≥ 0` 的乘积，这些乘积由 `nlinarith` 自己去造；`linarith` 不造乘积：
-/

example (a b : ℝ) (h : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by nlinarith

/-- error: linarith failed to find a contradiction -/
#guard_msgs (substring := true) in
example (a b : ℝ) (h : 0 ≤ a) (hab : a ≤ b) : a ^ 2 ≤ b ^ 2 := by linarith

/-!
`nlinarith` 找不到时，失败信息仍由 `linarith` 给出；把关键的平方作为提示交给它，写法同 `linarith [...]`
（练习 2.10）。
-/

/-!
## 9. `positivity`：正性

目标是 `0 < e`、`0 ≤ e` 或 `e ≠ 0` 时，用 `positivity`。办法是沿着表达式的语法递归：平方非负，非负数的和
非负，正数的积与商为正。遇到其他子表达式 `e`，它在上下文里找形如 `0 < e`、`0 ≤ e`、`e ≠ 0` 的假设（下界是
数字的 `1 ≤ e` 之类也行）；`a ≤ b` 这样的假设它不会拿来推理，见边界三。`(n : ℝ)` 是自然数 `n` 转成的实数
（第 13 节细讲），它非负，所以 `(n : ℝ) + 1` 为正：
-/

example (x : ℝ) : 0 < x ^ 2 + 1 := by positivity
example (x : ℝ) : x ^ 2 + 1 ≠ 0 := by positivity
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b + a * b := by positivity
example (n : ℕ) : 0 < (n : ℝ) + 1 := by positivity
example (a : ℝ) (h : 1 ≤ a) : 0 < a := by positivity
example (a : ℝ) (h : 0 ≤ a) : 0 ≤ a + a ^ 2 := by positivity
example (a : ℝ) (h : a ≠ 0) : 0 < a ^ 2 := by positivity

/-!
**边界一：** `0 < x ^ 2` 对 `x = 0` 是假的，`positivity` 的错误信息说它只能证到非负：
-/

/--
error: failed to prove strict positivity, but it would be possible to prove nonnegativity if desired
-/
#guard_msgs in
example (x : ℝ) : 0 < x ^ 2 := by positivity

/-!
**边界二：** 目标必须是 `0 < e`、`0 ≤ e` 或 `e ≠ 0` 的形状，一般的不等式不是它的目标：
-/

/-- error: not a positivity goal -/
#guard_msgs in
example (x : ℝ) : 1 ≤ x ^ 2 + 1 := by positivity

/-!
**边界三：** 上下文里的 `a ≤ b`（`a` 不是数字）它不会用来推 `0 < b`；这种线性推理交给 `linarith`：
-/

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : 0 < b := by positivity

example (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : 0 < b := by linarith

/-!
## 10. `simp` 初见，与 simp 正规形

`ring`（第 5 节）证不了 `a + b - b = a`，`simp` 可以：它反复使用 simp lemma（simp 引理，即带 `@[simp]`
标签的等式与等价）重写目标，直到不能再改，而 simp set（simp 集）里正好有处理这个式子的引理。本节只是预告：
`simp` 的完整机制（含 `simp at`、`+arith`、simp 正规形）在第 5 章讲，这里只看最常见的用法。
-/

example (a b : ℕ) : a + b - b = a := by simp

/-!
`simp` 的结果是 simp 正规形：它把目标与假设重写成一种固定的写法，这样之后的 `rw`、`exact` 只要对着这一种写法
来写。两个最常见的：`a ≠ b` 被写成 `¬a = b`；`Nat.succ n` 被写成 `n + 1`。`simp at h` 在假设 `h` 里简化，
`trace_state` 把结果打印出来：
-/

/--
trace: a b : ℕ
h : ¬a = b
⊢ ¬a = b
-/
#guard_msgs in
example (a b : ℕ) (h : a ≠ b) : ¬a = b := by
  simp at h
  trace_state
  exact h

/--
trace: n m : ℕ
h : n.succ = m
⊢ n + 1 = m
---
trace: n m : ℕ
h : n + 1 = m
⊢ n + 1 = m
-/
#guard_msgs in
example (n m : ℕ) (h : Nat.succ n = m) : n + 1 = m := by
  trace_state
  simp at h
  trace_state
  exact h

/-!
**边界：`simp` 不使用上下文里的假设**，除非你把它们写进方括号。下面的 `simp` 把目标简化到 `x < y`
就停了：
-/

/--
error: unsolved goals
x y : ℝ
h : x < y
⊢ x < y
-/
#guard_msgs in
example (x y : ℝ) (h : x < y) : x + 1 < y + 1 := by simp

example (x y : ℝ) (h : x < y) : x + 1 < y + 1 := by simp [h]

/-!
`simp` 不会重排加法的顺序（它不做线性算术的正规化）：`x + y + 1 = y + x + 1` 消去两边的 `+ 1` 之后停在
`x + y = y + x`。`simp +arith` 额外打开 `ℕ`、`ℤ` 上线性算术的正规化，就能证（旧写法 `simp_arith` 已
deprecated（弃用），在 4.35 里直接报错，见第 14 节第 4 条）：
-/

/--
error: unsolved goals
x y : ℕ
⊢ x + y = y + x
-/
#guard_msgs in
example (x y : ℕ) : x + y + 1 = y + x + 1 := by simp

example (x y : ℕ) : x + y + 1 = y + x + 1 := by simp +arith
example (x y : ℤ) : x + y + 3 ≤ y + x + 5 := by simp +arith

/-!
## 11. `calc`：把一连串步骤写成一条链

`calc` 把「`a = b`，`b ≤ c`，`c < d`」这样一连串关系拼成「`a < d`」。第一步写出完整的关系，之后每一步以
`_` 开头，`_` 表示上一步的右端。本书的排版：`by` 之后 `calc` 单独占一行，步骤另起一行、缩进相同。每一步右边
的 `:= by …` 里放这一步的证明，各步可以用不同的策略。下面例子里的注释说明每一步做了什么：
-/

example (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  calc
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring     -- 展开，纯恒等式
    _ ≤ a ^ 2 + (a ^ 2 + b ^ 2) + b ^ 2 := by              -- 此步：2ab ≤ a² + b²
      nlinarith [sq_nonneg (a - b)]                        -- 差额恰是 (a - b) ^ 2 ≥ 0
    _ = 2 * (a ^ 2 + b ^ 2) := by ring                     -- 合并同类项，又是恒等式

/-!
同方向的 `=`、`≤`、`<` 可以混着写（为什么能混写，见第 5 章：靠 `Trans` 的 instance（实例））：例如 `<` 接 `≤`
得 `<`，`=` 接 `≤` 得 `≤`。`calc` 也可以直接作为项模式的证明项：
-/

theorem my_lt_le_chain (a b c : ℝ) (h1 : a < b) (h2 : b ≤ c) : a < c :=
  calc
    a < b := h1
    _ ≤ c := h2

/-!
**边界。** 链的结论必须与目标的关系对得上：`<` 的链不能充当 `≤` 目标的证明（得到的是比目标更强的
结论，Lean 不会自动弱化）。把第一步改成 `≤`，链就是 `≤` 链：
-/

/-- error: 'calc' expression has type a < c but is expected to have type a ≤ c -/
#guard_msgs (whitespace := lax, substring := true) in
example (a b c : ℕ) (h1 : a < b) (h2 : b ≤ c) : a ≤ c := by
  calc
    a < b := h1
    _ ≤ c := h2

example (a b c : ℕ) (h1 : a < b) (h2 : b ≤ c) : a ≤ c :=
  calc
    a ≤ b := h1.le     -- `h1.le` 即 `LT.lt.le h1`：把 `<` 弱化为 `≤`（dot notation（点记号）见第 3 章）
    _ ≤ c := h2

/-!
## 12. `exact?`：让 Lean 替你找引理

不知道引理叫什么时，写 `exact?`（第 1 章第 7 节见过）。它在当前导入的所有声明里搜索一个能直接关闭目标的
项，找到后以 `Try this` 的形式报告。**找到之后立刻把它换成报告的那条证明**，不要把 `exact?` 留在成品文件里。
第 9 章系统讲搜索；这里看它找到的名字是否是日常写法：
-/

/--
info: Try this:
  [apply] exact Right.mul_pos ha hb
-/
#guard_msgs in
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by exact?

/-!
报告的名字正确，但不一定是日常写法：这里是 `Right.mul_pos`（它假设「右乘正数保持严格序」），`Left.mul_pos` 是
对应的「左乘」版本，而日常写的 `mul_pos` 只是 `Left.mul_pos` 的别名（alias）；三个名字在 `ℝ` 上都能证这个目标。
成品里写日常名 `mul_pos`（第 9 章讲怎么从 `Right.mul_pos` 找到它）；报告的名字也可能随 Mathlib 版本变化：
-/

example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := Left.mul_pos ha hb
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb

/-!
**边界。** `exact?` 的搜索能力有限，不会任意组合库里的引理。它的做法是：先在库里找一条结论能与目标匹配的
引理，再用 `solve_by_elim`（有深度上限的回溯搜索，`exact?` 取深度 6；源码见 Lean 工具链的
`Lean/Meta/Tactic/LibrarySearch.lean`）补全这条引理的前提。补前提时只用**局部假设**和 `rfl`、`trivial` 等
少数默认规则，不再回到库里搜索。所以局部的蕴含链它串得起来：下面 `hf`、`hg` 都是局部假设，`hf a ha`、`hg (f a) …` 两步局部推理被接成
一个项。外面包着的那层库引理只负责调整形状（具体是哪一个，随 Mathlib 版本和导入而变），不是推理的实质：
-/

/--
info: Try this:
  [apply] exact lt_of_lt_of_eq (hg (f a) (hf a ha)) rfl
-/
#guard_msgs in
example (f g : ℝ → ℝ) (hf : ∀ x, 0 < x → 0 < f x) (hg : ∀ x, 0 < x → 0 < g x) (a : ℝ)
    (ha : 0 < a) : 0 < g (f a) := by exact?

/-!
但要用到库里的多条引理时就不行了。下面的目标是真的，要先 `mul_pos` 再 `add_pos`。按上面的做法推断：
套 `add_pos` 之后，前提 `0 < a` 可由局部假设 `ha` 补上，而前提 `0 < a * b` 要靠库里的 `mul_pos`，
`solve_by_elim` 不会去库里找它（这是对失败原因的推断，不是 Lean 打印出来的）；`exact?` 以错误结束
（`positivity` 一步就能证）：
-/

/-- error: `exact?` could not close the goal. Try `apply?` to see partial suggestions. -/
#guard_msgs in
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a * b + a := by exact?

/-!
## 13. 强制转换：`↑` 初识

`n : ℕ` 想当实数用时，写 `(n : ℝ)`，这叫 type ascription（类型标注）：它告诉 elaborator（精译器；另译
繁饰器）这里期望 `ℝ`。`n` 的类型是 `ℕ`，于是 elaborator 自动插入强制转换，即函数 `Nat.cast`，infoview 里
显示成 `↑n`。完整理论在第 8 章，这里只学两件事：怎么读（下面 `push_cast` 的输出里就有 `↑m`）、怎么搬。
-/

example (n : ℕ) : (n : ℝ) = Nat.cast n := rfl

/-!
顺序：`((n / 2 : ℕ) : ℝ)` 先在 `ℕ` 里做向下取整除法再转换；`(n / 2 : ℝ)` 则是实数除法 `↑n / 2`：
-/

example : ((1 / 2 : ℕ) : ℝ) = 0 := by norm_num
example (n : ℕ) : (n / 2 : ℝ) = (n : ℝ) / 2 := rfl

/-!
**`push_cast`** 把转换推进到运算内部：`↑(m + n)` 变成 `↑m + ↑n`（目标里显示的 `↑m` 就是 `(m : ℝ)`）。
**`norm_cast`** 方向相反，把转换拉到外面，常用来把关于实数的假设变回关于 `ℕ` 的命题（这里只用，不讲机制）：
-/

/--
trace: m n : ℕ
⊢ (↑m + ↑n) * 2 = 2 * ↑m + 2 * ↑n
-/
#guard_msgs in
example (m n : ℕ) : ((m + n : ℕ) : ℝ) * 2 = 2 * m + 2 * n := by
  push_cast
  trace_state
  ring

example (m n : ℕ) (h : (m : ℝ) < n) : m < n := by
  norm_cast at h   -- h 变成 m < n，正是目标，目标随之关闭

/-!
**减法与转换不交换。** `ℕ` 的减法截断，`ℝ` 的减法不截断，所以 `↑(a - b)` 一般不等于 `↑a - ↑b`
（比如 `a = 2`、`b = 3`）。`Nat.cast_sub` 与 `push_cast` 如何处理它，留到第 8 章：
-/

example : ((2 - 3 : ℕ) : ℝ) = 0 ∧ (2 : ℝ) - 3 = -1 := by norm_num

/-!
## 14. 常见错误

各策略自己的失败例子见第 3、5–12 节的「边界」；这里收集与重写、名字和旧写法有关的错误。拼错引理名得到的
`Unknown constant`，见第 1 章第 12 节。

**1. `rw` 用了方向相反的引理。** 本书锁定的 Mathlib 里，`pow_succ` 把 `a ^ (n + 1)` 写成 `a ^ n * a`（新的
因子在右边），带撇的 `pow_succ'` 方向相反，是 `a * a ^ n`（都在 `Mathlib/Algebra/Group/Monoid.lean`）。目标是
`a ^ (n + 1) = a * a ^ n` 时，用 `pow_succ` 重写，`rw` 本身成功了，但留下的 `a ^ n * a = a * a ^ n` 两边写法
不同，收尾的 `rfl` 关不上，于是报 `unsolved goals`。改正：换成 `pow_succ'`，或者再补一步 `mul_comm`：
-/

/--
error: unsolved goals
a : ℝ
n : ℕ
⊢ a ^ n * a = a * a ^ n
-/
#guard_msgs in
example (a : ℝ) (n : ℕ) : a ^ (n + 1) = a * a ^ n := by
  rw [pow_succ]

example (a : ℝ) (n : ℕ) : a ^ (n + 1) = a * a ^ n := by
  rw [pow_succ']

example (a : ℝ) (n : ℕ) : a ^ (n + 1) = a * a ^ n := by
  rw [pow_succ, mul_comm]

/-!
**2. 用了只属于 `ℕ` 的引理去处理 `ℝ`。** 信息说得很直接：参数 `a` 的类型是 `ℝ`，而 `Nat.add_comm` 期望
`ℕ`。改正：对 `ℝ` 用根命名空间的 `add_comm`；`#check @add_comm` 看通用版本的签名：
-/

/--
error: Application type mismatch: The argument
  a
has type
  ℝ
but is expected to have type
  ℕ
in the application
  Nat.add_comm a
-/
#guard_msgs (whitespace := lax) in
example (a b : ℝ) : a + b = b + a := Nat.add_comm a b

example (a b : ℝ) : a + b = b + a := add_comm a b

/-!
**3. `rw` 找不到可重写的子项。** 目标里没有 `?n + ?m` 的形状（`?n`、`?m` 是引理里的元变量，第 2 节），
`rw [Nat.add_comm]` 无处下手；注意错误信息里写的是 `rewrite`（`rw` 是 `rewrite` 再加一次保守的 `rfl` 尝试）。
信息末尾列出的是当时的目标。改正：看清目标的形状，换一条匹配的引理：
-/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ?n + ?m
in the target expression
  a * b = b * a

a b : ℕ
⊢ a * b = b * a
-/
#guard_msgs (whitespace := lax) in
example (a b : ℕ) : a * b = b * a := by
  rw [Nat.add_comm]

/-!
**4. 用了已弃用的写法。** `simp_arith` 自 Lean v4.18（2025-04）起弃用，在本书锁定的 4.35 里直接报错
（源码 `Lean/Elab/Tactic/SimpArith.lean`），同时给出 `Try these` 建议；应改用 `simp +arith`：
-/

/--
info: Try these:
  [apply] simp +arith
  [apply] simp +arith +decide
---
error: `simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.
-/
#guard_msgs (whitespace := lax) in
example (x y : ℕ) : x + y + 1 > x + y := by simp_arith

/-!
## 练习

练习 2.1、2.9 复习 NNG 的 `rw` 与归纳；2.3、2.5、2.6、2.14、2.15 回到第 1 章（练习 1.9 的 `omega`，练习 1.8
的 `exact?`，练习 1.4 的 `#guard_msgs`，练习 1.11 的 `Nat.factorial`，练习 1.1、1.6、1.12 的 `norm_num`、
`constructor`、`intro`）；其余练习用本章的新策略。引理名要么在本章出现过，要么在题面里给出（练习 2.5 例外：
它要你用 `exact?` 自己找）。2.3、2.4、2.7、2.12、2.13 不点名策略，见本章末小结的「先试什么」。
-/

/-- 练习 2.1（★）：只用 `rw`，从 `Nat.add_assoc` 与 `Nat.add_comm` 出发。 -/
theorem ex_2_1 (a b c : ℕ) : a + b + c = a + (c + b) := by sorry

/-- 练习 2.2（★）：用 `ring`。 -/
theorem ex_2_2 (a b : ℤ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by sorry

/-- 练习 2.3（★）：与练习 1.9 同类的 `ℕ` 问题；两个假设都要用到。 -/
theorem ex_2_3 (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : c - a = (c - b) + (b - a) := by sorry

/-- 练习 2.4（★）：三个假设都要用到。 -/
theorem ex_2_4 (a b c : ℝ) (h1 : a + b = 10) (h2 : b + c = 7) (h3 : 0 ≤ c) : 3 ≤ a := by sorry

/-- 练习 2.5（★）：用 `exact?` 找一个引理（练习 1.8 的办法），再把 `exact?` 换成它报告的证明；
你得到的名字可能与 `Solutions/` 里的不同。 -/
theorem ex_2_5 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by sorry

/-- 练习 2.6（★）：先试 `norm_num`；如果它没证完，再用 `positivity`。 -/
theorem ex_2_6 (n : ℕ) (x : ℝ) : 0 < (n : ℝ) ^ 2 + x ^ 2 + 1 := by sorry

/-- 练习 2.7（★★）：第 4 节表里的四条，逐一证明（截断减法、`% 0`、`/ 0`、`0 ^ 0`）；每一条各选合适的策略。 -/
theorem ex_2_7 (n : ℕ) (x : ℝ) :
    n - (n + 1) = 0 ∧ (n + 1) % 0 = n + 1 ∧ x / 0 + 1 = 1 ∧ (0 : ℝ) ^ 0 + 1 = 2 := by sorry

/-- 练习 2.8（★）：只用 `rw`：先 `pow_succ'`（方向见第 14 节第 1 条），再 `mul_assoc`。 -/
theorem ex_2_8 (a b : ℝ) (n : ℕ) : a ^ (n + 1) * b = a * (a ^ n * b) := by sorry

/-- 练习 2.9（★★）：对 `n` 归纳；零的情形用 `norm_num`。归纳步先用 `pow_succ` 展开 `2 ^ (n + 1)`
（方向见第 14 节第 1 条），再用 `omega` 收尾（它把 `2 ^ n` 当作原子，见第 6 节）；注意目标里是 `n + 1`。 -/
theorem ex_2_9 (n : ℕ) : n + 1 ≤ 2 ^ n := by sorry

/-- 练习 2.10（★★）：用 `nlinarith`，提示项取 `sq_nonneg (x - y)`（第 8 节）；`nlinarith` 会自己把
被否定的目标与 `hx`、`hy` 相乘。 -/
theorem ex_2_10 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x * y = 1) : 2 ≤ x + y := by sorry

/-- 练习 2.11（★）：先 `push_cast` 把转换推进运算内部（第 13 节），再用 `ring`（第 5 节）。 -/
theorem ex_2_11 (m n : ℕ) : ((m + n : ℕ) : ℝ) ^ 2 = (m : ℝ) ^ 2 + 2 * m * n + (n : ℝ) ^ 2 := by sorry

/-- 练习 2.12（★★）：写成三步的 `calc`，关系依次是 `<`、`≤`、`=`（第 11 节）；每一步各选合适的策略。 -/
theorem ex_2_12 (x : ℝ) (hx : 0 < x) : x ^ 2 < (x + 1) ^ 2 := by sorry

/-- 练习 2.13（★★）：不点名工具；提示：想想哪几个平方的非负性，按适当的正系数加起来就是目标
（第 7 节有两个变量的版本）。 -/
theorem ex_2_13 (a b c : ℝ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by sorry

/-- 练习 2.14（★）：练习 1.11 的 `Nat.factorial`，加上本章的截断减法与向下取整除法；用 `decide`。 -/
theorem ex_2_14 :
    Nat.factorial 4 - Nat.factorial 5 = 0 ∧ Nat.factorial 5 / Nat.factorial 4 = 5 := by sorry

/-- 练习 2.15（★）：用 `constructor` 拆成两个目标（练习 1.6）；第一个用 `norm_num`（练习 1.1），
第二个先 `intro x y z`（练习 1.12），再用 `simp +arith`（第 10 节）。 -/
theorem ex_2_15 :
    (7 : ℝ) / 3 + 5 / 6 < 4 ∧ ∀ x y z : ℕ, x + y + z + 2 = z + y + x + 2 := by sorry

/-!
## 小结

| 工具 | 语法 | 何时用 | 边界或注意（见节） |
|---|---|---|---|
| `rw` | `rw [h]`，`rw [← h]` | 已知引理，逐步重写 | 找不到可匹配的子项（第 14 节第 3 条） |
| `induction` | `induction n with \| zero => … \| succ n ih => …` | 归纳 | 目标是 `0`、`n + 1`（第 2 节） |
| `Nat.add_comm` | `Nat.add_comm a b` | `ℕ` 专用；通用版 `add_comm` 管所有结构 | 对 `ℝ` 误用（第 14 节第 2 条） |
| `norm_num` | `norm_num` | 数值，比较大小 | 不展开含变量的恒等式（第 3 节） |
| 垃圾值 | `8 - 20 = 0`，`x / 0 = 0` | 证明在 `0` 处卡住时 | `n - 1 + 1 = n` 为假（第 4 节） |
| `ring` | `ring` | 交换环恒等式 | `ℕ` 的减法、`x / x`，不读假设（第 5 节） |
| `omega` | `omega` | `ℕ`、`ℤ` 线性算术，含截断减法 | 非线性、缺假设（第 6 节） |
| `linarith` | `linarith [t]` | 线性不等式 | 非线性、`ℕ` 的减法（第 7 节） |
| `nlinarith` | `nlinarith [t]` | 二次不等式，要乘积 | 需要提示平方（第 8 节） |
| `positivity` | `positivity` | `0 < e`、`0 ≤ e`、`e ≠ 0` | `0 < x ^ 2`、一般的不等式（第 9 节） |
| `simp` | `simp [h]`，`simp +arith` | 简化到 simp 正规形 | 不使用上下文里的假设（第 10 节） |
| `calc` | `calc` 块 | 多步链，同方向混合 | 结论的关系必须对得上（第 11 节） |
| `exact?` | `exact?` | 不知道引理名 | 没有现成引理时以错误结束（第 12 节） |
| `push_cast`/`norm_cast` | `push_cast`，`norm_cast at h` | 处理 `↑` | 注意：减法不与转换交换（第 13 节） |
| 旧写法 | `simp_arith` → `simp +arith` | 读旧教程时 | `simp_arith` 现在直接报错（第 14 节第 4 条） |

**先试什么。** 纯数值 → `norm_num`；含变量的恒等式 → `ring`；`ℕ`、`ℤ` 上含 `-`、`/`、`%`、`∣` 的线性问题 →
`omega`；其余线性不等式 → `linarith`，要乘积 → `nlinarith`（给提示）；目标是 `0 < e` 之类 → `positivity`；
都不对口，就 `simp`，或者 `exact?` 找引理。
-/

/-!
## 延伸阅读

- Mathematics in Lean（MIL）第 2 章 *Basics*：2.1 *Calculating*、2.2 *Proving Identities in Algebraic
  Structures*、2.3 *Using Theorems and Lemmas*，与本章同一路线。
- Lean 参考手册 4.35.0 的策略索引：
  <https://lean-lang.org/doc/reference/4.35.0/Tactic-Proofs/Tactic-Reference/>（该页仍列着已报错的
  `simp_arith`，以第 14 节为准）。源码里 `omega` 能处理的等式、不等式与整除的形状写在 `Init/Tactics.lean` 中
  `omega` 的文档注释（逻辑连接词见第 6 节的例子）；`calc` 的语法是 `Init/NotationExtra.lean` 里的 `calcSteps`。
- Mathlib 源码：`Mathlib/Tactic/Ring/Basic.lean` 的 *Caveats and future work*（在环里减法能消去相同项、除法
  不能）；`Mathlib/Tactic/Linarith/Frontend.lean` 的 module docstring（模块文档注释；`linarith` 何时是判定
  过程、何时会漏掉问题）；`Mathlib/Tactic/Positivity/Core.lean`。
- 本书第 5 章（`rw`、`simp`、`calc` 的完整机制）、第 8 章（强制转换与 `norm_cast`）、第 9 章（找引理）、
  第 10 章（自动化策略全景，`field_simp` 与 `field` 的细节）。
-/

end Lean4Learn.Ch02

end
