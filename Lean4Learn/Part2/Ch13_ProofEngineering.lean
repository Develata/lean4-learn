module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.DepRewrite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Ring

/-!
# 第 13 章　证明的组织、调试与风格

写出一个能编译的证明只是工作的一半。另一半是：怎样把二十行以上的证明拆成可以逐块填入的骨架，出错时怎样
读懂 error message（错误信息），最后怎样整理成别人愿意读的样子。本章讲这套工程习惯。

## 学习目标
- 用「先写陈述、再用 `have … := sorry` 分解、最后填叶子」的方式写证明，并看懂 `sorry` 警告；
- 选对搭骨架的工具：`have`、`suffices`、`obtain`、`refine ⟨?_, ?_⟩`、`set … with`、`generalize`、`wlog`；
- 组织归纳：`induction … generalizing`、强归纳的本书统一写法、`Nat.le_induction`，以及「分支名 = 绑定名」的规则；
- 用 `fin_cases`、`interval_cases` 穷举，用 `convert … using`、`congr!` 处理「差一点就是引理」的目标；
- 用 `extract_goal`、`pp.explicit`、`trace.Meta.synthInstance` 检查目标；按固定顺序读错误信息，
  认识本章的几种工程性错误（motive、实例合成、目标数目、`maxHeartbeats`、`variable`）；
- 解释 `simp?` 与 `says` 的用法和风格纪律，会写基本的 `conv`；
- 按 Mathlib 风格指南改写证明，用 `set_option linter.style.* true in` 检查，写合格的 docstring（文档注释）。

## 前置知识
第 1 章（`extract_goal` 初见），第 2 章（`ring`、`linarith`、`omega`），第 4 章（`have`、`suffices`、
`obtain`、`rcases`），第 5 章（`rw` 与 `rw!`、`simp`、`calc`），第 6 章（`induction … with`），
第 8 章（`exact_mod_cast`），第 9 章（`exact?`），第 10 章（`linarith`/`nlinarith` 的边界），
第 12 章（`Finset`、`DecidableEq`）。
-/

@[expose] public section

namespace Lean4Learn.Ch13

/-!
## 1. 自顶向下：先写陈述，再分解，最后填叶子

长证明最常见的失败方式，是从第一行开始顺着写，写到第十五行才发现中间缺一个引理。更稳的做法分三步：

1. **写陈述**，整个证明先用 `sorry` 占位，确认陈述本身能通过 elaboration（精译）；
2. **分解**：把证明拆成几个 `have name : 陈述 := sorry`，每个 `have` 是一个**叶子**。此时 `sorry` 只出现在
   叶子上，主干（归纳、分情况）是真的，编译器已经替你检查了「叶子拼起来确实推出结论」；
3. **填叶子**：一次填一个，每填完一个重新编译，`sorry` 越来越少。

本节用一个定理走完这个过程：每个正整数都可以写成 `2 ^ a * b`，其中 `b` 是奇数。数学证明是强归纳：
`n` 是奇数时取 `a = 0`；`n = k + k` 时 `k` 更小，induction hypothesis（归纳假设）给出 `k = 2 ^ a * b`，于是 `n = 2 ^ (a + 1) * b`。

**快照 1：骨架。** 主干已经是真的：强归纳、分奇偶、取 witness（见证）。`Even n` 的定义是 `∃ r, n = r + r`，
所以 `⟨k, hk⟩` 给出 `hk : n = k + k`。四个叶子是 `sorry`。`sorry` 只许出现在练习
和这种用 `#guard_msgs` 捕获警告的匿名 `example` 里，所以本书里的快照 1 是这种 `example`；
你在自己的草稿里可以随便写，但交付之前要清零。编译结果只有一条警告，它不说是哪个叶子：
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (n : ℕ) (hn : 0 < n) : ∃ a b : ℕ, Odd b ∧ n = 2 ^ a * b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    -- ih : ∀ m < n, 0 < m → ∃ a b, Odd b ∧ m = 2 ^ a * b      （hn 被自动并入了 ih）
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
    · -- hk : n = k + k
      have hk0 : 0 < k := sorry
      have hlt : k < n := sorry
      obtain ⟨a, b, hb, hkab⟩ := ih k hlt hk0
      -- hkab : k = 2 ^ a * b
      refine ⟨a + 1, b, hb, ?_⟩
      sorry
    · -- hodd : Odd n
      sorry

/-!
注意 `ih k hlt hk0` 已经用到了叶子 `hlt`、`hk0` 的**陈述**：骨架的价值在于，叶子的陈述一旦写错，
后面的步骤就会报错，而不必等到叶子填完。`hk0`、`hlt` 是线性算术，`omega` 直接关掉；奇数情形和最后的
等式是剩下的两个叶子。

**快照 2：完成。** 最后的等式把 `hk : n = k + k` 与 `hkab : k = 2 ^ a * b` 依次代入，剩下
`2 ^ a * b + 2 ^ a * b = 2 ^ (a + 1) * b`，是 `ring` 的活；奇数情形取 `a = 0`，`2 ^ 0 * n = n` 由 `simp` 证：
-/

theorem exists_pow_two_mul_odd (n : ℕ) (hn : 0 < n) :
    ∃ a b : ℕ, Odd b ∧ n = 2 ^ a * b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
    · have hk0 : 0 < k := by omega
      have hlt : k < n := by omega
      obtain ⟨a, b, hb, hkab⟩ := ih k hlt hk0
      refine ⟨a + 1, b, hb, ?_⟩
      rw [hk, hkab]
      ring
    · exact ⟨0, n, hodd, by simp⟩

/-!
还有两条纪律。**一次只填一个叶子**：别的叶子保持 `sorry`，不要同时动两处。**`?_` 与 `sorry` 的区别**：
`refine ⟨a + 1, b, hb, ?_⟩` 里的 `?_` 成为新的目标；它若到块末尾仍未关闭，报的是 `unsolved goals` **错误**，
而 `sorry` 只是**警告**，所以 `?_` 更难被忘掉：
-/

/--
error: unsolved goals
p q : Prop
hp : p
⊢ q
-/
#guard_msgs in
example (p q : Prop) (hp : p) : p ∧ q := by
  refine ⟨hp, ?_⟩

/-!
## 2. 搭骨架的工具箱

下面几个 tactic 前几章零散出现过，这里按「它在骨架里扮演什么角色」重新排。

**`have`**：给中间结论起名。陈述写全（`have h : T := …`），后面的 `omega`、`linarith` 才能用。
**`suffices h : T by tac`** 说「只要证 `T`」，主目标变成 `T`，适合先把「用得上的形状」写出来。
**`refine ⟨?_, ?_⟩`** 把 `∧`、`↔`、`∃` 拆成目标，一般比 `constructor` 清楚，因为你能看到每个洞；
匿名构造子会自动嵌套，`⟨?_, ?_, ?_⟩` 就是 `⟨?_, ⟨?_, ?_⟩⟩`：
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ (q ∧ p) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hp -- ⊢ p
  · exact hq -- ⊢ q
  · exact hp -- ⊢ p

example (a b : ℕ) (h : a + 1 ≤ b) : a < b ∧ 0 < b := by
  suffices hb : a < b by exact ⟨hb, by omega⟩
  -- ⊢ a < b
  omega

/-!
**`obtain`** 拆开存在量词、合取与析取（`obtain ⟨x, hx⟩ := e`、`obtain h1 | h2 := h`，第 4 章）。
带类型的写法 `obtain h : T := proof` 和 `have` 一样。省略 `:= proof` 也合法：此时 `T` 成为一个**新目标**，
排在主目标**之前**，证完之后 `h : T` 才出现在主目标的上下文里——这是搭骨架的另一种写法：
-/

example (n : ℕ) (h : 2 < n) : n ≠ 0 := by
  obtain h1 : 0 < n
  · omega -- 第一个目标：⊢ 0 < n
  · omega -- 主目标：h1 : 0 < n 已在上下文里

/-!
**`set x := e with h`** 引入局部定义 `x := e`，并把目标和所有假设里的 `e` 替换成 `x`，同时给出 `h : x = e`。它用来给一个反复出现的长表达式起短名字。用 `guard_hyp` 检查替换确实发生了：
-/

example (a b : ℕ) (h : (a + b) * (a + b) = 49) : a + b = 7 := by
  set s := a + b with hs
  guard_hyp h : s * s = 49
  guard_hyp hs : s = a + b
  have h1 : s ≤ 7 := by nlinarith
  have h2 : 7 ≤ s := by nlinarith
  omega

/-!
**`generalize e = x`** 把目标里的 `e` 换成一个新变量 `x`，丢掉 `x` 是什么的信息。
当你要对 `e` 做 `cases` 或 `induction`，而 `e` 不是变量时用它：
-/

example (f : ℕ → ℕ) (a : ℕ) : f a = 0 ∨ ∃ k, f a = k + 1 := by
  generalize f a = x
  cases x with
  | zero =>
    left
    rfl
  | succ k =>
    right
    exact ⟨k, rfl⟩

/-!
**`wlog h : P with H`**（without loss of generality，不失一般性）用对称性减少情形。它生成两个目标：先是
「`¬ P` 的情形可以化到 `P` 的情形」，此时 `H : ∀ a b, P → 原命题`（对所有变量全称化），`h : ¬ P` 在上下文里
；然后才是带着 `h : P` 的主情形。下面用 `a ≤ b` 的对称性证
`min a b ∣ a * b`，`trace_state` 显示第一个目标：
-/

/--
trace: case isFalse
a b : ℕ
H : ∀ (a b : ℕ), a ≤ b → min a b ∣ a * b
h : ¬a ≤ b
⊢ min a b ∣ a * b
-/
#guard_msgs in
example (a b : ℕ) : min a b ∣ a * b := by
  wlog h : a ≤ b with H
  · trace_state
    have := H b a (by omega)
    rwa [min_comm, mul_comm] at this
  · rw [min_eq_left h]
    exact dvd_mul_right a b

/-!
## 3. 归纳的组织

### 3.1 `generalizing`：归纳假设要够强

`induction n` 把目标里**除 `n` 之外**的变量当作固定的，归纳假设只对同一个固定值成立。若递推要改变另一个变量，
归纳假设就太弱。用尾递归累加函数 `sumAux` 说明：`sumAux acc n` 把 `acc` 加上 `0 + 1 + … + n`，每步改 `acc`。
-/

/-- 尾递归累加：`sumAux acc n = acc + (0 + 1 + … + n)`。 -/
def sumAux : ℕ → ℕ → ℕ
  | acc, 0 => acc
  | acc, n + 1 => sumAux (acc + n + 1) n

example : sumAux 5 3 = 11 := by decide

/-!
想证 `2 * sumAux acc n = 2 * acc + n * (n + 1)`。直接对 `n` 归纳，`succ` 情形展开后出现的是
`sumAux (acc + n + 1) n`，而归纳假设说的是 `sumAux acc n`，模式对不上，`rw [ih]` 找不到东西：
-/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  2 * sumAux acc n
in the target expression
  2 * sumAux (acc + n + 1) n = 2 * acc + (n + 1) * (n + 1 + 1)

case succ
acc n : ℕ
ih : 2 * sumAux acc n = 2 * acc + n * (n + 1)
⊢ 2 * sumAux (acc + n + 1) n = 2 * acc + (n + 1) * (n + 1 + 1)
-/
#guard_msgs in
example (acc n : ℕ) : 2 * sumAux acc n = 2 * acc + n * (n + 1) := by
  induction n with
  | zero => simp [sumAux]
  | succ n ih =>
    simp only [sumAux]
    rw [ih]

/-!
修法是 `induction n generalizing acc`：归纳假设变成 `∀ acc, 2 * sumAux acc n = …`，在 `succ` 情形可以取
`acc + n + 1`。若上下文里有依赖 `n` 的假设（如 `hn : 0 < n`），`induction` 会自动把它们
revert 再 intro，使归纳假设也带上这些假设，这就是 §1 里 `ih k hlt hk0` 要多传一个 `hk0` 的原因。
-/

/-- 累加函数的闭式：`2 * sumAux acc n = 2 * acc + n * (n + 1)`。 -/
theorem two_mul_sumAux (acc n : ℕ) : 2 * sumAux acc n = 2 * acc + n * (n + 1) := by
  induction n generalizing acc with
  | zero => simp [sumAux]
  | succ n ih =>
    simp only [sumAux]
    rw [ih (acc + n + 1)]
    ring

/-!
### 3.2 强归纳：本书统一的写法

要用「所有更小的情形」时，本书统一写 `induction n using Nat.strong_induction_on with | _ n ih => …`
（§1 已经用过），归纳假设是 `ih : ∀ m < n, P m`。规则是：**分支名必须等于归纳原理里对应绑定的名字**。
`Nat.strong_induction_on` 的唯一分支叫 `h`，没有意义，所以用通配符 `_`；Mathlib 里两种写法都有
（`| h n ih` 与 `| _ n ih`，后者如 `Mathlib/Analysis/Analytic/Inverse.lean` 的 `leftInv_removeZero`），
本书统一用 `_`。core 里的 `Nat.strongRecOn` 的分支叫 `ind`，可以写出来：
-/

example (n : ℕ) : n % 2 < 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih => omega

/-!
写错分支名，Lean 报两条错误：一条说分支名无效、应为 `h`，另一条说分支 `h` 没有给出：
-/

/--
error: Invalid alternative name `ind`: Expected `h`
---
error: Alternative `h` has not been provided
-/
#guard_msgs in
example (n : ℕ) : n % 2 < 2 := by
  induction n using Nat.strong_induction_on with
  | ind n ih => omega

/-!
`using`、`generalizing`、`with` 同时出现时，顺序固定为这个顺序：
-/

example (n k : ℕ) (hk : k ≤ n) : k ≤ n + 1 := by
  induction n using Nat.strong_induction_on generalizing k with
  | _ n ih => omega

/-!
### 3.3 `Nat.le_induction`：从某个起点开始

命题只对 `n ≥ m` 成立时，用 `Nat.le_induction`。它的目标有**两个**——`n` 和证明 `hn : m ≤ n`——所以写
`induction n, hn using Nat.le_induction`，分支是 `base`（无字段）与 `succ n hn ih`（三个名字）：
-/

example (n : ℕ) (hn : 4 ≤ n) : n ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    nlinarith [ih, hn]

/-!
## 4. 穷举与 `convert`

### 4.1 `fin_cases` 与 `interval_cases`

变量只有有限多个取值时，把它们逐个列出。`fin_cases x` 对 `x : Fin 3` 之类的有限类型变量分三种情形；
`interval_cases n` 在上下文里找 `n` 的上下界，对区间里每个值各生成一个目标。之后常用 `<;> simp_all` 收尾：
-/

example (x : Fin 3) (h : x ≠ 0) : 1 ≤ x.val := by
  fin_cases x <;> simp_all

example (n : ℕ) (h1 : 2 ≤ n) (h2 : n ≤ 5) (h : n ^ 2 = 16) : n = 4 := by
  interval_cases n <;> simp_all

/-!
### 4.2 `convert … using` 与 `congr!`

假设 `h` 和目标「几乎一样」，只差一处子项时，`exact h` 失败。`convert h` 比较目标与 `h` 的类型，
把**不同的子项**变成新目标（等式）；`using n` 限制向下比较的深度。下面 `h : P (0 + n)`，目标 `P n`，
`using 2` 展开到 `n = 0 + n` 这个等式：
-/

/--
trace: P : ℕ → Prop
n : ℕ
h : P (0 + n)
⊢ n = 0 + n
-/
#guard_msgs in
example (P : ℕ → Prop) (n : ℕ) (h : P (0 + n)) : P n := by
  convert h using 2
  trace_state
  omega

/-!
`congr!` 把形如 `f a = f b` 的目标按参数拆开，能用上下文里的假设（`assumption`）关掉的就地关掉，所以
`congr!` 常用来替代手工的 `congrArg`。两者都是「按函数应用拆开、比较参数」的策略。两边只差 cast
（类型转换）的「差一点」交给第 8 章的 `exact_mod_cast`。
-/

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f (a + 1) = f (b + 1) := by
  congr!

/-!
## 5. 检查：看清 Lean 实际看到的东西

出错时先别猜，看一看 Lean 实际拿到的是什么。

**`extract_goal`**（第 1 章见过）把当前目标连同上下文打印成一个独立的定理，打印出来的定理名带
命名空间，贴出去之前改短。它会丢掉与目标无关的变量和假设（下面的 `k` 与 `_hk`）：
-/

/--
info: theorem Lean4Learn.Ch13._example.extracted_1 (f : ℕ → ℕ) (hf : ∀ (x : ℕ), f x = x + 1)
(n : ℕ) : n < f n := sorry
-/
#guard_msgs in
example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) (n k : ℕ) (_hk : 3 < k) : n < f n := by
  extract_goal
  rw [hf]
  omega

/-!
**`set_option pp.explicit true`** 让 pretty printing（美观打印）显示所有隐式参数和实例，用来看 unification
（合一）到底在哪一步失败。下面的输出里，`a + b` 其实是 `HAdd.hAdd` 的应用，实例 `instHAdd Nat instAddNat` 才是加法的来源：
-/

/-- info: fun a b ↦ @HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) a b : Nat → Nat → Nat -/
#guard_msgs in
set_option pp.explicit true in
#check fun (a b : ℕ) ↦ a + b

/-!
**实例合成**出了问题时，错误信息自己会提示 `set_option trace.Meta.synthInstance true`（§6）。打开之后，
`trace:` 消息把合成的每一步展开成树，`✅️` 表示成功的分支（第一行就是目标 `Inhabited ℕ` 的结果）：
-/

/-- [Meta.synthInstance] ✅️ Inhabited ℕ -/
#guard_msgs (substring := true) in
set_option trace.Meta.synthInstance true in
example : Inhabited ℕ := inferInstance

/-!
## 6. 读懂错误信息

Lean 的错误信息有固定的结构：位置，错误的种类，再是「期望什么、得到什么」，最后常是目标的 proof state（证明状态）。
读法有三条：**先读第一条**；**对照期望与实际**，找出两者不同的那一处子项；
看不清时用 §5 的工具（`extract_goal`、`pp.explicit`、`trace.Meta.synthInstance`）看 Lean 实际拿到了什么。
基础的几种错误前面已经见过：type mismatch 与 application type mismatch（第 2、3 章）、unknown identifier
（第 1 章）、`linarith failed`（第 2 章，边界在第 10 章）。下面只讲调试长证明时才会遇到的几种，消息都用
`#guard_msgs` 捕获，所以是真的。

**① motive is not type correct。** 第 5 章 §5 讲过原因：`rw` 把目标里的 `n` 抽象成变量 `_a`，若别的项的类型
依赖 `n`（这里 `v : Fin n`），抽象后不再合法。完整消息后面还有一大段解释，我们只核对前半。补救办法按顺序：
`subst h`；其次 `rw!`（`Mathlib.Tactic.DepRewrite`，`castMode := .all` 时沿等式转运依赖项）：
-/

/-- error: Tactic `rewrite` failed: motive is not type correct:
  fun _a ↦ ↑v < _a -/
#guard_msgs (whitespace := lax, substring := true) in
example (n m : ℕ) (h : n = m) (v : Fin n) : v.val < n := by
  rw [h]

/-- `subst h` 把 `m` 整个换成 `n`，依赖关系消失。 -/
theorem val_lt_of_subst (n m : ℕ) (h : n = m) (v : Fin n) : v.val < m := by
  subst h
  exact v.isLt

example (n m : ℕ) (h : n = m) (v : Fin n) : v.val < n := by
  rw! (castMode := .all) [h]
  exact Fin.isLt _

/-!
**② failed to synthesize。** instance synthesis（实例合成）没找到实例。消息里的类型类告诉你缺什么，末尾的
`Hint` 告诉你怎样看过程（§5）。`Finset` 的并集需要 `DecidableEq`；下面缺它，于是有两处报错：陈述里的
`s ∪ t`（缺 `Union (Finset α)`），证明项 `Finset.card_union_le s t`（缺 `DecidableEq α`）。按「先读第一条」，
补救是在签名里加 `[DecidableEq α]`，两条一起消失：
-/

/--
error: failed to synthesize instance of type class
  Union (Finset α)

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  DecidableEq α

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (α : Type) (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card := Finset.card_union_le s t

example (α : Type) [DecidableEq α] (s t : Finset α) : (s ∪ t).card ≤ s.card + t.card :=
  Finset.card_union_le s t

/-!
**③ 目标数目不对。** `unsolved goals` 是策略块结束时还有目标没关，消息把剩下的目标原样打印出来（§1 的
`?_` 例子）。反过来，`No goals to be solved` 是多写了策略：上一步已经关掉了所有目标，删掉多余的行即可：
-/

/-- error: No goals to be solved -/
#guard_msgs in
example (a : ℕ) : a + 0 = a := by
  simp
  omega

/-!
**④ 运行资源与 `variable`。** 有两个错误和「写错了」无关。其一是 heartbeat（心跳）超限：
`maxHeartbeats` 以 1000 次小块内存分配为一个单位计量（默认 `200000`，即两亿次分配），不是秒数，所以不随机器快慢
变化。限制是 1 时几乎任何东西都会超：
-/

/--
(1) has been reached Note: Use `set_option maxHeartbeats <num>` to set the limit.
-/
#guard_msgs (whitespace := lax, substring := true) in
set_option maxHeartbeats 1 in
example (a b : ℕ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring

-- 200000 是默认值：把限制从 1 恢复回去，同一个证明就通过
set_option maxHeartbeats 200000 in
example (a b : ℕ) : (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 := by
  ring

/-!
调高限制是最后的手段：先看是不是用错了策略（决策表在第 10 章），要调就写成 `set_option maxHeartbeats N in`，
只管下一条声明。

其二是 `variable`。Lean 4.11 起，区段假设**不会因为在 `theorem` 的证明里被用到**就进入定理：证明里提到
陈述没提到的 `hn` 会失败（错误原文见第 15 章 §8）。`example` 则按使用包含区段变量（`def` 也是），同样的写法不出错。
哪些区段变量会进入定理（还有 `include`、实例变量等几种情形），完整规则在第 15 章 §8。下面的定理陈述为真、
不需要 `hn`；`fail_if_success` 断言 `hn` 在定理里确实不可见，`#check` 显示签名里没有它：
-/

section

variable (n : ℕ) (hn : 0 < n)

example : n ≠ 0 := hn.ne'   -- `example` 按使用包含 `hn`

theorem pos_succ_demo : 0 < n + 1 := by
  fail_if_success have := hn
  exact Nat.succ_pos n

/-- info: pos_succ_demo : ∀ (n : ℕ), 0 < n + 1 -/
#guard_msgs in
#check @pos_succ_demo

/-!
要在 `theorem` 里用 `hn`，写 `include hn in`（只管下一条声明），签名随之多出这个假设。在签名里直接写出假设，
通常比 `include` 清楚：
-/

include hn in
theorem ne_zero_of_hn : n ≠ 0 := hn.ne'

/-- info: ne_zero_of_hn : ∀ (n : ℕ), 0 < n → n ≠ 0 -/
#guard_msgs in
#check @ne_zero_of_hn

end

/-!
**交付前的检查。** 按核心库 `Init/Prelude.lean` 里 `sorryAx` 的说明，类型错误或策略失败处会被填入合成的 `sorry`；
确认一个定理不依赖 `sorry` 的办法是看 `#print axioms` 的输出里有没有 `sorryAx`：
-/

/-- info: 'Lean4Learn.Ch13.pos_succ_demo' does not depend on any axioms -/
#guard_msgs in
#print axioms pos_succ_demo

/-!
## 7. `simp?`、`says` 与 `conv`

**`simp?`** 运行 `simp` 并打印它实际用了哪些引理，写成 `simp only [...]`（第 5 章 §6）。它是**发现工具**：
确认某个 `simp` 到底靠什么引理成功。纪律是：**末尾的 `simp` 不要换成 `simp?` 的输出**。末尾的 `simp` 靠
simp 集吸收改动，换成一长串 `simp only` 则在引理改名时先坏。

**`says`** 把 `simp?` 的输出固定在文件里：写 `simp? says simp only [List.append_nil]` 之后，编译时只运行
`says` 后面的部分（快）。把 `set_option says.verify true` 打开，则会重新运行 `simp?` 并核对输出是否仍然
一致（见 `Mathlib/Tactic/Says.lean` 的说明）。下面的第二个例子故意写了一个不对的引理来模拟「引理改名」，
核对失败会告诉你要更新成什么：
-/

example (xs : List ℕ) : (xs ++ []).length = xs.length := by
  simp? says simp only [List.append_nil]

/--
error: Tactic `simp?` produced `simp only [List.append_nil]`,
but was expecting it to produce `simp only [List.length_append]`!

You can reproduce this error locally using `set_option says.verify true`.
-/
#guard_msgs in
set_option says.verify true in
example (xs : List ℕ) : (xs ++ []).length = xs.length := by
  simp? says simp only [List.length_append]

/-!
**`conv`** 进入表达式的某个位置，只在那里重写。第 5 章 §5 说过 `rw` 匹配不了含 bound variable（绑定变量）的
子项；`conv` 用 `ext x` 进入 `fun x ↦ …` 之内，那里 `x` 是普通变量。`rw` 直接失败：
-/

/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  f ?x
in the target expression
  (fun x ↦ f x * 2) = fun x ↦ (x + 1) * 2

f : ℕ → ℕ
h : ∀ (x : ℕ), f x = x + 1
⊢ (fun x ↦ f x * 2) = fun x ↦ (x + 1) * 2
-/
#guard_msgs in
example (f : ℕ → ℕ) (h : ∀ x, f x = x + 1) : (fun x ↦ f x * 2) = fun x ↦ (x + 1) * 2 := by
  rw [h]

example (f : ℕ → ℕ) (h : ∀ x, f x = x + 1) : (fun x ↦ f x * 2) = fun x ↦ (x + 1) * 2 := by
  conv_lhs =>
    ext x
    rw [h x]

/-!
本章用到的导航命令：`conv_lhs`（进入等式左边）、`ext x`（进入 `fun`）、`arg i`（进入函数的第 `i` 个显式参数）。
`conv` 块结束时会自动尝试 `rfl`，所以重写完就收工：
-/

example (a b c : ℕ) : a * (b + c) = a * (c + b) := by
  conv_lhs => arg 2; rw [Nat.add_comm]

/-!
## 8. 风格与代码检查器

Mathlib 的风格指南很长，下面七条值得记住。其中 1 的行宽、2、6 在本节用 linter 演示，5 的 `linter.style.show` 见第 4 章，其余是约定：

1. **行宽 ≤ 100 字符**，缩进两个空格，`by` 放在行尾，续行（定理陈述换行）缩进四个空格；
2. **`fun x ↦`，不写 `λ`；`<|`，不写 `$`；`·` 聚焦，不写 `.`**；
3. 声明的参数和返回类型都显式写出；不用 `Type _` 而用 `Type*`；
4. 假设写在冒号左边（`(h : …) : …`），而不是 `: … → … := by intro h`；
5. `show` 只用来标明中间目标，改变目标用 `change`；
6. 一次只做一件事：每个策略一行，多个目标用 `·`；
7. 末尾的 `simp` 不要换成 `simp?` 的输出（§7）。

### 8.1 语法类 linter

这些 linter 的选项名都以 `linter.style.` 开头，每个选项可以用 `set_option … true in` 对单条声明打开。
下面是带 `λ`、`$`、`.` 的「旧写法」：`cdot` 报两条（两处 `.`），另外两个各报一条：
-/

/--
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
---
warning: Please, use '·' (typed as `\.`) instead of '.' as 'cdot'.

Note: This linter can be disabled with `set_option linter.style.cdot false`
---
warning: Please use '<|' instead of '$' for the pipe operator.

Note: This linter can be disabled with `set_option linter.style.dollarSyntax false`
---
warning: Please use 'fun' and not 'λ' to define anonymous functions.
The 'λ' syntax is deprecated in mathlib4.

Note: This linter can be disabled with `set_option linter.style.lambdaSyntax false`
-/
#guard_msgs in
set_option linter.style.lambdaSyntax true in
set_option linter.style.dollarSyntax true in
set_option linter.style.cdot true in
example (f : ℕ → ℕ) (hf : ∀ x, f x = x + 1) : (∀ n, n < f n) ∧ (λ x => f x) 0 = 1 := by
  constructor
  . intro n
    rw [hf]
    omega
  . exact id $ hf 0

/-!
### 8.2 结构类 linter

下面两个 linter 针对**结构**而不是语法。`multiGoal`：产生多个目标后下一条策略没有用 `·` 聚焦。
`flexible`：`simp` 之类「灵活」的策略后面接着用 `rw` 之类「刚性」的策略，而它依赖 `simp` 产出的具体形状，
`simp` 一变就坏。修法之一是合成一步 `simpa using h`：第二个例子里空的 `#guard_msgs` 断言 linter 不再报告。
-/

/--
warning: The following tactic starts with 2 goals and ends with 1 goal,
1 of which is not operated on.
  exact hp
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
-/
#guard_msgs in
set_option linter.style.multiGoal true in
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  exact hp
  exact hq

/-- warning: `simp` is a flexible tactic modifying `⊢`. -/
#guard_msgs (substring := true) in
set_option linter.flexible true in
example (a b : ℕ) (h : a = b) : a + 0 = b := by
  simp
  rw [h]

#guard_msgs in
set_option linter.flexible true in
example (a b : ℕ) (h : a = b) : a + 0 = b := by
  simpa using h

/-!
行宽的 linter 是 `linter.style.longLine`，上限由选项 `linter.style.longLine.maxLineLength` 设定（默认值 100，
见 `Mathlib/Tactic/Linter/Style.lean` 里该选项的说明）。不必真写一行超长的代码：把上限临时调成 20，
26 个字符的一行就会被报告：
-/

/--
warning: This line exceeds the 20 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
-/
#guard_msgs in
set_option linter.style.longLine true in
set_option linter.style.longLine.maxLineLength 20 in
example : 2 + 2 = 4 := rfl

/-!
这些 linter 在 Mathlib 里由一个 linter 集 `linter.mathlibStandardSet` 统一打开，成员与下游项目的用法见
`Mathlib/Init.lean` 里它的说明；本书的 `lakefile.toml` 没有打开它，所以本节逐条用 `set_option … in`。

### 8.3 docstring

docstring 的约定：每个 `def` 和重要的 `theorem` 都写 `/-- … -/`；是完整的句子，以句号结尾；引用其他声明时用
反引号加全名（文档站里自动变成链接）；定理名用**粗体**；数学可以写 `$…$`。本章的 `sumAux` 与
`exists_pow_two_mul_odd` 就是这样写的。`/-! … -/` 写模块说明，依次是 `# 标题`、概述、`## Main definitions`、
`## Main statements`、`## Notation`、`## Implementation notes`、`## References`、`## Tags`。
本书的练习 docstring 以「练习 N.k（★）：」开头，是书的约定，不是 Mathlib 的。

## 常见错误

| 症状 | 多半的原因 | 先试 |
|---|---|---|
| `ih` 套不上 | 归纳变量之外的变量也在变 | `induction n generalizing acc` |
| `Invalid alternative name` | 分支名不是归纳原理里的绑定名 | 用错误信息里给的名字或 `_` |
| `motive is not type correct` | 别的项的类型依赖被重写的项 | `subst h`；`rw!` |
| `failed to synthesize` | 缺类型类实例（如 `DecidableEq α`） | 签名里加实例参数 |
| `unsolved goals` | 策略块提前结束，或 `?_` 没填 | 看消息里剩下的目标 |
| `No goals to be solved` | 上一步已关掉目标 | 删掉多余的策略 |
| 超限，`maxHeartbeats` | 策略选错，或规模真的大 | 换策略；最后才 `set_option … in` |
| `variable` 的假设找不到 | 没出现在陈述里 | `include h in`；或写进签名 |

## 练习

下面的练习按本章各节的顺序排列。练习 13.1、13.2、13.11、13.12、13.15 复习前面章节（提示里标出章号）。
-/

/-- 练习 13.1（★）：用 `suffices` 把目标化成只剩 `r`（第 4 章）。 -/
theorem ex_13_1 (p q r s : Prop) (h1 : p → q) (h2 : q → r) (h3 : r → s) : p → s := by sorry

/-- 练习 13.2（★）：`obtain ⟨k, hk⟩ := h` 拆开存在量词，然后 `omega`（第 2 章）。 -/
theorem ex_13_2 (n : ℕ) (h : ∃ k, n = 2 * k + 1) : n % 2 = 1 := by sorry

/-- 练习 13.3（★）：`set s := x + y with hs` 把长表达式换成 `s`，
然后 `mul_self_eq_zero`（`a * a = 0 ↔ a = 0`）。 -/
theorem ex_13_3 (x y : ℤ) (h : (x + y) * (x + y) = 0) : x + y = 0 := by sorry

/-- 练习 13.4（★★）：`induction n generalizing acc`；`succ` 情形先 `simp only [sumAux]`，
再对两个累加值分别用 `ih`（本章 §3.1）。 -/
theorem ex_13_4 (acc n : ℕ) : sumAux acc n = acc + sumAux 0 n := by sorry

/-- 练习 13.5（★★）：强归纳（§3.2）。写 `induction n using Nat.strong_induction_on with | _ n ih`；
`n = 2`、`n = 3` 直接给出见证，`n ≥ 4` 对 `n - 2` 用 `ih`。 -/
theorem ex_13_5 (n : ℕ) (hn : 2 ≤ n) : ∃ a b : ℕ, n = 2 * a + 3 * b := by sorry

/-- 练习 13.6（★★）：`Nat.le_induction`（§3.3）：`induction n, hn using Nat.le_induction`，
`succ` 情形用 `pow_succ`，再 `omega`。 -/
theorem ex_13_6 (n : ℕ) (hn : 1 ≤ n) : n + 1 ≤ 2 ^ n := by sorry

/-- 练习 13.7（★）：`interval_cases`（§4.1）：用 `h1`、`h2` 对 `n` 穷举，再 `omega` 或
`simp_all` 收尾。 -/
theorem ex_13_7 (n : ℕ) (h1 : 3 ≤ n) (h2 : n ≤ 6) (h : n * n + n = 30) : n = 5 := by sorry

/-- 练习 13.8（★）：`fin_cases`（§4.1）的替代：`Fin.ext : a.val = b.val → a = b` 把 `h0`、`h1` 变成
`x.val ≠ 0`、`x.val ≠ 1`，再交给 `omega`。 -/
theorem ex_13_8 (x : Fin 4) (h0 : x ≠ 0) (h1 : x ≠ 1) : 2 ≤ x.val := by sorry

/-- 练习 13.9（★）：`convert h using 2`（§4.2）把目标化成一个等式，再用 `hm` 关掉。 -/
theorem ex_13_9 (P : ℕ → Prop) (n m : ℕ) (hm : m = 0) (h : P (n + m)) : P n := by sorry

/-- 练习 13.10（★★）：`wlog h : a ≤ b with H`（§2）。主情形用 `max_eq_right`、`min_eq_left` 与 `ring`；
另一个情形取 `H b a`，用 `max_comm`、`min_comm` 重写后 `ring`。 -/
theorem ex_13_10 (a b : ℤ) : (a - b) ^ 2 = (max a b - min a b) ^ 2 := by sorry

/-- 练习 13.11（★★）：调试 motive 错误（§6 ①，第 5 章）并处理类型转换（第 8 章）。
`v : Fin n` 的类型依赖 `n`，对 `n` 的 `rw [h]` 会遇到 §6 ① 的错误；先 `subst h`，再 `exact_mod_cast`。 -/
theorem ex_13_11 (n m : ℕ) (h : n = m) (v : Fin n) : (v.val : ℤ) < m := by sorry

/-- 练习 13.12（★）：用三个 `have` 各给出一个平方非负的事实（`sq_nonneg (a - b)` 等），
再让 `linarith` 收尾（第 10 章）。 -/
theorem ex_13_12 (a b c : ℤ) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by sorry

/-- 练习 13.13（★★★）：自顶向下写一个陌生的证明（§1）。立方数模 9 只能是 0、1、8。
提示：`Nat.pow_mod`、`generalize`、`interval_cases`。先写 `sorry` 骨架，再逐个填。 -/
theorem ex_13_13 (n : ℕ) : n ^ 3 % 9 = 0 ∨ n ^ 3 % 9 = 1 ∨ n ^ 3 % 9 = 8 := by sorry

/-- 练习 13.14（★★）：`conv_lhs` 里用 `ext x` 进入 `fun`，再 `rw [h x]`（§7；直接 `rw [h]` 会失败）。 -/
theorem ex_13_14 (f g : ℕ → ℕ) (h : ∀ x, f x = g x + 1) :
    (fun x ↦ f x * f x) = fun x ↦ (g x + 1) * (g x + 1) := by sorry

/-- 练习 13.15（★）：类型转换（第 8 章）：先用 `exact_mod_cast` 得到 `ℤ` 里的等式，再收尾。 -/
theorem ex_13_15 (a b : ℕ) (h : a + b = 3) : ((a : ℤ) + b) * 2 = 6 := by sorry

/-!
## 小结

| 任务 | 工具 | 何时用 |
|---|---|---|
| 搭骨架 | `have h : T := sorry`、`refine ⟨?_, ?_⟩`、`suffices h : T by tac`、`obtain h : T` | 写陈述之后，先让主干编译 |
| 起短名 | `set x := e with h`、`generalize e = x` | 长表达式反复出现；对非变量做 `cases` |
| 对称性 | `wlog h : P with H` | 变量可交换 |
| 归纳 | `induction n generalizing x` | 归纳假设太弱 |
| 强归纳 | `induction n using Nat.strong_induction_on with \| _ n ih` | 要用所有更小的情形 |
| 从 `m` 起 | `induction n, hn using Nat.le_induction` | 命题只对 `n ≥ m` 成立 |
| 穷举 | `fin_cases x`、`interval_cases n` | 有限个取值 |
| 差一点 | `convert h using k`、`congr!`、`exact_mod_cast h` | 假设与目标只差一处 |
| 检查 | `extract_goal`、`pp.explicit`、`trace.Meta.synthInstance` | 出错时看 Lean 实际看到什么 |
| 固定 | `simp? says simp only [...]`、`says.verify` | 关键位置固定 `simp` 用的引理 |
| 局部重写 | `conv_lhs => ext x; rw [h x]`、`arg i` | `rw` 匹配不了含绑定变量的子项 |
| 风格 | `set_option linter.style.* true in` | 提交前检查 |
-/

/-!
## 延伸阅读

- Mathlib 贡献文档（`https://leanprover-community.github.io/contribute/`）：*Style guidelines*（`style.html`）、
  *Naming conventions*（`naming.html`）、*Documentation style*（`doc.html`）。
- 源码：`Mathlib/Tactic/Linter/Style.lean`（`λ`、`$`、`·`、行宽、`show`）、`Multigoal.lean`、
  `FlexibleLinter.lean`（同一目录），`Mathlib/Init.lean`（`linter.mathlibStandardSet`）。
- 策略：`Mathlib/Tactic/` 下的 `WLOG.lean`、`Set.lean`、`ExtractGoal.lean`、`Says.lean`、`Convert.lean`、
  `IntervalCases.lean`、`FinCases.lean`；归纳原理 `Mathlib/Data/Nat/Init.lean`。
- Lean 参考手册（`https://lean-lang.org/doc/reference/latest/`）中 `induction` 策略的说明；
  `variable` 的规则见 Lean v4.11.0 的发布说明。
- 本书第 5 章（`rw` 的 motive、`simp` 机制）、第 9 章（找引理）、第 10 章（自动化的边界）、
  第 15 章（`variable` 的完整规则）、第 23 章（向 Mathlib 贡献：`lake exe lint-style`、弃用策略）。
-/

end Lean4Learn.Ch13

end
