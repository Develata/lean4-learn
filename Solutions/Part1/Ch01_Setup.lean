module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.NormNum.Basic

/-!
# 第 1 章　答案

本文件给出 `Lean4Learn.Part1.Ch01_Setup` 中各道练习的完整证明。陈述与练习逐字相同，只是证明体不同。
-/

@[expose] public section

namespace Solutions.Ch01

/-- 练习 1.1（★）：把 `sorry` 换成 `rfl`；再依次试 `decide` 与 `norm_num`，三者都应通过。 -/
theorem ex_1_1 : (6 : ℕ) * 7 = 42 := by rfl

-- 另外两种证法也都通过：
example : (6 : ℕ) * 7 = 42 := by decide
example : (6 : ℕ) * 7 = 42 := by norm_num

/-- 练习 1.2（★）：用 `decide` 证明。先在草稿里自己用 `\mid` 敲出 `∣`，确认它与键盘上的竖线 `|` 不是
同一个字符。 -/
theorem ex_1_2 : (7 : ℕ) ∣ 91 := by decide

/-- 练习 1.3 要用的函数：把一个自然数乘以 `3`。 -/
def triple (n : ℕ) : ℕ := 3 * n

/-- 练习 1.3（★）：先用 `#print triple`（第 6 节）看定义，用 `#eval triple 4` 算一次。因为文件头的
`@[expose]`（第 8 节），`triple` 的定义体对下游文件也是暴露的。本文件里 `decide`、`rfl` 与 `simp [triple]`
三种证法都应通过。 -/
theorem ex_1_3 : triple 4 = 12 := by decide

-- 另外两种证法也都通过：
example : triple 4 = 12 := by rfl
example : triple 4 = 12 := by simp [triple]

/-- 练习 1.4（★）：先在草稿里为 `#check Nat.succ_le_of_lt` 配一个留空的 `#guard_msgs in`，把真实消息
抄进去直到通过（第 6 节），再删掉草稿；比较它的签名与本题的陈述（几乎相同），然后用 `omega` 证明本题。 -/
theorem ex_1_4 (a b : ℕ) (h : a < b) : a + 1 ≤ b := by omega

/-- 练习 1.5（★）：用 `exact hq` 证明。再在整条声明前加一行 `set_option autoImplicit true in` 并删掉
`(P Q : Prop)`：声明仍然通过，`P`、`Q` 成了自动绑定的隐式参数（第 9 节）。去掉那行 `set_option` 之后，
同一份签名报 `Unknown identifier`（项目已全局关闭 `autoImplicit`）。最后恢复原样。 -/
theorem ex_1_5 (P Q : Prop) (_hp : P) (hq : Q) : Q := by exact hq

-- 打开 `autoImplicit` 后，不写 `(P Q : Prop)` 的签名也能通过：
set_option autoImplicit true in
example (_hp : P) (hq : Q) : Q := by exact hq

/-- 练习 1.6（★）：用 `constructor` 拆开目标，用 `trace_state` 看两个 `case`（第 4 节），再用 `·` 分别
`exact`。 -/
theorem ex_1_6 (A B : Prop) (ha : A) (hb : B) : A ∧ B := by
  constructor
  · exact ha
  · exact hb

/-- 练习 1.7（★）：先在草稿里试 `example : (2 : ℕ) + 2 = 5 := by decide`，读第 12 节那样的消息，
再删掉草稿；然后用 `decide` 证明本题。否定号 `¬` 用 `\not` 输入。 -/
theorem ex_1_7 : ¬ ((2 : ℕ) + 2 = 5) := by decide

/-- 练习 1.8（★）：把 `sorry` 换成 `exact?`，让 Lean 找出一个引理；再把 `exact?` 换成它给出的
`Try this` 里的内容。答案不止一个，你得到的引理可能与 `Solutions/` 里的不同。 -/
theorem ex_1_8 (a b c : ℕ) : a * (b + c) = a * b + a * c := Nat.left_distrib a b c

/-- 练习 1.9（★★）：先用 `omega` 证明。再试 `exact?`（第 7 节的例子就是这个形状，它会失败）；然后用
`Nat.lt_add_one_of_le`（输入 `Nat.lt_add_one` 按 `Ctrl+Space` 找到它，用 `#check` 看签名），配合
`Nat.le_trans` 与 `Nat.le_of_lt` 再证一遍，任选一种留在文件里。 -/
theorem ex_1_9 (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b < c) : a < c + 1 := by omega

-- 另一种证法（库引理）：
example (a b c : ℕ) (h₁ : a ≤ b) (h₂ : b < c) : a < c + 1 :=
  Nat.lt_add_one_of_le (Nat.le_trans h₁ (Nat.le_of_lt h₂))

/-- 练习 1.10（★）：`simp [pentagonal]` 在这里不可用（第 8 节）。改用 `pentagonal_def`，
再用 `rfl` 收尾；注意参数 `3` 是整数。 -/
theorem ex_1_10 : pentagonal 3 = 12 := by
  rw [pentagonal_def]
  rfl

/-- 练习 1.11（★）：`Nat.factorial` 的定义体是暴露的（第 8 节）。分别用 `simp [Nat.factorial]`、`decide`
与 `rfl` 证明，三者都应通过。 -/
theorem ex_1_11 : Nat.factorial 6 = 720 := by decide

-- 另外两种证法也都通过：
example : Nat.factorial 6 = 720 := by simp [Nat.factorial]
example : Nat.factorial 6 = 720 := by rfl

/-- 练习 1.12（★）：用 `intro n` 引入有名字的变量（第 4 节），用 `trace_state` 看它。先试 `rfl`，它会
失败，原因见第 12 节；再改用 `Nat.zero_add n`（配合 `exact`）或 `omega`。 -/
theorem ex_1_12 : ∀ n : ℕ, 0 + n = n := by
  intro n
  exact Nat.zero_add n

/-- 练习 1.13（★）：在 `omega` 之前加一行 `extract_goal`，读它打印的定理（第 11 节）；再在草稿里按第 11 节
把这个目标写成一份 MWE（完整的 `import`，用 `-- HERE` 标出疑问），然后删掉草稿；用 `omega` 证明。 -/
theorem ex_1_13 (x y : ℕ) (h₁ : x + y = 10) (h₂ : x = 4) : y = 6 := by omega

end Solutions.Ch01

end
