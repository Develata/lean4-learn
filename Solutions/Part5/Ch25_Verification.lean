module

public import Mathlib.Data.List.Sort

/-!
# 第 25 章　答案

`Lean4Learn/Part5/Ch25_Verification.lean` 中练习的参考答案。每道题的陈述与章节文件逐字相同。
练习用到的函数（`sgcd`、`logSteps`、`collatzFuel`、`ins`、`isort`、`findIdx`、`headS`、`mapL`、
`sumAcc`、`sumList`、`lastOpt`）和插入排序的几条主要定理在这里重新给出，使本文件自成一体。
-/

@[expose] public section

namespace Solutions.Ch25

/-! ## 章节里的函数与辅助定理（从章节文件复制） -/

/-- 减法版 Euclid 算法。 -/
def sgcd (a b : ℕ) : ℕ :=
  if a = 0 then b
  else if b = 0 then a
  else if a ≤ b then sgcd a (b - a)
  else sgcd (a - b) b
termination_by a + b

/-- 连续除以 `b` 直到 0 的次数（即 `b` 进制的位数）；`b ≤ 1` 或 `n = 0` 时为 0。 -/
def logSteps (n b : ℕ) : ℕ :=
  if h : 1 < b ∧ 0 < n then logSteps (n / b) b + 1 else 0
termination_by n
decreasing_by exact Nat.div_lt_self h.2 h.1

/-- 带燃料的 Collatz：燃料用完就停。对燃料的递归是结构递归。 -/
def collatzFuel : ℕ → ℕ → ℕ → ℕ
  | 0, _, steps => steps
  | fuel + 1, n, steps =>
    if n ≤ 1 then steps
    else if n % 2 = 0 then collatzFuel fuel (n / 2) (steps + 1)
    else collatzFuel fuel (3 * n + 1) (steps + 1)

/-- 把 `x` 插入一个（假定有序的）列表。 -/
def ins (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

/-- 插入排序。 -/
def isort : List ℕ → List ℕ
  | [] => []
  | x :: xs => ins x (isort xs)

theorem perm_ins (x : ℕ) (l : List ℕ) : List.Perm (ins x l) (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    by_cases h : x ≤ y
    · simp only [ins, h, ↓reduceIte]
      exact List.Perm.refl _
    · simp only [ins, h, ↓reduceIte]
      exact (ih.cons y).trans (List.Perm.swap x y ys)

theorem perm_isort (l : List ℕ) : List.Perm (isort l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih => exact (perm_ins x (isort xs)).trans (ih.cons x)

theorem sorted_ins (x : ℕ) (l : List ℕ) (hl : l.Pairwise (· ≤ ·)) :
    (ins x l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [ins]
  | cons y ys ih =>
    rw [List.pairwise_cons] at hl
    by_cases h : x ≤ y
    · simp only [ins, h, ↓reduceIte, List.pairwise_cons, List.mem_cons]
      refine ⟨?_, hl⟩
      rintro a (rfl | ha)
      · exact h
      · exact Nat.le_trans h (hl.1 a ha)
    · simp only [ins, h, ↓reduceIte, List.pairwise_cons]
      refine ⟨fun a ha ↦ ?_, ih hl.2⟩
      rcases List.mem_cons.mp ((perm_ins x ys).mem_iff.mp ha) with rfl | hmem
      · omega
      · exact hl.1 a hmem

theorem sorted_isort (l : List ℕ) : (isort l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [isort]
  | cons x xs ih => exact sorted_ins x _ ih

theorem eq_isort_of_sorted_perm (l m : List ℕ) (hm : m.Pairwise (· ≤ ·))
    (hp : List.Perm m l) : m = isort l :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ ↦ Nat.le_antisymm h₁ h₂) hm (sorted_isort l)
    (hp.trans (perm_isort l).symm)

/-- 在数组中从左到右查找等于 `x` 的位置。 -/
def findIdx (a : Array ℕ) (x : ℕ) : Option (Fin a.size) :=
  go 0
where
  go (i : ℕ) : Option (Fin a.size) :=
    if h : i < a.size then
      if a[i] = x then some ⟨i, h⟩ else go (i + 1)
    else none
  termination_by a.size - i

/-- 非空列表的首元素：前置条件写在参数类型里，函数体用 `.property` 取出证明。 -/
def headS {α : Type*} (l : {l : List α // l ≠ []}) : α := l.val.head l.property

/-- 列表求和（第 24 章 §1）。 -/
def sumList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sumList xs

/-- 最后一个元素，空列表给 `none`（第 24 章 §1）。 -/
def lastOpt {α : Type*} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => lastOpt xs

/-- 逐元素映射。 -/
def mapL {α β : Type*} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: mapL f xs

/-- 带累加器的求和（尾递归写法）。 -/
def sumAcc : ℕ → List ℕ → ℕ
  | acc, [] => acc
  | acc, x :: xs => sumAcc (acc + x) xs

theorem findIdx_go_none (a : Array ℕ) (x j : ℕ) (h : findIdx.go a x j = none) :
    ∀ (i : ℕ) (hi : i < a.size), j ≤ i → a[i] ≠ x := by
  fun_induction findIdx.go a x j with
  | case1 j hj hx => simp at h
  | case2 j hj hx ih =>
    intro i hi hji
    rcases Nat.eq_or_lt_of_le hji with rfl | hlt
    · exact hx
    · exact ih h i hi hlt
  | case3 j hj =>
    intro i hi hji
    omega

/-! ## 练习答案 -/

/-- 练习 25.1（★）：`mapL` 保持长度。 -/
theorem ex_25_1 {α β : Type*} (f : α → β) (xs : List α) :
    (mapL f xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapL, ih]

/-- 练习 25.2（★）：`mapL` 与 `++` 交换。 -/
theorem ex_25_2 {α β : Type*} (f : α → β) (xs ys : List α) :
    mapL f (xs ++ ys) = mapL f xs ++ mapL f ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapL, ih]

/-- 练习 25.3（★★）：`mapL` 与 `reverse` 交换。提示：用上一题和归纳假设。 -/
theorem ex_25_3 {α β : Type*} (f : α → β) (xs : List α) :
    mapL f xs.reverse = (mapL f xs).reverse := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapL, ex_25_2, ih]

/-- 练习 25.4（★★）：`mapL` 的成员刻画。提示：`simp [mapL, ih]` 之后只剩逻辑；
两侧的等式可能方向相反，需要 `eq_comm`（第 3、4 章）。 -/
theorem ex_25_4 {α β : Type*} (f : α → β) (b : β) (xs : List α) :
    b ∈ mapL f xs ↔ ∃ a ∈ xs, f a = b := by
  induction xs with
  | nil => simp [mapL]
  | cons x xs ih => simp [mapL, ih, eq_comm]

/-- 练习 25.5（★★）：尾递归求和与第 24 章的 `sumList` 一致。提示：`induction xs generalizing acc`。 -/
theorem ex_25_5 (acc : ℕ) (xs : List ℕ) : sumAcc acc xs = acc + sumList xs := by
  induction xs generalizing acc with
  | nil => simp [sumAcc, sumList]
  | cons x xs ih =>
    simp only [sumAcc, ih, sumList]
    omega

/-- 练习 25.6（★★）：验证第 24 章的 `lastOpt`：它就是库函数 `List.getLast?`。
提示：`fun_induction lastOpt xs`。 -/
theorem ex_25_6 {α : Type*} (xs : List α) : lastOpt xs = xs.getLast? := by
  fun_induction lastOpt xs with
  | case1 => rfl
  | case2 x => rfl
  | case3 x ys h ih =>
    rw [ih]
    cases ys with
    | nil => exact absurd rfl h
    | cons y zs => simp

/-- 练习 25.7（★）：`sgcd` 不超过两数之和。提示：`fun_induction sgcd a b`，四个分支都可以用
`omega`（第 2 章；注意每个分支的变量个数，§3）。 -/
theorem ex_25_7 (a b : ℕ) : sgcd a b ≤ a + b := by
  fun_induction sgcd a b with
  | case1 b => omega
  | case2 a h => omega
  | case3 a b h₁ h₂ h ih => omega
  | case4 a b h₁ h₂ h ih => omega

/-- 练习 25.8（★★）：`logSteps` 不超过 `n`。提示：`fun_induction logSteps n b`（§11 第 1 条说明
分支的变量个数），递归分支里先 `have := Nat.div_lt_self h.2 h.1`，再 `omega`。 -/
theorem ex_25_8 (n b : ℕ) : logSteps n b ≤ n := by
  fun_induction logSteps n b with
  | case1 n h ih =>
    have := Nat.div_lt_self h.2 h.1
    omega
  | case2 n h => omega

/-- 练习 25.9（★★）：燃料不会让步数变少。提示：`induction fuel generalizing n steps`，
然后对 `n ≤ 1` 与 `n % 2 = 0` 用 `by_cases`，`simp [collatzFuel, h]` 之后 `omega`。 -/
theorem ex_25_9 (fuel n steps : ℕ) : steps ≤ collatzFuel fuel n steps := by
  induction fuel generalizing n steps with
  | zero => simp [collatzFuel]
  | succ fuel ih =>
    by_cases h1 : n ≤ 1
    · simp [collatzFuel, h1]
    · by_cases h2 : n % 2 = 0
      · have := ih (n / 2) (steps + 1)
        simp [collatzFuel, h1, h2]
        omega
      · have := ih (3 * n + 1) (steps + 1)
        simp [collatzFuel, h1, h2]
        omega

/-- 练习 25.10（★）：用 `decide +kernel`（§5）证明一个具体的 `sgcd` 值，并用 `#print axioms`
确认它没有引入专属公理。 -/
theorem ex_25_10 : sgcd 100 75 = 25 := by
  decide +kernel

-- 只有两条标准公理，没有 `native_decide` 那样的专属公理。
/-- info: 'Solutions.Ch25.ex_25_10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ex_25_10

/-- 练习 25.11（★）：`isort` 保持长度与成员关系。提示：`perm_isort`、`List.Perm.length_eq`、
`List.Perm.mem_iff`。 -/
theorem ex_25_11 (l : List ℕ) :
    (isort l).length = l.length ∧ ∀ x : ℕ, x ∈ isort l ↔ x ∈ l :=
  ⟨(perm_isort l).length_eq, fun _ ↦ (perm_isort l).mem_iff⟩

/-- 练习 25.12（★）：`ins` 恰好多一个元素，即 `insBad` 违反的那条性质。
提示：`perm_ins` 与 `List.Perm.length_eq`，或者归纳。 -/
theorem ex_25_12 (x : ℕ) (l : List ℕ) : (ins x l).length = l.length + 1 := by
  have := (perm_ins x l).length_eq
  simpa using this

/-- 练习 25.13（★★）：`isort` 与 `++` 不交换（排序不是追加的同态）。提示：先把去掉 `¬` 的命题
写成一个 `example`，用 `plausible` 找反例（找到后删掉这个 `example`），再回到本题；
证明里 `intro h`，把反例代入。 -/
theorem ex_25_13 : ¬ ∀ xs ys : List ℕ, isort (xs ++ ys) = isort xs ++ isort ys := by
  intro h
  have := h [2] [1]
  revert this
  decide

/-- 练习 25.14（★★）：`headS` 的结果属于原列表。提示：`unfold headS`，`List.head_mem`。 -/
theorem ex_25_14 {α : Type*} (l : {l : List α // l ≠ []}) : headS l ∈ l.val := by
  unfold headS
  exact List.head_mem l.property

/-- 练习 25.15（★★★）：`findIdx` 的另一半规格说明（§6 的（b））：返回 `none` 时数组里没有 `x`。
提示：先对内部循环 `findIdx.go` 证明一个对起点 `j` 一般化的引理。 -/
theorem ex_25_15 (a : Array ℕ) (x : ℕ) (h : findIdx a x = none) :
    ∀ (i : ℕ) (hi : i < a.size), a[i] ≠ x := by
  intro i hi
  exact findIdx_go_none a x 0 h i hi (Nat.zero_le i)

end Solutions.Ch25

end
