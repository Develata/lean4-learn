module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Lean4Learn.Part1.Ch04_Tactics
public meta import Lean.Elab.Command
public meta import Lean.Util.CollectAxioms
public meta import Mathlib.Tactic.Linter.ValidatePRTitle

/-!
# 第 23 章　从练习到研究：形式化项目方法论与贡献 Mathlib

前 22 章的每个陈述都是别人给好的。研究里陈述要自己写，证明要自己拆，写完还要让别人相信。
本章讲这一整条链：怎样规划一个 formalization（形式化）项目，怎样设计 API，怎样在模块系统下组织多个文件，
怎样验证一个证明可信，怎样向 Mathlib 贡献，怎样在 Zulip 上提问，以及怎样负责任地使用 AI 助手。
正文是散文加小例子；所有能在 Lean 里演示的都编译过，只能在命令行或网站上做的，注明来源与是否实测。

## 学习目标
- 先写陈述再写证明：用 blueprint 和 `proof_wanted`、`sorry` 骨架规划一个项目（以第 20 章为例）；
- 设计 API：命名、参数、类型类假设、junk value（垃圾值）、`_def` 引理与 `@[expose]` 的取舍；
- 在模块系统下组织文件：`public import` 与 `import` 的区别（第 1 章 §8 没法演示的跨文件部分）；
- 验证一个证明：`#print axioms`、`native_decide` 的专属公理、`leanchecker`、`lake check`、`lake comparator`；
- 走一遍向 Mathlib 贡献的流程：fork、分支、`lake exe` 工具、PR 标题、评审、弃用政策、AI 使用政策；
- 会在 Zulip 上提一个能被回答的问题，会判断哪些活可以交给 AI、怎样核对它的产出。

## 前置知识
第 1 章（文件头、版本锁定、MWE（最小可复现例子）与 Zulip，§8、§10、§11）；第 2 章（截断减法）；
第 3、4 章（`#print axioms`）；第 9 章（找引理，§8；弃用警告，§13）；
第 13 章（`sorry` 分解，§1；交付前检查，§6；代码检查器，§8）；第 14 章（`Tendsto`、夹逼）；
第 20–22 章（本章的例子取自第 20 章的五步链与第 22 章 §9 的规划）。
-/

@[expose] public section

open Filter Topology

namespace Lean4Learn.Ch23

/-!
## 1. 规划：先写陈述，再写 blueprint

研究里最贵的错误是**形式化了错的陈述**，或者写到一半才发现缺一个没人证过的引理。流程因此是：

1. **陈述优先。** 在写任何证明之前，把要证的定理、用到的定义写成能通过 elaboration（精译）的陈述
   （假设、量词范围、垃圾值都要想清，见第 2 章、第 22 章 §3 与本章 §3）。陈述通过精译，才算定义对了。
2. **写 blueprint。** blueprint 是一份人读的数学提纲：每个定义、引理、定理一个节点，写清「用到谁」。
   节点是否对应 Lean 声明、证明是否完成，单独记录。
3. **按依赖图分工与推进。** 节点之间的依赖构成有向无环图；叶子可以单独陈述、单独证明（第 22 章 §9 的列表就是这样的
   一份依赖列表）。

**leanblueprint** 是 plasTeX 的一个插件，由 Patrick Massot 为 Sphere Eversion 项目写成，PFR、FLT 等大项目都用它。
你写 LaTeX，它生成网页与 PDF，并把依赖画成图。三个宏最重要（README 的宏表，2026-10-27 抓取）：

| 宏 | 含义 |
|---|---|
| `\lean{名字,…}` | 对应的 Lean 声明（含命名空间） |
| `\uses{标签,…}` | 依赖的节点；依赖图由它生成。写在陈述里，表示「写出这个陈述要用到」；写在 `proof` 环境里，表示「证明要用到」 |
| `\leanok` | 已形式化；写在陈述里表示陈述已形式化，写在 `proof` 环境里表示证明已完成 |

其余的宏（`\notready`、`\mathlibok`、`\discussion{编号}`）和命令（`leanblueprint new`、`pdf`、`web`、`serve`，
以及检查 `\lean{}` 里的声明真的存在的 `checkdecls`）见 README。下面是第 20 章最后两个节点，两个都已形式化，
所以都带 `\leanok`（本书没有安装 leanblueprint，这段 LaTeX 未经它处理，只对照了 README 的宏表）：

```latex
\begin{lemma}[含三角形的概率]\label{lem:P-triangle}
  \lean{Lean4Learn.Ch20.prob_triangle_le}\leanok
  $P(G(n,p)\text{ 含三角形}) \le \binom n3 p^3$.
\end{lemma}
\begin{proof} \leanok  取 $k=3$ 用 Markov 不等式。 \end{proof}

\begin{theorem}[三角形几乎必然不出现]\label{thm:tendsto}
  \lean{Lean4Learn.Ch20.tendsto_triangle}\leanok
  若 $np_n\to0$，则 $P(G(n,p_n)\text{ 含三角形})\to0$.
\end{theorem}
\begin{proof} \leanok \uses{lem:P-triangle}  夹逼。 \end{proof}
```

好的 blueprint 的标准：每个节点的陈述**单独可读**；依赖只写直接依赖；每个叶子你能估出「用 Mathlib 的哪几个引理」。
下面用一个玩具模型把「依赖图无环、依赖在前」这条要求变成可检查的东西：`Blueprint` 是（名字，依赖）的列表，
`ok` 检查名字互不重复、每个节点的依赖都出现在它之前。两条合起来说明列表的顺序就是一个拓扑序，所以（按名字
识别节点的）依赖图无环。第 20 章的十个主要节点（只算本书自己证明的，不含 Mathlib 现成的）：
-/

/-- 玩具版 blueprint：每个节点是（名字，直接依赖的节点名）。 -/
abbrev Blueprint : Type := List (String × List String)

/-- `Blueprint.ok bp seen`：按顺序检查，每个节点的名字是新的、依赖都已出现过（`seen` 是已出现的名字）。 -/
def Blueprint.ok : Blueprint → List String → Bool
  | [], _ => true
  | (n, us) :: rest, seen =>
    decide (n ∉ seen) && us.all (fun u ↦ decide (u ∈ seen)) && Blueprint.ok rest (n :: seen)

/-- 第 20 章的依赖图（节点名即 Lean 声明名，依赖取自各自证明里用到的本章引理）。 -/
def ch20Blueprint : Blueprint :=
  [("measure_edges_eq", []), ("real_edges_eq", ["measure_edges_eq"]),
   ("edge_marginal", ["real_edges_eq"]), ("integral_edgeCount", ["real_edges_eq"]),
   ("real_isClique", ["real_edges_eq"]), ("integral_cliqueCount", ["real_isClique"]),
   ("integral_triangleCount", ["integral_cliqueCount"]),
   ("prob_not_cliqueFree_le", ["integral_cliqueCount"]),
   ("prob_triangle_le", ["prob_not_cliqueFree_le"]),
   ("tendsto_triangle", ["prob_triangle_le"])]

example : Blueprint.ok ch20Blueprint [] = true := by decide

/-!
顺序错了（用到的节点还没出现）不合格；名字重复也不合格，否则 `[("a", []), ("a", ["a"])]` 按名字看是自环：
-/

example : Blueprint.ok [("tendsto_triangle", ["prob_triangle_le"]), ("prob_triangle_le", [])] [] =
    false := by decide

/-- info: false -/
#guard_msgs in
#eval Blueprint.ok [("a", []), ("a", ["a"])] []

/-!
## 2. 把 blueprint 变成 `sorry` 骨架与 `proof_wanted`

blueprint 的每个节点在 Lean 里有两种「先占位」的写法。

**写法一：`proof_wanted`。** 只陈述、不证明，**不产生 `sorry`**：Batteries 的 `proof_wanted` 把陈述装进一个
私有占位 `def name : ProofWanted 陈述 := ⟨⟩`（`Batteries/Util/ProofWanted.lean`），所以陈述要通过精译，
但没有任何定理被假装证明了。Mathlib 的 `Wanted/` 库就是这样存放「欢迎来证」的陈述。
它不是证明，不能当证明用（见「常见错误」）；`#print axioms` 对它报告「不依赖任何公理」，
因为它根本不是那条陈述的证明。名字前的 `_private.…0.` 是模块系统给私有声明加的前缀，不必理解。
（下面这条其实能由 Mathlib 现成的引理导出，练习 23.6 就是这样做的；这里借它演示写法。）
-/

proof_wanted pentagonal_le_add_one (k : ℤ) (hk : 0 ≤ k) : pentagonal k ≤ pentagonal (k + 1)

/--
info: '_private.Lean4Learn.Part4.Ch23_Methodology.0.Lean4Learn.Ch23.pentagonal_le_add_one'
does not depend on any axioms
-/
#guard_msgs in
#print axioms pentagonal_le_add_one

/-!
**写法二：`sorry` 骨架。** 第 13 章 §1 的自顶向下：主干是真的，叶子是 `sorry`。下面是第 20 章 `tendsto_triangle` 的
骨架（假设 `hP` 是第 4 步 `prob_triangle_le` 的结论，`squeeze_zero` 来自第 20 章 §9）。叶子 `hcube` 还没填，
所以只有一条警告；`exact squeeze_zero …` 这一行已经被检查过：
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
example (P p : ℕ → ℝ) (h0 : ∀ n, 0 ≤ P n) (hP : ∀ n, P n ≤ ((n : ℝ) * p n) ^ 3)
    (hp : Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop (𝓝 0)) : Tendsto P atTop (𝓝 0) := by
  have hcube : Tendsto (fun n : ℕ ↦ ((n : ℝ) * p n) ^ 3) atTop (𝓝 0) := sorry
  exact squeeze_zero h0 hP hcube

/-- 填完叶子（`Tendsto.pow`，第 14 章）：第 20 章 `tendsto_triangle` 的抽象版。 -/
theorem tendsto_of_cube_bound (P p : ℕ → ℝ) (h0 : ∀ n, 0 ≤ P n)
    (hP : ∀ n, P n ≤ ((n : ℝ) * p n) ^ 3)
    (hp : Tendsto (fun n : ℕ ↦ (n : ℝ) * p n) atTop (𝓝 0)) : Tendsto P atTop (𝓝 0) := by
  have hcube : Tendsto (fun n : ℕ ↦ ((n : ℝ) * p n) ^ 3) atTop (𝓝 0) := by
    -- hp.pow 3 : Tendsto (fun n ↦ (↑n * p n) ^ 3) atTop (𝓝 (0 ^ 3))
    -- simpa 先把 0 ^ 3 化成 0，再与目标对上
    simpa using hp.pow 3
  exact squeeze_zero h0 hP hcube

/-!
两种写法的分工：`proof_wanted` 用于**暂时不打算证**、只想让陈述入库的东西（blueprint 里还没轮到的节点）；
`sorry` 用于**马上要证**、想让编译器先检查主干的东西。交付前 `sorry` 必须清零：具名的 `sorry` 声明会把一条
可能为假的陈述导出给所有导入者，所以本书只在练习和 `#guard_msgs` 下的匿名 `example` 里留 `sorry`。

## 3. API 设计：设计先于代码

一个定义被别人用上之后，改名、改参数、改假设都是破坏性改动。所以在写证明之前先设计 API。检查表：

1. **命名**：照第 9 章的规范，结论优先，`_of_`、`_iff`、`pos`/`nonneg` 的位置固定。
2. **假设放最弱**：陈述在哪个 type class（类型类）里成立，就放在哪个类里，别写成 `ℕ` 或 `ℝ` 专用。
3. **junk value（垃圾值）要有处理**：总函数在无定义处取约定值；要么让引理带上排除它的假设，要么把「垃圾值是什么」
   单独写成一条引理，让读者查得到。
4. **每个定义配一条 `_def` 引理**，必要时配 `@[simp]` 引理：定义体不一定对下游暴露（§4）。
5. **docstring（文档注释）**：Mathlib 要求定义和主要定理有 docstring，普通引理鼓励有，具体规则见风格指南。
6. **讨论在前**：在 Zulip 的 `Is there code for X?` 先问有没有现成的；对要进 Mathlib 的新定义，先在 `mathlib4` 频道
   或 PR 草稿里讨论定义本身（Mathlib 的价值观页要求定义由领域专家和 Lean 专家审过，见延伸阅读）。

预算 `Budget` 演示第 3、4 条（以及第 1 条的命名）。`left` 用 `ℕ` 的截断减法，`spent > total` 时是垃圾值 `0`：
-/

/-- 预算：总额与已花费。 -/
structure Budget where
  total : ℕ
  spent : ℕ

namespace Budget

/-- 剩余额度。`ℕ` 的减法是截断的，`spent > total` 时取垃圾值 `0`。 -/
def left (b : Budget) : ℕ := b.total - b.spent

theorem left_def (b : Budget) : b.left = b.total - b.spent := rfl

/-- 主引理：带副条件 `spent ≤ total`。 -/
theorem left_add_spent (b : Budget) (h : b.spent ≤ b.total) : b.left + b.spent = b.total := by
  rw [left_def]
  -- ⊢ b.total - b.spent + b.spent = b.total
  omega

/-- 垃圾值引理：超支时 `left = 0`。它是真的，但在数学上没有意义，所以单独命名而不是藏在别的引理里。 -/
theorem left_eq_zero_of_total_le (b : Budget) (h : b.total ≤ b.spent) : b.left = 0 := by
  rw [left_def]
  -- ⊢ b.total - b.spent = 0
  omega

end Budget

/-!
没有副条件的版本是假的，这一点本身也要有一个编译过的见证（设计时问自己「去掉这个假设还成立吗」，就是在找它）：
-/

example : ¬ ∀ b : Budget, b.left + b.spent = b.total := by
  intro h
  have := h ⟨0, 1⟩
  -- this 是 h 在 total := 0, spent := 1 处的实例；展开 left 后是 0 - 1 + 1 = 0，即 1 = 0
  simp [Budget.left_def] at this

/-!
数据在前、假设在后，`b.left_add_spent h` 的点记号才顺手（第 9 章 §7）。第 2 条「假设放最弱」用 Mathlib 的
`mul_self_eq_zero` 演示：它不写成 `ℕ` 或 `ℝ` 专用，而是要求 `MulZeroClass` 加 `NoZeroDivisors`，所以对 `ℕ`、`ℤ`、`ℝ`
一次得到：
-/

/--
info: @mul_self_eq_zero : ∀ {M₀ : Type u_1} [inst : MulZeroClass M₀] [NoZeroDivisors M₀] {a : M₀},
  a * a = 0 ↔ a = 0
-/
#guard_msgs (whitespace := lax) in
#check @mul_self_eq_zero

example (a : ℕ) (h : a * a = 0) : a = 0 := mul_self_eq_zero.1 h
example (a : ℝ) (h : a * a = 0) : a = 0 := mul_self_eq_zero.1 h

/-!
## 4. 多文件项目与模块系统

第 1 章 §8 已经见过 `pentagonal`：它在 `public section` 里但没有 `@[expose]`，定义体不可见，`simp [pentagonal]` 与
`decide` 失败，作者特意导出的 `pentagonal_def` 可以用。那一节在单个文件里没法演示的是**跨文件**：别的文件到底能看到
什么？每个文件都是一个模块，要回答两个问题：别的文件能看到我的**名字**吗？能**展开**我的定义吗？

规则（Lean 参考手册「Source Files and Modules」）：module system（模块系统）下名字默认私有，
`public section` 或 `public` 让名字公开；公开的 `def` 的**定义体**仍然私有，除非 `@[expose]`（暴露）；
定理的证明永远私有。导入同理：`import M` 只让你自己看见 `M`，`public import M`（公开导入）把 `M` 的公开部分
转手给导入你的文件。

本文件头部是刻意的例外：全书其余章节一律 `public import`（第 1 章 §8），而这里第 4 章只在 `#print axioms`
里用，所以写成普通 `import`，好让规则露出来。先看单个文件里还能看到的一半：`pentagonal` 的定义体是
`<not imported>`，`rfl` 失败，作者的 `natCast_pentagonal` 可以用：
-/

/-- info: def pentagonal : ℤ → ℕ := <not imported> -/
#guard_msgs (whitespace := lax) in
#print pentagonal

/--
error: Tactic `rfl` failed: The left-hand side
  pentagonal 2
is not definitionally equal to the right-hand side
  5

⊢ pentagonal 2 = 5
-/
#guard_msgs in
example : pentagonal 2 = 5 := by rfl

example : pentagonal 2 = 5 := by
  have := natCast_pentagonal 2   -- (↑(pentagonal 2) : ℤ) = 2 * (3 * 2 - 1) / 2
  omega

/-!
这就是「定义 + `_def` 引理」模式（§3 第 4 条）：作者不暴露定义体，只承诺 `pentagonal_def` 这一条等式，
以后改实现不会破坏下游。

**`import` 与 `public import` 的区别（实测）。** 单文件演示不了「下游看不见」，所以用五个小文件做了实验
（Lean 4.35.0，`lean -o` 逐个编译，`LEAN_PATH` 指向输出目录；用 Lake 建成库应当得到同样的结果，但没有试）。
被导入的 `A` 里有一个暴露的和一个不暴露的定义：

```text
-- Ch23Mod/A.lean
module
@[expose] public section
def exposedFn (n : Nat) : Nat := n + 1
end
public section
def hiddenFn (n : Nat) : Nat := n + 2
theorem hiddenFn_def (n : Nat) : hiddenFn n = n + 2 := by rfl
end
```

其余文件各只有一两行有用内容：`BPlain` 是 `import Ch23Mod.A` 加 `public def useA (n : Nat) : Nat := exposedFn n`；
`BPub` 是 `public import Ch23Mod.A` 加同样的 `useA2`；`CPlain`、`CPub` 分别用普通 `import` 导入它们，再检查：

| 文件 | 内容 | 结果 |
|---|---|---|
| `CPlain` | `#check useA` | 通过 |
| `CPlain` | `#check exposedFn` | `error: Unknown identifier `exposedFn``（`A` 的名字没有传过来） |
| `CPub` | `#check exposedFn`；`example : exposedFn 1 = 2 := rfl` | 通过（暴露了，可以展开） |
| `CPub` | `example : hiddenFn 1 = 3 := rfl` | `error: Type mismatch`，附注里说 `hiddenFn` 的定义体没有暴露 |
| `CPub` | `example : hiddenFn 1 = 3 := by simp [hiddenFn_def]` | 通过 |

再看签名。`BSig` 是 `import Ch23Mod.A` 加
`public def sigFn (n : Nat) (h : exposedFn n = n + 1) : Nat := n`（`exposedFn` 出现在公开签名里）：它报
`error: Unknown identifier `exposedFn``，并附注 `A public declaration `exposedFn` exists but is imported
privately; consider adding `public import Ch23Mod.A`.`；把 `import` 换成 `public import`（`BSig2`）就编译通过。
而 `BPlain` 把 `exposedFn` 只用在定义体里，普通 `import` 就够。**经验规则：一个名字出现在你的公开签名里，定义它的模块就要
公开导入；只在（未暴露的）定义体里用，普通 `import` 够。**

另一个实测：在 `A` 里把 `hiddenFn_def` 写成项模式的 `:= rfl`（而不是 `by rfl`），编译器拒绝，并提示
`This theorem is exported from the current module. This requires that all definitions
that need to be unfolded to prove this theorem must be exposed.`。

**构建目标与 `lake`。** package（包）是 `lakefile.toml` 所在的单位，里面有若干 library（库）；
`lake build` 构建默认 target（构建目标，与证明里的「目标」无关）；`lake help build` 给出的目标语法是
`[@[<package>]/][<target>|[+]<module>][:<facet>]`，
例如 `lake build +Lean4Learn.Part2.Ch13_ProofEngineering` 只建一个模块（`+` 区分模块与库）。
`--wfail` 是 `--fail-level=warning` 的简写，有任何警告就失败（`--iofail` 连信息也算）；
本书的发布门槛就是 `lake build Solutions --wfail`（第 1 章 §3）。多文件时的另外两个工具：
`lake exe mk_all --lib 库名` 重新生成「导入全部模块」的聚合文件（`Foo.lean`；Mathlib 自己用它维护
`Mathlib.lean`，`--check` 只检查不改）；`lake shake` 找出没用上的导入（`lake help shake`：分析 `.olean`
推断实际需要的导入，`--fix` 直接改源文件，`--keep-public` 保留 `public` 导入）。

## 5. 信任一个证明：验证阶梯

「编译通过」不等于「可信」。从弱到强，一共五级。

**第 1 级：没有 `sorry`、没有错误。** 交付前检查见第 13 章 §6 末尾（用 `#print axioms` 找 `sorryAx`）；
下面第 2 级的审计示例里有一个 `sorryAx` 的实例。

**第 2 级：`#print axioms` 的清单。** 一个定理依赖的 axiom（公理）全在清单里。标准的三条是 `propext`、
`Classical.choice`、`Quot.sound`（第 28 章 §6），Mathlib 是经典的，出现它们是正常的；出现 `sorryAx` 是未完成；
出现别的名字（自己写的 `axiom`，或下面的 `native_decide`）要有理由。本书的两个定理对照
（第 4 章的 `by_contra_nat` 是构造性的，`double_neg_elim` 要经典逻辑）：
-/

/-- info: 'Lean4Learn.Ch04.by_contra_nat' does not depend on any axioms -/
#guard_msgs in
#print axioms Lean4Learn.Ch04.by_contra_nat

/--
info: 'Lean4Learn.Ch04.double_neg_elim' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Learn.Ch04.double_neg_elim

/-!
**审计示例：`native_decide` 与 `sorry`。** `native_decide` 不让内核求值，而是让编译器求值，再添一条**专属公理**。
`#print axioms` 只认已经存在的名字，而本书不愿为演示导出一个 `native_decide` 或 `sorry` 的具名声明，
所以下面这段是一小段元编程，把它当黑盒，只看输出：`withoutModifyingEnv` 在结束时丢掉里面新建的临时声明，
`elabCommand` 执行一条命令，`collectAxioms` 收集一个声明依赖的全部公理（这三个 API 本书不展开，见 Lean 源码）。
它建了三个临时定理：用一次 `native_decide`，用两次 `native_decide`，和带 `sorry` 的，然后依次打印公理清单：
-/

open Lean Elab Command in
/--
info: [_private.Lean4Learn.Part4.Ch23_Methodology.0.Lean4Learn.Ch23.nd1._native.native_decide.ax_1_1]
---
info: [_private.Lean4Learn.Part4.Ch23_Methodology.0.Lean4Learn.Ch23.nd2._native.native_decide.ax_1_1,
 _private.Lean4Learn.Part4.Ch23_Methodology.0.Lean4Learn.Ch23.nd2._native.native_decide.ax_1_2]
---
info: [sorryAx]
---
warning: declaration uses `sorry`
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  withoutModifyingEnv do
    let n1 := mkIdent `nd1
    let n2 := mkIdent `nd2
    let n3 := mkIdent `sr
    elabCommand (← `(theorem $n1 : (2 : ℕ) + 2 = 4 := by native_decide))
    elabCommand (← `(theorem $n2 : (2 : ℕ) + 2 = 4 ∧ 3 + 3 = 6 :=
      ⟨by native_decide, by native_decide⟩))
    elabCommand (← `(theorem $n3 : (2 : ℕ) + 2 = 4 := sorry))
    for nm in [`Lean4Learn.Ch23.nd1, `Lean4Learn.Ch23.nd2, `Lean4Learn.Ch23.sr] do
      logInfo m!"{(← liftCoreM <| collectAxioms nm).toList}"

/-!
读法：用一次 `native_decide` 得一条专属公理（`nd1._native.native_decide.ax_1_1`），用两次得两条（`ax_1_1`、
`ax_1_2`），即每次一条；前缀 `_private…` 是模块系统给私有名加的。`2 + 2 = 4` 不需要 `propext` 之类的标准公理，所以
清单里没有它们。专属公理断言「编译器说这个命题为真」，所以信任范围从内核扩大到整个编译器。Mathlib 因此禁止它
（`linter.style.native`，见第 25 章 §5）。带 `sorry` 的那个定理的清单是 `[sorryAx]`，并且有一条
`declaration uses `sorry`` 警告：这就是第 1 级要找的东西。

以前的写法是 `Lean.ofReduceBool`；它在 4.35 已删除（发布说明记为 4.35 的改动），在本书的工具链里查不到：
-/

/-- error: Unknown identifier `Lean.ofReduceBool` -/
#guard_msgs in
#check @Lean.ofReduceBool

/-!
**第 3 级：`leanchecker`。** 它把模块新增的所有声明重放进内核。工具链自带（4.28 起）；源码
`src/lean/LeanChecker.lean`（`leanprover/lean4`，标签 `v4.35.0`）的文档注释：`leanchecker` 检查整个当前项目，
`leanchecker Mathlib.Data.Nat` 检查名字以此开头的所有模块，`leanchecker --fresh 模块名` 把该模块的全部常量
（含导入的）重放进全新环境；并且声明「这不是外部验证器，只是检测环境被改动（environment hacking）的工具」。
一个由源码推得的坑：不带模块名运行时，它用 `lake-manifest.json` 里包名的首字母大写去找模块
（`getCurrentModule`），而本仓库的包名是 `lean4-learn`，所以大概率找不到；应当显式写成
`lake env leanchecker Lean4Learn.Part2.Ch13_ProofEngineering`。这些命令**本书都没有在本机运行**。

**第 4 级：外部检查器。** 内核本身是被信任的一份 C++ 代码，所以还有独立实现的检查器。`lake check`
（`lake help check`）：构建默认构建目标，导出，用内核重放，**遇到任何非标准公理就报错**；`--paranoid` 另外跑
`leanchecker-paranoid`、`lean4lean`、`nanoda` 等。它在 `bwrap`（bubblewrap，Linux 沙箱）里运行，
所以文档要求系统装有 `bwrap`；退出码 `0` 全部接受，`1` 被拒绝，`2` 无法启动（缺 `bwrap`、缺 `lake-manifest.json`、
没有默认构建目标）。原生 Windows 没有 `bwrap`，这一级应该在 WSL 里跑（未实测）。

**第 5 级：理解陈述。** 所有工具都只回答「这条陈述被证明了」。陈述是否忠实，只有人能判断，第 13 章 §5 的
「看清 Lean 实际看到的东西」与本章 §3 的垃圾值检查，是这一级的基本功。`lake comparator` 能把其中一部分机械化：
出题人发一个 `comparator.json`，写明挑战模块、解答模块、`theorem_names` 和 `permitted_axioms`；它确认解答里
每个同名定理**与挑战陈述相同**、只用允许的公理、并被内核接受。把它用来防「AI 证明了另一条陈述」，是本书作者的读法，
文档没有这么写（`lake help comparator`，未实测）。

**内核修复意味着什么。** 据发布说明（本书没有逐条核对），内核的可靠性漏洞在 2026 年持续被发现并修复
（4.32.1 到 4.34 的几个版本各有修复，部分由 AI 对抗性测试发现）。如果属实，含义有三：(1)「内核接受」是相对于某个
内核版本的结论，要写明工具链版本（本书钉在 `v4.35.0`）；(2) 重要结果值得用较新的工具链或外部检查器再检查一遍；
(3) 没有哪一层单独算数，所以参考手册的「Validating a Lean Proof」一章也是分层讲的。内核一侧见第 28 章 §17。

## 6. 向 Mathlib 贡献

Mathlib 欢迎小修补、单条引理和对现有理论的补充；新理论要符合「数学系通常教授或研究的材料」，且维护者愿意长期维护。
未合并的 PR 很多，所以：先在 Zulip 的 `mathlib4` 频道讨论；也可以做一个依赖 Mathlib 的独立仓库，
在 Reservoir 上登记。以下命令取自 Mathlib 的 `how-to-contribute` 页（2026-10-16 抓取）与 Git Guide
（<https://leanprover-community.github.io/contribute/git.html>，2026-10-27 抓取）；`git add`、`git commit`
是两页都没单列的普通 Git 步骤。全部**没有在本机执行**：

```bash
gh repo fork leanprover-community/mathlib4 --default-branch-only --clone
cd mathlib4                 # 克隆不改变当前目录
git fetch upstream          # origin 是你的 fork，upstream 是官方库
git branch --set-upstream-to=upstream/master master
gh repo set-default leanprover-community/mathlib4
lake exe cache get          # 下载预编译的 .olean
git switch -c my_new_branch
# 编辑；然后
lake build
lake exe mk_all             # 只有新增了文件时：更新 Mathlib.lean
lake exe lint-style         # 文本型 linter（代码检查器；行宽、尾随空白……）
git add Mathlib/路径/文件.lean Mathlib.lean
git commit -m "feat(路径): 一句话说明"
git push -u origin my_new_branch   # 然后对 leanprover-community/mathlib4:master 开 PR
```

要点：PR 一律从 fork 发（缓存对 fork 的 PR 也生效）；默认分支是 `master`；开始评审之后用 merge 而不是 rebase
（合并时会 squash）。提交前清掉调试痕迹：`#check`、`#eval`、`#loogle` 这类 `#` 开头的命令，以及 `exact?` 留下的
`Try this`。`linter.hashCommand` 专抓 `#` 命令（`Mathlib/Tactic/Linter/HashCommandLinter.lean`，读源码，
未实测）：`warningAsError` 关着时只对本身没有输出的 `#` 命令报警告；开着时（源码注释说 CI 如此）有输出的也报，
改记为 info；允许列表里的 `#adaptation_note` 不报。`exact?` 是策略，不在它的范围内，要手动清。
本地能构建、文本 linter 能过，CI 里还有语法 linter 集合 `linter.mathlibStandardSet` 与环境 linter（`simpNF` 等）。

**PR 标题**遵循 commit 约定：`<type>(<scope>): <subject>`，`type` 取
`feat fix doc style refactor test chore perf ci`，`subject` 用祈使句、小写开头、不以句号结尾，
`scope` 是去掉 `Mathlib/` 的路径（如 `Algebra/Group/Defs`）。
CI 的检查代码就在 pin 里（`Mathlib/Tactic/Linter/ValidatePRTitle.lean`），公开的 `validateTitle` 可以直接调用：
返回空数组表示通过，否则是错误信息：
-/

/-- info: #[] -/
#guard_msgs in
#eval validateTitle "feat(Probability/Combinatorics): add the degree of a vertex in `G(V, p)`"

/-- info: #["error: a PR's scope must not start with 'Mathlib/'"] -/
#guard_msgs in
#eval validateTitle "feat(Mathlib/Probability): add something"

/-- info: #["error: the PR title does not contain a colon"] -/
#guard_msgs in
#eval validateTitle "Add something"

/-!
**评审与合并。** CI 绿、没有阻塞标签的 PR 才进入评审队列（Zulip 的 `#queueboard`）。任何人都可以评审；
维护者在评论里写 `bors merge`（或 `bors r+`）做最后批准，由 bors 排队合并（`bors.toml`：squash；PR 描述里
`---` 以下的内容不进提交信息）。作者最常见的状态标签是 `awaiting-author`（等你改）、`awaiting-zulip`、`WIP`，
评审者可以加 `maintainer-merge`。读别人的 PR 时（也是学习的好办法）按这个顺序看：先读陈述与 docstring，
再看定义有没有重复造轮子，最后才读证明；每条评审意见都能追溯到风格指南或命名规范里的一条。

**弃用政策。** 改名时旧名变成带 `@[deprecated (since := "日期")]` 的别名，使用它产生警告（读法见第 9 章 §13）；
风格指南说弃用的声明可以在 **6 个月后**删除，Mathlib 仓库的 `remove_deprecated_decls.yml` 工作流每月 15 日运行，
默认删除 6 个月前弃用的声明（未在本机运行）。本机 pin 里带 2026-06 到 2026-10 日期的弃用别名约有 1300 个。所以：
重命名要提供别名，别名要带 `since`；而且要预期别名会消失。写法与效果：
-/

theorem add_zero_nat (n : ℕ) : n + 0 = n := rfl

@[deprecated (since := "2026-10-27")] alias add_zero_nat_old := add_zero_nat

/--
warning: `Lean4Learn.Ch23.add_zero_nat_old` has been deprecated: Use `Lean4Learn.Ch23.add_zero_nat` instead
-/
#guard_msgs (substring := true) in
example : 3 + 0 = 3 := add_zero_nat_old 3

/-!
**AI 使用政策**（Mathlib 贡献首页「Use of AI」一节，2026-10-27 抓取原页核对；以下是复述，只引一句原文）。
在 GitHub 或 Zulip 上写评论不得使用 LLM，要用自己的话。Mathlib 对泛化程度、与现有库的融合、可维护性（含代码风格）
的标准很高；页面写道，截至 2026 年中，没有 Lean 领域专家监督的 AI 代码 "fails to meet that bar by a large margin"。
评审团队会不加评论地直接关闭低质量的 LLM 产出的 PR；反复这样做的人会被禁止开 PR、禁止进入 Zulip。
如果你用了 AI 工具（Copilot、ChatGPT、Codex、Claude、Gemini，或 Aristotle 这类 Lean 专用代理），
**必须在 PR 描述里说明用了什么、怎么用的**；PR 含大量 LLM 生成的代码时，用评论 `LLM-generated` 加上同名标签。
作者必须理解 AI 写的全部内容，包括形式化中的设计决策，并且能不借助 AI 向评审者解释每一个决定。

## 7. Zulip：怎么问

Zulip（`leanprover.zulipchat.com`）是社区主要的交流处。第 1 章 §11 讲过 MWE 的要求，这里只补流程：

1. **选频道**：初学者问题去 `new members`；找某个结果去 `Is there code for X?`；建模选择去 `maths`；
   进 Mathlib 的事去 `mathlib4`；方向相关的有 `graph theory`、`Brownian motion` 等；
   元编程去 `metaprogramming / tactics`。先搜索（公开归档更新有滞后，较新的帖子要在 Zulip 里搜）。
2. **做 MWE、报告版本**：做法见第 1 章 §11（全部 `import`、`open`、`variable`，`sorry` 缩短，`extract_goal`，
   Show Setup Information）；先在 <https://live.lean-lang.org/> 里确认能复现。
3. **把错误固定下来**：本书到处用的 `#guard_msgs` 块是一种让读者复制进去就能看到同一条消息的写法（例子在下面）。
4. **问清楚**：说明你要证什么（数学陈述）、试过什么、卡在哪一步，而不是「帮我看看我的项目」。
   社区守则（`community_guidelines`）另外把用社区做作业、重复的低质量发帖、贴未经请求的 AI 生成代码
   列为可被处罚的行为（第 1 章 §11 提过的两条之外）。
5. **回帖**：问题解决后回一句怎么解决的，并把这个 MWE 里能留下的部分变成自己的测试。

第 3 条的例子：
-/

/--
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  c ≥ 0
where
 c := ↑a
-/
#guard_msgs in
example (a b : ℕ) (h : a ≤ b) : a < b := by omega

/-!
第 4 条的对比（一个虚构的例子）：

```text
差：标题「我的概率项目编译不了」；正文「求帮忙看看」。
好：标题「Tendsto.pow 之后 𝓝 (0 ^ 3) 化不成 𝓝 0」；正文依次是要证的数学陈述；Lean 4.35.0 / Mathlib v4.35.0；
    含全部 import 的最小代码；完整的错误信息；已经试过 simp、norm_num；卡在哪一步。
```

## 8. 负责任地使用 AI 助手

AI 助手在形式化里已经很有用，但「有用」与「可信」是两回事。下面的工具信息转述自各项目的 README
（2026-10-16 核对），本书没有重新测试：**lean-lsp-mcp**（`oOo0oOo/lean-lsp-mcp`）给 Claude Code、Codex 一类
代理接上 Lean 语言服务器，工具有 `lean_goal`、`lean_diagnostic_messages`、`lean_multi_attempt`、`lean_local_search`、
`lean_loogle`、`lean_leansearch`、`lean_verify` 等；Claude Code 里的安装命令是
`claude mcp add lean-lsp uvx lean-lsp-mcp`，先 `lake build` 一次再启动，装 `ripgrep` 才有 `lean_local_search`。
`lean4-skills` 是配套的 Claude Code 插件。远程的 Loogle 和 LeanSearch 有频率限制，并且会把你的查询发给外部服务器。

**可以交出去的活**：在本地 Mathlib 里搜引理名（`rg`、`lean_local_search`）、写样板（`Finset` 求和的拆分、
`measurability`/`fun_prop` 能关的目标）、给 `sorry` 叶子找候选证明、把已有证明改成不触发弃用警告的写法、
写测试与 `#guard_msgs`。**不能交出去的活**：决定陈述（它可能证明了另一条陈述）、选择定义、命名、
写 PR 描述与 Zulip 回复（政策禁止）。

**核对清单**（(2)–(4) 是机器检查，(1)、(5) 是人工审查）：(1) 自己读一遍每条陈述，AI 改过陈述就拒收；(2) `lake build` 零错误零警告；
(3) `#print axioms` 里没有 `sorryAx`，也没有陌生的 `axiom` 或 `native_decide` 的专属公理；(4) 有挑战陈述时用
`lake comparator`；(5) 自己能不借助 AI 解释每一步。第 (1) 条是关键，因为**漂移后的陈述往往更好证**。
设想你要的是「`x ≠ 0` 时 `x / x = 1`」：
-/

example : ∀ x : ℝ, x ≠ 0 → x / x = 1 := fun _ hx ↦ div_self hx

/-!
一个把假设 `x ≠ 0` 悄悄换成 `x = 1` 的助手，交出来的也是一份通过编译的证明，但它证明的陈述弱得多：
-/

example : ∀ x : ℝ, x = 1 → x / x = 1 := by
  intro x hx
  subst hx
  simp

/-!
编译器不会替你发现这种漂移，只有读陈述的人会。反过来，直接丢掉假设得到的陈述是假的，Lean 会拒绝：
-/

example : ¬ ∀ x : ℝ, x / x = 1 := by
  intro h
  simpa using h 0

/-!
## 9. 项目卫生

一个典型的失败：lakefile 里 Mathlib 的 `rev` 写成 `master`，几个月后再 `lake update`，拉到一个要求别的工具链的
Mathlib，几十个文件同时报弃用或改名错误。下面几条都是为了避免它。

1. **钉住版本**：`rev = "v4.35.0"`，`lean-toolchain` 与 `lake-manifest.json` 一起提交；第 1 章 §10 讲了原理，
   并用 `#eval Lean.versionString` 的断言让工具链一变就编译失败。
2. **升级是一次有计划的动作**（`lake update` 的副作用见第 1 章 §10）。顺序：同时改 `rev` 与 `lean-toolchain`，
   `lake update mathlib`，`lake exe cache get`，`lake build`，修弃用警告，再提交。越久不升级，一次要修的越多，
   所以按月或按季度升级比一年一次省事。
3. **缓存。** 依赖 Mathlib 的项目靠 `lake exe cache get` 下载 `.olean`；缓存键由 Mathlib 的 lakefile、工具链、清单
   与各文件内容的哈希组成，所以只在 Mathlib 官方 CI 构建过的提交上命中（标签版本最稳）。Windows 上缓存在
   `C:\Users\<用户>\.cache\mathlib`，可由环境变量 `MATHLIB_CACHE_DIR` 改；`lake update` 后会自动取缓存，
   设 `MATHLIB_NO_CACHE_ON_UPDATE=1` 可以关掉（以上来自 Mathlib 的 `Cache` 说明，未在本机验证）。
4. **CI。** `lake new 项目名 math` 的模板自带 `.github/workflows/lean_action_ci.yml`；你的项目至少要在 CI 里跑
   `lake build --wfail`，并让 `lake exe mk_all --check` 与 `lake shake` 把关导入。
5. **项目文档**：blueprint（§1）与 doc-gen4 生成的 API 文档一起发布到网页上，别人才知道哪些节点已完成。
   doc-gen4 的 `lake build 库名:docs` 要在一个单独的 `docbuild/` 子项目里运行（它 `require` doc-gen4 与你的库），
   见 doc-gen4 的 README；本书没有配置，未实测。

## 常见错误

**1. 在没有暴露的定义上用 `unfold`（`rfl`、`simp [定义]` 同理，见 §4 与第 1 章 §8）。**
改用作者给的 `_def` 引理（这里是 `pentagonal_def`），或者去问作者能否暴露，不要去改库：
-/

/-- error: Tactic `unfold` failed to unfold `pentagonal` in
  pentagonal 2 = 5 -/
#guard_msgs in
example : pentagonal 2 = 5 := by unfold pentagonal; rfl

/-!
**2. 把 `proof_wanted` 当证明用，类型对不上：**
-/

/--
error: Type mismatch
  pentagonal_le_add_one k hk
has type
  ProofWanted (pentagonal k ≤ pentagonal (k + 1))
of sort `Type` but is expected to have type
  pentagonal k ≤ pentagonal (k + 1)
of sort `Prop`
-/
#guard_msgs in
example (k : ℤ) (hk : 0 ≤ k) : pentagonal k ≤ pentagonal (k + 1) := pentagonal_le_add_one k hk

/-!
**3. 依赖图成环或顺序错。** blueprint 里把「用到」写反，节点就无法逐个推进；成环时更糟，没有任何排列合格。
`Blueprint.ok` 对环给出 `false`，靠重复声明 `a` 把 `a → b → a` 排成一列也一样（§1 的名字检查）：
-/

/-- info: (false, false) -/
#guard_msgs in
#eval (Blueprint.ok [("a", ["b"]), ("b", ["a"])] [],
  Blueprint.ok [("a", []), ("b", ["a"]), ("a", ["b"])] [])

/-!
**4. 陈述缺假设。** 去掉 `x ≠ 0`，`x / x = 1` 就是假的（§8）；而垃圾值会让一些「看起来荒谬」的陈述变成真的，所以
陈述写完要问「去掉这个假设还成立吗」。一个新手常见版本，直接套 `div_self` 会缺假设：
-/

/--
error: Type mismatch
  div_self
has type
  ?_ ≠ 0 → ?_ / ?_ = 1
but is expected to have type
  x / x = 1
-/
#guard_msgs in
set_option pp.mvars false in
example (x : ℝ) : x / x = 1 := div_self

/-!
## 练习

共 12 题（★ 八题，★★ 四题）。23.1、23.2 在玩具 blueprint 上练习依赖顺序；23.3、23.4 练习审计公理（复习第 3、4 章）；
23.5、23.6 用 `pentagonal` 的 API（第 1、9 章）；23.7、23.8 练习 API 设计与垃圾值（复习第 2 章）；23.9 是最弱假设
（第 8 章）；23.10、23.11 是风格修正（复习第 4、7、9 章）；23.12 把 `sorry` 骨架填成证明（复习第 14、20 章）。
-/

section Exercises

/-- 练习 23.1（★）：补一个节点。`c` 依赖 `a` 和 `b`，请给出中间那个节点 `b`（名字只能是 `"b"`，
它的依赖自己选），使整个列表合格。提示：`decide`。 -/
theorem ex_23_1 : ∃ b : String × List String,
    Blueprint.ok [("a", []), b, ("c", ["a", "b"])] [] = true := by sorry

/-- 练习 23.2（★★）：为第 22 章的上界 `cramer_upper` 写一个 blueprint：至少 5 个节点，最后一个是 `cramer_upper`，
所有依赖都在前面，依赖边（各节点依赖个数之和）至少 4 条。给出一个列表并用 `decide` 验证。
（节点可以取 Chernoff 方法、`iIndepFun.mgf_sum`、`iSup` 的上界等，第 22 章 §3–§5；Lean 不检查节点名
是否对应第 22 章，请自己对照。）
提示：先写节点名，再从 `cramer_upper` 往回写它的依赖。 -/
theorem ex_23_2 : ∃ bp : Blueprint, Blueprint.ok bp [] = true ∧
    (bp.map Prod.fst).getLast? = some "cramer_upper" ∧ 5 ≤ bp.length ∧
    4 ≤ (bp.map fun nd ↦ nd.2.length).sum := by sorry

/-- 练习 23.3（★）：经典逻辑要付出公理。证明 `¬¬p → p`，然后在你的草稿里运行 `#print axioms ex_23_3`，
确认清单里有 `Classical.choice`。提示：`by_contra` 或 `Classical.byContradiction`（第 4 章）。 -/
theorem ex_23_3 (p : Prop) (h : ¬¬p) : p := by sorry

/-- 练习 23.4（★）：同一个结论，命题可判定时不需要任何公理。证明后用 `#print axioms ex_23_4` 确认输出是
「does not depend on any axioms」，并与 23.3 对比。提示：`Decidable.of_not_not`。 -/
theorem ex_23_4 (p : Prop) [Decidable p] (h : ¬¬p) : p := by sorry

/-- 练习 23.5（★★）：只用作者导出的 API 证明 `pentagonal (-1) = 2` 与 `pentagonal (-2) = 7`
（第 1 章 §8：`rfl` 与 `simp [pentagonal]` 都不行；`ℤ` 的除法与负数交给 `omega`）。
提示：`natCast_pentagonal (-1)` 给出 `(↑(pentagonal (-1)) : ℤ) = -1 * (3 * -1 - 1) / 2`。 -/
theorem ex_23_5 : pentagonal (-1) = 2 ∧ pentagonal (-2) = 7 := by sorry

/-- 练习 23.6（★★）：把 §2 的 `proof_wanted` 做成定理。提示：在本地 Mathlib 的
`Combinatorics/Enumerative/Pentagonal/Basic.lean` 里找 `pentagonal` 的单调性引理（第 9 章 §8 的方法），
再用 `omega` 补上区间成员条件。 -/
theorem ex_23_6 (k : ℤ) (hk : 0 ≤ k) : pentagonal k ≤ pentagonal (k + 1) := by sorry

/-- 练习 23.7（★）：陈述漂移与垃圾值（§3、§8，第 2 章的截断减法）：`ℕ` 上 `a - b + b = a` 不总成立，
加上 `b ≤ a` 就成立。两个都要证。提示：反例取 `a = 0`、`b = 1`；`Nat.sub_add_cancel` 或 `omega`。 -/
theorem ex_23_7 : (¬ ∀ a b : ℕ, a - b + b = a) ∧ ∀ a b : ℕ, b ≤ a → a - b + b = a := by sorry

/-- 练习 23.8（★）：垃圾值引理的用法（§3）：超支时 `left = 0`，所以 `left + spent` 等于 `spent`；
严格超支时它不等于 `total`。提示：`Budget.left_eq_zero_of_total_le`，或 `Budget.left_def` 加 `omega`。 -/
theorem ex_23_8 (b : Budget) (h : b.total ≤ b.spent) : b.left + b.spent = b.spent := by sorry

/-- 练习 23.9（★）：把假设放最弱（§3，第 8 章）：对任意交换半环成立的二项平方公式，而不是 `ℕ` 或 `ℝ` 专用。
提示：`ring`。证完再把它用在 `ℕ` 与 `ℝ` 上。 -/
theorem ex_23_9 {R : Type*} [CommSemiring R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by sorry

/-- 练习 23.10（★）：风格修正（第 7、9 章）。旧的证明是 `by rw [Set.mem_setOf_eq]`，用了已弃用的名字，
`lake build --wfail` 会失败；改用新名字 `Set.mem_ofPred_eq`。 -/
theorem ex_23_10 (p q : ℕ → Prop) (a : ℕ) : (a ∈ {x | p x ∧ q x}) = (p a ∧ q a) := by sorry

/-- 练习 23.11（★）：风格修正（第 4 章）。旧的证明是 `push_neg at h` 加 `exact h`（`push_neg` 已弃用）；
改用 `push Not at h`。 -/
theorem ex_23_11 (p : ℕ → Prop) (h : ¬ ∀ n, p n) : ∃ n, ¬ p n := by sorry

/-- 练习 23.12（★★）：把 §2 的 `sorry` 骨架做成证明（第 14 章、第 20 章）：这次 `P n` 被两项之和控制，
`P n ≤ A n + B n`，`A`、`B` 都趋于 `0`。
分步骨架：(a) `hsum : Tendsto (fun n ↦ A n + B n) atTop (𝓝 0)`，用 `hA.add hB` 并把 `0 + 0` 化成 `0`；
(b) `squeeze_zero h0 hP hsum`。 -/
theorem ex_23_12 (P A B : ℕ → ℝ) (h0 : ∀ n, 0 ≤ P n) (hP : ∀ n, P n ≤ A n + B n)
    (hA : Tendsto A atTop (𝓝 0)) (hB : Tendsto B atTop (𝓝 0)) : Tendsto P atTop (𝓝 0) := by
  sorry

end Exercises

/-!
## 小结

| 概念 | 写法 | 何时用 |
|---|---|---|
| blueprint | LaTeX + `\lean{}`、`\uses{}`、`\leanok`（leanblueprint） | 项目有多个节点、多人协作时 |
| 只陈述不证明 | `proof_wanted 名字 : 陈述` | 陈述要入库，证明暂不做；不产生 `sorry` |
| 骨架 | `have 叶子 : 陈述 := sorry` | 马上要证，先让编译器检查主干 |
| API 设计 | 最弱的类型类假设；`_def` 引理；垃圾值引理；docstring | 定义被别人用上之前 |
| 模块可见性 | `public import`、`import`、`@[expose]`、`public section` | 名字在公开签名里 → `public import` |
| 构建 | `lake build`、`lake build +模块`、`--wfail`、`lake exe mk_all`、`lake shake` | 多文件、发布前 |
| 验证阶梯 | `#print axioms` → `leanchecker` → `lake check` → 人读陈述（`lake comparator`） | 要对一个结果负责时 |
| `native_decide` | 每次一条专属公理，Mathlib 禁止 | 只在自己的、不进 Mathlib 的代码里 |
| 贡献 | fork → 分支 → `lake exe mk_all`/`lint-style` → PR（标题 `feat(scope): …`）→ bors | 要进 Mathlib 时 |
| 弃用 | `@[deprecated (since := "日期")] alias 旧名 := 新名` | 重命名时；6 个月后可被删除 |
| AI 政策 | PR 描述说明工具；`LLM-generated` 标签；评论不得由 LLM 写 | 用了 AI 的 PR |
| 版本卫生 | 钉 `rev` 与 `lean-toolchain`；`lake update` 只在有意升级时 | 每个项目 |
-/

/-!
## 延伸阅读

- 本书：第 1 章 §8、§10、§11；第 13 章 §1、§6、§8；第 22 章 §9（blueprint 风格的依赖列表）；
  第 25 章 §5（`native_decide`）；第 28 章 §6（公理）、§15（模块系统内部）、§17（内核的信任边界）。
- Lean 参考手册 4.35.0（<https://lean-lang.org/doc/reference/4.35.0/>）：「Source Files and Modules」、
  「Validating a Lean Proof」、「Build Tools and Distribution」；`lake help check|comparator|build|shake`；
  `leanprover/lean4` 标签 `v4.35.0` 的 `src/lean/LeanChecker.lean`。
- Mathlib 贡献文档 <https://leanprover-community.github.io/contribute/index.html>（范围、「Use of AI」）
  及 `how-to-contribute`、`git.html`、`commit`、`naming`、`style` 各页；本地源码 `ValidatePRTitle.lean`、
  `HashCommandLinter.lean`（均在 `Mathlib/Tactic/Linter/`）、`bors.toml`。
- leanblueprint <https://github.com/PatrickMassot/leanblueprint>；Zulip 社区守则
  <https://leanprover-community.github.io/community_guidelines.html>。
-/

end Lean4Learn.Ch23

end
