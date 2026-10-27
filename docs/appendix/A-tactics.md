# 附录 A　策略速查表（中英）

本附录把全书教过或演示过的 tactic（策略）与交互命令按用途汇成一张表，供写证明时查找「该用哪个、它在哪一章讲、
容易在哪里出错」。每行一条：名字、作用（一行）、典型写法、本书出处（「4 §2」即第 4 章 §2；没有编号的节写节名，如「27 常见错误 2」）、
陷阱。出处里的章节都有编译过的例子或用 `#guard_msgs` 固定的真实信息作证；本表本身不编译，有疑问时回到出处。
内容对应锁定版本 Lean `v4.35.0` + Mathlib `v4.35.0`（commit `56a0058`）；更名与弃用见附录 D，记号所需的
`open` 见附录 C。

**来源记法。** 不加标注的是 Lean 核心库策略，无需导入；「B」是 Batteries；「M:`X`」表示需要导入
`Mathlib.Tactic.X`（例如 M:`Ring` 即 `Mathlib.Tactic.Ring`）；只写「M」表示来自 Mathlib、本书没有点名模块。
本书文件只做窄导入，所以 `ring`、`linarith`、`norm_num`、`positivity`、`field_simp` 等都要各自导入
（第 10 章「小结」的决策表列出了导入）。

## 1. 逻辑与证明结构

| 策略 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `intro` | 引入 `→`、`∀` 的前提或变量 | `intro x hx` | 4 §2 | `¬p` 就是 `p → False`，所以目标 `¬p` 也能 `intro`（4 §5） |
| `rintro` | 带模式的 `intro`，同时拆开 `∧ ∨ ∃` | `rintro ⟨x, hx⟩`、`rintro (h \| h)` | 4 §3、§4；7 §4 | 像的成员常写 `rintro _ ⟨x, hx, rfl⟩`（第 7 章 §4） |
| `exact` | 用一个类型恰好对上的项关闭目标 | `exact h.1` | 4 §2 | 只差一处时改用 `convert`（第 13 章 §4） |
| `apply` | 倒推：用结论匹配目标的项，前提变成新目标 | `apply le_trans h` | 4 §2 | 结论合一失败报 `could not unify the conclusion`（4 §10 ②） |
| `refine` | 给出带洞 `?_` 的项，洞成为新目标 | `refine ⟨?_, ?_⟩` | 4 §2、§3；13 §2 | 写 `_` 不产生目标，报 `don't know how to synthesize placeholder`（4 §10 ①） |
| `assumption` | 在上下文里找类型相同的假设 | `assumption` | 4 §2 | — |
| `constructor` | 用目标类型的构造子拆开 `∧`、`↔` | `constructor` | 4 §3 | 对 `Or` 两个构造子都匹配时警告（4.35 起），改用 `left`/`right`（4 §4）；漏关一个目标留下 `case right`（4 §10 ③） |
| `left` / `right` | 选择证明析取的一边 | `left; exact hp` | 4 §4 | 本书一律用它们代替对 `Or` 的 `constructor` |
| `rcases` / `obtain` | 按模式拆开假设（`∧ ∨ ∃`、结构体） | `obtain ⟨x, hx⟩ := h`、`rcases h with hp \| hq` | 4 §3、§4、§6；13 §2 | `obtain h : T` 不写 `:=` 时 `T` 成为排在前面的新目标（13 §2） |
| `exfalso` | 把目标换成 `False` | `exfalso` | 4 §5 | — |
| `contradiction` | 上下文里有直接矛盾时关闭目标 | `contradiction` | 4 §5 | — |
| `absurd` (B) | 指定矛盾的一方，目标换成它的否定 | `absurd hp` | 4 §5 | 项模式的 `absurd hp hnp` 在核心库 |
| `use` (M:`Use`) / `exists` | 给 `∃` 的见证 | `use 7`、`use a, b`、`exists 2` | 4 §6 | `use` 会尝试关掉剩下的目标，关不掉的留给你（4 §6） |
| `by_cases` | 对命题分情况，分支标签 `pos`、`neg` | `by_cases h : p` | 4 §7 | 对任意命题会依赖经典公理，可判定命题不会（4 §7 的 `#print axioms`） |
| `by_contra` (B) | 反证：加入 `¬目标`，目标变 `False` | `by_contra h` | 4 §7 | 目标本身是 `¬q` 时引入的是 `h : q` |
| `by_contra!` (M) | `by_contra` 后对新假设 `push Not` | `by_contra! h` | 4 §7 | — |
| `push Not` (M:`Push`) | 把否定推过量词与联结词 | `push Not at h`、`push +distrib Not` | 4 §7 | 旧名 `push_neg` 已弃用（附录 D）；`¬(p ∧ q)` 默认变成 `p → ¬q` |
| `contrapose!` (M) | 换成逆否命题并整理否定 | `contrapose!` | 4 §7 | — |
| `tauto` (M:`Tauto`) | 经典命题逻辑重言式 | `tauto` | 4 §7；10 §7 | 不懂算术，目标一出命题逻辑就失败（10 §7） |
| `have` | 给中间结论起名 | `have h : T := by …` | 4 §8；13 §2 | 写全类型，后面的自动化才用得上 |
| `show` / `change` | 标明 / 改写为定义相等的目标 | `show T`、`change T at h` | 4 §8；7 §1 | 风格上 `show` 只用来标明，改目标用 `change`（13 §8） |
| `suffices` | 先说明只要证 `T` | `suffices h : T by tac` | 4 §8；13 §2 | — |
| `·`、`case` | 聚焦一个目标；按标签选目标 | `· exact hp`、`case pos => …` | 4 §9 | 用 `.` 当聚焦符号会被 `linter.style.cdot` 警告（13 §8.1） |
| `<;>`、`all_goals`、`try` | 对多个目标运行同一策略；失败不报错 | `constructor <;> omega` | 4 §9 | `try` 吞掉失败，调试时先去掉它 |
| `specialize` | 把 `∀` 假设实例化 | `specialize h 3` | 10 §4 | `omega`、`lia` 不会自己实例化 `∀` 假设 |
| `set` (M:`Set`) | 给子表达式起名并替换，附带等式 | `set x := e with hx` | 13 §2 | — |
| `generalize` | 把非变量的子项换成新变量 | `generalize e = x` | 13 §2 | 丢掉 `x` 与 `e` 的联系（13 §2） |
| `wlog` (M:`WLOG`) | 不失一般性，先证化归方向 | `wlog h : a ≤ b with H` | 13 §2 | 第一个目标是化归（带 `h : ¬P` 与 `H`），主情形在后 |
| `choose` (M:`Choose`) | 从 `∀ x, ∃ y, …` 取出函数与性质 | `choose f hf using h` | 7 §10 | 结果依赖选择公理，定义要 `noncomputable` |
| `classical` | 在证明里启用经典可判定性实例 | `classical` | 8 §12；12 §11 | 救不了陈述：陈述在它之外精译（12 §12 第 4 条） |
| `infer_instance` | 用实例合成关闭目标 | `infer_instance` | 16 §6 | 项模式写 `inferInstance`（8 §2） |

## 2. 归纳、分情况与递归

| 策略 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `induction … with` | 按构造子归纳，分支带归纳假设 | `induction n with \| zero => … \| succ n ih => …` | 2 §2；6 §2、§3 | `ℕ` 的目标显示 `0`、`n + 1`；NNG 的 `induction n with d hd` 是解析错误（2 §2）；分支名写错见 6 §11 第 2 条 |
| `induction … generalizing` | 归纳前把变量放回目标，加强归纳假设 | `induction xs generalizing acc` | 13 §3；25 §2 | 归纳假设太弱时首先想到它 |
| 强归纳 | 用所有更小的情形 | `induction n using Nat.strong_induction_on with \| _ n ih => …` | 13 §3 | 本书只用这一种写法 |
| `Nat.le_induction` | 从 `m` 起归纳 | `induction n, hn using Nat.le_induction` | 13 §3 | — |
| `Finset` 归纳 | 对有限集插入元素归纳 | `induction s using Finset.induction_on with \| empty => … \| insert a s ha ih => …` | 12 §5 | 一般类型上要先 `classical`（12 §12 第 2 条）；`Finset.cons_induction` 不要 |
| `cases` / `match` | 对构造子分情况 | `cases h`、`match x with \| … => …` | 6 §1、§4、§6 | `match` 必须穷尽，报错会列出缺的情形（6 §11 第 1 条） |
| `fun_induction` | 按函数的递归结构归纳 | `fun_induction f a b with \| case1 … => …` | 6 §5；25 §3 | 分支变量只含会变的参数、条件与 `ih`，个数写错报错（25 §11 第 1 条） |
| `fin_cases` / `interval_cases` (M) | 有限个取值逐一检查 | `fin_cases i`、`interval_cases n` | 13 §4 | `interval_cases` 从上下文里找 `n` 的上下界 |
| `termination_by` / `decreasing_by` | 给良基递归指定度量与证明 | `termination_by b`、`decreasing_by omega` | 6 §9；25 §4 | 良基递归默认不可约，`decide`、`rfl` 会失效（6 §9；25 §5）；`if` 不写 `h :` 时 `decreasing_by` 引用不到条件（25 §11 第 2 条） |

## 3. 等式、重写与简化

| 策略 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `rfl` | 两边定义相等时关闭目标 | `rfl` | 5 §2 | `0 + n = n` 对变量 `n` 不是定义相等 |
| `unfold` | 展开定义 | `unfold f` | 5 §2；10 §2 | 递归函数也可用 `simp [f]` 或等式引理 `f.eq_1`（6 §5） |
| `rw` | 用等式或 `↔` 精确改写子项 | `rw [h]`、`rw [← h] at h' ⊢` | 2 §2；5 §4 | 找不到匹配（2 §14 第 3 条）；不能改写含绑定变量的子项、motive 不合类型（5 §5） |
| `nth_rw` (M:`NthRewrite`) | 只改第 n 处出现 | `nth_rw 1 [h]` | 5 §4 | 计数次序见 5 §4 |
| `rw!` (M) | `rw` 报 motive is not type correct 时的替代 | `rw! [h]`、`rw! (castMode := .all) [h]` | 5 §5 | — |
| `rwa` | `rw` 后 `assumption` | `rwa [h] at this` | 13 §2 等处使用 | `rwa … at h₁ h₂` 一类旧写法已弃用（附录 D） |
| `simp` | 用 simp 集重写到正规形 | `simp`、`simp [h]`、`simp at h` | 2 §10；5 §6；10 §2 | 不看上下文假设；没有进展就报错 `simp made no progress`（5 §11 ①）；方向相反的引理会循环（5 §11 ③、10 §2） |
| `simp only` | 只用列出的引理 | `simp only [add_zero]` | 5 §6；10 §2 | 没用上的参数触发 `linter.unusedSimpArgs` 警告（10 §2） |
| `simp` 配置 | `+flag`、`-flag`、`(disch := tac)` | `simp +arith`、`simp (disch := omega) [l]` | 5 §7；10 §2 | 旧的 `simp_arith` 在 4.35 直接报错（2 §14 第 4 条） |
| `simpa` | `simp` 目标与假设后关闭 | `simpa using h` | 5 §6 | — |
| `simp_all` | 假设与目标互相简化直到稳定 | `simp_all` | 5 §7；10 §2 | `simp at *` 只各自简化，不互相代入（10 §2） |
| `simp_rw` (M:`SimpRw`) | 按序逐条 `simp only`，能进 binder | `simp_rw [l₁, l₂] at h` | 5 §5；10 §2 | 每条规则都必须改动目标，否则报错（10 §2） |
| `calc` | 等式与不等式的链 | `calc a = b := … ` 换行 `_ ≤ c := …` | 2 §11；5 §8 | 链没到终点会多出 `calc.step` 目标（5 §11 ②） |
| `congr` / `congr!` (M) | 把等式推到函数的参数 | `congr 1`、`congr!` | 5 §9；13 §4 | — |
| `convert` (M:`Convert`) | 用一个只差几处的项，不同的子项变成等式目标 | `convert h using 2` | 13 §4 | `using k` 限制向下比较的深度 |
| `subst` | 用变量等式消去变量 | `subst h` | 5 §9 | — |
| `ext` / `funext` | 函数、集合等相等化成逐点相等 | `ext x`、`funext x` | 5 §9；7 §2 | 结构体要 `@[ext]` 才有 `ext` 引理（6 §8） |
| `symm` / `trans` (B) | 翻转等式；拆传递链 | `symm`、`trans b` | 5 §9 | — |
| `conv`、`conv_lhs` (M) | 进入子项局部重写（`conv` 是核心，`conv_lhs` 来自 Mathlib） | `conv_lhs => ext x; rw [h x]` | 13 §7 | — |
| `simp? says` (M:`Says`) | 固定 `simp?` 的输出并可复核 | `simp? says simp only [...]` | 13 §7 | 末尾收尾的 `simp` 不必换成 `simp only`（13 §8） |
| `push_cast` / `norm_cast` / `exact_mod_cast` | 推进、拉出、消去强制转换 `↑` | `push_cast`、`norm_cast at h`、`exact_mod_cast h` | 2 §13；8 §9 | `ℕ` 减法与转换不交换，`push_cast` 不会去上下文找 `b ≤ a`（8 §14 第 3 条） |
| `field_simp` (M:`FieldSimp`) | 清分母（等式交叉相乘，不等式要正） | `field_simp` 然后 `ring` | 10 §3 | 证不出分母 `≠ 0`/`> 0` 就跳过，不报错（10 §3）；新版 `field_simp [t]` 的 `t` 只交给副条件处理器 |
| `filter_upwards` (M) | 合并若干 `∀ᶠ`/`∀ᵐ` 假设，化为逐点推导 | `filter_upwards [h₁, h₂] with x hx₁ hx₂` | 14 §3；16 §5 | — |

## 4. 算术与判定过程

| 策略 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `norm_num` (M:`NormNum`) | 数值计算、比较、素数、`gcd` | `norm_num`、`norm_num [h] at h'` | 2 §3；10 §5 | 素数、`gcd` 扩展要 `NormNum.Prime`、`NormNum.GCD`；假命题被化成 `False`，报错显示化简后的目标（10 §5） |
| `ring` (M:`Ring`) | 交换（半）环恒等式 | `ring`、`ring_nf`、`ring1` | 2 §5；10 §3 | 不读假设；`ℕ` 减法、`x / x` 不在范围内；`ring` 失败时退回 `ring_nf` 并提示 |
| `field` (M:`Field`) | 含除法的恒等式（`field_simp` + `ring`） | `field`、`field [hf]` | 10 §3 | 分母 `≠ 0` 要能从上下文或给出的项得到 |
| `linear_combination` (M:`LinearCombination`) | 检查目标是假设的给定线性组合 | `linear_combination (h₁ + h₂) / 2` | 10 §3 | 系数不对时用 `(norm := ring_nf)` 看残差；`≤` 假设的系数须非负 |
| `grobner` | 多项式等式（不给系数） | `grobner` | 10 §3 | 不输出 `linear_combination` 系数；`polyrith` 已不可用 |
| `abel` (M:`Abel`) | 交换加群恒等式 | `abel` | 10 §3 | 不读假设，先 `rw` |
| `omega` | `ℕ`、`ℤ`、`Fin` 上的线性算术，含截断减法、字面量 `/ % ∣` | `omega` | 2 §6；10 §4 | 非线性、`ℝ` 上无效（`No usable constraints`，10 §9 ④）；不实例化 `∀` 假设 |
| `lia` | `grind` 的整数线性算术入口，可喂额外事实 | `lia [h 3]` | 10 §4 | 旧名 `cutsat` 已弃用（10 §9 ①） |
| `decide` | 求值可判定命题 | `decide`、`decide +revert` | 5 §3；6 §10；10 §4 | 不能有自由变量（`+revert` 先回退）；`ℝ`、`ℝ≥0∞` 上无效（16 §9 第 3 条）；数据大时撞递归深度；良基递归不可约（25 §5） |
| `decide +kernel` | 让内核求值，绕过可约性 | `decide +kernel` | 5 §3；10 §4；25 §5 | 度量不取值于 `ℕ` 的良基递归仍可能失败（6 §9） |
| `native_decide` | 编译后求值 | `native_decide` | 25 §5 | 每次使用加一条专属公理；Mathlib 禁止（`linter.style.native`） |
| `cbv` | 按值调用式化简 | `cbv` | 25 §5 | — |
| `linarith` (M:`Linarith`) | 有序域上的线性不等式 | `linarith [t]`、`linarith +splitNe` | 2 §7；10 §6 | 默认不用 `≠` 假设；不拆 `min`（11 §11 第 4 条） |
| `nlinarith` (M:`Linarith`) | 加入乘积与平方后再 `linarith` | `nlinarith [sq_nonneg (a - b)]` | 2 §8；10 §6；11 §10 | 需要的因式要作为提示给出 |
| `positivity` (M:`Positivity`) | 证 `0 < e`、`0 ≤ e`、`e ≠ 0` | `positivity` | 2 §9；10 §6 | 按语法递归；`a - b` 只在上下文恰有 `b < a`、`b ≤ a`、`a ≠ b` 一类关于这两项的假设时处理（`Mathlib/Tactic/Positivity/Basic.lean:182`），`h : b ≤ a` 推不出 `0 ≤ a * c - b * c`（10 §6） |
| `gcongr` (M:`GCongr`) | 两边结构相同的不等式拆成各位置比较 | `gcongr`、`gcongr with i hi` | 10 §6；11 §1 | 副条件证不了时留作目标（如 `case ha`）；两边无共同结构报 `did not make progress` |
| `bound` (M:`Bound`) | 基于 `@[bound]` 规则的不等式搜索 | `bound` | 10 §6 | 不会自己构造 `(a - b) ^ 2` 这类项 |
| `order` (M:`Order`) | 预序、偏序、全序与格上的纯序事实 | `order` | 10 §6 | 不懂分配律（10 §6） |
| `aesop` (M:`Common`) | 规则库上的最佳优先搜索 | `aesop`、`aesop (add norm unfold D)` | 10 §7 | 不展开新定义；部分集合恒等式无进展（10 §7） |
| `grind` | 同余闭包 + 线性整数算术 + 环/域 + 分情况 | `grind`、`grind?` | 10 §1、§4、§7 | 不会自己归纳：先 `induction` 再 `grind`（10 §7） |

## 5. 搜索与诊断

| 策略 / 命令 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `exact?` | 在已导入的声明里找关闭目标的项 | `exact?` | 1 §7；2 §12；9 §9 | 找不到时报错；提交前换成它建议的显式写法 |
| `apply?` / `rw?` | 找可 `apply` 的项 / 可改写目标的等式 | `apply?`、`rw?` | 9 §9 | 同上，是调试工具 |
| `simp?` | 把 `simp` 用到的引理写成 `simp only [...]` | `simp?` | 5 §6；9 §9 | — |
| `hint` (M) / `try?` | 依次试一批策略并列出成功者 | `hint`、`try?` | 9 §9 | 输出多行，`#guard_msgs` 宜用 `substring := true` |
| `grind?` | 报告等价的 `grind only [...]` | `grind?` | 10 §7 | — |
| `#min_imports` (M) | 计算一条命令所需的最少导入 | `#min_imports in example …` | 9 §14 | 输出已带 `public` |
| `#loogle` / `#leansearch`（LeanSearchClient 包） | 站外按形状 / 自然语言搜索 | `#loogle Nat.succ_le_succ` | 9 §10（只有文字） | 需联网，查询会发到外部服务器；站外结果领先锁定版本，以本地 `#check` 为准 |
| `trace_state` | 打印当前证明状态 | `trace_state` | 1 §4 | 配合 `#guard_msgs` 固定 infoview 内容 |
| `show_term` | 显示策略证明拼出的项 | `by show_term tac` | 3 §11 | — |
| `guard_target` | 断言当前目标的形状 | `guard_target = (a = b)` | 10 §1 | — |
| `extract_goal` (M:`ExtractGoal`) | 把当前目标打印成独立的 `example` | `extract_goal` | 1 §11；13 §5 | 用来做 MWE |
| `pp.explicit` | 显示全部隐式参数与实例 | `set_option pp.explicit true in` | 13 §5 | — |
| `trace.Meta.synthInstance` | 跟踪实例合成 | `set_option trace.Meta.synthInstance true in` | 13 §5 | 实例合成失败时错误信息自己会提示它 |

## 6. 测度、概率与函数性质

| 策略 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `fun_prop` (M:`FunProp`) | 沿 `fun` 的语法证 `Continuous`、`Measurable` 等 | `fun_prop` | 10 §8；14 §4、§11；16 §2 | 集合可测性要先化成函数可测性（16 §2） |
| `measurability` (M:`Measurability`) | 基于 `aesop` 的可测性证明，也处理集合 | `measurability` | 10 §8；16 §2 | 较老；新引理应标 `@[fun_prop]`（10 §8） |
| `continuity` (M:`Continuity`) | 基于 `aesop` 的连续性证明 | `continuity` | 10 §8 | 同上，优先 `fun_prop` |
| `finiteness` (M:`Finiteness`) | 证 `ℝ≥0∞` 里的 `x ≠ ∞` | `finiteness` | 10 §8；16 §4 | 测度有限要有 `IsFiniteMeasure` 实例（16 §9 第 4 条） |

## 7. 程序验证

| 策略 / 命令 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `#guard` | 运行布尔检查或可判定命题 | `#guard f 3 = 6` | 24 §1；25 §8 | 是测试，不是证明 |
| `plausible`（`plausible` 包） | 随机找反例 | `plausible (config := { randomSeed := some 7 })` | 25 §8 | 没找到反例时目标被当作 `sorry` 关掉，不算证明 |
| `vcgen` | 命令式程序的验证条件（实验性） | `set_option experimental.vcgen true`；`vcgen` | 25 §10 | 实验性；旧名 `mvcgen` 已弃用（附录 D） |

## 8. 命令、选项与元编程

| 命令 | 作用 | 典型写法 | 本书 | 陷阱 |
|---|---|---|---|---|
| `#check` / `#eval` / `#print` | 查类型 / 求值 / 打印定义 | `#check @f`、`#eval e`、`#print f` | 1 §6 | 在 `module` 文件里对未 `meta` 导入的定义 `#eval` 会失败（24 §12 第 5 条） |
| `#guard_msgs` | 把命令发出的消息与文档注释逐字比对 | `#guard_msgs in`、`(substring := true)`、`(whitespace := lax)`、`(error, …)` | 1 §6；10 §2 | 解析错误与文件头的消息捕获不到（1 §6；2 §2；12 §1）；比对时 `error(lean.xxx)` 的错误名不出现 |
| `#print axioms` | 列出声明依赖的公理 | `#print axioms thm` | 3 §8.8；4 §7；25 §5 | `native_decide` 会多出专属公理（25 §5）；机制见第 28 章 |
| `#synth` | 打印实例合成找到的实例 | `#synth Field ℝ` | 8 §2 | — |
| `set_option … in` | 只对下一条命令改选项 | `set_option linter.style.lambdaSyntax true in` | 1 §6、§9；13 §8 | `lake env lean` 不读 `lakefile.toml` 的选项，要加 `-D…`（1 §3） |
| `notation` / `infixl` 等 | 声明记号 | `infixl:65 " ⊞ " => f`、`scoped notation …` | 26 §2、§3 | `infixl`/`infixr`/`infix`/`prefix`/`postfix` 必须写优先级，`notation` 可省（`Lean/Parser/Syntax.lean:91`–`97`）；`scoped` 记号要 `open`（附录 C） |
| `syntax` + `macro_rules`、`macro` | 新语法与展开规则 | `` macro "t" : tactic => `(tactic\| …) `` | 26 §4、§5、§8 | 只写 `syntax` 不写规则，精译时报错（26 §11 第 1 条） |
| `elab` | 定义项、命令、策略的 elaborator（精译器；另译繁饰器） | `elab "k" : tactic => withMainContext do …` | 27 §3、§4 | `closeMainGoal` 不检查类型（27 常见错误 2） |
| `#eval show MetaM Unit from do …` | 在 `MetaM` 里做实验 | 同左 | 27 §2 | 用 `mkAppM` 而不是手写 `mkApp`（27 常见错误 1） |
| `simproc` / `@[positivity]`、`@[norm_num]`、`@[aesop]` | 扩展 `simp` 与驱动策略 | `simproc …`、`@[positivity pat] def …` | 27 §7、§8 | `meta` 声明里不能调用普通函数（27 常见错误 4） |
