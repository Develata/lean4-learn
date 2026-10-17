# 术语表（Glossary）

本书所有章节、文档注释、练习统一使用本表的中文译名。调研依据：`_research/12-gap-8.md`（主）、`_research/07-pedagogy-survey.md` §12–13。适用版本：Lean v4.35.0 / Mathlib v4.35.0。

## 使用规则

1. **一个概念一个译名。** 本表之外不另造译名；「其他译法」列只供读者对照其他中文资料，**正文不得使用**。
2. **首次出现的写法固定为「English（中文）」**，例如 elaborator（精译器）、filter（滤子）：每章第一次在正文或文档注释里提到某术语时用此形式，此后中英文任选，但中文必须是本表译名。
3. **永不翻译**：标识符、引理名、策略名（`simp`、`rw`、`omega`）、选项名、关键字（`Prop`、`Type`、`sorry`、`by`）、文件路径、报错信息；一律用代码字体。策略名之外的相关概念照常翻译（`simp` 的引理称「simp 引理」，该工具称「简化器」）。
4. **另译只进本表。** 仅有两个例外，首次出现时必须带上另译或消歧注：「elaborator（精译器；另译繁饰器）」「filtration（滤流；与滤子 `Filter` 无关）」。
5. **人名定理**：只有通行音译才用中文（马尔可夫、切比雪夫、伯努利、泊松、柯西–施瓦茨、勒贝格、富比尼、伽罗瓦、琴生、拉姆齐、图兰），其余保留拉丁拼写（Chernoff、Hoeffding、Azuma、Doob、Cramér、Sanov、Varadhan、Gärtner–Ellis、Borel–Cantelli、Erdős–Rényi、Szemerédi、Lovász、Fenchel、Esscher）。
6. **撞词**（同一汉字对应不同概念）须在首次遇到它的章节用提示框说明，并按文末「表 D　易混词」区分。数学名词一律用大陆简体通行写法（概率、泊松、期望、随机变量）。
7. **「其他译法」列的缩写与计数。** RM = Lean-zh《Lean 语言参考手册》；TP = 《Lean 4 定理证明》；MP = 《Lean 4 元编程》；FP = 《Lean 函数式编程》；MIL = 《Lean 形式化数学》；WP = 中文维基百科标题；NJU / USTC / PKU = 对应高校的概率或随机过程讲义；OI = OI-wiki；JS = 简书《大偏差原理文献综述》；SCI = 《中国科学》大偏差论文；CASB = 《中国科学院院刊》2012 大偏差文章；力学进展 = 《力学进展》2020 大偏差综述；HDP 讲义 / Zhihu = 高维概率（Vershynin）的中文笔记；Baidu Baike = 百度百科词条；CSDN = CSDN 译文。括号里的数字是调研笔记中的原始子串计数（含噪声，只表优势，不是精确用量）；没有数字就是笔记没有计数。
8. **†** 表示该行没有 Lean-zh 语料计数，译名按通行的大陆数学或计算机用法暂定（调研笔记中为推断或记忆）；若与权威词表（《数学名词》《英汉数学词汇》）冲突，以后者为准并改表。

---

## 表 A　Lean 语言与证明术语

### A.1　基本对象与证明

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| term | 项 | 术语（仅指 terminology，不是此义） | 类型论中的项；与级数的「通项」「第 n 项」区分，元编程里的 `Expr` 称「表达式」。 |
| type | 类型 | — | 与「命题」同属 `Sort`，见「`Sort` / `Prop` / `Type`」行。 |
| proposition | 命题 | — | 住在 `Prop` 中的类型。 |
| proof | 证明 | — | 命题的项（居留元）。 |
| proof term | 证明项 | — | 强调「证明即项」的 Curry–Howard 视角时使用。 |
| theorem / lemma | 定理 / 引理 | — | `theorem`、`lemma` 为关键字不译；本书只在讲「Mathlib 里有这条引理」时用 `lemma`。 |
| goal | 目标 | 目的（MIL 中指 target） | 证明状态中 `⊢` 右侧待证的命题（目标 TP 132, MIL 112）。 |
| hypothesis | 假设 | 前提（TP 8, MP 2, FP 2, MIL 6） | 局部上下文中类型为命题的变量（假设 TP 94, MIL 144）。 |
| (local) context | 上下文 | 语境（MP 54，指 `LocalContext`） | 某个目标之前的全部局部变量与假设。 |
| proof state | 证明状态 | — | 当前所有目标及其上下文（RM 9, TP 5）。 |
| goal state | 证明状态 | 目标状态（语料中未见） | 与「证明状态」同义，infoview 里显示的就是它。 |
| infoview | 信息视图（infoview） | — | † VS Code 中显示证明状态与消息的面板；首次出现保留英文名。 |
| error message | 错误信息 | — | † 引用时原样保留英文原文。 |
| exercise | 练习 | — | † 命名 `ex_<章>_<序号>`，证明体留 `sorry`。 |
| solution | 答案 | 解答 | † 对应 `Solutions/` 目录，与 outline 一致。 |
| docstring | 文档注释 | — | † 指 `/-- … -/`。 |
| module docstring | 模块文档注释 | — | † 指 `/-! … -/`，即本书正文所在位置。 |
| formalization | 形式化 | — | † 把数学陈述与证明写成可被 Lean 检查的代码。 |
| proof assistant / prover | 定理证明器 | 证明器（TP 4）；证明助手（WP） | RM 简介称「交互式定理证明器」。 |

### A.2　策略与证明风格

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| tactic | 策略 | 战术（MIL 1，其余 0）；证明策略 | 策略 RM 58, TP 188, MP 106, FP 76, MIL 170；outline 里的「战术」须改为「策略」。 |
| tactic proof / tactic block | 策略证明 | — | `by` 引入的证明；RM 章名「策略证明」。 |
| term-mode / tactic-mode | 项模式 / 策略模式 | — | † 区分直接写项与用 `by` 写策略，前五章两者并列对照；outline 里的「项式 / 战术式」同改此二词。 |
| tactic combinator | 策略组合子 | — | TP 注释；如 `<;>`、`first`、`try`。 |
| hole | 洞 | — | RM；`?_` 产生的待补部分。 |
| placeholder | 占位符 | 填充 | TP 19；指 `_`，由精译器填入。 |
| `sorry` | `sorry` | — | 不译；称「`sorry` 占位」，只允许出现在练习里。 |
| case analysis | 分情况讨论 | — | MIL 9, TP 10。 |
| by contradiction | 反证法 | — | TP 3, MIL 2。 |
| contrapositive | 逆否命题 | — | † `contrapose` 策略名不译。 |
| induction | 归纳 | — | † 数学归纳与结构归纳的统称。 |
| induction hypothesis | 归纳假设 | — | FP 8, MIL 7。 |
| biconditional (iff) | 双向蕴含 | — | MIL 目录；`↔` 读作「当且仅当」。 |
| classical logic | 经典逻辑 | — | † 允许排中律的逻辑，Mathlib 默认如此。 |
| constructive logic | 构造性逻辑 | — | † 不依赖排中律与选择公理的逻辑。 |
| Curry–Howard correspondence | 柯里–霍华德对应 | — | WP 柯里-霍华德对应。 |
| lambda abstraction | λ 抽象 | — | MIL 对照「抽象」；本书源码一律写 `fun`，不写 `λ`。 |

### A.3　精译、统一与参数

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| elaborator | 精译器 | 繁饰器（TP 4, MP 65）；阐释器（TP 1, MP 1） | 首次出现写「elaborator（精译器；另译繁饰器）」；精译器 RM 28。 |
| elaboration | 精译 | 繁饰（TP 10, MP 164）；阐释（TP 1, MP 1） | 把表面语法补全并检查为内核项的过程（精译 RM 92）；RM 章名「精译与编译」。 |
| kernel (Lean) | 内核 | 核（TP 作 Kernel 的注释，13） | 只指 Lean 的类型检查内核；Mathlib 的 `Kernel` 称「概率核」，绝不单写「核」。 |
| type checker | 类型检查器 | — | RM `TERMINOLOGY.md`。 |
| type inference | 类型推断 | 类型推论（WP）；类型推导 | RM `TERMINOLOGY.md`。 |
| type ascription | 类型标注 | — | † 指 `(e : T)`。 |
| unification | 合一 | 统一（TP 5，多为泛指） | 高阶合一 = higher-order unification（TP 注释）。 |
| metavariable | 元变量 | — | 精译中尚未赋值的占位，显示为 `?m`（MP 143, TP 6）。 |
| implicit argument | 隐式参数 | 隐参数（TP 14） | 隐式参数 RM 4, TP 21, MIL 16；`{x}` 绑定。 |
| explicit argument | 显式参数 | — | † `(x : α)` 绑定。 |
| instance-implicit argument | 实例隐式参数 | — | † `[inst : C α]` 绑定，由实例合成填入。 |
| strict-implicit argument | 严格隐式参数 | — | † `⦃x⦄` 绑定，只在后继显式参数出现时才补全。 |
| auto-bound implicit | 自动绑定隐式参数 | — | † 选项 `autoImplicit`；本书全局关闭，从不依赖。 |
| universe | 宇宙 | — | RM `TERMINOLOGY.md`（宇宙 TP 30）。 |
| universe level | 宇宙层级 | — | 与「层次结构」(hierarchy) 区分。 |
| universe polymorphism | 宇宙多态 | — | `Type*` 的含义：对宇宙层级多态的类型。 |
| `Sort` / `Prop` / `Type` | `Sort` / `Prop` / `Type` | — | 不译；`Prop` 中的居留者称「命题」，`Type u` 中的称「类型」。 |
| impredicative | 非直谓的 | — | `Prop` 的性质，outline 已用。 |
| dependent type | 依值类型 | 依赖类型（TP 6, FP 3） | 依值类型 RM 4, TP 20, FP 21, MP 2；outline 里的「依赖类型」须改。 |
| Pi type / dependent function type | Π 类型（依值函数类型） | — | † `(a : α) → β a`，`∀` 是其特例。 |
| Sigma type / dependent pair | Σ 类型（依值对） | — | † `(a : α) × β a`，`∃` 是其命题版本。 |
| overloading | 重载 | — | FP 章名「重载与类型类」。 |

### A.4　归纳类型、结构与递归

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| inductive type | 归纳类型 | — | 归纳类型 TP 77；`inductive` 声明。 |
| inductive family | 归纳族 | — | TP 7；带下标的归纳类型。 |
| constructor | 构造子 | 构造函数（TP 9, MIL 8） | 构造子 TP 89；不叫「构造函数」以免与 C 语言的概念混淆。 |
| recursor | 递归子 | 递归器（TP 18） | RM `TERMINOLOGY.md`；`T.rec`。 |
| eliminator | 消去子 | — | † 与构造子、递归子成对，泛指消去 `T` 的函数（`casesOn`、`rec`）。 |
| induction principle | 归纳原理 | — | † 由递归子导出的归纳推理规则。 |
| structure (Lean keyword / object) | 结构体 | 结构（FP 1.4 节；泛指义 MIL 227） | 结构体 TP 25, MIL 40；数学上的 structure（如拓扑结构）见表 B「结构」。 |
| field | 字段 | — | † 结构体的成员；数学的「域」(field) 只用于代数，两者不混。 |
| projection | 投影 | — | † 取出字段的函数，如 `p.1`、`Prod.fst`。 |
| anonymous constructor | 匿名构造子 | — | `⟨a, b⟩`（匿名构造子 TP 3, MIL 6）。 |
| class | 类 | — | `class` 声明；其居留者是实例。 |
| `deriving` | 派生 | — | † `deriving` 子句不译，说明时称「派生实例」。 |
| pattern matching | 模式匹配 | — | 模式匹配 TP 39, MIL 12。 |
| match | `match` 表达式 | — | † 关键字不译。 |
| recursion | 递归 | — | 递归 TP 96。 |
| structural recursion | 结构递归 | — | TP 6；MIL 名词表。 |
| well-founded recursion | 良基递归 | — | 良基 TP 23；与「良构的」(well-formed) 不是一回事。 |
| termination | 终止性 | — | † `termination_by`、`decreasing_by` 是其证明接口。 |
| termination measure | 度量 | — | RM `TERMINOLOGY.md`；只在 `termination_by` 语境使用，与测度论的「测度」、度量空间的「度量」不同。 |
| mutual recursion | 互递归 | — | TP 6。 |
| partial function | 偏函数 | — | RM；`partial def` 称「偏函数定义」，数学里的偏函数（`PFun`）同此词。 |
| equation lemma | 等式引理 | — | RM；`f.eq_1` 之类。 |
| subtype | 子类型 | — | MIL 14；`{x // p x}`；集合的子集见表 B。 |
| quotient (type) | 商类型 | 商（MIL 10） | 商类型 RM 10；`Quot`、`Quotient`。 |
| setoid | 广集 | — | TP 注释；指带等价关系的类型。 |
| subsingleton | 子单点类型 | — | † 至多一个居留者的类型；`Subsingleton` 不译。 |
| extensionality | 外延性 | — | MIL 名词表；`funext`、`Set.ext` 是其实例。 |
| propositional extensionality | 命题外延性 | — | RM。 |
| proof irrelevance | 证明无关性 | — | RM；同一命题的任意两个证明定义相等。 |
| decidable | 可判定 | — | TP 20；`Decidable p` 的实例称「可判定性实例」。 |
| computable / noncomputable | 可计算 / 不可计算 | — | MIL 6；`noncomputable` 关键字不译。 |
| axiom | 公理 | — | 本书涉及 `propext`、`Classical.choice`、`Quot.sound`。 |
| trusted computing base | 可信基 | — | † 必须信任的代码与公理集合。 |

### A.5　相等、归约与化简

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| definitional equality | 定义相等 | 定义等价（RM 12, MP 16, TP 1；RM `TERMINOLOGY.md`）；定义上相等 | 本书采用「定义相等」（TP 2, MP 1），与「命题相等」配对；Lean-zh 手册作「定义等价」。 |
| propositional equality | 命题相等 | — | `a = b : Prop` 的居留证明；与「定义相等」配对。 |
| reduction | 规约 | 归约（TP 19, MP 10；RM 2） | RM `TERMINOLOGY.md`，规约 RM 9。 |
| β / δ / η / ι / ζ-reduction | β / δ / η / ι / ζ 规约 | — | † 内核的基本化简步骤；structure eta 称「结构 eta」。 |
| reducibility / transparency | 可约性 / 透明度 | — | † `@[reducible]` 等属性名不译；transparency 的梯级称「透明度梯级」。 |
| whnf (weak head normal form) | 弱头正规形（whnf） | — | † 首次出现写全称；函数 `whnf` 不译。 |
| normal form | 正规形 | 范式；标准形 | † outline 已用「simp 正规形」。 |
| rewriting (`rw`) | 重写 | — | 重写 TP 38, MIL 23；`rw` 不译。 |
| simplifier | 简化器 | 化简（TP 7, MIL 14） | 简化器 RM 10, TP 13；动词用「简化」（TP 34）。 |
| simp lemma | simp 引理 | — | † 带 `@[simp]` 的引理，策略名 `simp` 不译。 |
| simp set | simp 集 | — | † 当前可用的 simp 引理集合，outline 已用。 |
| simp normal form | simp 正规形 | — | † 反复运用 simp 引理后到达的形式，outline 已用。 |
| discharger | 副条件处理器 | — | † simp 用来证明引理副条件的子过程。 |
| congruence | 同余 | — | † `congr` 一族策略的名义；与数论同余无关。 |

### A.6　类型类、实例与强制转换

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| type class | 类型类 | — | 类型类 TP 62, MIL 35；FP 章名「重载与类型类」。 |
| instance | 实例 | 实例化（MIL 13，是 instantiate） | 实例 TP 115, MIL 140；`instance` 关键字不译。 |
| instance resolution / synthesis | 实例合成 | 类型类解析（TP 10）；类型类合成（RM 1） | 实例合成 RM 5；outline 里的「类型类解析」须改。 |
| instance priority | 实例优先级 | — | † 实例冲突时决定顺序。 |
| coercion | 强制转换 | 强制类型转换（FP 30, MIL 1；RM/TP/MP 为 0） | 强制转换合计 154（RM 57, TP 37, MP 3, FP 29, MIL 28）；`↑` 是其显示形式。 |
| cast | 类型转换 | — | † 指 `Nat.cast` 一族及 `norm_cast` 所处理的转换函数，与 C 语言的 cast 无关；沿等式搬运元素的 `cast` 称「沿等式转运」。 |

### A.7　语法、记号与宏

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| notation | 记号 | 记法（RM 41, MIL 26）；符号（TP 用作 Notation 节名） | 记号 MIL 29；`notation`、`infix` 命令不译；RM 章名「记法与宏」，「do notation」同样译「do 记号」。 |
| macro | 宏 | — | 宏 MP 114, RM 48。 |
| syntax | 语法 | — | MP 译者注「Syntax 译为语法」；`syntax` 命令不译。 |
| grammar | 文法 | — | MP 译者注「Grammar 译为文法」。 |
| syntax category | 语法范畴 | — | † `declare_syntax_cat` 声明的类别，如 `term`、`tactic`。 |
| quotation / antiquotation | 引用 / 反引用 | — | † outline 已用；指 `` `(…) `` 与 `$x`。 |
| hygiene | 卫生性 | — | † outline 作「卫生」；宏展开不捕获名字的性质。 |
| attribute | 属性 | — | RM 章名「属性」；`@[simp]` 中的 `simp` 不译。 |
| metaprogramming | 元编程 | — | MP 书名。 |
| expression (`Expr`) | 表达式 | — | 表达式 TP 162, MP 193；元编程里的数据结构，与「项」不同。 |
| pretty printing | 美观打印 | — | MP 章名；`delab` 的任务。 |

### A.8　命名空间、区段与模块

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| namespace | 命名空间 | — | 命名空间 RM 146, TP 57, MIL 42。 |
| section (the Lean command) | 区段 | 小节（TP 15）；节（泛指） | 区段 RM 90；本书自己的章节称「节」，绝不用来指 `section`。 |
| scope | 作用域 | — | RM 59；区段内的称「区段作用域」。 |
| `variable` | `variable` 声明 | — | 命令不译；其绑定的变量称「区段变量」。 |
| `open` | `open`（打开命名空间） | — | 命令不译；`open … in` 称「一次性打开」。 |
| `scoped` | `scoped`（限定作用域） | — | 关键字不译；「限定作用域的记号」指 `scoped notation`。 |
| module | 模块 | — | † 一个 `.lean` 文件，对应 `module` 头。 |
| module system | 模块系统 | — | Lean 4.35 + Mathlib 的 `module` / `public import` 机制。 |
| public / private | 公开 / 私有 | — | † `public section`、`private def` 中的关键字不译。 |
| expose | 暴露 | — | † 指 `@[expose]`，使定义体对其他模块可见。 |
| import | 导入 | — | † `import`、`public import` 命令不译；`public import` 称「公开导入」。 |
| package | 包 | — | † Lake 的包（`lakefile.toml` 所在）。 |
| library | 库 | — | † Lake 的 `lean_lib`，本书有两个：`Lean4Learn` 与 `Solutions`。 |
| target (Lake) | 构建目标 | 目的（MIL 中指 goal 对应处） | † 与证明中的「目标」(goal) 必须区分。 |
| toolchain | 工具链 | — | † 由 `lean-toolchain` 固定，经 elan 管理。 |
| olean | olean 文件 | — | † `.olean` 为编译产物；扩展名保持英文。 |
| linter | 代码检查器 | — | † 与「类型检查器」区分；具体 linter 名不译。 |
| deprecation | 弃用 | — | † `@[deprecated]` 属性及其警告；outline 已用。 |
| naming convention | 命名规范 | — | † 指 Mathlib 的 snake_case / UpperCamelCase 约定。 |

### A.9　函数式编程与数据结构

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| monad | 单子 | — | FP 书名与章名；`Monad` 不译。 |
| functor | 函子 | — | FP / RM 章名。 |
| applicative functor | 应用函子 | — | FP；`Applicative`。 |
| monad transformer | 单子转换器 | — | FP。 |
| do-notation | do 记号 | do 记法（RM 章名「函子、单子与 do 记法」） | 与 notation 同取「记号」。 |
| pure function | 纯函数 | — | † 无副作用，同输入同输出。 |
| `IO` | `IO` | — | 不译；称「`IO` 单子」。 |
| side effect | 副作用 | — | † 读写文件、随机数、打印等。 |
| string slice | 字符串切片 | — | † `String.Slice`，不拷贝的子串视图。 |
| array | 数组 | — | † `Array`，随机访问，与链表式的 `List` 对照。 |
| list | 列表 | — | † `List`；Mathlib 中不要与「有限集」混淆。 |
| option | `Option` 类型 | — | † 表示可能缺失的值，不译为「选项」，以免与 `set_option` 的选项混淆。 |
| option (`set_option`) | 选项 | — | † 指 `set_option` 所设；与 `Option` 类型区分。 |
| hash map | 哈希表 | — | † `Std.HashMap`。 |
| heartbeat | 心跳 | — | † `maxHeartbeats`；精译与策略执行的计算量单位。 |

---

## 表 B　Mathlib 与数学术语（本书涉及的）

### B.1　集合、函数与计数

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| set | 集合 | — | † Mathlib 的 `Set α` 是 `α → Prop`，是「α 中的子集」而不是独立的类型。 |
| subset | 子集 | — | † `⊆`；`⊂` 为真子集。 |
| symmetric difference | 对称差 | — | † `s ∆ t`（需 `open symmDiff`）。 |
| power set | 幂集 | — | † `Set.powerset`、`Finset.powerset`。 |
| image / preimage | 像 / 原像 | 逆像 | † `f '' s`、`f ⁻¹' s`。 |
| injective | 单射 | — | † `Function.Injective`。 |
| surjective | 满射 | — | † `Function.Surjective`。 |
| bijective | 双射 | — | † `Function.Bijective`。 |
| equivalence relation | 等价关系 | — | WP；与「等价对应」(Equiv) 区分。 |
| finset | 有限集 | — | MIL 名词表（finite sets）；`Finset α` 是元素可计算枚举的有限集合（底层为去重的多重集），与命题 `Set.Finite` 不同。 |
| fintype | 有限类型 | — | † `Fintype α`，附带元素枚举的类型。 |
| cardinality | 基数 | 势（WP 势 (数学)） | `Finset.card`、`Fintype.card`、`Nat.card`、`Set.ncard` 都译「基数」，具体含义以类型区分。 |
| big operator | 大算子 | — | † `∑`、`∏` 等对有限族的求和求积记号。 |
| finite sum / product | 有限和 / 有限积 | — | † outline 已用「有限和」。 |
| binomial coefficient | 二项式系数 | 组合数（NJU 9） | WP；`Nat.choose n k`。 |
| factorial | 阶乘 | — | † `n !`（需 `open Nat`）。 |
| inclusion–exclusion principle | 容斥原理 | 排容原理（WP） | †。 |
| pigeonhole principle | 抽屉原理 | 鸽巢原理（WP 鴿巢原理） | † 大陆更常用「抽屉原理」。 |
| double counting | 双重计数 | 算两次（WP） | † 用两种方式数同一个量。 |
| indicator function | 指示函数 | 示性函数（USTC） | `Set.indicator`；随机变量版称「指示随机变量」（NJU）。 |

### B.2　分析：滤子与极限

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| filter | 滤子 | 过滤器（MIL 1） | 滤子 MIL 63；WP「滤子 (数学)」；`List.filter`、`Finset.filter` 的 filter 称「过滤」；Mathlib 的 `Filter` 允许平凡滤子，与 Bourbaki 不同。 |
| non-trivial filter | 非平凡滤子 | — | MIL；`Filter.NeBot`。 |
| filter basis | 滤子基 | — | MIL；`HasBasis`。 |
| principal filter | 主滤子 | — | MIL；`𝓟 s`。 |
| ultrafilter | 超滤子 | — | WP。 |
| push-forward / pull-back (of filters) | 前推 / 拉回 | — | MIL；`Filter.map`、`Filter.comap`。 |
| `atTop` | `atTop`（趋于无穷的滤子） | — | † 名字不译，叙述时称「趋于无穷的滤子」。 |
| neighborhood filter | 邻域滤子 | — | MIL；`𝓝 x`。 |
| neighborhood | 邻域 | — | WP, MIL；图论中的邻点集见表 B.9，不叫邻域。 |
| eventually | 最终成立 | 最终发生的事情（MIL） | MIL；`∀ᶠ x in l, p x`，读作「沿 `l` 最终成立」。 |
| frequently | 经常成立 | 经常发生的事情（MIL） | MIL；`∃ᶠ x in l, p x`。 |
| tends to (`Tendsto`) | 趋于 | 趋向于（MIL） | MIL；`Tendsto f l₁ l₂` 读作「`f` 沿 `l₁` 趋于 `l₂`」。 |
| limit | 极限 | — | † 数列极限（WP）与函数极限的统称；在 Mathlib 中统一表述为 `Tendsto`。 |
| cluster point | 聚点 | — | MIL。 |
| limsup / liminf | 上极限 / 下极限 | — | WP 上极限和下极限；`Filter.limsup`。 |
| supremum / infimum | 上确界 / 下确界 | — | †；`sSup`、`iSup`。 |
| summable | 可和 | — | † `Summable`：无条件收敛的求和族；`tsum` 称「无穷和」。 |
| metric space | 度量空间 | — | MIL；此处的「度量」= 距离函数。 |
| lower / upper semicontinuous | 下半连续 / 上半连续 | — | SCI；`LowerSemicontinuous`。 |
| compact | 紧 | 紧致（MIL） | MIL 两词并用；本书统一用「紧」。 |
| convex function | 凸函数 | — | WP；`ConvexOn`。 |
| concave function | 凹函数 | — | †；`ConcaveOn`。 |
| Jensen's inequality | 琴生不等式 | 詹森不等式；簡森（WP 繁体标题，不用） | 琴生为 †；Mathlib `ConvexOn.map_sum_le`。 |
| Cauchy–Schwarz inequality | 柯西–施瓦茨不等式 | — | WP；内积空间中的版本在 `Mathlib/Analysis/InnerProductSpace/Basic.lean`。 |
| AM–GM inequality | 均值不等式 | 算术–几何平均不等式 | † Mathlib `geom_mean_le_arith_mean`（`Analysis/MeanInequalities.lean`）。 |

### B.3　测度与积分

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| measurable space | 可测空间 | — | MIL, PKU；`MeasurableSpace`。 |
| measurable set | 可测集 | — | MIL, PKU。 |
| measurable function | 可测函数 | — | PKU, WP；`Measurable`。 |
| σ-algebra | σ-代数 | σ-域；σ代数；事件域（PKU） | MIL；亦称 σ-域。 |
| π-system | π 系 | — | PKU。 |
| measure | 测度 | 度量（MIL 43，指 metric 等泛义） | MIL 26；永远不写「度量」，见表 D。 |
| measure space | 测度空间 | — | PKU。 |
| finite / σ-finite measure | 有限测度 / σ-有限测度 | σ 有限测度（PKU） | PKU；`IsFiniteMeasure`、`SigmaFinite`。 |
| outer measure | 外测度 | — | †；Mathlib 的 `Measure` 以外测度为底。 |
| Lebesgue measure | 勒贝格测度 | — | †；`volume`。 |
| Dirac measure | 狄拉克测度 | — | †；`Measure.dirac`。 |
| counting measure | 计数测度 | — | WP；`Measure.count`。 |
| product measure | 积测度 | — | WP；`Measure.prod`、`Measure.pi`。 |
| probability measure | 概率测度 | — | PKU, USTC；`IsProbabilityMeasure`。 |
| probability space | 概率空间 | — | USTC；`MeasureSpace` 加概率测度。 |
| almost everywhere | 几乎处处 | — | MIL；`ae`、`∀ᵐ`。 |
| almost surely | 几乎必然 | — | NJU 12；概率测度下用此词并注明就是 `∀ᵐ ω ∂μ`，一般测度用「几乎处处」。 |
| Lebesgue integral (`lintegral`) | 勒贝格积分 | — | WP；`∫⁻` 是取值于 `ℝ≥0∞` 的非负函数积分。 |
| Bochner integral | Bochner 积分 | — | MIL；`∫ x, f x ∂μ`，对 Banach 空间取值的函数。 |
| integrable | 可积 | — | †；`Integrable`。 |
| Lp space / `MemLp` | Lp 空间 / 属于 Lp | — | WP Lp空间；`MemLp f p μ` 读作「`f` 属于 Lp(μ)」†。 |
| dominated convergence theorem | 控制收敛定理 | — | MIL。 |
| monotone convergence theorem | 单调收敛定理 | — | WP。 |
| Fatou's lemma | Fatou 引理 | 法图引理 | WP 两写法；本书用拉丁。 |
| Fubini's theorem | 富比尼定理 | Fubini 定理 | MIL；通行音译，可用中文。 |
| Radon–Nikodym derivative | Radon–Nikodym 导数 | 拉东–尼科迪姆（WP） | USTC；`rnDeriv`，记 `∂P/∂Q`。 |
| change of variables | 换元公式 | — | MIL。 |
| extended non-negative reals | 扩展非负实数 | — | MIL；`ℝ≥0∞`。 |
| non-negative reals | 非负实数 | — | †；`ℝ≥0`（`NNReal`）。 |

### B.4　概率

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| random variable | 随机变量 | — | 全体来源；Mathlib 中就是 `Ω → E` 的可测函数。 |
| distribution / law | 分布 | 律 | USTC；`HasLaw X P μ` 读作「`X` 在 `μ` 下的分布为 `P`」†；单写「律」易与「分布律」(pmf) 混淆。 |
| expectation | 期望 | 数学期望 | NJU, USTC；`μ[X]`、`𝔼[X]`。 |
| variance | 方差 | — | NJU；`variance`、`Var[X; μ]`。 |
| covariance | 协方差 | — | USTC。 |
| moment / central moment | 矩 / 中心矩 | — | NJU, USTC；`moment`、`centralMoment`。 |
| moment-generating function | 矩母函数 | 矩生成函数（WP, NJU 2）；矩量母函数 | 矩母函数 NJU 2；母函数 = 生成函数的传统叫法；`mgf`。 |
| cumulant-generating function | 累积量母函数 | 对数矩母函数（JS） | `cgf`，即矩母函数取对数；对应 LDP 里的 Λ。 |
| independence | 独立 | — | NJU；`IndepFun`、`iIndepFun`。 |
| pairwise independent | 两两独立 | — | †；`Pairwise (· ⟂ᵢ[μ] ·)`。 |
| mutually independent | 相互独立 | — | †；`iIndepFun` 表示的整族独立。 |
| identically distributed | 同分布 | — | WP；`IdentDistrib`。 |
| i.i.d. | 独立同分布 | — | NJU 11, WP。 |
| conditional expectation | 条件期望 | 条件数学期望 | NJU 10, USTC。 |
| kernel (probability) / Markov kernel | 概率核 / 马尔可夫核 | — | `Kernel` 称概率核，`IsMarkovKernel` 称马尔可夫核；绝不单写「核」。 |
| filtration | 滤流 | σ-代数流（PKU） | USTC；首次出现写「filtration（滤流；与滤子 `Filter` 无关）」。 |
| adapted process | 适应过程 | — | USTC。 |
| stopping time | 停时 | — | NJU 129, USTC, WP；`IsStoppingTime`。 |
| martingale / supermartingale / submartingale | 鞅 / 上鞅 / 下鞅 | — | 《数学名词》镜像；NJU 鞅 208；上鞅 = supermartingale。 |
| optional stopping theorem | 可选停时定理 | 择停定理（USTC）；可选抽样定理（PKU） | NJU；同一定理三个名称，本书选前者。 |
| Doob decomposition / inequality | Doob 分解 / Doob 不等式 | 杜布 | USTC, NJU；保留拉丁。 |
| law of large numbers | 大数定律 | 大数律（NJU 1） | USTC；弱 / 强分别称弱大数定律、强大数定律。 |
| central limit theorem | 中心极限定理 | — | USTC, WP。 |
| Borel–Cantelli lemma | Borel–Cantelli 引理 | 波莱尔–坎泰利 | USTC；保留拉丁。 |
| Bernoulli distribution | 伯努利分布 | — | WP；`Ber(x, y, p)`。 |
| binomial distribution | 二项分布 | — | †；`Bin(n, p)`。 |
| Poisson distribution | 泊松分布 | 卜瓦松（WP 台湾译） | NJU 15；本书不用台湾译名。 |
| Gaussian / normal distribution | 正态分布（高斯分布） | — | WP；`gaussianReal`。 |
| uniform distribution | 均匀分布 | — | WP；`uniformOn`。 |
| total variation distance | 全变差距离 | — | WP。 |
| coupling | 耦合 | — | †。 |
| empirical measure | 经验测度 | — | SCI。 |
| exponential tilting | 指数倾斜 | Esscher 变换 | Mathlib `Measure.tilted`；中文来源较弱，Esscher 变换作别称。 |

### B.5　不等式与概率方法

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| Markov's inequality | 马尔可夫不等式 | — | NJU, WP。 |
| Chebyshev's inequality | 切比雪夫不等式 | — | NJU；`meas_ge_le_variance_div_sq`。 |
| Chernoff bound | Chernoff 界 | — | NJU 36；保留拉丁；Mathlib `measure_ge_le_exp_mul_mgf`。 |
| Hoeffding's inequality / lemma | 霍夫丁不等式 / 引理 | Hoeffding | NJU 6, WP；通行音译，可用中文。 |
| Azuma–Hoeffding inequality | Azuma–Hoeffding 不等式 | 吾妻不等式（WP） | NJU 21；保留拉丁。 |
| Bernstein's inequality | 伯恩斯坦不等式 | 伯恩施坦（WP） | TengJiaye 讲义。 |
| sub-Gaussian | 次高斯 | 亚高斯（CSDN 译文） | 次高斯 Zhihu 高维概率；`HasSubgaussianMGF X c μ` 读作「`X` 具有参数 `c` 的次高斯矩母函数」。 |
| sub-exponential | 次指数 | — | HDP 讲义。 |
| concentration inequality | 集中不等式 | — | WP, Zhihu。 |
| concentration of measure | 测度集中现象 | — | NJU。 |
| tail bound | 尾界 | — | Zhihu 高维概率。 |
| union bound | 联合界 | 布尔不等式（WP） | NJU 保留英文；联合界为 †；`measure_union_le`、`measure_biUnion_finset_le`。 |
| linearity of expectation | 期望的线性性 | — | NJU。 |
| probabilistic method | 概率方法 | 概率法（NJU） | WP；本书用「概率方法」。 |
| first-moment method | 一阶矩方法 | — | NJU。 |
| second-moment method | 二阶矩方法 | — | NJU。 |
| Lovász local lemma | Lovász 局部引理 | — | NJU；保留拉丁。 |

### B.6　随机图与图论

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| random graph | 随机图 | — | †。 |
| binomial random graph G(n,p) | 二项随机图 | Erdős–Rényi 随机图（NJU）；ER 随机图 | Mathlib 取名 `binomialRandom`，文档说明 Erdős–Rényi 之名史实不确，故本书采用「二项随机图」，Erdős–Rényi 作别称。 |
| threshold (function) | 阈值（函数） | — | NJU；阈值现象。 |
| with high probability (w.h.p.) | 以高概率 | — | † 概率趋于 1。 |
| asymptotically almost surely (a.a.s.) | 渐近几乎必然 | 渐进几乎一定（NJU，疑为误写） | NJU；「渐近」是规范写法。 |
| percolation | 渗流 | 逾渗 | 渗流（WP 渗流理论）；Baidu Baike 称「渗流」或「逾渗」。 |
| phase transition | 相变 | — | WP。 |
| giant component | 巨型连通分支 | 巨分支 | † 中文来源仅有非正式的「巨大的分支」，暂定，待核。 |
| random walk | 随机游走 | 随机漫步（WP 台湾译） | NJU。 |
| vertex | 顶点 | 节点（泛指 node） | OI；`V`。 |
| edge | 边 | — | OI；`edgeSet`。 |
| simple graph | 简单图 | — | OI；`SimpleGraph`。 |
| adjacent | 相邻 | 邻接 | OI；`Adj`。 |
| degree | 度 | — | OI；入度 / 出度用于有向图。 |
| neighbor set | 邻点集 | 邻域（OI） | OI；`neighborSet`；邻域一词留给拓扑。 |
| subgraph | 子图 | — | OI；`Subgraph`。 |
| induced subgraph | 导出子图 | 诱导子图（OI） | † 研究笔记未定（OI 作诱导，WP 作导出）；本书取《图论》教材通行的「导出子图」，`induce`。 |
| walk | 途径 | 道路、通道 | OI；`Walk`，顶点可重复的相邻点序列。 |
| trail | 迹 | — | OI；`IsTrail`，边不重复。 |
| path | 路径 | 道路（WP）；链 | OI；`IsPath`，顶点不重复；他书用词可能与「途径」错位，须用上下文校对。 |
| circuit | 回路 | — | OI；`IsCircuit`，闭迹。 |
| cycle | 圈 | — | OI；`IsCycle`。 |
| connected | 连通 | — | OI；`Connected`。 |
| reachable | 可达 | — | †；`Reachable`。 |
| connected component | 连通分量 | — | OI。 |
| tree | 树 | — | OI；`IsTree`。 |
| clique | 团 | — | OI；k-clique 称「k-团」（NJU）；`IsClique`。 |
| independent set | 独立集 | — | OI；`IsIndepSet`。 |
| complete graph | 完全图 | — | OI；`⊤`。 |
| edgeless graph | 空图 | 无边图 | †；`⊥`。 |
| bipartite graph | 二分图 | — | OI。 |
| coloring | 着色 | 图着色（WP） | WP；`Coloring`。 |
| chromatic number | 色数 | — | OI；`chromaticNumber`，取值 `ℕ∞`。 |
| matching | 匹配 | — | OI。 |
| perfect matching | 完美匹配 | — | OI。 |
| isomorphism (of graphs) | 同构 | — | OI；`≃g`。 |
| handshaking lemma | 握手引理 | — | WP；`sum_degrees_eq_twice_card_edges`。 |
| Hall's marriage theorem | 霍尔婚配定理 | — | WP。 |
| Ramsey number | 拉姆齐数 | — | WP。 |
| Turán's theorem | 图兰定理 | — | WP；`Extremal/`。 |
| regularity lemma | 正则性引理 | 塞迈雷迪正则性引理（WP） | WP 作者名；本书写「Szemerédi 正则性引理」。 |
| unordered pair | 无序对 | — | †；`Sym2`，记 `s(a, b)`。 |

### B.7　大偏差

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| large deviations | 大偏差 | 大偏离 | 大偏差 CASB, 力学进展, SCI；非「大偏离」。 |
| large deviation principle (LDP) | 大偏差原理 | — | SCI。 |
| rare event | 稀有事件 | 罕见事件（力学进展） | JS。 |
| rate function | 速率函数 | 率函数（†） | SCI, JS。 |
| good rate function | 好速率函数 | 紧速率函数 | JS, SCI；好 = 水平集紧。 |
| exponentially tight | 指数紧 | — | † 无中文来源，待核。 |
| log moment-generating function | 对数矩母函数 | — | JS；即「累积量母函数」。 |
| Legendre–Fenchel transform | Legendre–Fenchel 变换 | 勒让德变换；凸共轭（WP） | JS, WP；Mathlib 在 v4.35 无此对象。 |
| convex conjugate | 凸共轭 | — | WP。 |
| Cramér's theorem | Cramér 定理 | 克莱默（CASB） | JS；保留拉丁。 |
| Sanov's theorem | Sanov 定理 | 萨诺夫（CASB） | 保留拉丁。 |
| Varadhan's lemma | Varadhan 积分引理 | — | SCI。 |
| contraction principle | 压缩原理 | — | SCI。 |
| Gärtner–Ellis theorem | Gärtner–Ellis 定理 | — | †；保留拉丁。 |
| relative entropy / KL divergence | 相对熵（KL 散度） | — | JS, WP。 |

### B.8　序与代数结构

| English | 本书译名 | 其他译法（见于何处） | 说明 |
|---|---|---|---|
| linear order | 全序 | 线性序 | † Mathlib 的 `LinearOrder`；本书叙述用「全序」。 |
| preorder | 预序 | — | †；`Preorder`。 |
| partial order | 偏序 | — | †；`PartialOrder`。 |
| lattice | 格 | — | MIL 名词表；`Lattice`。 |
| complete lattice | 完备格 | — | MIL。 |
| Galois connection | 伽罗瓦连接 | — | MIL。 |
| lower bound / upper bound | 下界 / 上界 | — | †。 |
| well-founded (order) | 良基 | — | TP 23；与递归同词。 |
| monoid | 幺半群 | — | †；`Monoid`。 |
| group | 群 | — | †；`Group`。 |
| ring | 环 | — | MIL 名词表；`Ring`。 |
| field (algebra) | 域 | — | †；与结构体的「字段」区分。 |
| ordered field | 有序域 | — | † 在 Mathlib 中由 `Field`、`LinearOrder`、`IsStrictOrderedRing` 三个类共同表达。 |
| homomorphism | 同态 | — | †。 |
| morphism | 态射 | — | †。 |
| bundled map | 打包映射 | — | † 数据与性质打包在一个结构体里（`→+*`、`FunLike`）；对立面称「未打包」。 |
| quotient group | 商群 | — | †；`QuotientGroup`。 |
| equivalence (`Equiv`) | 等价对应 | — | † `α ≃ β`，带显式逆的双射；与「等价关系」「逻辑等价」区分。 |
| isomorphism (algebraic) | 同构 | — | †；`≃+*` 等。 |
| structure (mathematical) | 结构 | — | MIL；数学对象（拓扑结构、群结构）；Lean 关键字 `structure` 译「结构体」。 |
| hierarchy | 层次结构 | 层级（MIL 4） | 层次结构 MIL 22；用于代数类型类层次；outline 里的「层级」须改；宇宙层级不受影响。 |
| subobject / `SetLike` | 子结构 | — | † 子群、子环等的统称。 |

---

## 表 C　记号读法

「读法」是口头或行文中的叫法；「含义与出处」中写明所需的 `open` / `open scoped`（见 style.md §5 的记号作用域）。

| 记号 | 读法 | 含义与出处 |
|---|---|---|
| `x ↦ f x`（`fun x ↦ …`） | 「x 映到 f x」 | 匿名函数；本书源码写 `fun x ↦ …`，不写 `λ`。 |
| `⟨a, b⟩` | 「匿名构造子 a，b」 | 匿名构造子，由期望类型决定具体构造子；`h.1`、`h.2` 是其投影。 |
| `↑x` | 「强制转换 x」，或「x 的提升」 | 强制转换的显示形式，如 `((n : ℕ) : ℝ)` 显示为 `↑n`；`⇑`、`↥` 是其特化。 |
| `⇑f` | 「f 的函数形式」 | 把打包映射 `f` 转成函数（`DFunLike.coe`），不读出。 |
| `↥S` | 「S 的底层类型」 | 把集合或子结构 `S` 转成类型（`CoeSort`）。 |
| `∀ᶠ x in l, p x` | 「沿 l 最终，p x 成立」 | `Filter.Eventually`；需 `open Filter`。 |
| `∃ᶠ x in l, p x` | 「沿 l 经常，p x 成立」 | `Filter.Frequently`；需 `open Filter`。 |
| `∀ᵐ x ∂μ, p x` | 「μ 几乎处处，p x 成立」 | `MeasureTheory.ae` 上的最终成立；概率测度下读「几乎必然」；需 `open MeasureTheory`。 |
| `𝓝 x` | 「x 的邻域滤子」 | `nhds x`；需 `open Topology`。 |
| `𝓟 s` | 「s 的主滤子」 | `Filter.principal s`；需 `open Filter`。 |
| `∑ x ∈ s, f x` | 「对 s 中的 x，f x 求和」 | `Finset.sum`；全局可用；`∏` 同理为求积。 |
| `#s` | 「s 的基数」 | `Finset.card s`；需 `open Finset`。 |
| `μ[X]` | 「X 关于 μ 的期望」 | 宏 `μ[X]` 展开为 `∫ x, ↑(X x) ∂μ`；需 `open ProbabilityTheory`，与列表的 `l[i]` 可能冲突。 |
| `𝔼[X]` | 「X 的期望」 | 对 `volume` 的期望，展开为 `∫ a, X a`；需 `open ProbabilityTheory`。 |
| `𝔼 i ∈ s, f i` | 「对 s 取 f 的平均」 | `Finset.expect`；需 `open scoped BigOperators`。 |
| `Var[X; μ]` | 「X 关于 μ 的方差」 | `ProbabilityTheory.variance X μ`；`Var[X]` 取 `volume`；需 `open ProbabilityTheory`。 |
| `∫ x, f x ∂μ` | 「f 关于 μ 的积分」 | Bochner 积分；需 `open MeasureTheory`。 |
| `∫⁻ x, f x ∂μ` | 「f 关于 μ 的勒贝格积分」 | `lintegral`，取值于 `ℝ≥0∞`；需 `open MeasureTheory`。 |
| `X ⟂ᵢ[μ] Y` | 「X 与 Y 在 μ 下独立」 | `IndepFun X Y μ`；需 `open ProbabilityTheory`。 |
| `f =ᵐ[μ] g` | 「f 与 g 在 μ 下几乎处处相等」 | `Filter.EventuallyEq (ae μ) f g`；概率测度下读「几乎必然相等」。 |
| `f ≤ᵐ[μ] g` | 「f 在 μ 下几乎处处小于等于 g」 | 同上，`≤` 版本。 |
| `f ∘ g` | 「f 复合 g」 | 先 `g` 后 `f`。 |
| `sᶜ` | 「s 的补集」 | `Set.compl`，也适用于有限集（Boolean 代数）。 |
| `s ∆ t` | 「s 与 t 的对称差」 | `symmDiff`；需 `open symmDiff`（scoped）。 |
| `a ⊓ b` / `a ⊔ b` | 「a 与 b 的下确界 / 上确界（交 / 并）」 | 格运算；集合上就是 `∩` / `∪`。 |
| `⨆ i, f i` / `⨅ i, f i` | 「f i 的上确界 / 下确界」 | `iSup` / `iInf`；`⨆ i ∈ s` 等是带条件的形式。 |
| `ℝ≥0` | 「非负实数」 | `NNReal`；需 `open scoped NNReal`。 |
| `ℝ≥0∞` | 「扩展非负实数」 | `ENNReal`，即 `[0, ∞]`；需 `open scoped ENNReal`。 |
| `∞` | 「无穷（大）」 | 在 `ℝ≥0∞` 中是 `⊤`，在 `ℝ` 中不存在；需 `open scoped ENNReal`。 |
| `G(V, p)` | 「顶点集 V、边概率 p 的二项随机图」 | `SimpleGraph.binomialRandom V p`，`SimpleGraph V` 上的测度；需 `open SimpleGraph`。 |
| `Ber(x, y, p)` | 「以 p 取 x、以 1−p 取 y 的伯努利分布」 | `bernoulliMeasure x y p`，其中 `p : unitInterval`；需 `open ProbabilityTheory`。 |
| `Bin(n, p)` | 「参数 n、p 的二项分布」 | `ProbabilityTheory.binomial n p`，`ℕ` 上的测度；需 `open ProbabilityTheory`。 |
| `s(a, b)` | 「无序对 a，b」 | `Sym2.mk a b`；`s(a, b) = s(b, a)`；全局可用。 |
| `G →g H` | 「G 到 H 的图同态」 | `SimpleGraph.Hom`。 |
| `α ≃ β` | 「α 与 β 之间的等价对应」 | `Equiv`；此处不是逻辑等价。 |
| `G ≃g H` | 「G 与 H 同构」 | `SimpleGraph.Iso`。 |
| `⊢` | 「推出」，或读作「目标是」 | infoview 中分隔上下文与目标，不是输入的记号。 |
| `?_` | 「新目标」 | `refine`、`apply`、`calc` 中产生新目标的洞。 |
| `·`（项首） | 「聚焦到第一个目标」 | 策略块的聚焦项，对目标逐一处理。 |
| `<;>` | 「对每个新目标运行」 | `t₁ <;> t₂`：运行 `t₁` 后对产生的每个目标运行 `t₂`。 |
| `∎` | 「证毕」 | 排版用的证毕符号，**不是** Lean 或 Mathlib 记号；代码里不要写。 |

---

## 表 D　易混词

| 汉字 | 区分 | 本书写法 |
|---|---|---|
| 测度 / 度量 | `Measure`（测度论） / `termination_by` 的度量 / `Metric` 的距离 | 测度；「终止度量」；度量空间 |
| 滤子 / 过滤 / 滤流 | `Filter` / `List.filter`、`Finset.filter` / `Filtration` | 滤子；过滤；滤流（首次写明与滤子无关） |
| 内核 / 概率核 | Lean 的 `Kernel` / `ProbabilityTheory.Kernel` | 内核；概率核或马尔可夫核（绝不单写「核」） |
| 项 / 通项 | Lean 的 `Term` / 级数的第 n 项 | 项；通项、第 n 项 |
| 途径 / 路径 | `Walk` / `IsPath` | 途径；路径；他书用词可能互换，须看定义 |
| 目标 / 构建目标 | 证明的 goal / Lake 的 target | 目标；构建目标 |
| 域 / 字段 | 代数的 field / 结构体的 field | 域；字段 |
| 结构 / 结构体 | 数学上的 structure / Lean 的 `structure` | 结构；结构体 |
| 选项 / `Option` | `set_option` 的选项 / `Option` 类型 | 选项；`Option` 类型 |
| 节 / 区段 | 本书的章节 / Lean 的 `section` | 节；区段 |
| 等价 / 等价对应 | 逻辑或关系的等价 / `Equiv` | 等价关系、逻辑等价；等价对应 |
| 记号 / 符号 | notation / symbol | 记号；符号 |
