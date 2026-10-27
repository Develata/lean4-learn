# 附录 F　延伸阅读

本附录把全书各章「延伸阅读」里反复出现的外部资料收在一处：Lean 官方文档与教材、查找与提问的渠道、Lean-zh
社区的中文译本，以及第 III、IV 部分引用的数学文献。本书锁定 Lean `v4.35.0` + Mathlib `v4.35.0`
（commit `56a0058`）；下面多数网站跟随最新版本，内容可能领先于锁定版本，也可能（中文译本）落后于它。
遇到名字或行为不一致时，以本地源码 `.lake/packages/mathlib/` 和 `#check` 为准（第 9 章）。

每个网址都在 2026-10-27 打开核对过；括号里记下当天页面声明的版本。打不开的条目不给网址，只给书目信息，
并注明「未核对」。

## 1. 官方文档与教材

| 资源 | 内容 | 当天页面声明的版本 | 配合本书 |
|---|---|---|---|
| *Theorem Proving in Lean 4*（Avigad、de Moura、Kong、Ullrich）<br><https://lean-lang.org/theorem_proving_in_lean4/> | 依值类型论、命题与证明、策略、归纳类型、结构体、类型类、公理 | Lean 4.33.0 | 第 1 章引用；内容对应第 3–6 章 |
| *Functional Programming in Lean*（Christiansen）<br><https://lean-lang.org/functional_programming_in_lean/> | 把 Lean 当编程语言：类型类、单子、单子变换器、依值类型编程 | 代码示例用 4.33.0 测试 | 第 24、25 章引用 |
| *Mathematics in Lean*（Avigad、Massot）<br><https://leanprover-community.github.io/mathematics_in_lean/> | Mathlib 风格的数学形式化：逻辑、集合与函数、数论、结构体、层次结构、拓扑、积分与测度论 | 标题标注 v4.19.0 | 第 1、2、4、7、11、14、15、16 章引用其相应章节 |
| *The Lean Language Reference*<br><https://lean-lang.org/doc/reference/4.35.0/> | 语言参考手册；第 5 章模块系统，第 14 章策略证明，第 15 章简化器，第 25 章 Lake 与 elan | 4.35.0（版本固定页） | 全书；第 1、5、8、28 章直接引用 |
| *Metaprogramming in Lean 4*<br><https://leanprover-community.github.io/lean4-metaprogramming-book/> | `Expr`、`MetaM`、语法与宏、精译、策略编写 | 首页未写版本 | 第 26、27 章引用（第 26 章记了与 v4.35.0 对应的仓库提交） |
| Lean 社区学习资源列表<br><https://leanprover-community.github.io/learn.html> | 游戏（NNG 等）、书目、元编程、类型论基础的链接汇总 | — | 全书 |

参考手册一定要用带版本号的网址：`latest` 指向更新的版本，章节编号会变（第 1 章延伸阅读）。

## 2. 查找引理与提问

| 资源 | 用途 | 注意 | 配合本书 |
|---|---|---|---|
| Mathlib 文档站<br><https://leanprover-community.github.io/mathlib4_docs/> | 按模块浏览声明、文档注释与源码链接 | 当天首页写「built using Lean 4 4.36.0-rc1」，已领先于锁定版本 | 第 9 章 |
| Loogle<br><https://loogle.lean-lang.org/> | 按常量、名字片段、子表达式模式、结论形状 `⊢ …` 搜索 | 当天服务的 Mathlib 版本是 `8000f01`，不是本书的 `56a0058` | 第 9 章 |
| LeanSearch<br><https://leansearch.net/> | 用自然语言描述搜索 Mathlib 定理（北京大学 BICMR AI4M 团队） | 页面声明会收集搜索词与反馈 | 第 9 章 |
| Undergraduate mathematics in mathlib<br><https://leanprover-community.github.io/undergrad.html> | 本科数学主题与 Mathlib 声明名的对照表 | 跟随 Mathlib master | 第 9 章起 |
| Lean Zulip<br><https://leanprover.zulipchat.com/> | 社区讨论区；新手从 `new members` 频道开始 | 当天首页标题为「Public view of Lean」 | 第 1 章第 11 节，第 23 章 |
| 最小可复现例子（MWE）说明<br><https://leanprover-community.github.io/mwe.html> | 提问前怎样缩小问题、怎样写 MWE | — | 第 1 章第 11 节 |
| 社区准则<br><https://leanprover-community.github.io/community_guidelines.html> | Zulip 与 GitHub 上的行为准则 | 明确要求不要用大模型写 Zulip 或 GitHub 评论 | 第 1、23 章 |

Lean 里的 `#loogle`、`#leansearch` 命令会把查询发到上面的外部服务，需要联网，且结果同样来自较新的 Mathlib
（调研笔记 `_research/10-tooling-ecosystem-windows.md` §2.1、§2.4；第 9 章）。

## 3. 中文译本（Lean-zh）

Lean-zh（<https://www.leanprover.cn/>，GitHub 组织 <https://github.com/Lean-zh>）是自发组成的中文社区，
翻译了几本官方教材。声明了版本的三种（参考手册 4.34.0-rc1、定理证明 4.26.0、函数式编程 4.23.0）都落后于
本书的锁定版本，后来加入的特性（模块系统与 `public import`、`grind`、
`vcgen` 等）在译本里可能没有或不完整。本书术语以 `docs/glossary.md` 为准，表中的缩写 RM / TP / MP / FP / MIL
就是术语表「其他译法」列的缩写；同一个概念译本可能用了别的词（例如 elaborator，参考手册译本作「精译器」，
定理证明与元编程译本作「繁饰器」）。

| 译本 | 原书 | 当天页面声明的版本 | 网址 |
|---|---|---|---|
| 《Lean 语言参考手册》（RM） | *The Lean Language Reference* | 「本手册涵盖 Lean `4.34.0-rc1` 版本」；共 24 章 | <https://www.leanprover.cn/reference-manual/latest/> |
| 《Lean 4 定理证明》（TP） | *Theorem Proving in Lean 4* | 「本书假定你使用 Lean 4 `4.26.0`」 | <https://www.leanprover.cn/tp-lean-zh/> |
| 《Lean 函数式编程》（FP） | *Functional Programming in Lean* | 「所有代码示例都使用 Lean 版本 `4.23.0` 进行测试」 | <https://www.leanprover.cn/fp-lean-zh/> |
| 《Lean 4 元编程》（MP） | *Metaprogramming in Lean 4* | 首页未写版本 | <https://www.leanprover.cn/mp-lean-zh/> |
| 《Lean 形式化数学》（MIL） | *Mathematics in Lean* | 首页标题「Mathematics in Lean 0.1 documentation」，未写 Lean 版本；13 章与英文版一致 | <https://www.leanprover.cn/math-in-lean-zh/> |
| 《Lean 4 类型检查》 | *Type Checking in Lean 4*（据 Lean-zh 首页；译本首页本身未注明原书） | 未写版本 | <https://www.leanprover.cn/type-checking-in-lean-zh/> |
| 《逻辑验证漫游指南 2026 版》 | *The Hitchhiker's Guide to Logical Verification*（Logical Verification 2026 课程材料） | 2026 版，GitHub 仓库，含 PDF | <https://github.com/Lean-zh/LoVe-zh> |

**参考手册译本的章号与 4.35.0 英文版不同。** 译本 24 章，没有 4.35.0 英文版的第 17 章 *The `vcgen` tactic* 与
第 26 章 *Linters and Code Quality*，所以从第 17 章起章号错开一位：英文版第 25 章 *Build Tools and Distribution*
在译本里是第 24 章。本书引用的章号一律指英文 4.35.0 版。

## 4. 数学文献

格式：作者，题名，出版信息。后面写它补充本书哪些章，以及原章节给出的定位与核对状态。各章自己带的
「未核对」标记原样保留。

**随机图与概率方法**

1. P. Erdős, *Some remarks on the theory of graphs*, Bull. Amer. Math. Soc. 53 (1947)。补充第 19 章（拉姆齐数的
   概率下界的原始文献）。页码与网址未核对：AMS 期刊页面拒绝访问（HTTP 403）。
2. P. Erdős, A. Rényi, *On random graphs. I*, Publicationes Mathematicae Debrecen 6 (1959), no. 3–4, 290–297,
   DOI 10.5486/PMD.1959.6.3-4.12（<https://publi.math.unideb.hu/paper/2769>）。补充第 20 章。书目信息已按期刊
   页面核对。
3. N. Alon, J. H. Spencer, *The Probabilistic Method*, Wiley（出版社页面当前为第 4 版，2016；
   <https://www.wiley.com/en-us/The+Probabilistic+Method%2C+4th+Edition-p-9781119061953>）。补充第 19 章
   （第 1 章「基本方法」，含 `R(k, k) > ⌊2^{k/2}⌋`，`k ≥ 3`）与第 20 章（*The Second Moment* 与 *Random Graphs*
   两章，按章名引用）。本书两章都没有指明版次；出版社页面未列目录，章号与章名未核对。
4. S. Janson, T. Łuczak, A. Ruciński, *Random Graphs*, Wiley, 2000（Wiley Series in Discrete Mathematics and
   Optimization；<https://www.wiley.com/en-us/Random+Graphs-p-9780471175414>）。补充第 20 章（*Small Subgraphs*
   一章，第 20 章原注「按章名引用，没有给章号」）。

**集中不等式**

5. R. Vershynin, *High-Dimensional Probability*, Cambridge University Press, 2018。补充第 21 章（第 2 章：次高斯
   变量与 Hoeffding 不等式；第 21 章原注「章号凭记忆，未逐条核对」）。作者主页
   （<https://webapps.math.uci.edu/~rvershyn/papers/HDP-book/HDP-book.html>）当天显示第 2 版已于 2026-02-19 出版并
   提供免费 PDF，第 1 版 PDF 标为过时；第 2 版的章号是否与上面一致，未核对。
6. S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of Independence*,
   Oxford University Press, 2013（<https://academic.oup.com/book/26549>）。补充第 21 章。出版社目录核对了第 2 章
   题为 *Basic Inequalities*；第 21 章说它讲 Chernoff 方法，这一点未核对（原注「章号凭记忆，未逐条核对」）。

**大偏差**

7. A. Dembo, O. Zeitouni, *Large Deviations Techniques and Applications*, Springer。补充第 22 章（Cramér 定理一节
   与 LDP 定义一节；第 22 章原注「节号和定理编号凭记忆，本书未核对，使用前请对照原书」）。版次与丛书信息
   未核对：出版社页面要求登录，未能打开。
8. F. den Hollander, *Large Deviations*。补充第 22 章（第 I 章；原注「章节号未核对」）。出版信息未核对：检索
   结果显示为 American Mathematical Society 的 Fields Institute Monographs 丛书，2000 年，但 AMS 页面拒绝访问
   （HTTP 403），未能打开出版社页面。

**相关的 Mathlib 内部文档**（随本地源码，无须联网）：`Mathlib/Probability/Combinatorics/README.md` 与
`Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean` 的文件头（第 20 章），
`Mathlib/Probability/Moments/SubGaussian.lean` 的文件头（第 21 章）。
