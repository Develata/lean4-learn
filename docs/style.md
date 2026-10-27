# Authoring guide (for chapter authors, human or agent)

This file is the contract every chapter of the book must satisfy. It exists so that 27 chapters written at different times read as one book and all compile against the pinned toolchain.

## 0. Pins and build

- Lean `leanprover/lean4:v4.35.0`, Mathlib tag `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`). Never run `lake update`; never edit `lean-toolchain`, `lakefile.toml` requirements or `lake-manifest.json`.
- Local Mathlib source (the primary source for every API claim): `.lake/packages/mathlib/Mathlib/`. Use `rg` there before naming any lemma.
- Compile a single file with `lake env lean <path>` (narrow imports ≈ 2–7 min on this machine; `import Mathlib` ≈ 20 min and is forbidden). Compile at most one or two files at a time.
- The whole book builds with `lake build` (both libraries `Lean4Learn` and `Solutions`).

## 1. Files and layout

```
Lean4Learn/Part1/Ch01_Setup.lean        -- chapter text + examples + exercises (sorry only per §5)
Solutions/Part1/Ch01_Setup.lean         -- the same exercise statements, fully proved (no sorry)
Lean4Learn.lean, Solutions.lean         -- aggregators: one `public import` line per file
docs/outline.md                         -- the table of contents and per-chapter spec (Chinese)
docs/glossary.md                        -- term translations; use these words, no others
```

Module names: `Lean4Learn.Part1.Ch01_Setup`, `Solutions.Part1.Ch01_Setup`. Chapter numbers are two digits.

## 2. File header (identical in every file)

```lean
module

public import Mathlib.Data.Nat.Basic      -- narrow imports only; one per line; sorted
public import Mathlib.Tactic.Linarith

/-!
# 第 N 章　标题

一段话说明本章目标，以及读者学完后能做什么。

## 学习目标
- …
-/

@[expose] public section

namespace Lean4Learn.Ch01

-- content

end Lean4Learn.Ch01

end
```

- `module` / `public import` / `@[expose] public section … end` is the Mathlib v4.35.0 majority convention (4933 of 8624 files; Mathlib sets `requiresModuleSystem`, so a plain `import` file still builds but Lake warns). In a `module` file declarations are private by default, `public section` makes names visible to importers, and `@[expose]` additionally lets importers unfold `def`s (`simp [f]`, `unfold f`, `rfl`); theorem proofs are never exposed. Chapter 1 explains each line in plain words; chapter 28 gives the mechanism.
- Metaprogramming chapters (26–27) and any file that defines `macro`/`elab`/`syntax`/attribute-based metaprograms use the Mathlib tactic-file header instead: `module` / `public meta import Lean…` (narrow modules such as `Lean.Elab.Tactic.Basic`) / `public import Mathlib…` / `public meta section`. Helper functions called from a macro or elab body must be `meta def`; attribute-form metaprograms (`@[macro]`, `@[tactic]`, `@[simproc]`, `@[app_delab]`…) must be `meta` and public. Put ordinary `example`/`theorem` uses of the new tactic in a separate `public section` after `end`ing the meta section if needed. See `_research/12-gap-6.md` §2 and `Mathlib/Tactic/Use.lean`, `Mathlib/Tactic/ByContra.lean`.
- Every chapter lives in its own namespace `Lean4Learn.ChNN` (solutions: `Solutions.ChNN`) so names never clash across chapters and never shadow Mathlib names.
- `autoImplicit` is `false` project-wide: every variable must be bound. Explain this once (chapter 1/2) and never rely on auto-bound implicits.
- Imports: choose the narrowest Mathlib modules that provide what the chapter uses. Candidates come from `rg` in local Mathlib. Never `import Mathlib`, never `import Mathlib.Tactic` unless the chapter is about the tactic catalogue (chapter 9) — prefer `Mathlib.Tactic.Common` plus specific tactic modules.

## 3. Language

- Prose (everything inside `/-! … -/` and `/-- … -/`) is Chinese. Technical terms may stay in English, and the first occurrence of a term in a chapter uses the form fixed in `docs/glossary.md`, e.g. 「elaborator（精译器；另译繁饰器）」 — follow the glossary exactly.
- Identifiers, lemma names, tactic names, option names, file paths, error messages: English, verbatim, in backticks.
- Line comments (`--`) may be English or short Chinese. Comments that show the goal state use the exact infoview rendering, e.g. `-- ⊢ n + 0 = n`.
- Math may be bilingual; notation follows Mathlib's rendering (`∑ i ∈ s, f i`, `μ.real s`, `∀ᵐ ω ∂μ`).
- Tone: direct, concrete, no filler. Conclusion first, then reasons.

## 4. Chapter structure (in this order)

1. Module docstring: title, one-paragraph goal, 「学习目标」 bullet list, 「前置知识」 (chapters assumed).
2. Sections `/-! ## 1. … -/` …: each introduces one idea with a runnable example *immediately* after the explanation. Keep sections short (≈ 40–120 lines each).
3. 「常见错误」 section: at least three real mistakes shown with their real error messages, captured with `#guard_msgs`:
   ```lean
   /--
   error: Unknown identifier `Nat.add_com`
   -/
   #guard_msgs in
   example (a b : ℕ) : a + b = b + a := Nat.add_com a b
   ```
   Workflow: write `#guard_msgs in` with an empty docstring, compile, and copy the generated message from the `#guard_msgs` mismatch report (it prints the actual text). `#guard_msgs` text omits the CLI's error code (`error(lean.unknownIdentifier):` in the terminal is just `error:` here) and normalizes whitespace. Never type an error message from memory.
4. 「练习」 section: 8–15 exercises, each with a docstring `/-- 练习 N.k（★）：…description… -/`, named `ex_N_k`, body `:= by sorry` (or `:= sorry` for terms). Difficulty ★ (direct application), ★★ (combines two ideas), ★★★ (needs a search or a new idea). At least one third revisits earlier chapters (chapter 1 is exempt: it has no earlier chapters).
5. 「小结」: a cheat-sheet table (concept → syntax → when to use).
6. 「延伸阅读」: 3–6 pointers with locators (reference manual section names/URLs, Mathlib file paths, book chapter names). No bare "see the docs".

Target length: 300–700 lines per chapter file. Capstone chapters (19–21) may reach 900.

## 5. Correctness rules (non-negotiable)

- **Every behavioural claim is demonstrated in the same file.** "`simp` closes this", "this lemma is called `X`", "`omega` fails here", "`rw` cannot rewrite under binders" — each must have a compiled example (or `#guard_msgs` failure) right there. No example, no claim.
- **`sorry` is allowed in exactly two places.** (a) The exercise statements `ex_N_k` (their `declaration uses 'sorry'` warning is the only warning a chapter file may emit). (b) An anonymous `example` placed directly under a `#guard_msgs in` that captures the resulting message, e.g. to show the `sorry` warning itself or an error in a signature. **Never in a named declaration** (`theorem`, `lemma`, `def`, `instance`, `abbrev`, …) outside the exercises: not under `#guard_msgs`, not `private`, because `#guard_msgs` only checks messages and does not undo the declaration, so a named `sorry` would export a possibly false theorem to every importer (e.g. an `autoImplicit` demo `theorem t (n : ℕ) : n + 0 = m := sorry` is the statement `∀ {m n}, n + 0 = m`). Demos that need a hole use an `example` (nothing is exported); a proof skeleton with `sorry` holes is shown in a code block in the prose, next to a compiled version (fully proved, or with `?_` placeholders that become goals). Worked examples are otherwise fully proved. Solutions files contain zero `sorry`/`admit`.
- **No warnings** other than `declaration uses 'sorry'` on exercises. Gate: `lake build Solutions --wfail` must pass; `lake build Lean4Learn` output may contain only sorry warnings. In particular: no deprecation warnings (use `push Not` not `push_neg`; `Set.mem_ofPred_eq` not `Set.mem_setOf_eq`; `integral_finsetSum` not `integral_finset_sum`; `Mathlib.Basic.Real.Basic` not `Mathlib.Data.Real.Basic`; `uniformOn`/`Ber`/`Bin` not `PMF.*`; `if_pos` → `ite_eq_left`…), no unused-variable warnings, no `linter.unusedSimpArgs`, no `constructor` ambiguity warning (use `left`/`right`), no legacy `rwa … at h₁ h₂`.
- **Lean 4 only**: `fun x ↦`, `rcases/obtain/rintro` patterns, `?_` placeholders, `·` bullets, `calc` with uniform indentation, `simp +arith` config syntax, `decide +kernel`, `induction n with | zero => … | succ n ih => …` producing `0`/`n + 1`. Never `λ`, `begin…end`, `cases h with a b`, `refine ⟨_, _⟩` with `_` for goals, `library_search`, `dec_trivial`, `simp_arith`, `decide!`, `polyrith`, `native_decide` (except in the chapter that explains why Mathlib bans it, guarded with `#guard_msgs` or clearly marked).
- **One idiom per concept** across the book: strong induction is `induction n using Nat.strong_induction_on with | _ n ih => …` (mention `Nat.strongRecOn` once); `Finset` induction is `induction s using Finset.induction_on with | empty => … | insert a s ha ih => …` (verify case names by compiling); negation pushing is `push Not`; big sums are `∑ i ∈ s, f i`; set-builder lemmas are `Set.mem_ofPred_eq` / `*_setOfPred`; real division facts are `div_le_iff₀` and friends; `field_simp` then `ring`, or `field`.
- **Exercise mirror**: each `ex_N_k` statement in `Solutions/` is character-identical to the chapter's (same docstring, same binders, same type) up to the proof. A script checks this before commit.
- **Style**: lines ≤ 100 characters; two-space indentation; `by` at line end for multi-line tactic blocks; `theorem` for Props, `def` for data, `lemma` only when teaching that Mathlib has it; explicit types on top-level definitions; `Type*` for universe-polymorphic types; `open … in` for one-off openings; `open scoped` for notation-only scopes.
- **Notation scopes** (verified at this pin; "needs `open N`" means `open N` or `open scoped N`, both activate scoped notation): `∑/∏` are global; `#s` needs `open Finset` (scoped); `𝔼 i ∈ s, f i` needs `open scoped BigOperators`; `μ[X]`, `Var[X; μ]`, `Ber(…)`, `Bin(…)`, `⟂ᵢ[μ]` need `open ProbabilityTheory`; `∫`, `∀ᵐ`, `∀ᶠ` are global `notation3` (no `open` needed), while the *names* `volume`, `ae`, `Measure` need `open MeasureTheory` and `atTop`, `Tendsto` need `open Filter` (or full names); `𝓝` needs `open Topology`; `G(V, p)` needs `open SimpleGraph`; `I`/`σ` for `unitInterval` need `open unitInterval`; `n !` needs `open Nat`; `π` needs `open Real`.

## 6. Pedagogy rules

- Introduce theory just in time and only once; later chapters cite the chapter that introduced it (「见第 3 章」).
- Show the infoview state in comments at each nontrivial step of the first few worked examples in a section; stop doing so once the pattern is clear.
- Term-mode and tactic-mode versions side by side whenever a construct is first met (chapters 2–5).
- From chapter 8 on, use real Mathlib objects (`ℝ`, `Finset`, `Measure`, `SimpleGraph`), real lemma names, and show how the name was found (`exact?`, naming convention, Loogle).
- `lemma` and `Type*` are Mathlib, not core; `ring`, `linarith`, `norm_num`, `positivity`, `field_simp` need their own `Mathlib.Tactic.X` imports (not in `Mathlib.Tactic.Common`); `bv_decide` needs `Std.Tactic.BVDecide`; `#loogle`/`#leansearch` need network.
- Name the 2024–2026 churn explicitly where the reader will meet old material: say what the old name/tactic was and what replaced it, with the `since` date from the deprecation attribute.
- Exercises never require a lemma whose name the reader has not been shown or cannot find by the methods taught so far (chapter 8 onwards may require a search).

## 7. Workflow for an author

1. Read `docs/outline.md` (your chapter's row and its dependencies) and `docs/glossary.md`.
2. Draft the file. Verify every lemma name with `rg` in local Mathlib *before* using it.
3. `lake env lean Lean4Learn/PartN/ChNN_X.lean`; fix until the only warnings are the exercise sorries. Then write `Solutions/PartN/ChNN_X.lean` and compile it to zero warnings.
4. Add both modules to `Lean4Learn.lean` / `Solutions.lean`.
5. Report: compile commands run, exit codes, remaining warnings (quote them), exercise count, line count, any claim you could not verify.
