# Project Status

Last updated: April 20, 2026

## Discrete Case — Submission-Ready

**Paper:** `discrete/online_full_behavior.tex` (LNCS, full-behavior formulation)

Earlier drafts `discrete/discrete_case_clean_proof_v8.tex` and
`discrete/online tex` are retained for reference; the submission file is
`online_full_behavior.tex`, whose main theorem bounds the *full behavior
language* `B_k(𝔄) = ⋃_{(T,r): width(T) ≤ k} L(𝔄, T, r)` — every
action sequence the agent can produce consistently with its beliefs —
rather than a single decomposition's language.

**Lean 4 formalization:** `discrete/AsymptoticBB/`

| File | Role |
|------|------|
| `Axioms.lean` | Cited theorems (Grohe, Engelfriet) and MCFL closure axioms (`mcfg_homomorphic_image`, `mcfg_finite_union`, `finite_language_is_mcfl`) |
| `Bridge.lean` | Bridge theorem: bounded treewidth ⟹ per-decomposition behavior language is `(k+1)`-MCFL |
| `Main.lean` | `full_behavior_bound` / `main_theorem_full` (paper `thm:full-bound`, `thm:main`); `main_theorem_finite_subclass` (paper `thm:main-finite`); legacy `main_theorem` retained |
| `Basic/`, `Agent/`, `Grammars/`, `TreeDecomposition/` | Supporting definitions and lemmas |

**Axioms (external declarations in the Lean trust base):**
- `FPT_ne_W1` — the parameterized-complexity hypothesis.
- `thm_grohe` — Grohe 2007: tractable CSP on bounded-arity core class ⟹ bounded treewidth.
- `IsTreeCompatibleOrdering`, `isTreeCompatibleOrdering_spec`, `isTreeCompatibleOrdering_nonempty` — the tree-compatible-ordering predicate of the Engelfriet construction and its basic coherence + nonemptiness.
- `engelfriet_tw_to_mcfl` — Engelfriet 1997 / Habel 1992: width-≤k tree decomposition ⟹ `(k+1)`-MCFG generating exactly the tree-compatible orderings.
- `mcfg_homomorphic_image`, `mcfg_finite_union` — standard MCFL closure under homomorphic image and finite union (Seki et al. 1991).
- `finite_language_is_mcfl` — finite languages are `d`-MCFL for every `d ≥ 1` (Seki et al. 1991, Thm 3.9 + dimension monotonicity).

**Proof chain for `thm:main` / `thm:full-bound` (full behavior):**
1. `FPT ≠ W[1]` + RE class + uniform tractable revision + bounded arity ⟹ bounded treewidth of cores (`class_tractable_implies_bounded_tw` via Grohe).
2. Standing core convention (WLOG) collapses core treewidth to original treewidth.
3. For finite `V` and finite domains, every word in `B_k(𝔄)` is the flattened projection of a `Nodup` permutation of `V` under a total assignment `β`; the joint space is finite via `fintypeNodupList`, so `B_k(𝔄)` is finite.
4. Finite-language MCFL closure (`finite_language_is_mcfl`) at dimension `k+1` gives `IsMCFL (B_k(𝔄)) (k+1)`.

**Proof chain for `thm:main-finite` (finite sub-class, legacy path):**
Uses `bridge_theorem` + `mcfg_finite_union` over `F`; does not depend on `finite_language_is_mcfl`.

**Build status:** `lake build` is green; no `sorry` in the load-bearing chain.

## Continuous Case — Work in Progress

**Paper:** `continuous/submission_final_v7.tex` (compiled PDF included)

**Lean 4 formalization:** `continuous/AsymptoticContinuous/`

The continuous generalization is included for transparency. It is not claimed to be as polished as the discrete submission.

## Building

Both projects use Lean 4 (v4.28.0) with Mathlib. Run `lake build` in either `discrete/` or `continuous/`.