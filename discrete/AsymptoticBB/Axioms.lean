/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.CSP
import AsymptoticBB.Basic.SizedInstances
import AsymptoticBB.TreeDecomposition.Defs
import AsymptoticBB.TreeDecomposition.Boundary
import AsymptoticBB.Grammars.Union
import AsymptoticBB.Grammars.TCO
import AsymptoticBB.Grammars.Homomorphism
import AsymptoticBB.Agent.Defs
import AsymptoticBB.Agent.Tractability

/-!
# Axioms and Cited Theorems (Asymptotic Version)

This module declares the external results cited by the proof:

- **`FPT_ne_W1`**: The complexity-theoretic hypothesis FPT ≠ W[1].
- **`thm_grohe`**: Grohe's theorem (2007) — tractable CSP on a class of
  bounded-arity core hypergraphs implies uniformly bounded treewidth.
  Operates on `SizedHypergraph` so different class members can have
  different vertex-set sizes, making the uniform bound non-trivial.
- **`mcfg_homomorphic_image`**: A single homomorphic image preserves
  dimension (Seki et al. 1991).

The former external assumptions `IsTreeCompatibleOrdering`,
`isTreeCompatibleOrdering_spec`, `isTreeCompatibleOrdering_nonempty`, and
`engelfriet_tw_to_mcfl` are **no longer axioms**: they are now a concrete
definition and machine-checked theorems in `AsymptoticBB.Grammars.TCO`
(imported above), which constructs the tree-compatible-ordering grammar
explicitly.  `mcfg_finite_union` is likewise a proved theorem
(`AsymptoticBB.Grammars.Union`).
-/

set_option autoImplicit false

universe u v

/-! ## Complexity-theoretic hypothesis -/

/-- FPT ≠ W[1]: the parameterized analogue of P ≠ NP.
(Definitions 8.1–8.2, Remark 8.3)

TRUST-BASE GUARD: this must remain an *uninterpreted* `Prop` used only
as a hypothesis. Do NOT add an axiom asserting it holds (e.g.
`axiom fpt_ne_w1_holds : FPT_ne_W1`). The consistency of `thm_grohe`
against adversarial interpretations of the opaque class predicates
depends on its conclusion staying guarded behind this hypothesis. -/
axiom FPT_ne_W1 : Prop

/-! ## Grohe's Theorem -/

/-- Theorem 5.1 (Grohe 2007) — Asymptotic version.

Assume FPT ≠ W[1]. Let 𝓗 be a recursively enumerable class of
bounded-arity core hypergraphs (where different members can have different
vertex-set sizes). If CSP restricted to instances whose constraint
hypergraph belongs to 𝓗 is solvable in polynomial time for all choices
of constraint relations, then 𝓗 has uniformly bounded treewidth.

𝓗 : Set SizedHypergraph — each element is a pair (n, H) where
H : Hypergraph (Fin n). Different elements can have different n,
making the uniform k non-trivial.

Correspondences to Grohe 2007:
- "recursively enumerable class" → SizedHypergraphClass.RecursivelyEnumerable
- "bounded arity" → SizedHypergraphClass.BoundedArity
- "polynomial time for all relation choices" → SizedHypergraphClass.UniformPolyTimeSolvable
- "bounded treewidth" → SizedHypergraphClass.BoundedTreewidth
- "core" → SizedHypergraphClass.AllCores

Note on the core condition (Grohe 2007, Theorem 1.2):
Grohe's theorem concludes bounded treewidth *of cores*. Without the
AllCores hypothesis, the class of bipartite graphs is a counterexample:
CSP on bipartite graphs is tractable (all cores are K₁ or K₂), but
grid graphs are bipartite with unbounded treewidth. With AllCores,
bounded core treewidth = bounded treewidth. -/
axiom thm_grohe :
  FPT_ne_W1 →
  ∀ (𝓗 : Set SizedHypergraph),
    SizedHypergraphClass.RecursivelyEnumerable 𝓗 →
    SizedHypergraphClass.BoundedArity 𝓗 →
    SizedHypergraphClass.AllCores 𝓗 →
    SizedHypergraphClass.UniformPolyTimeSolvable 𝓗 →
    SizedHypergraphClass.BoundedTreewidth 𝓗

/-! ## Tree-Compatible Orderings -/

/-! ## Former Engelfriet interface — now proved

The declarations `IsTreeCompatibleOrdering`, `isTreeCompatibleOrdering_spec`,
`isTreeCompatibleOrdering_nonempty`, `StructuredMCFG`, and
`engelfriet_tw_to_mcfl` were **axioms** in earlier revisions of this project,
attributed to Engelfriet (1997) / Habel (1992).  The cited works do not
contain the bespoke statement that was attributed to them (see
`FORMALIZATION_AUDIT.md`).  They are now a concrete grammar construction
with machine-checked proofs in `AsymptoticBB/Grammars/TCO.lean`, imported
above: tree-compatible orderings are *defined* as the language of the
explicit budget-disciplined grammar `tcoGrammar`, whose dimension is bounded
by boundary size, and the spec/nonemptiness/packaging statements are proved
by induction on derivations and by an explicit depth-first derivation. -/

/-! ## MCFL Closure Properties

The homomorphic-image closure (`mcfg_homomorphic_image`, Seki et al. 1991
Thm 3.9) was formerly an axiom here.  It is now a proved theorem in
`AsymptoticBB.Grammars.Homomorphism` (imported below): the image grammar is
constructed by substituting `h a` for each terminal occurrence, keeping
variables and arities, so the dimension bound holds by construction and the
language identity is proved by two derivation inductions.  Finite union
(`mcfg_finite_union`) is likewise proved in `AsymptoticBB.Grammars.Union`.

The remaining trust base of this project is exactly:
- `FPT_ne_W1` (an uninterpreted hypothesis, never asserted), and
- `thm_grohe` (Grohe 2007, the one imported literature theorem). -/

/-! ### Non-vacuity of the dimension bound (trust-base note)

An axiom `finite_language_is_mcfl : L.Finite → 1 ≤ d → IsMCFL L d`
previously lived here. It was UNUSED by the proof chain, and it was a
trivializing hazard: since every per-agent behavior language is finite,
it let Lean discharge every headline conclusion `IsMCFL L (k+1)` — and,
worse, the class-level statement `∃ k, ∀ F, …` — with the junk witness
`k = 0`, bypassing Grohe and Engelfriet entirely. It has been DELETED.

The relevant routes to `IsMCFL` in this development are:
- `engelfriet_tw_to_mcfl` (dimension tied to tree-decomposition width),
- `mcfg_homomorphic_image` (a dimension-preserving image of one grammar),
- `mcfg_finite_union` (existential stitching within a fixed tier), and
- explicit grammar constructions such as `MCFG.empty`.

The bridge below first derives one language for each satisfying assignment by
homomorphic image of the width-bounded ordering grammar and then stitches those
languages by finite union.  Thus finiteness is used for the intended meaning of
combining finitely many behaviors; it does not choose the treewidth parameter,
which remains the uniform bound supplied by the structural theorem. -/
