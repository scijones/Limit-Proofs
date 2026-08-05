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

/-- Theorem 5.1 (Grohe 2007, JACM Theorem 1.2) — faithful (core-conclusion)
form.

Assume FPT ≠ W[1]. Let 𝓗 be a recursively enumerable class of
bounded-arity hypergraphs (different members may have different vertex-set
sizes). If CSP restricted to instances whose constraint hypergraph belongs
to 𝓗 is solvable in polynomial time for all choices of constraint
relations, then:

1. **the cores of 𝓗 have uniformly bounded treewidth** — there is one `k`
   such that every member has a core of treewidth at most `k`; and
2. if every member is itself a core, 𝓗 has uniformly bounded treewidth.

Conjunct 1 is the published conclusion; conjunct 2 is its standard
instantiation to classes of cores (the core of a core is the structure
itself, up to isomorphism — which preserves treewidth).  Both are readings
of the same named theorem.  The instantiation is bundled here rather than
derived because deriving it inside Lean would require asserting auxiliary
facts about the opaque predicates (`HomEquiv` reflexivity, core
uniqueness); bundling keeps the trust base at exactly the named theorem.

The core appears in the **conclusion**, not as a hypothesis on the class:
no minimality of members is assumed.  The raw-treewidth strengthening of
conjunct 1 is false (bipartite grids: tractable, unbounded raw treewidth,
all cores ≤ K₂), so conjunct 1 is the strongest conclusion available and
applies to *every* tractable class. -/
axiom thm_grohe :
  FPT_ne_W1 →
  ∀ (𝓗 : Set SizedHypergraph),
    SizedHypergraphClass.RecursivelyEnumerable 𝓗 →
    SizedHypergraphClass.BoundedArity 𝓗 →
    SizedHypergraphClass.UniformPolyTimeSolvable 𝓗 →
    SizedHypergraphClass.BoundedCoreTreewidth 𝓗 ∧
      (SizedHypergraphClass.AllCores 𝓗 →
        SizedHypergraphClass.BoundedTreewidth 𝓗)

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
- `thm_grohe` (Grohe 2007, stated in its published core-conclusion form
  together with its standard instantiation to classes of cores). -/

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
