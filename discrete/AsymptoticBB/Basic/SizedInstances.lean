/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.Hypergraph
import AsymptoticBB.TreeDecomposition.Defs
import AsymptoticBB.Basic.CSP

/-!
# Sized Instances: Hypergraphs and CSPs with Variable-Size Vertex Sets

Defines `SizedHypergraph` — a hypergraph bundled with its vertex-set size
`n`, so that different class members can have different vertex counts. A
uniform treewidth bound across such a class is non-trivial because as n
varies, the trivial bound n−1 varies with it.

We use `Fin n` as the vertex type, pinning everything to Type 0. `Fin n`
has automatic `Fintype`, `DecidableEq`, and `Nonempty` (for n > 0).

## Type propagation
```
SizedHypergraph ─────────────────────────────┐
  (n : ℕ, H : Hypergraph (Fin n))           │
                                              ├──▶ thm_grohe (Axioms.lean)
SizedHypergraphClass predicates:              │
  BoundedTreewidth, BoundedArity,            │
  RecursivelyEnumerable,                     │
  UniformPolyTimeSolvable  ──────────────────┘
```
-/

set_option autoImplicit false

/-! ## Sized Hypergraphs -/

/-- A hypergraph bundled with its vertex-set size.

Different elements of `Set SizedHypergraph` can have different `n` values,
so a uniform treewidth bound `∃ k, ∀ sH ∈ 𝓗, sH.H.HasTreewidthAtMost k`
is genuinely non-trivial (it can't be satisfied by k = n−1 when n varies). -/
structure SizedHypergraph where
  /-- The number of vertices. -/
  n : ℕ
  /-- The hypergraph on Fin n. -/
  H : Hypergraph (Fin n)

/-- Treewidth of a sized hypergraph (delegates to the underlying definition). -/
def SizedHypergraph.HasTreewidthAtMost (sH : SizedHypergraph) (k : ℕ) : Prop :=
  sH.H.HasTreewidthAtMost k

/-! ## Class-Level Predicates for Sized Hypergraph Classes

These are the predicates that appear in Grohe's theorem statement.
They quantify over `Set SizedHypergraph` — a collection of hypergraphs
with HETEROGENEOUS vertex-set sizes. -/

/-- A class of sized hypergraphs has bounded treewidth: one uniform k works
for all members regardless of their vertex-set size. -/
def SizedHypergraphClass.BoundedTreewidth (𝓗 : Set SizedHypergraph) : Prop :=
  ∃ k : ℕ, ∀ sH ∈ 𝓗, sH.HasTreewidthAtMost k

/-- A class of sized hypergraphs has bounded arity: one uniform r works for
all members. (Arity of a hyperedge = number of vertices in it.) -/
def SizedHypergraphClass.BoundedArity (𝓗 : Set SizedHypergraph) : Prop :=
  ∃ r : ℕ, ∀ sH ∈ 𝓗, sH.H.BoundedArity r

/-- A class of sized hypergraphs is recursively enumerable.

Opaque: effective encodings of finite hypergraphs are orthogonal to the proof.
The predicate enables stating Grohe's theorem in its published form.

An element of such a class is a pair (n, H) — an r.e. enumeration must
enumerate both the size and the hypergraph structure. -/
opaque SizedHypergraphClass.RecursivelyEnumerable : Set SizedHypergraph → Prop

/-- A class of sized hypergraphs admits a uniform polynomial-time CSP solver
for arbitrary constraint relations on every member.

Opaque: formalizing Turing machines is orthogonal.

"Uniform" means one algorithm handles:
1. All sizes n (the vertex count varies across the class)
2. All choices of constraint relations on each hypergraph
3. Polynomial in |V| + Σ|Rⱼ| (input size includes the relations)

This models a single online real-time belief-revision architecture that
operates over an open-ended family of possible encountered instances. -/
opaque SizedHypergraphClass.UniformPolyTimeSolvable : Set SizedHypergraph → Prop

/-- A sized hypergraph is a core: it has no non-trivial endomorphism
(no homomorphism to a proper substructure).

Opaque: formalizing graph homomorphisms and core computation is orthogonal.

Grohe 2007 (JACM, Theorem 1.2) proves bounded treewidth *of cores*.
A class of cores has bounded core treewidth iff it has bounded treewidth.
The `AllCores` hypothesis constrains the class to already-minimal
representations, so the Grohe conclusion gives actual treewidth bounds.

For the agent application this is natural: a non-core constraint
hypergraph has redundant variables that could be collapsed. -/
opaque SizedHypergraph.IsCore : SizedHypergraph → Prop

/-- Every member of the class is a core (no non-trivial endomorphism).
With this hypothesis, Grohe's bounded-core-treewidth conclusion
is equivalent to bounded treewidth of the structures themselves. -/
def SizedHypergraphClass.AllCores (𝓗 : Set SizedHypergraph) : Prop :=
  ∀ sH ∈ 𝓗, SizedHypergraph.IsCore sH

/-! ## Sized CSPs

A CSP bundled with its vertex-set size, for use in the class-level
tractability definitions. -/

/-- A CSP instance bundled with its vertex-set size and domain assignment.

Domain types `D : Fin n → Type` live in `Type 0`.
This is sufficient for the mathematical content (domains are finite sets
of values). -/
structure SizedCSP where
  n : ℕ
  D : Fin n → Type
  csp : CSP (Fin n) D

/-- The sized hypergraph induced by a sized CSP. -/
def SizedCSP.constraintSizedHypergraph (P : SizedCSP) : SizedHypergraph :=
  ⟨P.n, P.csp.constraintHypergraph⟩

/-! ## Connection Lemmas

These connect the sized and unsized worlds, enabling reuse of all
per-instance theorems (bridge, Engelfriet, etc.) within the sized framework. -/

/-- Every SizedHypergraph can be viewed as a Hypergraph (Fin n).
This is just `sH.H` — trivial but worth naming for documentation. -/
def SizedHypergraph.toHypergraph (sH : SizedHypergraph) : Hypergraph (Fin sH.n) :=
  sH.H

/-- HasTreewidthAtMost for SizedHypergraph agrees with the per-instance notion. -/
theorem SizedHypergraph.hasTW_iff (sH : SizedHypergraph) (k : ℕ) :
    sH.HasTreewidthAtMost k ↔ sH.H.HasTreewidthAtMost k := by
  rfl -- definitionally equal

