/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.CSP
import AsymptoticBB.Basic.SizedInstances
import AsymptoticBB.TreeDecomposition.Defs
import AsymptoticBB.TreeDecomposition.Boundary
import AsymptoticBB.Grammars.MCFG
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
- **`IsTreeCompatibleOrdering`**: Axiomatized predicate for the structured
  yields of a rooted tree decomposition — the orderings that respect the
  tree's bag-separation structure.
- **`StructuredMCFG` / `engelfriet_tw_to_mcfl`**: Engelfriet's construction
  (1997) — given a tree decomposition of width ≤ k, produces a (k+1)-MCFG
  whose language is exactly the set of tree-compatible orderings.
- **`mcfg_homomorphic_image`, `mcfg_finite_union`**: Standard MCFL closure
  properties (homomorphic image preserves dimension; finite union preserves
  dimension).
-/

set_option autoImplicit false

universe u v

/-! ## Complexity-theoretic hypothesis -/

/-- FPT ≠ W[1]: the parameterized analogue of P ≠ NP.
(Definitions 8.1–8.2, Remark 8.3) -/
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

/-- A predicate characterizing the "structured yields" of a rooted tree
decomposition. These are linearizations of the vertices of H that respect
the tree decomposition's bag structure — the exact orderings that the
Engelfriet MCFG construction generates.

Intuitively, a tree-compatible ordering processes the tree nodes in some
traversal order, outputting each vertex when its "home" bag is reached.
The resulting linearization respects the tree's separation structure:
vertices in different subtrees are separated by vertices in the separator
(boundary) bags. A formal characterization would require defining tree
traversals and vertex-to-bag assignments; since we axiomatize the entire
Engelfriet construction, we axiomatize this predicate alongside it. -/
axiom IsTreeCompatibleOrdering : ∀ {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V} (td : TreeDecomposition H) (r : td.I)
    (perm : List V), Prop

/-- Tree-compatible orderings are nodup permutations of H.verts.
This is a basic coherence property: any structured yield lists each vertex
exactly once and covers all vertices. -/
axiom isTreeCompatibleOrdering_spec : ∀ {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V} {td : TreeDecomposition H} {r : td.I}
    {perm : List V},
    IsTreeCompatibleOrdering td r perm →
    perm.toFinset = H.verts ∧ perm.Nodup

/-- Every tree decomposition admits at least one tree-compatible ordering.
This follows from the fact that any rooted tree has at least one valid
traversal, and any traversal yields a structured linearization. -/
axiom isTreeCompatibleOrdering_nonempty : ∀ {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V} (td : TreeDecomposition H) (r : td.I),
    ∃ (perm : List V), IsTreeCompatibleOrdering td r perm

/-! ## Engelfriet Structure Theorems -/

/-- Theorems 5.8 + 5.9 (Engelfriet 1997, Habel 1992, Aiswarya et al. 2026).

Per-instance axiom. Given one hypergraph H with a tree decomposition,
produces a structured MCFG whose language is exactly the set of
tree-compatible orderings of H's vertices.

When used in the main theorem:
- Grohe gives a uniform k and per-agent treewidth bounds
- For each specific agent with V = Fin n, we apply this axiom
- The axiom sees V = Fin n, [DecidableEq (Fin n)], [Fintype (Fin n)] — automatic

The grammar's language satisfies:
- `lang_complete`: every tree-compatible ordering is generated
- `lang_sound`: everything generated is a tree-compatible ordering
  (with toFinset = H.verts and Nodup)
- Together: L(grammar) = { tree-compatible orderings of H.verts } -/
structure StructuredMCFG {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V}
    (td : TreeDecomposition H) (r : td.I) where
  grammar : MCFG V
  node : grammar.N → td.I
  start_node : node grammar.S = r
  arity_eq : ∀ A : grammar.N, grammar.ar A = max 1 (td.boundary r (node A)).card
  terminals_in_bag : ∀ (p : MCFGProduction V grammar.N grammar.ar)
    (_ : p ∈ grammar.productions),
    ∀ (s : List (V ⊕ ℕ)) (_ : s ∈ p.lhs_strings)
      (v : V) (_ : Sum.inl v ∈ s),
      v ∈ td.bag (node p.lhs)
  rhs_are_children : ∀ (p : MCFGProduction V grammar.N grammar.ar)
    (_ : p ∈ grammar.productions)
    (i : Fin p.rhs.length),
    node (p.rhs.get i) ∈ td.children r (node p.lhs)
  /-- Completeness: every tree-compatible ordering is generated.
  The grammar produces all orderings consistent with the tree
  decomposition's bag structure. -/
  lang_complete : ∀ (perm : List V),
    IsTreeCompatibleOrdering td r perm →
    perm ∈ grammar.Language
  /-- Soundness: everything generated is a tree-compatible ordering.
  Every word in the grammar's language is a nodup permutation of H.verts
  that respects the tree decomposition's bag structure. -/
  lang_sound : ∀ (perm : List V), perm ∈ grammar.Language →
    perm.toFinset = H.verts ∧ perm.Nodup ∧ IsTreeCompatibleOrdering td r perm

axiom engelfriet_tw_to_mcfl :
  ∀ (V : Type u) [DecidableEq V] [Fintype V]
    (H : Hypergraph V)
    (td : TreeDecomposition H) (r : td.I)
    (k : ℕ) (hk : td.width ≤ k),
      ∃ (S : StructuredMCFG td r),
        S.grammar.dimension ≤ k + 1

/-! ## MCFL Closure Properties -/

axiom mcfg_homomorphic_image {Sym₁ : Type*} {Sym₂ : Type*}
    (G : MCFG Sym₁) (h : Sym₁ → List Sym₂) :
    ∃ G' : MCFG Sym₂, G'.dimension ≤ G.dimension ∧
      G'.Language = { w : List Sym₂ | ∃ w' ∈ G.Language, w = (w'.map h).flatten }

axiom mcfg_finite_union {Sym : Type*} {ι : Type*} [Fintype ι]
    (Ls : ι → Set (List Sym)) (d : ℕ)
    (h : ∀ i, ∃ G : MCFG Sym, G.dimension ≤ d ∧ G.Language = Ls i) :
    ∃ G : MCFG Sym, G.dimension ≤ d ∧ G.Language = ⋃ i, Ls i

/-- **Finite languages are MCFLs at every positive dimension.**

A standard closure property of multiple context-free languages: every
finite language `L ⊆ Σ*` is a `d`-MCFL for every `d ≥ 1`. This follows
because a finite language is context-free (list its elements as
productions from the start symbol), and context-free = 1-MCFL ⊆ d-MCFL
for `d ≥ 1`. See e.g. Seki et al. (1991), Theorem 3.9 and the
dimension-monotonicity remark in Section 3.

We axiomatize this directly; a full mechanization would introduce a
trivial MCFG whose productions enumerate the finite language and invoke
`MCFG.dimension_le_of_forall`.

NOTE (alternative route considered): instead of adding this axiom, one
could discharge `full_behavior_bound` using only `mcfg_finite_union` by
constructing the finite image of decompositions explicitly. In the paper
this is the one-line observation "only finitely many distinct
languages"; in Lean, to hand `mcfg_finite_union` a `Fintype` index, you
would take `Set.range (fun (td, r) ↦ A.TreeBehaviorLanguage td r …)`,
show it is finite because it sits inside the finite powerset of
`Σ^{≤|V|}`, convert that `Set.Finite` to a `Finset`, and then re-express
`FullBehaviorLanguage` as `⋃ L ∈ thisFinset, L` via a `Set.biUnion`
rewrite. That route is not hard but is not "a few lines" either — it is
genuine `Set.Finite` ↔ `Finset` plumbing plus a `Set.biUnion` unfold.
The axiom below collapses that bookkeeping into a single standard
closure fact. -/
axiom finite_language_is_mcfl {Sym : Type*}
    (L : Set (List Sym)) (hfin : L.Finite) (d : ℕ) (hd : 1 ≤ d) :
    IsMCFL L d
