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

- **`FPT_ne_W1`**: The complexity-theoretic hypothesis FPT â‰  W[1].
- **`thm_grohe`**: Grohe's theorem (2007) â€” tractable CSP on a class of
  bounded-arity core hypergraphs implies uniformly bounded treewidth.
  Operates on `SizedHypergraph` so different class members can have
  different vertex-set sizes, making the uniform bound non-trivial.
- **`IsTreeCompatibleOrdering`**: Axiomatized predicate for the structured
  yields of a rooted tree decomposition â€” the orderings that respect the
  tree's bag-separation structure.
- **`StructuredMCFG` / `engelfriet_tw_to_mcfl`**: Engelfriet's construction
  (1997) â€” given a tree decomposition of width â‰¤ k, produces a (k+1)-MCFG
  whose language is exactly the set of tree-compatible orderings.
- **`mcfg_homomorphic_image`, `mcfg_finite_union`**: Standard MCFL closure
  properties (homomorphic image preserves dimension; finite union preserves
  dimension).
-/

set_option autoImplicit false

universe u v

/-! ## Complexity-theoretic hypothesis -/

/-- FPT â‰  W[1]: the parameterized analogue of P â‰  NP.
(Definitions 8.1â€“8.2, Remark 8.3) -/
axiom FPT_ne_W1 : Prop

/-! ## Grohe's Theorem -/

/-- Theorem 5.1 (Grohe 2007) â€” Asymptotic version.

Assume FPT â‰  W[1]. Let ð“— be a recursively enumerable class of
bounded-arity core hypergraphs (where different members can have different
vertex-set sizes). If CSP restricted to instances whose constraint
hypergraph belongs to ð“— is solvable in polynomial time for all choices
of constraint relations, then ð“— has uniformly bounded treewidth.

ð“— : Set SizedHypergraph â€” each element is a pair (n, H) where
H : Hypergraph (Fin n). Different elements can have different n,
making the uniform k non-trivial.

Correspondences to Grohe 2007:
- "recursively enumerable class" â†’ SizedHypergraphClass.RecursivelyEnumerable
- "bounded arity" â†’ SizedHypergraphClass.BoundedArity
- "polynomial time for all relation choices" â†’ SizedHypergraphClass.UniformPolyTimeSolvable
- "bounded treewidth" â†’ SizedHypergraphClass.BoundedTreewidth
- "core" â†’ SizedHypergraphClass.AllCores

Note on the core condition (Grohe 2007, Theorem 1.2):
Grohe's theorem concludes bounded treewidth *of cores*. Without the
AllCores hypothesis, the class of bipartite graphs is a counterexample:
CSP on bipartite graphs is tractable (all cores are Kâ‚ or Kâ‚‚), but
grid graphs are bipartite with unbounded treewidth. With AllCores,
bounded core treewidth = bounded treewidth. -/
axiom thm_grohe :
  FPT_ne_W1 â†’
  âˆ€ (ð“— : Set SizedHypergraph),
    SizedHypergraphClass.RecursivelyEnumerable ð“— â†’
    SizedHypergraphClass.BoundedArity ð“— â†’
    SizedHypergraphClass.AllCores ð“— â†’
    SizedHypergraphClass.UniformPolyTimeSolvable ð“— â†’
    SizedHypergraphClass.BoundedTreewidth ð“—

/-! ## Tree-Compatible Orderings -/

/-- A predicate characterizing the "structured yields" of a rooted tree
decomposition. These are linearizations of the vertices of H that respect
the tree decomposition's bag structure â€” the exact orderings that the
Engelfriet MCFG construction generates.

Intuitively, a tree-compatible ordering processes the tree nodes in some
traversal order, outputting each vertex when its "home" bag is reached.
The resulting linearization respects the tree's separation structure:
vertices in different subtrees are separated by vertices in the separator
(boundary) bags. A formal characterization would require defining tree
traversals and vertex-to-bag assignments; since we axiomatize the entire
Engelfriet construction, we axiomatize this predicate alongside it. -/
axiom IsTreeCompatibleOrdering : âˆ€ {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V} (td : TreeDecomposition H) (r : td.I)
    (perm : List V), Prop

/-- Tree-compatible orderings are nodup permutations of H.verts.
This is a basic coherence property: any structured yield lists each vertex
exactly once and covers all vertices. -/
axiom isTreeCompatibleOrdering_spec : âˆ€ {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V} {td : TreeDecomposition H} {r : td.I}
    {perm : List V},
    IsTreeCompatibleOrdering td r perm â†’
    perm.toFinset = H.verts âˆ§ perm.Nodup

/-- Every tree decomposition admits at least one tree-compatible ordering.
This follows from the fact that any rooted tree has at least one valid
traversal, and any traversal yields a structured linearization. -/
axiom isTreeCompatibleOrdering_nonempty : âˆ€ {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V} (td : TreeDecomposition H) (r : td.I),
    âˆƒ (perm : List V), IsTreeCompatibleOrdering td r perm

/-! ## Engelfriet Structure Theorems -/

/-- Theorems 5.8 + 5.9 (Engelfriet 1997, Habel 1992, Aiswarya et al. 2026).

Per-instance axiom. Given one hypergraph H with a tree decomposition,
produces a structured MCFG whose language is exactly the set of
tree-compatible orderings of H's vertices.

When used in the main theorem:
- Grohe gives a uniform k and per-agent treewidth bounds
- For each specific agent with V = Fin n, we apply this axiom
- The axiom sees V = Fin n, [DecidableEq (Fin n)], [Fintype (Fin n)] â€” automatic

The grammar's language satisfies:
- `lang_complete`: every tree-compatible ordering is generated
- `lang_sound`: everything generated is a tree-compatible ordering
  (with toFinset = H.verts and Nodup)
- Together: L(grammar) = { tree-compatible orderings of H.verts } -/
structure StructuredMCFG {V : Type*} [DecidableEq V] [Fintype V]
    {H : Hypergraph V}
    (td : TreeDecomposition H) (r : td.I) where
  grammar : MCFG V
  node : grammar.N â†’ td.I
  start_node : node grammar.S = r
  arity_eq : âˆ€ A : grammar.N, grammar.ar A = max 1 (td.boundary r (node A)).card
  terminals_in_bag : âˆ€ (p : MCFGProduction V grammar.N grammar.ar)
    (_ : p âˆˆ grammar.productions),
    âˆ€ (s : List (V âŠ• â„•)) (_ : s âˆˆ p.lhs_strings)
      (v : V) (_ : Sum.inl v âˆˆ s),
      v âˆˆ td.bag (node p.lhs)
  rhs_are_children : âˆ€ (p : MCFGProduction V grammar.N grammar.ar)
    (_ : p âˆˆ grammar.productions)
    (i : Fin p.rhs.length),
    node (p.rhs.get i) âˆˆ td.children r (node p.lhs)
  /-- Completeness: every tree-compatible ordering is generated.
  The grammar produces all orderings consistent with the tree
  decomposition's bag structure. -/
  lang_complete : âˆ€ (perm : List V),
    IsTreeCompatibleOrdering td r perm â†’
    perm âˆˆ grammar.Language
  /-- Soundness: everything generated is a tree-compatible ordering.
  Every word in the grammar's language is a nodup permutation of H.verts
  that respects the tree decomposition's bag structure. -/
  lang_sound : âˆ€ (perm : List V), perm âˆˆ grammar.Language â†’
    perm.toFinset = H.verts âˆ§ perm.Nodup âˆ§ IsTreeCompatibleOrdering td r perm

axiom engelfriet_tw_to_mcfl :
  âˆ€ (V : Type u) [DecidableEq V] [Fintype V]
    (H : Hypergraph V)
    (td : TreeDecomposition H) (r : td.I)
    (k : â„•) (hk : td.width â‰¤ k),
      âˆƒ (S : StructuredMCFG td r),
        S.grammar.dimension â‰¤ k + 1

/-! ## MCFL Closure Properties -/

axiom mcfg_homomorphic_image {Symâ‚ : Type*} {Symâ‚‚ : Type*}
    (G : MCFG Symâ‚) (h : Symâ‚ â†’ List Symâ‚‚) :
    âˆƒ G' : MCFG Symâ‚‚, G'.dimension â‰¤ G.dimension âˆ§
      G'.Language = { w : List Symâ‚‚ | âˆƒ w' âˆˆ G.Language, w = (w'.map h).flatten }

axiom mcfg_finite_union {Sym : Type*} {Î¹ : Type*} [Fintype Î¹]
    (Ls : Î¹ â†’ Set (List Sym)) (d : â„•)
    (h : âˆ€ i, âˆƒ G : MCFG Sym, G.dimension â‰¤ d âˆ§ G.Language = Ls i) :
    âˆƒ G : MCFG Sym, G.dimension â‰¤ d âˆ§ G.Language = â‹ƒ i, Ls i

/-- **Finite languages are MCFLs at every positive dimension.**

A standard closure property of multiple context-free languages: every
finite language `L âŠ† Î£*` is a `d`-MCFL for every `d â‰¥ 1`. This follows
because a finite language is context-free (list its elements as
productions from the start symbol), and context-free = 1-MCFL âŠ† d-MCFL
for `d â‰¥ 1`. See e.g. Seki et al. (1991), Theorem 3.9 and the
dimension-monotonicity remark in Section 3.

We axiomatize this directly; a full mechanization would introduce a
trivial MCFG whose productions enumerate the finite language and invoke
`MCFG.dimension_le_of_forall`.

NOTE (alternative route considered): instead of adding this axiom, one
could discharge `full_behavior_bound` using only `mcfg_finite_union` by
constructing the finite image of decompositions explicitly. In the paper
this is the one-line observation "only finitely many distinct
languages"; in Lean, to hand `mcfg_finite_union` a `Fintype` index, you
would take `Set.range (fun (td, r) â†¦ A.TreeBehaviorLanguage td r â€¦)`,
show it is finite because it sits inside the finite powerset of
`Î£^{â‰¤|V|}`, convert that `Set.Finite` to a `Finset`, and then re-express
`FullBehaviorLanguage` as `â‹ƒ L âˆˆ thisFinset, L` via a `Set.biUnion`
rewrite. That route is not hard but is not "a few lines" either â€” it is
genuine `Set.Finite` â†” `Finset` plumbing plus a `Set.biUnion` unfold.
The axiom below collapses that bookkeeping into a single standard
closure fact. -/
axiom finite_language_is_mcfl {Sym : Type*}
    (L : Set (List Sym)) (hfin : L.Finite) (d : â„•) (hd : 1 â‰¤ d) :
    IsMCFL L d
