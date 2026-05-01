/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.Hypergraph
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Tree Decompositions and Treewidth

Definitions 4.1 and 4.2 from the paper.
-/

set_option autoImplicit false

/-- A tree decomposition of a hypergraph H = (V, E).
(Definition 4.1)

A tree decomposition is a pair (T, {B_t}) where T is a tree and each B_t ⊆ V
is a bag, satisfying:
- (T1) Vertex cover: every vertex appears in some bag.
- (T2) Edge cover: every hyperedge is contained in some bag.
- (T3) Running intersection: for each vertex v, the nodes whose bags contain v
  form a connected subtree. -/
structure TreeDecomposition {V : Type*} (H : Hypergraph V) where
  /-- The index type for nodes of the tree. -/
  I : Type
  [instFintypeI : Fintype I]
  [instDecEqI : DecidableEq I]
  [instNonemptyI : Nonempty I]
  /-- The tree structure on nodes. -/
  tree : SimpleGraph I
  /-- The tree is actually a tree (connected and acyclic). -/
  tree_isTree : tree.IsTree
  /-- The bag assignment: each node gets a finite set of vertices. -/
  bag : I → Finset V
  /-- Bags only contain vertices of H. -/
  bags_subset : ∀ i, bag i ⊆ H.verts
  /-- (T1) Every vertex of H appears in at least one bag. -/
  vertex_cover : ∀ v ∈ H.verts, ∃ i : I, v ∈ bag i
  /-- (T2) Every hyperedge of H is contained in some bag. -/
  edge_cover : ∀ e ∈ H.edges, ∃ i : I, e ⊆ bag i
  /-- (T3) Running intersection: for each vertex v, the subgraph induced
  on nodes containing v in their bags is connected. -/
  running_intersection : ∀ v ∈ H.verts,
    (tree.induce {i : I | v ∈ bag i}).Connected

attribute [instance] TreeDecomposition.instFintypeI
  TreeDecomposition.instDecEqI TreeDecomposition.instNonemptyI

/-- The width of a tree decomposition is max_t |B_t| - 1.
(Part of Definition 4.1) -/
noncomputable def TreeDecomposition.width {V : Type*} {H : Hypergraph V}
    (td : TreeDecomposition H) : ℕ :=
  (Finset.univ.image (fun i => (td.bag i).card)).max.getD 0 - 1

/-- A hypergraph has treewidth at most k if there exists a tree decomposition
of width at most k.
(Definition 4.2) -/
def Hypergraph.HasTreewidthAtMost {V : Type*} (H : Hypergraph V) (k : ℕ) : Prop :=
  ∃ td : TreeDecomposition H, td.width ≤ k

/-- The treewidth of a hypergraph. (Definition 4.2) -/
noncomputable def Hypergraph.treewidth {V : Type*} (H : Hypergraph V) : ℕ :=
  ⨅ (td : TreeDecomposition H), td.width

/-- The cardinality of any bag is at most width + 1.
This is the defining property unpacked from the definition of width. -/
theorem TreeDecomposition.bag_card_le_width_succ
    {V : Type*} {H : Hypergraph V} (td : TreeDecomposition H) (t : td.I) :
    (td.bag t).card ≤ td.width + 1 := by
  unfold TreeDecomposition.width
  set S := Finset.univ.image (fun i => (td.bag i).card) with hS_def
  have ht_mem : (td.bag t).card ∈ S := Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  obtain ⟨m, hm⟩ := Finset.max_of_mem ht_mem
  have hle : (td.bag t).card ≤ m := Finset.le_max_of_eq ht_mem hm
  have hgetD : S.max.getD 0 = m := by
    rw [hm]; rfl
  rw [hgetD]
  omega
