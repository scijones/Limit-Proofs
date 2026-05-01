/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Basic

/-!
# Graphs and Tree Decompositions

The CI graph of a system is an undirected graph on the coordinate index set
{1, …, N}. We reuse Mathlib's `SimpleGraph` for this and define tree
decompositions of simple graphs.

## Main definitions

* `TreeDecomposition` — a tree decomposition of a `SimpleGraph`
* `TreeDecomposition.width` — max bag size minus 1
* `HasTreewidthAtMost` — existence of a decomposition of bounded width
-/

set_option autoImplicit false

/-- A tree decomposition of a simple graph G on vertex set V. -/
structure TreeDecomposition {V : Type*} (G : SimpleGraph V) where
  I : Type
  [instFintypeI : Fintype I]
  [instDecEqI : DecidableEq I]
  [instNonemptyI : Nonempty I]
  tree : SimpleGraph I
  tree_isTree : tree.IsTree
  bag : I → Finset V
  vertex_cover : ∀ v : V, ∃ i : I, v ∈ bag i
  edge_cover : ∀ (u v : V), G.Adj u v → ∃ i : I, u ∈ bag i ∧ v ∈ bag i
  running_intersection : ∀ (v : V),
    (tree.induce {i : I | v ∈ bag i}).Connected

attribute [instance] TreeDecomposition.instFintypeI
  TreeDecomposition.instDecEqI TreeDecomposition.instNonemptyI

noncomputable def TreeDecomposition.width {V : Type*} {G : SimpleGraph V}
    (td : TreeDecomposition G) : ℕ :=
  (Finset.univ.image (fun i => (td.bag i).card)).max.getD 0 - 1

def SimpleGraph.HasTreewidthAtMost {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ td : TreeDecomposition G, td.width ≤ k

theorem TreeDecomposition.bag_card_le_width_succ
    {V : Type*} {G : SimpleGraph V} (td : TreeDecomposition G) (t : td.I) :
    (td.bag t).card ≤ td.width + 1 := by
  unfold TreeDecomposition.width
  set S := Finset.univ.image (fun i => (td.bag i).card) with hS_def
  have ht_mem : (td.bag t).card ∈ S := Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  obtain ⟨m, hm⟩ := Finset.max_of_mem ht_mem
  have hle : (td.bag t).card ≤ m := Finset.le_max_of_eq ht_mem hm
  have hgetD : S.max.getD 0 = m := by rw [hm]; rfl
  rw [hgetD]
  omega
