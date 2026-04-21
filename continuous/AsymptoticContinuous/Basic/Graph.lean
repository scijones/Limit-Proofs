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
{1, â€¦, N}. We reuse Mathlib's `SimpleGraph` for this and define tree
decompositions of simple graphs.

## Main definitions

* `TreeDecomposition` â€” a tree decomposition of a `SimpleGraph`
* `TreeDecomposition.width` â€” max bag size minus 1
* `HasTreewidthAtMost` â€” existence of a decomposition of bounded width
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
  bag : I â†’ Finset V
  vertex_cover : âˆ€ v : V, âˆƒ i : I, v âˆˆ bag i
  edge_cover : âˆ€ (u v : V), G.Adj u v â†’ âˆƒ i : I, u âˆˆ bag i âˆ§ v âˆˆ bag i
  running_intersection : âˆ€ (v : V),
    (tree.induce {i : I | v âˆˆ bag i}).Connected

attribute [instance] TreeDecomposition.instFintypeI
  TreeDecomposition.instDecEqI TreeDecomposition.instNonemptyI

noncomputable def TreeDecomposition.width {V : Type*} {G : SimpleGraph V}
    (td : TreeDecomposition G) : â„• :=
  (Finset.univ.image (fun i => (td.bag i).card)).max.getD 0 - 1

def SimpleGraph.HasTreewidthAtMost {V : Type*} (G : SimpleGraph V) (k : â„•) : Prop :=
  âˆƒ td : TreeDecomposition G, td.width â‰¤ k

theorem TreeDecomposition.bag_card_le_width_succ
    {V : Type*} {G : SimpleGraph V} (td : TreeDecomposition G) (t : td.I) :
    (td.bag t).card â‰¤ td.width + 1 := by
  unfold TreeDecomposition.width
  set S := Finset.univ.image (fun i => (td.bag i).card) with hS_def
  have ht_mem : (td.bag t).card âˆˆ S := Finset.mem_image.mpr âŸ¨t, Finset.mem_univ _, rflâŸ©
  obtain âŸ¨m, hmâŸ© := Finset.max_of_mem ht_mem
  have hle : (td.bag t).card â‰¤ m := Finset.le_max_of_eq ht_mem hm
  have hgetD : S.max.getD 0 = m := by rw [hm]; rfl
  rw [hgetD]
  omega
