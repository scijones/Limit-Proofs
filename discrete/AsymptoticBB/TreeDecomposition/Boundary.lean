/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.TreeDecomposition.Defs
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Boundary Size in Tree Decompositions

Lemma 11.2: the boundary of any subtree in a tree decomposition has size
at most k+1, where k is the width.

We define the subtree, boundary, and prove the bound.
-/

set_option autoImplicit false

noncomputable section Boundary

set_option linter.style.openClassical false
open Classical

variable {V : Type*} [DecidableEq V] {H : Hypergraph V} (td : TreeDecomposition H)

/-- A node s is a descendant of t (with respect to root r) if the unique
path from r to s passes through t. -/
def TreeDecomposition.IsDescendant (r t s : td.I) : Prop :=
  âˆƒ (p : td.tree.Walk r s), p.IsPath âˆ§ t âˆˆ p.support

/-- The subtree rooted at t (with respect to root r): the set of all nodes s
such that t lies on the unique path from r to s. -/
def TreeDecomposition.subtreeAt (r t : td.I) : Set td.I :=
  { s | td.IsDescendant r t s }

/-- The vertices "below" node t: the union of all bags in the subtree at t. -/
def TreeDecomposition.vertsBelow (r t : td.I) : Finset V :=
  (Finset.univ.filter (fun i => i âˆˆ td.subtreeAt r t)).biUnion td.bag

/-- The vertices "outside" node t: the union of all bags NOT in the subtree at t. -/
def TreeDecomposition.vertsOutside (r t : td.I) : Finset V :=
  (Finset.univ.filter (fun i => i âˆ‰ td.subtreeAt r t)).biUnion td.bag

/-- The boundary of node t (with respect to root r): vertices that appear both
below t and outside t. (Definition from Lemma 10.2) -/
def TreeDecomposition.boundary (r t : td.I) : Finset V :=
  td.vertsBelow r t âˆ© td.vertsOutside r t

/-- Lemma 11.2a (Boundary âŠ† bag).
Every boundary vertex of node t lies in the bag of t. -/
private theorem connected_induced_contains_separator
    {I : Type*}
    (G : SimpleGraph I) (hG : G.IsTree)
    (S : Set I) (hconn : (G.induce S).Connected)
    (r t : I)
    (s : I) (hs : s âˆˆ S)
    (hs_desc : âˆƒ (p : G.Walk r s), p.IsPath âˆ§ t âˆˆ p.support)
    (s' : I) (hs' : s' âˆˆ S)
    (hs'_not_desc : âˆ€ (p : G.Walk r s'), p.IsPath â†’ t âˆ‰ p.support) :
    t âˆˆ S := by
  obtain âŸ¨w_indâŸ© := hconn.preconnected âŸ¨s, hsâŸ© âŸ¨s', hs'âŸ©
  let subHom : (G.induce S) â†’g G := âŸ¨Subtype.val, fun h => hâŸ©
  set w_G := w_ind.map subHom with hw_G_def
  have hw_S : âˆ€ x âˆˆ w_G.support, x âˆˆ S := by
    intro x hx
    rw [hw_G_def, SimpleGraph.Walk.support_map] at hx
    obtain âŸ¨âŸ¨y, hyâŸ©, _, rflâŸ© := List.mem_map.mp hx
    exact hy
  set p_ss' := w_G.toPath with hp_ss'_def
  have hp_S : âˆ€ x âˆˆ p_ss'.val.support, x âˆˆ S :=
    fun x hx => hw_S x (SimpleGraph.Walk.support_toPath_subset w_G hx)
  suffices t âˆˆ p_ss'.val.support from hp_S t this
  by_contra ht_not_ss'
  obtain âŸ¨p_rs, hp_rs, ht_rsâŸ© := hs_desc
  obtain âŸ¨p_rs', hp_rs'âŸ© := hG.isConnected.exists_isPath r s'
  have ht_not_rs' : t âˆ‰ p_rs'.support := hs'_not_desc p_rs' hp_rs'
  set W := p_rs'.append p_ss'.val.reverse with hW_def
  have ht_not_W : t âˆ‰ W.support := by
    rw [hW_def, SimpleGraph.Walk.support_append]
    intro ht
    rcases List.mem_append.mp ht with h1 | h2
    Â· exact ht_not_rs' h1
    Â· have h3 : t âˆˆ p_ss'.val.reverse.support := by
        have hsub : âˆ€ x, x âˆˆ (p_ss'.val.reverse.support).tail â†’
                          x âˆˆ p_ss'.val.reverse.support := by
          intro x hx
          cases h : p_ss'.val.reverse.support with
          | nil => simp [h] at hx
          | cons a as => exact List.mem_cons.mpr (Or.inr (by rwa [h] at hx))
        exact hsub t h2
      rw [SimpleGraph.Walk.support_reverse] at h3
      exact ht_not_ss' (List.mem_reverse.mp h3)
  have h_eq := hG.IsAcyclic.path_unique W.toPath âŸ¨p_rs, hp_rsâŸ©
  have h_val : W.toPath.val = p_rs := congrArg Subtype.val h_eq
  have ht_toPath : t âˆˆ W.toPath.val.support := by rw [h_val]; exact ht_rs
  exact ht_not_W (SimpleGraph.Walk.support_toPath_subset W ht_toPath)

theorem boundary_subset_bag (r t : td.I) :
    td.boundary r t âŠ† td.bag t := by
  intro v hv
  simp only [TreeDecomposition.boundary, Finset.mem_inter] at hv
  obtain âŸ¨hbelow, houtsideâŸ© := hv
  simp only [TreeDecomposition.vertsBelow, Finset.mem_biUnion, Finset.mem_filter,
             Finset.mem_univ, true_and] at hbelow
  obtain âŸ¨s, hs_sub, hv_sâŸ© := hbelow
  simp only [TreeDecomposition.vertsOutside, Finset.mem_biUnion, Finset.mem_filter,
             Finset.mem_univ, true_and] at houtside
  obtain âŸ¨s', hs'_out, hv_s'âŸ© := houtside
  have hv_in : v âˆˆ H.verts := td.bags_subset s hv_s
  have hconn := td.running_intersection v hv_in
  exact connected_induced_contains_separator
    td.tree td.tree_isTree
    {i | v âˆˆ td.bag i} hconn r t
    s hv_s hs_sub
    s' hv_s' (fun p hp ht_mem => hs'_out âŸ¨p, hp, ht_memâŸ©)

/-- Lemma 11.2b (Boundary cardinality bound).
|âˆ‚_t| â‰¤ k + 1 when the tree decomposition has width â‰¤ k. -/
theorem boundary_card_le (r t : td.I) (k : â„•) (hk : td.width â‰¤ k) :
    (td.boundary r t).card â‰¤ k + 1 := by
  calc (td.boundary r t).card
      â‰¤ (td.bag t).card := Finset.card_le_card (boundary_subset_bag td r t)
    _ â‰¤ td.width + 1 := td.bag_card_le_width_succ t
    _ â‰¤ k + 1 := Nat.add_le_add_right hk 1

omit [DecidableEq V] in
/-- Every node is a descendant of itself (the path from r to s passes through s). -/
theorem IsDescendant_self (r s : td.I) : td.IsDescendant r s s := by
  obtain âŸ¨p, hpâŸ© := td.tree_isTree.isConnected.exists_isPath r s
  exact âŸ¨p, hp, p.end_mem_supportâŸ©

omit [DecidableEq V] in
/-- The root is in the subtree at the root. -/
theorem root_mem_subtreeAt_root (r : td.I) : r âˆˆ td.subtreeAt r r :=
  IsDescendant_self td r r

omit [DecidableEq V] in
/-- Every node is in the subtree at the root. -/
theorem mem_subtreeAt_root (r s : td.I) : s âˆˆ td.subtreeAt r r := by
  obtain âŸ¨p, hpâŸ© := td.tree_isTree.isConnected.exists_isPath r s
  exact âŸ¨p, hp, p.start_mem_supportâŸ©

/-- vertsOutside(r, r) = âˆ…: there are no nodes outside the subtree at root. -/
theorem vertsOutside_root_eq_empty (r : td.I) : td.vertsOutside r r = âˆ… := by
  simp only [TreeDecomposition.vertsOutside]
  have hfilter : Finset.filter (fun i => i âˆ‰ td.subtreeAt r r) Finset.univ = âˆ… := by
    rw [Finset.filter_eq_empty_iff]
    intro i _
    simp only [not_not]
    exact mem_subtreeAt_root td r i
  rw [hfilter, Finset.biUnion_empty]

/-- boundary(r, r) = âˆ…: the boundary at the root is empty. -/
theorem boundary_root_eq_empty (r : td.I) : td.boundary r r = âˆ… := by
  simp only [TreeDecomposition.boundary, vertsOutside_root_eq_empty, Finset.inter_empty]

/-- |boundary(r, r)| = 0: the boundary at root has cardinality 0. -/
theorem boundary_root_card (r : td.I) : (td.boundary r r).card = 0 := by
  simp only [boundary_root_eq_empty, Finset.card_empty]

/-! ## Rooted Tree Structure -/

/-- A node c is a child of t (with respect to root r) if:
1. c is adjacent to t in the tree
2. c is a strict descendant of t (i.e., c â‰  t and c is in the subtree at t) -/
def TreeDecomposition.IsChild (r t c : td.I) : Prop :=
  td.tree.Adj t c âˆ§ c â‰  t âˆ§ c âˆˆ td.subtreeAt r t

/-- The set of children of node t with respect to root r. -/
def TreeDecomposition.children (r t : td.I) : Finset td.I :=
  Finset.univ.filter (fun c => td.IsChild r t c)

/-- A node is a leaf (with respect to root r) if it has no children. -/
def TreeDecomposition.IsLeaf (r t : td.I) : Prop :=
  td.children r t = âˆ…

/-- Children are adjacent to their parent. -/
theorem children_adj (r t : td.I) (c : td.I) (hc : c âˆˆ td.children r t) :
    td.tree.Adj t c := by
  simp only [TreeDecomposition.children, Finset.mem_filter, Finset.mem_univ,
             true_and, TreeDecomposition.IsChild] at hc
  exact hc.1

/-- Children are in the subtree at t. -/
theorem children_in_subtree (r t : td.I) (c : td.I) (hc : c âˆˆ td.children r t) :
    c âˆˆ td.subtreeAt r t := by
  simp only [TreeDecomposition.children, Finset.mem_filter, Finset.mem_univ,
             true_and, TreeDecomposition.IsChild] at hc
  exact hc.2.2

/-- Children are different from their parent. -/
theorem children_ne_parent (r t : td.I) (c : td.I) (hc : c âˆˆ td.children r t) :
    c â‰  t := by
  simp only [TreeDecomposition.children, Finset.mem_filter, Finset.mem_univ,
             true_and, TreeDecomposition.IsChild] at hc
  exact hc.2.1

/-- The parent-child relationship is antireflexive. -/
theorem not_child_self (r t : td.I) : t âˆ‰ td.children r t := by
  simp only [TreeDecomposition.children, Finset.mem_filter, Finset.mem_univ,
             true_and, TreeDecomposition.IsChild, and_imp, not_and]
  intro _ hne
  exact absurd rfl hne

/-- Subtree at a child is contained in subtree at parent. -/
theorem subtreeAt_child_subset (r t c : td.I) (hc : c âˆˆ td.children r t) :
    td.subtreeAt r c âŠ† td.subtreeAt r t := by
  intro s hs
  obtain âŸ¨p_rs, hp_rs, hc_in_pâŸ© := hs
  have hc_sub := children_in_subtree td r t c hc
  obtain âŸ¨p_rc, hp_rc, ht_in_prcâŸ© := hc_sub
  let prefix_walk := p_rs.takeUntil c hc_in_p
  have h_path_unique := td.tree_isTree.IsAcyclic.path_unique prefix_walk.toPath âŸ¨p_rc, hp_rcâŸ©
  have ht_in_prefix_path : t âˆˆ prefix_walk.toPath.val.support := by
    simp only [congrArg (Â·.val.support) h_path_unique, ht_in_prc]
  have ht_in_prefix : t âˆˆ prefix_walk.support :=
    SimpleGraph.Walk.support_toPath_subset prefix_walk ht_in_prefix_path
  have h_subwalk := SimpleGraph.Walk.isSubwalk_takeUntil p_rs hc_in_p
  rw [SimpleGraph.Walk.isSubwalk_iff_support_isInfix] at h_subwalk
  have ht_in_p : t âˆˆ p_rs.support := h_subwalk.subset ht_in_prefix
  exact âŸ¨p_rs, hp_rs, ht_in_pâŸ©

end Boundary
