/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Basic.Graph
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Boundary Separators in Tree Decompositions — proved

This module **replaces** the former axiom `separator_existence_from_treewidth`,
which asserted that in a graph of treewidth ≤ k *any* two vertex sets admit a
separator of size ≤ k+1.  That statement is **false**: on the path graph
`P₆` (treewidth 1) with `A` = odd and `B` = even vertices, every edge joins
`A` to `B`, so any separating set must be a vertex cover (size ≥ 3 > 2).
Treewidth does not bound the minimum cut between arbitrary coordinate sets.

What treewidth *does* provide — and what is proved here, mirroring the
discrete development — is a **boundary separator**: for any rooted tree
decomposition and any node `t`, the boundary `∂t` (vertices appearing both
inside and outside the subtree at `t`) is contained in the bag of `t`, hence
has size ≤ width + 1, and it separates the vertices below `t` from the
vertices outside `t`.  Consequently, whenever two sets lie on opposite sides
of some node of a width-≤ k decomposition, they are separated by ≤ k+1
vertices.

Everything in this file is proved; no axioms are introduced.
-/

set_option autoImplicit false

/-- A vertex set `C` separates `A` from `B` in `G`: every walk from a vertex
of `A \ C` to a vertex of `B \ C` passes through `C`. -/
def SimpleGraph.IsSeparatingSet {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B C : Finset V) : Prop :=
  ∀ u ∈ A \ C, ∀ v ∈ B \ C, ∀ (p : G.Walk u v),
    ∃ w, w ∈ C ∧ w ∈ p.support

noncomputable section Separator

set_option linter.style.openClassical false
open Classical

open SimpleGraph Walk

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  (td : TreeDecomposition G)

/-! ## Rooted subtrees, vertices below/outside, boundary -/

/-- A node `s` is a descendant of `t` (with respect to root `r`) if the
unique path from `r` to `s` passes through `t`. -/
def TreeDecomposition.IsDescendant (r t s : td.I) : Prop :=
  ∃ (p : td.tree.Walk r s), p.IsPath ∧ t ∈ p.support

/-- The subtree rooted at `t` (with respect to root `r`). -/
def TreeDecomposition.subtreeAt (r t : td.I) : Set td.I :=
  { s | td.IsDescendant r t s }

/-- The vertices "below" node `t`: the union of all bags in the subtree. -/
def TreeDecomposition.vertsBelow (r t : td.I) : Finset V :=
  (Finset.univ.filter (fun i => i ∈ td.subtreeAt r t)).biUnion td.bag

/-- The vertices "outside" node `t`: the union of all bags not in the
subtree. -/
def TreeDecomposition.vertsOutside (r t : td.I) : Finset V :=
  (Finset.univ.filter (fun i => i ∉ td.subtreeAt r t)).biUnion td.bag

/-- The boundary of node `t` (with respect to root `r`). -/
def TreeDecomposition.boundary (r t : td.I) : Finset V :=
  td.vertsBelow r t ∩ td.vertsOutside r t

omit [DecidableEq V] [Fintype V] in
/-- Every node is a descendant of itself. -/
theorem TreeDecomposition.isDescendant_self (r s : td.I) :
    td.IsDescendant r s s := by
  obtain ⟨p, hp⟩ := td.tree_isTree.isConnected.exists_isPath r s
  exact ⟨p, hp, p.end_mem_support⟩

/-- A path in a connected induced subgraph containing endpoints on both
sides of `t` must contain `t`.  (Identical to the discrete development.) -/
private theorem connected_induced_contains_separator
    {I : Type*}
    (T : SimpleGraph I) (hT : T.IsTree)
    (S : Set I) (hconn : (T.induce S).Connected)
    (r t : I)
    (s : I) (hs : s ∈ S)
    (hs_desc : ∃ (p : T.Walk r s), p.IsPath ∧ t ∈ p.support)
    (s' : I) (hs' : s' ∈ S)
    (hs'_not_desc : ∀ (p : T.Walk r s'), p.IsPath → t ∉ p.support) :
    t ∈ S := by
  obtain ⟨w_ind⟩ := hconn.preconnected ⟨s, hs⟩ ⟨s', hs'⟩
  let subHom : (T.induce S) →g T := ⟨Subtype.val, fun h => h⟩
  set w_G := w_ind.map subHom with hw_G_def
  have hw_S : ∀ x ∈ w_G.support, x ∈ S := by
    intro x hx
    rw [hw_G_def, SimpleGraph.Walk.support_map] at hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := List.mem_map.mp hx
    exact hy
  set p_ss' := w_G.toPath with hp_ss'_def
  have hp_S : ∀ x ∈ p_ss'.val.support, x ∈ S :=
    fun x hx => hw_S x (SimpleGraph.Walk.support_toPath_subset w_G hx)
  suffices t ∈ p_ss'.val.support from hp_S t this
  by_contra ht_not_ss'
  obtain ⟨p_rs, hp_rs, ht_rs⟩ := hs_desc
  obtain ⟨p_rs', hp_rs'⟩ := hT.isConnected.exists_isPath r s'
  have ht_not_rs' : t ∉ p_rs'.support := hs'_not_desc p_rs' hp_rs'
  set W := p_rs'.append p_ss'.val.reverse with hW_def
  have ht_not_W : t ∉ W.support := by
    rw [hW_def, SimpleGraph.Walk.support_append]
    intro ht
    rcases List.mem_append.mp ht with h1 | h2
    · exact ht_not_rs' h1
    · have h3 : t ∈ p_ss'.val.reverse.support := by
        have hsub : ∀ x, x ∈ (p_ss'.val.reverse.support).tail →
                          x ∈ p_ss'.val.reverse.support := by
          intro x hx
          cases h : p_ss'.val.reverse.support with
          | nil => simp [h] at hx
          | cons a as => exact List.mem_cons.mpr (Or.inr (by rwa [h] at hx))
        exact hsub t h2
      rw [SimpleGraph.Walk.support_reverse] at h3
      exact ht_not_ss' (List.mem_reverse.mp h3)
  have h_eq := hT.IsAcyclic.path_unique W.toPath ⟨p_rs, hp_rs⟩
  have h_val : W.toPath.val = p_rs := congrArg Subtype.val h_eq
  have ht_toPath : t ∈ W.toPath.val.support := by rw [h_val]; exact ht_rs
  exact ht_not_W (SimpleGraph.Walk.support_toPath_subset W ht_toPath)

/-- Boundary vertices lie in the bag of `t`. -/
theorem boundary_subset_bag (r t : td.I) :
    td.boundary r t ⊆ td.bag t := by
  intro v hv
  simp only [TreeDecomposition.boundary, Finset.mem_inter] at hv
  obtain ⟨hbelow, houtside⟩ := hv
  simp only [TreeDecomposition.vertsBelow, Finset.mem_biUnion, Finset.mem_filter,
             Finset.mem_univ, true_and] at hbelow
  obtain ⟨s, hs_sub, hv_s⟩ := hbelow
  simp only [TreeDecomposition.vertsOutside, Finset.mem_biUnion, Finset.mem_filter,
             Finset.mem_univ, true_and] at houtside
  obtain ⟨s', hs'_out, hv_s'⟩ := houtside
  have hconn := td.running_intersection v
  exact connected_induced_contains_separator
    td.tree td.tree_isTree
    {i | v ∈ td.bag i} hconn r t
    s hv_s hs_sub
    s' hv_s' (fun p hp ht_mem => hs'_out ⟨p, hp, ht_mem⟩)

/-- **Boundary size bound**: `|∂t| ≤ k + 1` when the width is ≤ `k`. -/
theorem boundary_card_le (r t : td.I) (k : ℕ) (hk : td.width ≤ k) :
    (td.boundary r t).card ≤ k + 1 := by
  calc (td.boundary r t).card
      ≤ (td.bag t).card := Finset.card_le_card (boundary_subset_bag td r t)
    _ ≤ td.width + 1 := td.bag_card_le_width_succ t
    _ ≤ k + 1 := Nat.add_le_add_right hk 1

/-! ## The boundary separates below from outside -/

omit [Fintype V] in
/-- Any walk from a `P`-vertex to a non-`P`-vertex crosses an edge from
`P` to non-`P`. -/
private theorem walk_crossing {P : V → Prop}
    {u v : V} (p : G.Walk u v) (hu : P u) (hv : ¬ P v) :
    ∃ x y, G.Adj x y ∧ P x ∧ ¬ P y ∧ x ∈ p.support := by
  induction p with
  | nil => exact absurd hu hv
  | @cons a b c hadj q ih =>
    by_cases hb : P b
    · obtain ⟨x, y, hxy, hx, hy, hxs⟩ := ih hb hv
      exact ⟨x, y, hxy, hx, hy, by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem a hxs⟩
    · exact ⟨a, b, hadj, hu, hb, by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_self⟩

/-- Vertices not below `t` are outside `t`. -/
theorem mem_vertsOutside_of_not_below (r t : td.I) (v : V)
    (hv : v ∉ td.vertsBelow r t) : v ∈ td.vertsOutside r t := by
  obtain ⟨i, hi⟩ := td.vertex_cover v
  simp only [TreeDecomposition.vertsOutside, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine ⟨i, ?_, hi⟩
  intro hsub
  exact hv (by
    simp only [TreeDecomposition.vertsBelow, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨i, hsub, hi⟩)

/-- **The boundary separates.**  If `A` lies below `t` and `B` lies outside
the subtree at `t` (i.e. avoids `vertsBelow` except possibly at the
boundary), then `∂t` separates `A` from `B`. -/
theorem boundary_separates (r t : td.I) (A B : Finset V)
    (hA : A ⊆ td.vertsBelow r t)
    (hB : ∀ v ∈ B, v ∈ td.vertsBelow r t → v ∈ td.boundary r t) :
    G.IsSeparatingSet A B (td.boundary r t) := by
  intro u hu v hv p
  rw [Finset.mem_sdiff] at hu hv
  have hu_below : u ∈ td.vertsBelow r t := hA hu.1
  have hv_not_below : v ∉ td.vertsBelow r t := by
    intro hcon
    exact hv.2 (hB v hv.1 hcon)
  obtain ⟨x, y, hxy, hx_below, hy_not, hx_supp⟩ :=
    walk_crossing (P := fun w => w ∈ td.vertsBelow r t) p hu_below hv_not_below
  -- The edge (x, y) lies in some bag; that bag cannot be in the subtree
  -- (else y would be below), so x is also outside — hence on the boundary.
  obtain ⟨i, hxi, hyi⟩ := td.edge_cover x y hxy
  have hi_not_sub : i ∉ td.subtreeAt r t := by
    intro hsub
    exact hy_not (by
      simp only [TreeDecomposition.vertsBelow, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨i, hsub, hyi⟩)
  have hx_outside : x ∈ td.vertsOutside r t := by
    simp only [TreeDecomposition.vertsOutside, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨i, hi_not_sub, hxi⟩
  exact ⟨x, Finset.mem_inter.mpr ⟨hx_below, hx_outside⟩, hx_supp⟩

end Separator
