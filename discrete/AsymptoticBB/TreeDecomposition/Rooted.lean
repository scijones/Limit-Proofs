/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.TreeDecomposition.Boundary

/-!
# Rooted Tree Structure of a Tree Decomposition

Structural lemmas about the rooted tree of a tree decomposition, needed by
the concrete tree-compatible-ordering grammar (`Grammars/TCO.lean`):

- `mem_subtreeAt_iff_eq_or_child`: the subtree at `t` decomposes as `{t}`
  plus the subtrees at the children of `t`.
- `not_mem_subtreeAt_child`: a node is never in the subtree of one of its
  children (gives the termination measure for recursion over the tree).
- `subtreeAt_child_disjoint`: subtrees of distinct children are disjoint.
- `homeNode` / `emitAt` / `emitBelow`: a fixed assignment of each vertex to
  one covering bag, and the induced partition of vertices across the tree.

All proofs are elementary manipulations of unique paths in a tree; no new
axioms are introduced.
-/

set_option autoImplicit false

noncomputable section Rooted

set_option linter.style.openClassical false
open Classical

open SimpleGraph Walk

variable {V : Type*} [DecidableEq V] {H : Hypergraph V} (td : TreeDecomposition H)

/-! ## Unique-path facts -/

omit [DecidableEq V] in
/-- If `s` is a descendant of `t`, then **every** path from the root to `s`
passes through `t` (paths in a tree are unique). -/
theorem TreeDecomposition.IsDescendant.mem_support_of_isPath
    {r t s : td.I} (h : td.IsDescendant r t s)
    (p : td.tree.Walk r s) (hp : p.IsPath) : t ∈ p.support := by
  obtain ⟨q, hq, ht⟩ := h
  have huniq : (⟨q, hq⟩ : td.tree.Path r s) = ⟨p, hp⟩ :=
    td.tree_isTree.IsAcyclic.path_unique _ _
  have hqp : q = p := congrArg Subtype.val huniq
  rwa [hqp] at ht

omit [DecidableEq V] in
/-- A node is never inside the subtree of one of its own children. -/
theorem not_mem_subtreeAt_child {r t c : td.I} (hc : c ∈ td.children r t) :
    t ∉ td.subtreeAt r c := by
  rintro ⟨P, hP, hcP⟩
  have hct : c ≠ t := children_ne_parent td r t c hc
  have hcsub : c ∈ td.subtreeAt r t := children_in_subtree td r t c hc
  -- The prefix of `P` up to `c` is the unique path `r → c`, so it contains `t`.
  have htake_path : (P.takeUntil c hcP).IsPath := hP.takeUntil hcP
  have ht_take : t ∈ (P.takeUntil c hcP).support :=
    TreeDecomposition.IsDescendant.mem_support_of_isPath td hcsub _ htake_path
  -- But `t` is also the endpoint of the suffix, and `c ≠ t` makes the suffix
  -- non-nil, so `t` appears in the suffix's tail as well — contradicting
  -- nodup-ness of `P.support`.
  have hdrop_nnil : ¬ (P.dropUntil c hcP).Nil := Walk.not_nil_of_ne hct
  have ht_drop : t ∈ (P.dropUntil c hcP).support.tail :=
    Walk.end_mem_tail_support hdrop_nnil
  have hsupp : P.support =
      (P.takeUntil c hcP).support ++ (P.dropUntil c hcP).support.tail := by
    conv_lhs => rw [← Walk.take_spec P hcP]
    exact Walk.support_append _ _
  have hnodup : P.support.Nodup := hP.support_nodup
  rw [hsupp] at hnodup
  exact (List.nodup_append'.mp hnodup).2.2 ht_take ht_drop

omit [DecidableEq V] in
/-- On the unique path from the root through `t` to a strict descendant, the
node immediately after `t` is the unique child of `t` whose subtree contains
the descendant.  This lemma extracts that child: any child of `t` lying on
the path `r → s` equals the successor of `t` on that path. -/
theorem child_eq_snd_dropUntil {r t s : td.I}
    (P : td.tree.Walk r s) (hP : P.IsPath) (htP : t ∈ P.support)
    {c : td.I} (hc : c ∈ td.children r t) (hcP : c ∈ P.support) :
    c = (P.dropUntil t htP).snd := by
  have hct : c ≠ t := children_ne_parent td r t c hc
  have hadj : td.tree.Adj t c := children_adj td r t c hc
  -- `c` cannot lie in the prefix `r → t`: otherwise `t ∈ subtreeAt r c`,
  -- contradicting `not_mem_subtreeAt_child`.
  have hc_not_take : c ∉ (P.takeUntil t htP).support := by
    intro hmem
    exact not_mem_subtreeAt_child td hc
      ⟨P.takeUntil t htP, hP.takeUntil htP, hmem⟩
  -- Hence `c` lies in the suffix `Q := P.dropUntil t htP`.
  have hsupp : P.support =
      (P.takeUntil t htP).support ++ (P.dropUntil t htP).support.tail := by
    conv_lhs => rw [← Walk.take_spec P htP]
    exact Walk.support_append _ _
  have hc_tail : c ∈ (P.dropUntil t htP).support.tail := by
    have := hcP
    rw [hsupp] at this
    rcases List.mem_append.mp this with h | h
    · exact absurd h hc_not_take
    · exact h
  set Q := P.dropUntil t htP with hQ_def
  have hQ_path : Q.IsPath := hP.dropUntil htP
  have hcQ : c ∈ Q.support := List.mem_of_mem_tail hc_tail
  -- The prefix of `Q` up to `c` is a path `t → c`; the unique such path is
  -- the single edge, whose second vertex is `c`.
  have htake_path : (Q.takeUntil c hcQ).IsPath := hQ_path.takeUntil hcQ
  have hedge_path : (Walk.cons hadj Walk.nil : td.tree.Walk t c).IsPath := by
    rw [Walk.isPath_def]
    simp [hadj.ne]
  have huniq : (⟨Q.takeUntil c hcQ, htake_path⟩ : td.tree.Path t c) =
      ⟨Walk.cons hadj Walk.nil, hedge_path⟩ :=
    td.tree_isTree.IsAcyclic.path_unique _ _
  have hval : Q.takeUntil c hcQ = Walk.cons hadj Walk.nil :=
    congrArg Subtype.val huniq
  -- `snd` of the takeUntil equals `snd` of `Q`; `snd` of the edge is `c`.
  have hsnd : (Q.takeUntil c hcQ).snd = Q.snd :=
    Walk.snd_takeUntil hct Q hcQ
  rw [hval] at hsnd
  simpa using hsnd

omit [DecidableEq V] in
/-- **Subtree decomposition.** A node `s` lies in the subtree at `t` iff it
is `t` itself or lies in the subtree of some child of `t`. -/
theorem mem_subtreeAt_iff_eq_or_child (r t s : td.I) :
    s ∈ td.subtreeAt r t ↔
      s = t ∨ ∃ c ∈ td.children r t, s ∈ td.subtreeAt r c := by
  constructor
  · rintro ⟨P, hP, htP⟩
    by_cases hst : s = t
    · exact Or.inl hst
    · refine Or.inr ?_
      -- The successor of `t` on the path is the desired child.
      set Q := P.dropUntil t htP with hQ_def
      have hQ_path : Q.IsPath := hP.dropUntil htP
      have hQ_nnil : ¬ Q.Nil := Walk.not_nil_of_ne (Ne.symm hst)
      have hadj : td.tree.Adj t Q.snd := Walk.adj_snd hQ_nnil
      have hc_tail : Q.snd ∈ Q.support.tail := Walk.snd_mem_tail_support hQ_nnil
      have hct : Q.snd ≠ t := hadj.ne'
      have hcQ : Q.snd ∈ Q.support := List.mem_of_mem_tail hc_tail
      have hcP : Q.snd ∈ P.support :=
        Walk.support_dropUntil_subset P htP hcQ
      -- Build the path `r → Q.snd` through `t`: prefix `r → t` plus `t → Q.snd`.
      have hcsub : Q.snd ∈ td.subtreeAt r t := by
        set R := (P.takeUntil t htP).append (Q.takeUntil Q.snd hcQ) with hR_def
        have hR_supp : R.support =
            (P.takeUntil t htP).support ++ (Q.takeUntil Q.snd hcQ).support.tail :=
          Walk.support_append _ _
        have htake_t_path : (P.takeUntil t htP).IsPath := hP.takeUntil htP
        have htake_c_path : (Q.takeUntil Q.snd hcQ).IsPath := hQ_path.takeUntil hcQ
        have hP_supp : P.support =
            (P.takeUntil t htP).support ++ Q.support.tail := by
          conv_lhs => rw [← Walk.take_spec P htP]
          exact Walk.support_append _ _
        have hP_nodup : P.support.Nodup := hP.support_nodup
        rw [hP_supp] at hP_nodup
        have hdisj := (List.nodup_append'.mp hP_nodup).2.2
        have hR_path : R.IsPath := by
          rw [Walk.isPath_def, hR_supp, List.nodup_append']
          refine ⟨htake_t_path.support_nodup,
            (List.tail_sublist _).nodup htake_c_path.support_nodup, ?_⟩
          intro x hx_take hx_tail
          -- Elements of the tail of `(Q.takeUntil Q.snd).support` lie in
          -- `Q.support.tail`, which is disjoint from the prefix support.
          have hx_ne_t : x ≠ t := by
            intro hxt
            have hnodup_tc : (Q.takeUntil Q.snd hcQ).support.Nodup :=
              htake_c_path.support_nodup
            rw [Walk.support_eq_cons (Q.takeUntil Q.snd hcQ)] at hnodup_tc
            exact (List.nodup_cons.mp hnodup_tc).1 (hxt ▸ hx_tail)
          have hx_Q : x ∈ Q.support :=
            Walk.support_takeUntil_subset Q hcQ (List.mem_of_mem_tail hx_tail)
          have hx_Q_tail : x ∈ Q.support.tail := by
            rw [Walk.support_eq_cons Q] at hx_Q
            rcases List.mem_cons.mp hx_Q with h | h
            · exact absurd h hx_ne_t
            · exact h
          exact hdisj hx_take hx_Q_tail
        have ht_R : t ∈ R.support := by
          rw [hR_supp]
          exact List.mem_append.mpr (Or.inl (Walk.end_mem_support _))
        exact ⟨R, hR_path, ht_R⟩
      exact ⟨Q.snd, by
        simp only [TreeDecomposition.children, Finset.mem_filter,
          Finset.mem_univ, true_and, TreeDecomposition.IsChild]
        exact ⟨hadj, hct, hcsub⟩,
        ⟨P, hP, hcP⟩⟩
  · rintro (rfl | ⟨c, hc, hs⟩)
    · exact IsDescendant_self td r s
    · exact subtreeAt_child_subset td r t c hc hs

omit [DecidableEq V] in
/-- **Sibling disjointness.** Subtrees of distinct children are disjoint. -/
theorem subtreeAt_child_disjoint {r t : td.I} {c c' : td.I}
    (hc : c ∈ td.children r t) (hc' : c' ∈ td.children r t) (hne : c ≠ c') :
    td.subtreeAt r c ∩ td.subtreeAt r c' = ∅ := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨P, hP, hcP⟩ hs'
  -- Both `c` and `c'` lie on the unique path `r → s`.
  have hc'P : c' ∈ P.support :=
    TreeDecomposition.IsDescendant.mem_support_of_isPath td hs' P hP
  -- `t` lies on the prefix up to `c`, hence on `P`.
  have hcsub : c ∈ td.subtreeAt r t := children_in_subtree td r t c hc
  have htP : t ∈ P.support := by
    have htake : t ∈ (P.takeUntil c hcP).support :=
      TreeDecomposition.IsDescendant.mem_support_of_isPath td hcsub _
        (hP.takeUntil hcP)
    exact Walk.support_takeUntil_subset P hcP htake
  -- Both children equal the successor of `t` on `P`.
  have h1 : c = (P.dropUntil t htP).snd :=
    child_eq_snd_dropUntil td P hP htP hc hcP
  have h2 : c' = (P.dropUntil t htP).snd :=
    child_eq_snd_dropUntil td P hP htP hc' hc'P
  exact hne (h1.trans h2.symm)

/-! ## Termination measure -/

omit [DecidableEq V] in
/-- The number of nodes in the subtree at `t`. -/
noncomputable def TreeDecomposition.subtreeSize (r t : td.I) : ℕ :=
  (Finset.univ.filter (fun s => s ∈ td.subtreeAt r t)).card

omit [DecidableEq V] in
/-- Children have strictly smaller subtrees. -/
theorem subtreeSize_child_lt {r t c : td.I} (hc : c ∈ td.children r t) :
    td.subtreeSize r c < td.subtreeSize r t := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨t, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsDescendant_self td r t, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_mem_subtreeAt_child td hc⟩
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact subtreeAt_child_subset td r t c hc hs

/-! ## Home bags and the emission partition -/

/-- A fixed (choice-based) assignment of each vertex to one bag containing
it.  Any such assignment works for the yield grammar; no root-most or
canonical choice is required. -/
noncomputable def TreeDecomposition.homeNode (v : V) : td.I :=
  if hv : v ∈ H.verts then (td.vertex_cover v hv).choose
  else Classical.arbitrary td.I

theorem TreeDecomposition.mem_bag_homeNode {v : V} (hv : v ∈ H.verts) :
    v ∈ td.bag (td.homeNode v) := by
  unfold TreeDecomposition.homeNode
  rw [dif_pos hv]
  exact (td.vertex_cover v hv).choose_spec

/-- Vertices assigned to node `t`. -/
noncomputable def TreeDecomposition.emitAt (t : td.I) : Finset V :=
  H.verts.filter (fun v => td.homeNode v = t)

/-- Vertices assigned to nodes in the subtree at `t`. -/
noncomputable def TreeDecomposition.emitBelow (r t : td.I) : Finset V :=
  H.verts.filter (fun v => td.homeNode v ∈ td.subtreeAt r t)

theorem emitAt_subset_bag (t : td.I) : td.emitAt t ⊆ td.bag t := by
  intro v hv
  simp only [TreeDecomposition.emitAt, Finset.mem_filter] at hv
  obtain ⟨hv_mem, hv_home⟩ := hv
  have := td.mem_bag_homeNode hv_mem
  rwa [hv_home] at this

theorem emitAt_subset_emitBelow (r t : td.I) :
    td.emitAt t ⊆ td.emitBelow r t := by
  intro v hv
  simp only [TreeDecomposition.emitAt, Finset.mem_filter] at hv
  simp only [TreeDecomposition.emitBelow, Finset.mem_filter]
  exact ⟨hv.1, hv.2 ▸ IsDescendant_self td r t⟩

theorem emitBelow_root (r : td.I) : td.emitBelow r r = H.verts := by
  ext v
  simp only [TreeDecomposition.emitBelow, Finset.mem_filter, and_iff_left_iff_imp]
  intro _
  exact mem_subtreeAt_root td r (td.homeNode v)

/-- **Emission decomposition.** The vertices below `t` split into those
assigned to `t` itself and those below the children. -/
theorem emitBelow_decomp (r t : td.I) :
    td.emitBelow r t =
      td.emitAt t ∪ (td.children r t).biUnion (fun c => td.emitBelow r c) := by
  ext v
  simp only [TreeDecomposition.emitBelow, TreeDecomposition.emitAt,
    Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨hv_mem, hv_sub⟩
    rcases (mem_subtreeAt_iff_eq_or_child td r t (td.homeNode v)).mp hv_sub with
      h | ⟨c, hc, hsub⟩
    · exact Or.inl ⟨hv_mem, h⟩
    · exact Or.inr ⟨c, hc, hv_mem, hsub⟩
  · rintro (⟨hv_mem, h⟩ | ⟨c, hc, hv_mem, hsub⟩)
    · exact ⟨hv_mem, h ▸ IsDescendant_self td r t⟩
    · exact ⟨hv_mem, subtreeAt_child_subset td r t c hc hsub⟩

/-- Emissions at `t` are disjoint from emissions below any child. -/
theorem emitAt_disjoint_emitBelow_child {r t c : td.I}
    (hc : c ∈ td.children r t) :
    Disjoint (td.emitAt t) (td.emitBelow r c) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [TreeDecomposition.emitAt, Finset.mem_filter] at hv
  simp only [TreeDecomposition.emitBelow, Finset.mem_filter] at hv'
  exact not_mem_subtreeAt_child td hc (hv.2 ▸ hv'.2)

/-- Emissions below distinct children are disjoint. -/
theorem emitBelow_child_disjoint {r t : td.I} {c c' : td.I}
    (hc : c ∈ td.children r t) (hc' : c' ∈ td.children r t) (hne : c ≠ c') :
    Disjoint (td.emitBelow r c) (td.emitBelow r c') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [TreeDecomposition.emitBelow, Finset.mem_filter] at hv hv'
  have := subtreeAt_child_disjoint td hc hc' hne
  have hmem : td.homeNode v ∈ td.subtreeAt r c ∩ td.subtreeAt r c' :=
    ⟨hv.2, hv'.2⟩
  rw [this] at hmem
  exact hmem

end Rooted
