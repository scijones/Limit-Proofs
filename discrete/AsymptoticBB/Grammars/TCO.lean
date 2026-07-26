/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Grammars.MCFG
import AsymptoticBB.TreeDecomposition.Boundary
import AsymptoticBB.TreeDecomposition.Rooted
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.List

/-!
# The Tree-Compatible-Ordering Grammar

This module **replaces** the former external assumptions
`IsTreeCompatibleOrdering`, `isTreeCompatibleOrdering_spec`,
`isTreeCompatibleOrdering_nonempty`, and `engelfriet_tw_to_mcfl` with a
concrete construction and machine-checked proofs.

## What is constructed

Given a rooted tree decomposition `(td, r)` of a hypergraph `H`, we build an
explicit MCFG `tcoGrammar td r` over the vertex alphabet:

* **Nonterminals** are pairs `(t, S)`: a tree node together with the finite
  set of vertices (the *budget*) that the subtree rooted at `t` still has to
  emit.  The arity of `(t, S)` is `max 1 |∂(t)|`, the boundary size of `t`
  (paper Lemma `lem:boundary`), so the grammar dimension is at most `k + 1`
  whenever `td.width ≤ k`.
* **Productions** at `(t, S)` choose a set `F ⊆ S ∩ B_t` of vertices emitted
  at `t` itself, a partition of `S \ F` into budgets for the children of
  `t`, and an arbitrary copyless interleaving of the fresh vertices and the
  children's tuple components into the `max 1 |∂(t)|` output components.

The **tree-compatible orderings** of `(td, r)` are *defined* as the language
of this grammar.  This is a definition, not a theorem about the literature:
the construction follows the string-yield technique of Engelfriet–Heyker
(JCSS 1991) and the boundary-indexed nonterminals of the paper's bridge
construction, but no result of Engelfriet's is invoked.  What the cited
literature still supplies downstream is Grohe's treewidth theorem and the
MCFL closure properties of Seki et al.

## What is proved (no new axioms)

* `tcoGrammar_dimension_le`: the grammar dimension is `≤ k + 1` when
  `td.width ≤ k`.
* `isTreeCompatibleOrdering_spec`: every word of the grammar is a
  duplicate-free enumeration of `H.verts` (by induction on derivations —
  the budget discipline makes this structural).
* `isTreeCompatibleOrdering_nonempty`: at least one ordering is generated
  (an explicit depth-first derivation, by strong induction on subtree size).
* `engelfriet_tw_to_mcfl`: the packaged existence statement consumed by the
  bridge theorem, now a theorem, with `StructuredMCFG` slimmed to exactly
  the fields the bridge uses.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

noncomputable section TCO

set_option linter.style.openClassical false
open Classical

/-! ### List helpers -/

/-- Splitting a list into the fibers of an ℕ-valued function (in fiber-index
order) permutes the original list. -/
private theorem filter_partition_perm {α : Type*} (n : ℕ) (l : List α)
    (f : α → ℕ) (hf : ∀ x ∈ l, f x < n) :
    ((List.range n).map (fun i => l.filter (fun x => f x = i))).flatten.Perm l := by
  induction l with
  | nil =>
    have hz : ((List.range n).map
        (fun i => ([] : List α).filter (fun x => f x = i))).flatten = ([] : List α) := by
      simp
    rw [hz]
  | cons a l ihl =>
    have hfa : f a ∈ List.range n := List.mem_range.mpr (hf a List.mem_cons_self)
    obtain ⟨s, t, hst⟩ := List.append_of_mem hfa
    have hnodup : (List.range n).Nodup := List.nodup_range
    rw [hst] at hnodup
    have hnot_s : f a ∉ s :=
      fun hmem => (List.nodup_append'.mp hnodup).2.2 hmem List.mem_cons_self
    have hnot_t : f a ∉ t :=
      (List.nodup_cons.mp (List.nodup_append'.mp hnodup).2.1).1
    have hfilter_ne : ∀ i : ℕ, i ≠ f a →
        (a :: l).filter (fun x => f x = i) = l.filter (fun x => f x = i) := by
      intro i hi
      rw [List.filter_cons_of_neg]
      simp only [decide_eq_true_eq]
      exact fun hcon => hi hcon.symm
    have hfilter_fa : (a :: l).filter (fun x => f x = f a) =
        a :: l.filter (fun x => f x = f a) := by
      rw [List.filter_cons_of_pos]
      simp
    have hperm_l := ihl (fun x hx => hf x (List.mem_cons_of_mem a hx))
    rw [hst] at hperm_l ⊢
    rw [List.map_append, List.map_cons] at hperm_l ⊢
    rw [List.map_congr_left
      (fun i hi => hfilter_ne i (fun h => hnot_s (h ▸ hi)))]
    rw [List.map_congr_left
      (fun i hi => hfilter_ne i (fun h => hnot_t (h ▸ hi)))]
    rw [hfilter_fa]
    rw [List.flatten_append, List.flatten_cons] at hperm_l ⊢
    rw [List.cons_append]
    exact List.Perm.trans List.perm_middle ((hperm_l).cons a)

/-- Flattening pointwise-disjoint duplicate-free expansions of a
duplicate-free list is duplicate-free. -/
private theorem flatten_expand_nodup {α β : Type*} (l : List α) (g : α → List β)
    (hl : l.Nodup) (hg : ∀ x ∈ l, (g x).Nodup)
    (hdisj : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ v ∈ g x, v ∉ g y) :
    (l.map g).flatten.Nodup := by
  rw [List.nodup_flatten]
  constructor
  · intro m hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    exact hg x hx
  · rw [List.pairwise_map]
    exact hl.pairwise_of_forall_ne
      (fun x hx y hy hne v hv hv' => hdisj x hx y hy hne v hv hv')

/-- A list is recovered by reading `getD` along its index range. -/
private theorem range_map_getD {α : Type*} (l : List α) (d : α) :
    (List.range l.length).map (fun j => l.getD j d) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem l d h2

/-- Bridge between `Fin`-indexed and ℕ-indexed maps over an index range. -/
private theorem map_finRange_eq_map_range {α : Type*} (n : ℕ) (F : ℕ → α) :
    (List.finRange n).map (fun i : Fin n => F i.val) = (List.range n).map F := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    congr 1
    simp [List.getElem_finRange]

/-- Flatten of a map is `flatMap`. -/
private theorem map_flatten_eq_flatMap {α β : Type*} (l : List α) (f : α → List β) :
    (l.map f).flatten = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

variable {V : Type u} [DecidableEq V] [Fintype V] {H : Hypergraph V}
  (td : TreeDecomposition H) (r : td.I)

/-! ### Tokens and encoding -/

/-- Tokens of a production arrangement: either a terminal vertex or a
reference to component `j` of a child node `c`.  The component index is
drawn from `Fin (|V| + 1)`, a uniform bound on all arities. -/
abbrev TCOTok (td : TreeDecomposition H) : Type u :=
  V ⊕ (td.I × Fin (Fintype.card V + 1))

/-- Injective encoding of child-component references as ℕ variable names. -/
noncomputable def tokEnc (x : td.I × Fin (Fintype.card V + 1)) : ℕ :=
  (Fintype.equivFin (td.I × Fin (Fintype.card V + 1)) x : ℕ)

theorem tokEnc_injective : Function.Injective (tokEnc td) := by
  intro a b h
  exact (Fintype.equivFin _).injective (Fin.val_injective h)

/-- Token-to-symbol map used in production strings. -/
noncomputable def tokToSym : TCOTok td → V ⊕ ℕ
  | Sum.inl v => Sum.inl v
  | Sum.inr pr => Sum.inr (tokEnc td pr)

theorem tokToSym_injective : Function.Injective (tokToSym td) := by
  intro a b h
  cases a with
  | inl v => cases b with
    | inl w => simpa [tokToSym] using h
    | inr pr => simp [tokToSym] at h
  | inr pr => cases b with
    | inl w => simp [tokToSym] at h
    | inr pr' =>
      simp only [tokToSym, Sum.inr.injEq] at h
      exact congrArg Sum.inr (tokEnc_injective td h)

/-! ### Arity -/

/-- The arity of tree node `t`: `max 1 |∂(t)|`. -/
noncomputable def tcoArity (t : td.I) : ℕ := max 1 (td.boundary r t).card

theorem tcoArity_pos (t : td.I) : 0 < tcoArity td r t :=
  Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)

theorem tcoArity_le_card (t : td.I) :
    tcoArity td r t ≤ Fintype.card V + 1 := by
  unfold tcoArity
  have hb : (td.boundary r t).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

theorem tcoArity_le (t : td.I) (k : ℕ) (hk : td.width ≤ k) :
    tcoArity td r t ≤ k + 1 := by
  unfold tcoArity
  have hb := boundary_card_le td r t k hk
  omega

theorem tcoArity_root : tcoArity td r r = 1 := by
  unfold tcoArity
  rw [boundary_root_card td r]
  omega

/-! ### Production parameters -/

/-- A parameter describing one production of the TCO grammar.

At node `t` with remaining budget `budget`:
* `fresh` — the vertices emitted at `t` itself (must lie in `t`'s bag);
* `cb c` — the budget delegated to child `c` (disjointly partitioning
  `budget \ fresh` across the children);
* `flat`, `assign` — a duplicate-free arrangement of the fresh terminals
  and all child-component references, distributed among the `tcoArity t`
  output components by `assign`. -/
structure TCOParam (td : TreeDecomposition H) (r : td.I) : Type u where
  t : td.I
  budget : Finset V
  fresh : Finset V
  cb : td.I → Finset V
  flat : List (TCOTok td)
  assign : TCOTok td → Fin (Fintype.card V + 1)
  flat_nodup : flat.Nodup
  fresh_sub_budget : fresh ⊆ budget
  fresh_sub_bag : fresh ⊆ td.bag t
  cb_sub : ∀ c ∈ td.children r t, cb c ⊆ budget \ fresh
  cb_disj : ∀ c ∈ td.children r t, ∀ c' ∈ td.children r t, c ≠ c' →
    Disjoint (cb c) (cb c')
  cover : budget = fresh ∪ (td.children r t).biUnion cb
  term_iff : ∀ v : V, Sum.inl v ∈ flat ↔ v ∈ fresh
  var_iff : ∀ (c : td.I) (j : Fin (Fintype.card V + 1)),
    Sum.inr (c, j) ∈ flat ↔ c ∈ td.children r t ∧ (j : ℕ) < tcoArity td r c
  assign_lt : ∀ tok ∈ flat, ((assign tok) : ℕ) < tcoArity td r t

noncomputable instance : Fintype (TCOParam td r) := by
  classical
  exact Fintype.ofInjective
    (fun p : TCOParam td r =>
      (p.t, p.budget, p.fresh, p.cb,
        (⟨p.flat, p.flat_nodup⟩ : {l : List (TCOTok td) // l.Nodup}),
        p.assign))
    (by
      intro a b h
      cases a
      cases b
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
      rfl)

variable {td r}

/-- The `i`-th output component of the arrangement: tokens of `flat`
assigned to component `i`, in `flat`'s order. -/
noncomputable def TCOParam.comp (p : TCOParam td r) (i : ℕ) : List (TCOTok td) :=
  p.flat.filter (fun tok => ((p.assign tok) : ℕ) = i)

/-- The variable-name list owned by child `c`: names for its components. -/
noncomputable def TCOParam.varNames (_p : TCOParam td r) (c : td.I) : List ℕ :=
  (List.finRange (tcoArity td r c)).map
    (fun j => tokEnc td (c, Fin.castLE (tcoArity_le_card td r c) j))

variable (td r)

/-! ### Building the production -/

/-- The MCFG production described by a parameter. -/
noncomputable def mkProd (p : TCOParam td r) :
    MCFGProduction V (td.I × Finset V) (fun A => tcoArity td r A.1) where
  lhs := (p.t, p.budget)
  rhs := (td.children r p.t).toList.map (fun c => (c, p.cb c))
  rhs_vars := (td.children r p.t).toList.map p.varNames
  lhs_strings := (List.range (tcoArity td r p.t)).map
    (fun i => (p.comp i).map (tokToSym td))
  lhs_arity := by simp
  rhs_len := by simp
  rhs_arities := by
    intro i
    simp only [List.get_eq_getElem, List.getElem_map, TCOParam.varNames,
      List.length_map, List.length_finRange]
    try rfl
  rhs_vars_nodup := by
    rw [List.nodup_flatten]
    constructor
    · intro l hl
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hl
      unfold TCOParam.varNames
      refine List.Nodup.map ?_ (List.nodup_finRange _)
      intro a b hab
      have hinj := tokEnc_injective td hab
      rw [Prod.mk.injEq] at hinj
      exact Fin.castLE_injective _ hinj.2
    · rw [List.pairwise_map]
      refine ((td.children r p.t).nodup_toList).pairwise_of_forall_ne ?_
      intro c hc c' hc' hne x hx hx'
      obtain ⟨j, -, hjx⟩ := List.mem_map.mp hx
      obtain ⟨j', -, hjx'⟩ := List.mem_map.mp hx'
      have hinj := tokEnc_injective td (hjx.trans hjx'.symm)
      rw [Prod.mk.injEq] at hinj
      exact hne hinj.1
  lhs_indices_bounded := by
    intro s hs x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hs
    obtain ⟨tok, htok, hsym⟩ := List.mem_map.mp hx
    have htok_flat : tok ∈ p.flat := List.mem_of_mem_filter htok
    cases tok with
    | inl v => simp [tokToSym] at hsym
    | inr pr =>
      obtain ⟨c, j⟩ := pr
      simp only [tokToSym, Sum.inr.injEq] at hsym
      subst hsym
      obtain ⟨hc, hj⟩ := (p.var_iff c j).mp htok_flat
      rw [List.mem_flatten]
      refine ⟨p.varNames c,
        List.mem_map.mpr ⟨c, Finset.mem_toList.mpr hc, rfl⟩, ?_⟩
      unfold TCOParam.varNames
      refine List.mem_map.mpr ⟨⟨(j : ℕ), hj⟩, List.mem_finRange _, ?_⟩
      exact congrArg (tokEnc td) (Prod.ext rfl (Fin.ext rfl))
  lhs_vars_nodup := by
    have hflat_nodup : ((List.range (tcoArity td r p.t)).map
        (fun i => (p.comp i).map (tokToSym td))).flatten.Nodup := by
      rw [List.nodup_flatten]
      constructor
      · intro l hl
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hl
        exact ((p.flat_nodup.filter _).map (tokToSym_injective td))
      · rw [List.pairwise_map]
        refine (List.nodup_range).pairwise_of_forall_ne ?_
        intro i hi i' hi' hne x hx hx'
        obtain ⟨tok, htok, rfl⟩ := List.mem_map.mp hx
        obtain ⟨tok', htok', heq⟩ := List.mem_map.mp hx'
        have htt : tok' = tok := tokToSym_injective td heq
        subst htt
        simp only [TCOParam.comp, List.mem_filter, decide_eq_true_eq] at htok htok'
        exact hne (htok.2.symm.trans htok'.2)
    refine List.Nodup.filterMap ?_ hflat_nodup
    intro a a' b hb hb'
    cases a with
    | inl v => simp at hb
    | inr x => cases a' with
      | inl v => simp at hb'
      | inr x' =>
        simp only [Option.mem_def, Option.some.injEq] at hb hb'
        rw [← hb'] at hb
        exact congrArg Sum.inr hb

/-! ### The grammar -/

/-- The tree-compatible-ordering grammar of a rooted tree decomposition. -/
noncomputable def tcoGrammar : MCFG V where
  N := td.I × Finset V
  ar := fun A => tcoArity td r A.1
  ar_pos := fun A => tcoArity_pos td r A.1
  S := (r, H.verts)
  start_arity := tcoArity_root td r
  productions := (Finset.univ : Finset (TCOParam td r)).toList.map (mkProd td r)

theorem tcoGrammar_dimension_le (k : ℕ) (hk : td.width ≤ k) :
    (tcoGrammar td r).dimension ≤ k + 1 :=
  MCFG.dimension_le_of_forall _ _ (fun A => tcoArity_le td r A.1 k hk)

/-- **Definition.** Tree-compatible orderings are the words of the TCO
grammar.  This replaces the former axiomatized predicate. -/
def IsTreeCompatibleOrdering (perm : List V) : Prop :=
  perm ∈ (tcoGrammar td r).Language

/-! ### Soundness: the budget invariant -/

/-- Expansion of a token under a substitution `η`. -/
noncomputable def tokExpand (η : ℕ → List V) : TCOTok td → List V
  | Sum.inl v => [v]
  | Sum.inr pr => η (tokEnc td pr)

/-- The generic substitution of `MCFG.Generates.prod`, at token level. -/
private theorem subst_map_eq (η : ℕ → List V) (l : List (TCOTok td)) :
    ((l.map (tokToSym td)).map (fun c => match c with
      | Sum.inl a => [a]
      | Sum.inr x => η x)).flatten =
    (l.map (tokExpand td η)).flatten := by
  rw [List.map_map]
  congr 1
  refine List.map_congr_left ?_
  intro tok _
  cases tok with
  | inl v => rfl
  | inr pr => rfl

/-- **The budget invariant.**  Every tuple generated at nonterminal `(t, S)`
flattens to a duplicate-free list whose content is exactly `S`.

The budget discipline of `TCOParam` makes this structural: fresh terminals
come from `S ∩ B_t`, and each child receives a sub-budget, disjointly.  By
induction on the derivation, the child components exhaust their budgets
without duplication, and the arrangement is copyless, so the flattened
output enumerates `S` exactly once. -/
theorem tco_generates_invariant (A : (tcoGrammar td r).N) (ss : List (List V))
    (h : (tcoGrammar td r).Generates A ss) :
    ss.flatten.toFinset = A.2 ∧ ss.flatten.Nodup := by
  induction h with
  | prod p hp η rhs_gen ih =>
    -- Recover the generating parameter.
    rw [show (tcoGrammar td r).productions =
      (Finset.univ : Finset (TCOParam td r)).toList.map (mkProd td r) from rfl] at hp
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
    -- ## Child tuples.
    have child_tuple : ∀ c ∈ td.children r q.t,
        (((List.finRange (tcoArity td r c)).map
          (fun j => η (tokEnc td (c, Fin.castLE (tcoArity_le_card td r c) j)))).flatten.toFinset
            = q.cb c) ∧
        ((List.finRange (tcoArity td r c)).map
          (fun j => η (tokEnc td (c, Fin.castLE (tcoArity_le_card td r c) j)))).flatten.Nodup := by
      intro c hc
      have hc_list : c ∈ (td.children r q.t).toList := Finset.mem_toList.mpr hc
      obtain ⟨i0, hi0⟩ := List.get_of_mem hc_list
      have hlen : ((mkProd td r q).rhs).length = (td.children r q.t).toList.length := by
        simp [mkProd]
      have hgen := ih (Fin.cast hlen.symm i0)
      have hrhs_i : ((mkProd td r q).rhs).get (Fin.cast hlen.symm i0) = (c, q.cb c) := by
        simp only [mkProd, List.get_eq_getElem, List.getElem_map, Fin.coe_cast]
        rw [show (td.children r q.t).toList[(i0 : ℕ)] = c from by
          simpa [List.get_eq_getElem] using hi0]
      have hvars_i : ((mkProd td r q).rhs_vars).get
          ((Fin.cast hlen.symm i0).cast (mkProd td r q).rhs_len.symm) =
            q.varNames c := by
        simp only [mkProd, List.get_eq_getElem, List.getElem_map, Fin.coe_cast]
        rw [show (td.children r q.t).toList[(i0 : ℕ)] = c from by
          simpa [List.get_eq_getElem] using hi0]
      rw [hrhs_i, hvars_i] at hgen
      unfold TCOParam.varNames at hgen
      rw [List.map_map] at hgen
      exact hgen
    -- The child tuple, named.
    set tup : td.I → List (List V) := fun c =>
      (List.finRange (tcoArity td r c)).map
        (fun j => η (tokEnc td (c, Fin.castLE (tcoArity_le_card td r c) j)))
      with htup_def
    have htup_len : ∀ c, (tup c).length = tcoArity td r c := by
      intro c
      simp [htup_def]
    have htup_mem : ∀ (c : td.I) (j : Fin (Fintype.card V + 1)),
        ((j : ℕ) < tcoArity td r c) →
        η (tokEnc td (c, j)) ∈ tup c := by
      intro c j hj
      rw [htup_def]
      refine List.mem_map.mpr ⟨⟨(j : ℕ), hj⟩, List.mem_finRange _, ?_⟩
      exact congrArg (fun x => η (tokEnc td (c, x))) (Fin.ext rfl)
    -- ## Per-component facts.
    have comp_nodup : ∀ c ∈ td.children r q.t,
        ∀ (j : Fin (Fintype.card V + 1)), ((j : ℕ) < tcoArity td r c) →
          (η (tokEnc td (c, j))).Nodup := by
      intro c hc j hj
      exact (List.nodup_flatten.mp (child_tuple c hc).2).1 _ (htup_mem c j hj)
    have comp_sub : ∀ c ∈ td.children r q.t,
        ∀ (j : Fin (Fintype.card V + 1)), ((j : ℕ) < tcoArity td r c) →
          ∀ x ∈ η (tokEnc td (c, j)), x ∈ q.cb c := by
      intro c hc j hj x hx
      rw [← (child_tuple c hc).1, List.mem_toFinset, List.mem_flatten]
      exact ⟨η (tokEnc td (c, j)), htup_mem c j hj, hx⟩
    have comp_complete : ∀ c ∈ td.children r q.t,
        ∀ x ∈ q.cb c, ∃ (j : Fin (Fintype.card V + 1)),
          ((j : ℕ) < tcoArity td r c) ∧ x ∈ η (tokEnc td (c, j)) := by
      intro c hc x hx
      rw [← (child_tuple c hc).1, List.mem_toFinset, List.mem_flatten] at hx
      obtain ⟨m, hm, hxm⟩ := hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hm
      exact ⟨Fin.castLE (tcoArity_le_card td r c) j, by simpa using j.isLt, hxm⟩
    have comp_disj : ∀ c ∈ td.children r q.t,
        ∀ (j j' : Fin (Fintype.card V + 1)),
          ((j : ℕ) < tcoArity td r c) → ((j' : ℕ) < tcoArity td r c) → j ≠ j' →
          ∀ x ∈ η (tokEnc td (c, j)), x ∉ η (tokEnc td (c, j')) := by
      intro c hc j j' hj hj' hne x hx hx'
      have hpw : (tup c).Pairwise List.Disjoint :=
        (List.nodup_flatten.mp (child_tuple c hc).2).2
      rw [List.pairwise_iff_getElem] at hpw
      have hj_len : (j : ℕ) < (tup c).length := by rw [htup_len]; exact hj
      have hj'_len : (j' : ℕ) < (tup c).length := by rw [htup_len]; exact hj'
      have hget : ∀ (jj : Fin (Fintype.card V + 1)) (hjj : (jj : ℕ) < (tup c).length),
          (tup c)[(jj : ℕ)] = η (tokEnc td (c, jj)) := by
        intro jj hjj
        simp only [htup_def, List.getElem_map, List.getElem_finRange]
        exact congrArg (fun x => η (tokEnc td (c, x))) (Fin.ext rfl)
      have hne_val : (j : ℕ) ≠ (j' : ℕ) := fun hcon => hne (Fin.ext hcon)
      rcases Nat.lt_or_ge (j : ℕ) (j' : ℕ) with hlt | hge
      · have hd := hpw (j : ℕ) (j' : ℕ) hj_len hj'_len hlt
        rw [hget j hj_len, hget j' hj'_len] at hd
        exact hd hx hx'
      · have hlt' : (j' : ℕ) < (j : ℕ) := lt_of_le_of_ne hge (Ne.symm hne_val)
        have hd := hpw (j' : ℕ) (j : ℕ) hj'_len hj_len hlt'
        rw [hget j hj_len, hget j' hj'_len] at hd
        exact hd hx' hx
    -- ## The output, re-expressed at token level.
    have houtput : ((mkProd td r q).lhs_strings.map (fun s =>
        (s.map (fun csym => match csym with
          | Sum.inl a => [a]
          | Sum.inr x => η x)).flatten)).flatten.Perm
        (q.flat.flatMap (tokExpand td η)) := by
      have hstrings : (mkProd td r q).lhs_strings.map (fun s =>
          (s.map (fun csym => match csym with
            | Sum.inl a => [a]
            | Sum.inr x => η x)).flatten) =
          (List.range (tcoArity td r q.t)).map
            (fun i => (q.comp i).flatMap (tokExpand td η)) := by
        show ((List.range (tcoArity td r q.t)).map
            (fun i => (q.comp i).map (tokToSym td))).map _ = _
        rw [List.map_map]
        refine List.map_congr_left ?_
        intro i _
        rw [Function.comp_apply, subst_map_eq td η (q.comp i),
          map_flatten_eq_flatMap]
      rw [hstrings, map_flatten_eq_flatMap, ← List.flatMap_assoc]
      have hperm : ((List.range (tcoArity td r q.t)).flatMap q.comp).Perm q.flat := by
        rw [← map_flatten_eq_flatMap]
        exact filter_partition_perm (tcoArity td r q.t) q.flat
          (fun tok => ((q.assign tok) : ℕ)) q.assign_lt
      exact hperm.flatMap (fun a _ => List.Perm.refl _)
    -- ## Token-level content and nodup.
    have htok_sub : ∀ tok ∈ q.flat, ∀ x ∈ tokExpand td η tok, x ∈ q.budget := by
      intro tok htok x hx
      cases tok with
      | inl v =>
        simp only [tokExpand, List.mem_singleton] at hx
        subst hx
        exact q.fresh_sub_budget ((q.term_iff x).mp htok)
      | inr pr =>
        obtain ⟨c, j⟩ := pr
        obtain ⟨hc, hj⟩ := (q.var_iff c j).mp htok
        have := comp_sub c hc j hj x hx
        exact (Finset.mem_sdiff.mp (q.cb_sub c hc this)).1
    have htok_complete : ∀ x ∈ q.budget, ∃ tok ∈ q.flat, x ∈ tokExpand td η tok := by
      intro x hx
      rw [q.cover] at hx
      rcases Finset.mem_union.mp hx with hfresh | hchild
      · exact ⟨Sum.inl x, (q.term_iff x).mpr hfresh, by simp [tokExpand]⟩
      · obtain ⟨c, hc, hxc⟩ := Finset.mem_biUnion.mp hchild
        obtain ⟨j, hj, hxj⟩ := comp_complete c hc x hxc
        exact ⟨Sum.inr (c, j), (q.var_iff c j).mpr ⟨hc, hj⟩, hxj⟩
    have htok_nodup : ∀ tok ∈ q.flat, (tokExpand td η tok).Nodup := by
      intro tok htok
      cases tok with
      | inl v => simp [tokExpand]
      | inr pr =>
        obtain ⟨c, j⟩ := pr
        obtain ⟨hc, hj⟩ := (q.var_iff c j).mp htok
        exact comp_nodup c hc j hj
    have htok_disj : ∀ tok ∈ q.flat, ∀ tok' ∈ q.flat, tok ≠ tok' →
        ∀ x ∈ tokExpand td η tok, x ∉ tokExpand td η tok' := by
      intro tok htok tok' htok' hne x hx hx'
      cases tok with
      | inl v =>
        simp only [tokExpand, List.mem_singleton] at hx
        subst hx
        have hv_fresh : x ∈ q.fresh := (q.term_iff x).mp htok
        cases tok' with
        | inl v' =>
          simp only [tokExpand, List.mem_singleton] at hx'
          exact hne (by rw [hx'])
        | inr pr' =>
          obtain ⟨c', j'⟩ := pr'
          obtain ⟨hc', hj'⟩ := (q.var_iff c' j').mp htok'
          have := comp_sub c' hc' j' hj' x hx'
          exact (Finset.mem_sdiff.mp (q.cb_sub c' hc' this)).2 hv_fresh
      | inr pr =>
        obtain ⟨c, j⟩ := pr
        obtain ⟨hc, hj⟩ := (q.var_iff c j).mp htok
        have hx_cb : x ∈ q.cb c := comp_sub c hc j hj x hx
        cases tok' with
        | inl v' =>
          simp only [tokExpand, List.mem_singleton] at hx'
          subst hx'
          have hv_fresh : x ∈ q.fresh := (q.term_iff x).mp htok'
          exact (Finset.mem_sdiff.mp (q.cb_sub c hc hx_cb)).2 hv_fresh
        | inr pr' =>
          obtain ⟨c', j'⟩ := pr'
          obtain ⟨hc', hj'⟩ := (q.var_iff c' j').mp htok'
          have hx'_cb : x ∈ q.cb c' := comp_sub c' hc' j' hj' x hx'
          by_cases hcc : c = c'
          · subst hcc
            have hjj : j ≠ j' := by
              intro hj_eq
              exact hne (by rw [hj_eq])
            exact comp_disj c hc j j' hj hj' hjj x hx hx'
          · exact (Finset.disjoint_left.mp (q.cb_disj c hc c' hc' hcc)) hx_cb hx'_cb
    -- ## Assemble.
    have hflat_nodup : (q.flat.flatMap (tokExpand td η)).Nodup := by
      rw [← map_flatten_eq_flatMap]
      exact flatten_expand_nodup q.flat (tokExpand td η) q.flat_nodup
        htok_nodup htok_disj
    have hflat_toFinset : (q.flat.flatMap (tokExpand td η)).toFinset = q.budget := by
      ext x
      rw [List.mem_toFinset, ← map_flatten_eq_flatMap, List.mem_flatten]
      constructor
      · rintro ⟨m, hm, hxm⟩
        obtain ⟨tok, htok, rfl⟩ := List.mem_map.mp hm
        exact htok_sub tok htok x hxm
      · intro hx
        obtain ⟨tok, htok, hxtok⟩ := htok_complete x hx
        exact ⟨tokExpand td η tok, List.mem_map.mpr ⟨tok, htok, rfl⟩, hxtok⟩
    -- The goal's substitution function and `houtput`'s are alpha-variants
    -- elaborated to distinct (but definitionally equal) matcher constants,
    -- so we finish with defeq-tolerant term applications instead of `rw`.
    constructor
    · ext x
      constructor
      · intro hx
        have hx2 : x ∈ q.flat.flatMap (tokExpand td η) :=
          houtput.mem_iff.mp (List.mem_toFinset.mp hx)
        have hxb : x ∈ q.budget := by
          rw [← hflat_toFinset]
          exact List.mem_toFinset.mpr hx2
        exact hxb
      · intro hx
        have hxb : x ∈ q.budget := hx
        have hx2 : x ∈ q.flat.flatMap (tokExpand td η) := by
          have := List.mem_toFinset.mp (hflat_toFinset.symm ▸ hxb)
          exact this
        exact List.mem_toFinset.mpr (houtput.mem_iff.mpr hx2)
    · exact houtput.nodup_iff.mpr hflat_nodup

/-! ### Completeness: an explicit depth-first derivation -/

/-- Decode a variable name back to its child-component pair. -/
noncomputable def tokDec (n : ℕ) : Option (td.I × Fin (Fintype.card V + 1)) :=
  if h : n < Fintype.card (td.I × Fin (Fintype.card V + 1)) then
    some ((Fintype.equivFin (td.I × Fin (Fintype.card V + 1))).symm ⟨n, h⟩)
  else none

theorem tokDec_tokEnc (pr : td.I × Fin (Fintype.card V + 1)) :
    tokDec td (tokEnc td pr) = some pr := by
  unfold tokDec tokEnc
  rw [dif_pos (Fin.is_lt _)]
  congr 1
  simpa using (Fintype.equivFin (td.I × Fin (Fintype.card V + 1))).symm_apply_apply pr

/-- Every nonterminal `(t, emitBelow t)` derives some tuple: the canonical
depth-first derivation.  By strong induction on subtree size. -/
theorem tco_derives_canonical :
    ∀ (n : ℕ) (t : td.I), td.subtreeSize r t ≤ n →
    ∃ ss : List (List V),
      (tcoGrammar td r).Generates (t, td.emitBelow r t) ss ∧
      ss.length = tcoArity td r t := by
  intro n
  induction n with
  | zero =>
    intro t ht
    exfalso
    have : 0 < td.subtreeSize r t := by
      unfold TreeDecomposition.subtreeSize
      refine Finset.card_pos.mpr ⟨t, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsDescendant_self td r t
    omega
  | succ n ihn =>
    intro t ht
    -- Child derivations, by induction.
    have hchild : ∀ c ∈ td.children r t,
        ∃ ss : List (List V),
          (tcoGrammar td r).Generates (c, td.emitBelow r c) ss ∧
          ss.length = tcoArity td r c := by
      intro c hc
      refine ihn c ?_
      have := subtreeSize_child_lt td hc
      omega
    classical
    -- Chosen child tuples.
    let ssF : td.I → List (List V) := fun c =>
      if hc : c ∈ td.children r t then (hchild c hc).choose else []
    have hssF_gen : ∀ c (hc : c ∈ td.children r t),
        (tcoGrammar td r).Generates (c, td.emitBelow r c) (ssF c) := by
      intro c hc
      simp only [ssF, dif_pos hc]
      exact (hchild c hc).choose_spec.1
    have hssF_len : ∀ c (hc : c ∈ td.children r t),
        (ssF c).length = tcoArity td r c := by
      intro c hc
      simp only [ssF, dif_pos hc]
      exact (hchild c hc).choose_spec.2
    -- The canonical arrangement: all fresh vertices, then all child
    -- components, everything in output component 0.
    have hassign0 : (0 : ℕ) < tcoArity td r t := tcoArity_pos td r t
    let flatT : List (TCOTok td) :=
      (td.emitAt t).toList.map Sum.inl ++
      (td.children r t).toList.flatMap (fun c =>
        (List.finRange (tcoArity td r c)).map
          (fun j => Sum.inr (c, Fin.castLE (tcoArity_le_card td r c) j)))
    have hflatT_nodup : flatT.Nodup := by
      rw [List.nodup_append']
      refine ⟨List.Nodup.map Sum.inl_injective (td.emitAt t).nodup_toList, ?_, ?_⟩
      · rw [List.nodup_flatMap]
        constructor
        · intro c _
          refine List.Nodup.map ?_ (List.nodup_finRange _)
          intro a b hab
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hab
          exact Fin.castLE_injective _ hab.2
        · refine ((td.children r t).nodup_toList).pairwise_of_forall_ne ?_
          intro c hc c' hc' hne x hx hx'
          obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
          obtain ⟨j', -, hx'⟩ := List.mem_map.mp hx'
          simp only [Sum.inr.injEq, Prod.mk.injEq] at hx'
          exact hne hx'.1.symm
      · intro x hx hx'
        obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
        obtain ⟨c, -, hj⟩ := List.mem_flatMap.mp hx'
        obtain ⟨j, -, hcon⟩ := List.mem_map.mp hj
        simp at hcon
    let param : TCOParam td r :=
      { t := t
        budget := td.emitBelow r t
        fresh := td.emitAt t
        cb := fun c => if c ∈ td.children r t then td.emitBelow r c else ∅
        flat := flatT
        assign := fun _ => ⟨0, by omega⟩
        flat_nodup := hflatT_nodup
        fresh_sub_budget := emitAt_subset_emitBelow td r t
        fresh_sub_bag := emitAt_subset_bag td t
        cb_sub := by
          intro c hc
          rw [if_pos hc]
          intro x hx
          rw [Finset.mem_sdiff]
          constructor
          · simp only [TreeDecomposition.emitBelow, Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, subtreeAt_child_subset td r t c hc hx.2⟩
          · exact fun hfr =>
              (Finset.disjoint_left.mp (emitAt_disjoint_emitBelow_child td hc)) hfr hx
        cb_disj := by
          intro c hc c' hc' hne
          rw [if_pos hc, if_pos hc']
          exact emitBelow_child_disjoint td hc hc' hne
        cover := by
          rw [emitBelow_decomp td r t]
          congr 1
          refine Finset.biUnion_congr rfl ?_
          intro c hc
          rw [if_pos hc]
        term_iff := by
          intro v
          constructor
          · intro hv
            rcases List.mem_append.mp hv with h | h
            · obtain ⟨w, hw, hww⟩ := List.mem_map.mp h
              rw [← Sum.inl_injective hww]
              exact Finset.mem_toList.mp hw
            · obtain ⟨c, -, hj⟩ := List.mem_flatMap.mp h
              obtain ⟨j, -, hcon⟩ := List.mem_map.mp hj
              simp at hcon
          · intro hv
            exact List.mem_append_left _
              (List.mem_map.mpr ⟨v, Finset.mem_toList.mpr hv, rfl⟩)
        var_iff := by
          intro c j
          constructor
          · intro hj
            rcases List.mem_append.mp hj with h | h
            · obtain ⟨w, -, hcon⟩ := List.mem_map.mp h
              simp at hcon
            · obtain ⟨c', hc', hj'⟩ := List.mem_flatMap.mp h
              obtain ⟨j', -, heq⟩ := List.mem_map.mp hj'
              simp only [Sum.inr.injEq, Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              exact ⟨Finset.mem_toList.mp hc', by simpa using j'.isLt⟩
          · rintro ⟨hc, hj⟩
            refine List.mem_append_right _ (List.mem_flatMap.mpr
              ⟨c, Finset.mem_toList.mpr hc, List.mem_map.mpr
                ⟨⟨(j : ℕ), hj⟩, List.mem_finRange _, ?_⟩⟩)
            exact congrArg (fun x => (Sum.inr (c, x) : TCOTok td)) (Fin.ext rfl)
        assign_lt := fun tok _ => hassign0 }
    -- The substitution: decode a name, look up the child tuple component.
    let η : ℕ → List V := fun nvar =>
      match tokDec td nvar with
      | some (c, j) => (ssF c).getD (j : ℕ) []
      | none => []
    have hη : ∀ (c : td.I) (j : Fin (Fintype.card V + 1)),
        η (tokEnc td (c, j)) = (ssF c).getD (j : ℕ) [] := by
      intro c j
      simp only [η, tokDec_tokEnc]
    -- Verify the RHS derivations.
    have hrhs : ∀ (i : Fin ((mkProd td r param).rhs).length),
        (tcoGrammar td r).Generates
          (((mkProd td r param).rhs).get i)
          ((((mkProd td r param).rhs_vars).get
            (i.cast (mkProd td r param).rhs_len.symm)).map η) := by
      intro i
      have hkid_len : ((mkProd td r param).rhs).length =
          ((td.children r t).toList).length := by
        simp [mkProd, param]
      have hc : ((td.children r t).toList).get (Fin.cast hkid_len i) ∈ td.children r t :=
        Finset.mem_toList.mp (List.get_mem _ _)
      set c := ((td.children r t).toList).get (Fin.cast hkid_len i) with hc_def
      have hrhs_i : ((mkProd td r param).rhs).get i = (c, td.emitBelow r c) := by
        simp only [mkProd, List.get_eq_getElem, List.getElem_map, Fin.coe_cast]
        rw [show (td.children r t).toList[(i : ℕ)] = c from by
          simp [hc_def, List.get_eq_getElem]]
        show (c, param.cb c) = (c, td.emitBelow r c)
        show (c, if c ∈ td.children r t then td.emitBelow r c else ∅) =
          (c, td.emitBelow r c)
        rw [if_pos hc]
      have hvars_i : ((mkProd td r param).rhs_vars).get
          (i.cast (mkProd td r param).rhs_len.symm) = param.varNames c := by
        simp only [mkProd, List.get_eq_getElem, List.getElem_map, Fin.coe_cast]
        rw [show (td.children r t).toList[(i : ℕ)] = c from by
          simp [hc_def, List.get_eq_getElem]]
      rw [hrhs_i, hvars_i]
      have hmap : (param.varNames c).map η = ssF c := by
        apply List.ext_getElem
        · simp [TCOParam.varNames, hssF_len c hc]
        · intro i' h1 h2
          have hi' : i' < tcoArity td r c := by
            simpa [TCOParam.varNames] using h1
          rw [List.getElem_map]
          have hv : (param.varNames c)[i']'(by
              simpa [TCOParam.varNames] using hi') =
              tokEnc td (c, ⟨i', lt_of_lt_of_le hi' (tcoArity_le_card td r c)⟩) := by
            simp only [TCOParam.varNames, List.getElem_map, List.getElem_finRange]
            exact congrArg (tokEnc td) (Prod.ext rfl (Fin.ext (by simp)))
          rw [hv, hη]
          exact List.getD_eq_getElem (ssF c) [] h2
      rw [hmap]
      exact hssF_gen c hc
    -- Apply the production.
    have hmem : mkProd td r param ∈ (tcoGrammar td r).productions :=
      List.mem_map.mpr ⟨param, Finset.mem_toList.mpr (Finset.mem_univ _), rfl⟩
    have hgen := MCFG.Generates.prod (G := tcoGrammar td r)
      (mkProd td r param) hmem η hrhs
    refine ⟨_, hgen, ?_⟩
    simp [mkProd, param]

end TCO

/-! ### The replacement theorems -/

section Replacement

open Classical

universe u'

variable {V : Type u'} [DecidableEq V] [Fintype V] {H : Hypergraph V}

/-- Tree-compatible orderings are duplicate-free enumerations of `H.verts`.
Formerly an axiom; now a consequence of the budget invariant. -/
theorem isTreeCompatibleOrdering_spec
    {td : TreeDecomposition H} {r : td.I}
    {perm : List V}
    (h : IsTreeCompatibleOrdering td r perm) :
    perm.toFinset = H.verts ∧ perm.Nodup := by
  have := tco_generates_invariant td r ((tcoGrammar td r).S) [perm] h
  simpa using this

/-- Every rooted tree decomposition admits a tree-compatible ordering.
Formerly an axiom; now witnessed by the canonical depth-first derivation. -/
theorem isTreeCompatibleOrdering_nonempty
    (td : TreeDecomposition H) (r : td.I) :
    ∃ (perm : List V), IsTreeCompatibleOrdering td r perm := by
  obtain ⟨ss, hgen, hlen⟩ :=
    tco_derives_canonical td r (td.subtreeSize r r) r (le_refl _)
  rw [tcoArity_root td r] at hlen
  obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨w, ?_⟩
  unfold IsTreeCompatibleOrdering MCFG.Language
  have hroot : ((r, td.emitBelow r r) : (tcoGrammar td r).N) = (tcoGrammar td r).S := by
    show ((r, td.emitBelow r r) : td.I × Finset V) = (r, H.verts)
    rw [emitBelow_root td r]
  simp only [Set.mem_setOf_eq]
  rw [← hroot]
  exact hgen

/-- The interface consumed by the bridge theorem: a grammar for exactly the
tree-compatible orderings.  The former over-specified record (node maps,
boundary arities, bag-local terminals, child fields) has been slimmed to the
fields actually used downstream. -/
structure StructuredMCFG (td : TreeDecomposition H) (r : td.I) where
  grammar : MCFG.{u', u'} V
  /-- Completeness: every tree-compatible ordering is generated. -/
  lang_complete : ∀ (perm : List V),
    IsTreeCompatibleOrdering td r perm → perm ∈ grammar.Language
  /-- Soundness: everything generated is a tree-compatible ordering. -/
  lang_sound : ∀ (perm : List V), perm ∈ grammar.Language →
    perm.toFinset = H.verts ∧ perm.Nodup ∧ IsTreeCompatibleOrdering td r perm

/-- **The bounded-width ordering grammar.**  Formerly the axiom
`engelfriet_tw_to_mcfl`, which attributed to Engelfriet (1997) a bespoke
statement not present in that work; now a theorem about the explicit
construction above.  The name is kept so downstream proofs are unchanged.
The construction technique follows Engelfriet–Heyker (1991) string yields;
the statement itself is proved here, not imported. -/
theorem engelfriet_tw_to_mcfl
    (V : Type u') [DecidableEq V] [Fintype V]
    (H : Hypergraph V)
    (td : TreeDecomposition H) (r : td.I)
    (k : ℕ) (hk : td.width ≤ k) :
    ∃ (S : StructuredMCFG td r),
      S.grammar.dimension ≤ k + 1 := by
  refine ⟨⟨tcoGrammar td r, fun _ h => h, fun perm h => ?_⟩,
    tcoGrammar_dimension_le td r k hk⟩
  obtain ⟨h1, h2⟩ := isTreeCompatibleOrdering_spec (td := td) (r := r) h
  exact ⟨h1, h2, h⟩

end Replacement
