/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Axioms
import AsymptoticBB.TreeDecomposition.Boundary
import AsymptoticBB.TreeDecomposition.Locality
import AsymptoticBB.Grammars.Refinement
import Mathlib.Data.Fintype.Pi

/-!
# Bridge Theorem

Theorem 11.3: If an embodied agent's constraint hypergraph has treewidth ≤ k,
then its behavior language is a (k+1)-MCFL.

The behavior language is defined via tree-compatible orderings: for a given
tree decomposition (td, r), a behavior string arises from a satisfying
assignment and a tree-compatible ordering of all variables, projecting
onto action variables. The bridge theorem constructs a (k+1)-MCFG
generating exactly this language by composing Engelfriet's construction
with an encoding homomorphism and finite union over satisfying assignments.
-/

set_option autoImplicit false

universe u v

noncomputable section BehaviorGrammar

open Classical

variable {V : Type u} [DecidableEq V] [Fintype V]
         {D : V → Type v} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]

/-- A partial assignment to a finite set of variables.
Equivalently: a dependent function from the subtype {v | v ∈ S}. -/
def PartialAssignment (D : V → Type v) (S : Finset V) :=
  (v : S) → D v.val

/-- PartialAssignment is Fintype when domains are Fintype. -/
noncomputable instance PartialAssignment.instFintype (S : Finset V) :
    Fintype (PartialAssignment D S) := by
  unfold PartialAssignment
  infer_instance

/-- PartialAssignment has DecidableEq when domains do. -/
instance PartialAssignment.instDecidableEq (S : Finset V) :
    DecidableEq (PartialAssignment D S) := by
  unfold PartialAssignment
  infer_instance

/-- Evaluate a partial assignment at a variable known to be in the domain. -/
def PartialAssignment.eval {S : Finset V} (σ : PartialAssignment D S)
    (v : V) (hv : v ∈ S) : D v :=
  σ ⟨v, hv⟩

/-- A partial assignment is consistent if it satisfies all constraints
whose scope is fully contained in S. -/
def PartialAssignment.IsConsistent (P : CSP V D) (S : Finset V)
    (σ : PartialAssignment D S) : Prop :=
  ∀ c ∈ P.constraints, (h : c.scope.toFinset ⊆ S) →
    c.relation (fun i => σ.eval (c.scope.get i)
      (h (List.mem_toFinset.mpr (c.scope.get_mem i))))

/-- The type of consistent partial assignments to S. -/
def ConsistentPartialAssignment (P : CSP V D) (S : Finset V) :=
  { σ : PartialAssignment D S // σ.IsConsistent P S }

/-- ConsistentPartialAssignment is Fintype (using classical decidability). -/
noncomputable instance ConsistentPartialAssignment.instFintype
    (P : CSP V D) (S : Finset V) : Fintype (ConsistentPartialAssignment P S) := by
  unfold ConsistentPartialAssignment
  haveI : DecidablePred (PartialAssignment.IsConsistent P S) := Classical.decPred _
  exact Subtype.fintype _

/-- ConsistentPartialAssignment has DecidableEq. -/
instance ConsistentPartialAssignment.instDecidableEq
    (P : CSP V D) (S : Finset V) : DecidableEq (ConsistentPartialAssignment P S) :=
  inferInstanceAs (DecidableEq { σ : PartialAssignment D S // _ })

/-- The nonterminal type for the behavior grammar:
pairs (t, σ) where t is a tree node and σ is a consistent assignment
to the boundary of t. -/
def BehaviorNonterminal {H : Hypergraph V} (P : CSP V D)
    (td : TreeDecomposition H) (r : td.I) :=
  Σ (t : td.I), ConsistentPartialAssignment P (td.boundary r t)

/-- BehaviorNonterminal is Fintype. -/
noncomputable instance BehaviorNonterminal.instFintype {H : Hypergraph V} (P : CSP V D)
    (td : TreeDecomposition H) (r : td.I) :
    Fintype (BehaviorNonterminal P td r) := by
  unfold BehaviorNonterminal
  exact Sigma.instFintype

/-- BehaviorNonterminal has DecidableEq. -/
instance BehaviorNonterminal.instDecidableEq {H : Hypergraph V} (P : CSP V D)
    (td : TreeDecomposition H) (r : td.I) :
    DecidableEq (BehaviorNonterminal P td r) := by
  unfold BehaviorNonterminal
  infer_instance

/-- The arity of a behavior nonterminal: max(1, |boundary|).
We use max(1, ...) to satisfy the MCFG requirement ar ≥ 1. -/
def BehaviorNonterminal.arity {H : Hypergraph V} {P : CSP V D}
    {td : TreeDecomposition H} {r : td.I}
    (A : BehaviorNonterminal P td r) : ℕ :=
  max 1 (td.boundary r A.1).card

/-- Arity is always positive. -/
theorem BehaviorNonterminal.arity_pos {H : Hypergraph V} {P : CSP V D}
    {td : TreeDecomposition H} {r : td.I}
    (A : BehaviorNonterminal P td r) : 0 < A.arity := by
  unfold arity
  exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left 1 _)

/-- Arity is bounded by k+1 when td.width ≤ k. -/
theorem BehaviorNonterminal.arity_le {H : Hypergraph V} {P : CSP V D}
    {td : TreeDecomposition H} {r : td.I}
    (A : BehaviorNonterminal P td r)
    (k : ℕ) (hk : td.width ≤ k) : A.arity ≤ k + 1 := by
  unfold arity
  apply Nat.max_le.mpr
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
  · exact boundary_card_le td r A.1 k hk

/-- Restrict a global assignment to a boundary, yielding a partial assignment. -/
def restrictToBoundary {H : Hypergraph V}
    (td : TreeDecomposition H) (r t : td.I)
    (β : ∀ v : V, D v) : PartialAssignment D (td.boundary r t) :=
  fun ⟨v, _⟩ => β v

/-- Restricting a satisfying assignment yields a consistent partial assignment. -/
theorem restrictToBoundary_consistent {H : Hypergraph V}
    (P : CSP V D) (td : TreeDecomposition H) (r t : td.I)
    (β : ∀ v : V, D v) (hsat : P.IsSatisfying β) :
    (restrictToBoundary td r t β).IsConsistent P (td.boundary r t) := by
  intro c hc hscope
  -- β satisfies c, and we're just restricting
  have hsat_c := hsat c hc
  -- The restriction evaluates to β on each variable in scope
  simp only [restrictToBoundary, PartialAssignment.eval, PartialAssignment.IsConsistent] at *
  exact hsat_c

/-- Helper: mapping with conditional singleton then flattening equals filter-then-map.
(l.map (fun a => if p a then [f a] else [])).flatten = (l.filter (decide ∘ p)).map f -/
private theorem list_map_ite_flatten_eq_filter_map {α β : Type*} (l : List α)
    (p : α → Prop) [DecidablePred p] (f : α → β) :
    (l.map (fun a => if p a then [f a] else [])).flatten =
      (l.filter (fun a => decide (p a))).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.filter_cons]
    by_cases h : p x
    · simp [h, decide_eq_true h, ih]
    · simp [h, decide_eq_false h, ih]

/-! ## Tree-Structured Behavior Language -/

/-- The tree-structured behavior language of an embodied agent.
(Definition 7.6)

Given a tree decomposition (td, r) of the agent's constraint hypergraph,
a behavior string arises from:
(i) a satisfying assignment β ∈ Sol(P), and
(ii) a tree-compatible ordering `perm` of all variables V
     (w.r.t. the tree decomposition),
where non-action variables are deleted and action variables are encoded.

The execution order respects the constraint hypergraph's tree structure —
the agent linearizes its variables in an order consistent with the
tree decomposition's bag separation.

Since different tree decompositions of the same hypergraph yield different
sets of tree-compatible orderings, the behavior language depends on the
choice of (td, r). This is natural: the tree decomposition represents the
agent's internal scheduling strategy. -/
def EmbodiedAgent.TreeBehaviorLanguage [Fintype V]
    (A : EmbodiedAgent V D)
    (td : TreeDecomposition A.constraintHypergraph) (r : td.I)
    (Sym : Type*) (encode : (v : V) → D v → Sym) : Set (List Sym) :=
  { w | ∃ (β : ∀ v : V, D v),
        A.toCSP.IsSatisfying β ∧
        ∃ (perm : List V),
          IsTreeCompatibleOrdering td r perm ∧
          w = (perm.map (fun v =>
            if v ∈ A.action_vars then [encode v (β v)] else [])).flatten }

theorem behavior_grammar_exists
    (A : EmbodiedAgent V D)
    (td : TreeDecomposition A.constraintHypergraph)
    (r : td.I)
    (k : ℕ) (hk : td.width ≤ k)
    (Sym : Type*) (encode : (v : V) → D v → Sym) :
    ∃ (G_beh : MCFG Sym),
      G_beh.dimension ≤ k + 1 ∧
      G_beh.Language = A.TreeBehaviorLanguage td r Sym encode := by
  -- Step 1: Ordering grammar from Engelfriet (Theorems 5.8 + 5.9)
  obtain ⟨S_ord, hdim⟩ := @engelfriet_tw_to_mcfl.{_, 0} V _ _ A.constraintHypergraph td r k hk
  -- Step 2: Encoding homomorphism — action vars encoded, non-action deleted
  let h_β : (∀ v : V, D v) → V → List Sym := fun β v =>
    if v ∈ A.action_vars then [encode v (β v)] else []
  -- Step 3: Index homomorphic images by satisfying assignments
  let ι := { β : ∀ v : V, D v // A.toCSP.IsSatisfying β }
  haveI : Fintype ι := by
    haveI : DecidablePred A.toCSP.IsSatisfying := Classical.decPred _
    exact Subtype.fintype _
  let L_β : ι → Set (List Sym) := fun ⟨β, _⟩ =>
    { w | ∃ w' ∈ S_ord.grammar.Language, w = (w'.map (h_β β)).flatten }
  -- Steps 4-5: Homomorphism closure + finite union → single (k+1)-MCFG
  obtain ⟨G, hGdim, hGlang⟩ := @mcfg_finite_union.{_, _, 0, _} _ _ _ L_β (k + 1) (fun ⟨β, _⟩ =>
    let ⟨G', hG'dim, hG'lang⟩ := @mcfg_homomorphic_image.{_, _, 0, 0} _ _ S_ord.grammar (h_β β)
    ⟨G', le_trans hG'dim hdim, hG'lang⟩)
  refine ⟨G, hGdim, ?_⟩
  -- Step 6: ⋃_β h_β(L(S_ord)) = TreeBehaviorLanguage
  -- This is now direct because lang_complete/lang_sound characterize
  -- L(S_ord) = {tree-compatible orderings}, and TreeBehaviorLanguage
  -- is defined using exactly tree-compatible orderings.
  rw [hGlang]
  ext w
  simp only [Set.mem_iUnion, EmbodiedAgent.TreeBehaviorLanguage, Set.mem_setOf_eq]
  constructor
  · -- Soundness: w ∈ ⋃_β h_β(L(S_ord)) → w ∈ TreeBehaviorLanguage
    rintro ⟨⟨β, hβ_sat⟩, perm, hperm_lang, rfl⟩
    obtain ⟨_, _, hperm_compat⟩ := S_ord.lang_sound perm hperm_lang
    exact ⟨β, hβ_sat, perm, hperm_compat, rfl⟩
  · -- Completeness: w ∈ TreeBehaviorLanguage → w ∈ ⋃_β h_β(L(S_ord))
    rintro ⟨β, hβ_sat, perm, hperm_compat, rfl⟩
    exact ⟨⟨β, hβ_sat⟩, perm,
      S_ord.lang_complete perm hperm_compat, rfl⟩

end BehaviorGrammar

/-! ## The Bridge Theorem -/

/-- **Theorem 11.3 (Bridge theorem, universal form).**

Let `A` be an embodied agent whose constraint hypergraph has `tw(H) ≤ k`.
Then for **every** tree decomposition `td` of `A.constraintHypergraph` with
`td.width ≤ k` and every root `r : td.I`, the tree-structured behavior
language `L(A, td, r)` is a `(k+1)`-MCFL.

This is the "witness" form of the bridge theorem: the dimension bound
`(k+1)`-MCFL is invariant under the choice of width-`≤k` decomposition.
Different decompositions yield different languages (they reorder the
readout of action variables along different tree-compatible linearizations),
but all such languages lie in the same class. The tree decomposition
therefore plays the role of a witness for the complexity bound rather than
a semantic parameter that changes it. -/
theorem bridge_theorem_forall {V : Type u} [DecidableEq V] [Fintype V]
    {D : V → Type v} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
    (A : EmbodiedAgent V D) (k : ℕ)
    (Sym : Type*) (encode : (v : V) → D v → Sym)
    (td : TreeDecomposition A.constraintHypergraph) (r : td.I)
    (hwidth : td.width ≤ k) :
    IsMCFL (A.TreeBehaviorLanguage td r Sym encode) (k + 1) := by
  obtain ⟨G_beh, hdim, hlang⟩ := behavior_grammar_exists A td r k hwidth Sym encode
  exact ⟨G_beh, hdim, hlang⟩

/-- **Theorem 11.3 (Bridge theorem, existential corollary).**

Existential packaging of `bridge_theorem_forall`: given `tw(H) ≤ k`, there
exists at least one decomposition `(td, r)` of width `≤ k` for which
`L(A, td, r)` is a `(k+1)`-MCFL. This form exists for compatibility with
downstream statements that choose a witness; by `bridge_theorem_forall`,
any width-`≤k` witness would work equally well. -/
theorem bridge_theorem {V : Type u} [DecidableEq V] [Fintype V]
    {D : V → Type v} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
    (A : EmbodiedAgent V D) (k : ℕ)
    (Sym : Type*) (encode : (v : V) → D v → Sym)
    (htw : A.constraintHypergraph.HasTreewidthAtMost k) :
    ∃ (td : TreeDecomposition A.constraintHypergraph) (r : td.I),
      IsMCFL (A.TreeBehaviorLanguage td r Sym encode) (k + 1) := by
  obtain ⟨td, hwidth⟩ := htw
  obtain ⟨r⟩ := td.instNonemptyI
  exact ⟨td, r, bridge_theorem_forall A k Sym encode td r hwidth⟩
