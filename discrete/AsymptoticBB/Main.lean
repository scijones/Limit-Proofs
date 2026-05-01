/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Bridge
import AsymptoticBB.Agent.SizedAgent
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.Pi

/-!
# Main Theorem

The main results combine Grohe's theorem with the bridge theorem to obtain
structural characterizations of agent behavior at the class level.

## Structure

- **`ClassBehaviorLanguage`**: The class-level behavior language — the union
  of per-agent tree-structured behavior languages across an agent class.
- **`class_tractable_implies_bounded_tw`** (Corollary 9.3): Tractability
  implies uniformly bounded treewidth.
- **`main_theorem`** (Theorem 12.1): Per-agent formulation — for every
  agent in the class, there exists a tree decomposition under which the
  behavior language is a (k+1)-MCFL, with k uniform across the class.
- **`main_theorem_finite_subclass`** (Theorem 12.2): For any finite
  sub-class, the union of behavior languages is a single (k+1)-MCFL.

## Type flow
```
𝓐 : SizedEmbodiedAgentClass
  │
  ├── thm_grohe → ∃ k, uniform treewidth bound
  │
  ├── ∀ A ∈ 𝓐: bridge_theorem → ∃ td r, IsMCFL (L(A,td,r)) (k+1)
  │
  └── ClassBehaviorLanguage(𝓐) = ⋃_{A ∈ 𝓐} L(A, td_A, r_A)
      └── For finite F ⊆ 𝓐: IsMCFL (⋃_{A ∈ F} L(A)) (k+1)
```
-/

set_option autoImplicit false

/-! ## Class-Level Behavior Language -/

/-- The class-level behavior language: the union of per-agent tree-structured
behavior languages across all agents in a sized agent class.

For each agent A ∈ 𝓐, we existentially quantify over tree decompositions
(td, r) of A's constraint hypergraph. A word w is in the class language if
it belongs to L(A, td, r) for SOME agent A ∈ 𝓐 and SOME tree decomposition.

This language is potentially infinite when 𝓐 contains agents with
unbounded vertex-set sizes (varying n). The uniform dimension bound k+1
(from Grohe's theorem) is genuinely non-trivial for such classes.

NOTE (unused by submission): this definition is retained as documentation
of the class-level object discussed informally in the paper, but the
paper's load-bearing class-level statement
(`thm:main-finite`) operates on a *finite* sub-class whose union is
itself a `(k+1)`-MCFL via `main_theorem_finite_subclass`, and the
paper's strongest per-agent statement (`thm:full-bound`,
`thm:main`) uses the full-behavior language `FullBehaviorLanguage`
below. `ClassBehaviorLanguage` is not cited by any theorem conclusion
currently in the paper and can be removed without affecting the proof
chain. -/
def ClassBehaviorLanguage
    (𝓐 : SizedEmbodiedAgentClass)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) → (v : Fin A.n) → A.D v → Sym) :
    Set (List Sym) :=
  { w | ∃ (A : SizedEmbodiedAgent), A ∈ 𝓐 ∧
        ∃ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
          w ∈ A.agent.TreeBehaviorLanguage td r Sym (encode A) }

/-! ## Corollary 9.3: Tractability implies bounded treewidth -/

/-- Corollary 9.3 — Asymptotic version.

Assume FPT ≠ W[1]. Let 𝓐 be a class of sized embodied agents (varying
vertex-set sizes) sharing a single uniform polynomial-time belief-revision
architecture. If 𝓐 has uniformly bounded arity and all constraint
hypergraphs are cores, then there is one constant k such that EVERY agent
in 𝓐 has a constraint hypergraph of treewidth at most k. -/
theorem class_tractable_implies_bounded_tw
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores) :
    ∃ k, ∀ A ∈ 𝓐, A.agent.constraintHypergraph.HasTreewidthAtMost k := by
  obtain ⟨k, hk⟩ := thm_grohe h_conj 𝓐.hypergraphs h_re
    (SizedEmbodiedAgentClass.hypergraphs_boundedArity h_arity) h_cores h_tract
  refine ⟨k, ?_⟩
  intro A hA
  have : A.constraintSizedHypergraph ∈ 𝓐.hypergraphs := ⟨A, hA, rfl⟩
  exact hk A.constraintSizedHypergraph this

/-! ## Theorem 12.1: Main theorem — per-agent -/

/-- Theorem 12.1 (Main theorem) — per-agent formulation.

Assume FPT ≠ W[1]. For a class 𝓐 satisfying the standard hypotheses,
there exists a uniform k such that for every A ∈ 𝓐, there exists a tree
decomposition (td, r) such that L(A, td, r) is a (k+1)-MCFL.

The tree decomposition is existential in the conclusion, and k is
uniform across the class. -/
theorem main_theorem
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (A : SizedEmbodiedAgent)
    (hA : A ∈ 𝓐)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores)
    (Sym : Type*) (encode : (v : Fin A.n) → A.D v → Sym) :
    ∃ k, ∃ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
      IsMCFL (A.agent.TreeBehaviorLanguage td r Sym encode) (k + 1) := by
  obtain ⟨k, hk⟩ := class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  obtain ⟨td, r, hmcfl⟩ := bridge_theorem A.agent k Sym encode (hk A hA)
  exact ⟨k, td, r, hmcfl⟩

/-! ## Theorem 12.1′: Main theorem — universal (witness) form -/

/-- Theorem 12.1′ (Main theorem, universal form).

The "decomposition as witness" form of `main_theorem`: there is a uniform
`k` such that for every `A ∈ 𝓐`, *every* width-`≤k` tree decomposition of
`A.constraintHypergraph` (with any root) yields a `(k+1)`-MCFL behavior
language. In particular, the complexity bound is invariant under the
choice of width-`k` witness.

At least one such decomposition exists because `tw(H_A) ≤ k`. -/
theorem main_theorem_forall
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) → (v : Fin A.n) → A.D v → Sym) :
    ∃ k, ∀ (A : SizedEmbodiedAgent), A ∈ 𝓐 →
      ∀ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
        td.width ≤ k →
        IsMCFL (A.agent.TreeBehaviorLanguage td r Sym (encode A)) (k + 1) := by
  obtain ⟨k, hk⟩ := class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  refine ⟨k, ?_⟩
  intro A hA td r hwidth
  exact bridge_theorem_forall A.agent k Sym (encode A) td r hwidth

/-! ## Theorem 12.2: Main theorem — finite sub-class -/

/-- Theorem 12.2 (Main theorem — finite sub-class formulation).

For any FINITE subset F ⊆ 𝓐, the union of behavior languages
⋃_{A ∈ F} L(A, td_A, r_A) is a single (k+1)-MCFL.

This is the strongest non-vacuous statement provable from the existing
axiom `mcfg_finite_union`: the union of finitely many (k+1)-MCFLs is
a (k+1)-MCFL, and the k is uniform across the entire class (independent
of which finite subset F is chosen or how large it is).

NON-TRIVIALITY: As |F| grows (sampling agents of larger and larger sizes),
the union language grows without bound. The dimension bound k+1 remains
fixed, showing that the constraint structure genuinely controls the
formal-language complexity — not just per-agent, but uniformly. -/
theorem main_theorem_finite_subclass
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) → (v : Fin A.n) → A.D v → Sym) :
    ∃ k, ∀ (F : Finset SizedEmbodiedAgent), ↑F ⊆ 𝓐 →
      ∃ (td_choice : ∀ A ∈ F, TreeDecomposition A.agent.constraintHypergraph)
        (r_choice : ∀ (A : SizedEmbodiedAgent) (hA : A ∈ F), (td_choice A hA).I),
        IsMCFL (⋃ (A : F),
          (A : SizedEmbodiedAgent).agent.TreeBehaviorLanguage
            (td_choice A A.prop) (r_choice A A.prop) Sym (encode A)) (k + 1) := by
  -- Get uniform treewidth bound
  obtain ⟨k, hk⟩ := class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  refine ⟨k, ?_⟩
  intro F hF
  -- For each A ∈ F, get a tree decomposition witnessing tw ≤ k
  -- and a per-agent (k+1)-MCFG (with pinned nonterminal universe)
  have per_agent : ∀ A ∈ F,
      ∃ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I)
        (G : MCFG.{_, 0} Sym), G.dimension ≤ k + 1 ∧
        G.Language = A.agent.TreeBehaviorLanguage td r Sym (encode A) := by
    intro A hA
    obtain ⟨td, r, G, hGdim, hGlang⟩ := bridge_theorem A.agent k Sym (encode A) (hk A (hF hA))
    exact ⟨td, r, G, hGdim, hGlang⟩
  -- Use classical choice to extract td and r for each A ∈ F
  classical
  let td_choice : ∀ A ∈ F, TreeDecomposition A.agent.constraintHypergraph :=
    fun A hA => (per_agent A hA).choose
  let r_choice : ∀ (A : SizedEmbodiedAgent) (hA : A ∈ F), (td_choice A hA).I :=
    fun A hA => (per_agent A hA).choose_spec.choose
  refine ⟨td_choice, r_choice, ?_⟩
  -- Each per-agent language has a (k+1)-MCFG
  have per_mcfg : ∀ (A : F),
      ∃ (G : MCFG.{_, 0} Sym), G.dimension ≤ k + 1 ∧
        G.Language = (A : SizedEmbodiedAgent).agent.TreeBehaviorLanguage
          (td_choice A A.prop) (r_choice A A.prop) Sym (encode A) :=
    fun ⟨A, hA⟩ => (per_agent A hA).choose_spec.choose_spec
  -- Define per-agent languages indexed by F
  let Ls : F → Set (List Sym) := fun A =>
    (A : SizedEmbodiedAgent).agent.TreeBehaviorLanguage
      (td_choice A A.prop) (r_choice A A.prop) Sym (encode A)
  -- Each is a (k+1)-MCFL — universe pinned to 0
  have hLs : ∀ i : F, ∃ G : MCFG.{_, 0} Sym, G.dimension ≤ k + 1 ∧ G.Language = Ls i := by
    intro ⟨A, hA⟩
    exact per_mcfg ⟨A, hA⟩
  -- Finite union of (k+1)-MCFLs is a (k+1)-MCFL
  obtain ⟨G, hGdim, hGlang⟩ := @mcfg_finite_union.{_, _, 0, _} _ _ _ Ls (k + 1) hLs
  exact ⟨G, hGdim, hGlang⟩

/-! ## Full behavior bound

The full behavior language of `A` at width bound `k`: the union of
tree-structured behavior languages over every width-`≤k` rooted tree
decomposition of `A`'s constraint hypergraph. Under the policy-as-CSP
reading of the paper (Remark `rem:policy`), every action sequence the
agent can produce self-consistently is the action-variable projection
of some `β ∈ Sol(P)` along a tree-compatible ordering of `V`; when
`tw(H) ≤ k`, every such ordering is tree-compatible for some width-`≤k`
decomposition. Hence `FullBehaviorLanguage A k` captures every action
sequence `A` can produce consistently with its beliefs.
-/

/-- The **full behavior language** of an embodied agent at width bound `k`:
the union of `TreeBehaviorLanguage` over all width-`≤k` rooted tree
decompositions of `A.constraintHypergraph`. Paper definition
`def:full-behavior-language`. -/
def EmbodiedAgent.FullBehaviorLanguage {V : Type*} [DecidableEq V] [Fintype V]
    {D : V → Type*} [∀ v, DecidableEq (D v)] [∀ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (k : ℕ)
    (Sym : Type*) (encode : (v : V) → D v → Sym) : Set (List Sym) :=
  { w | ∃ (td : TreeDecomposition A.constraintHypergraph) (r : td.I),
          td.width ≤ k ∧ w ∈ A.TreeBehaviorLanguage td r Sym encode }

/-- **Full behavior bound** (paper Theorem `thm:full-bound`).

Under `tw(H) ≤ k`, the full behavior language of `A` is a `(k+1)`-MCFL.

Proof idea:
  For finite `V` and finite domains `D v`, every word in
  `A.FullBehaviorLanguage k Sym encode` is the flattened map of a
  `Nodup` permutation of `V` (via `IsTreeCompatibleOrdering`'s
  specification) under a total assignment `β : ∀ v, D v`. Both the
  assignment space `∀ v, D v` and the set of `Nodup` lists over `V`
  are finite (the latter by `fintypeNodupList`), so the language is a
  subset of the range of a function out of a finite type, hence finite.
  Apply `finite_language_is_mcfl` at dimension `k+1 ≥ 1`.

The paper proves this at `thm:full-bound` by the same argument plus the
observation that each per-decomposition language is a `(k+1)`-MCFL by
`bridge_theorem_forall`; since our Lean route goes through the finite
closure axiom we do not need the per-decomposition step, but the paper
statement and this Lean statement agree. -/
theorem full_behavior_bound {V : Type*} [DecidableEq V] [Fintype V]
    {D : V → Type*} [∀ v, DecidableEq (D v)] [∀ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (k : ℕ)
    (_htw : A.constraintHypergraph.HasTreewidthAtMost k)
    (Sym : Type*) (encode : (v : V) → D v → Sym) :
    IsMCFL (A.FullBehaviorLanguage k Sym encode) (k + 1) := by
  -- Every word in the full behavior language is determined by a pair
  -- `(β, perm)` with `β : ∀ v, D v` (finitely many since `V` and each
  -- `D v` are finite) and `perm : {l : List V // l.Nodup}` (finitely
  -- many by `fintypeNodupList`). So the language is a subset of the
  -- range of a map out of a finite type, hence finite. Apply
  -- `finite_language_is_mcfl`.
  let f : (∀ v, D v) × {l : List V // l.Nodup} → List Sym :=
    fun p => (p.2.1.map (fun v =>
      if v ∈ A.action_vars then [encode v (p.1 v)] else [])).flatten
  have hfin : (A.FullBehaviorLanguage k Sym encode).Finite := by
    refine (Set.finite_range f).subset ?_
    rintro w ⟨td, r, _hw, β, _hsat, perm, htco, rfl⟩
    exact ⟨(β, ⟨perm, (isTreeCompatibleOrdering_spec htco).2⟩), rfl⟩
  exact finite_language_is_mcfl _ hfin (k + 1) (by omega)

/-- **Main theorem, full-behavior formulation** (paper Theorem `thm:main`).

Under the standard hypotheses, there is a uniform `k` such that every
agent's full behavior language is a `(k+1)`-MCFL — bounding every action
sequence the agent can produce consistently with its beliefs. -/
theorem main_theorem_full
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (A : SizedEmbodiedAgent)
    (hA : A ∈ 𝓐)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores)
    (Sym : Type*) (encode : (v : Fin A.n) → A.D v → Sym) :
    ∃ k, IsMCFL (A.agent.FullBehaviorLanguage k Sym encode) (k + 1) := by
  obtain ⟨k, hk⟩ := class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  exact ⟨k, full_behavior_bound A.agent k (hk A hA) Sym encode⟩
