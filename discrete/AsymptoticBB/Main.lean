/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Bridge
import AsymptoticBB.Agent.SizedAgent
import AsymptoticBB.Basic.Intendable
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
- **`main_theorem_finite_subclass`** and **`full_behavior_bound`** stitch
  finitely many already width-bounded behavior languages without changing
  their common MCFG tier.

## Type flow
```
𝓐 : SizedEmbodiedAgentClass
  │
  ├── thm_grohe → ∃ k, uniform treewidth bound
  │
  ├── ∀ A ∈ 𝓐: bridge_theorem → ∃ td r, IsMCFL (L(A,td,r)) (k+1)
  │
  └── finite behavior families are stitched by union at the same tier;
      k is still the uniform treewidth bound supplied by Grohe
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

This definition records the class-level object discussed informally in the
paper.  The active finite-subclass theorem applies finite union only after each
member language has been placed in the common width-derived tier. -/
def ClassBehaviorLanguage
    (𝓐 : SizedEmbodiedAgentClass)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) → (v : Fin A.n) → A.D v → Sym) :
    Set (List Sym) :=
  { w | ∃ (A : SizedEmbodiedAgent), A ∈ 𝓐 ∧
        ∃ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
          w ∈ A.agent.TreeBehaviorLanguage td r Sym (encode A) }

/-! ## Corollary 9.3: Tractability implies bounded treewidth -/

/-- Tractability implies bounded **core** treewidth — no minimality assumed.

Assume FPT ≠ W[1]. Let 𝓐 be a class of sized embodied agents sharing a
single uniform polynomial-time belief-revision architecture, with uniformly
bounded arity.  Then there is one constant `k` such that EVERY agent's
constraint hypergraph has a *core* of treewidth at most `k`.

This is the maximal-scope form: no `AllCores` hypothesis.  Tractability
cannot bound raw treewidth (padding is free), but it does bound the
treewidth of what the store is committed to — its core.  Direct from the
faithful (core-conclusion) form of Grohe's theorem. -/
theorem class_tractable_implies_bounded_core_tw
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity) :
    ∃ k, ∀ A ∈ 𝓐, ∃ K : SizedHypergraph,
      SizedHypergraph.CoreOf K A.constraintSizedHypergraph ∧
        K.HasTreewidthAtMost k := by
  obtain ⟨k, hk⟩ := (thm_grohe h_conj 𝓐.hypergraphs h_re
    (SizedEmbodiedAgentClass.hypergraphs_boundedArity h_arity) h_tract).1
  refine ⟨k, ?_⟩
  intro A hA
  exact hk A.constraintSizedHypergraph ⟨A, hA, rfl⟩

/-- Corollary 9.3 — Asymptotic version.

Assume FPT ≠ W[1]. Let 𝓐 be a class of sized embodied agents (varying
vertex-set sizes) sharing a single uniform polynomial-time belief-revision
architecture. If 𝓐 has uniformly bounded arity and all constraint
hypergraphs are cores, then there is one constant k such that EVERY agent
in 𝓐 has a constraint hypergraph of treewidth at most k.

The classes-of-cores instantiation of `thm_grohe` (its second conjunct). -/
theorem class_tractable_implies_bounded_tw
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores) :
    ∃ k, ∀ A ∈ 𝓐, A.agent.constraintHypergraph.HasTreewidthAtMost k := by
  obtain ⟨k, hk⟩ := (thm_grohe h_conj 𝓐.hypergraphs h_re
    (SizedEmbodiedAgentClass.hypergraphs_boundedArity h_arity) h_tract).2 h_cores
  refine ⟨k, ?_⟩
  intro A hA
  have : A.constraintSizedHypergraph ∈ 𝓐.hypergraphs := ⟨A, hA, rfl⟩
  exact hk A.constraintSizedHypergraph this

/-! ## Theorem 12.1: Main theorem — per-agent -/

/-! Theorem 12.1 (Main theorem) — per-agent formulation.

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
      IsMCFL.{_, 0} (A.agent.TreeBehaviorLanguage td r Sym encode) (k + 1) := by
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
        IsMCFL.{_, 0} (A.agent.TreeBehaviorLanguage td r Sym (encode A)) (k + 1) := by
  obtain ⟨k, hk⟩ := class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  refine ⟨k, ?_⟩
  intro A hA td r hwidth
  exact bridge_theorem_forall A.agent k Sym (encode A) td r hwidth

/-- **Schedule-class formulation.** There is one structural bound `k` such
that every class member has a width-`≤k` decomposition and every action
schedule language induced by any such rooted decomposition belongs to the same
`(k+1)`-MCFL class.

This states existence and class membership only.  It neither constructs a
scheduler nor asks the stitching argument to preserve a selected solution. -/
theorem main_theorem_schedule_class
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) → (v : Fin A.n) → A.D v → Sym) :
    ∃ k,
      (∀ A ∈ 𝓐, A.agent.constraintHypergraph.HasTreewidthAtMost k) ∧
      ∀ (A : SizedEmbodiedAgent), A ∈ 𝓐 →
        ∀ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
          td.width ≤ k →
          IsMCFL.{_, 0}
            (A.agent.TreeBehaviorLanguage td r Sym (encode A)) (k + 1) := by
  obtain ⟨k, hk⟩ :=
    class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  refine ⟨k, hk, ?_⟩
  intro A hA td r hwidth
  exact bridge_theorem_forall A.agent k Sym (encode A) td r hwidth

/-! ## Theorem 12.2: Main theorem — finite sub-class -/

/-! Theorem 12.2 (Main theorem — finite sub-class formulation).

For any FINITE subset F ⊆ 𝓐, the union of behavior languages
⋃_{A ∈ F} L(A, td_A, r_A) is a single (k+1)-MCFL.

The union of finitely many `(k+1)`-MCFLs is a `(k+1)`-MCFL, and `k` is
uniform across the entire class (independent of the chosen finite subset).
This is an existence statement: stitching does not preserve or select a
particular satisfying assignment or grammar witness. -/
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
        IsMCFL.{_, 0} (⋃ (A : F),
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
  obtain ⟨G, hGdim, hGlang⟩ :=
    @mcfg_finite_union _ _ _ Ls (k + 1) (Nat.le_add_left 1 k) hLs
  exact ⟨G, hGdim, hGlang⟩

/-! ## Full behavior bound

The full behavior language of `A` at width bound `k`: the union of
tree-structured behavior languages over every width-`≤k` rooted tree
decomposition of `A`'s constraint hypergraph.

SEMANTICS (emittable = schedulable). Under the policy-as-CSP reading of
the paper (Remark `rem:policy`), a behavior of `A` is an action sequence
that `A`'s own execution machinery can schedule. That machinery is the
same tractable belief-revision process whose tractability forces
`tw(H) ≤ k` (Grohe); its executions walk a width-`≤k` tree decomposition,
so the orderings it can realize are exactly the tree-compatible orderings
of some width-`≤k` rooted decomposition. `FullBehaviorLanguage A k` is
therefore the set of ALL behaviors emittable by `A` — not a subset of
some larger behavior set. Vertex orderings that are tree-compatible for
no width-`≤k` decomposition are not uncounted behaviors: they are strings
no tractable execution of this CSP can schedule, i.e. the bound is causal
(the same treewidth that makes revision tractable constrains emission
order), not merely descriptive. Multi-cycle histories are concatenations
/ Kleene star of per-cycle emissions, and both operations preserve MCFL
dimension (Seki et al. 1991), so the `(k+1)` bound extends to iterated,
self-correcting execution.
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

/-! **Full behavior bound** (paper Theorem `thm:full-bound`).

Under `tw(H) ≤ k`, the full behavior language of `A` is a `(k+1)`-MCFL.

Proof: We follow the paper's argument exactly.

  (1) For each width-`≤k` rooted tree decomposition `(td, r)` of
      `A.constraintHypergraph`, `bridge_theorem_forall` (via
      `behavior_grammar_exists`) constructs an explicit `(k+1)`-MCFG
      whose language is `TreeBehaviorLanguage A td r Sym encode`.
  (2) The set `S` of *distinct* per-decomposition languages is finite,
      because every such language is a subset of the range of the
      action-projection map `f : (∀ v, D v) × {l : List V // l.Nodup} →
      List Sym`, the range of `f` is finite, and the powerset of a
      finite set is finite.
  (3) `FullBehaviorLanguage A k Sym encode = ⋃_{L ∈ S} L`, so
      `mcfg_finite_union` produces a single `(k+1)`-MCFG generating it.

A stronger finite-language shortcut axiom (`finite_language_is_mcfl`) is
not assumed.  Here finite union expresses only that finitely many schedule
languages already known to occupy the same tier can be stitched into one
existential language witness.  In the class-level theorem, the value of `k`
is fixed first by the uniform treewidth conclusion. -/
theorem full_behavior_bound {V : Type*} [DecidableEq V] [Fintype V]
    {D : V → Type*} [∀ v, DecidableEq (D v)] [∀ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (k : ℕ)
    (_htw : A.constraintHypergraph.HasTreewidthAtMost k)
    (Sym : Type*) (encode : (v : V) → D v → Sym) :
    IsMCFL.{_, 0} (A.FullBehaviorLanguage k Sym encode) (k + 1) := by
  classical
  -- Action-projection map: every per-decomposition language is a
  -- subset of `Set.range f`, which is finite.
  let f : (∀ v, D v) × {l : List V // l.Nodup} → List Sym :=
    fun p => (p.2.1.map (fun v =>
      if v ∈ A.action_vars then [encode v (p.1 v)] else [])).flatten
  -- `S` collects the distinct per-decomposition languages.
  let S : Set (Set (List Sym)) :=
    { L | ∃ (td : TreeDecomposition A.constraintHypergraph) (r : td.I),
            td.width ≤ k ∧ L = A.TreeBehaviorLanguage td r Sym encode }
  -- `S ⊆ powerset (range f)`, hence finite.
  have hS_finite : S.Finite := by
    refine (Set.Finite.powerset (Set.finite_range f)).subset ?_
    rintro L ⟨td, r, _hwidth, rfl⟩
    intro w hw
    obtain ⟨β, _hsat, perm, htco, rfl⟩ := hw
    exact ⟨(β, ⟨perm, (isTreeCompatibleOrdering_spec htco).2⟩), rfl⟩
  -- Index the union by `↑Sf`, which is a `Fintype` subtype.
  let Sf : Finset (Set (List Sym)) := hS_finite.toFinset
  let Ls : Sf → Set (List Sym) := fun L => L.val
  -- Each per-decomposition language is a `(k+1)`-MCFL by the bridge
  -- theorem (i.e. the explicit construction in `behavior_grammar_exists`).
  have hLs : ∀ L : Sf, ∃ G : MCFG.{_, 0} Sym,
      G.dimension ≤ k + 1 ∧ G.Language = Ls L := by
    rintro ⟨L, hL⟩
    rw [Set.Finite.mem_toFinset] at hL
    obtain ⟨td, r, hwidth, rfl⟩ := hL
    show ∃ G : MCFG.{_, 0} Sym, G.dimension ≤ k + 1 ∧
      G.Language = A.TreeBehaviorLanguage td r Sym encode
    exact behavior_grammar_exists A td r k hwidth Sym encode
  -- Finite union of `(k+1)`-MCFLs is a `(k+1)`-MCFL.
  obtain ⟨G, hGdim, hGlang⟩ :=
    @mcfg_finite_union _ _ _ Ls (k + 1) (Nat.le_add_left 1 k) hLs
  refine ⟨G, hGdim, ?_⟩
  rw [hGlang]
  -- `⋃ L : ↑Sf, L.val = FullBehaviorLanguage A k Sym encode`.
  ext w
  simp only [Set.mem_iUnion, EmbodiedAgent.FullBehaviorLanguage,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨L, hL⟩, hw⟩
    rw [Set.Finite.mem_toFinset] at hL
    obtain ⟨td, r, hwidth, rfl⟩ := hL
    exact ⟨td, r, hwidth, hw⟩
  · rintro ⟨td, r, hwidth, hw⟩
    refine ⟨⟨A.TreeBehaviorLanguage td r Sym encode, ?_⟩, hw⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨td, r, hwidth, rfl⟩

/-! **Main theorem, full-behavior formulation** (paper Theorem `thm:main`).

Under the standard hypotheses, there is a uniform `k` such that every
agent's full behavior language is a `(k+1)`-MCFL — bounding every action
sequence the agent can produce consistently with its beliefs.

The statement is existential and does not ask for a procedure that constructs
or preserves a solution.  Its class-level content is the common value of `k`,
obtained from the uniform treewidth theorem: all member schedule languages are
bounded by the same MCFG class, and finite families may be stitched without
changing that class. -/
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
    ∃ k, IsMCFL.{_, 0} (A.agent.FullBehaviorLanguage k Sym encode) (k + 1) := by
  obtain ⟨k, hk⟩ := class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  exact ⟨k, full_behavior_bound A.agent k (hk A hA) Sym encode⟩

/-- **Instantaneous operational-semantics corollary.**

`actual` is an independently supplied language of action words for one
instantaneous belief/action CSP.  The hypothesis `hschedule` is the exact
semantic bridge needed to identify that operational language with the
structured yields used by the graph-grammar argument.  It says that whenever a
width bound is available, the schedules admitted by the agent's own policy and
scheduling constraints are exactly the projections along the corresponding
width-bounded tree-compatible orderings.

This theorem separates two facts that should not be conflated:

* action and scheduling variables may be vertices of the original CSP; and
* their operational words must still be proved to coincide with the structured
  yield language to which the bounded-treewidth/MCFG result applies.

Under that equality, the ceiling is a theorem about the independently defined
behavior of the original agent, not merely about an auxiliary decomposition
language. -/
theorem main_theorem_instantaneous_behavior
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (A : SizedEmbodiedAgent)
    (hA : A ∈ 𝓐)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores)
    (Sym : Type*) (encode : (v : Fin A.n) → A.D v → Sym)
    (actual : Set (List Sym))
    (hschedule : ∀ k,
      (∀ B ∈ 𝓐, B.agent.constraintHypergraph.HasTreewidthAtMost k) →
      actual = A.agent.FullBehaviorLanguage k Sym encode) :
    ∃ k, IsMCFL.{_, 0} actual (k + 1) := by
  obtain ⟨k, hk⟩ :=
    class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  have htw := hk A hA
  refine ⟨k, ?_⟩
  rw [hschedule k hk]
  exact full_behavior_bound A.agent k htw Sym encode

/-! ## Main theorem without the cores hypothesis (semantic-core form) -/

/-- **Main theorem, semantic-core formulation** — no `AllCores` hypothesis.

The agent class carries NO minimality requirement: members may pad their
stores with arbitrary redundancy.  Tractability then bounds the treewidth
not of the raw stores but of their cores
(`class_tractable_implies_bounded_core_tw`), and the ceiling applies to any
behavior language realized at core width.

`hcore_realize` is the visible semantic-adequacy hypothesis, in the style
of `hschedule` in `main_theorem_instantaneous_behavior`.  Be precise about
what it carries — BOTH of the following, neither of which is a theorem of
this development:

1. **Representation**: the independently supplied language `actual` of
   certifiable behavior is the kind of object the semantic-core argument
   applies to.  (The invariance lemma
   `HomSystem.certifiable_behavior_core_bound` is proved axiom-free, but
   in an abstract layer that no Lean definition connects to
   `FullBehaviorLanguage` or to any agent object here; see its SCOPE
   WARNING.)
2. **Core realization**: whenever every member's core fits in width `k`,
   `actual` is realized as the full behavior language of SOME width-`≤k`
   representative agent — the tree-compatible-emission modeling claim
   applied at a core representative.

The mechanism-level strengthening ("the padded agent's own emission is
organized by its core") is FALSE in general and is not claimed.  What this
theorem establishes unconditionally is the ceiling constant: for every
tractable class — cores or not — there is one `k` such that any behavior
language satisfying `hcore_realize` is a `(k+1)`-MCFL.  One-sided and
existential, per the intended scope. -/
theorem main_theorem_semantic_core
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (Sym : Type*)
    (actual : Set (List Sym))
    (hcore_realize : ∀ k : ℕ,
      (∀ B ∈ 𝓐, ∃ K : SizedHypergraph,
        SizedHypergraph.CoreOf K B.constraintSizedHypergraph ∧
          K.HasTreewidthAtMost k) →
      ∃ (A' : SizedEmbodiedAgent)
        (encode' : (v : Fin A'.n) → A'.D v → Sym),
        A'.agent.constraintHypergraph.HasTreewidthAtMost k ∧
          actual = A'.agent.FullBehaviorLanguage k Sym encode') :
    ∃ k, IsMCFL.{_, 0} actual (k + 1) := by
  obtain ⟨k, hk⟩ :=
    class_tractable_implies_bounded_core_tw h_conj 𝓐 h_re h_tract h_arity
  obtain ⟨A', encode', htw, hactual⟩ := hcore_realize k hk
  refine ⟨k, ?_⟩
  rw [hactual]
  exact full_behavior_bound A'.agent k htw Sym encode'

/-! ## Main theorem — intendable (certified-quotient) formulation -/

/-- **Main theorem, intendable formulation.**  The end-to-end statement
for arbitrary (padded, non-minimal, non-rigid) agents:

Assume FPT ≠ W[1] and the class hypotheses.  Then there is one uniform
`k` such that for every agent that realizes its Grohe-level narrow core
as a concrete typed representative (`hrealize` — the visible seam between
the opaque hypergraph layer where Grohe's theorem lives and the concrete
CSP layer where behavior lives), the agent's certified-intendable
behavior language is a `(k+1)`-MCFL.

No rigidity hypothesis: by `soundlyReportable_iff_factorsThrough`, the
certified language already contains every record that admits ANY sound
token-typed description at width `k`; what it omits is indescribable at
that width, provably.  Trust base: `FPT_ne_W1` and `thm_grohe` only. -/
theorem main_theorem_intendable
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (hrealize : ∀ k : ℕ,
      (∀ B ∈ 𝓐, ∃ K : SizedHypergraph,
        SizedHypergraph.CoreOf K B.constraintSizedHypergraph ∧
          K.HasTreewidthAtMost k) →
      ∀ A ∈ 𝓐, ∃ (B : SizedEmbodiedAgent)
        (R : CSPRetraction A.agent.toCSP B.agent.toCSP)
        (td : TreeDecomposition B.agent.constraintHypergraph) (r : td.I),
        ActionTyped A.agent B.agent R ∧ td.width ≤ k) :
    ∃ k, ∀ A ∈ 𝓐, ∃ (B : SizedEmbodiedAgent)
      (R : CSPRetraction A.agent.toCSP B.agent.toCSP)
      (td : TreeDecomposition B.agent.constraintHypergraph) (r : td.I),
      ∀ (Sym : Type) (encodeC : (w : Fin B.n) → B.D w → Sym),
        IsMCFL.{_, 0}
          (CertifiedQuotientTreeBehaviorLanguage A.agent B.agent R td r
            encodeC) (k + 1) := by
  obtain ⟨k, hk⟩ :=
    class_tractable_implies_bounded_core_tw h_conj 𝓐 h_re h_tract h_arity
  refine ⟨k, ?_⟩
  intro A hA
  obtain ⟨B, R, td, r, hat, hw⟩ := hrealize k hk A hA
  exact ⟨B, R, td, r, fun Sym encodeC =>
    certified_quotient_behavior_bound A.agent B.agent R hat td r k hw
      encodeC⟩

/-! ## Theorem 12.3: Uniform grammar family (architectural-limit form) -/

/-! **Theorem 12.3 (Uniform grammar family).**

The architectural-limit reading of the main theorem, surfaced at the
statement level. There exists a uniform `k` (from Grohe) and a uniform
construction `G` such that, for every agent `A ∈ 𝓐` and every
width-`≤k` rooted tree decomposition `(td, r)` of `A`'s constraint
hypergraph, `G A hA td r hwidth` is an explicit `(k+1)`-MCFG generating
`A`'s tree-structured behavior language.

The result is existential at the class level: it does not require an
algorithm that constructs grammars or preserves a chosen satisfying assignment.
Classical choice merely packages the per-agent existence theorem as a family.
The substantive restriction is that all schedules obtained from width-`≤k`
decompositions lie in the same `(k+1)`-MCFL class; finite stitching does not
select or alter `k`.

The `k` is uniform across the entire RE class `𝓐`, including agents of
unboundedly many sizes; this is the substantive Grohe consequence. -/
theorem main_theorem_uniform_family
    (h_conj : FPT_ne_W1)
    (𝓐 : SizedEmbodiedAgentClass)
    (h_re : 𝓐.RecursivelyEnumerable)
    (h_tract : 𝓐.UniformTractableBelRevision)
    (h_arity : 𝓐.BoundedArity)
    (h_cores : 𝓐.AllCores)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) → (v : Fin A.n) → A.D v → Sym) :
    ∃ k : ℕ,
      (∀ (A : SizedEmbodiedAgent), A ∈ 𝓐 →
        A.agent.constraintHypergraph.HasTreewidthAtMost k) ∧
      ∃ G : (A : SizedEmbodiedAgent) → A ∈ 𝓐 →
            (td : TreeDecomposition A.agent.constraintHypergraph) → (r : td.I) →
            td.width ≤ k → MCFG.{_, 0} Sym,
        ∀ (A : SizedEmbodiedAgent) (hA : A ∈ 𝓐)
          (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I)
          (hwidth : td.width ≤ k),
          (G A hA td r hwidth).dimension ≤ k + 1 ∧
          (G A hA td r hwidth).Language =
            A.agent.TreeBehaviorLanguage td r Sym (encode A) := by
  classical
  obtain ⟨k, hk⟩ :=
    class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  refine ⟨k, hk, ?_⟩
  -- Define the uniform construction `G` by extracting from
  -- `behavior_grammar_exists` per (A, td, r, hwidth). The point is that
  -- a single function from agents and decompositions to grammars is
  -- exhibited; its dimension is uniformly `≤ k+1` by the bridge
  -- construction (Engelfriet + homomorphism + finite union).
  refine ⟨fun A _hA td r hwidth =>
    (behavior_grammar_exists A.agent td r k hwidth Sym (encode A)).choose, ?_⟩
  intro A hA td r hwidth
  exact (behavior_grammar_exists A.agent td r k hwidth Sym (encode A)).choose_spec
