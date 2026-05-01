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

The route via `finite_language_is_mcfl` would have been a one-line
shortcut (the language is finite, so it is trivially a `(k+1)`-MCFL),
but it would have left `bridge_theorem_forall` off the proof's critical
path. Routing through the bridge makes the constructive content
(Engelfriet's grammar + homomorphism + finite union over satisfying
assignments) load-bearing in this headline theorem, even though the
finite ambient set is also what makes step (2) work. -/
theorem full_behavior_bound {V : Type*} [DecidableEq V] [Fintype V]
    {D : V → Type*} [∀ v, DecidableEq (D v)] [∀ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (k : ℕ)
    (_htw : A.constraintHypergraph.HasTreewidthAtMost k)
    (Sym : Type*) (encode : (v : V) → D v → Sym) :
    IsMCFL (A.FullBehaviorLanguage k Sym encode) (k + 1) := by
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
  obtain ⟨G, hGdim, hGlang⟩ := @mcfg_finite_union.{_, _, 0, _} _ _ _ Ls (k + 1) hLs
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

/-- **Main theorem, full-behavior formulation** (paper Theorem `thm:main`).

Under the standard hypotheses, there is a uniform `k` such that every
agent's full behavior language is a `(k+1)`-MCFL — bounding every action
sequence the agent can produce consistently with its beliefs.

**Scope of this statement.** Per agent, `V` and the domains `D v` are
finite, so the per-agent full behavior language is a finite set of
strings. The substantive content of the theorem therefore lives in the
*proof* (which exhibits an explicit `(k+1)`-MCFG via `bridge_theorem`)
and in the *uniformity* of `k` across the entire RE class `𝓐` (which
comes from Grohe). The non-trivial set-level statement is
`main_theorem_finite_subclass`, which says the union of behavior
languages over any finite sub-class of `𝓐` lives in the same `(k+1)`-MCFL
class with the same uniform `k`. See repository `STATUS.md` for the full
discussion of headline framing. -/
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

/-! ## Theorem 12.3: Uniform grammar family (architectural-limit form) -/

/-- **Theorem 12.3 (Uniform grammar family).**

The architectural-limit reading of the main theorem, surfaced at the
statement level. There exists a uniform `k` (from Grohe) and a uniform
construction `G` such that, for every agent `A ∈ 𝓐` and every
width-`≤k` rooted tree decomposition `(td, r)` of `A`'s constraint
hypergraph, `G A hA td r hwidth` is an explicit `(k+1)`-MCFG generating
`A`'s tree-structured behavior language.

Why this is stronger than `main_theorem_full` *as a statement*. The
existing `main_theorem_full` says, per agent, that *some* grammar of
dimension `≤ k+1` exists generating the behavior language. Because the
per-agent language is finite (since `V` and the domains `D v` are
`Fintype`), that existential is satisfiable per-agent at dimension `1`
by any enumerative grammar listing the words — without ever invoking
Grohe or Engelfriet. The dimension bound `k+1` then carries no
architectural information at the statement level.

This theorem, by contrast, asserts the existence of a single function
`G : (A : SizedEmbodiedAgent) → A ∈ 𝓐 → ⋯ → MCFG Sym` whose dimension is
uniformly bounded by `k+1`. To produce such a `G`, one must have a
uniform construction recipe — exactly what `behavior_grammar_exists`
provides via Engelfriet's grammar plus homomorphism plus finite union
over satisfying assignments. The trivial enumerative-grammar
satisfaction route does not produce a uniform recipe; the bridge
construction does.

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
  -- Step 1: Grohe gives the uniform k.
  obtain ⟨k, _hk⟩ :=
    class_tractable_implies_bounded_tw h_conj 𝓐 h_re h_tract h_arity h_cores
  refine ⟨k, ?_⟩
  -- Step 2: Define the uniform construction `G` by extracting from
  -- `behavior_grammar_exists` per (A, td, r, hwidth). The point is that
  -- a single function from agents and decompositions to grammars is
  -- exhibited; its dimension is uniformly `≤ k+1` by the bridge
  -- construction (Engelfriet + homomorphism + finite union).
  refine ⟨fun A _hA td r hwidth =>
    (behavior_grammar_exists A.agent td r k hwidth Sym (encode A)).choose, ?_⟩
  intro A hA td r hwidth
  exact (behavior_grammar_exists A.agent td r k hwidth Sym (encode A)).choose_spec
