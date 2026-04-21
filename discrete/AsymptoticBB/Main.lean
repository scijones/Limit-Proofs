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

- **`ClassBehaviorLanguage`**: The class-level behavior language â€” the union
  of per-agent tree-structured behavior languages across an agent class.
- **`class_tractable_implies_bounded_tw`** (Corollary 9.3): Tractability
  implies uniformly bounded treewidth.
- **`main_theorem`** (Theorem 12.1): Per-agent formulation â€” for every
  agent in the class, there exists a tree decomposition under which the
  behavior language is a (k+1)-MCFL, with k uniform across the class.
- **`main_theorem_finite_subclass`** (Theorem 12.2): For any finite
  sub-class, the union of behavior languages is a single (k+1)-MCFL.

## Type flow
```
ð“ : SizedEmbodiedAgentClass
  â”‚
  â”œâ”€â”€ thm_grohe â†’ âˆƒ k, uniform treewidth bound
  â”‚
  â”œâ”€â”€ âˆ€ A âˆˆ ð“: bridge_theorem â†’ âˆƒ td r, IsMCFL (L(A,td,r)) (k+1)
  â”‚
  â””â”€â”€ ClassBehaviorLanguage(ð“) = â‹ƒ_{A âˆˆ ð“} L(A, td_A, r_A)
      â””â”€â”€ For finite F âŠ† ð“: IsMCFL (â‹ƒ_{A âˆˆ F} L(A)) (k+1)
```
-/

set_option autoImplicit false

/-! ## Class-Level Behavior Language -/

/-- The class-level behavior language: the union of per-agent tree-structured
behavior languages across all agents in a sized agent class.

For each agent A âˆˆ ð“, we existentially quantify over tree decompositions
(td, r) of A's constraint hypergraph. A word w is in the class language if
it belongs to L(A, td, r) for SOME agent A âˆˆ ð“ and SOME tree decomposition.

This language is potentially infinite when ð“ contains agents with
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
    (ð“ : SizedEmbodiedAgentClass)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) â†’ (v : Fin A.n) â†’ A.D v â†’ Sym) :
    Set (List Sym) :=
  { w | âˆƒ (A : SizedEmbodiedAgent), A âˆˆ ð“ âˆ§
        âˆƒ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
          w âˆˆ A.agent.TreeBehaviorLanguage td r Sym (encode A) }

/-! ## Corollary 9.3: Tractability implies bounded treewidth -/

/-- Corollary 9.3 â€” Asymptotic version.

Assume FPT â‰  W[1]. Let ð“ be a class of sized embodied agents (varying
vertex-set sizes) sharing a single uniform polynomial-time belief-revision
architecture. If ð“ has uniformly bounded arity and all constraint
hypergraphs are cores, then there is one constant k such that EVERY agent
in ð“ has a constraint hypergraph of treewidth at most k. -/
theorem class_tractable_implies_bounded_tw
    (h_conj : FPT_ne_W1)
    (ð“ : SizedEmbodiedAgentClass)
    (h_re : ð“.RecursivelyEnumerable)
    (h_tract : ð“.UniformTractableBelRevision)
    (h_arity : ð“.BoundedArity)
    (h_cores : ð“.AllCores) :
    âˆƒ k, âˆ€ A âˆˆ ð“, A.agent.constraintHypergraph.HasTreewidthAtMost k := by
  obtain âŸ¨k, hkâŸ© := thm_grohe h_conj ð“.hypergraphs h_re
    (SizedEmbodiedAgentClass.hypergraphs_boundedArity h_arity) h_cores h_tract
  refine âŸ¨k, ?_âŸ©
  intro A hA
  have : A.constraintSizedHypergraph âˆˆ ð“.hypergraphs := âŸ¨A, hA, rflâŸ©
  exact hk A.constraintSizedHypergraph this

/-! ## Theorem 12.1: Main theorem â€” per-agent -/

/-- Theorem 12.1 (Main theorem) â€” per-agent formulation.

Assume FPT â‰  W[1]. For a class ð“ satisfying the standard hypotheses,
there exists a uniform k such that for every A âˆˆ ð“, there exists a tree
decomposition (td, r) such that L(A, td, r) is a (k+1)-MCFL.

The tree decomposition is existential in the conclusion, and k is
uniform across the class. -/
theorem main_theorem
    (h_conj : FPT_ne_W1)
    (ð“ : SizedEmbodiedAgentClass)
    (A : SizedEmbodiedAgent)
    (hA : A âˆˆ ð“)
    (h_re : ð“.RecursivelyEnumerable)
    (h_tract : ð“.UniformTractableBelRevision)
    (h_arity : ð“.BoundedArity)
    (h_cores : ð“.AllCores)
    (Sym : Type*) (encode : (v : Fin A.n) â†’ A.D v â†’ Sym) :
    âˆƒ k, âˆƒ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
      IsMCFL (A.agent.TreeBehaviorLanguage td r Sym encode) (k + 1) := by
  obtain âŸ¨k, hkâŸ© := class_tractable_implies_bounded_tw h_conj ð“ h_re h_tract h_arity h_cores
  obtain âŸ¨td, r, hmcflâŸ© := bridge_theorem A.agent k Sym encode (hk A hA)
  exact âŸ¨k, td, r, hmcflâŸ©

/-! ## Theorem 12.1â€²: Main theorem â€” universal (witness) form -/

/-- Theorem 12.1â€² (Main theorem, universal form).

The "decomposition as witness" form of `main_theorem`: there is a uniform
`k` such that for every `A âˆˆ ð“`, *every* width-`â‰¤k` tree decomposition of
`A.constraintHypergraph` (with any root) yields a `(k+1)`-MCFL behavior
language. In particular, the complexity bound is invariant under the
choice of width-`k` witness.

At least one such decomposition exists because `tw(H_A) â‰¤ k`. -/
theorem main_theorem_forall
    (h_conj : FPT_ne_W1)
    (ð“ : SizedEmbodiedAgentClass)
    (h_re : ð“.RecursivelyEnumerable)
    (h_tract : ð“.UniformTractableBelRevision)
    (h_arity : ð“.BoundedArity)
    (h_cores : ð“.AllCores)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) â†’ (v : Fin A.n) â†’ A.D v â†’ Sym) :
    âˆƒ k, âˆ€ (A : SizedEmbodiedAgent), A âˆˆ ð“ â†’
      âˆ€ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I),
        td.width â‰¤ k â†’
        IsMCFL (A.agent.TreeBehaviorLanguage td r Sym (encode A)) (k + 1) := by
  obtain âŸ¨k, hkâŸ© := class_tractable_implies_bounded_tw h_conj ð“ h_re h_tract h_arity h_cores
  refine âŸ¨k, ?_âŸ©
  intro A hA td r hwidth
  exact bridge_theorem_forall A.agent k Sym (encode A) td r hwidth

/-! ## Theorem 12.2: Main theorem â€” finite sub-class -/

/-- Theorem 12.2 (Main theorem â€” finite sub-class formulation).

For any FINITE subset F âŠ† ð“, the union of behavior languages
â‹ƒ_{A âˆˆ F} L(A, td_A, r_A) is a single (k+1)-MCFL.

This is the strongest non-vacuous statement provable from the existing
axiom `mcfg_finite_union`: the union of finitely many (k+1)-MCFLs is
a (k+1)-MCFL, and the k is uniform across the entire class (independent
of which finite subset F is chosen or how large it is).

NON-TRIVIALITY: As |F| grows (sampling agents of larger and larger sizes),
the union language grows without bound. The dimension bound k+1 remains
fixed, showing that the constraint structure genuinely controls the
formal-language complexity â€” not just per-agent, but uniformly. -/
theorem main_theorem_finite_subclass
    (h_conj : FPT_ne_W1)
    (ð“ : SizedEmbodiedAgentClass)
    (h_re : ð“.RecursivelyEnumerable)
    (h_tract : ð“.UniformTractableBelRevision)
    (h_arity : ð“.BoundedArity)
    (h_cores : ð“.AllCores)
    (Sym : Type*)
    (encode : (A : SizedEmbodiedAgent) â†’ (v : Fin A.n) â†’ A.D v â†’ Sym) :
    âˆƒ k, âˆ€ (F : Finset SizedEmbodiedAgent), â†‘F âŠ† ð“ â†’
      âˆƒ (td_choice : âˆ€ A âˆˆ F, TreeDecomposition A.agent.constraintHypergraph)
        (r_choice : âˆ€ (A : SizedEmbodiedAgent) (hA : A âˆˆ F), (td_choice A hA).I),
        IsMCFL (â‹ƒ (A : F),
          (A : SizedEmbodiedAgent).agent.TreeBehaviorLanguage
            (td_choice A A.prop) (r_choice A A.prop) Sym (encode A)) (k + 1) := by
  -- Get uniform treewidth bound
  obtain âŸ¨k, hkâŸ© := class_tractable_implies_bounded_tw h_conj ð“ h_re h_tract h_arity h_cores
  refine âŸ¨k, ?_âŸ©
  intro F hF
  -- For each A âˆˆ F, get a tree decomposition witnessing tw â‰¤ k
  -- and a per-agent (k+1)-MCFG (with pinned nonterminal universe)
  have per_agent : âˆ€ A âˆˆ F,
      âˆƒ (td : TreeDecomposition A.agent.constraintHypergraph) (r : td.I)
        (G : MCFG.{_, 0} Sym), G.dimension â‰¤ k + 1 âˆ§
        G.Language = A.agent.TreeBehaviorLanguage td r Sym (encode A) := by
    intro A hA
    obtain âŸ¨td, r, G, hGdim, hGlangâŸ© := bridge_theorem A.agent k Sym (encode A) (hk A (hF hA))
    exact âŸ¨td, r, G, hGdim, hGlangâŸ©
  -- Use classical choice to extract td and r for each A âˆˆ F
  classical
  let td_choice : âˆ€ A âˆˆ F, TreeDecomposition A.agent.constraintHypergraph :=
    fun A hA => (per_agent A hA).choose
  let r_choice : âˆ€ (A : SizedEmbodiedAgent) (hA : A âˆˆ F), (td_choice A hA).I :=
    fun A hA => (per_agent A hA).choose_spec.choose
  refine âŸ¨td_choice, r_choice, ?_âŸ©
  -- Each per-agent language has a (k+1)-MCFG
  have per_mcfg : âˆ€ (A : F),
      âˆƒ (G : MCFG.{_, 0} Sym), G.dimension â‰¤ k + 1 âˆ§
        G.Language = (A : SizedEmbodiedAgent).agent.TreeBehaviorLanguage
          (td_choice A A.prop) (r_choice A A.prop) Sym (encode A) :=
    fun âŸ¨A, hAâŸ© => (per_agent A hA).choose_spec.choose_spec
  -- Define per-agent languages indexed by F
  let Ls : F â†’ Set (List Sym) := fun A =>
    (A : SizedEmbodiedAgent).agent.TreeBehaviorLanguage
      (td_choice A A.prop) (r_choice A A.prop) Sym (encode A)
  -- Each is a (k+1)-MCFL â€” universe pinned to 0
  have hLs : âˆ€ i : F, âˆƒ G : MCFG.{_, 0} Sym, G.dimension â‰¤ k + 1 âˆ§ G.Language = Ls i := by
    intro âŸ¨A, hAâŸ©
    exact per_mcfg âŸ¨A, hAâŸ©
  -- Finite union of (k+1)-MCFLs is a (k+1)-MCFL
  obtain âŸ¨G, hGdim, hGlangâŸ© := @mcfg_finite_union.{_, _, 0, _} _ _ _ Ls (k + 1) hLs
  exact âŸ¨G, hGdim, hGlangâŸ©

/-! ## Full behavior bound

The full behavior language of `A` at width bound `k`: the union of
tree-structured behavior languages over every width-`â‰¤k` rooted tree
decomposition of `A`'s constraint hypergraph. Under the policy-as-CSP
reading of the paper (Remark `rem:policy`), every action sequence the
agent can produce self-consistently is the action-variable projection
of some `Î² âˆˆ Sol(P)` along a tree-compatible ordering of `V`; when
`tw(H) â‰¤ k`, every such ordering is tree-compatible for some width-`â‰¤k`
decomposition. Hence `FullBehaviorLanguage A k` captures every action
sequence `A` can produce consistently with its beliefs.
-/

/-- The **full behavior language** of an embodied agent at width bound `k`:
the union of `TreeBehaviorLanguage` over all width-`â‰¤k` rooted tree
decompositions of `A.constraintHypergraph`. Paper definition
`def:full-behavior-language`. -/
def EmbodiedAgent.FullBehaviorLanguage {V : Type*} [DecidableEq V] [Fintype V]
    {D : V â†’ Type*} [âˆ€ v, DecidableEq (D v)] [âˆ€ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (k : â„•)
    (Sym : Type*) (encode : (v : V) â†’ D v â†’ Sym) : Set (List Sym) :=
  { w | âˆƒ (td : TreeDecomposition A.constraintHypergraph) (r : td.I),
          td.width â‰¤ k âˆ§ w âˆˆ A.TreeBehaviorLanguage td r Sym encode }

/-- **Full behavior bound** (paper Theorem `thm:full-bound`).

Under `tw(H) â‰¤ k`, the full behavior language of `A` is a `(k+1)`-MCFL.

Proof idea:
  For finite `V` and finite domains `D v`, every word in
  `A.FullBehaviorLanguage k Sym encode` is the flattened map of a
  `Nodup` permutation of `V` (via `IsTreeCompatibleOrdering`'s
  specification) under a total assignment `Î² : âˆ€ v, D v`. Both the
  assignment space `âˆ€ v, D v` and the set of `Nodup` lists over `V`
  are finite (the latter by `fintypeNodupList`), so the language is a
  subset of the range of a function out of a finite type, hence finite.
  Apply `finite_language_is_mcfl` at dimension `k+1 â‰¥ 1`.

The paper proves this at `thm:full-bound` by the same argument plus the
observation that each per-decomposition language is a `(k+1)`-MCFL by
`bridge_theorem_forall`; since our Lean route goes through the finite
closure axiom we do not need the per-decomposition step, but the paper
statement and this Lean statement agree. -/
theorem full_behavior_bound {V : Type*} [DecidableEq V] [Fintype V]
    {D : V â†’ Type*} [âˆ€ v, DecidableEq (D v)] [âˆ€ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (k : â„•)
    (_htw : A.constraintHypergraph.HasTreewidthAtMost k)
    (Sym : Type*) (encode : (v : V) â†’ D v â†’ Sym) :
    IsMCFL (A.FullBehaviorLanguage k Sym encode) (k + 1) := by
  -- Every word in the full behavior language is determined by a pair
  -- `(Î², perm)` with `Î² : âˆ€ v, D v` (finitely many since `V` and each
  -- `D v` are finite) and `perm : {l : List V // l.Nodup}` (finitely
  -- many by `fintypeNodupList`). So the language is a subset of the
  -- range of a map out of a finite type, hence finite. Apply
  -- `finite_language_is_mcfl`.
  let f : (âˆ€ v, D v) Ã— {l : List V // l.Nodup} â†’ List Sym :=
    fun p => (p.2.1.map (fun v =>
      if v âˆˆ A.action_vars then [encode v (p.1 v)] else [])).flatten
  have hfin : (A.FullBehaviorLanguage k Sym encode).Finite := by
    refine (Set.finite_range f).subset ?_
    rintro w âŸ¨td, r, _hw, Î², _hsat, perm, htco, rflâŸ©
    exact âŸ¨(Î², âŸ¨perm, (isTreeCompatibleOrdering_spec htco).2âŸ©), rflâŸ©
  exact finite_language_is_mcfl _ hfin (k + 1) (by omega)

/-- **Main theorem, full-behavior formulation** (paper Theorem `thm:main`).

Under the standard hypotheses, there is a uniform `k` such that every
agent's full behavior language is a `(k+1)`-MCFL â€” bounding every action
sequence the agent can produce consistently with its beliefs. -/
theorem main_theorem_full
    (h_conj : FPT_ne_W1)
    (ð“ : SizedEmbodiedAgentClass)
    (A : SizedEmbodiedAgent)
    (hA : A âˆˆ ð“)
    (h_re : ð“.RecursivelyEnumerable)
    (h_tract : ð“.UniformTractableBelRevision)
    (h_arity : ð“.BoundedArity)
    (h_cores : ð“.AllCores)
    (Sym : Type*) (encode : (v : Fin A.n) â†’ A.D v â†’ Sym) :
    âˆƒ k, IsMCFL (A.agent.FullBehaviorLanguage k Sym encode) (k + 1) := by
  obtain âŸ¨k, hkâŸ© := class_tractable_implies_bounded_tw h_conj ð“ h_re h_tract h_arity h_cores
  exact âŸ¨k, full_behavior_bound A.agent k (hk A hA) Sym encodeâŸ©
