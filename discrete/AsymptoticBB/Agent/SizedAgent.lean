/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Agent.Defs
import AsymptoticBB.Basic.SizedInstances

/-!
# Sized Embodied Agents

Defines `SizedEmbodiedAgent`, which bundles a vertex-set size `n`, a domain
function `D : Fin n → Type`, and an `EmbodiedAgent (Fin n) D`. Different
sized agents can have different `n`, so a class `Set SizedEmbodiedAgent`
can contain agents of varying sizes — making uniform treewidth bounds
non-trivial.

Also defines `SizedEmbodiedAgentClass` predicates:
- `RecursivelyEnumerable`, `UniformTractableBelRevision`, `BoundedArity`,
  `AllCores` — these feed into `thm_grohe` via the `.hypergraphs` extraction.

## Type propagation
```
SizedEmbodiedAgent ────────────────────────────┐
  (n : ℕ, D : Fin n → Type,                   │
   agent : EmbodiedAgent (Fin n) D)            │
                                                ├──▶ Main.lean
SizedEmbodiedAgentClass predicates:             │
  RecursivelyEnumerable, UniformTractable,     │
  BoundedArity  ────────────────────────────────┘
       │
       ├──▶ .hypergraphs : Set SizedHypergraph ──▶ thm_grohe (Axioms.lean)
       │
       └──▶ Per-instance extraction: A.agent works with
            bridge_theorem, engelfriet, etc.
```

## Universe considerations

Domain types `D : Fin n → Type` are in Type 0. This means:
- `EmbodiedAgent (Fin n) D` has `V : Type 0` (from `Fin n`)
- All CSP constraint relations are `Prop` (universe-independent)
- BehaviorLanguage produces `Set (List Sym)` — Sym can be any universe
-/

set_option autoImplicit false

/-! ## Sized Embodied Agents -/

/-- An embodied agent bundled with its vertex-set size and domain assignment.

Each `SizedEmbodiedAgent` represents a self-contained agent instance:
- `n` variables (vertices), numbered 0 to n-1
- Domain function `D` assigning a type of values to each variable
- The agent structure (CSP + action variables)
- Required typeclass instances for the domains

Different SizedEmbodiedAgents can have different `n` and `D`.
A class `Set SizedEmbodiedAgent` can thus contain agents of varying sizes,
making uniform treewidth bounds non-trivial.

Fintype and DecidableEq instances for domains are included because:
1. `BehaviorLanguage` needs `[Fintype V]` (automatic for Fin n)
2. The bridge theorem needs `[∀ v, Fintype (D v)]` and `[∀ v, DecidableEq (D v)]`
3. These are always satisfiable for the finite domains used in CSPs -/
structure SizedEmbodiedAgent where
  /-- Number of variables. -/
  n : ℕ
  /-- Domain assignment: each variable gets a type of values. -/
  D : Fin n → Type
  /-- Fintype instance for each domain (needed for bridge theorem). -/
  instFintype : ∀ v, Fintype (D v)
  /-- DecidableEq instance for each domain (needed for bridge theorem). -/
  instDecEq : ∀ v, DecidableEq (D v)
  /-- The embodied agent. -/
  agent : EmbodiedAgent (Fin n) D

-- Register instances so they're picked up by typeclass resolution
-- when working with a specific SizedEmbodiedAgent
attribute [instance] SizedEmbodiedAgent.instFintype SizedEmbodiedAgent.instDecEq

/-! ## Extraction and Connection -/

/-- The constraint hypergraph of a sized agent, as a SizedHypergraph. -/
def SizedEmbodiedAgent.constraintSizedHypergraph (A : SizedEmbodiedAgent) :
    SizedHypergraph :=
  ⟨A.n, A.agent.constraintHypergraph⟩

/-- The behavior language of a sized agent.
Delegates to the per-instance BehaviorLanguage. -/
def SizedEmbodiedAgent.BehaviorLanguage (A : SizedEmbodiedAgent)
    (Sym : Type*) (encode : (v : Fin A.n) → A.D v → Sym) : Set (List Sym) :=
  A.agent.BehaviorLanguage Sym encode

/-! ## Sized Agent Classes -/

/-- A class of sized embodied agents (a set of agents with varying sizes). -/
abbrev SizedEmbodiedAgentClass := Set SizedEmbodiedAgent

/-- The sized hypergraph class induced by a sized agent class.
Each agent's constraint hypergraph is bundled with its vertex-set size. -/
def SizedEmbodiedAgentClass.hypergraphs (𝓐 : SizedEmbodiedAgentClass) :
    Set SizedHypergraph :=
  { sH | ∃ A ∈ 𝓐, A.constraintSizedHypergraph = sH }

/-- A class of sized agents is recursively enumerable when its induced
sized hypergraph class is recursively enumerable. -/
def SizedEmbodiedAgentClass.RecursivelyEnumerable
    (𝓐 : SizedEmbodiedAgentClass) : Prop :=
  SizedHypergraphClass.RecursivelyEnumerable 𝓐.hypergraphs

/-- A class of sized agents is uniformly tractable for belief revision when one
uniform polynomial-time CSP solver works for all hypergraphs realized by the
class — across ALL sizes n.

This is where the non-triviality enters: the solver must handle instances
of UNBOUNDED size, not just permutations on a fixed vertex set. -/
def SizedEmbodiedAgentClass.UniformTractableBelRevision
    (𝓐 : SizedEmbodiedAgentClass) : Prop :=
  SizedHypergraphClass.UniformPolyTimeSolvable 𝓐.hypergraphs

/-- A class of sized agents has bounded arity if one arity bound works
uniformly for every member regardless of size. -/
def SizedEmbodiedAgentClass.BoundedArity
    (𝓐 : SizedEmbodiedAgentClass) : Prop :=
  ∃ r : ℕ, ∀ A ∈ 𝓐, A.agent.constraintHypergraph.BoundedArity r

/-- Every agent in the class has a core constraint hypergraph (no
redundant variables that could be collapsed by a non-trivial endomorphism).

This is natural for the agent application: a well-designed agent should not
have redundant constraint variables. It matches Grohe's core condition. -/
def SizedEmbodiedAgentClass.AllCores
    (𝓐 : SizedEmbodiedAgentClass) : Prop :=
  SizedHypergraphClass.AllCores 𝓐.hypergraphs

/-- Uniform bounded arity for a sized agent class induces uniform bounded
arity for its sized hypergraph class. -/
theorem SizedEmbodiedAgentClass.hypergraphs_boundedArity
    {𝓐 : SizedEmbodiedAgentClass}
    (h : 𝓐.BoundedArity) :
    SizedHypergraphClass.BoundedArity 𝓐.hypergraphs := by
  rcases h with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  intro sH hsH
  obtain ⟨A, hA, heq⟩ := hsH
  subst heq
  exact hr A hA
