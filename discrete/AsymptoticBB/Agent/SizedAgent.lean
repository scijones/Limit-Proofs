/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Agent.Defs
import AsymptoticBB.Basic.SizedInstances

/-!
# Sized Embodied Agents

Defines `SizedEmbodiedAgent`, which bundles a vertex-set size `n`, a domain
function `D : Fin n â†’ Type`, and an `EmbodiedAgent (Fin n) D`. Different
sized agents can have different `n`, so a class `Set SizedEmbodiedAgent`
can contain agents of varying sizes â€” making uniform treewidth bounds
non-trivial.

Also defines `SizedEmbodiedAgentClass` predicates:
- `RecursivelyEnumerable`, `UniformTractableBelRevision`, `BoundedArity`,
  `AllCores` â€” these feed into `thm_grohe` via the `.hypergraphs` extraction.

## Type propagation
```
SizedEmbodiedAgent â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”
  (n : â„•, D : Fin n â†’ Type,                   â”‚
   agent : EmbodiedAgent (Fin n) D)            â”‚
                                                â”œâ”€â”€â–¶ Main.lean
SizedEmbodiedAgentClass predicates:             â”‚
  RecursivelyEnumerable, UniformTractable,     â”‚
  BoundedArity  â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”˜
       â”‚
       â”œâ”€â”€â–¶ .hypergraphs : Set SizedHypergraph â”€â”€â–¶ thm_grohe (Axioms.lean)
       â”‚
       â””â”€â”€â–¶ Per-instance extraction: A.agent works with
            bridge_theorem, engelfriet, etc.
```

## Universe considerations

Domain types `D : Fin n â†’ Type` are in Type 0. This means:
- `EmbodiedAgent (Fin n) D` has `V : Type 0` (from `Fin n`)
- All CSP constraint relations are `Prop` (universe-independent)
- BehaviorLanguage produces `Set (List Sym)` â€” Sym can be any universe
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
2. The bridge theorem needs `[âˆ€ v, Fintype (D v)]` and `[âˆ€ v, DecidableEq (D v)]`
3. These are always satisfiable for the finite domains used in CSPs -/
structure SizedEmbodiedAgent where
  /-- Number of variables. -/
  n : â„•
  /-- Domain assignment: each variable gets a type of values. -/
  D : Fin n â†’ Type
  /-- Fintype instance for each domain (needed for bridge theorem). -/
  instFintype : âˆ€ v, Fintype (D v)
  /-- DecidableEq instance for each domain (needed for bridge theorem). -/
  instDecEq : âˆ€ v, DecidableEq (D v)
  /-- The embodied agent. -/
  agent : EmbodiedAgent (Fin n) D

-- Register instances so they're picked up by typeclass resolution
-- when working with a specific SizedEmbodiedAgent
attribute [instance] SizedEmbodiedAgent.instFintype SizedEmbodiedAgent.instDecEq

/-! ## Extraction and Connection -/

/-- The constraint hypergraph of a sized agent, as a SizedHypergraph. -/
def SizedEmbodiedAgent.constraintSizedHypergraph (A : SizedEmbodiedAgent) :
    SizedHypergraph :=
  âŸ¨A.n, A.agent.constraintHypergraphâŸ©

/-- The behavior language of a sized agent.
Delegates to the per-instance BehaviorLanguage. -/
def SizedEmbodiedAgent.BehaviorLanguage (A : SizedEmbodiedAgent)
    (Sym : Type*) (encode : (v : Fin A.n) â†’ A.D v â†’ Sym) : Set (List Sym) :=
  A.agent.BehaviorLanguage Sym encode

/-! ## Sized Agent Classes -/

/-- A class of sized embodied agents (a set of agents with varying sizes). -/
abbrev SizedEmbodiedAgentClass := Set SizedEmbodiedAgent

/-- The sized hypergraph class induced by a sized agent class.
Each agent's constraint hypergraph is bundled with its vertex-set size. -/
def SizedEmbodiedAgentClass.hypergraphs (ð“ : SizedEmbodiedAgentClass) :
    Set SizedHypergraph :=
  { sH | âˆƒ A âˆˆ ð“, A.constraintSizedHypergraph = sH }

/-- A class of sized agents is recursively enumerable when its induced
sized hypergraph class is recursively enumerable. -/
def SizedEmbodiedAgentClass.RecursivelyEnumerable
    (ð“ : SizedEmbodiedAgentClass) : Prop :=
  SizedHypergraphClass.RecursivelyEnumerable ð“.hypergraphs

/-- A class of sized agents is uniformly tractable for belief revision when one
uniform polynomial-time CSP solver works for all hypergraphs realized by the
class â€” across ALL sizes n.

This is where the non-triviality enters: the solver must handle instances
of UNBOUNDED size, not just permutations on a fixed vertex set. -/
def SizedEmbodiedAgentClass.UniformTractableBelRevision
    (ð“ : SizedEmbodiedAgentClass) : Prop :=
  SizedHypergraphClass.UniformPolyTimeSolvable ð“.hypergraphs

/-- A class of sized agents has bounded arity if one arity bound works
uniformly for every member regardless of size. -/
def SizedEmbodiedAgentClass.BoundedArity
    (ð“ : SizedEmbodiedAgentClass) : Prop :=
  âˆƒ r : â„•, âˆ€ A âˆˆ ð“, A.agent.constraintHypergraph.BoundedArity r

/-- Every agent in the class has a core constraint hypergraph (no
redundant variables that could be collapsed by a non-trivial endomorphism).

This is natural for the agent application: a well-designed agent should not
have redundant constraint variables. It matches Grohe's core condition. -/
def SizedEmbodiedAgentClass.AllCores
    (ð“ : SizedEmbodiedAgentClass) : Prop :=
  SizedHypergraphClass.AllCores ð“.hypergraphs

/-- Uniform bounded arity for a sized agent class induces uniform bounded
arity for its sized hypergraph class. -/
theorem SizedEmbodiedAgentClass.hypergraphs_boundedArity
    {ð“ : SizedEmbodiedAgentClass}
    (h : ð“.BoundedArity) :
    SizedHypergraphClass.BoundedArity ð“.hypergraphs := by
  rcases h with âŸ¨r, hrâŸ©
  refine âŸ¨r, ?_âŸ©
  intro sH hsH
  obtain âŸ¨A, hA, heqâŸ© := hsH
  subst heq
  exact hr A hA
