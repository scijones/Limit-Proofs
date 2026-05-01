/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.CSP
import Mathlib.Data.Finset.Basic

/-!
# Embodied Agents

Definitions 7.1–7.6 from the paper: embodied agents, belief states,
belief revision, action grounding, and behavior languages.
-/

set_option autoImplicit false

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {D : V → Type v}

/-- An embodied agent is a CSP together with a designated non-empty set of
action variables.
(Definition 7.1) -/
structure EmbodiedAgent (V : Type u) [DecidableEq V] (D : V → Type v) extends CSP V D where
  /-- The set of action variables V_A ⊆ V. -/
  action_vars : Finset V
  /-- Action variables are non-empty. -/
  action_vars_nonempty : action_vars.Nonempty

/-- The constraint hypergraph of an embodied agent is the constraint hypergraph
of its underlying CSP. -/
def EmbodiedAgent.constraintHypergraph [Fintype V] (A : EmbodiedAgent V D) : Hypergraph V :=
  A.toCSP.constraintHypergraph

/-- A belief state is a satisfying assignment of the CSP. (Definition 7.2) -/
def EmbodiedAgent.BeliefState [Fintype V] (A : EmbodiedAgent V D) : Set (∀ v : V, D v) :=
  A.toCSP.Sol

/-- An agent satisfies action grounding if every action variable belongs to
the scope of at least one constraint whose scope also contains a non-action
variable. (Definition 7.4)

This is used in the bridge theorem construction (Theorem 11.3) to ensure
that action variables are connected to the constraint structure, but is not
an explicit hypothesis of the main theorem — it is a structural property
of meaningful agents. -/
def EmbodiedAgent.ActionGrounding (A : EmbodiedAgent V D) : Prop :=
  ∀ X ∈ A.action_vars,
    ∃ c ∈ A.constraints, X ∈ c.scope ∧ ∃ Y ∈ c.scope, Y ∉ A.action_vars

/-- The behavior language of an embodied agent.
(Definition 7.6)

A behavior string is a word v₁v₂⋯vₗ ∈ A* for which there exist:
(i) a satisfying assignment β ∈ Sol(P), and
(ii) a permutation σ of {1, …, ℓ},
such that vⱼ = β(X_{i_{σ(j)}}) for each j.

Critical nuances:
- β must be a SATISFYING assignment (not just any assignment).
- σ is a permutation of execution ORDER — the agent executes its ℓ
  action variables in some order σ, reading off the values β assigns.
- vⱼ is the VALUE of the σ(j)-th action variable under β — each
  letter in the word is a domain element, not a variable name.
- The language collects ALL such words over all satisfying assignments
  AND all permutations.

Since action variables may have heterogeneous domains, we use an encoding
function to a common output type Sym.

The quantification over `action_list` with `toFinset = action_vars` and
`Nodup` is equivalent to quantifying over permutations σ ∈ S_ℓ. -/
def EmbodiedAgent.BehaviorLanguage [Fintype V]
    (A : EmbodiedAgent V D)
    (Sym : Type*) (encode : (v : V) → D v → Sym) : Set (List Sym) :=
  { w | ∃ (β : ∀ v : V, D v),
        A.toCSP.IsSatisfying β ∧
        ∃ (action_list : List V),
          action_list.toFinset = A.action_vars ∧
          action_list.Nodup ∧
          w = action_list.map (fun v => encode v (β v)) }
