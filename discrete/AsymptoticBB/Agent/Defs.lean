/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.CSP
import Mathlib.Data.Finset.Basic

/-!
# Embodied Agents

Definitions 7.1â€“7.6 from the paper: embodied agents, belief states,
belief revision, action grounding, and behavior languages.
-/

set_option autoImplicit false

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {D : V â†’ Type v}

/-- An embodied agent is a CSP together with a designated non-empty set of
action variables.
(Definition 7.1) -/
structure EmbodiedAgent (V : Type u) [DecidableEq V] (D : V â†’ Type v) extends CSP V D where
  /-- The set of action variables V_A âŠ† V. -/
  action_vars : Finset V
  /-- Action variables are non-empty. -/
  action_vars_nonempty : action_vars.Nonempty

/-- The constraint hypergraph of an embodied agent is the constraint hypergraph
of its underlying CSP. -/
def EmbodiedAgent.constraintHypergraph [Fintype V] (A : EmbodiedAgent V D) : Hypergraph V :=
  A.toCSP.constraintHypergraph

/-- A belief state is a satisfying assignment of the CSP. (Definition 7.2) -/
def EmbodiedAgent.BeliefState [Fintype V] (A : EmbodiedAgent V D) : Set (âˆ€ v : V, D v) :=
  A.toCSP.Sol

/-- An agent satisfies action grounding if every action variable belongs to
the scope of at least one constraint whose scope also contains a non-action
variable. (Definition 7.4)

This is used in the bridge theorem construction (Theorem 11.3) to ensure
that action variables are connected to the constraint structure, but is not
an explicit hypothesis of the main theorem â€” it is a structural property
of meaningful agents. -/
def EmbodiedAgent.ActionGrounding (A : EmbodiedAgent V D) : Prop :=
  âˆ€ X âˆˆ A.action_vars,
    âˆƒ c âˆˆ A.constraints, X âˆˆ c.scope âˆ§ âˆƒ Y âˆˆ c.scope, Y âˆ‰ A.action_vars

/-- The behavior language of an embodied agent.
(Definition 7.6)

A behavior string is a word vâ‚vâ‚‚â‹¯vâ‚— âˆˆ A* for which there exist:
(i) a satisfying assignment Î² âˆˆ Sol(P), and
(ii) a permutation Ïƒ of {1, â€¦, â„“},
such that vâ±¼ = Î²(X_{i_{Ïƒ(j)}}) for each j.

Critical nuances:
- Î² must be a SATISFYING assignment (not just any assignment).
- Ïƒ is a permutation of execution ORDER â€” the agent executes its â„“
  action variables in some order Ïƒ, reading off the values Î² assigns.
- vâ±¼ is the VALUE of the Ïƒ(j)-th action variable under Î² â€” each
  letter in the word is a domain element, not a variable name.
- The language collects ALL such words over all satisfying assignments
  AND all permutations.

Since action variables may have heterogeneous domains, we use an encoding
function to a common output type Sym.

The quantification over `action_list` with `toFinset = action_vars` and
`Nodup` is equivalent to quantifying over permutations Ïƒ âˆˆ S_â„“. -/
def EmbodiedAgent.BehaviorLanguage [Fintype V]
    (A : EmbodiedAgent V D)
    (Sym : Type*) (encode : (v : V) â†’ D v â†’ Sym) : Set (List Sym) :=
  { w | âˆƒ (Î² : âˆ€ v : V, D v),
        A.toCSP.IsSatisfying Î² âˆ§
        âˆƒ (action_list : List V),
          action_list.toFinset = A.action_vars âˆ§
          action_list.Nodup âˆ§
          w = action_list.map (fun v => encode v (Î² v)) }
