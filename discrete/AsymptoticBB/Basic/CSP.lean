/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.Hypergraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Constraint Satisfaction Problems

Definitions 3.1â€“3.5 from the paper: CSP instances, satisfying assignments,
pinned CSPs, constraint hypergraphs, and partial assignments.
-/

set_option autoImplicit false

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {D : V â†’ Type v}

/-- A constraint consists of a scope (an ordered tuple of distinct variables) and
a constraint relation (a predicate on tuples over the domains of those variables).
(Part of Definition 3.1) -/
structure Constraint (V : Type u) (D : V â†’ Type v) where
  scope : List V
  scope_nodup : scope.Nodup
  relation : (âˆ€ i : Fin scope.length, D (scope.get i)) â†’ Prop

/-- The arity of a constraint is the length of its scope. -/
def Constraint.arity' (c : Constraint V D) : â„• :=
  c.scope.length

/-- A CSP instance âŸ¨V, D, CâŸ©. V and D are parameters; constraints are data.
(Definition 3.1) -/
structure CSP (V : Type u) [DecidableEq V] (D : V â†’ Type v) where
  constraints : List (Constraint V D)

/-- A satisfying assignment satisfies all constraints.
(Definition 3.2) -/
def CSP.IsSatisfying (P : CSP V D) (Î² : âˆ€ v : V, D v) : Prop :=
  âˆ€ c âˆˆ P.constraints,
    c.relation (fun i => Î² (c.scope.get i))

/-- The solution set of a CSP. (Definition 3.2) -/
def CSP.Sol (P : CSP V D) : Set (âˆ€ v : V, D v) :=
  { Î² | P.IsSatisfying Î² }

/-- A CSP is satisfiable if its solution set is nonempty.
This is a well-formedness condition excluding trivial/contradictory CSPs. -/
def CSP.IsSatisfiable (P : CSP V D) : Prop :=
  P.Sol.Nonempty

/-- Satisfying assignment for the pinned CSP P|_{X=v}.
(Definition 3.3) -/
def CSP.IsSatisfyingPinned (P : CSP V D)
    (X : V) (v : D X) (Î² : âˆ€ w : V, D w) : Prop :=
  Î² X = v âˆ§ P.IsSatisfying Î²

/-- The constraint hypergraph of a CSP: vertices are all variables,
hyperedges are the variable sets of non-empty constraint scopes.
(Definition 3.4) -/
def CSP.constraintHypergraph (P : CSP V D) : Hypergraph V where
  verts := Finset.univ
  edges := (((P.constraints.filter (fun c => c.scope â‰  [])).map
    (fun c => c.scope.toFinset)) : List (Finset V))
  edges_subset := by
    intro e _
    exact Finset.subset_univ e
  edges_nonempty := by
    intro e he
    -- edges is a list coerced to multiset. Unpack membership.
    rw [Multiset.mem_coe] at he
    -- he : e âˆˆ List.map toFinset (List.filter (scope â‰  []) constraints)
    obtain âŸ¨c, hc_in, rflâŸ© := List.mem_map.mp he
    have hne : c.scope â‰  [] := by
      have := (List.mem_filter.mp hc_in).2
      exact of_decide_eq_true this
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hne
    rwa [List.toFinset_eq_empty_iff] at h

/-- A partial assignment is consistent if it satisfies all constraints
whose scope is fully contained in W.
(Definition 3.5) -/
def CSP.IsConsistent (P : CSP V D) (W : Finset V)
    (Ïƒ : âˆ€ (v : V), v âˆˆ W â†’ D v) : Prop :=
  âˆ€ c âˆˆ P.constraints,
    (h : c.scope.toFinset âŠ† W) â†’
    c.relation (fun i => Ïƒ (c.scope.get i)
      (h (List.mem_toFinset.mpr (c.scope.get_mem i))))
