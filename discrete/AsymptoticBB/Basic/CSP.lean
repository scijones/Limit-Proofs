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

Definitions 3.1–3.5 from the paper: CSP instances, satisfying assignments,
pinned CSPs, constraint hypergraphs, and partial assignments.
-/

set_option autoImplicit false

universe u v

variable {V : Type u} [DecidableEq V] [Fintype V]
variable {D : V → Type v}

/-- A constraint consists of a scope (an ordered tuple of distinct variables) and
a constraint relation (a predicate on tuples over the domains of those variables).
(Part of Definition 3.1) -/
structure Constraint (V : Type u) (D : V → Type v) where
  scope : List V
  scope_nodup : scope.Nodup
  relation : (∀ i : Fin scope.length, D (scope.get i)) → Prop

/-- The arity of a constraint is the length of its scope. -/
def Constraint.arity' (c : Constraint V D) : ℕ :=
  c.scope.length

/-- A CSP instance ⟨V, D, C⟩. V and D are parameters; constraints are data.
(Definition 3.1) -/
structure CSP (V : Type u) [DecidableEq V] (D : V → Type v) where
  constraints : List (Constraint V D)

/-- A satisfying assignment satisfies all constraints.
(Definition 3.2) -/
def CSP.IsSatisfying (P : CSP V D) (β : ∀ v : V, D v) : Prop :=
  ∀ c ∈ P.constraints,
    c.relation (fun i => β (c.scope.get i))

/-- The solution set of a CSP. (Definition 3.2) -/
def CSP.Sol (P : CSP V D) : Set (∀ v : V, D v) :=
  { β | P.IsSatisfying β }

/-- A CSP is satisfiable if its solution set is nonempty.
This is a well-formedness condition excluding trivial/contradictory CSPs. -/
def CSP.IsSatisfiable (P : CSP V D) : Prop :=
  P.Sol.Nonempty

/-- Satisfying assignment for the pinned CSP P|_{X=v}.
(Definition 3.3) -/
def CSP.IsSatisfyingPinned (P : CSP V D)
    (X : V) (v : D X) (β : ∀ w : V, D w) : Prop :=
  β X = v ∧ P.IsSatisfying β

/-- The constraint hypergraph of a CSP: vertices are all variables,
hyperedges are the variable sets of non-empty constraint scopes.
(Definition 3.4) -/
def CSP.constraintHypergraph (P : CSP V D) : Hypergraph V where
  verts := Finset.univ
  edges := (((P.constraints.filter (fun c => c.scope ≠ [])).map
    (fun c => c.scope.toFinset)) : List (Finset V))
  edges_subset := by
    intro e _
    exact Finset.subset_univ e
  edges_nonempty := by
    intro e he
    -- edges is a list coerced to multiset. Unpack membership.
    rw [Multiset.mem_coe] at he
    -- he : e ∈ List.map toFinset (List.filter (scope ≠ []) constraints)
    obtain ⟨c, hc_in, rfl⟩ := List.mem_map.mp he
    have hne : c.scope ≠ [] := by
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
    (σ : ∀ (v : V), v ∈ W → D v) : Prop :=
  ∀ c ∈ P.constraints,
    (h : c.scope.toFinset ⊆ W) →
    c.relation (fun i => σ (c.scope.get i)
      (h (List.mem_toFinset.mpr (c.scope.get_mem i))))
