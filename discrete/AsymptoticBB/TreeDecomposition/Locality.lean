/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.TreeDecomposition.Defs
import AsymptoticBB.Basic.CSP

/-!
# Constraint Locality in Tree Decompositions

Lemma 11.1: every constraint scope is contained in some bag.
-/

set_option autoImplicit false

universe u v

/-- Lemma 11.1 (Constraint locality).
For every constraint C_j, all variables in its scope appear together in at
least one bag of the tree decomposition.

This is immediate from the edge cover property (T2). -/
theorem constraint_locality {V : Type u} [DecidableEq V] [Fintype V]
    {D : V → Type v} (P : CSP V D) (td : TreeDecomposition P.constraintHypergraph)
    (c : Constraint V D) (hc : c ∈ P.constraints) (hne : c.scope ≠ []) :
    ∃ i : td.I, c.scope.toFinset ⊆ td.bag i := by
  have he : c.scope.toFinset ∈ P.constraintHypergraph.edges := by
    change c.scope.toFinset ∈ (((P.constraints.filter (fun c => c.scope ≠ [])).map
      (fun c => c.scope.toFinset)) : List (Finset V))
    exact List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, decide_eq_true hne⟩, rfl⟩
  exact td.edge_cover _ he
