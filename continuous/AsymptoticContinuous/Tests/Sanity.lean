/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Throughput

/-!
# Non-Vacuity Guards

`RandomVariable` is an opaque type and `IsMarkovChain` an uninterpreted
predicate, so without witnesses `ContinuousSystem` could be an empty
type and every class-level theorem vacuously true.  This module
constructs a concrete system from the three-axiom witness interface in
`InformationTheory/Axioms.lean` (each axiom a textbook-true fact) and
kernel-checks that:

1. `ContinuousSystem` is inhabited (`trivialSystem`);
2. its effective graph provably has treewidth 0, via an explicit
   one-bag `TreeDecomposition` — the same construction that makes
   `∃ k, tw ≤ k` trivially true per-instance, documented here so the
   deletion of the per-instance necessity axioms is self-explaining;
3. `throughput_rate_bound` applies non-vacuously: the hypothesis is
   satisfiable and the conclusion `throughput ≤ 1 · R_max` holds, with
   `throughput = 0` computed exactly.

None of this is load-bearing for the class-level results; it certifies
they are not theorems about the empty type.
-/

set_option autoImplicit false

/-! ## A one-bag tree decomposition of the empty graph on `Fin 1` -/

/-- The single-node tree decomposition: one bag containing the single
vertex.  Witnesses `tw(⊥ : SimpleGraph (Fin 1)) ≤ 0`. -/
def trivialTD : TreeDecomposition (⊥ : SimpleGraph (Fin 1)) where
  I := PUnit
  tree := ⊥
  tree_isTree := by
    constructor
    · exact ⟨fun u v => (Subsingleton.elim u v) ▸ SimpleGraph.Reachable.refl u⟩
    · intro v p hp
      cases p with
      | nil => exact hp.ne_nil rfl
      | cons h _ => exact h.elim
  bag := fun _ => Finset.univ
  vertex_cover := fun v => ⟨PUnit.unit, Finset.mem_univ v⟩
  edge_cover := fun u v h => h.elim
  running_intersection := by
    intro v
    haveI : Nonempty {i : PUnit | v ∈ (Finset.univ : Finset (Fin 1))} :=
      ⟨⟨PUnit.unit, Finset.mem_univ v⟩⟩
    exact ⟨fun a b => (Subsingleton.elim a b) ▸ SimpleGraph.Reachable.refl a⟩

theorem trivialTD_width : trivialTD.width = 0 := by
  unfold TreeDecomposition.width trivialTD
  simp
  rfl

theorem trivial_graph_tw0 : (⊥ : SimpleGraph (Fin 1)).HasTreewidthAtMost 0 :=
  ⟨trivialTD, le_of_eq trivialTD_width⟩

/-! ## A concrete continuous system -/

/-- The trivial system: one coordinate, empty effective graph, all
random variables equal to the witness, zero rates.  Every structure
field is discharged from the witness interface. -/
noncomputable def trivialSystem : ContinuousSystem where
  N := 1
  hN := Nat.one_pos
  G_eff := ⊥
  V_O := Finset.univ
  V_A := Finset.univ
  obs := witnessRV
  action := witnessRV
  state := witnessRV
  coordsRV := fun _ => witnessRV
  R := fun _ => 0
  hR_nonneg := fun _ => le_refl 0
  graph_structured := fun _ _ =>
    isMarkovChain_self_right witnessRV witnessRV witnessRV
  rate_bound := fun C => by
    rw [cmi_cond_self witnessRV witnessRV]
    simp

/-- `ContinuousSystem` is inhabited. -/
theorem continuousSystem_nonempty : Nonempty ContinuousSystem :=
  ⟨trivialSystem⟩

/-- The trivial system's throughput is exactly zero. -/
theorem trivialSystem_throughput : trivialSystem.throughput = 0 :=
  cmi_cond_self witnessRV witnessRV

/-- **Non-vacuity of the throughput bound**: the hypothesis of
`throughput_rate_bound` is satisfiable (by `trivialSystem` at k = 0)
and its conclusion holds. -/
theorem throughput_rate_bound_nonvacuous :
    trivialSystem.throughput ≤ ((0 + 1 : ℕ) : ℝ) * trivialSystem.R_max :=
  throughput_rate_bound trivialSystem 0 trivial_graph_tw0
