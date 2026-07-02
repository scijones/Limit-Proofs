/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Basic.Graph
import AsymptoticContinuous.InformationTheory.Axioms
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Basic

/-!
# Continuous Agent Model

The continuous inference system satisfying Axioms 1–4.
`ContinuousSystem` already bundles N : ℕ internally, so it is
ALREADY a per-instance type — no analogue of the discrete's
`SizedHypergraph` wrapper is needed.

## Main definitions

* `SimpleGraph.IsSeparatingSet` — vertex separator between two sets
* `ContinuousSystem` — structure encoding Axioms 1–4 + rate structure
* `ContinuousSystem.throughput` — instantaneous information throughput I(t)
* `ContinuousSystem.R_max` — max per-coordinate information rate
-/

set_option autoImplicit false

def SimpleGraph.IsSeparatingSet {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B C : Finset V) : Prop :=
  ∀ u ∈ A \ C, ∀ v ∈ B \ C, ∀ (p : G.Walk u v),
    ∃ w, w ∈ C ∧ w ∈ p.support

axiom separator_existence_from_treewidth
    {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (k : ℕ)
    (htw : G.HasTreewidthAtMost k) :
    ∃ C : Finset V, C.card ≤ k + 1 ∧ G.IsSeparatingSet A B C

structure ContinuousSystem where
  N : ℕ
  hN : 0 < N
  G_eff : SimpleGraph (Fin N)
  V_O : Finset (Fin N)
  V_A : Finset (Fin N)
  obs : RandomVariable
  action : RandomVariable
  state : RandomVariable
  coordsRV : Finset (Fin N) → RandomVariable
  R : Fin N → ℝ
  hR_nonneg : ∀ i, 0 ≤ R i
  graph_structured :
    ∀ (C : Finset (Fin N)),
      G_eff.IsSeparatingSet V_O V_A C →
      IsMarkovChain obs (coordsRV C) action state
  /-- Per-coordinate rate constraint, in capacity (mutual-information)
  form: the coordinates in `C` jointly convey at most `Σ_{i∈C} R i`
  units of information about the observation given the state.

  Deliberately NOT the entropy form `H(coordsRV C | state) ≤ Σ R`:
  differential entropy can be negative, and the bridging inequality
  `I ≤ H` is false for continuous variables, so the entropy form is
  sound only in a discrete model.  The MI form is the correct
  continuous statement (each coordinate is a channel of capacity
  `R i`), is non-negative-safe, and is also a weaker hypothesis —
  making every theorem proved from it stronger. -/
  rate_bound :
    ∀ (C : Finset (Fin N)),
      I(obs ; coordsRV C | state) ≤ C.sum R

noncomputable def ContinuousSystem.throughput (sys : ContinuousSystem) : ℝ :=
  I(sys.obs ; sys.action | sys.state)

noncomputable def ContinuousSystem.R_max (sys : ContinuousSystem) : ℝ :=
  Finset.univ.sup' (⟨⟨0, sys.hN⟩, Finset.mem_univ _⟩) sys.R

theorem ContinuousSystem.le_R_max (sys : ContinuousSystem)
    (i : Fin sys.N) : sys.R i ≤ sys.R_max :=
  Finset.le_sup' sys.R (Finset.mem_univ i)

theorem ContinuousSystem.R_max_nonneg (sys : ContinuousSystem) :
    0 ≤ sys.R_max :=
  le_trans (sys.hR_nonneg ⟨0, sys.hN⟩) (sys.le_R_max ⟨0, sys.hN⟩)

/-! ## Partition function tractability predicates

These are placed here (rather than in SystemClass.lean) so that
Necessity/*.lean files can reference them without creating import cycles.
SystemClass.lean imports the Necessity files and lifts these predicates
to the class level. -/

/-- The system's partition function is tractable (exact).
Note: the "for all η" quantifier is internal to this predicate. -/
opaque HasTractablePartitionFunction (sys : ContinuousSystem) : Prop

/-- The system's approximate partition function is tractable.
Concretely: there exists a poly-time algorithm computing log Z to
within additive error 1 for any choice of strictly positive potentials
on G_eff. -/
opaque HasTractableApproxPartitionFunction (sys : ContinuousSystem) : Prop
