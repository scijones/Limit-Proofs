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

The continuous inference system satisfying Axioms 1â€“4.
`ContinuousSystem` already bundles N : â„• internally, so it is
ALREADY a per-instance type â€” no analogue of the discrete's
`SizedHypergraph` wrapper is needed.

## Main definitions

* `SimpleGraph.IsSeparatingSet` â€” vertex separator between two sets
* `ContinuousSystem` â€” structure encoding Axioms 1â€“4 + rate structure
* `ContinuousSystem.throughput` â€” instantaneous information throughput I(t)
* `ContinuousSystem.R_max` â€” max per-coordinate information rate
-/

set_option autoImplicit false

def SimpleGraph.IsSeparatingSet {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B C : Finset V) : Prop :=
  âˆ€ u âˆˆ A \ C, âˆ€ v âˆˆ B \ C, âˆ€ (p : G.Walk u v),
    âˆƒ w, w âˆˆ C âˆ§ w âˆˆ p.support

axiom separator_existence_from_treewidth
    {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (A B : Finset V) (k : â„•)
    (htw : G.HasTreewidthAtMost k) :
    âˆƒ C : Finset V, C.card â‰¤ k + 1 âˆ§ G.IsSeparatingSet A B C

structure ContinuousSystem where
  N : â„•
  hN : 0 < N
  G_eff : SimpleGraph (Fin N)
  V_O : Finset (Fin N)
  V_A : Finset (Fin N)
  obs : RandomVariable
  action : RandomVariable
  state : RandomVariable
  coordsRV : Finset (Fin N) â†’ RandomVariable
  R : Fin N â†’ â„
  hR_nonneg : âˆ€ i, 0 â‰¤ R i
  graph_structured :
    âˆ€ (C : Finset (Fin N)),
      G_eff.IsSeparatingSet V_O V_A C â†’
      IsMarkovChain obs (coordsRV C) action state
  rate_bound :
    âˆ€ (C : Finset (Fin N)),
      ConditionalEntropy (coordsRV C) state â‰¤ C.sum R

noncomputable def ContinuousSystem.throughput (sys : ContinuousSystem) : â„ :=
  I(sys.obs ; sys.action | sys.state)

noncomputable def ContinuousSystem.R_max (sys : ContinuousSystem) : â„ :=
  Finset.univ.sup' (âŸ¨âŸ¨0, sys.hNâŸ©, Finset.mem_univ _âŸ©) sys.R

theorem ContinuousSystem.le_R_max (sys : ContinuousSystem)
    (i : Fin sys.N) : sys.R i â‰¤ sys.R_max :=
  Finset.le_sup' sys.R (Finset.mem_univ i)

theorem ContinuousSystem.R_max_nonneg (sys : ContinuousSystem) :
    0 â‰¤ sys.R_max :=
  le_trans (sys.hR_nonneg âŸ¨0, sys.hNâŸ©) (sys.le_R_max âŸ¨0, sys.hNâŸ©)

/-! ## Partition function tractability predicates

These are placed here (rather than in SystemClass.lean) so that
Necessity/*.lean files can reference them without creating import cycles.
SystemClass.lean imports the Necessity files and lifts these predicates
to the class level. -/

/-- The system's partition function is tractable (exact).
Note: the "for all Î·" quantifier is internal to this predicate. -/
opaque HasTractablePartitionFunction (sys : ContinuousSystem) : Prop

/-- The system's approximate partition function is tractable.
Concretely: there exists a poly-time algorithm computing log Z to
within additive error 1 for any choice of strictly positive potentials
on G_eff. -/
opaque HasTractableApproxPartitionFunction (sys : ContinuousSystem) : Prop
