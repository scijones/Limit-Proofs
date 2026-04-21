/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Throughput Rate Bound â€” Theorem 7.1

The per-instance throughput bound.
Given ONE system with tw(G_eff) â‰¤ k, the throughput is â‰¤ (k+1)Â·R_max.

When k is small, this is a tight bottleneck constraint.
When k = N-1 (trivial), it gives I â‰¤ NÂ·R_max (which is just subadditivity).
The theorem itself is correct; the vacuousness issue is in the
necessity axioms that try to conclude âˆƒ k (which is always satisfiable).
-/

set_option autoImplicit false

/-- **Theorem 7.1: Throughput Rate Bound.**

For any continuous system satisfying Axioms 1â€“4, if tw(G_eff) â‰¤ k then
    I(t) â‰¤ (k + 1) Â· R_max. -/
theorem throughput_rate_bound (sys : ContinuousSystem) (k : â„•)
    (htw : sys.G_eff.HasTreewidthAtMost k) :
    sys.throughput â‰¤ (â†‘(k + 1) : â„) * sys.R_max := by
  obtain âŸ¨C, hC_card, hC_sepâŸ© :=
    separator_existence_from_treewidth sys.G_eff sys.V_O sys.V_A k htw
  have hmc : IsMarkovChain sys.obs (sys.coordsRV C) sys.action sys.state :=
    sys.graph_structured C hC_sep
  calc sys.throughput
      = I(sys.obs ; sys.action | sys.state) := rfl
    _ â‰¤ I(sys.obs ; sys.coordsRV C | sys.state) :=
        data_processing_inequality sys.obs (sys.coordsRV C) sys.action sys.state hmc
    _ â‰¤ ConditionalEntropy (sys.coordsRV C) sys.state :=
        mi_le_conditional_entropy sys.obs (sys.coordsRV C) sys.state
    _ â‰¤ C.sum sys.R := sys.rate_bound C
    _ â‰¤ â†‘C.card * sys.R_max := by
        have h1 : C.sum sys.R â‰¤ C.card â€¢ sys.R_max :=
          Finset.sum_le_card_nsmul C sys.R sys.R_max (fun i _ => sys.le_R_max i)
        rw [nsmul_eq_mul] at h1
        exact h1
    _ â‰¤ (â†‘(k + 1) : â„) * sys.R_max := by
        apply mul_le_mul_of_nonneg_right
        Â· exact_mod_cast hC_card
        Â· exact sys.R_max_nonneg
