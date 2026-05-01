/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Throughput Rate Bound — Theorem 7.1

The per-instance throughput bound.
Given ONE system with tw(G_eff) ≤ k, the throughput is ≤ (k+1)·R_max.

When k is small, this is a tight bottleneck constraint.
When k = N-1 (trivial), it gives I ≤ N·R_max (which is just subadditivity).
The theorem itself is correct; the vacuousness issue is in the
necessity axioms that try to conclude ∃ k (which is always satisfiable).
-/

set_option autoImplicit false

/-- **Theorem 7.1: Throughput Rate Bound.**

For any continuous system satisfying Axioms 1–4, if tw(G_eff) ≤ k then
    I(t) ≤ (k + 1) · R_max. -/
theorem throughput_rate_bound (sys : ContinuousSystem) (k : ℕ)
    (htw : sys.G_eff.HasTreewidthAtMost k) :
    sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  obtain ⟨C, hC_card, hC_sep⟩ :=
    separator_existence_from_treewidth sys.G_eff sys.V_O sys.V_A k htw
  have hmc : IsMarkovChain sys.obs (sys.coordsRV C) sys.action sys.state :=
    sys.graph_structured C hC_sep
  calc sys.throughput
      = I(sys.obs ; sys.action | sys.state) := rfl
    _ ≤ I(sys.obs ; sys.coordsRV C | sys.state) :=
        data_processing_inequality sys.obs (sys.coordsRV C) sys.action sys.state hmc
    _ ≤ ConditionalEntropy (sys.coordsRV C) sys.state :=
        mi_le_conditional_entropy sys.obs (sys.coordsRV C) sys.state
    _ ≤ C.sum sys.R := sys.rate_bound C
    _ ≤ ↑C.card * sys.R_max := by
        have h1 : C.sum sys.R ≤ C.card • sys.R_max :=
          Finset.sum_le_card_nsmul C sys.R sys.R_max (fun i _ => sys.le_R_max i)
        rw [nsmul_eq_mul] at h1
        exact h1
    _ ≤ (↑(k + 1) : ℝ) * sys.R_max := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hC_card
        · exact sys.R_max_nonneg
