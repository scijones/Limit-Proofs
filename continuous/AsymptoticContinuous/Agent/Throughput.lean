/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Throughput Bounds — Theorem 7.1

Three results, in decreasing generality:

* `throughput_cut_bound` — **unconditional**: the throughput is bounded by
  the total capacity of *any* observation–action separator.  No treewidth
  or placement hypothesis; this is the maximal-scope statement.
* `throughput_le_sensor_capacity` — **unconditional corollary**: the
  observation set itself is (vacuously) a separator, so
  `I(t) ≤ |V_O| · R_max` always.
* `throughput_rate_bound` — the `(k+1)·R_max` form, under the explicit
  `InterfaceSeparated` hypothesis: when the sensors and effectors lie on
  opposite sides of a node of a width-≤k decomposition, the (proved)
  boundary separator of `Basic/Separator.lean` has size ≤ k+1.

The former version of `throughput_rate_bound` concluded the `(k+1)` bound
from `tw(G_eff) ≤ k` alone, via an axiom asserting small separators between
arbitrary coordinate sets.  That axiom was false (treewidth does not bound
the observation–action cut when the two sets interleave), so the hypothesis
is now the honest one, and the unconditional bounds above cover every
system with no hypothesis at all.
-/

set_option autoImplicit false

/-- **Unconditional cut bound.**  For any separator `C` between the
observation and action coordinate sets, the throughput is at most the
total capacity of `C`. -/
theorem throughput_cut_bound (sys : ContinuousSystem) (C : Finset (Fin sys.N))
    (hC : sys.G_eff.IsSeparatingSet sys.V_O sys.V_A C) :
    sys.throughput ≤ C.sum sys.R := by
  have hmc : IsMarkovChain sys.obs (sys.coordsRV C) sys.action sys.state :=
    sys.graph_structured C hC
  calc sys.throughput
      = I(sys.obs ; sys.action | sys.state) := rfl
    _ ≤ I(sys.obs ; sys.coordsRV C | sys.state) :=
        data_processing_inequality sys.obs (sys.coordsRV C) sys.action sys.state hmc
    _ ≤ C.sum sys.R := sys.rate_bound C

/-- Capacity of a coordinate set is at most `card · R_max`. -/
theorem sum_R_le_card_mul_R_max (sys : ContinuousSystem) (C : Finset (Fin sys.N)) :
    C.sum sys.R ≤ (C.card : ℝ) * sys.R_max := by
  have h1 : C.sum sys.R ≤ C.card • sys.R_max :=
    Finset.sum_le_card_nsmul C sys.R sys.R_max (fun i _ => sys.le_R_max i)
  rwa [nsmul_eq_mul] at h1

/-- **Unconditional sensor-capacity bound.**  The observation set is
vacuously a separator (`V_O \ V_O = ∅`), so every system — with no
structural hypothesis whatsoever — satisfies
`I(t) ≤ |V_O| · R_max`. -/
theorem throughput_le_sensor_capacity (sys : ContinuousSystem) :
    sys.throughput ≤ (sys.V_O.card : ℝ) * sys.R_max := by
  have hsep : sys.G_eff.IsSeparatingSet sys.V_O sys.V_A sys.V_O := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    exact absurd hu.1 hu.2
  exact le_trans (throughput_cut_bound sys sys.V_O hsep)
    (sum_R_le_card_mul_R_max sys sys.V_O)

/-- **Theorem 7.1: Throughput Rate Bound.**

If the observation and action coordinates lie on opposite sides of some
node of a width-≤k rooted tree decomposition of `G_eff`
(`InterfaceSeparated`), then
    I(t) ≤ (k + 1) · R_max.
The separator is the node's boundary: it has size ≤ k+1
(`boundary_card_le`) and separates the two sides (`boundary_separates`) —
both proved, not assumed. -/
theorem throughput_rate_bound (sys : ContinuousSystem) (k : ℕ)
    (hsep : sys.InterfaceSeparated k) :
    sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  obtain ⟨td, hw, r, t, hO, hA⟩ := hsep
  have hC_sep : sys.G_eff.IsSeparatingSet sys.V_O sys.V_A (td.boundary r t) :=
    boundary_separates td r t sys.V_O sys.V_A hO hA
  have hC_card : (td.boundary r t).card ≤ k + 1 :=
    boundary_card_le td r t k hw
  calc sys.throughput
      ≤ (td.boundary r t).sum sys.R := throughput_cut_bound sys _ hC_sep
    _ ≤ ((td.boundary r t).card : ℝ) * sys.R_max :=
        sum_R_le_card_mul_R_max sys _
    _ ≤ (↑(k + 1) : ℝ) * sys.R_max := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hC_card
        · exact sys.R_max_nonneg
