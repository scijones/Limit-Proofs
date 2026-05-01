/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs

/-!
# Pitman–Koopman–Darmois Theorem

Per-instance theorem: exact sufficiency + parameter-independent support
forces exponential family.

The PKD theorem requires that the support of the probability distribution
does not depend on the parameter θ. Without this condition, distributions
like Uniform(0, θ) admit fixed-dimension sufficient statistics (the max
order statistic) but are not exponential families (their support [0, θ]
depends on θ).

### References
- Pitman, E. J. G. (1936). "Sufficient statistics and intrinsic accuracy."
- Koopman, B. O. (1936). "On distributions admitting a sufficient statistic."
- Darmois, G. (1935). "Sur les lois de probabilité à estimation exhaustive."
- Geyer, C. J. (2016). Stat 5421 Lecture Notes: Exponential Families, Part I.
-/

set_option autoImplicit false

/-- The system admits exact sufficient statistics of fixed dimension
(independent of sample size N). -/
opaque HasExactSufficiency (sys : ContinuousSystem) : Prop

/-- The support of the system's probability distribution does not depend
on the parameter θ. This is the "common support" or "parameter-independent
support" condition required by PKD.

Without this condition, distributions like Uniform(0, θ) have
fixed-dimension sufficient statistics but are not exponential families.
The PKD theorem is provably false without this hypothesis. -/
opaque HasIndependentSupport (sys : ContinuousSystem) : Prop

/-- The system belongs to an exponential family (the conclusion of PKD). -/
opaque IsExponentialFamily (sys : ContinuousSystem) : Prop

/-- **Pitman–Koopman–Darmois Theorem (1935–1936).**

If a system admits exact sufficient statistics of fixed dimension AND
the support of its distribution is independent of the parameter, then
the system belongs to an exponential family.

Both hypotheses are essential:
- `HasExactSufficiency` encodes the existence of a fixed-dim sufficient statistic.
- `HasIndependentSupport` encodes support independence (rules out Uniform(0,θ) etc.).

Paper reference: Theorem 7.4, Axiom 5. -/
axiom pkd_theorem :
  ∀ (sys : ContinuousSystem),
    HasExactSufficiency sys → HasIndependentSupport sys → IsExponentialFamily sys
