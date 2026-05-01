/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs

/-!
# Bernstein–von Mises Theorem

Per-instance theorem: regularity conditions force convergence to an
asymptotic exponential family (Gaussian posterior).

The BvM theorem's mathematical engine is Local Asymptotic Normality (LAN),
whose weakest sufficient condition is differentiability in quadratic mean
(DQM):

  ∫ (√p(x|θ+h) − √p(x|θ))/h − ṡ(x,θ))² dx → 0  as h → 0

This is van der Vaart (1998), Theorem 7.2 (DQM → LAN) and
Theorem 10.1 (LAN + prior consistency → BvM).

DQM allows kinks, piecewise-smooth likelihoods, L1-penalized models,
quantile regression, and ReLU-based generative models. The integral
in the DQM condition averages over x, so pointwise non-differentiability
in θ at isolated x-values does not violate DQM.

DQM fails only for densities that change discontinuously as a function
of θ in the L²(μ) sense — e.g., parameter-dependent support (already
excluded by `HasIndependentSupport` on the exact track).

### References
- Bernstein, S. N. (1917). "Theory of Probability" (Russian original).
- von Mises, R. (1931). "Wahrscheinlichkeitsrechnung."
- Le Cam, L. (1953). "On some asymptotic properties of maximum likelihood
  estimates and related Bayes estimates."
- van der Vaart, A. W. (1998). *Asymptotic Statistics*, Cambridge,
  Theorems 7.2, 10.1.
-/

set_option autoImplicit false

/-- The Fisher information matrix I(θ₀) is strictly positive definite
at the true parameter value.

This ensures the model is locally identifiable: distinct parameter values
near θ₀ induce distinct distributions. BvM fails at singular points
where the Fisher matrix is degenerate. -/
opaque FisherPositiveDefinite (sys : ContinuousSystem) : Prop

/-- The family {p(·|θ)} is differentiable in quadratic mean (DQM).

Formally: the map θ ↦ √p(x|θ) is differentiable in L²(μ), i.e.,
there exists a measurable function ṡ(x, θ₀) such that

  ∫ ((√p(x|θ₀+h) − √p(x|θ₀))/‖h‖ − ṡ(x, θ₀)·(h/‖h‖))² dμ(x) → 0

as ‖h‖ → 0.

DQM is the weakest standard condition under which LAN holds
(van der Vaart 1998, Theorem 7.2). LAN is the engine of BvM.

DQM is dramatically weaker than C³:
- A kink in log p(x|θ) does NOT violate DQM (the L² integral
  averages over x, smoothing the kink).
- LASSO, quantile regression, piecewise-smooth likelihoods,
  ReLU-based generative models: all satisfy DQM.

DQM fails only when √p(·|θ) changes discontinuously in L²,
meaning the density jumps in an averaged sense that can't be
linearly approximated. -/
opaque DifferentiableInQuadraticMean (sys : ContinuousSystem) : Prop

/-- The prior distribution π(θ) is continuous and assigns strictly
positive probability mass in a neighborhood of the true parameter θ₀.

Without this, the posterior may not concentrate at the MLE, breaking
the asymptotic normality conclusion of BvM. -/
opaque PriorConsistent (sys : ContinuousSystem) : Prop

/-- The system is an asymptotic exponential family: the posterior
converges to a Gaussian (which is a member of the exponential family)
in total variation distance as data accumulates.

This is the conclusion of BvM. The specific Gaussian has mean = MLE
and covariance = I(θ₀)⁻¹. We abstract this to `IsAsymptoticExpFamily`
because the proof only needs the exponential-family structure to invoke
partition-function hardness. -/
opaque IsAsymptoticExpFamily (sys : ContinuousSystem) : Prop

/-- **Bernstein–von Mises Theorem (via LAN).**

If a system has:
1. Strictly positive definite Fisher information at the true parameter,
2. Differentiability in quadratic mean (DQM), and
3. A consistent prior (positive near true parameter),

then the posterior converges to a Gaussian (asymptotic exponential family)
as data accumulates.

**Citation:** van der Vaart (1998), Theorems 7.2 (DQM → LAN) and
10.1 (LAN + prior → BvM). The composition gives: DQM + Fisher pos-def
+ prior consistent → asymptotic exponential family.

DQM accommodates non-smooth models (LASSO, ReLU, piecewise-linear)
while retaining full mathematical rigor. The only exclusion is
families where √p(·|θ) is discontinuous in L².

Paper reference: Theorem 7.6, Axiom 6. -/
axiom bvm_theorem :
  ∀ (sys : ContinuousSystem),
    FisherPositiveDefinite sys →
    DifferentiableInQuadraticMean sys →
    PriorConsistent sys →
    IsAsymptoticExpFamily sys
