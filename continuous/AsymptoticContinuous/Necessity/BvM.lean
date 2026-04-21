/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs

/-!
# Bernsteinâ€“von Mises Theorem

Per-instance theorem: regularity conditions force convergence to an
asymptotic exponential family (Gaussian posterior).

The BvM theorem's mathematical engine is Local Asymptotic Normality (LAN),
whose weakest sufficient condition is differentiability in quadratic mean
(DQM):

  âˆ« (âˆšp(x|Î¸+h) âˆ’ âˆšp(x|Î¸))/h âˆ’ á¹¡(x,Î¸))Â² dx â†’ 0  as h â†’ 0

This is van der Vaart (1998), Theorem 7.2 (DQM â†’ LAN) and
Theorem 10.1 (LAN + prior consistency â†’ BvM).

DQM allows kinks, piecewise-smooth likelihoods, L1-penalized models,
quantile regression, and ReLU-based generative models. The integral
in the DQM condition averages over x, so pointwise non-differentiability
in Î¸ at isolated x-values does not violate DQM.

DQM fails only for densities that change discontinuously as a function
of Î¸ in the LÂ²(Î¼) sense â€” e.g., parameter-dependent support (already
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

/-- The Fisher information matrix I(Î¸â‚€) is strictly positive definite
at the true parameter value.

This ensures the model is locally identifiable: distinct parameter values
near Î¸â‚€ induce distinct distributions. BvM fails at singular points
where the Fisher matrix is degenerate. -/
opaque FisherPositiveDefinite (sys : ContinuousSystem) : Prop

/-- The family {p(Â·|Î¸)} is differentiable in quadratic mean (DQM).

Formally: the map Î¸ â†¦ âˆšp(x|Î¸) is differentiable in LÂ²(Î¼), i.e.,
there exists a measurable function á¹¡(x, Î¸â‚€) such that

  âˆ« ((âˆšp(x|Î¸â‚€+h) âˆ’ âˆšp(x|Î¸â‚€))/â€–hâ€– âˆ’ á¹¡(x, Î¸â‚€)Â·(h/â€–hâ€–))Â² dÎ¼(x) â†’ 0

as â€–hâ€– â†’ 0.

DQM is the weakest standard condition under which LAN holds
(van der Vaart 1998, Theorem 7.2). LAN is the engine of BvM.

DQM is dramatically weaker than CÂ³:
- A kink in log p(x|Î¸) does NOT violate DQM (the LÂ² integral
  averages over x, smoothing the kink).
- LASSO, quantile regression, piecewise-smooth likelihoods,
  ReLU-based generative models: all satisfy DQM.

DQM fails only when âˆšp(Â·|Î¸) changes discontinuously in LÂ²,
meaning the density jumps in an averaged sense that can't be
linearly approximated. -/
opaque DifferentiableInQuadraticMean (sys : ContinuousSystem) : Prop

/-- The prior distribution Ï€(Î¸) is continuous and assigns strictly
positive probability mass in a neighborhood of the true parameter Î¸â‚€.

Without this, the posterior may not concentrate at the MLE, breaking
the asymptotic normality conclusion of BvM. -/
opaque PriorConsistent (sys : ContinuousSystem) : Prop

/-- The system is an asymptotic exponential family: the posterior
converges to a Gaussian (which is a member of the exponential family)
in total variation distance as data accumulates.

This is the conclusion of BvM. The specific Gaussian has mean = MLE
and covariance = I(Î¸â‚€)â»Â¹. We abstract this to `IsAsymptoticExpFamily`
because the proof only needs the exponential-family structure to invoke
partition-function hardness. -/
opaque IsAsymptoticExpFamily (sys : ContinuousSystem) : Prop

/-- **Bernsteinâ€“von Mises Theorem (via LAN).**

If a system has:
1. Strictly positive definite Fisher information at the true parameter,
2. Differentiability in quadratic mean (DQM), and
3. A consistent prior (positive near true parameter),

then the posterior converges to a Gaussian (asymptotic exponential family)
as data accumulates.

**Citation:** van der Vaart (1998), Theorems 7.2 (DQM â†’ LAN) and
10.1 (LAN + prior â†’ BvM). The composition gives: DQM + Fisher pos-def
+ prior consistent â†’ asymptotic exponential family.

DQM accommodates non-smooth models (LASSO, ReLU, piecewise-linear)
while retaining full mathematical rigor. The only exclusion is
families where âˆšp(Â·|Î¸) is discontinuous in LÂ².

Paper reference: Theorem 7.6, Axiom 6. -/
axiom bvm_theorem :
  âˆ€ (sys : ContinuousSystem),
    FisherPositiveDefinite sys â†’
    DifferentiableInQuadraticMean sys â†’
    PriorConsistent sys â†’
    IsAsymptoticExpFamily sys
