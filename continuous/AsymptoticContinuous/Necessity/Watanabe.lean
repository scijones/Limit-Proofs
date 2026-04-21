/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs

/-!
# Watanabe Backward Reduction â€” Singular Model Bridge

For singular models, BvM fails: the Fisher information is degenerate
(rank-deficient or zero) at the true parameter wâ‚€. This includes neural
networks, mixture models, reduced-rank regression, HMMs with redundant
states â€” essentially all models of practical interest in modern ML.

The Watanabe bridge provides an alternative route:
  learning success + latent variables â†’ tractable partition function.
This arrives at the same downstream input (HasTractableApproxPartitionFunction)
as BvM but without requiring regularity.

## The argument

### Step 1: Uniqueness (Watanabe 2009, Theorems 6.7 + 7.2)

For any statistical model (regular or singular), the Bayes posterior
predictive p(x_{n+1} | x^n) = Z_{n+1}/Z_n is the unique predictor
achieving the optimal generalization rate:

    G_n = K(w*) + (Î»/n) log n + o(log n / n)

where Î» is the real log canonical threshold (RLCT).

In the regular case, MLE also achieves an optimal rate (d/(2n)), so
non-Bayesian methods exist. In the singular case, MLE may not exist
(degenerate Fisher), or achieves the worse rate d/(2n) > Î»/n Â· log n.
The Bayes predictive is the uniquely optimal method.

### Step 2: Internal computational requirements

If a polynomial-time learner achieves the optimal rate, it must be
computing something equivalent to the Bayes predictive (by uniqueness).
The Bayes predictive for a graphical model requires evaluating the
likelihood p(x_obs | w) at polynomially many parameter values w (for
MCMC sampling, variational optimization, or numerical integration of the
posterior).

For a graphical model with latent variables, each likelihood evaluation:

    p(x_obs | w) = (1/Z(w)) Î£_h âˆ_C Ïˆ_C(x_C, h_C; w)

requires marginalizing over the hidden variables h. This marginalization
is a sum-product computation on the graph whose complexity is governed
by the treewidth of G_eff. Therefore the poly-time learner must be
performing poly-time partition function evaluations.

### Step 3: Connection to Marx

The learner's success implies poly-time Z(w) computation. The existing
class_partition_general_necessity axiom (Marx 2010, under ETH) then
gives: tractable Z across a class with unbounded N â†’ bounded treewidth.

## Non-circularity

This argument combines two elements:
- BACKWARD (uniqueness): the learner's success means it computes the
  Bayes predictive, not something else
- FORWARD (analysis of Bayes predictive): the Bayes predictive requires
  Z(w) evaluations for graphical models with latents

We axiomatize the conclusion directly:
  poly-time optimal learning + latents â†’ tractable Z.

## On latent variables

The HasLatentVariables hypothesis is genuinely load-bearing.

For fully-observed models without latents:
  p(x | w) = âˆ_C Ïˆ_C(x_C; w) / Z(w)
MCMC methods can use likelihood ratios p(x|wâ‚)/p(x|wâ‚‚) = Z(wâ‚‚)/Z(wâ‚) Â·
âˆ(Ïˆ ratio), where Z cancels. So inference can be tractable without
computing Z.

For models with latents:
  p(x_obs | w) = Î£_h âˆ_C Ïˆ_C(x_obs, h; w) / Z(w)
The marginalization over h is a sum over the graph that cannot be avoided
by taking ratios. Each likelihood evaluation requires a sum-product
computation whose complexity is governed by treewidth.

Without this hypothesis, a fully-observed singular model could
hypothetically achieve optimal learning via likelihood-ratio MCMC
without ever computing Z(w), evading the Marx connection.

## References

- Watanabe, S. (2009). *Algebraic Geometry and Statistical Learning
  Theory*. Cambridge University Press. Theorems 6.7, 7.2.
- Watanabe, S. (2013). "A Widely Applicable Bayesian Information
  Criterion." *JMLR* 14:867â€“897.
- Marx, D. (2010). "Can You Beat Treewidth?" *Theory of Computing*
  6:85â€“112. (JACM 2013 version: Theorem 1.4.)
-/

set_option autoImplicit false

/-- The system is a graphical model with latent variables: the likelihood
p(x_obs | w) requires marginalizing over hidden variables h, which is a
sum-product computation on G_eff.

This is the condition that makes Z(w) evaluation unavoidable: without
latents, likelihood ratios can cancel Z, but with latents, the
marginalization over h IS a partition-function computation.

Concretely: the system's joint distribution factors as
  p(x_obs, h | w) = (1/Z(w)) âˆ_C Ïˆ_C(x_C, h_C; w)
and the observed-data likelihood requires
  p(x_obs | w) = Î£_h p(x_obs, h | w)
which is a sum-product computation on the graph. -/
opaque HasLatentVariables (sys : ContinuousSystem) : Prop

/-- There exists a polynomial-time algorithm that, when given data
from the system, achieves the Watanabe-optimal generalization rate:

    G_n = K(w*) + (Î»/n) log n + o(log n / n)

where Î» is the real log canonical threshold.

IMPORTANT: This predicate encodes BOTH success AND tractability:
- The learner achieves the optimal rate (not just any rate)
- The learner runs in polynomial time in n and N

Without the poly-time requirement, an exponential-time exact Bayesian
always achieves the optimal rate, and the predicate would be trivially
true. The computational content is in the conjunction: achieving the
optimal rate WHILE running in poly-time.

This is analogous to HasTractableApproxPartitionFunction, but phrased
in terms of learning success rather than partition function computation.
The watanabe_backward_reduction axiom connects the two. -/
opaque TractableWatanabeOptimalLearning (sys : ContinuousSystem) : Prop

/-- **Watanabe Backward Reduction (v4).**

If a system is a graphical model with latent variables and admits a
polynomial-time learner achieving the Watanabe-optimal generalization
rate, then the system has a tractable approximate partition function.

The argument (see module docstring for details):
1. Watanabe uniqueness: the optimal-rate learner must compute (something
   equivalent to) the Bayes posterior predictive p(x_{n+1}|x^n).
2. The Bayes predictive requires evaluating p(x_obs|w) at poly-many w
   values (for posterior sampling/integration).
3. For graphical models with latents, each p(x_obs|w) evaluation
   requires the partition function Z(w) via marginalization over h.
4. The learner runs in poly-time (encoded in TractableWatanabeOptimalLearning).
5. Therefore: Z(w) is evaluated in poly-time â†’ HasTractableApproxPartitionFunction.

The output type (HasTractableApproxPartitionFunction) is chosen to match
the input of class_partition_general_necessity, so the existing Marx
machinery applies without modification.

Paper reference: Theorem 7.X (Singular Model Necessity), Axiom Y.

### Non-circularity
- TractableWatanabeOptimalLearning is about LEARNING (prediction quality)
- HasTractableApproxPartitionFunction is about COMPUTATION (evaluating Z)
- The axiom says: if you can learn well, you must be computing Z
- There is no reverse implication assumed or needed -/
axiom watanabe_backward_reduction :
  âˆ€ (sys : ContinuousSystem),
    HasLatentVariables sys â†’
    TractableWatanabeOptimalLearning sys â†’
    HasTractableApproxPartitionFunction sys
