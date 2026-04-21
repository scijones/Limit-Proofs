/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Defs

/-!
# Comparative Bayesian Revision â€” Fully Observed Singular Bridge

For singular models with no latent variables, likelihood-ratio methods can
cancel the partition function, so the Watanabe latent-variable route does
not apply. This module targets a stronger capability: tractable comparative
Bayesian belief revision.

For a fully observed graphical model,

    p(x | w) = exp(S_w(x) - A(w))

where S_w(x) is the clique score and A(w) = log Z(w) is the log-partition.
For two hypotheses w and w0,

    log p(x|w) / p(x|w0)
      = (S_w(x) - S_w0(x)) - (A(w) - A(w0)).

Bayesian posterior odds update satisfies the same identity:

    log Ï€(w|x) / Ï€(w0|x) - log Ï€(w) / Ï€(w0)
      = log p(x|w) / p(x|w0).

Therefore, an oracle that tractably computes posterior log-odds updates for
arbitrary hypothesis pairs also tractably computes free-energy differences
A(w) - A(w0). Given one anchor w0 with known A(w0), this recovers A(w), hence
Z(w), in polynomial time.

This is a black-box reduction: the partition function is recovered directly
from the oracle's observable output (posterior odds updates), rather than
from a white-box analysis of the oracle's internals.

## Scope

This route covers fully-observed singular models with parametric uncertainty.
It does NOT require latent variables or Watanabe-optimal asymptotics.
Instead it requires:

- exact or approximate Bayesian comparative revision over arbitrary
  hypothesis pairs, in polynomial time
- one anchor parameter with known/tractable partition value

What remains outside scope: non-Bayesian or weakly Bayesian systems â€”
heuristic learners, discriminative predictors, local gradient methods
without posterior-odds semantics.
-/

set_option autoImplicit false

/-- The system is fully observed: there are no hidden variables h to
sum out in the likelihood. Concretely,

  p(x | w) = (1 / Z(w)) âˆ_C Ïˆ_C(x_C; w).

This is the residual case not covered by the latent-variable Watanabe route.
Likelihood ratios can cancel Z(w), so one needs a different bridge to recover
partition-function hardness. -/
opaque IsFullyObservedModel (sys : ContinuousSystem) : Prop

/-- There exists a polynomial-time procedure that performs comparative
Bayesian belief revision over hypotheses: for arbitrary relevant parameter
pairs w, w0 and observations x, it computes posterior log-odds updates

  log Ï€(w | x) / Ï€(w0 | x) - log Ï€(w) / Ï€(w0)

to the accuracy needed by the downstream approximate-partition predicate.

The key point is that this is stronger than "good prediction" or even
"low regret": it exposes the Bayesian revision quantity whose algebraic form
contains the free-energy difference A(w) - A(w0). -/
opaque TractableComparativeBayesRevision (sys : ContinuousSystem) : Prop

/-- The system's model family contains a reference parameter w0 whose
log-partition A(w0) is known or tractable.

This anchor turns tractable free-energy differences A(w) - A(w0) into
tractable absolute log-partition values A(w). In many natural families,
w0 corresponds to zero interactions / independent coordinates, where Z is
explicitly computable. -/
opaque HasPartitionAnchor (sys : ContinuousSystem) : Prop

/-- **Comparative-revision backward reduction (v5).**

If a fully observed system admits tractable comparative Bayesian revision and
has one tractable anchor partition value, then the system has a tractable
approximate partition function.

Argument:
1. For fully observed models,
     log p(x|w) / p(x|w0)
       = (S_w(x) - S_w0(x)) - (A(w) - A(w0)).
2. Bayesian posterior odds update equals the same likelihood-ratio term.
3. Therefore the oracle's output reveals A(w) - A(w0).
4. The anchor gives A(w0), hence A(w) itself.
5. Therefore Z(w) is tractable.

This is a genuine black-box reduction covering fully observed singular
models with purely parametric uncertainty, provided their belief revision
is Bayesian enough to expose posterior-odds updates. -/
axiom comparative_revision_backward_reduction :
  âˆ€ (sys : ContinuousSystem),
    IsFullyObservedModel sys â†’
    TractableComparativeBayesRevision sys â†’
    HasPartitionAnchor sys â†’
    HasTractableApproxPartitionFunction sys