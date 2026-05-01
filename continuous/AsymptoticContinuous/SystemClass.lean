/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Necessity.PKD
import AsymptoticContinuous.Necessity.BvM
import AsymptoticContinuous.Necessity.Watanabe
import AsymptoticContinuous.Necessity.ComparativeRevision

/-!
# System Classes — Class-Level Predicates

Defines `ContinuousSystemClass` (a set of `ContinuousSystem` with
potentially different N) and class-level predicates that lift per-instance
conditions to the entire class.

Since each `ContinuousSystem` already bundles `N : ℕ` internally, each
system has its own coordinate count. The per-instance throughput theorem
(Theorem 7.1) is useful as-is. However, the necessity axioms need
class-level statements to avoid vacuity: for a single system with N
coordinates, k = N−1 always satisfies the treewidth bound. A uniform k
across a class with varying N is genuinely non-trivial.

## Predicate structure

- **PKD predicates**: `AllExactSufficiency`, `AllIndependentSupport` →
  (lift) → `AllExponentialFamily`
- **BvM predicates**: `AllFisherPositiveDefinite`, `AllDQM`,
  `AllPriorConsistent` → (lift) → `AllAsymptoticExpFamily`
- **Watanabe predicates**: `AllLatentVariables`,
  `AllTractableWatanabeOptimal` → (lift) → `AllTractableApproxPartition`
- **Comparative revision predicates**: `AllFullyObservedModels`,
  `AllTractableComparativeRevision`, `AllPartitionAnchors` → (lift) →
  `AllTractableApproxPartition`
-/

set_option autoImplicit false

/-! ## Class of continuous systems -/

/-! ## Forward declarations needed by both SystemClass and PartitionFunction -/

-- HasTractablePartitionFunction and HasTractableApproxPartitionFunction
-- are now defined in Agent/Defs.lean to break import cycles with
-- Necessity/Watanabe.lean. They are available here via the transitive
-- import chain: SystemClass → Necessity/PKD → Agent/Defs.

/-- The class of effective CI graphs induced by a system class is recursively
enumerable.

Opaque: formalizing Turing machines is orthogonal.

Marx (2010, JACM 2013, Theorem 1.4) and Kwisthout et al. (2010) require
the graph class to be recursively enumerable so that the counting-reduction
can enumerate target instances at each size. Without this, one could
construct pathological non-r.e. classes that evade the hardness reduction.

IMPLEMENTATION NOTE: Since each `ContinuousSystem` bundles `N : ℕ` and
`G_eff : SimpleGraph (Fin N)`, a class `𝓢 : Set ContinuousSystem` induces
a class of graphs. The r.e. condition says this induced graph class
(varying N) can be effectively enumerated. -/
opaque ContinuousSystemClass.IsRecursivelyEnumerable : Set ContinuousSystem → Prop

/-- A class of continuous inference systems.

Different members `sys ∈ 𝓢` may have different coordinate counts `sys.N`.
This is the analogue of `Set SizedHypergraph` in the discrete fix,
but no wrapper is needed because `ContinuousSystem` already bundles N. -/
abbrev ContinuousSystemClass := Set ContinuousSystem

namespace ContinuousSystemClass

variable (𝓢 : ContinuousSystemClass)

/-! ## Treewidth predicate -/

/-- The class has UNIFORMLY bounded treewidth: there exists a single k
that bounds the treewidth of every member's effective CI graph.

**NON-TRIVIALITY**: For a single system with N coordinates,
k = N−1 always works (trivial). But for a class with arbitrarily
large N values, a uniform k that works for ALL members is a genuine
structural constraint. This is exactly the content of the theoretical
results: tractable inference forces a uniform treewidth ceiling
regardless of system size. -/
def HasBoundedTreewidth : Prop :=
  ∃ k : ℕ, ∀ sys ∈ 𝓢, sys.G_eff.HasTreewidthAtMost k

/-! ## Per-instance predicates lifted to class level -/

/-- Every system in the class admits exact sufficient statistics (PKD input). -/
def AllExactSufficiency : Prop :=
  ∀ sys ∈ 𝓢, HasExactSufficiency sys

/-- Every system in the class has parameter-independent support (PKD input). -/
def AllIndependentSupport : Prop :=
  ∀ sys ∈ 𝓢, HasIndependentSupport sys

/-- Every system in the class belongs to an exponential family (PKD output). -/
def AllExponentialFamily : Prop :=
  ∀ sys ∈ 𝓢, IsExponentialFamily sys

/-- Every system in the class has a tractable partition function. -/
def AllTractablePartition : Prop :=
  ∀ sys ∈ 𝓢, HasTractablePartitionFunction sys

/-- Every system in the class has strictly positive definite Fisher
information at the true parameter (BvM input). -/
def AllFisherPositiveDefinite : Prop :=
  ∀ sys ∈ 𝓢, FisherPositiveDefinite sys

/-- Every system in the class is differentiable in quadratic mean.
DQM is the weakest standard condition for LAN/BvM
(van der Vaart 1998, Theorem 7.2). Accommodates kinks, L1 penalties,
piecewise-smooth likelihoods, ReLU-based models. -/
def AllDQM : Prop :=
  ∀ sys ∈ 𝓢, DifferentiableInQuadraticMean sys

/-- Every system in the class has a consistent prior (positive near true
parameter) (BvM input). -/
def AllPriorConsistent : Prop :=
  ∀ sys ∈ 𝓢, PriorConsistent sys

/-- Every system in the class is an asymptotic exponential family (BvM output). -/
def AllAsymptoticExpFamily : Prop :=
  ∀ sys ∈ 𝓢, IsAsymptoticExpFamily sys

/-- Every system in the class has a tractable approximate partition function. -/
def AllTractableApproxPartition : Prop :=
  ∀ sys ∈ 𝓢, HasTractableApproxPartitionFunction sys

/-- The class is recursively enumerable (delegates to the opaque). -/
def RecursivelyEnumerable : Prop :=
  ContinuousSystemClass.IsRecursivelyEnumerable 𝓢

/-! ## Derived predicates -/

/-- PKD lifts to the class level: if every system has exact sufficiency
and parameter-independent support, then every system is in an exponential
family. -/
theorem allExactSufficiency_implies_allExpFamily
    (h_suff : 𝓢.AllExactSufficiency)
    (h_supp : 𝓢.AllIndependentSupport) : 𝓢.AllExponentialFamily :=
  fun sys hs => pkd_theorem sys (h_suff sys hs) (h_supp sys hs)

/-- BvM lifts to the class level (via DQM).
If every system has positive-definite Fisher information, is DQM, and
has a consistent prior, then every system is an asymptotic exponential
family. -/
theorem allBvMConditions_implies_allAsymptoticExpFamily
    (h_fisher : 𝓢.AllFisherPositiveDefinite)
    (h_dqm : 𝓢.AllDQM)
    (h_prior : 𝓢.AllPriorConsistent) : 𝓢.AllAsymptoticExpFamily :=
  fun sys hs => bvm_theorem sys (h_fisher sys hs) (h_dqm sys hs) (h_prior sys hs)

/-! ## Singular-model predicates -/

/-- Every system in the class has latent variables (Watanabe input). -/
def AllLatentVariables : Prop :=
  ∀ sys ∈ 𝓢, HasLatentVariables sys

/-- Every system in the class admits a polynomial-time learner achieving
the Watanabe-optimal generalization rate (Watanabe input). -/
def AllTractableWatanabeOptimal : Prop :=
  ∀ sys ∈ 𝓢, TractableWatanabeOptimalLearning sys

/-- Watanabe lifts to the class level: if every system has latents and
admits tractable optimal learning, then every system has a tractable
approximate partition function.

This is the singular-model analog of allBvMConditions_implies_allAsymptoticExpFamily.
Where BvM connects regularity to exp-family structure, Watanabe connects
learning success to partition function tractability. Both arrive at the
same downstream type consumed by the Marx/Kwisthout necessity axiom. -/
theorem allWatanabe_implies_allTractableApproxPartition
    (h_lat : 𝓢.AllLatentVariables)
    (h_opt : 𝓢.AllTractableWatanabeOptimal) : 𝓢.AllTractableApproxPartition :=
  fun sys hs => watanabe_backward_reduction sys (h_lat sys hs) (h_opt sys hs)

/-! ## Fully observed comparative-revision predicates -/

/-- Every system in the class is fully observed (comparative route input). -/
def AllFullyObservedModels : Prop :=
  ∀ sys ∈ 𝓢, IsFullyObservedModel sys

/-- Every system in the class admits tractable comparative Bayesian revision
over hypotheses (comparative route input). -/
def AllTractableComparativeRevision : Prop :=
  ∀ sys ∈ 𝓢, TractableComparativeBayesRevision sys

/-- Every system in the class has a tractable/known partition anchor
(comparative route input). -/
def AllPartitionAnchors : Prop :=
  ∀ sys ∈ 𝓢, HasPartitionAnchor sys

/-- Comparative revision lifts to the class level: if every fully observed
system admits tractable comparative Bayesian revision and has an anchor,
then every system in the class has a tractable approximate partition function.

This covers fully observed singular models with parametric uncertainty
without using latent variables or Watanabe optimality. -/
theorem allComparativeRevision_implies_allTractableApproxPartition
    (h_obs : 𝓢.AllFullyObservedModels)
    (h_cmp : 𝓢.AllTractableComparativeRevision)
    (h_anchor : 𝓢.AllPartitionAnchors) : 𝓢.AllTractableApproxPartition :=
  fun sys hs =>
    comparative_revision_backward_reduction sys (h_obs sys hs) (h_cmp sys hs) (h_anchor sys hs)

end ContinuousSystemClass
