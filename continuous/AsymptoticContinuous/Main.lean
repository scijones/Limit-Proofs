/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Axioms

/-!
# Main Results (Asymptotic Version)

Four class-level corollaries, each concluding that a recursively enumerable
class of continuous inference systems satisfying appropriate hypotheses has
uniformly bounded treewidth and throughput ≤ (k+1)·R_max.

- **`class_main_exact`** (Corollary 7.9(a)): PKD route — exact sufficiency +
  independent support + tractable partition function.
- **`class_main_approx`** (Corollary 7.9(b)): BvM route — Fisher pos-def +
  DQM + consistent prior + tractable approximate partition function.
- **`class_main_singular`** (Corollary 7.9(c)): Watanabe route — latent
  variables + tractable Watanabe-optimal learning.
- **`class_main_comparative`** (Corollary 7.9(d)): Comparative revision
  route — fully observed + tractable comparative revision + anchor.

Each proof follows the same structure:
1. Per-instance statistical theorem lifts to the class level
2. Class-level necessity (Marx/Kwisthout) gives uniform treewidth bound
3. Per-instance throughput bound applies to each member using that k
-/

set_option autoImplicit false

/-! ## Class-level corollaries (the non-trivial versions) -/

/-- **Corollary 7.9(a), class version: Full exact-inference pipeline.**

Given:
1. The FPT ≠ #W[1] conjecture
2. A recursively enumerable class of systems where every member has:
   - exact sufficiency (PKD input)
   - parameter-independent support (PKD input)
3. Each system in the class has a tractable partition function

Conclude: there exists a uniform k such that for every system in the class,
tw(G_eff) ≤ k and I(t) ≤ (k+1)·R_max.

The r.e. hypothesis is required by Marx (2010, JACM 2013) so that the
counting reduction can enumerate target instances at each graph size.
It excludes only pathological non-constructive classes. -/
theorem class_main_exact (h_conj : FPT_ne_SharpW1)
    (𝓢 : ContinuousSystemClass)
    (h_re : 𝓢.RecursivelyEnumerable)
    (h_exact : 𝓢.AllExactSufficiency)
    (h_supp : 𝓢.AllIndependentSupport)
    (h_tract : 𝓢.AllTractablePartition) :
    ∃ k : ℕ, ∀ sys ∈ 𝓢,
      sys.G_eff.HasTreewidthAtMost k ∧
      sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  -- Step 1: PKD lifts to the class level (requires IndependentSupport)
  have h_exp : 𝓢.AllExponentialFamily :=
    𝓢.allExactSufficiency_implies_allExpFamily h_exact h_supp
  -- Step 2: Class-level necessity gives uniform treewidth bound
  obtain ⟨k, hk⟩ := class_partition_exact_necessity h_conj 𝓢 h_re h_exp h_tract
  -- Step 3: Per-instance throughput bound for each member
  exact ⟨k, fun sys hs => ⟨hk sys hs, throughput_rate_bound sys k (hk sys hs)⟩⟩

/-- **Corollary 7.9(b), class version: Full approximate-inference pipeline.**

Given:
1. The Exponential Time Hypothesis
2. A recursively enumerable class of systems where every member has:
   - strictly positive-definite Fisher information
   - differentiability in quadratic mean (DQM)
   - prior positive near the true parameter
3. Each system in the class has a tractable approximate partition function

Conclude: there exists a uniform k such that for every system in the class,
tw(G_eff) ≤ k and I(t) ≤ (k+1)·R_max.

DQM (van der Vaart 1998, Theorems 7.2 + 10.1) accommodates non-smooth
models (LASSO, ReLU, piecewise-linear) while retaining full rigor. -/
theorem class_main_approx (h_eth : ETH)
    (𝓢 : ContinuousSystemClass)
    (h_re : 𝓢.RecursivelyEnumerable)
    (h_fisher : 𝓢.AllFisherPositiveDefinite)
    (h_dqm : 𝓢.AllDQM)
    (h_prior : 𝓢.AllPriorConsistent)
    (h_tract : 𝓢.AllTractableApproxPartition) :
    ∃ k : ℕ, ∀ sys ∈ 𝓢,
      sys.G_eff.HasTreewidthAtMost k ∧
      sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  -- Step 1: BvM lifts to the class level (via DQM)
  have h_exp : 𝓢.AllAsymptoticExpFamily :=
    𝓢.allBvMConditions_implies_allAsymptoticExpFamily h_fisher h_dqm h_prior
  -- Step 2: Class-level necessity gives uniform treewidth bound
  obtain ⟨k, hk⟩ := class_partition_approx_necessity h_eth 𝓢 h_re h_exp h_tract
  -- Step 3: Per-instance throughput bound for each member
  exact ⟨k, fun sys hs => ⟨hk sys hs, throughput_rate_bound sys k (hk sys hs)⟩⟩

/-! ## Class-level corollary: singular models -/

/-- **Corollary 7.9(c), class version: Full singular-model pipeline.**

Given:
1. The Exponential Time Hypothesis
2. A recursively enumerable class of systems where every member:
   - has latent variables (marginalization requires Z)
   - admits a poly-time learner achieving Watanabe-optimal generalization

Conclude: there exists a uniform k such that for every system in the class,
tw(G_eff) ≤ k and I(t) ≤ (k+1)·R_max.

This parallels class_main_approx but drops all regularity hypotheses:
- No FisherPositiveDefinite (singular Fisher is the whole point)
- No DifferentiableInQuadraticMean (non-smooth models are fine)
- No PriorConsistent (prior enters via Watanabe's theory, not BvM)
- No AllAsymptoticExpFamily (singular models are not exp families)

In exchange, two hypotheses are required:
- AllLatentVariables: marginalization over h forces Z(w) evaluation
- AllTractableWatanabeOptimal: poly-time learning achieves optimal rate

The proof has three steps:
1. Watanabe backward reduction: learning success + latents → tractable Z
2. General necessity (Marx): tractable Z across class → bounded tw
3. Throughput (proved): bounded tw → I(t) ≤ (k+1)R_max

Non-circularity: TractableWatanabeOptimalLearning (prediction quality)
is a genuinely different predicate from HasTractableApproxPartitionFunction
(Z computation). The axiom connects them without assuming a reverse
implication.

Scope: this does not cover fully-observed singular models without latent
variables. For such models, MCMC can use likelihood ratios that cancel
Z(w), so tractable learning does not imply tractable Z. The AllLatentVariables
hypothesis is genuinely load-bearing. -/
theorem class_main_singular (h_eth : ETH)
    (𝓢 : ContinuousSystemClass)
    (h_re : 𝓢.RecursivelyEnumerable)
    (h_lat : 𝓢.AllLatentVariables)
    (h_opt : 𝓢.AllTractableWatanabeOptimal) :
    ∃ k : ℕ, ∀ sys ∈ 𝓢,
      sys.G_eff.HasTreewidthAtMost k ∧
      sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  -- Step 1: Watanabe backward reduction: success + latents → tractable Z
  have h_tract : 𝓢.AllTractableApproxPartition :=
    𝓢.allWatanabe_implies_allTractableApproxPartition h_lat h_opt
  -- Step 2: General necessity (Marx): tractable Z across class → bounded tw
  obtain ⟨k, hk⟩ := class_partition_general_necessity h_eth 𝓢 h_re h_tract
  -- Step 3: Per-instance throughput bound for each member (already proved)
  exact ⟨k, fun sys hs => ⟨hk sys hs, throughput_rate_bound sys k (hk sys hs)⟩⟩

/-! ## Class-level corollary: fully observed comparative revision -/

/-- **Corollary 7.9(d), class version: Fully observed comparative-revision
pipeline.**

Given:
1. The Exponential Time Hypothesis
2. A recursively enumerable class of systems where every member:
   - is fully observed (no latent variables)
   - admits tractable comparative Bayesian revision over hypotheses
   - has one tractable anchor partition value

Conclude: there exists a uniform k such that for every system in the class,
tw(G_eff) ≤ k and I(t) ≤ (k+1)·R_max.

This covers fully-observed singular models with parametric uncertainty.
The reduction is black-box, via posterior log-odds updates, and does not
require latent variables or Watanabe-optimal asymptotics.

What remains outside scope: non-Bayesian or weakly Bayesian systems that do
not expose tractable comparative revision over hypotheses. -/
theorem class_main_comparative (h_eth : ETH)
    (𝓢 : ContinuousSystemClass)
    (h_re : 𝓢.RecursivelyEnumerable)
    (h_obs : 𝓢.AllFullyObservedModels)
    (h_cmp : 𝓢.AllTractableComparativeRevision)
    (h_anchor : 𝓢.AllPartitionAnchors) :
    ∃ k : ℕ, ∀ sys ∈ 𝓢,
      sys.G_eff.HasTreewidthAtMost k ∧
      sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  -- Step 1: Comparative revision + anchor → tractable Z
  have h_tract : 𝓢.AllTractableApproxPartition :=
    𝓢.allComparativeRevision_implies_allTractableApproxPartition h_obs h_cmp h_anchor
  -- Step 2: General necessity (Marx): tractable Z across class → bounded tw
  obtain ⟨k, hk⟩ := class_partition_general_necessity h_eth 𝓢 h_re h_tract
  -- Step 3: Per-instance throughput bound for each member
  exact ⟨k, fun sys hs => ⟨hk sys hs, throughput_rate_bound sys k (hk sys hs)⟩⟩

/-! ## Per-instance corollaries (trivially follow from class-level) -/

/-- Per-instance Corollary 7.9(a). Uses the per-instance necessity axiom
directly, bypassing the class-level version (and its r.e. requirement).
Requires `HasIndependentSupport`.
This conclusion is vacuously satisfiable with k = N−1. -/
theorem main_exact_instance (h_conj : FPT_ne_SharpW1)
    (sys : ContinuousSystem) (h_exact : HasExactSufficiency sys)
    (h_supp : HasIndependentSupport sys)
    (h_tract : HasTractablePartitionFunction sys) :
    ∃ k : ℕ, sys.G_eff.HasTreewidthAtMost k ∧
      sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  obtain ⟨k, hk⟩ := partition_exact_necessity_instance h_conj sys
    (pkd_theorem sys h_exact h_supp) h_tract
  exact ⟨k, hk, throughput_rate_bound sys k hk⟩

/-- Per-instance Corollary 7.9(b). Same caveat as above.
Uses decomposed non-degeneracy conditions: `FisherPositiveDefinite`,
`DifferentiableInQuadraticMean`, `PriorConsistent`. -/
theorem main_approx_instance (h_eth : ETH)
    (sys : ContinuousSystem)
    (h_fisher : FisherPositiveDefinite sys)
    (h_dqm : DifferentiableInQuadraticMean sys)
    (h_prior : PriorConsistent sys)
    (h_tract : HasTractableApproxPartitionFunction sys) :
    ∃ k : ℕ, sys.G_eff.HasTreewidthAtMost k ∧
      sys.throughput ≤ (↑(k + 1) : ℝ) * sys.R_max := by
  obtain ⟨k, hk⟩ := partition_approx_necessity_instance h_eth sys
    (bvm_theorem sys h_fisher h_dqm h_prior) h_tract
  exact ⟨k, hk, throughput_rate_bound sys k hk⟩
