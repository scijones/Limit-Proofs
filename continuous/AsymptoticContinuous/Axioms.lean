/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.InformationTheory.Axioms
import AsymptoticContinuous.Agent.Throughput
import AsymptoticContinuous.Necessity.PartitionFunction

/-!
# Axiom Inventory

Importing `AsymptoticContinuous.Axioms` gives access to all axioms,
definitions, the proved throughput bound, and the class-level predicates
(via re-export of `SystemClass`).

## Complexity hypotheses (2)

| Axiom             | Source                          |
|-------------------|---------------------------------|
| `FPT_ne_SharpW1`  | Flum & Grohe (2006)             |
| `ETH`             | Impagliazzo & Paturi (2001)     |

## Information theory (2 load-bearing + 3 witness-only)

| Axiom                          | Source                         |
|--------------------------------|--------------------------------|
| `IsMarkovChain` (predicate)    | interface token (global Markov property) |
| `data_processing_inequality`   | Polyanskiy & Wu (2024), Ch. 3 — valid for continuous RVs |
| `witnessRV` (sanity only)      | any probability space has a RV |
| `isMarkovChain_self_right` (sanity only) | X—Y—Y is always Markov |
| `cmi_cond_self` (sanity only)  | I(X;Y|Y) = 0                   |

DELETED (false for differential entropy, sound only in a discrete
model): `mi_le_conditional_entropy`, `subadditivity_entropy`.  The
rate constraint is now stated in capacity (MI) form directly in
`ContinuousSystem.rate_bound`, so the remaining information-theoretic
trust base is valid for genuinely continuous random variables.

## Graph theory (1)

| Axiom                              | Source               |
|------------------------------------|----------------------|
| `separator_existence_from_treewidth` | Diestel (2017), Ch 12 |

## Statistical characterization — per-instance (4 axioms)

| Axiom            | Paper theorem | Source                         |
|------------------|---------------|--------------------------------|
| `pkd_theorem`    | 7.4           | Darmois (1935), Koopman (1936) |
| `bvm_theorem`    | 7.6           | van der Vaart (1998)           |
| `watanabe_backward_reduction` | 7.X | Watanabe (2009), Thms 6.7+7.2 |
| `comparative_revision_backward_reduction` | 7.Y | Posterior odds reduction |

## Computational necessity — class-level (3 axioms)

| Axiom                                | Paper theorem | Source                  |
|--------------------------------------|---------------|-------------------------|
| `class_partition_exact_necessity`    | 7.8(b)        | Marx (2010, JACM 2013)  |
| `class_partition_approx_necessity`   | 7.8(c)        | Kwisthout et al. (2010) |
| `class_partition_general_necessity`  | 7.8(d)        | Marx (2010) direct      |

Both require `𝓢.RecursivelyEnumerable` so that the hardness reduction can
enumerate target instances at each graph size.

DELETED (vacuous — ∃ k is satisfiable with k = N−1 via the one-bag
decomposition, proved constructively in `Tests/Sanity.lean`):
`partition_exact_necessity_instance`, `partition_approx_necessity_instance`,
and the per-instance corollaries `main_exact_instance`,
`main_approx_instance` that consumed them.

## Class-level predicates (in SystemClass.lean)

| Predicate                   | Meaning                                        |
|-----------------------------|------------------------------------------------|
| `ContinuousSystemClass`     | `Set ContinuousSystem`                         |
| `.RecursivelyEnumerable`    | opaque — the induced graph class is r.e.       |
| `.HasBoundedTreewidth`      | `∃ k, ∀ sys ∈ 𝓢, tw(G_eff) ≤ k` (uniform)    |
| `.AllExactSufficiency`      | all members have exact sufficiency              |
| `.AllIndependentSupport`    | all members have parameter-independent support  |
| `.AllExponentialFamily`     | all members are exponential families            |
| `.AllTractablePartition`    | all members have tractable partition fn          |
| `.AllFisherPositiveDefinite`| all members have pos-def Fisher info            |
| `.AllDQM`                   | all members are DQM                             |
| `.AllPriorConsistent`       | all members have consistent prior               |
| `.AllAsymptoticExpFamily`   | all members are asymptotic exp families          |
| `.AllTractableApproxPartition` | all members have tractable approx partition  |
| `.AllLatentVariables`       | all members have latent variables                |
| `.AllTractableWatanabeOptimal` | all members admit poly-time optimal learning  |
| `.AllFullyObservedModels`   | all members are fully observed                   |
| `.AllTractableComparativeRevision` | all members admit tractable comparative revision |
| `.AllPartitionAnchors`      | all members have a tractable anchor              |

## Proved results (re-exported)

| Theorem                    | Paper theorem | Module              |
|----------------------------|---------------|---------------------|
| `throughput_rate_bound`    | 7.1           | Agent.Throughput    |
| `trivial_graph_tw0`        | non-vacuity   | Tests.Sanity        |
| `continuousSystem_nonempty`| non-vacuity   | Tests.Sanity        |
| `throughput_rate_bound_nonvacuous` | non-vacuity | Tests.Sanity  |
-/
