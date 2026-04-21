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

## Information theory (3)

| Axiom                          | Source                         |
|--------------------------------|--------------------------------|
| `data_processing_inequality`   | Cover & Thomas (1991), Thm 2.8.1 |
| `mi_le_conditional_entropy`    | Cover & Thomas (1991)          |
| `subadditivity_entropy`        | Cover & Thomas (1991), Thm 2.6.5 |

## Graph theory (1)

| Axiom                              | Source               |
|------------------------------------|----------------------|
| `separator_existence_from_treewidth` | Diestel (2017), Ch 12 |

## Statistical characterization â€” per-instance (4 axioms)

| Axiom            | Paper theorem | Source                         |
|------------------|---------------|--------------------------------|
| `pkd_theorem`    | 7.4           | Darmois (1935), Koopman (1936) |
| `bvm_theorem`    | 7.6           | van der Vaart (1998)           |
| `watanabe_backward_reduction` | 7.X | Watanabe (2009), Thms 6.7+7.2 |
| `comparative_revision_backward_reduction` | 7.Y | Posterior odds reduction |

## Computational necessity â€” class-level (3 axioms)

| Axiom                                | Paper theorem | Source                  |
|--------------------------------------|---------------|-------------------------|
| `class_partition_exact_necessity`    | 7.8(b)        | Marx (2010, JACM 2013)  |
| `class_partition_approx_necessity`   | 7.8(c)        | Kwisthout et al. (2010) |
| `class_partition_general_necessity`  | 7.8(d)        | Marx (2010) direct      |

Both require `ð“¢.RecursivelyEnumerable` so that the hardness reduction can
enumerate target instances at each graph size.

## Class-level predicates (in SystemClass.lean)

| Predicate                   | Meaning                                        |
|-----------------------------|------------------------------------------------|
| `ContinuousSystemClass`     | `Set ContinuousSystem`                         |
| `.RecursivelyEnumerable`    | opaque â€” the induced graph class is r.e.       |
| `.HasBoundedTreewidth`      | `âˆƒ k, âˆ€ sys âˆˆ ð“¢, tw(G_eff) â‰¤ k` (uniform)    |
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

**Total: 15 axioms, 10 tractability/r.e./opaque predicates, 18 class predicates, 1 proved theorem.**
-/
