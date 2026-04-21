/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.SystemClass

/-!
# Partition Function Hardness

Class-level necessity axioms connecting partition-function tractability
to bounded treewidth. Each axiom says: under a complexity-theoretic
assumption (FPT â‰  #W[1] or ETH), if a recursively enumerable class of
systems has tractable partition functions, then the class has uniformly
bounded treewidth.

The class-level statement is non-trivial because different systems have
different N, so the trivial bound Nâˆ’1 is not uniform.

Three variants:
- **Exact** (Theorem 7.8(b)): requires exponential family + tractable Z,
  under FPT â‰  #W[1]. Source: Marx (2010, JACM 2013, Theorem 1.4).
- **Approximate** (Theorem 7.8(c)): requires asymptotic exp family +
  tractable approximate Z, under ETH. Source: Kwisthout et al. (2010).
- **General** (Theorem 7.8(d)): requires only tractable approximate Z,
  under ETH. The exponential-family hypothesis is upstream bookkeeping
  (connecting inference to Z), not something Marx's theorem requires.

## Complexity hypotheses
-/

set_option autoImplicit false

/-- FPT â‰  #W[1]. -/
axiom FPT_ne_SharpW1 : Prop

/-- ETH. -/
axiom ETH : Prop

-- HasTractablePartitionFunction and HasTractableApproxPartitionFunction
-- are declared in SystemClass.lean (imported above) to break the import cycle.

/-! ## CLASS-LEVEL NECESSITY AXIOMS -/

/-- **Theorem 7.8(b), class version: Exact partition-function necessity.**

Under FPT â‰  #W[1], if a recursively enumerable class of systems consists
entirely of exponential families with tractable partition functions, then
the class has uniformly bounded treewidth.

Mathematical content: Marx (2010, JACM 2013, Theorem 1.4). The counting
reduction produces hard instances at every graph size, so tractability
across all sizes forces a uniform treewidth bound. The r.e. hypothesis
is needed so the reduction can enumerate target instances. -/
axiom class_partition_exact_necessity :
  FPT_ne_SharpW1 â†’
  âˆ€ (ð“¢ : ContinuousSystemClass),
    ð“¢.RecursivelyEnumerable â†’
    ð“¢.AllExponentialFamily â†’
    ð“¢.AllTractablePartition â†’
    ð“¢.HasBoundedTreewidth

/-- **Theorem 7.8(c), class version: Approximate partition-function necessity.**

Under ETH, if a recursively enumerable class of systems consists entirely
of asymptotic exponential families with tractable approximate partition
functions, then the class has uniformly bounded treewidth.

Mathematical content: Kwisthout, Bodlaender, and van der Gaag (2010).
The r.e. hypothesis is needed so that the hardness reduction can
enumerate target instances at each size. -/
axiom class_partition_approx_necessity :
  ETH â†’
  âˆ€ (ð“¢ : ContinuousSystemClass),
    ð“¢.RecursivelyEnumerable â†’
    ð“¢.AllAsymptoticExpFamily â†’
    ð“¢.AllTractableApproxPartition â†’
    ð“¢.HasBoundedTreewidth

/-- **Theorem 7.8(d), class version: General partition-function necessity.**

Under ETH, if a recursively enumerable class of systems has tractable
approximate partition functions, then the class has uniformly bounded
treewidth.

This drops the AllAsymptoticExpFamily hypothesis from
class_partition_approx_necessity. Marx (2010, Theorem 1.4) proves hardness
for computing the partition function Z = Î£_x âˆ_C Ïˆ_C(x_C) on a graph â€” a
sum-product over graph cliques. This structure comes from the graph
factorization of the model, not from exponential family parameterization.
Any graphical model has factors Ïˆ_C over its cliques, and the normalizing
sum Î£ âˆ Ïˆ_C has the same algebraic structure regardless of whether the
model is an exponential family.

class_partition_approx_necessity is a special case of this axiom
(it has a strictly stronger hypothesis). -/
axiom class_partition_general_necessity :
  ETH â†’
  âˆ€ (ð“¢ : ContinuousSystemClass),
    ð“¢.RecursivelyEnumerable â†’
    ð“¢.AllTractableApproxPartition â†’
    ð“¢.HasBoundedTreewidth

/-! ## PER-INSTANCE VERSIONS (retained for composition, known to be vacuous) -/

/-- Per-instance exact necessity. VACUOUS: âˆƒ k is always satisfiable with k = Nâˆ’1.
Retained for documentation only. The per-instance conclusion is trivially
satisfiable and does not require the r.e. hypothesis that the class-level
version needs. -/
axiom partition_exact_necessity_instance (h : FPT_ne_SharpW1)
    (sys : ContinuousSystem) (hexp : IsExponentialFamily sys)
    (htract : HasTractablePartitionFunction sys) :
    âˆƒ k : â„•, sys.G_eff.HasTreewidthAtMost k

/-- Per-instance approximate necessity. VACUOUS for the same reason. -/
axiom partition_approx_necessity_instance (h : ETH)
    (sys : ContinuousSystem) (hexp : IsAsymptoticExpFamily sys)
    (htract : HasTractableApproxPartitionFunction sys) :
    âˆƒ k : â„•, sys.G_eff.HasTreewidthAtMost k
