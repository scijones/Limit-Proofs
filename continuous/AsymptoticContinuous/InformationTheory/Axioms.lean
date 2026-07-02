/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.InformationTheory.Defs

/-!
# Information-Theoretic Axioms

The data processing inequality, plus a minimal witness interface used
only by the non-vacuity guards in `Tests/Sanity.lean`.

## Soundness for continuous variables

Every axiom below is true for arbitrary (continuous or discrete) random
variables on a common probability space, with `I(·;·|·)` read as
conditional mutual information (Polyanskiy & Wu 2024, Ch. 3):

* `data_processing_inequality`: conditional MI DPI holds in full
  generality (no discreteness needed).
* `isMarkovChain_self_right`: X — Y — Y is always a Markov chain
  (Y ⊥ X | Y trivially).
* `cmi_cond_self`: I(X ; Y | Y) = 0 (given Y, Y is deterministic).

Deliberately ABSENT: any axiom of the form I(X;Y|Z) ≤ H(Y|Z).  That
inequality is true for discrete Shannon entropy but FALSE for
differential entropy (I ≥ 0 always, h can be negative), so admitting
it would make the trust base sound only in a discrete model —
contradicting the continuous scope of this development.  The
per-coordinate rate constraint is instead stated directly in
capacity (mutual-information) form in `ContinuousSystem.rate_bound`.
-/

set_option autoImplicit false

/-- `IsMarkovChain X Y Z W`: the chain X — Y — Z holds conditionally
on W, i.e. Z ⊥ X | (Y, W) almost surely.  Uninterpreted interface
token: the measure-theoretic content (conditional independence up to
null sets) lives in the intended model, not in Lean.  Consumed by
`data_processing_inequality`; produced by `ContinuousSystem.graph_structured`
(the global Markov property of the effective graph) and, for witnesses,
by `isMarkovChain_self_right`. -/
axiom IsMarkovChain (X Y Z W : RandomVariable) : Prop

axiom data_processing_inequality :
  ∀ (X Y Z W : RandomVariable),
    IsMarkovChain X Y Z W →
    I(X ; Z | W) ≤ I(X ; Y | W)

/-! ## Witness interface (used only by `Tests/Sanity.lean`)

Three textbook-true facts that make `ContinuousSystem` constructible,
so the class-level theorems are demonstrably non-vacuous.  None is
used by any load-bearing proof. -/

/-- Some random variable exists (any probability space has one). -/
axiom witnessRV : RandomVariable

/-- X — Y — Y is always a Markov chain: Y ⊥ X | (Y, W) trivially. -/
axiom isMarkovChain_self_right :
  ∀ (X Y W : RandomVariable), IsMarkovChain X Y Y W

/-- I(X ; Y | Y) = 0: conditioned on Y, Y carries no information. -/
axiom cmi_cond_self :
  ∀ (X Y : RandomVariable), I(X ; Y | Y) = 0
