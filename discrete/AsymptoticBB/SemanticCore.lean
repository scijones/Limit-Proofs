/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Grammars.MCFG

/-!
# The non-computational semantic-core bridge

This file isolates the semantic step needed to transfer a language bound from a
composition of cores back to the original CSP structure.  No algorithm for
finding a core, no reduction, and no complexity bound for core computation is
used.

The only ingredients are:

* CSP truth is represented by existence of a homomorphism from the instance
  structure to a target structure;
* an original structure and its core have homomorphisms in both directions;
* the chosen structural composition respects that equivalence; and
* the decision language of the composed cores has the stated MCFG bound.

The last item may itself be obtained by a tier-preserving language-composition
construction.  That closure property is made an explicit hypothesis below: it
is not conflated with semantic core equivalence.
-/

set_option autoImplicit false

universe u_obj u_sym

/-- An abstract category of CSP templates/structures, retaining exactly the
identity and composition laws needed for homomorphism-existence semantics. -/
structure HomSystem (Obj : Type u_obj) where
  Hom : Obj → Obj → Prop
  refl : ∀ A, Hom A A
  trans : ∀ {A B C}, Hom A B → Hom B C → Hom A C

namespace HomSystem

variable {Obj : Type u_obj} (S : HomSystem Obj)

/-- Homomorphic equivalence: homomorphisms exist in both directions. -/
def Equivalent (A K : Obj) : Prop :=
  S.Hom A K ∧ S.Hom K A

@[refl] theorem equivalent_refl (A : Obj) : S.Equivalent A A :=
  ⟨S.refl A, S.refl A⟩

@[symm] theorem equivalent_symm {A K : Obj} :
    S.Equivalent A K → S.Equivalent K A := by
  rintro ⟨hAK, hKA⟩
  exact ⟨hKA, hAK⟩

@[trans] theorem equivalent_trans {A B C : Obj} :
    S.Equivalent A B → S.Equivalent B C → S.Equivalent A C := by
  rintro ⟨hAB, hBA⟩ ⟨hBC, hCB⟩
  exact ⟨S.trans hAB hBC, S.trans hCB hBA⟩

/-- The Boolean-free decision proposition for the structural CSP `(A,B)`:
there is a homomorphism from the instance structure `A` to the target `B`. -/
def CSPDecision (A B : Obj) : Prop :=
  S.Hom A B

/-- The central semantic invariant.  Homomorphically equivalent left-hand
structures give exactly the same answer against every target structure. -/
theorem cspDecision_iff_of_equivalent {A K : Obj}
    (hAK : S.Equivalent A K) (B : Obj) :
    S.CSPDecision A B ↔ S.CSPDecision K B := by
  constructor
  · intro hAB
    exact S.trans hAK.2 hAB
  · intro hKB
    exact S.trans hAK.1 hKB

/-- A core witness is purely extensional data: a core predicate together with
homomorphic equivalence.  It deliberately contains no procedure for computing
or selecting `K` from `A`. -/
structure CoreWitness (IsCore : Obj → Prop) (A K : Obj) : Prop where
  equivalent : S.Equivalent A K
  isCore : IsCore K

/-- Forgetting core minimality from a list of static core witnesses leaves
exactly the componentwise homomorphic equivalences needed semantically. -/
theorem equivalents_of_coreWitnesses (IsCore : Obj → Prop)
    {originals cores : List Obj}
    (hcores : List.Forall₂ (S.CoreWitness IsCore) originals cores) :
    List.Forall₂ S.Equivalent originals cores := by
  induction hcores with
  | nil => exact .nil
  | cons hcore _ ih => exact .cons hcore.equivalent ih

/-- A composition operation on structures that is invariant under replacing
components by homomorphically equivalent representatives. -/
structure HomComposition where
  compose : List Obj → Obj
  respects_equivalence : ∀ {As Ks : List Obj},
    List.Forall₂ S.Equivalent As Ks →
      S.Equivalent (compose As) (compose Ks)

/-- Per-component core equivalence lifts to equivalence of the composed
original structure and the composed core structure. -/
theorem composed_equivalent (C : S.HomComposition)
    {originals cores : List Obj}
    (hcores : List.Forall₂ S.Equivalent originals cores) :
    S.Equivalent (C.compose originals) (C.compose cores) :=
  C.respects_equivalence hcores

/-- The decision language of a structure under an arbitrary encoding of input
words as target structures. -/
def DecisionLanguage {Sym : Type u_sym} (A : Obj)
    (target : List Sym → Obj) : Set (List Sym) :=
  {w | S.CSPDecision A (target w)}

/-- Homomorphic equivalence gives literal equality of the extensional decision
languages. -/
theorem decisionLanguage_eq_of_equivalent {Sym : Type u_sym} {A K : Obj}
    (hAK : S.Equivalent A K) (target : List Sym → Obj) :
    S.DecisionLanguage A target = S.DecisionLanguage K target := by
  ext w
  exact S.cspDecision_iff_of_equivalent hAK (target w)

/-- The non-computational bridge for a composition of cores.  If the composed
core decision language lies in dimension `d`, then the original composed CSP
language lies in the same dimension, solely because the two languages are
equal. -/
theorem complexity_correspondence_via_core_composition
    {Sym : Type u_sym}
    (C : S.HomComposition)
    (originals cores : List Obj)
    (hcores : List.Forall₂ S.Equivalent originals cores)
    (target : List Sym → Obj) (d : ℕ)
    (hcoreMCFL : IsMCFL.{u_sym, 0} (S.DecisionLanguage (C.compose cores) target) d) :
    S.DecisionLanguage (C.compose originals) target =
        S.DecisionLanguage (C.compose cores) target ∧
      IsMCFL.{u_sym, 0} (S.DecisionLanguage (C.compose originals) target) d := by
  have hEq : S.DecisionLanguage (C.compose originals) target =
      S.DecisionLanguage (C.compose cores) target :=
    S.decisionLanguage_eq_of_equivalent (C.respects_equivalence hcores) target
  exact ⟨hEq, hEq ▸ hcoreMCFL⟩

end HomSystem

/-- A language-composition operation preserves MCFG tier `d` when composing
any finite list of `d`-MCFLs again produces a `d`-MCFL.  This definition makes
precise the closure premise needed to assemble component-core languages. -/
def PreservesMCFLTier {Sym : Type u_sym}
    (combine : List (Set (List Sym)) → Set (List Sym)) (d : ℕ) : Prop :=
  ∀ Ls : List (Set (List Sym)),
    (∀ L ∈ Ls, IsMCFL.{u_sym, 0} L d) → IsMCFL.{u_sym, 0} (combine Ls) d

/-- Minimal (exact) MCFG dimension.  Unlike `IsMCFL.{u_sym, 0} L d`, this says that no
strictly smaller dimension suffices. -/
def HasExactMCFLDimension {Sym : Type u_sym}
    (L : Set (List Sym)) (d : ℕ) : Prop :=
  IsMCFL.{u_sym, 0} L d ∧ ∀ e < d, ¬ IsMCFL.{u_sym, 0} L e

/-- Equality of languages transports an exact MCFG tier in either direction. -/
theorem hasExactMCFLDimension_congr {Sym : Type u_sym}
    {L K : Set (List Sym)} (h : L = K) (d : ℕ) :
    HasExactMCFLDimension L d ↔ HasExactMCFLDimension K d := by
  subst h
  rfl

namespace HomSystem

variable {Obj : Type u_obj} (S : HomSystem Obj)

/-- Full composition theorem with the language-closure premise exposed.

If each component-core language is a `d`-MCFL, `combine` preserves tier `d`,
and its result is the decision language of the composed core structure, then
semantic equivalence transfers the resulting `d`-MCFL characterization to the
original composed CSP. -/
theorem complexity_correspondence_of_tier_preserving_composition
    {Sym : Type u_sym}
    (C : S.HomComposition)
    (originals cores : List Obj)
    (hcores : List.Forall₂ S.Equivalent originals cores)
    (target : List Sym → Obj)
    (coreLanguages : List (Set (List Sym)))
    (combine : List (Set (List Sym)) → Set (List Sym))
    (d : ℕ)
    (hcomponents : ∀ L ∈ coreLanguages, IsMCFL.{u_sym, 0} L d)
    (hclosure : PreservesMCFLTier combine d)
    (hidentifies : combine coreLanguages =
      S.DecisionLanguage (C.compose cores) target) :
    S.DecisionLanguage (C.compose originals) target =
        S.DecisionLanguage (C.compose cores) target ∧
      IsMCFL.{u_sym, 0} (S.DecisionLanguage (C.compose originals) target) d := by
  have hcombined : IsMCFL.{u_sym, 0} (combine coreLanguages) d :=
    hclosure coreLanguages hcomponents
  have hcore : IsMCFL.{u_sym, 0} (S.DecisionLanguage (C.compose cores) target) d := by
    rw [← hidentifies]
    exact hcombined
  exact S.complexity_correspondence_via_core_composition
    C originals cores hcores target d hcore

/-- Core-witness form of the correspondence theorem.  This version explicitly
records that every chosen representative satisfies `IsCore`, while retaining
the purely existential, non-algorithmic nature of the witnesses. -/
theorem complexity_correspondence_via_static_core_witnesses
    {Sym : Type u_sym} (IsCore : Obj → Prop)
    (C : S.HomComposition)
    (originals cores : List Obj)
    (hcores : List.Forall₂ (S.CoreWitness IsCore) originals cores)
    (target : List Sym → Obj) (d : ℕ)
    (hcoreMCFL : IsMCFL.{u_sym, 0}
      (S.DecisionLanguage (C.compose cores) target) d) :
    S.DecisionLanguage (C.compose originals) target =
        S.DecisionLanguage (C.compose cores) target ∧
      IsMCFL.{u_sym, 0}
        (S.DecisionLanguage (C.compose originals) target) d :=
  S.complexity_correspondence_via_core_composition
    C originals cores (S.equivalents_of_coreWitnesses IsCore hcores)
      target d hcoreMCFL

/-- If the composed core language has exact dimension `d`, then so does the
original composed CSP language.  Thus semantic replacement preserves not only
an upper bound but the minimal MCFG tier itself. -/
theorem exact_complexity_correspondence_via_core_composition
    {Sym : Type u_sym}
    (C : S.HomComposition)
    (originals cores : List Obj)
    (hcores : List.Forall₂ S.Equivalent originals cores)
    (target : List Sym → Obj) (d : ℕ)
    (hcoreExact : HasExactMCFLDimension
      (S.DecisionLanguage (C.compose cores) target) d) :
    HasExactMCFLDimension
      (S.DecisionLanguage (C.compose originals) target) d := by
  have hEq : S.DecisionLanguage (C.compose originals) target =
      S.DecisionLanguage (C.compose cores) target :=
    S.decisionLanguage_eq_of_equivalent (C.respects_equivalence hcores) target
  exact (hasExactMCFLDimension_congr hEq d).2 hcoreExact

end HomSystem
