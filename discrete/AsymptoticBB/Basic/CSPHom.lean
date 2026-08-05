/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Basic.SizedInstances
import AsymptoticBB.SemanticCore

/-!
# Concrete instantiation of the semantic-core layer at sized CSPs

`SemanticCore.lean` proves its invariance results for an arbitrary
`HomSystem` — an abstract preorder of objects with identity and
composition.  Until this file, nothing connected that abstraction to any
concrete object of the development (see the SCOPE WARNING on
`HomSystem.certifiable_behavior_core_bound`).

This file supplies the connection for the objects that carry real
semantics in this project: `SizedCSP`s and their solution sets.

* `SizedCSP.SemHom P Q` — a *solution-transferring homomorphism*: a
  variable map `Q ← P`… precisely, a map `toFun : Fin P.n → Fin Q.n`
  with domain agreement, such that **pulling any solution of `Q` back
  along the map yields a solution of `P`**.  This is the semantic content
  of "P's constraints are entailed by Q's under the renaming"; it is
  exactly what padding retractions and core inclusions provide.
* `SizedCSP.homSystem` — the `HomSystem` instance: `Hom P Q :=
  Nonempty (P.SemHom Q)`, with identity and composition **proved**, not
  assumed.
* `SizedCSP.satisfiable_iff_of_equivalent` — hom-equivalent sized CSPs
  are equisatisfiable: the concrete promise-keepability invariance.
* `SizedCSP.certifiable_core_bound` — the abstract core-transfer theorem
  instantiated at sized CSPs: for certification questions of the shape
  "does the store, mapped into the situation `target w`, remain
  solvable?", a core witness transfers any MCFG dimension bound because
  the two certifiable languages are equal.

What this file deliberately does NOT claim (the remaining, documented
gaps): (1) no identification of these certifiable languages with
`FullBehaviorLanguage` — that is the visible `hcore_realize` hypothesis;
(2) situations that share variables with the store (interfaces) are not
treated: `target` must be a store-independent encoding (closed queries).
Bounded-interface variants are future work.  No axiom is introduced
anywhere in this file.
-/

set_option autoImplicit false

universe u_sym

/-! ## Solutions of sized CSPs -/

/-- A total assignment satisfying every constraint of the sized CSP. -/
def SizedCSP.IsSolution (P : SizedCSP) (σ : ∀ v : Fin P.n, P.D v) : Prop :=
  P.csp.IsSatisfying σ

/-- A sized CSP is satisfiable if it has a solution. -/
def SizedCSP.Satisfiable (P : SizedCSP) : Prop :=
  ∃ σ, P.IsSolution σ

/-! ## Solution-transferring homomorphisms -/

/-- A solution-transferring homomorphism of sized CSPs: a variable map
with matching domains along which every solution of the codomain pulls
back to a solution of the domain.

This is the semantic notion the core-transfer argument needs, stated
directly (rather than via syntactic constraint mapping): padding
retractions provide `SemHom S core` (assign each padded variable the
value of its representative), and core inclusions provide
`SemHom core S` (restrict). -/
structure SizedCSP.SemHom (P Q : SizedCSP) where
  /-- The variable renaming. -/
  toFun : Fin P.n → Fin Q.n
  /-- Domains agree along the renaming. -/
  dom_eq : ∀ v, Q.D (toFun v) = P.D v
  /-- Every solution of `Q` pulls back to a solution of `P`. -/
  pullback : ∀ σ, Q.IsSolution σ →
    P.IsSolution (fun v => cast (dom_eq v) (σ (toFun v)))

namespace SizedCSP

/-- The identity solution-transferring homomorphism. -/
def SemHom.id (P : SizedCSP) : P.SemHom P where
  toFun := fun v => v
  dom_eq := fun _ => rfl
  pullback := fun σ hσ => by
    have h : (fun v => cast rfl (σ v)) = σ := funext fun v => cast_eq rfl _
    rw [h]
    exact hσ

/-- Composition of solution-transferring homomorphisms. -/
def SemHom.comp {P Q R : SizedCSP} (f : P.SemHom Q) (g : Q.SemHom R) :
    P.SemHom R where
  toFun := fun v => g.toFun (f.toFun v)
  dom_eq := fun v => (g.dom_eq (f.toFun v)).trans (f.dom_eq v)
  pullback := fun σ hσ => by
    have hQ := g.pullback σ hσ
    have hP := f.pullback _ hQ
    have h : (fun v => cast (f.dom_eq v)
        ((fun w => cast (g.dom_eq w) (σ (g.toFun w))) (f.toFun v))) =
        (fun v => cast ((g.dom_eq (f.toFun v)).trans (f.dom_eq v))
          (σ (g.toFun (f.toFun v)))) := by
      funext v
      exact (cast_cast _ _ _).symm ▸ rfl
    rw [← h]
    exact hP

/-- The `HomSystem` of sized CSPs under solution-transferring
homomorphisms.  Identity and composition are proved above; nothing is
assumed. -/
def homSystem : HomSystem SizedCSP where
  Hom P Q := Nonempty (P.SemHom Q)
  refl P := ⟨SemHom.id P⟩
  trans := fun ⟨f⟩ ⟨g⟩ => ⟨f.comp g⟩

/-! ## Concrete invariance -/

/-- **Hom-equivalent sized CSPs are equisatisfiable.**  The concrete
promise-keepability invariance: a store and its core give the same answer
to "are my commitments jointly keepable?", proved by pulling solutions
back along the two homomorphisms.  No axioms. -/
theorem satisfiable_iff_of_equivalent {P K : SizedCSP}
    (h : homSystem.Equivalent P K) :
    P.Satisfiable ↔ K.Satisfiable := by
  obtain ⟨⟨f⟩, ⟨g⟩⟩ := h
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, g.pullback σ hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨_, f.pullback σ hσ⟩

/-- **Core transfer for certifiable languages of sized CSPs.**  The
abstract `HomSystem.certifiable_behavior_core_bound`, instantiated at
concrete sized CSPs with solution-transferring homomorphisms.

For any store-independent situation encoding `target : List Sym → SizedCSP`,
the certifiable language `{w | ∃ hom from the store into target w}` of a
padded store equals that of its core, so any MCFG dimension bound on the
core's certifiable language holds verbatim for the original's.

The certification shape here is `Nonempty (P.SemHom (target w))` — "the
store maps solution-transferringly into the `w`-situation".  Identifying
an agent's operational behavior with a language of this shape (and the
choice of `target`) is the visible modeling step (`hcore_realize` in
`Main.lean`); this theorem discharges only the invariance half, now at
the concrete objects rather than in a floating abstraction. -/
theorem certifiable_core_bound {Sym : Type u_sym}
    (IsCore : SizedCSP → Prop) {P K : SizedCSP}
    (h : homSystem.CoreWitness IsCore P K)
    (target : List Sym → SizedCSP) (d : ℕ)
    (hK : IsMCFL.{u_sym, 0} (homSystem.DecisionLanguage K target) d) :
    homSystem.DecisionLanguage P target =
        homSystem.DecisionLanguage K target ∧
      IsMCFL.{u_sym, 0} (homSystem.DecisionLanguage P target) d :=
  homSystem.certifiable_behavior_core_bound IsCore h target d hK

end SizedCSP
