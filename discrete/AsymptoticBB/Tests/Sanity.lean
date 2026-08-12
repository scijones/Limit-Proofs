/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Main

/-!
# Sanity Tests: Non-Vacuous Behavior Languages

Audit remediation (vacuous-soundness protection): because the empty
language is trivially a `(k+1)`-MCFL (`MCFG.empty_language`), the
headline bound `full_behavior_bound` could be satisfied vacuously by an
agent whose behavior language accidentally collapsed to `∅` through a
projection bug. This file guards against that failure mode:

1. `EmbodiedAgent.behaviorLanguage_nonempty`: any agent with a
   satisfiable CSP has a non-empty behavior language.
2. `flagAgent`: a concrete non-trivial agent (one Boolean variable
   constrained to `true`, which is also the action variable), with an
   explicit proof that the word `[true]` is in its behavior language
   and that the language is non-empty.
-/

set_option autoImplicit false

universe u v

/-- **Non-vacuity guard.** Any embodied agent whose CSP is satisfiable
has a non-empty behavior language: project any satisfying assignment
along any enumeration of the action variables. -/
theorem EmbodiedAgent.behaviorLanguage_nonempty
    {V : Type u} [DecidableEq V] [Fintype V] {D : V → Type v}
    (A : EmbodiedAgent V D) (hsat : A.toCSP.IsSatisfiable)
    (Sym : Type*) (encode : (v : V) → D v → Sym) :
    (A.BehaviorLanguage Sym encode).Nonempty := by
  obtain ⟨β, hβ⟩ := hsat
  exact ⟨A.action_vars.toList.map (fun v => encode v (β v)),
    β, hβ, A.action_vars.toList,
    Finset.toList_toFinset _, A.action_vars.nodup_toList, rfl⟩

/-! ## A concrete non-trivial agent -/

/-- A minimal non-trivial agent: one Boolean variable, constrained to be
`true`, designated as the (sole) action variable. Its behavior language
should be exactly `{[true]}` — in particular, non-empty. -/
def flagAgent : EmbodiedAgent (Fin 1) (fun _ => Bool) where
  constraints := [{ scope := [0],
                    scope_nodup := List.nodup_singleton 0,
                    relation := fun f => f ⟨0, Nat.one_pos⟩ = true }]
  action_vars := {0}
  action_vars_nonempty := ⟨0, Finset.mem_singleton_self 0⟩

/-- The all-`true` assignment satisfies `flagAgent`'s CSP. -/
theorem flagAgent_satisfiable : flagAgent.toCSP.IsSatisfiable := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  simp only [flagAgent, List.mem_singleton] at hc
  subst hc
  rfl

/-- Concrete membership: the word `[true]` is a behavior of `flagAgent`.
This pins the non-vacuity witness to an explicit string, so a projection
bug that silently mapped the agent to the empty language would break
this proof. -/
theorem flagAgent_behavior_mem :
    [true] ∈ flagAgent.BehaviorLanguage Bool (fun _ b => b) := by
  refine ⟨fun _ => true, ?_, [0], ?_, List.nodup_singleton 0, rfl⟩
  · intro c hc
    simp only [flagAgent, List.mem_singleton] at hc
    subst hc
    rfl
  · rfl

/-- `flagAgent`'s behavior language is non-empty. -/
theorem flagAgent_behaviorLanguage_nonempty :
    (flagAgent.BehaviorLanguage Bool (fun _ b => b)).Nonempty :=
  ⟨[true], flagAgent_behavior_mem⟩

/-! ## Tree-level and full-behavior non-vacuity

The headline theorems conclude `IsMCFL L (k+1)` for the tree-structured
and full behavior languages. `MCFG.empty` shows the empty language
satisfies any dimension bound, so these guards certify that the
languages the theorems bound are not accidentally empty. -/

/-- **Non-vacuity guard (tree level).** Any agent with a satisfiable CSP
has a non-empty tree-structured behavior language, for every rooted tree
decomposition: some tree-compatible ordering exists
(`isTreeCompatibleOrdering_nonempty`), and projecting any satisfying
assignment along it produces a behavior string. -/
theorem EmbodiedAgent.treeBehaviorLanguage_nonempty
    {V : Type u} [DecidableEq V] [Fintype V] {D : V → Type v}
    (A : EmbodiedAgent V D) (hsat : A.toCSP.IsSatisfiable)
    (td : TreeDecomposition A.constraintHypergraph) (r : td.I)
    (Sym : Type*) (encode : (v : V) → D v → Sym) :
    (A.TreeBehaviorLanguage td r Sym encode).Nonempty := by
  obtain ⟨β, hβ⟩ := hsat
  obtain ⟨perm, hperm⟩ := isTreeCompatibleOrdering_nonempty td r
  exact ⟨_, β, hβ, perm, hperm, rfl⟩

/-- **Non-vacuity guard (full behavior).** Any agent with a satisfiable
CSP and a width-`≤k` tree decomposition has a non-empty full behavior
language at width bound `k`. Together with `full_behavior_bound`, this
rules out the failure mode where the headline bound is met by the empty
grammar: the language being bounded is provably inhabited. -/
theorem EmbodiedAgent.fullBehaviorLanguage_nonempty
    {V : Type u} [DecidableEq V] [Fintype V]
    {D : V → Type v} [∀ v, DecidableEq (D v)] [∀ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (k : ℕ) (hsat : A.toCSP.IsSatisfiable)
    (htw : A.constraintHypergraph.HasTreewidthAtMost k)
    (Sym : Type*) (encode : (v : V) → D v → Sym) :
    (A.FullBehaviorLanguage k Sym encode).Nonempty := by
  obtain ⟨td, hwidth⟩ := htw
  have hr : Nonempty td.I := td.instNonemptyI
  obtain ⟨r⟩ := hr
  obtain ⟨w, hw⟩ := A.treeBehaviorLanguage_nonempty hsat td r Sym encode
  exact ⟨w, td, r, hwidth, hw⟩

/-!
The non-emptiness theorem above is independent of the grammar bound.  The active
`full_behavior_bound` obtains each constituent language from the width-bounded
bridge and then stitches the finite family existentially; no particular
solution or derivation is required to be preserved.
-/

/-! ## Non-vacuity of the intendable (certified-quotient) layer -/

/-- **Non-vacuity guard (certified-quotient level).**  Any agent with a
satisfiable CSP, under the identity retraction onto itself and any rooted
tree decomposition, has a non-empty certified-quotient behavior language:
the identity retraction exists for every agent (`CSPRetraction.refl`),
is rigid (`CSPRetraction.refl_rigid` — so every solution factors), action
typing holds trivially, and any satisfying assignment with any
tree-compatible ordering and the canonical fibration produces a record.
Together with `certified_quotient_behavior_bound`, this rules out the
failure mode where the intendable ceiling is met by the empty grammar. -/
theorem EmbodiedAgent.certifiedQuotient_nonempty
    {V : Type u} [DecidableEq V] [Fintype V]
    {D : V → Type v} [∀ v, DecidableEq (D v)] [∀ v, Fintype (D v)]
    (A : EmbodiedAgent V D) (hsat : A.toCSP.IsSatisfiable)
    (td : TreeDecomposition A.constraintHypergraph) (r : td.I)
    (Sym : Type*) (encode : (w : V) → D w → Sym) :
    (CertifiedQuotientTreeBehaviorLanguage A A (CSPRetraction.refl A.toCSP)
      td r encode).Nonempty := by
  obtain ⟨β, hβ⟩ := hsat
  obtain ⟨perm, hperm⟩ := isTreeCompatibleOrdering_nonempty td r
  exact ⟨_, β, hβ, CSPRetraction.refl_rigid A.toCSP β hβ, perm, hperm,
    canonicalFibration A A (CSPRetraction.refl A.toCSP),
    canonicalFibration_valid A A (CSPRetraction.refl A.toCSP), rfl⟩

/-! ## Intention as store content: a concrete scheduling witness -/

/-- An agent whose store contains an explicit **order-belief** among its
action variables: variable `0` is an ordinary action (`Bool`, constrained
`true`); variable `1` is a scheduling decision (`Bool`, read as
``emit variable 0 in the first half of the cycle''), constrained `true`
by the store like any other belief.  Scheduling is not metadata here: it
is a typed, certified, emitted piece of store content. -/
def schedulerAgent : EmbodiedAgent (Fin 2) (fun _ => Bool) where
  constraints := [{ scope := [0],
                    scope_nodup := List.nodup_singleton 0,
                    relation := fun f => f ⟨0, Nat.one_pos⟩ = true },
                  { scope := [1],
                    scope_nodup := List.nodup_singleton 1,
                    relation := fun f => f ⟨0, Nat.one_pos⟩ = true }]
  action_vars := {0, 1}
  action_vars_nonempty := ⟨0, by decide⟩

/-- `schedulerAgent` is satisfiable (everything `true`). -/
theorem schedulerAgent_satisfiable : schedulerAgent.toCSP.IsSatisfiable := by
  refine ⟨fun _ => true, ?_⟩
  intro c hc
  simp only [schedulerAgent, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc
  · subst hc; rfl
  · subst hc; rfl

/-- **Intention-as-content witness.**  The certified (intended-record)
language of an agent whose action variables include an explicit
order-belief is non-empty: scheduling decisions are representable,
certifiable store content, and the ceiling covers them exactly as it
covers any other action (`intended_record_bound`).  This discharges, by
example, the reduction stated on `IntendedRecordLanguage`: "intending an
order" is nothing over and above holding a certified order-belief. -/
theorem schedulerAgent_certifiedQuotient_nonempty
    (td : TreeDecomposition schedulerAgent.constraintHypergraph) (r : td.I) :
    (CertifiedQuotientTreeBehaviorLanguage schedulerAgent schedulerAgent
      (CSPRetraction.refl schedulerAgent.toCSP) td r
      (coreEncode (V₂ := Fin 2) (D₂ := fun _ => Bool))).Nonempty :=
  schedulerAgent.certifiedQuotient_nonempty schedulerAgent_satisfiable
    td r _ coreEncode
