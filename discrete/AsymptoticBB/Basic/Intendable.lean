/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Bridge

/-!
# Intendable behavior: quotients of padded records (Option B, integrated)

This file states and proves the integrated Option-B theorem: the
*intendable* (quotient-encoded) behavior language of a padded agent,
defined from the padded agent's OWN solutions and schedules, equals a
symbol-to-word substitution image of its core representative's tree
behavior language — and is therefore a `(k+1)`-MCFL by the proved
homomorphic-image closure.  No axioms are introduced.

## The two counterexamples that shape the hypotheses

* **Loose copies** (kills naive quotients): `S = {a₁ : {0,1}, a₂ : {0,1,2}}`
  is hom-equivalent to `C = {a : {0,1}}` via `a₂ ↦ a₁`, yet the
  `S`-solution `(a₁ ↦ 0, a₂ ↦ 2)` quotients to a record containing `a:2`,
  which no core solution certifies.  Retractions are not canonical and do
  not respect action-value semantics.
* **Conditionally wild padding** (kills value-conservativity as a
  sufficient condition): padding whose constraints are vacuous on
  fiber-constant assignments but enforce cross-fiber threads on the
  remaining solutions is hom-equivalent to a free core and
  value-conservative, yet its quotient language contains
  `{u^(2m) : u ∈ {0,1}^n}` — unbounded copying, no fixed fan-out.  The
  ceiling *fails* there; the exclusion below is the boundary of the true
  theorem, not of the proof technique.

## The rigorous exclusion

`CSPRetraction.Rigid`: every solution of `S` factors through the typing
(each variable carries its representative's value).  An excluded agent is
one having a belief state its own semantic typing cannot express; by the
second counterexample the ceiling genuinely fails for such agents, so
"we do not care about the rest" is a theorem-shaped boundary, not a
convenience.

## Emission discipline

`QuotientTreeBehaviorLanguage` quantifies schedules as fiber expansions
of tree-compatible orderings of the CORE: each core variable's fiber is
emitted in one contiguous block (internal order free) at the position the
core ordering assigns.  This is the same time-mapping discipline the
minimal-store route always imposed — one pocket's work in one contiguous
span — stated at the quotient, where a fiber IS its core variable's
pocket.  Ordering discipline provably cannot be derived from the core
(shuffles of correlated streams carry no bounded-dimension guarantee), so
it enters as the modeling component of the agent class, visibly.

## Interpretation: types, promises, and the belief-driven class

Untyped actions cannot exist: the typing map is a homomorphism, and
homomorphisms are total — every variable, hence every action, has a
type.  Even a completely unconstrained action is typed (as the free
action over its domain).  No agent is excluded for having untypeable
actions; there is no such thing.

The content of an action's type is precisely its constraint
relationships:

* what the agent can PROMISE about an action is what its store's
  constraints say about it — a promise is a constraint undertaken to be
  kept satisfiable;
* what survives into the CORE is exactly the constraint role, nothing
  else;
* so an action's type is the sum of everything promisable about it.
  Same object, two names.

Edge cases confirm the identity rather than strain it.  An action with
no constraints is typed trivially and promisable-about trivially: any
value is always consistent, so promises about it are empty — the type is
honest that there was nothing to say.  An emission that depends on
something outside the constraint web (which redundant copy fired,
mechanism bookkeeping) is behavior EXCEEDING its type, and
`soundlyReportable_iff_factorsThrough` says exactly what that means: no
certificate can back a report of it.  Behavior beyond the type is
unpromisable — not forbidden (the agent can twitch), but nothing about
the twitch can be known, committed to, or corrected through any
constraint.

This closes a loop with the class definition itself.  Belief-driven
means acts are selected against the store; an action the store's
constraints do not touch is not belief-driven behavior at all.  The
typing requirement is therefore not a new demand on the agent — it is
the formal shadow of the class's first assumption, that actions come
from beliefs.  The ceiling covers everything the beliefs can send out;
the residue is exactly what the beliefs never sent.
-/

set_option autoImplicit false

universe u1 u2 v1 w_sym

variable {V₁ : Type u1} {V₂ : Type u2} [DecidableEq V₁] [DecidableEq V₂]
variable [Fintype V₁] [Fintype V₂]
variable {D₁ : V₁ → Type v1} {D₂ : V₂ → Type v1}

/-- A solution-transferring retraction between CSPs on different variable
sets: a typing map `ρ` and representative selection `ι`, with matching
domains, `ρ ∘ ι = id`, and solution transfer in both directions. -/
structure CSPRetraction (P : CSP V₁ D₁) (Q : CSP V₂ D₂) where
  /-- The typing map. -/
  ρ : V₁ → V₂
  /-- Representative selection. -/
  ι : V₂ → V₁
  /-- Domains agree along the typing. -/
  domEq : ∀ v, D₂ (ρ v) = D₁ v
  /-- Representatives are typed as themselves. -/
  sec : ∀ w, ρ (ι w) = w
  /-- Solutions of `Q` pull back along `ρ`. -/
  pull : ∀ τ, Q.IsSatisfying τ →
    P.IsSatisfying (fun v => cast (domEq v) (τ (ρ v)))
  /-- Solutions of `P` restrict along `ι`. -/
  restrict : ∀ σ, P.IsSatisfying σ →
    Q.IsSatisfying (fun w =>
      cast ((domEq (ι w)).symm.trans (congrArg D₂ (sec w))) (σ (ι w)))

namespace CSPRetraction

variable {P : CSP V₁ D₁} {Q : CSP V₂ D₂} (R : CSPRetraction P Q)

/-- Domain equality for representatives: `D₁ (ι w) = D₂ w`. -/
def domEqRep (w : V₂) : D₁ (R.ι w) = D₂ w :=
  (R.domEq (R.ι w)).symm.trans (congrArg D₂ (R.sec w))

/-- The restriction of a `P`-solution to a `Q`-assignment. -/
def restrictAssign (σ : ∀ v, D₁ v) : ∀ w, D₂ w :=
  fun w => cast (R.domEqRep w) (σ (R.ι w))

/-- Restriction of a satisfying assignment is satisfying. -/
theorem restrictAssign_satisfying {σ : ∀ v, D₁ v}
    (hσ : P.IsSatisfying σ) : Q.IsSatisfying (R.restrictAssign σ) := by
  have h := R.restrict σ hσ
  have heq : (fun w => cast ((R.domEq (R.ι w)).symm.trans
      (congrArg D₂ (R.sec w))) (σ (R.ι w))) = R.restrictAssign σ := rfl
  rwa [heq] at h

/-- **Rigidity**: every solution of `P` carries, at every variable, the
(transported) value of its representative — every solution factors
through the typing.  This is the exact boundary of the true theorem (see
module docstring). -/
def Rigid : Prop :=
  ∀ σ, P.IsSatisfying σ → ∀ v : V₁,
    cast (R.domEq v).symm (σ v) = R.restrictAssign σ (R.ρ v)

/-- A single solution **factors through** the typing: at every variable it
carries its representative's value.  `Rigid` = every satisfying solution
factors. -/
def FactorsThrough (σ : ∀ v, D₁ v) : Prop :=
  ∀ v : V₁, cast (R.domEq v).symm (σ v) = R.restrictAssign σ (R.ρ v)

/-- A solution's token-typed report is **sound** if one core solution
certifies every reported token jointly. -/
def SoundlyReportable (σ : ∀ v, D₁ v) : Prop :=
  ∃ τ, Q.IsSatisfying τ ∧ ∀ v : V₁,
    cast (R.domEq v).symm (σ v) = τ (R.ρ v)

/-- Transport of a dependent value along an index equality. -/
theorem cast_congrArg_apply {α : Type*} {D : α → Type*} (f : ∀ a, D a)
    {a b : α} (h : a = b) : cast (congrArg D h) (f a) = f b := by
  cases h; rfl

/-- **Well-posedness characterization.**  A solution's record admits a
sound token-typed core report **iff** the solution factors through the
typing.  Pointwise, both directions, no global hypothesis.

This is the formal content of "the rigid case is the only case there
is": a solution outside the factoring class is one about which NO
token-typed width-bounded description can speak without reporting a
record the core cannot certify.  `Rigid` is therefore not a modeling
restriction but the condition that the agent's entire behavior is
well-posed for narrow description; the residue is indescribable at this
width, not merely undescribed. -/
theorem soundlyReportable_iff_factorsThrough {σ : ∀ v, D₁ v}
    (hσ : P.IsSatisfying σ) :
    R.SoundlyReportable σ ↔ R.FactorsThrough σ := by
  constructor
  · rintro ⟨τ, _, hval⟩
    intro v
    rw [hval v]
    -- τ agrees with the restriction everywhere: evaluate `hval` at the
    -- representative of `ρ v`.
    have hrep := hval (R.ι (R.ρ v))
    unfold restrictAssign domEqRep
    rw [← cast_cast (R.domEq (R.ι (R.ρ v))).symm
      (congrArg D₂ (R.sec (R.ρ v))) (σ (R.ι (R.ρ v))), hrep,
      cast_congrArg_apply τ (R.sec (R.ρ v))]
  · intro hfac
    exact ⟨R.restrictAssign σ, R.restrictAssign_satisfying hσ, hfac⟩

/-- Pullbacks of core solutions factor through the typing. -/
theorem pullback_factorsThrough (τ : ∀ w, D₂ w) :
    R.FactorsThrough (fun v => cast (R.domEq v) (τ (R.ρ v))) := by
  intro v
  have hl : cast (R.domEq v).symm (cast (R.domEq v) (τ (R.ρ v))) =
      τ (R.ρ v) := by
    rw [cast_cast]
    exact cast_eq_iff_heq.mpr HEq.rfl
  rw [hl]
  unfold restrictAssign domEqRep
  rw [← cast_cast (R.domEq (R.ι (R.ρ v))).symm
    (congrArg D₂ (R.sec (R.ρ v))) _]
  have hm : cast (R.domEq (R.ι (R.ρ v))).symm
      (cast (R.domEq (R.ι (R.ρ v))) (τ (R.ρ (R.ι (R.ρ v))))) =
      τ (R.ρ (R.ι (R.ρ v))) := by
    rw [cast_cast]
    exact cast_eq_iff_heq.mpr HEq.rfl
  rw [hm, cast_congrArg_apply τ (R.sec (R.ρ v))]

end CSPRetraction

/-- The identity retraction: every CSP retracts onto itself.  Guards the
new definitions against vacuity — the retraction hypothesis of the
intendable theorems is satisfiable for every agent. -/
protected def CSPRetraction.refl {V : Type u1} [DecidableEq V] [Fintype V]
    {D : V → Type v1} (P : CSP V D) : CSPRetraction P P where
  ρ := id
  ι := id
  domEq := fun _ => rfl
  sec := fun _ => rfl
  pull := fun _ hτ => hτ
  restrict := fun _ hσ => hσ

/-- The identity retraction is rigid: every solution factors through it. -/
theorem CSPRetraction.refl_rigid {V : Type u1} [DecidableEq V] [Fintype V]
    {D : V → Type v1} (P : CSP V D) : (CSPRetraction.refl P).Rigid :=
  fun _ _ _ => rfl

section Quotient

variable [∀ v : V₁, Fintype (D₁ v)] [∀ v : V₁, DecidableEq (D₁ v)]
variable [∀ w : V₂, Fintype (D₂ w)] [∀ w : V₂, DecidableEq (D₂ w)]

/-- Action typing: actions are typed as actions.  Only this forward
direction is used by any proof, and it is exactly the direction that is
automatic once action-marking is part of the constraint structure (a
full-domain unary relation on each action variable): structure
homomorphisms preserve relations, so a retraction of the marked structure
cannot send an action anywhere untagged.  Marking costs nothing at any
fixed decomposition (unary edges impose no new bag obligations, arity
bound unaffected, solving unchanged), though marked cores can be larger
than blind cores, so the uniform Grohe constant is the marked class's. -/
def ActionTyped (S : EmbodiedAgent V₁ D₁) (C : EmbodiedAgent V₂ D₂)
    (R : CSPRetraction S.toCSP C.toCSP) : Prop :=
  ∀ v : V₁, v ∈ S.action_vars → R.ρ v ∈ C.action_vars

/-- A valid fiber enumeration: for each core variable, a duplicate-free
list of exactly its fiber. -/
def ValidFibration (S : EmbodiedAgent V₁ D₁) (C : EmbodiedAgent V₂ D₂)
    (R : CSPRetraction S.toCSP C.toCSP) (fe : V₂ → List V₁) : Prop :=
  ∀ w : V₂, (fe w).Nodup ∧ ∀ v : V₁, v ∈ fe w ↔ R.ρ v = w

/-- The canonical fiber enumeration. -/
noncomputable def canonicalFibration (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP) :
    V₂ → List V₁ :=
  fun w => (Finset.univ.filter (fun v => R.ρ v = w)).toList

theorem canonicalFibration_valid (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP) :
    ValidFibration S C R (canonicalFibration S C R) := by
  intro w
  constructor
  · exact Finset.nodup_toList _
  · intro v
    simp [canonicalFibration]

/-- The number of action variables in the fiber of `w`. -/
noncomputable def fiberActionCount (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (w : V₂) : ℕ :=
  (Finset.univ.filter (fun v => R.ρ v = w ∧ v ∈ S.action_vars)).card

/-- The canonical injective core event alphabet. -/
abbrev CoreEvent (V₂ : Type u2) (D₂ : V₂ → Type v1) := Σ w : V₂, D₂ w

/-- The canonical core encoding into the event alphabet. -/
def coreEncode : (w : V₂) → D₂ w → CoreEvent V₂ D₂ :=
  fun w d => ⟨w, d⟩

/-- The fiber substitution: each core event expands to fiber-many copies
of the target symbol. -/
noncomputable def fiberSubst (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    CoreEvent V₂ D₂ → List Sym :=
  fun e => List.replicate (fiberActionCount S C R e.1) (encodeC e.1 e.2)

/-- **The intendable (quotient) behavior language** of the padded agent,
defined from the padded agent's OWN data: its satisfying assignments, and
schedules that are fiber expansions of tree-compatible orderings of the
core representative.  Tokens are reported through the quotient encoding
`encodeC (ρ v) ·` (value transported). -/
def QuotientTreeBehaviorLanguage (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    Set (List Sym) :=
  { x | ∃ σ : ∀ v : V₁, D₁ v, S.toCSP.IsSatisfying σ ∧
        ∃ πC : List V₂, IsTreeCompatibleOrdering td r πC ∧
        ∃ fe : V₂ → List V₁, ValidFibration S C R fe ∧
        x = ((πC.map fe).flatten.map (fun v =>
          if v ∈ S.action_vars
          then [encodeC (R.ρ v) (cast (R.domEq v).symm (σ v))]
          else [])).flatten }

/-! ## List algebra helpers -/

theorem flatten_map_flatten {α β γ : Type*} (l : List α)
    (fe : α → List β) (g : β → List γ) :
    ((l.map fe).flatten.map g).flatten =
      (l.map (fun a => ((fe a).map g).flatten)).flatten := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append,
      List.flatten_append, ih]

/-- Emitting a fixed symbol at each satisfying position yields a
replicate of the count. -/
theorem emit_constant_block {α γ : Type*} (l : List α)
    (p : α → Bool) (s : γ) (emit : α → List γ)
    (h : ∀ a ∈ l, emit a = if p a then [s] else []) :
    (l.map emit).flatten = List.replicate (l.countP p) s := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.countP_cons]
    rw [h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]
    by_cases hp : p a
    · simp [hp, List.replicate_succ]
    · simp [hp]

/-- For a duplicate-free enumeration of the fiber of `w`, the count of
action variables equals `fiberActionCount`. -/
theorem countP_fiber_eq (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (fe : V₂ → List V₁) (hfe : ValidFibration S C R fe) (w : V₂) :
    (fe w).countP (fun v => decide (v ∈ S.action_vars)) =
      fiberActionCount S C R w := by
  classical
  obtain ⟨hnd, hmem⟩ := hfe w
  rw [List.countP_eq_length_filter]
  have hnd' : ((fe w).filter (fun v => decide (v ∈ S.action_vars))).Nodup :=
    hnd.filter _
  rw [← List.toFinset_card_of_nodup hnd']
  unfold fiberActionCount
  congr 1
  ext v
  simp only [List.mem_toFinset, List.mem_filter, hmem, Finset.mem_filter,
    Finset.mem_univ, true_and, decide_eq_true_eq]

/-- Per-node blockification: a fiber's emissions form a replicate block. -/
theorem fiber_block_eq (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (fe : V₂ → List V₁) (hfe : ValidFibration S C R fe)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym)
    (value : (w : V₂) → D₂ w) (emit : V₁ → List Sym)
    (hemit : ∀ v : V₁, emit v = if v ∈ S.action_vars
      then [encodeC (R.ρ v) (value (R.ρ v))] else [])
    (w : V₂) :
    ((fe w).map emit).flatten =
      List.replicate (fiberActionCount S C R w) (encodeC w (value w)) := by
  classical
  rw [← countP_fiber_eq S C R fe hfe w]
  apply emit_constant_block
  intro v hv
  have hρv : R.ρ v = w := ((hfe w).2 v).mp hv
  rw [hemit v, hρv]
  by_cases hva : v ∈ S.action_vars
  · simp [hva]
  · simp [hva]

/-- Non-action core variables have empty action fibers. -/
theorem fiberActionCount_eq_zero (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (hat : ActionTyped S C R) {w : V₂} (hw : w ∉ C.action_vars) :
    fiberActionCount S C R w = 0 := by
  classical
  unfold fiberActionCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro v -
  rintro ⟨hρv, hva⟩
  exact hw (hρv ▸ hat v hva)

/-! ## The integrated equality theorem -/

/-- **Intendable records are fiber-substitution images of core records,
and conversely** — for rigid, action-typed retractions and
fiber-contiguous schedules.

The left-hand side is defined from the padded agent's own solutions and
schedules; the right-hand side is the substitution image of the core
representative's tree behavior language over the injective event
alphabet.  Both inclusions are proved; rigidity is used exactly once, in
the forward direction (a padded solution's tokens all carry their
representative's value).  The reverse direction needs only the
retraction itself (core solutions pull back). -/
theorem quotient_eq_fiberSubst_image (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (hrig : R.Rigid) (hat : ActionTyped S C R)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    QuotientTreeBehaviorLanguage S C R td r encodeC =
      { x | ∃ y ∈ C.TreeBehaviorLanguage td r (CoreEvent V₂ D₂) coreEncode,
            x = (y.map (fiberSubst S C R encodeC)).flatten } := by
  classical
  ext x
  simp only [QuotientTreeBehaviorLanguage, Set.mem_setOf_eq,
    EmbodiedAgent.TreeBehaviorLanguage]
  constructor
  · rintro ⟨σ, hσ, πC, hπC, fe, hfe, rfl⟩
    refine ⟨(πC.map (fun w =>
      if w ∈ C.action_vars
      then [coreEncode w (R.restrictAssign σ w)]
      else [])).flatten,
      ⟨R.restrictAssign σ, R.restrictAssign_satisfying hσ, πC, hπC, rfl⟩, ?_⟩
    rw [flatten_map_flatten, flatten_map_flatten]
    congr 1
    apply List.map_congr_left
    intro w _
    rw [fiber_block_eq S C R fe hfe encodeC (R.restrictAssign σ) _
      (fun v => by
        by_cases hva : v ∈ S.action_vars
        · rw [if_pos hva, if_pos hva, hrig σ hσ v]
        · rw [if_neg hva, if_neg hva]) w]
    show _ = ((if w ∈ C.action_vars
      then [coreEncode w (R.restrictAssign σ w)]
      else []).map (fiberSubst S C R encodeC)).flatten
    by_cases hw : w ∈ C.action_vars
    · rw [if_pos hw]
      simp [fiberSubst, coreEncode]
    · rw [if_neg hw, fiberActionCount_eq_zero S C R hat hw]
      simp
  · rintro ⟨y, ⟨τ, hτ, πC, hπC, rfl⟩, rfl⟩
    refine ⟨fun v => cast (R.domEq v) (τ (R.ρ v)), R.pull τ hτ, πC, hπC,
      canonicalFibration S C R, canonicalFibration_valid S C R, ?_⟩
    rw [flatten_map_flatten, flatten_map_flatten]
    congr 1
    apply List.map_congr_left
    intro w _
    rw [fiber_block_eq S C R (canonicalFibration S C R)
      (canonicalFibration_valid S C R) encodeC τ _
      (fun v => by
        by_cases hva : v ∈ S.action_vars
        · simp [hva]
        · simp [hva]) w]
    by_cases hw : w ∈ C.action_vars
    · rw [if_pos hw]
      simp [fiberSubst, coreEncode]
    · rw [if_neg hw, fiberActionCount_eq_zero S C R hat hw]
      simp

/-! ## The dimension corollary -/

/-- **The intendable ceiling, integrated** (per agent and representative).

If the padded agent admits a rigid, action-typed retraction onto a core
representative whose constraint hypergraph has a width-`≤ k` rooted tree
decomposition, then its intendable behavior language (fiber-contiguous
schedules, quotient encoding) is a `(k+1)`-MCFL.

Kernel inputs: the bridge construction and homomorphic-image closure,
both proved.  No axioms enter through this corollary. -/
theorem quotient_behavior_bound (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (hrig : R.Rigid) (hat : ActionTyped S C R)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    (k : ℕ) (hk : td.width ≤ k)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    IsMCFL.{w_sym, 0}
      (QuotientTreeBehaviorLanguage S C R td r encodeC) (k + 1) := by
  classical
  obtain ⟨G, hGdim, hGlang⟩ := behavior_grammar_exists C td r k hk
    (CoreEvent V₂ D₂) coreEncode
  obtain ⟨G', hG'dim, hG'lang⟩ :=
    mcfg_homomorphic_image G (fiberSubst S C R encodeC)
  refine ⟨G', le_trans hG'dim hGdim, ?_⟩
  rw [hG'lang, hGlang,
    quotient_eq_fiberSubst_image S C R hrig hat td r encodeC]

/-! ## The full-scope certified language (no rigidity hypothesis) -/

/-- **The certified-intendable behavior language**, defined for EVERY
agent with a typed retraction — no rigidity hypothesis.  It collects the
records of exactly the solutions that factor through the typing, i.e.
(by `soundlyReportable_iff_factorsThrough`) exactly the records that
admit a sound narrow report at all.  The residue is not excluded by
choice: it is indescribable at this width, provably. -/
def CertifiedQuotientTreeBehaviorLanguage (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    Set (List Sym) :=
  { x | ∃ σ : ∀ v : V₁, D₁ v, S.toCSP.IsSatisfying σ ∧
        R.FactorsThrough σ ∧
        ∃ πC : List V₂, IsTreeCompatibleOrdering td r πC ∧
        ∃ fe : V₂ → List V₁, ValidFibration S C R fe ∧
        x = ((πC.map fe).flatten.map (fun v =>
          if v ∈ S.action_vars
          then [encodeC (R.ρ v) (cast (R.domEq v).symm (σ v))]
          else [])).flatten }

/-- The certified language equals the fiber-substitution image of the
core's tree behavior language — for EVERY agent, rigidity nowhere.
Forward: factoring is available per-solution from the definition.
Reverse: pullbacks factor (`pullback_factorsThrough`). -/
theorem certified_quotient_eq_fiberSubst_image (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (hat : ActionTyped S C R)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    CertifiedQuotientTreeBehaviorLanguage S C R td r encodeC =
      { x | ∃ y ∈ C.TreeBehaviorLanguage td r (CoreEvent V₂ D₂) coreEncode,
            x = (y.map (fiberSubst S C R encodeC)).flatten } := by
  classical
  ext x
  simp only [CertifiedQuotientTreeBehaviorLanguage, Set.mem_setOf_eq,
    EmbodiedAgent.TreeBehaviorLanguage]
  constructor
  · rintro ⟨σ, hσ, hfac, πC, hπC, fe, hfe, rfl⟩
    refine ⟨(πC.map (fun w =>
      if w ∈ C.action_vars
      then [coreEncode w (R.restrictAssign σ w)]
      else [])).flatten,
      ⟨R.restrictAssign σ, R.restrictAssign_satisfying hσ, πC, hπC, rfl⟩, ?_⟩
    rw [flatten_map_flatten, flatten_map_flatten]
    congr 1
    apply List.map_congr_left
    intro w _
    rw [fiber_block_eq S C R fe hfe encodeC (R.restrictAssign σ) _
      (fun v => by
        by_cases hva : v ∈ S.action_vars
        · rw [if_pos hva, if_pos hva, hfac v]
        · rw [if_neg hva, if_neg hva]) w]
    by_cases hw : w ∈ C.action_vars
    · rw [if_pos hw]
      simp [fiberSubst, coreEncode]
    · rw [if_neg hw, fiberActionCount_eq_zero S C R hat hw]
      simp
  · rintro ⟨y, ⟨τ, hτ, πC, hπC, rfl⟩, rfl⟩
    refine ⟨fun v => cast (R.domEq v) (τ (R.ρ v)), R.pull τ hτ,
      R.pullback_factorsThrough τ, πC, hπC,
      canonicalFibration S C R, canonicalFibration_valid S C R, ?_⟩
    rw [flatten_map_flatten, flatten_map_flatten]
    congr 1
    apply List.map_congr_left
    intro w _
    rw [fiber_block_eq S C R (canonicalFibration S C R)
      (canonicalFibration_valid S C R) encodeC τ _
      (fun v => by
        by_cases hva : v ∈ S.action_vars
        · simp [hva]
        · simp [hva]) w]
    by_cases hw : w ∈ C.action_vars
    · rw [if_pos hw]
      simp [fiberSubst, coreEncode]
    · rw [if_neg hw, fiberActionCount_eq_zero S C R hat hw]
      simp

/-- **The full-scope intendable ceiling.**  For EVERY agent with an
action-typed retraction onto a width-`≤ k` core representative — no
rigidity, gap region included — the language of soundly-reportable
records is a `(k+1)`-MCFL.  Combined with
`soundlyReportable_iff_factorsThrough`, everything a width-bounded
token-typed description can soundly say about ANY such agent's behavior
is `(k+1)`-bounded, and nothing more can be soundly said at that width. -/
theorem certified_quotient_behavior_bound (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (hat : ActionTyped S C R)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    (k : ℕ) (hk : td.width ≤ k)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    IsMCFL.{w_sym, 0}
      (CertifiedQuotientTreeBehaviorLanguage S C R td r encodeC) (k + 1) := by
  classical
  obtain ⟨G, hGdim, hGlang⟩ := behavior_grammar_exists C td r k hk
    (CoreEvent V₂ D₂) coreEncode
  obtain ⟨G', hG'dim, hG'lang⟩ :=
    mcfg_homomorphic_image G (fiberSubst S C R encodeC)
  refine ⟨G', le_trans hG'dim hGdim, ?_⟩
  rw [hG'lang, hGlang,
    certified_quotient_eq_fiberSubst_image S C R hat td r encodeC]

/-- Rigidity characterized: for rigid agents the certified language is
the whole quotient language — all behavior is soundly reportable. -/
theorem rigid_certified_eq_quotient (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (hrig : R.Rigid)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    CertifiedQuotientTreeBehaviorLanguage S C R td r encodeC =
      QuotientTreeBehaviorLanguage S C R td r encodeC := by
  ext x
  simp only [CertifiedQuotientTreeBehaviorLanguage,
    QuotientTreeBehaviorLanguage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨σ, hσ, -, rest⟩
    exact ⟨σ, hσ, rest⟩
  · rintro ⟨σ, hσ, rest⟩
    exact ⟨σ, hσ, hrig σ hσ, rest⟩

/-! ## Intention reduced to store content, explicitly -/

/-- **The intended-record language** — the formal referent of "intention"
in this development, BY DEFINITION equal to the certified quotient
language.  This abbreviation exists to make the reduction explicit in
the kernel-checked source rather than in prose:

* "intention" has no other formal meaning here.  Actions exist as
  beliefs (action variables ARE store variables); an intended act is a
  certified value of such a variable; an intended SCHEDULE is the same
  thing — order-beliefs are variables like any others, and scheduling
  decisions among the action variables are covered by the ceiling
  exactly as any other action (instantiate the bound with the
  order-beliefs among `action_vars`; see `schedulerAgent` in
  `Tests/Sanity.lean` for a concrete witness).
* Consequently "the agent intends a non-tree-compatible emission" has
  no formal counterpart to hypothesize away: enforced order is store
  content and falls under `certified_quotient_behavior_bound`;
  unenforced order is, by `soundlyReportable_iff_factorsThrough`
  applied to the order-beliefs, unpromisable residue.  A string-level
  strengthening ("every certifiable string is tree-compatible") is
  FALSE — two unlinked width-1 chains emit certifiable alternations of
  unbounded fan-out — and is not claimed; what the alternation lacks is
  exactly enforcement, i.e. intention. -/
abbrev IntendedRecordLanguage (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    Set (List Sym) :=
  CertifiedQuotientTreeBehaviorLanguage S C R td r encodeC

/-- The ceiling, stated for the intended-record language by name. -/
theorem intended_record_bound (S : EmbodiedAgent V₁ D₁)
    (C : EmbodiedAgent V₂ D₂) (R : CSPRetraction S.toCSP C.toCSP)
    (hat : ActionTyped S C R)
    (td : TreeDecomposition C.constraintHypergraph) (r : td.I)
    (k : ℕ) (hk : td.width ≤ k)
    {Sym : Type w_sym} (encodeC : (w : V₂) → D₂ w → Sym) :
    IsMCFL.{w_sym, 0}
      (IntendedRecordLanguage S C R td r encodeC) (k + 1) :=
  certified_quotient_behavior_bound S C R hat td r k hk encodeC

end Quotient
