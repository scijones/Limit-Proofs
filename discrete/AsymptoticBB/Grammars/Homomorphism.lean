/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Grammars.MCFG
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# MCFLs are closed under homomorphic image

This module **replaces** the former external assumption
`mcfg_homomorphic_image` (Seki et al. 1991, Theorem 3.9) with a concrete
construction and a machine-checked proof.

Given an MCFG `G` over `Sym₁` and a word-valued substitution
`h : Sym₁ → List Sym₂`, the **image grammar** `G.homImage h` is obtained by
replacing every terminal occurrence `a` in every production string by the
word `h a`, keeping all variables, nonterminals, and arities unchanged.
The nonterminal type is transported to `ULift (Fin |N|)` along
`Fintype.equivFin`, so the image grammar lives at any desired universe.

Since arities are untouched, `dimension (G.homImage h) ≤ dimension G` holds
by construction.  The language identity

`L(G.homImage h) = { (w.map h).flatten | w ∈ L(G) }`

is proved by two derivation inductions:

* **transport** (`homImage_generates_of`): every `G`-derivation maps to an
  image derivation, substituting `η' := fun x => ((η x).map h).flatten`;
* **reflection** (`generates_of_homImage`): every image derivation arises
  this way — the pre-image substitution `η` is reconstructed per variable
  from the child tuples, using the copylessness of productions (each
  variable belongs to exactly one right-hand-side component).

All substitution helper lemmas are stated **generically over the expansion
function** (with pointwise hypotheses) so that they unify with the matcher
constants produced by `MCFG.Generates.prod` regardless of elaboration site.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u1 u2 v1 v2

noncomputable section HomImage

set_option linter.style.openClassical false
open Classical

variable {Sym₁ : Type u1} {Sym₂ : Type u2}

/-! ### Terminal substitution in production strings -/

/-- Substitute a single production-string symbol: a terminal becomes the
word `h a` (as terminals), a variable is kept. -/
def symSub (h : Sym₁ → List Sym₂) : (Sym₁ ⊕ ℕ) → List (Sym₂ ⊕ ℕ)
  | Sum.inl a => (h a).map Sum.inl
  | Sum.inr x => [Sum.inr x]

/-- Substitute all terminals in a production string. -/
def strSub (h : Sym₁ → List Sym₂) (s : List (Sym₁ ⊕ ℕ)) : List (Sym₂ ⊕ ℕ) :=
  s.flatMap (symSub h)

/-- The word-level transport: `w ↦ (w.map h).flatten`. -/
def transWord (h : Sym₁ → List Sym₂) (w : List Sym₁) : List Sym₂ :=
  (w.map h).flatten

private theorem flatten_map_singleton {α : Type*} (l : List α) :
    (l.map (fun b => [b])).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Variables occurring in a substituted string are exactly those of the
original, for any variable-extractor `f` that ignores terminals. -/
private theorem strSub_filterMap (h : Sym₁ → List Sym₂)
    (f₁ : (Sym₁ ⊕ ℕ) → Option ℕ) (f₂ : (Sym₂ ⊕ ℕ) → Option ℕ)
    (hf₁l : ∀ a, f₁ (Sum.inl a) = none) (hf₁r : ∀ x, f₁ (Sum.inr x) = some x)
    (hf₂l : ∀ b, f₂ (Sum.inl b) = none) (hf₂r : ∀ x, f₂ (Sum.inr x) = some x)
    (s : List (Sym₁ ⊕ ℕ)) :
    (strSub h s).filterMap f₂ = s.filterMap f₁ := by
  induction s with
  | nil => rfl
  | cons tok rest ih =>
    have hcons : strSub h (tok :: rest) = symSub h tok ++ strSub h rest := rfl
    rw [hcons, List.filterMap_append, ih]
    cases tok with
    | inl a =>
      have hnil : ((h a).map Sum.inl).filterMap f₂ = [] := by
        induction h a with
        | nil => rfl
        | cons b bs ihb =>
          simp only [List.map_cons, List.filterMap_cons, hf₂l b]
          exact ihb
      rw [List.filterMap_cons, hf₁l a]
      show ((h a).map Sum.inl).filterMap f₂ ++ _ = _
      rw [hnil, List.nil_append]
    | inr x =>
      rw [List.filterMap_cons, hf₁r x]
      show (List.filterMap f₂ [Sum.inr x]) ++ _ = _
      rw [show List.filterMap f₂ [Sum.inr x] = [x] from by
        simp [List.filterMap_cons, hf₂r x]]
      rfl

/-- Membership of variables in substituted strings. -/
private theorem mem_inr_strSub {h : Sym₁ → List Sym₂}
    {s : List (Sym₁ ⊕ ℕ)} {x : ℕ}
    (hx : (Sum.inr x : Sym₂ ⊕ ℕ) ∈ strSub h s) :
    (Sum.inr x : Sym₁ ⊕ ℕ) ∈ s := by
  obtain ⟨tok, htok, hmem⟩ := List.mem_flatMap.mp hx
  cases tok with
  | inl a =>
    obtain ⟨b, -, hcon⟩ := List.mem_map.mp hmem
    exact absurd hcon (by simp)
  | inr y =>
    have : (Sum.inr x : Sym₂ ⊕ ℕ) = Sum.inr y := List.mem_singleton.mp hmem
    obtain rfl : x = y := by simpa using this
    exact htok

/-- **The substitution–expansion exchange.**  Expanding a substituted string
under `η'` equals transporting the expansion of the original string under
`η`, provided `η' x = transWord h (η x)` on the variables that occur.
Stated generically over the two expansion functions. -/
private theorem strSub_expand (h : Sym₁ → List Sym₂)
    (η : ℕ → List Sym₁) (η' : ℕ → List Sym₂)
    (F : (Sym₁ ⊕ ℕ) → List Sym₁) (F' : (Sym₂ ⊕ ℕ) → List Sym₂)
    (hFl : ∀ a, F (Sum.inl a) = [a]) (hFr : ∀ x, F (Sum.inr x) = η x)
    (hF'l : ∀ b, F' (Sum.inl b) = [b]) (hF'r : ∀ x, F' (Sum.inr x) = η' x)
    (s : List (Sym₁ ⊕ ℕ))
    (hη : ∀ x, (Sum.inr x : Sym₁ ⊕ ℕ) ∈ s → η' x = transWord h (η x)) :
    ((strSub h s).map F').flatten = transWord h ((s.map F).flatten) := by
  induction s with
  | nil => simp [strSub, transWord]
  | cons tok rest ih =>
    have hcons : strSub h (tok :: rest) = symSub h tok ++ strSub h rest := rfl
    have hrest := ih (fun x hx => hη x (List.mem_cons_of_mem tok hx))
    rw [hcons, List.map_append, List.flatten_append, hrest,
      List.map_cons, List.flatten_cons]
    have htrans_append : ∀ (u v : List Sym₁),
        transWord h (u ++ v) = transWord h u ++ transWord h v := by
      intro u v
      simp [transWord]
    rw [htrans_append]
    congr 1
    cases tok with
    | inl a =>
      rw [hFl a]
      have hmm : ((h a).map Sum.inl).map F' = (h a).map (fun b => [b]) := by
        rw [List.map_map]
        exact List.map_congr_left (fun b _ => hF'l b)
      show (((h a).map Sum.inl).map F').flatten = transWord h [a]
      rw [hmm, flatten_map_singleton]
      simp [transWord]
    | inr x =>
      rw [hFr x]
      show (([Sum.inr x] : List (Sym₂ ⊕ ℕ)).map F').flatten = transWord h (η x)
      rw [show (([Sum.inr x] : List (Sym₂ ⊕ ℕ)).map F').flatten = F' (Sum.inr x) from by
        simp]
      rw [hF'r x]
      exact hη x List.mem_cons_self

/-! ### The image grammar -/

variable (G : MCFG.{u1, v1} Sym₁) (h : Sym₁ → List Sym₂)

/-- Encoding of `G`'s nonterminals into the transported type. -/
private def encN : G.N → ULift.{v2} (Fin (Fintype.card G.N)) :=
  fun A => ⟨Fintype.equivFin G.N A⟩

/-- Decoding. -/
private def decN : ULift.{v2} (Fin (Fintype.card G.N)) → G.N :=
  fun A => (Fintype.equivFin G.N).symm A.down

private theorem decN_encN (A : G.N) : decN G (encN G A) = A := by
  simp [decN, encN]

private theorem encN_decN (A : ULift.{v2} (Fin (Fintype.card G.N))) :
    encN G (decN G A) = A := by
  simp [decN, encN]

/-- Transport one production along the substitution. -/
private def prodSub (p : MCFGProduction Sym₁ G.N G.ar) :
    MCFGProduction Sym₂ (ULift.{v2} (Fin (Fintype.card G.N)))
      (fun A => G.ar (decN G A)) where
  lhs := encN G p.lhs
  rhs := p.rhs.map (encN G)
  rhs_vars := p.rhs_vars
  lhs_strings := p.lhs_strings.map (strSub h)
  lhs_arity := by
    rw [List.length_map, p.lhs_arity, decN_encN]
  rhs_len := by
    rw [List.length_map, p.rhs_len]
  rhs_arities := by
    intro i
    have hi : (i : ℕ) < p.rhs.length := by
      simpa using i.isLt
    have hget : (p.rhs.map (encN G)).get i = encN G (p.rhs.get ⟨(i : ℕ), hi⟩) := by
      simp [List.get_eq_getElem]
    rw [hget, decN_encN]
    have := p.rhs_arities ⟨(i : ℕ), hi⟩
    simpa using this
  rhs_vars_nodup := p.rhs_vars_nodup
  lhs_indices_bounded := by
    intro s hs x hx
    obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
    exact p.lhs_indices_bounded s₀ hs₀ x (mem_inr_strSub hx)
  lhs_vars_nodup := by
    -- Generic transfer: substituting terminals preserves the variable
    -- sequence, for any variable-extractors that ignore terminals.  Stated
    -- with both extractors as variables so it unifies with the matcher
    -- constants of the structure fields regardless of elaboration site.
    have key : ∀ (f₂ : (Sym₂ ⊕ ℕ) → Option ℕ) (f₁ : (Sym₁ ⊕ ℕ) → Option ℕ),
        (∀ b, f₂ (Sum.inl b) = none) → (∀ x, f₂ (Sum.inr x) = some x) →
        (∀ a, f₁ (Sum.inl a) = none) → (∀ x, f₁ (Sum.inr x) = some x) →
        (p.lhs_strings.flatten.filterMap f₁).Nodup →
        ((p.lhs_strings.map (strSub h)).flatten.filterMap f₂).Nodup := by
      intro f₂ f₁ hf₂l hf₂r hf₁l hf₁r hnd
      have heq : (p.lhs_strings.map (strSub h)).flatten.filterMap f₂ =
          p.lhs_strings.flatten.filterMap f₁ := by
        induction p.lhs_strings with
        | nil => rfl
        | cons s rest ih =>
          rw [List.map_cons, List.flatten_cons, List.flatten_cons,
            List.filterMap_append, List.filterMap_append, ih]
          congr 1
          exact strSub_filterMap h f₁ f₂ hf₁l hf₁r hf₂l hf₂r s
      rw [heq]
      exact hnd
    exact key _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      p.lhs_vars_nodup

/-- **The image grammar**: substitute `h` into every production of `G`. -/
noncomputable def MCFG.homImage : MCFG.{u2, v2} Sym₂ where
  N := ULift.{v2} (Fin (Fintype.card G.N))
  ar := fun A => G.ar (decN G A)
  ar_pos := fun A => G.ar_pos (decN G A)
  S := encN G G.S
  start_arity := by rw [decN_encN]; exact G.start_arity
  productions := G.productions.map (prodSub G h)

theorem homImage_dimension_le : (G.homImage h).dimension ≤ G.dimension :=
  MCFG.dimension_le_of_forall _ _ (fun A => G.ar_le_dimension (decN G A))

/-! ### Transport: G-derivations map to image derivations -/

theorem homImage_generates_of (A : G.N) (ss : List (List Sym₁))
    (hgen : G.Generates A ss) :
    (G.homImage h).Generates (encN G A) (ss.map (transWord h)) := by
  induction hgen with
  | prod p hp η rhs_gen ih =>
    have hq : prodSub G h p ∈ (G.homImage h).productions :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    -- The image substitution.
    set η' : ℕ → List Sym₂ := fun x => transWord h (η x) with hη'_def
    -- Child derivations.
    have hrhs : ∀ (i : Fin ((prodSub G h p).rhs).length),
        (G.homImage h).Generates
          (((prodSub G h p).rhs).get i)
          ((((prodSub G h p).rhs_vars).get
            (i.cast (prodSub G h p).rhs_len.symm)).map η') := by
      intro i
      have hi : (i : ℕ) < p.rhs.length := by
        have := i.isLt
        simpa [prodSub] using this
      have hget_rhs : ((prodSub G h p).rhs).get i =
          encN G (p.rhs.get ⟨(i : ℕ), hi⟩) := by
        simp [prodSub, List.get_eq_getElem]
      have hget_vars : ((prodSub G h p).rhs_vars).get
          (i.cast (prodSub G h p).rhs_len.symm) =
          p.rhs_vars.get ((⟨(i : ℕ), hi⟩ : Fin p.rhs.length).cast p.rhs_len.symm) := by
        simp [prodSub, List.get_eq_getElem]
      rw [hget_rhs, hget_vars]
      have hmap : (p.rhs_vars.get ((⟨(i : ℕ), hi⟩ : Fin p.rhs.length).cast
          p.rhs_len.symm)).map η' =
          ((p.rhs_vars.get ((⟨(i : ℕ), hi⟩ : Fin p.rhs.length).cast
            p.rhs_len.symm)).map η).map (transWord h) := by
        rw [List.map_map]
        rfl
      rw [hmap]
      exact ih ⟨(i : ℕ), hi⟩
    have hgen' := MCFG.Generates.prod (G := G.homImage h)
      (prodSub G h p) hq η' hrhs
    -- Identify the output tuples.
    convert hgen' using 1
    show (p.lhs_strings.map _).map (transWord h) =
      ((prodSub G h p).lhs_strings).map _
    rw [show ((prodSub G h p).lhs_strings) = p.lhs_strings.map (strSub h) from rfl,
      List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro s _
    show transWord h ((s.map _).flatten) = ((strSub h s).map _).flatten
    exact (strSub_expand h η η' _ _ (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) s (fun x _ => rfl)).symm

/-! ### Reflection: image derivations come from G-derivations -/

theorem generates_of_homImage (A' : (G.homImage h).N) (ss' : List (List Sym₂))
    (hgen : (G.homImage h).Generates A' ss') :
    ∃ ss : List (List Sym₁),
      G.Generates (decN G A') ss ∧ ss' = ss.map (transWord h) := by
  induction hgen with
  | prod q hq η' rhs_gen ih =>
    -- Recover the original production.
    rw [show (G.homImage h).productions = G.productions.map (prodSub G h) from rfl]
      at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    -- Choose G-side child tuples from the inductive hypothesis.
    choose ssF hssF_gen hssF_eq using ih
    -- Convenience: index bridging between (prodSub p).rhs and p.rhs.
    have hlen_eq : ((prodSub G h p).rhs).length = p.rhs.length := by
      simp [prodSub]
    -- The reconstructed substitution: for a variable x owned by component j
    -- of child i, return component j of the chosen G-side child tuple.
    set η : ℕ → List Sym₁ := fun x =>
      if hx : ∃ i : Fin ((prodSub G h p).rhs).length,
          x ∈ ((prodSub G h p).rhs_vars).get (i.cast (prodSub G h p).rhs_len.symm)
        then (ssF hx.choose).getD
          ((((prodSub G h p).rhs_vars).get
            (hx.choose.cast (prodSub G h p).rhs_len.symm)).idxOf x) []
        else [] with hη_def
    -- Variables lists are pairwise disjoint and duplicate-free.
    have hvars_nodup : ∀ (i : Fin ((prodSub G h p).rhs).length),
        (((prodSub G h p).rhs_vars).get
          (i.cast (prodSub G h p).rhs_len.symm)).Nodup := by
      intro i
      have := (prodSub G h p).rhs_vars_nodup
      rw [List.nodup_flatten] at this
      exact this.1 _ (List.get_mem _ _)
    have hvars_disj : ∀ (i i' : Fin ((prodSub G h p).rhs).length), i ≠ i' →
        ∀ x, x ∈ ((prodSub G h p).rhs_vars).get
            (i.cast (prodSub G h p).rhs_len.symm) →
          x ∉ ((prodSub G h p).rhs_vars).get
            (i'.cast (prodSub G h p).rhs_len.symm) := by
      intro i i' hne x hx hx'
      have hnd := (prodSub G h p).rhs_vars_nodup
      rw [List.nodup_flatten] at hnd
      have hpw := hnd.2
      rw [List.pairwise_iff_getElem] at hpw
      have hlen_vars : ((prodSub G h p).rhs_vars).length =
          ((prodSub G h p).rhs).length := (prodSub G h p).rhs_len
      have hi : (i : ℕ) < ((prodSub G h p).rhs_vars).length := by
        rw [hlen_vars]; exact i.isLt
      have hi' : (i' : ℕ) < ((prodSub G h p).rhs_vars).length := by
        rw [hlen_vars]; exact i'.isLt
      have hne_val : (i : ℕ) ≠ (i' : ℕ) := fun hcon => hne (Fin.ext hcon)
      have hgi : ((prodSub G h p).rhs_vars).get
          (i.cast (prodSub G h p).rhs_len.symm) =
          ((prodSub G h p).rhs_vars)[(i : ℕ)] := by
        simp [List.get_eq_getElem]
      have hgi' : ((prodSub G h p).rhs_vars).get
          (i'.cast (prodSub G h p).rhs_len.symm) =
          ((prodSub G h p).rhs_vars)[(i' : ℕ)] := by
        simp [List.get_eq_getElem]
      rw [hgi] at hx
      rw [hgi'] at hx'
      rcases Nat.lt_or_ge (i : ℕ) (i' : ℕ) with hlt | hge
      · exact (hpw (i : ℕ) (i' : ℕ) hi hi' hlt) hx hx'
      · have hlt' : (i' : ℕ) < (i : ℕ) := lt_of_le_of_ne hge (Ne.symm hne_val)
        exact (hpw (i' : ℕ) (i : ℕ) hi' hi hlt') hx' hx
    -- Lengths of chosen tuples match variable lists.
    have hssF_len : ∀ (i : Fin ((prodSub G h p).rhs).length),
        (ssF i).length = (((prodSub G h p).rhs_vars).get
          (i.cast (prodSub G h p).rhs_len.symm)).length := by
      intro i
      have := hssF_eq i
      have hlen := congrArg List.length this
      rw [List.length_map, List.length_map] at hlen
      exact hlen.symm
    -- η reproduces each chosen child tuple.
    have hη_tuple : ∀ (i : Fin ((prodSub G h p).rhs).length),
        (((prodSub G h p).rhs_vars).get
          (i.cast (prodSub G h p).rhs_len.symm)).map η = ssF i := by
      intro i
      apply List.ext_getElem
      · rw [List.length_map, hssF_len i]
      · intro j h1 h2
        simp only [List.getElem_map]
        set vs := ((prodSub G h p).rhs_vars).get
          (i.cast (prodSub G h p).rhs_len.symm) with hvs_def
        have hj : j < vs.length := by
          simpa using h1
        have hmem : vs[j] ∈ vs := List.getElem_mem _
        have hex : ∃ i' : Fin ((prodSub G h p).rhs).length,
            vs[j] ∈ ((prodSub G h p).rhs_vars).get
              (i'.cast (prodSub G h p).rhs_len.symm) := ⟨i, hmem⟩
        -- Evaluate η at this variable, in a clean context.
        have hev : η vs[j] = (ssF hex.choose).getD
            ((((prodSub G h p).rhs_vars).get
              (hex.choose.cast (prodSub G h p).rhs_len.symm)).idxOf vs[j]) [] := by
          simp only [hη_def]
          rw [dif_pos hex]
        -- The chosen index equals i, by disjointness.
        have hchoose : hex.choose = i := by
          by_contra hne
          exact hvars_disj hex.choose i hne vs[j] hex.choose_spec hmem
        have hidx : (((prodSub G h p).rhs_vars).get
            (hex.choose.cast (prodSub G h p).rhs_len.symm)).idxOf vs[j] = j := by
          rw [hchoose]
          exact List.idxOf_getElem (hvars_nodup i) j hj
        rw [hev, hidx, hchoose]
        exact List.getD_eq_getElem (ssF i) [] h2
    -- η' agrees with the transport of η on every variable that occurs.
    have hη'_trans : ∀ (i : Fin ((prodSub G h p).rhs).length) (x : ℕ),
        x ∈ ((prodSub G h p).rhs_vars).get
          (i.cast (prodSub G h p).rhs_len.symm) →
        η' x = transWord h (η x) := by
      intro i x hx
      set vs := ((prodSub G h p).rhs_vars).get
        (i.cast (prodSub G h p).rhs_len.symm) with hvs_def
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hjs : j < (ssF i).length := by
        rw [hssF_len i]; exact hj
      -- Pointwise reading of the tuple identities, via `getElem?`.
      have hopt := congrArg (fun l => l[j]?) (hssF_eq i)
      simp only [List.getElem?_map] at hopt
      rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjs] at hopt
      have hpoint : η' vs[j] = transWord h ((ssF i)[j]) := by
        simpa using hopt
      have hopt2 := congrArg (fun l => l[j]?) (hη_tuple i)
      simp only [List.getElem?_map] at hopt2
      rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjs] at hopt2
      have hpoint2 : η vs[j] = (ssF i)[j] := by
        simpa using hopt2
      rw [hpoint, hpoint2]
    -- Assemble the G-side derivation.
    have hrhs_G : ∀ (i : Fin p.rhs.length),
        G.Generates (p.rhs.get i)
          ((p.rhs_vars.get (i.cast p.rhs_len.symm)).map η) := by
      intro i
      have hi : (i : ℕ) < ((prodSub G h p).rhs).length := by
        rw [hlen_eq]; exact i.isLt
      set i' : Fin ((prodSub G h p).rhs).length := ⟨(i : ℕ), hi⟩ with hi'_def
      have hvars_eq : ((prodSub G h p).rhs_vars).get
          (i'.cast (prodSub G h p).rhs_len.symm) =
          p.rhs_vars.get (i.cast p.rhs_len.symm) := by
        simp only [prodSub, List.get_eq_getElem]
        rfl
      have hgen_i := hssF_gen i'
      have hdec : decN G (((prodSub G h p).rhs).get i') = p.rhs.get i := by
        have henc : ((prodSub G h p).rhs).get i' = encN G (p.rhs.get i) := by
          simp only [prodSub, List.get_eq_getElem, List.getElem_map]
          rfl
        rw [henc, decN_encN]
      rw [hdec] at hgen_i
      have htup := hη_tuple i'
      rw [hvars_eq] at htup
      rw [htup]
      exact hgen_i
    have hgen_G := MCFG.Generates.prod (G := G) p hp η hrhs_G
    refine ⟨p.lhs_strings.map (fun s =>
        (s.map (fun c => match c with
          | Sum.inl a => [a]
          | Sum.inr x => η x)).flatten), ?_, ?_⟩
    · rw [show decN G ((prodSub G h p).lhs) = p.lhs from by
        rw [show (prodSub G h p).lhs = encN G p.lhs from rfl, decN_encN]]
      exact hgen_G
    · -- Output identification.
      show ((prodSub G h p).lhs_strings).map _ =
        (p.lhs_strings.map _).map (transWord h)
      rw [show ((prodSub G h p).lhs_strings) = p.lhs_strings.map (strSub h) from rfl,
        List.map_map, List.map_map]
      refine List.map_congr_left ?_
      intro s hs
      show ((strSub h s).map _).flatten = transWord h ((s.map _).flatten)
      refine strSub_expand h η η' _ _ (fun _ => rfl) (fun _ => rfl)
        (fun _ => rfl) (fun _ => rfl) s ?_
      intro x hx
      -- Every variable occurring in a production string is bound on the rhs.
      have hbound := p.lhs_indices_bounded s hs x hx
      rw [List.mem_flatten] at hbound
      obtain ⟨vl, hvl, hxvl⟩ := hbound
      obtain ⟨jv, hjv⟩ := List.get_of_mem hvl
      have hjv' : (jv : ℕ) < ((prodSub G h p).rhs).length := by
        have h1 := jv.isLt
        have h2 := p.rhs_len
        omega
      refine hη'_trans ⟨(jv : ℕ), hjv'⟩ x ?_
      have hget_vl : p.rhs_vars[(jv : ℕ)]'jv.isLt = vl := by
        rw [← hjv]
        exact List.get_eq_getElem.symm
      show x ∈ p.rhs_vars[(jv : ℕ)]'jv.isLt
      rw [hget_vl]
      exact hxvl

/-! ### The closure theorem -/

/-- **MCFLs are closed under word-valued homomorphic image.**  Formerly the
axiom `mcfg_homomorphic_image` (attributed to Seki et al. 1991); now a
theorem about the explicit image grammar above.  The name and statement are
kept so downstream proofs are unchanged. -/
theorem mcfg_homomorphic_image {Sym₁ : Type u1} {Sym₂ : Type u2}
    (G : MCFG.{u1, v1} Sym₁) (h : Sym₁ → List Sym₂) :
    ∃ G' : MCFG.{u2, v2} Sym₂, G'.dimension ≤ G.dimension ∧
      G'.Language = { w : List Sym₂ | ∃ w' ∈ G.Language, w = (w'.map h).flatten } := by
  refine ⟨G.homImage h, homImage_dimension_le G h, ?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨ss, hgen, heq⟩ := generates_of_homImage G h (G.homImage h).S [w] hw
    -- The tuple is a singleton.
    have hlen : ss.length = 1 := by
      have := congrArg List.length heq
      simpa using this.symm
    obtain ⟨w', rfl⟩ := List.length_eq_one_iff.mp hlen
    have hw' : w = transWord h w' := by
      simpa using heq
    refine ⟨w', ?_, hw'⟩
    have hdec : decN G (G.homImage h).S = G.S := by
      rw [show (G.homImage h).S = encN G G.S from rfl, decN_encN]
    rw [hdec] at hgen
    exact hgen
  · rintro ⟨w', hw', rfl⟩
    have := homImage_generates_of G h G.S [w'] hw'
    simpa [MCFG.Language, transWord] using this

end HomImage
