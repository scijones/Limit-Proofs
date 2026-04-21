/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold

/-!
# Multiple Context-Free Grammars (MCFGs)

Definitions 6.1â€“6.3 from the paper: MCFGs, derivations, dimension, and MCFLs.
-/

set_option autoImplicit false

universe u_sym u_nt

/-- An MCFG production.
(Part of Definition 6.1) -/
structure MCFGProduction (Sym : Type*) (N : Type*) (ar : N â†’ â„•) where
  /-- The left-hand side nonterminal. -/
  lhs : N
  /-- The right-hand side nonterminals. -/
  rhs : List N
  /-- Variable indices: for each RHS nonterminal Báµ¢, a list of variable
      names (represented as â„•). -/
  rhs_vars : List (List â„•)
  /-- The LHS component strings, each being a list of terminal symbols or
      variable references. -/
  lhs_strings : List (List (Sym âŠ• â„•))
  /-- The number of LHS strings matches the arity of the LHS nonterminal. -/
  lhs_arity : lhs_strings.length = ar lhs
  /-- The number of variable lists matches the number of RHS nonterminals. -/
  rhs_len : rhs_vars.length = rhs.length
  /-- Each variable list has length matching the arity of the corresponding
      RHS nonterminal. -/
  rhs_arities : âˆ€ (i : Fin rhs.length),
    (rhs_vars.get (i.cast rhs_len.symm)).length = ar (rhs.get i)

/-- A multiple context-free grammar.
(Definition 6.1) -/
structure MCFG (Sym : Type*) where
  /-- Nonterminal symbols. -/
  N : Type*
  [instFintypeN : Fintype N]
  [instDecEqN : DecidableEq N]
  /-- Arity function: number of string components each nonterminal generates. -/
  ar : N â†’ â„•
  /-- Every nonterminal has positive arity (Definition 6.1). -/
  ar_pos : âˆ€ A : N, 0 < ar A
  /-- The start symbol. -/
  S : N
  /-- The start symbol has arity 1 (generates a single string). -/
  start_arity : ar S = 1
  /-- The productions. -/
  productions : List (MCFGProduction Sym N ar)

attribute [instance] MCFG.instFintypeN MCFG.instDecEqN

/-- Derivation in an MCFG: a nonterminal A generates a tuple of strings.
(Definition 6.2) -/
inductive MCFG.Generates {Sym : Type*} (G : MCFG Sym) :
    G.N â†’ List (List Sym) â†’ Prop where
  | prod (p : MCFGProduction Sym G.N G.ar)
      (hp : p âˆˆ G.productions)
      (Î· : â„• â†’ List Sym)
      (rhs_generated : âˆ€ (i : Fin p.rhs.length),
        G.Generates (p.rhs.get i)
          ((p.rhs_vars.get (i.cast p.rhs_len.symm)).map Î·))
      : G.Generates p.lhs
          (p.lhs_strings.map (fun s =>
            (s.map (fun c => match c with
              | .inl a => [a]
              | .inr x => Î· x)).flatten))

/-- The language of an MCFG: all strings w such that S â‡’* (w).
(Definition 6.2) -/
def MCFG.Language {Sym : Type*} (G : MCFG Sym) : Set (List Sym) :=
  { w | G.Generates G.S [w] }

/-- The dimension of an MCFG is the maximum arity of its nonterminals.
(Definition 6.3) -/
noncomputable def MCFG.dimension {Sym : Type*} (G : MCFG Sym) : â„• := by
  exact (Finset.univ : Finset G.N).toList.map G.ar |>.foldl Nat.max 0

/-- Helper: init â‰¤ foldl Nat.max init L for any list L. -/
private theorem List.foldl_max_init_le (L : List â„•) (init : â„•) :
    init â‰¤ L.foldl Nat.max init := by
  induction L generalizing init with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    simp only [List.foldl_cons]
    calc init â‰¤ Nat.max init y := Nat.le_max_left init y
      _ â‰¤ ys.foldl Nat.max (Nat.max init y) := ih (Nat.max init y)

/-- Helper: every element of a list is â‰¤ foldl Nat.max of that list. -/
private theorem List.le_foldl_max (L : List â„•) (init : â„•) (x : â„•) (hx : x âˆˆ L) :
    x â‰¤ L.foldl Nat.max init := by
  induction L generalizing init with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h
    Â· calc x â‰¤ Nat.max init x := Nat.le_max_right init x
        _ â‰¤ ys.foldl Nat.max (Nat.max init x) := List.foldl_max_init_le ys (Nat.max init x)
    Â· exact ih (Nat.max init y) h

/-- Helper: foldl Nat.max init L â‰¤ bound when init â‰¤ bound and all elements â‰¤ bound. -/
private theorem List.foldl_max_le (L : List â„•) (init bound : â„•)
    (hinit : init â‰¤ bound) (hall : âˆ€ x âˆˆ L, x â‰¤ bound) :
    L.foldl Nat.max init â‰¤ bound := by
  induction L generalizing init with
  | nil => exact hinit
  | cons y ys ih =>
    simp only [List.foldl_cons]
    apply ih (Nat.max init y) (Nat.max_le.mpr âŸ¨hinit, hall y (List.mem_cons.mpr (Or.inl rfl))âŸ©)
    intro x hx
    exact hall x (List.mem_cons.mpr (Or.inr hx))

/-- Every nonterminal's arity is bounded by the dimension. -/
theorem MCFG.ar_le_dimension {Sym : Type*} (G : MCFG Sym) (A : G.N) :
    G.ar A â‰¤ G.dimension := by
  unfold MCFG.dimension
  have hmem : G.ar A âˆˆ (Finset.univ : Finset G.N).toList.map G.ar :=
    List.mem_map.mpr âŸ¨A, Finset.mem_toList.mpr (Finset.mem_univ A), rflâŸ©
  exact List.le_foldl_max _ 0 _ hmem

/-- The dimension is bounded by any uniform upper bound on arities. -/
theorem MCFG.dimension_le_of_forall {Sym : Type*} (G : MCFG Sym) (bound : â„•)
    (h : âˆ€ A : G.N, G.ar A â‰¤ bound) : G.dimension â‰¤ bound := by
  unfold MCFG.dimension
  apply List.foldl_max_le
  Â· exact Nat.zero_le bound
  Â· intro x hx
    obtain âŸ¨A, _, rflâŸ© := List.mem_map.mp hx
    exact h A

/-- A language L is a d-MCFL if it equals the language of some d-MCFG.
(Definition 6.3) -/
def IsMCFL.{u_nt'} {Sym : Type u_sym} (L : Set (List Sym)) (d : â„•) : Prop :=
  âˆƒ G : MCFG.{u_sym, u_nt'} Sym, G.dimension â‰¤ d âˆ§ G.Language = L

/-! ## Empty MCFG -/

/-- An MCFG with no productions, generating the empty language. -/
noncomputable def MCFG.empty (Sym : Type*) (k : â„•) : MCFG Sym where
  N := Unit
  ar := fun _ => 1
  ar_pos := fun _ => Nat.one_pos
  S := ()
  start_arity := rfl
  productions := []

/-- A lemma extracting production membership from Generates. -/
theorem MCFG.Generates.mem_productions {Sym : Type*} {G : MCFG Sym} {A : G.N}
    {ss : List (List Sym)}
    (h : G.Generates A ss) : âˆƒ p âˆˆ G.productions, p.lhs = A := by
  induction h with
  | prod p hp _ _ => exact âŸ¨p, hp, rflâŸ©

/-- The empty MCFG generates the empty language. -/
theorem MCFG.empty_language (Sym : Type*) (k : â„•) :
    (MCFG.empty Sym k).Language = âˆ… := by
  ext w
  simp only [Language, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain âŸ¨p, hp, _âŸ© := h.mem_productions
  simp only [empty] at hp
  simp only [List.mem_nil_iff] at hp

/-- The empty MCFG has dimension 1 â‰¤ k+1 for any k. -/
theorem MCFG.empty_dimension_le (Sym : Type*) (k : â„•) :
    (MCFG.empty Sym k).dimension â‰¤ k + 1 := by
  apply MCFG.dimension_le_of_forall
  intro A
  simp only [empty]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)

/-- An MCFG with no productions at any universe level. -/
noncomputable def MCFG.emptyAt (Sym : Type*) (N : Type*) [Fintype N] [DecidableEq N] [Nonempty N] : MCFG Sym where
  N := N
  ar := fun _ => 1
  ar_pos := fun _ => Nat.one_pos
  S := Classical.arbitrary N
  start_arity := rfl
  productions := []

/-- The emptyAt MCFG generates the empty language. -/
theorem MCFG.emptyAt_language (Sym : Type*) (N : Type*) [Fintype N] [DecidableEq N] [Nonempty N] :
    (MCFG.emptyAt Sym N).Language = âˆ… := by
  ext w
  simp only [Language, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain âŸ¨p, hp, _âŸ© := h.mem_productions
  simp only [emptyAt, List.mem_nil_iff] at hp

/-- The emptyAt MCFG has dimension 1 â‰¤ any bound. -/
theorem MCFG.emptyAt_dimension_le (Sym : Type*) (N : Type*) [Fintype N] [DecidableEq N] [Nonempty N] (k : â„•) :
    (MCFG.emptyAt Sym N).dimension â‰¤ k + 1 := by
  apply MCFG.dimension_le_of_forall
  intro A
  simp only [emptyAt]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
