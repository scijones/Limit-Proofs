/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold

/-!
# Multiple Context-Free Grammars (MCFGs)

Definitions 6.1–6.3 from the paper: MCFGs, derivations, dimension, and MCFLs.
-/

set_option autoImplicit false

universe u_sym u_nt

/-- An MCFG production.
(Part of Definition 6.1) -/
structure MCFGProduction (Sym : Type*) (N : Type*) (ar : N → ℕ) where
  /-- The left-hand side nonterminal. -/
  lhs : N
  /-- The right-hand side nonterminals. -/
  rhs : List N
  /-- Variable indices: for each RHS nonterminal Bᵢ, a list of variable
      names (represented as ℕ). -/
  rhs_vars : List (List ℕ)
  /-- The LHS component strings, each being a list of terminal symbols or
      variable references. -/
  lhs_strings : List (List (Sym ⊕ ℕ))
  /-- The number of LHS strings matches the arity of the LHS nonterminal. -/
  lhs_arity : lhs_strings.length = ar lhs
  /-- The number of variable lists matches the number of RHS nonterminals. -/
  rhs_len : rhs_vars.length = rhs.length
  /-- Each variable list has length matching the arity of the corresponding
      RHS nonterminal. -/
  rhs_arities : ∀ (i : Fin rhs.length),
    (rhs_vars.get (i.cast rhs_len.symm)).length = ar (rhs.get i)

/-- A multiple context-free grammar.
(Definition 6.1) -/
structure MCFG (Sym : Type*) where
  /-- Nonterminal symbols. -/
  N : Type*
  [instFintypeN : Fintype N]
  [instDecEqN : DecidableEq N]
  /-- Arity function: number of string components each nonterminal generates. -/
  ar : N → ℕ
  /-- Every nonterminal has positive arity (Definition 6.1). -/
  ar_pos : ∀ A : N, 0 < ar A
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
    G.N → List (List Sym) → Prop where
  | prod (p : MCFGProduction Sym G.N G.ar)
      (hp : p ∈ G.productions)
      (η : ℕ → List Sym)
      (rhs_generated : ∀ (i : Fin p.rhs.length),
        G.Generates (p.rhs.get i)
          ((p.rhs_vars.get (i.cast p.rhs_len.symm)).map η))
      : G.Generates p.lhs
          (p.lhs_strings.map (fun s =>
            (s.map (fun c => match c with
              | .inl a => [a]
              | .inr x => η x)).flatten))

/-- The language of an MCFG: all strings w such that S ⇒* (w).
(Definition 6.2) -/
def MCFG.Language {Sym : Type*} (G : MCFG Sym) : Set (List Sym) :=
  { w | G.Generates G.S [w] }

/-- The dimension of an MCFG is the maximum arity of its nonterminals.
(Definition 6.3) -/
noncomputable def MCFG.dimension {Sym : Type*} (G : MCFG Sym) : ℕ := by
  exact (Finset.univ : Finset G.N).toList.map G.ar |>.foldl Nat.max 0

/-- Helper: init ≤ foldl Nat.max init L for any list L. -/
private theorem List.foldl_max_init_le (L : List ℕ) (init : ℕ) :
    init ≤ L.foldl Nat.max init := by
  induction L generalizing init with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    simp only [List.foldl_cons]
    calc init ≤ Nat.max init y := Nat.le_max_left init y
      _ ≤ ys.foldl Nat.max (Nat.max init y) := ih (Nat.max init y)

/-- Helper: every element of a list is ≤ foldl Nat.max of that list. -/
private theorem List.le_foldl_max (L : List ℕ) (init : ℕ) (x : ℕ) (hx : x ∈ L) :
    x ≤ L.foldl Nat.max init := by
  induction L generalizing init with
  | nil => contradiction
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · calc x ≤ Nat.max init x := Nat.le_max_right init x
        _ ≤ ys.foldl Nat.max (Nat.max init x) := List.foldl_max_init_le ys (Nat.max init x)
    · exact ih (Nat.max init y) h

/-- Helper: foldl Nat.max init L ≤ bound when init ≤ bound and all elements ≤ bound. -/
private theorem List.foldl_max_le (L : List ℕ) (init bound : ℕ)
    (hinit : init ≤ bound) (hall : ∀ x ∈ L, x ≤ bound) :
    L.foldl Nat.max init ≤ bound := by
  induction L generalizing init with
  | nil => exact hinit
  | cons y ys ih =>
    simp only [List.foldl_cons]
    apply ih (Nat.max init y) (Nat.max_le.mpr ⟨hinit, hall y (List.mem_cons.mpr (Or.inl rfl))⟩)
    intro x hx
    exact hall x (List.mem_cons.mpr (Or.inr hx))

/-- Every nonterminal's arity is bounded by the dimension. -/
theorem MCFG.ar_le_dimension {Sym : Type*} (G : MCFG Sym) (A : G.N) :
    G.ar A ≤ G.dimension := by
  unfold MCFG.dimension
  have hmem : G.ar A ∈ (Finset.univ : Finset G.N).toList.map G.ar :=
    List.mem_map.mpr ⟨A, Finset.mem_toList.mpr (Finset.mem_univ A), rfl⟩
  exact List.le_foldl_max _ 0 _ hmem

/-- The dimension is bounded by any uniform upper bound on arities. -/
theorem MCFG.dimension_le_of_forall {Sym : Type*} (G : MCFG Sym) (bound : ℕ)
    (h : ∀ A : G.N, G.ar A ≤ bound) : G.dimension ≤ bound := by
  unfold MCFG.dimension
  apply List.foldl_max_le
  · exact Nat.zero_le bound
  · intro x hx
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp hx
    exact h A

/-- A language L is a d-MCFL if it equals the language of some d-MCFG.
(Definition 6.3) -/
def IsMCFL.{u_nt'} {Sym : Type u_sym} (L : Set (List Sym)) (d : ℕ) : Prop :=
  ∃ G : MCFG.{u_sym, u_nt'} Sym, G.dimension ≤ d ∧ G.Language = L

/-! ## Empty MCFG -/

/-- An MCFG with no productions, generating the empty language. -/
noncomputable def MCFG.empty (Sym : Type*) (k : ℕ) : MCFG Sym where
  N := Unit
  ar := fun _ => 1
  ar_pos := fun _ => Nat.one_pos
  S := ()
  start_arity := rfl
  productions := []

/-- A lemma extracting production membership from Generates. -/
theorem MCFG.Generates.mem_productions {Sym : Type*} {G : MCFG Sym} {A : G.N}
    {ss : List (List Sym)}
    (h : G.Generates A ss) : ∃ p ∈ G.productions, p.lhs = A := by
  induction h with
  | prod p hp _ _ => exact ⟨p, hp, rfl⟩

/-- The empty MCFG generates the empty language. -/
theorem MCFG.empty_language (Sym : Type*) (k : ℕ) :
    (MCFG.empty Sym k).Language = ∅ := by
  ext w
  simp only [Language, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨p, hp, _⟩ := h.mem_productions
  simp only [empty] at hp
  simp only [List.mem_nil_iff] at hp

/-- The empty MCFG has dimension 1 ≤ k+1 for any k. -/
theorem MCFG.empty_dimension_le (Sym : Type*) (k : ℕ) :
    (MCFG.empty Sym k).dimension ≤ k + 1 := by
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
    (MCFG.emptyAt Sym N).Language = ∅ := by
  ext w
  simp only [Language, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  obtain ⟨p, hp, _⟩ := h.mem_productions
  simp only [emptyAt, List.mem_nil_iff] at hp

/-- The emptyAt MCFG has dimension 1 ≤ any bound. -/
theorem MCFG.emptyAt_dimension_le (Sym : Type*) (N : Type*) [Fintype N] [DecidableEq N] [Nonempty N] (k : ℕ) :
    (MCFG.emptyAt Sym N).dimension ≤ k + 1 := by
  apply MCFG.dimension_le_of_forall
  intro A
  simp only [emptyAt]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)
