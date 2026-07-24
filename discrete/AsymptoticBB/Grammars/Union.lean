import AsymptoticBB.Grammars.MCFG
import Mathlib

/-!
# Finite union of multiple context-free languages

This file proves the standard existential closure of a fixed positive MCFG tier
under finite union.  The construction does not preserve or select a derivation;
it only produces a grammar whose extensional language is the union.
-/

set_option autoImplicit false

universe u v

/-- A finite union of languages in one positive MCFG tier remains in that tier. -/
theorem mcfg_finite_union {Sym : Type u} {ι : Type v} [Fintype ι]
    (Ls : ι → Set (List Sym)) (d : ℕ) (hd : 1 ≤ d)
    (hLs : ∀ i, IsMCFL.{u, 0} (Ls i) d) :
    IsMCFL.{u, 0} (⋃ i, Ls i) d := by
  -- Obtain MCFGs for each language
  have hLs' : ∀ i, ∃ G : MCFG.{u, 0} Sym, G.dimension ≤ d ∧ G.Language = Ls i := hLs
  choose G hGdim hGlang using hLs'
  -- Define combined nonterminal type: Option (Σ i : Fin n, (G (equiv i)).N) in Type 0
  -- where n = Fintype.card ι and equiv : Fin n ≃ ι
  let n := Fintype.card ι
  let equiv : Fin n ≃ ι := (Fintype.equivFin ι).symm
  let sigmaN : Type 0 := Σ (i : Fin n), (G (equiv i)).N
  letI fintype_sigmaN : Fintype sigmaN := by
    apply Fintype.ofFinite
  letI decEq_sigmaN : DecidableEq sigmaN := Classical.decEq _
  let N' : Type 0 := Option sigmaN
  letI fintype_N' : Fintype N' := by
    dsimp [N']
    exact instFintypeOption
  haveI decEq_N' : DecidableEq N' := Classical.decEq _
  -- Define arity for combined grammar
  let ar' : N' → ℕ := fun n =>
    match n with
    | none => 1
    | some ⟨i, A⟩ => (G (equiv i)).ar A
  -- Check ar' is positive
  have ar'_pos : ∀ A : N', 0 < ar' A := by
    intro n
    cases n with
    | none => exact Nat.one_pos
    | some p => exact (G (equiv p.1)).ar_pos p.2
  -- Start symbol
  let S' : N' := none
  -- Start arity
  have start_arity : ar' S' = 1 := rfl
  -- Embedding function for nonterminals
  let emb : ∀ i : Fin n, (G (equiv i)).N → N' := fun i A => some ⟨i, A⟩
  -- Build the list of new start productions
  -- Each: none → some ⟨i, (G i).S⟩, passing through the output
  by_cases hempty : IsEmpty ι
  · -- ι is empty: union is empty
    have hunion : (⋃ i, Ls i) = ∅ := Set.iUnion_eq_empty.mpr (fun i => False.elim (hempty.elim i))
    rw [hunion]
    exact ⟨MCFG.empty Sym d, by
      have := MCFG.empty_dimension_le Sym 0
      exact Nat.le_trans this (Nat.add_le_add_right hd 0), MCFG.empty_language Sym d⟩
  · -- ι is nonempty
    haveI : Nonempty ι := by
      simp only [not_isEmpty_iff] at hempty
      exact hempty
    let startProds : List (MCFGProduction Sym N' ar') :=
    List.finRange n |>.map (fun j =>
      { lhs := S'
        rhs := [emb j (G (equiv j)).S]
        rhs_vars := [[0]]
        lhs_strings := [[Sum.inr 0]]  -- Pass through variable 0's output
        lhs_arity := rfl  -- ar' none = 1
        rhs_len := by simp [emb]
        rhs_arities := by
          intro k
          simp only [List.length_singleton] at k
          fin_cases k
          simp [ar', emb]; exact (G (equiv j)).start_arity.symm
        rhs_vars_nodup := by decide
        lhs_indices_bounded := by
          intro s hs x hx
          simp only [List.mem_singleton] at hs
          subst hs
          simp only [List.flatten] at hx ⊢
          simp at hx
          subst hx
          simp
        lhs_vars_nodup := by simp})
    -- Embed original productions from each G i
    let origProds : List (MCFGProduction Sym N' ar') :=
      List.finRange n |>.flatMap (fun j =>
        (G (equiv j)).productions.map (fun p =>
          { lhs := emb j p.lhs
            rhs := p.rhs.map (emb j)
            rhs_vars := p.rhs_vars
            lhs_strings := p.lhs_strings
            lhs_arity := p.lhs_arity
            rhs_len := by simp [p.rhs_len]
            rhs_arities := by
              intro k
              have klen : k.val < p.rhs.length := by simpa [List.length_map] using k.is_lt
              have hmap : (p.rhs.map (emb j)).get k = emb j (p.rhs.get ⟨k.val, klen⟩) := by
                simp [emb]
              simp only [ar', hmap]
              exact p.rhs_arities ⟨k.val, klen⟩
            rhs_vars_nodup := p.rhs_vars_nodup
            lhs_indices_bounded := p.lhs_indices_bounded
            lhs_vars_nodup := p.lhs_vars_nodup }))
    -- Combined productions
    let prods : List (MCFGProduction Sym N' ar') := startProds ++ origProds
    let G' : MCFG.{u, 0} Sym := {
      N := N'
      ar := ar'
      ar_pos := ar'_pos
      S := S'
      start_arity := start_arity
      productions := prods
    }
    -- Show G'.dimension ≤ d
    have dim_le : G'.dimension ≤ d := by
      apply MCFG.dimension_le_of_forall
      intro A
      show ar' A ≤ d
      rcases A with none | ⟨i, A₀⟩
      · exact hd
      · simp only [ar']; exact le_trans (MCFG.ar_le_dimension (G (equiv i)) A₀) (hGdim (equiv i))
    refine ⟨G', dim_le, ?_⟩
    ext w
    simp only [MCFG.Language, Set.mem_iUnion]
    constructor
    · intro hGen
      simp only [Set.mem_setOf_eq] at hGen
      -- First prove: if G'.Generates (emb j A) strs, then (G (equiv j)).Generates A strs
      have embod_converse : ∀ (j : Fin n) (A : (G (equiv j)).N) (strs : List (List Sym)),
          G'.Generates (emb j A) strs → (G (equiv j)).Generates A strs := by
        have embod_converse_aux : ∀ (B : N') (strs : List (List Sym)) (t : G'.Generates B strs),
            ∀ (j : Fin n) (A : (G (equiv j)).N), emb j A = B → (G (equiv j)).Generates A strs := by
          apply @MCFG.Generates.rec Sym G'
          intro p hp eta rhs_gen ih j A hBA
          -- Analyze if p is a start production or embedded
          simp only [G', prods, startProds, origProds] at hp
          rcases List.mem_append.mp hp with hp_start | hp_orig
          · -- Start production: lhs = S' = none, but emb j A = some ⟨j, A⟩
            simp only [List.mem_map] at hp_start
            obtain ⟨j', _, hj'⟩ := hp_start
            rw [hj'.symm] at hBA
            simp [emb] at hBA
          · -- Embedded production
            simp only [List.mem_flatMap, List.mem_map] at hp_orig
            obtain ⟨j', _, p', hp'_mem, hp_eq⟩ := hp_orig
            -- hp_eq : {lhs := emb j' p'.lhs, ...} = p
            -- p.lhs = emb j' p'.lhs = emb j A, so j' = j and p'.lhs = A
            have hp_lhs : p.lhs = emb j' p'.lhs := hp_eq.symm ▸ rfl
            have hlhs_eq : emb j' p'.lhs = emb j A := by rw [← hp_lhs]; exact hBA.symm
            simp only [emb] at hlhs_eq
            cases hlhs_eq with
            | refl =>
              -- Extract relationships between p and p'
              have hp_rhs : p.rhs = p'.rhs.map (emb j) := hp_eq.symm ▸ rfl
              have hp_rhs_vars : p.rhs_vars = p'.rhs_vars := hp_eq.symm ▸ rfl
              have h_rhs_len : p.rhs.length = p'.rhs.length := by rw [hp_rhs]; simp
              have h_rhs_vars_len : p.rhs_vars.length = p'.rhs_vars.length := by rw [hp_rhs_vars]
              -- For each i, p.rhs.get i = emb j (p'.rhs.get i)
              have rhs_get_eq : ∀ i : Fin p.rhs.length, p.rhs.get i = emb j (p'.rhs.get (i.cast h_rhs_len)) := by
                intro i
                simp [hp_rhs, List.getElem_map]
              -- For each i, p.rhs_vars.get i = p'.rhs_vars.get i
              have rhs_vars_eq : ∀ i : Fin p.rhs_vars.length, p.rhs_vars.get i = p'.rhs_vars.get (i.cast h_rhs_vars_len) := by
                intro i
                simp [hp_rhs_vars]
              -- Build the translated rhs_gen for G (equiv j)
              have rhs_gen' : ∀ (i : Fin p'.rhs.length),
                  (G (equiv j)).Generates (p'.rhs.get i) ((p'.rhs_vars.get (i.cast p'.rhs_len.symm)).map eta) := by
                intro i
                let i' := i.cast h_rhs_len.symm
                have h_cast_eq : i'.cast h_rhs_len = i := by simp [i']
                have h_rhs_get : p.rhs.get i' = emb j (p'.rhs.get i) := by
                  have := rhs_get_eq i'
                  rw [h_cast_eq] at this
                  exact this
                -- Need to convert variable lists: p.rhs_vars.get (i'.cast p.rhs_len.symm) = p'.rhs_vars.get (i.cast p'.rhs_len.symm)
                have h_var_eq : p.rhs_vars.get (i'.cast p.rhs_len.symm) = p'.rhs_vars.get (i.cast p'.rhs_len.symm) := by
                  rw [rhs_vars_eq]
                  apply congr_arg
                  apply Fin.ext
                  show ((i'.cast p.rhs_len.symm).val : ℕ) = (i.cast p'.rhs_len.symm).val
                  have h1 : i.val < p.rhs.length := by rw [h_rhs_len]; exact i.is_lt
                  have h2 : i.val < p.rhs_vars.length := by rw [p.rhs_len]; exact h1
                  have hi'_val : i'.val = i.val := by rfl
                  simp [i']
                exact h_var_eq ▸ ih i' j _ h_rhs_get.symm
              -- Use the original production's lhs_strings
              have h_lhs_strings : p.lhs_strings = p'.lhs_strings := hp_eq.symm ▸ rfl
              rw [h_lhs_strings]
              exact MCFG.Generates.prod (G := G (equiv j)) p' hp'_mem eta rhs_gen'
        intro j A strs hGen
        exact embod_converse_aux (emb j A) strs hGen j A rfl
      -- For the forward direction: G'.Generates S' [w] implies w ∈ some Ls i
      -- Since S' only has start productions S' → emb j (G j).S, we use induction
      -- Motive: for any A and strs, if G'.Generates A strs and A = S' and strs = [w], then ∃ i, w ∈ Ls i
      have forward : ∀ (A : N') (strs : List (List Sym)), G'.Generates A strs → A = G'.S → strs = [w] → ∃ i, w ∈ Ls i := by
        apply @MCFG.Generates.rec Sym G'
        intro p hp eta rhs_gen ih
        intro hA_eq hstrs_eq
        -- For S' = none, only start productions apply
        simp only [G', S', prods, startProds, origProds] at hp
        -- hp : p ∈ startProds ++ origProds
        -- For start productions, lhs = none
        -- For origProds, lhs = emb j p'.lhs which is always `some ...`
        -- So only start productions can have lhs = S' = none
        rcases List.mem_append.mp hp with hp_start | hp_orig
        · -- Start production case
          simp only [List.mem_map] at hp_start
          obtain ⟨j, _, hj⟩ := hp_start
          -- p = start production for j: lhs = S', rhs = [emb j (G j).S], lhs_strings = [[Sum.inr 0]]
          have hp_lhs : p.lhs = S' := hj.symm ▸ rfl
          have hp_rhs : p.rhs = [emb j (G (equiv j)).S] := hj.symm ▸ rfl
          have hp_lhs_strings : p.lhs_strings = [[Sum.inr 0]] := hj.symm ▸ rfl
          have hp_rhs_vars : p.rhs_vars = [[0]] := hj.symm ▸ rfl
          -- From hstrs_eq and the fact that Generates uses lhs_strings, we have [w] = p.lhs_strings.map (...)
          -- For start prod with lhs_strings = [[Sum.inr 0]], this means [w] = [(eta 0)], so w = eta 0
          have hw_eq_eta0 : w = eta 0 := by
            simp only [hp_lhs_strings] at hstrs_eq
            simp at hstrs_eq
            exact hstrs_eq.symm
          -- rhs_gen gives us: G'.Generates (p.rhs.get 0) (List.map eta (p.rhs_vars.get 0))
          have h_rhs_len : 0 < p.rhs.length := by simp [hp_rhs]
          have h_rhs_vars_len : 0 < p.rhs_vars.length := by simp [hp_rhs_vars]
          have h_get_vars : p.rhs_vars.get ⟨0, h_rhs_vars_len⟩ = [0] := by simp [hp_rhs_vars]
          have hGen_emb : G'.Generates (emb j (G (equiv j)).S) [eta 0] := by
            have := rhs_gen ⟨0, h_rhs_len⟩
            simp [hp_rhs, hp_rhs_vars] at this
            exact this
          have hGen_Gj : (G (equiv j)).Generates (G (equiv j)).S [eta 0] := embod_converse j _ _ hGen_emb
          -- Since (G (equiv j)).Language = Ls (equiv j), eta 0 ∈ Ls (equiv j)
          have h_mem : eta 0 ∈ (G (equiv j)).Language := hGen_Gj
          rw [hGlang] at h_mem
          exact ⟨equiv j, hw_eq_eta0 ▸ h_mem⟩
        · -- origProds case: lhs = emb j p'.lhs which is `some ...`, not `none`
          exfalso
          simp only [List.mem_flatMap, List.mem_map] at hp_orig
          obtain ⟨j', _, p', _, hp_eq⟩ := hp_orig
          have hp_lhs_emb : p.lhs = emb j' p'.lhs := hp_eq.symm ▸ rfl
          rw [hp_lhs_emb] at hA_eq
          simp [emb] at hA_eq
      exact forward _ _ hGen rfl rfl
    · intro ⟨i, hi⟩
      have hi' : (G i).Generates (G i).S [w] := (hGlang i).symm.subset hi
      -- Get j such that equiv j = i
      let j := equiv.symm i
      have hequiv : equiv j = i := equiv.apply_symm_apply i
      -- Prove by induction: if (G (equiv j)).Generates A strs, then G'.Generates (emb j A) strs
      have embod : ∀ (j : Fin n) (A : (G (equiv j)).N) (strs : List (List Sym)),
          (G (equiv j)).Generates A strs → G'.Generates (emb j A) strs := by
        intro j A strs hGen
        induction hGen with
        | prod p hp eta rhs_gen ih =>
          -- Construct the embedded production
          let p' : MCFGProduction Sym N' ar' :=
            { lhs := emb j p.lhs
              rhs := p.rhs.map (emb j)
              rhs_vars := p.rhs_vars
              lhs_strings := p.lhs_strings
              lhs_arity := p.lhs_arity
              rhs_len := by simp [p.rhs_len]
              rhs_arities := by
                intro k
                have klen : k.val < p.rhs.length := by simpa [List.length_map] using k.is_lt
                have hget : (p.rhs.map (emb j)).get k = some ⟨j, p.rhs.get ⟨k.val, klen⟩⟩ := by
                  simp [List.getElem_map, emb]
                rw [hget]
                exact p.rhs_arities ⟨k.val, klen⟩
              rhs_vars_nodup := p.rhs_vars_nodup
              lhs_indices_bounded := p.lhs_indices_bounded
              lhs_vars_nodup := p.lhs_vars_nodup }
          have hp' : p' ∈ G'.productions := by
            simp only [G', prods, origProds, startProds]
            apply List.mem_append_right
            apply List.mem_flatMap.mpr
            use j
            simp only [List.mem_finRange, true_and]
            apply List.mem_map.mpr
            refine ⟨p, ?_, ?_⟩
            · exact hp
            · simp [p']
          apply MCFG.Generates.prod (G := G') p' hp' _ _
          intro i
          have hlen : p'.rhs.length = p.rhs.length := by simp [p']
          have i' : i.val < p.rhs.length := hlen ▸ i.is_lt
          have hget_rhs : p'.rhs.get i = emb j (p.rhs.get ⟨i.val, i'⟩) := by simp [p', List.getElem_map]
          have hget_vars : p'.rhs_vars.get (Fin.cast p'.rhs_len.symm i) = p.rhs_vars.get (Fin.cast p.rhs_len.symm ⟨i.val, i'⟩) := by
            simp [p']
          rw [hget_rhs, hget_vars]
          exact ih ⟨i.val, i'⟩
      -- Backward direction: if w ∈ Ls i for some i, then G'.Generates G'.S [w]
      have hi'' : (G (equiv j)).Generates (G (equiv j)).S [w] := by rw [hequiv]; exact hi'
      have hi_emb : G'.Generates (emb j (G (equiv j)).S) [w] := embod j (G (equiv j)).S [w] hi''
      -- Use the start production: S' → emb j (G j).S
      -- Find the start production for j in startProds
      let startProdJ : MCFGProduction Sym N' ar' :=
        { lhs := S', rhs := [emb j (G (equiv j)).S], rhs_vars := [[0]], lhs_strings := [[Sum.inr 0]],
          lhs_arity := rfl, rhs_len := by simp [emb], rhs_arities := by
            intro k; simp only [List.length_singleton] at k; fin_cases k
            simp [ar', emb]; exact (G (equiv j)).start_arity.symm
          rhs_vars_nodup := by decide,
          lhs_indices_bounded := by
            intro s hs x hx
            simp at hs hx
            subst hs
            simp at hx
            subst hx
            simp,
          lhs_vars_nodup := by simp }
      have hstart_mem : startProdJ ∈ startProds := by
        simp only [startProds]
        apply List.mem_map.mpr
        exact ⟨j, by simp, rfl⟩
      have hstart_prod : startProdJ ∈ G'.productions := by
        simp only [G', prods]
        apply List.mem_append_left
        exact hstart_mem
      simp only [Set.mem_setOf_eq]
      convert MCFG.Generates.prod (G := G') startProdJ hstart_prod (fun _ => w) _ using 1
      · simp [startProdJ]
      · intro i
        simp [startProdJ] at *
        exact hi_emb
