/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Grammars.MCFG

/-!
# Nonterminal Refinement Preserves Dimension

Lemma 6.5 from the paper: splitting nonterminals into indexed copies
does not increase the dimension of an MCFG.
-/

set_option autoImplicit false

/-- A refinement of an MCFG replaces each nonterminal A with a finite family
{Aáµ… : Î± âˆˆ I_A}, preserving arities. (Lemma 6.5)

The paper specifies three conditions for a valid refinement:
1. Each nonterminal A is replaced by copies {Aáµ…}, with ar'(Aáµ…) = ar(A).
2. For each production in G, G' includes a subset of the corresponding
   productions obtained by choosing compatible indices for each nonterminal.
3. Terminal productions may change the terminal symbols emitted.

Condition (1) is captured by `proj` + `ar_preserved` + `proj_surj`.
Condition (2) is captured by `prod_compat` (each G' production corresponds
   to some G production with compatible nonterminal projections).
Condition (3) is captured by allowing different terminal types Symâ‚, Symâ‚‚.

For the dimension bound, conditions (1) and (3) suffice; `prod_compat`
is included for the bridge theorem's correctness (soundness/completeness). -/
structure MCFG.IsRefinementOf {Symâ‚ Symâ‚‚ : Type*} (G' : MCFG Symâ‚‚) (G : MCFG Symâ‚) where
  /-- There is a surjection from G'.N to G.N mapping each refined nonterminal
      back to its original. -/
  proj : G'.N â†’ G.N
  /-- Every original nonterminal has at least one copy (the paper says
      "replacing each nonterminal A with a finite set of copies"). -/
  proj_surj : Function.Surjective proj
  /-- The arity is preserved under projection. -/
  ar_preserved : âˆ€ A' : G'.N, G'.ar A' = G.ar (proj A')
  /-- The start symbol of G' projects to the start symbol of G. -/
  start_preserved : proj G'.S = G.S
  /-- Production compatibility: each production in G' corresponds to a
      production in G, with the LHS and all RHS nonterminals projecting
      correctly. (Condition (ii) from Lemma 6.5.) -/
  prod_compat : âˆ€ p' âˆˆ G'.productions,
    âˆƒ p âˆˆ G.productions,
      proj p'.lhs = p.lhs âˆ§
      p'.rhs.map proj = p.rhs

/-- Lemma 6.5 (Nonterminal refinement preserves dimension).
If G' is obtained from G by splitting nonterminals into indexed copies
(preserving arities), then dim(G') â‰¤ dim(G).

**Proof:** dim(G') = max_{A'} G'.ar(A') = max_{A'} G.ar(proj(A'))
â‰¤ max_{A} G.ar(A) = dim(G),
since proj(A') ranges over (a subset of) G.N and ar is preserved. -/
theorem refinement_preserves_dimension {Symâ‚ Symâ‚‚ : Type*}
    (G : MCFG Symâ‚) (G' : MCFG Symâ‚‚) (href : G'.IsRefinementOf G) :
    G'.dimension â‰¤ G.dimension := by
  apply G'.dimension_le_of_forall
  intro A'
  rw [href.ar_preserved]
  exact G.ar_le_dimension (href.proj A')
