/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Order.Defs.PartialOrder

/-!
# Hypergraphs and Ranked Alphabets

Definitions 2.1 and 2.2 from the paper.
-/

set_option autoImplicit false

/-- A hypergraph is a pair H = (V, E) where V is a finite set of vertices and
E is a finite multiset of hyperedges, each being a non-empty subset of V.
(Definition 2.1) -/
structure Hypergraph (V : Type*) where
  verts : Finset V
  edges : Multiset (Finset V)
  edges_subset : âˆ€ e âˆˆ edges, e âŠ† verts
  edges_nonempty : âˆ€ e âˆˆ edges, e.Nonempty

/-- A ranked alphabet is a finite set of symbols with a rank function.
(Definition 2.2) -/
structure RankedAlphabet where
  symbols : Type*
  rank : symbols â†’ â„•

/-- A hypergraph has bounded arity r if every hyperedge has cardinality â‰¤ r.
The paper (Theorem 9.2) requires "bounded arity" as a precondition for
Grohe's theorem. This is hypothesis (iv) of the main theorem (Theorem 12.1). -/
def Hypergraph.BoundedArity {V : Type*} (H : Hypergraph V) (r : â„•) : Prop :=
  âˆ€ e âˆˆ H.edges, e.card â‰¤ r
