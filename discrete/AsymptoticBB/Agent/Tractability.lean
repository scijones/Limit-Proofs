/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticBB.Agent.Defs
import AsymptoticBB.TreeDecomposition.Defs

/-!
# Tractable Belief Revision

Per-instance definitions for polynomial-time solvability and tractable
belief revision. Class-level versions of these predicates are defined
in SizedInstances.lean and SizedAgent.lean.
-/

set_option autoImplicit false

universe u v

opaque PolyTimeSolvable {V : Type u} [DecidableEq V] {D : V â†’ Type v} : CSP V D â†’ Prop

def EmbodiedAgent.TractableBelRevision {V : Type u} [DecidableEq V] [Fintype V]
    {D : V â†’ Type v} (A : EmbodiedAgent V D) : Prop :=
  âˆ€ (D' : V â†’ Type v) (P' : CSP V D'),
    P'.constraintHypergraph = A.constraintHypergraph â†’
    PolyTimeSolvable P'
