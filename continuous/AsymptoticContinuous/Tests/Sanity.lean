/-
Copyright (c) 2026 Steven J. Jones. All rights reserved.
Released under the MIT license as described in the file LICENSE.
-/
import AsymptoticContinuous.Agent.Throughput

/-!
# Non-Vacuity Guards

`RandomVariable` is an opaque type and `IsMarkovChain` an uninterpreted
predicate, so without witnesses `ContinuousSystem` could be an empty
type and every class-level theorem vacuously true.  This module
constructs a concrete system from the three-axiom witness interface in
`InformationTheory/Axioms.lean` (each axiom a textbook-true fact) and
kernel-checks that:

1. `ContinuousSystem` is inhabited (`trivialSystem`);
2. its effective graph provably has treewidth 0, via an explicit
   one-bag `TreeDecomposition` — the same construction that makes
   `∃ k, tw ≤ k` trivially true per-instance, documented here so the
   deletion of the per-instance necessity axioms is self-explaining;
3. the unconditional bound `throughput_le_sensor_capacity` applies
   non-vacuously (`throughput = 0` computed exactly);
4. the `InterfaceSeparated` hypothesis of `throughput_rate_bound` is
   satisfiable: a two-coordinate system (`sepSystem`) with sensors and
   effectors in different bags of a width-0 decomposition witnesses it,
   so the `(k+1)·R_max` theorem is not a theorem about the empty set.

None of this is load-bearing for the class-level results; it certifies
they are not theorems about the empty type.
-/

set_option autoImplicit false

/-! ## A one-bag tree decomposition of the empty graph on `Fin 1` -/

/-- The single-node tree decomposition: one bag containing the single
vertex.  Witnesses `tw(⊥ : SimpleGraph (Fin 1)) ≤ 0`. -/
def trivialTD : TreeDecomposition (⊥ : SimpleGraph (Fin 1)) where
  I := PUnit
  tree := ⊥
  tree_isTree := by
    constructor
    · exact ⟨fun u v => (Subsingleton.elim u v) ▸ SimpleGraph.Reachable.refl u⟩
    · intro v p hp
      cases p with
      | nil => exact hp.ne_nil rfl
      | cons h _ => exact h.elim
  bag := fun _ => Finset.univ
  vertex_cover := fun v => ⟨PUnit.unit, Finset.mem_univ v⟩
  edge_cover := fun u v h => h.elim
  running_intersection := by
    intro v
    haveI : Nonempty {i : PUnit | v ∈ (Finset.univ : Finset (Fin 1))} :=
      ⟨⟨PUnit.unit, Finset.mem_univ v⟩⟩
    exact ⟨fun a b => (Subsingleton.elim a b) ▸ SimpleGraph.Reachable.refl a⟩

theorem trivialTD_width : trivialTD.width = 0 := by
  unfold TreeDecomposition.width trivialTD
  simp
  rfl

theorem trivial_graph_tw0 : (⊥ : SimpleGraph (Fin 1)).HasTreewidthAtMost 0 :=
  ⟨trivialTD, le_of_eq trivialTD_width⟩

/-! ## A concrete continuous system -/

/-- The trivial system: one coordinate, empty effective graph, all
random variables equal to the witness, zero rates.  Every structure
field is discharged from the witness interface. -/
noncomputable def trivialSystem : ContinuousSystem where
  N := 1
  hN := Nat.one_pos
  G_eff := ⊥
  V_O := Finset.univ
  V_A := Finset.univ
  obs := witnessRV
  action := witnessRV
  state := witnessRV
  coordsRV := fun _ => witnessRV
  R := fun _ => 0
  hR_nonneg := fun _ => le_refl 0
  graph_structured := fun _ _ =>
    isMarkovChain_self_right witnessRV witnessRV witnessRV
  rate_bound := fun C => by
    rw [cmi_cond_self witnessRV witnessRV]
    simp

/-- `ContinuousSystem` is inhabited. -/
theorem continuousSystem_nonempty : Nonempty ContinuousSystem :=
  ⟨trivialSystem⟩

/-- The trivial system's throughput is exactly zero. -/
theorem trivialSystem_throughput : trivialSystem.throughput = 0 :=
  cmi_cond_self witnessRV witnessRV

/-- **Non-vacuity of the unconditional throughput bound**: the sensor
capacity bound applies to the trivial system with no hypotheses. -/
theorem throughput_rate_bound_nonvacuous :
    trivialSystem.throughput ≤
      ((trivialSystem.V_O.card : ℕ) : ℝ) * trivialSystem.R_max :=
  throughput_le_sensor_capacity trivialSystem

/-! ## A separated two-coordinate system

Witnesses that `InterfaceSeparated` — the hypothesis of the `(k+1)·R_max`
theorem — is satisfiable, so the conditional theorem is non-vacuous. -/

/-- The two-node path decomposition of the empty graph on `Fin 2`:
node `false` owns coordinate 0, node `true` owns coordinate 1. -/
noncomputable def sepTD : TreeDecomposition (⊥ : SimpleGraph (Fin 2)) where
  I := Bool
  tree := ⊤
  tree_isTree := by
    constructor
    · constructor
      intro u v
      by_cases huv : u = v
      · exact huv ▸ SimpleGraph.Reachable.refl u
      · exact (SimpleGraph.top_adj u v |>.mpr huv).reachable
    · intro v p hp
      have h3 : 3 ≤ p.length := hp.three_le_length
      have hnd : p.support.tail.Nodup := hp.support_nodup
      have hcard : p.support.tail.length ≤ 2 := by
        have := List.Nodup.length_le_card hnd
        simpa using this
      have hlen : p.support.length = p.length + 1 :=
        SimpleGraph.Walk.length_support p
      have htail : p.support.tail.length = p.length := by
        rw [List.length_tail, hlen]
        omega
      omega
  bag := fun b => {if b then 1 else 0}
  vertex_cover := by
    intro v
    fin_cases v
    · exact ⟨false, by simp⟩
    · exact ⟨true, by simp⟩
  edge_cover := fun u v h => h.elim
  running_intersection := by
    intro v
    have hsub : ∀ (a b : {i : Bool | v ∈ ({if i then 1 else 0} : Finset (Fin 2))}),
        a = b := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [Set.mem_setOf_eq, Finset.mem_singleton] at ha hb
      have : (if a then (1 : Fin 2) else 0) = (if b then 1 else 0) := by
        rw [← ha, ← hb]
      apply Subtype.ext
      by_cases hA : a <;> by_cases hB : b <;> simp_all
    haveI : Nonempty {i : Bool | v ∈ ({if i then 1 else 0} : Finset (Fin 2))} := by
      fin_cases v
      · exact ⟨⟨false, by simp⟩⟩
      · exact ⟨⟨true, by simp⟩⟩
    exact ⟨fun a b => (hsub a b) ▸ SimpleGraph.Reachable.refl a⟩

theorem sepTD_width : sepTD.width = 0 := by
  unfold TreeDecomposition.width
  have hbag : ∀ b : Bool, (sepTD.bag b).card = 1 := by
    intro b
    simp [sepTD]
  have himg : Finset.univ.image (fun i => (sepTD.bag i).card) = {1} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_image.mpr ⟨false, Finset.mem_univ _, hbag false⟩, ?_⟩
    intro n hn
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hn
    exact hbag b
  rw [himg]
  rfl

/-- Sensors at coordinate 1, effectors at coordinate 0, no coupling. -/
noncomputable def sepSystem : ContinuousSystem where
  N := 2
  hN := by omega
  G_eff := ⊥
  V_O := {1}
  V_A := {0}
  obs := witnessRV
  action := witnessRV
  state := witnessRV
  coordsRV := fun _ => witnessRV
  R := fun _ => 0
  hR_nonneg := fun _ => le_refl 0
  graph_structured := fun _ _ =>
    isMarkovChain_self_right witnessRV witnessRV witnessRV
  rate_bound := fun C => by
    rw [cmi_cond_self witnessRV witnessRV]
    simp

/-- The single-edge path from `false` to `true` in the two-node tree. -/
private noncomputable def sepPath : sepTD.tree.Walk false true :=
  SimpleGraph.Walk.cons (by simp [sepTD]) SimpleGraph.Walk.nil

/-- `true` is in the subtree at `true` (rooted at `false`). -/
theorem sepTD_true_mem_subtree : true ∈ sepTD.subtreeAt false true := by
  refine ⟨sepPath, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    simp [sepPath]
  · simp [sepPath]

/-- `false` is not in the subtree at `true` (rooted at `false`). -/
theorem sepTD_false_not_mem_subtree : false ∉ sepTD.subtreeAt false true := by
  rintro ⟨p, hp, htmem⟩
  have huniq := sepTD.tree_isTree.IsAcyclic.path_unique ⟨p, hp⟩
    ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil⟩
  have hval : p = SimpleGraph.Walk.nil := congrArg Subtype.val huniq
  rw [hval] at htmem
  simp at htmem

/-- **Non-vacuity of `InterfaceSeparated`**: the two-coordinate system is
interface-separated at width 0. -/
theorem sepSystem_interfaceSeparated : sepSystem.InterfaceSeparated 0 := by
  refine ⟨sepTD, le_of_eq sepTD_width, false, true, ?_, ?_⟩
  · -- V_O = {1} ⊆ vertsBelow false true
    intro v hv
    simp only [sepSystem, Finset.mem_singleton] at hv
    subst hv
    simp only [TreeDecomposition.vertsBelow, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨true, sepTD_true_mem_subtree, by simp [sepTD]⟩
  · -- V_A = {0} never appears below `true`
    intro v hv hbelow
    simp only [sepSystem, Finset.mem_singleton] at hv
    subst hv
    exfalso
    simp only [TreeDecomposition.vertsBelow, Finset.mem_biUnion, Finset.mem_filter,
      Finset.mem_univ, true_and] at hbelow
    obtain ⟨i, hi_sub, hi_bag⟩ := hbelow
    cases i with
    | false => exact sepTD_false_not_mem_subtree hi_sub
    | true =>
      simp [sepTD] at hi_bag

/-- **Non-vacuity of the conditional throughput theorem**: it applies to
`sepSystem` with a satisfied hypothesis. -/
theorem throughput_rate_bound_conditional_nonvacuous :
    sepSystem.throughput ≤ ((0 + 1 : ℕ) : ℝ) * sepSystem.R_max :=
  throughput_rate_bound sepSystem 0 sepSystem_interfaceSeparated
