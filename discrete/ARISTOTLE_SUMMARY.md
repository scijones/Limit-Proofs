# Summary of changes for run 29aaa2f5-20da-4fee-8446-a814c1afadd3
I reviewed the argument at the conceptual and formal levels and encoded the strongest honest version.

**Bottom line:** the one-directional ceiling works conditionally, but “actions are vertices and therefore occur in bags” is not alone sufficient. It establishes that action, policy, and scheduling dependencies are internal to the original CSP and that projecting to action terminals cannot increase the MCFL tier. It does not establish an execution order: a satisfying assignment is static, and a tree decomposition does not intrinsically order its vertices.

The remaining load-bearing condition is precise: the independently defined instantaneous operational behavior language must coincide with the structured-yield language obtained from the schedule-augmented CSP. Under that correspondence, the intended chain is valid:

1. uniform tractability and the Grohe hypotheses give one class-wide treewidth bound `k` for original structures assumed to be cores;
2. the bounded-treewidth/string-yield interface gives a `(k+1)`-MCFG for structured orderings;
3. homomorphic projection to action variables cannot increase dimension;
4. finite stitching over satisfying assignments and admissible decompositions preserves the tier;
5. the scheduling-semantics equality transfers this ceiling to the original agent’s instantaneous self-consistent action language.

Added the proved Lean theorem `main_theorem_instantaneous_behavior` in `AsymptoticBB/Main.lean`. It takes the operational action language independently and exposes exactly the scheduling-semantics equality required, so it cannot silently define “actual behavior” as only the convenient decomposition language.

Added `HIGH_LEVEL_ASSESSMENT.md`, explaining:
- what action membership in CSP bags does and does not imply;
- why tree compatibility needs an independent yield definition;
- why a prefix-frontier characterization should not be inferred casually from ordinary treewidth;
- the core-to-original-behavior qualification;
- why this is an upper-class statement, not an exact-dimension or individual-trace lower bound;
- why finite per-instance languages do not by themselves provide the claimed structural content.

The original external theorem/axiom declarations were preserved unchanged. The project layout was repaired to match its declared Lean module paths. The complete project builds successfully, and active Lean sources contain no `sorry` or `admit`. Changes were committed and pushed through commit `833f559`.

# Summary of changes for run 8f8c8811-5c80-435a-8117-e03418dc49a2
Yes—that distinction makes sense, and I revised the formalization accordingly.

- Restored finite union as a proved, existential **stitching** principle within a fixed positive MCFG tier. It does not choose `k`, preserve a selected solution, or require a construction algorithm.
- Fully proved the finite-union theorem in `AsymptoticBB/Grammars/Union.lean`; no new axiom was introduced.
- Proved `behavior_grammar_exists`: each satisfying assignment gives a homomorphic image of the width-bounded ordering grammar, and those image languages are stitched by finite union.
- Reactivated the behavior bridge and the per-agent, finite-subclass, full-behavior, and uniform-family main results.
- Added `main_theorem_schedule_class`, directly expressing the intended general restriction: one uniform structural `k` exists, and every action-schedule language induced by any width-`≤k` rooted decomposition belongs to the same `(k+1)`-MCFL class.
- Reworded the formalization and audit documentation to emphasize existential class membership rather than actual construction or solution preservation.
- Kept the stronger `finite_language_is_mcfl` shortcut absent. The uniform `k` is obtained from the treewidth result before finite stitching is applied.

Verification: the complete project builds successfully, active Lean sources contain no `sorry` or `admit`, and `mcfg_finite_union` uses only standard permitted logical axioms. All changes were committed and pushed through `1bf96d6`.

# Summary of changes for run 084f4cd6-d6f2-425d-8d0f-53716f83261c
Completed the non-computational semantic-core formalization and purged the finiteness bypass.

- Added `AsymptoticBB/SemanticCore.lean`, proving:
  - homomorphic equivalence preserves CSP decision truth against every target;
  - componentwise core equivalence lifts through a composition operation that respects homomorphic equivalence;
  - the original composed CSP and composed-core CSP have literally equal decision languages;
  - an MCFG upper bound, or an exact minimal MCFG tier, transfers from the composed cores to the original composed CSP;
  - static core witnesses require no algorithm for computing or selecting cores.
- Removed the generic `mcfg_finite_union` assumption. Combined with singleton grammars, it could recover a low-dimensional grammar for every finite language and thus recreate the prohibited shortcut.
- Removed the finite-powerset route used by `full_behavior_bound` and the finite-subclass route. The former `full_behavior_bound`, `main_theorem_full`, and `main_theorem_finite_subclass` sources remain as commented audit history rather than active declarations.
- Also disabled the decomposition-indexed behavior-grammar and downstream grammar-valued main theorems. Once generic finite union was removed, those claims required a synchronized grammar-refinement construction that the project had not proved. No new axiom was introduced to conceal that missing construction.
- The active structural result `class_tractable_implies_bounded_tw` remains, as do the new semantic correspondence theorems. Together they cleanly separate the existing Grohe treewidth interface from the non-computational transfer back to the original CSP.
- Updated `FORMALIZATION_AUDIT.md`, sanity documentation, and axiom reports to state the resulting scope accurately.

Verification:
- The project builds successfully: 1,177 jobs.
- Lean sources contain no `sorry` or `admit`.
- No new axioms were introduced.
- `HomSystem.cspDecision_iff_of_equivalent` depends on no axioms; the language-transfer results use only permitted standard logical principles.

Changes were committed and pushed in `bbb195e` and corrective commit `724a10c`.

# Summary of changes for run 1c693cce-e1e4-45d0-bef1-a4094a69edce
Completed a declaration-level fidelity audit, treating Lean definitions and theorem types—not comments—as authoritative.

Changes:
- Corrected `MCFGProduction` to enforce standard copyless/linear MCFG behavior: RHS component variables are distinct and each may occur at most once across output components. The previous encoding permitted copying and was not faithful to standard MCFG/LCFRS definitions.
- Strengthened `main_theorem_uniform_family` so its conclusion explicitly includes the uniform treewidth bound derived through the Grohe interface. Previously that conclusion was discarded, making the theorem’s grammar-family statement vacuous when no width-bounded decomposition was supplied.
- Added `FORMALIZATION_AUDIT.md`, documenting the exact status of the Grohe and Engelfriet encodings.

Main audit conclusion:
- The Grohe interface has the shape of a legitimate strong-hypothesis corollary: it assumes all structures are cores and concludes actual bounded treewidth rather than merely bounded treewidth modulo homomorphic equivalence. However, recursive enumerability, polynomial-time solvability, and the core predicate remain opaque, and relational structures/homomorphisms/algorithms are not formalized. Thus this is an external theorem interface, not a full formalization of Grohe’s work.
- The `engelfriet_tw_to_mcfl` interface is not presently justified by the cited Engelfriet result. It assumes a bespoke exact grammar for an undefined `IsTreeCompatibleOrdering` predicate, effectively placing the disputed bridge inside an axiom. The project formalizes neither HRGs and string yields nor the alternative special-treewidth/MSO/tree-automaton construction. The recent cited bounded-treewidth/MCFL result specifically concerns MSO-definable bounded **special** treewidth systems, not arbitrary rooted ordinary tree decompositions. This mismatch is detailed in the audit.
- The MCFG homomorphic-image and finite-union closure results also remain external assumptions.

The Lean project builds successfully after the corrections, and the Lean sources contain no `sorry` or `admit`. This establishes internal consistency of deductions from the declared interfaces, but does not turn the remaining external assumptions into formalizations of the cited works.