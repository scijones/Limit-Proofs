# High-level assessment of the instantaneous behavioral-ceiling argument

## Short answer

The proposed chain is **conditionally sound**, but the last answer in the
transcript overstates what follows merely from “the actions are in the bags.”
The correct one-directional theorem has this form:

1. one original, schedule-augmented relational CSP represents the agent’s
   instantaneous beliefs, policy, action choices, and admissible scheduling
   choices;
2. the class of those original structures satisfies the stated Grohe
   hypotheses (or the structures are assumed to be cores);
3. Grohe supplies one uniform treewidth bound `k`;
4. the independently defined operational action language is proved equal to
   the structured string-yield language covered by the graph-grammar result;
5. terminal projection/finite union then preserve the `(k+1)`-MCFL upper tier.

Under item 4, the result really is a ceiling on the original agent’s
instantaneous self-consistent behavior. No grammar-construction algorithm is
needed in the theorem statement.

## What “actions are in the bags” does establish

If action and schedule variables are vertices of the original CSP, the vertex
cover condition puts them in bags. If an action and the beliefs/policy facts
constraining it occur in one constraint scope, edge cover puts that whole scope
in some common bag. Thus action dependence is not external to the structure to
which the treewidth bound applies.

Projection from a generated full-variable word to action symbols is harmless
for an upper bound: MCFLs are closed under terminal homomorphism, including
erasure. Projection can lower language complexity; it does not invalidate a
ceiling.

Focusing on one instantaneous schedule-augmented CSP also avoids confusing one
static assignment with an indefinitely long trajectory. A trajectory can be
handled separately by explicit finite-horizon unrolling or a justified closure
operation.

## What it does *not* establish

Bag membership alone does not impose an order. A tree decomposition is an
undirected structural witness, and a satisfying assignment is a static
valuation. Neither one says which variable is read first.

Consequently, the following implication is not automatic:

> schedule variables occur in the CSP, therefore every operational schedule is
> a tree-compatible yield of every (or some) width-`k` decomposition.

The schedule constraints may indeed make that implication true, but it must be
a property of the schedule-augmented model. Mathematically, one needs an
identification such as

`ActualInstantaneousLanguage(A) = FullBehaviorLanguage(A, k)`

or, more generally, a dimension-preserving homomorphic-image/inclusion theorem
from the operational language to a specifically generated structured-yield
language. Merely saying that scheduling knowledge is “implicit” does not
supply this equality.

## “Tree-compatible” must be fixed independently

There is no single standard language called *the* tree-compatible orderings of
a rooted decomposition. A defensible definition must choose a concrete yield
semantics, for example:

* assign every vertex a unique home bag among the bags containing it;
* traverse/derive the rooted decomposition according to specified rules;
* emit each vertex exactly once at its home bag;
* describe which child-subtree yields may be concatenated or interleaved; and
* carry only the exposed boundary/interface while composing subtree yields.

Soundness says every generated word obeys those rules. Completeness says every
ordering obeying those rules is generated. The bounded interface then controls
the grammar parameter. This is where an HRG/tree-transducer/automaton theorem
can be applied.

A “prefix frontier lies in one bag” formulation should not be asserted without
proof: closely related linear-order frontier parameters characterize path-like
width notions and can be stronger than ordinary treewidth. Ordinary treewidth
naturally supports a branching decomposition; converting that branching object
to words requires an explicit yield construction.

## What the citations safely provide

At the level needed by this project, the literature supports a proof
architecture connecting bounded-width graph-algebra/HRG descriptions and
bounded-dimensional string-yield languages. It does not, merely from the words
“tree decomposition,” identify an arbitrary project-specific ordering
predicate with those yields.

Thus the strongest safe use is an external existential interface stating only:

`∃ G, G.dimension ≤ k + 1 ∧ G.Language = StructuredYields(td, r)`.

That is enough for the downstream one-directional ceiling once
`StructuredYields` is fixed and matched to the operational schedule semantics.
It is safer than the former `StructuredMCFG` interface, which additionally
postulated project-specific node maps, exact boundary arities, bag-local
terminals, and child fields not needed by the theorem.

## Core qualification

Grohe’s conclusion is naturally about cores/homomorphic equivalence. To make
the final language theorem literally concern the original CSP, use either:

* a class whose original relational structures are assumed to be cores; or
* an action- and schedule-preserving transfer theorem between each original
  structure and its core.

Decision-level homomorphic equivalence alone preserves existence of a solution,
not the multiplicity, names, or ordering of action variables. The current
concrete main theorem uses the first option through its `AllCores` hypothesis.

## Meaning of the ceiling

The result is an upper-class statement:

`ActualInstantaneousLanguage(A) ∈ (k+1)-MCFL`.

It does not say the minimal dimension is exactly `k+1`, that every individual
word outside a chosen traversal is “outside MCFL,” or that arbitrary
self-inconsistent/external schedules are prohibited. A single word is always a
regular language; hierarchy claims apply to languages, not isolated traces.

The per-instance language is finite, so bare existential MCFL membership is
also obtainable for an unrelated trivial reason. The structural content lies
in deriving the same `k` uniformly from the class-level treewidth theorem and
in tying the grammar witnesses to the structured-yield interface, rather than
claiming that a single finite language is intrinsically difficult.

## Formal change in this project

The Lean development now includes
`main_theorem_instantaneous_behavior`. It takes an independently supplied
instantaneous operational language and the explicit schedule-semantics equality
needed to identify it with the full structured behavior language at the
uniform class bound. It then proves that this original operational language is
a `(k+1)`-MCFL.

The Engelfriet-facing assumption has also been narrowed to the exact
existential language statement used downstream; the unused, over-specified
`StructuredMCFG` record has been removed from the trust interface.
