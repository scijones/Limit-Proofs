# Automaton Equivalence for Tractable Belief-Driven Systems

This repository accompanies the discrete paper *Automaton Equivalence for Tractable Belief-Driven Systems*.

## Submission

- `discrete/online_full_behavior.tex` — LNCS submission source.

Assuming FPT ≠ W[1]: any recursively enumerable class of embodied systems supporting uniform tractable belief revision over arbitrary constraint relations with bounded arity has bounded-treewidth constraint structure; consequently, the set of all action sequences any such system can produce consistently with its beliefs forms a (k+1)-MCFL, where k is the uniform treewidth bound for the class.

## Lean formalization

`discrete/AsymptoticBB/` — Lean 4 formalization.

- `Axioms.lean` — cited results (Grohe, Engelfriet) and MCFL closure axioms
- `Bridge.lean` — bounded treewidth ⟹ per-decomposition behavior language is (k+1)-MCFL
- `Main.lean` — `full_behavior_bound`, `main_theorem_full`, and the finite-sub-class theorem
- `Agent/`, `Basic/`, `Grammars/`, `TreeDecomposition/` — supporting definitions

See `STATUS.md` for the full axiom inventory and proof chain.

## Building

Requires Lean 4 (v4.28.0) with Mathlib. From the repo root:

```bash
cd discrete
lake build
```

The `cd discrete` step is required — Lake resolves the toolchain and manifest from that directory.

## License

MIT — see `LICENSE`.

