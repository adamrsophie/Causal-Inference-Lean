# Causal-Inference-Lean

A machine-checked Lean 4 formalization of foundational and canonical results in causal inference,
built on Mathlib. The aim is a library with explicit assumptions, verified counterexamples, and
documented scope limits; it is not, and does not claim to be, a complete formalization of all of
causal inference.

The project is at an early stage. Modules are added only when they contain checked declarations.

## Principles

- Identification, estimation, and inference are kept separate.
- Finite or discrete results are kept separate from general measurable ones.
- Every modeling assumption is a hypothesis of the theorem that uses it.
- Positive identification results are paired with counterexamples where that is meaningful.
- No `sorry`, no `admit`, and no axioms beyond those of Lean and Mathlib.

## Building

Lean `v4.36.0` and Mathlib `v4.36.0` (see `lean-toolchain` and `lakefile.toml`).

```sh
lake exe cache get     # prebuilt Mathlib
lake build
```

## License

GNU General Public License v3.0; see `LICENSE`.
