# Causal-Inference-Lean

A machine-checked Lean 4 formalization of foundational and canonical results in causal inference,
built on Mathlib. The aim is a library with explicit assumptions, verified counterexamples, and
documented scope limits; it is not, and does not claim to be, a complete formalization of all of
causal inference.

The project is at an early stage. Modules are added only when they contain checked declarations.

## Contents

| Directory | Content |
|---|---|
| `CausalInference/Graphical` | Directed graphs on Mathlib's `Digraph`: parents, ancestors, acyclicity, topological orders, graph surgery; acyclic directed mixed graphs, districts, latent projection |
| `CausalInference/PartialIdentification` | Identified sets, point identification, Manski bounds with sharpness |
| `CausalInference/Designs/Randomized` | Finite-population designs: Bernoulli and complete randomization, Neyman's variance, Fisher's randomization test |
| `CausalInference/Designs/DifferenceInDifferences` | Two-period identification and bias, staggered adoption with group-time effects, a two-way fixed effects counterexample |
| `CausalInference/Designs/RegressionDiscontinuity` | Sharp and fuzzy designs: identification at the cutoff |
| `CausalInference/Designs/SyntheticControl` | Synthetic control weights, fit, and the noiseless linear factor model |
| `CausalInference/InstrumentalVariables` | Principal strata, the local average treatment effect theorem, counterexamples without monotonicity |
| `CausalInference/Interference` | Partial interference, direct and indirect effects, two-stage randomization |
| `CausalInference/Mediation` | Controlled and natural effects, decompositions, the mediation formula, a cross-world counterexample |

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
scripts/check.sh       # placeholder scan, build, axiom check
```

## License

GNU General Public License v3.0; see `LICENSE`.
