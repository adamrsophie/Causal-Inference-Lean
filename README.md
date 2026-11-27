# Causal-Inference-Lean

A machine-checked Lean 4 formalization of foundational and canonical results in causal inference,
built on Mathlib. The aim is a library with explicit assumptions, verified counterexamples, and
documented scope limits; it is not, and does not claim to be, a complete formalization of all of
causal inference.

The project is at an early stage. Modules are added only when they contain checked declarations.

Project site with a dependency map, highlights, and a full reference:
<https://adamrsophie.github.io/Causal-Inference-Lean/>

## Contents

| Directory | Content |
|---|---|
| `CausalInference/Basic` | Finite probability distributions, marginals, conditional independence and the graphoid properties |
| `CausalInference/Graphical` | Directed graphs on Mathlib's `Digraph`: parents, ancestors, acyclicity, topological orders, graph surgery, ancestral sets; d-separation with a decidable checker and the equivalence to active paths; Markov factorization, the local Markov property, and the global Markov property (d-separation implies conditional independence, with no positivity assumption); graphical criteria: back-door, front-door, sequential back-door, instruments, the moral graph criterion for d-separation, Markov blankets; acyclic directed mixed graphs, districts, latent projection |
| `CausalInference/SCM` | Finite structural causal models: unique solutions, the causal Markov condition, interventions and the truncated factorization, adjustment for direct causes, identifiability with the bow counterexample, counterfactuals with consistency, composition, and the three-step evaluation; soundness of the three rules of do-calculus, with the back-door adjustment and the front-door formula derived from them |
| `CausalInference/LinearSEM` | Linear structural equation models: total effects as sums over directed paths, the implied covariance, regression coefficients and partial covariance, path coefficients by regression, instrumental variable ratios, the single-door decomposition, worked path diagrams, the bow counterexample |
| `CausalInference/PartialIdentification` | Identified sets, point identification, Manski bounds with sharpness, monotone treatment response |
| `CausalInference/Designs/Randomized` | Finite-population designs: Bernoulli, complete, stratified, paired, and cluster randomization; Neyman's variance; Fisher's randomization test |
| `CausalInference/Designs/DifferenceInDifferences` | Two-period identification and bias, conditional parallel trends with a general covariate, staggered adoption with group-time effects and event-time aggregation, two-way fixed effects counterexamples including contaminated leads |
| `CausalInference/Designs/RegressionDiscontinuity` | Sharp and fuzzy designs: identification at the cutoff from the observed law |
| `CausalInference/Designs/SyntheticControl` | Synthetic control weights, fit, and the noiseless linear factor model |
| `CausalInference/InstrumentalVariables` | Principal strata, the local average treatment effect theorem, counterexamples without monotonicity, bounds on the average effect with sharpness, instrumental inequalities, linear instrumental variables |
| `CausalInference/Interference` | Partial interference, direct and indirect effects, two-stage randomization |
| `CausalInference/Mediation` | Controlled and natural effects, decompositions, the mediation formula, a cross-world counterexample |
| `CausalInference/Longitudinal` | Time-varying treatments: sequential exchangeability, the g-formula at any finite horizon, inverse probability weighting, treatment-confounder feedback |
| `CausalInference/Measures` | Risk difference, risk ratio, odds ratio; collapsibility and the odds ratio counterexample; effect modification; the sure-thing principle and Simpson's reversal; paradox examples |
| `CausalInference/Interaction` | Response types for two treatments, additive interaction, synergism, sufficient causes |
| `CausalInference/Attribution` | Probabilities of necessity, sufficiency, and both: identification under exogeneity and monotonicity, sharp bounds from experimental and combined data, non-identification, textbook examples |
| `CausalInference/Bias` | Selection bias and conditioning on a collider, selection without bias, the built-in selection bias of hazard ratios, measurement error and misclassification with correction formulas |
| `CausalInference/BiasAnalysis` | Quantitative bias analysis on tables: selection bias adjustment by selection odds ratio, projection, and weighting, with their agreement, bounds over unknown participation, and loss to follow-up; worked examples recomputed from published inputs |
| `CausalInference/Survival` | Discrete-time survival, hazards and the product formula, independent censoring and the product-limit functional with a non-identification counterexample, hazard ratios against survival, the Kaplan-Meier estimator |
| `CausalInference/MissingData` | Missingness mechanisms, inverse probability weighting and its augmented form, regression identities, identification of the mean from the observed law under missingness at random, non-identification counterexamples without it and without positivity |
| `CausalInference/Sensitivity` | Rosenbaum bounds for sign and signed-rank statistics, bias formulas for unmeasured confounding, the bounding factor and the E-value |
| `CausalInference/Estimation` | Independent samples, consistency with continuous mapping, asymptotic linearity and its closure properties, asymptotic normality, the delta method, Wald interval coverage with an estimated scale |

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
