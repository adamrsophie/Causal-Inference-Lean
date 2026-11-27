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
| `CausalInference/SCM` | Finite structural causal models: unique solutions, the causal Markov condition, interventions and the truncated factorization, adjustment for direct causes, identifiability with the bow counterexample, counterfactuals with consistency, composition, and the three-step evaluation; soundness of the three rules of do-calculus, with the back-door adjustment and the front-door formula derived from them for arbitrary graphs and sets satisfying the graphical criteria, the effect of treatment on the treated by adjustment, and the effect of a plan of several controls under the sequential back-door criterion; twin networks and the joint law of factual and counterfactual worlds, with independence of counterfactuals read from d-separation; actual causation and sustenance with decidable checks on the standard examples |
| `CausalInference/LinearSEM` | Linear structural equation models: total effects as sums over directed paths, the implied covariance, regression coefficients and partial covariance, path coefficients by regression, instrumental variable ratios, the single-door decomposition, worked path diagrams, the bow counterexample |
| `CausalInference/PartialIdentification` | Identified sets, point identification, Manski bounds with sharpness, monotone treatment response |
| `CausalInference/Designs/Randomized` | Finite-population designs: Bernoulli, complete, stratified, paired, and cluster randomization; Neyman's variance; Fisher's randomization test |
| `CausalInference/Designs/DifferenceInDifferences` | Two-period identification and bias, conditional parallel trends with a general covariate, staggered adoption with group-time effects and event-time aggregation, two-way fixed effects counterexamples including contaminated leads, repeated cross sections under stable composition, the trend-adjusted estimator with three periods, parallel trends on the additive, log, and logit scales |
| `CausalInference/Designs/RegressionDiscontinuity` | Sharp and fuzzy designs: identification at the cutoff from the observed law; the fuzzy estimand as the average effect at the cutoff without selection on gains, absence of overlap in the sharp design, a sorting counterexample |
| `CausalInference/Designs/SyntheticControl` | Synthetic control weights, fit, and the noiseless linear factor model |
| `CausalInference/InstrumentalVariables` | Principal strata, the local average treatment effect theorem, counterexamples without monotonicity, bounds on the average effect with sharpness, the Balke and Pearl bounds as the exact identified set of the response-type model, the instrumental inequality for binary and finite variables, the effect on the treated, linear instrumental variables |
| `CausalInference/Interference` | Partial interference, direct and indirect effects, two-stage randomization |
| `CausalInference/Mediation` | Controlled and natural effects, decompositions, the mediation formula, a cross-world counterexample |
| `CausalInference/Longitudinal` | Time-varying treatments: sequential exchangeability, the g-formula at any finite horizon for static and dynamic regimes, inverse probability weighting at any horizon, treatment-confounder feedback, the g-null test and the g-null paradox setting |
| `CausalInference/Measures` | Risk difference, risk ratio, odds ratio; collapsibility and the odds ratio counterexample; effect modification; the sure-thing principle and Simpson's reversal; paradox examples |
| `CausalInference/Interaction` | Response types for two treatments, additive interaction, synergism, sufficient causes |
| `CausalInference/Attribution` | Probabilities of necessity, sufficiency, and both: probabilities of disablement and enablement; identification under weak exogeneity and monotonicity, with a countermodel for the results that need the strong form; sharp bounds from experimental and combined data, with the exact feasibility conditions on combined data; non-identification; textbook examples |
| `CausalInference/Bias` | Selection bias and conditioning on a collider, selection without bias, the built-in selection bias of hazard ratios, measurement error and misclassification with correction formulas |
| `CausalInference/BiasAnalysis` | Quantitative bias analysis on tables: external adjustment for an unmeasured confounder (bias factor, cell projection, the Mantel and Haenszel summary, Flanders and Khoury bounds, E-values and G-values, signed rules); misclassification (predictive values and their dependence on prevalence, validation designs, correction of differential and non-differential exposure and outcome error with admissibility regions, bias toward the null on ratio scales with counterexamples, the matrix method for joint and polytomous classification, dependent errors); selection bias adjustment by selection odds ratio, projection, and weighting, with their agreement, bounds over unknown participation, and loss to follow-up; measurement error in continuous variables (attenuation by the reliability ratio, regression calibration, Berkson error, outcome error, two mismeasured covariates); first-order variance formulas for bias-adjusted estimates (Woolf, Greenland, Marshall), predictive value weighting, the jackknife, Rubin's rules, inverse-variance pooling; several biases adjusted in series (confounding, selection, misclassification), with the conditions under which the order of corrections matters; probability distributions for bias parameters (beta moments and mode, uniform and normal draws, the trapezoidal distribution, sampling by the quantile transform); Bayesian bias analysis (the misclassification likelihood and its non-identifiability, beta and binomial conjugacy, Gibbs full conditionals, invariance of the target under the Metropolis kernel, binomial thinning); worked examples recomputed from published inputs |
| `CausalInference/Survival` | Discrete-time survival, hazards and the product formula, independent censoring and the product-limit functional under equality of hazards among the uncensored, with non-identification counterexamples without independence and without support, hazard ratios against survival, the Kaplan-Meier estimator as the product limit of the empirical law |
| `CausalInference/MissingData` | Missingness mechanisms, inverse probability weighting and its augmented form, regression identities, identification of the mean from the observed law under missingness at random, non-identification counterexamples without it and without positivity |
| `CausalInference/Sensitivity` | Rosenbaum bounds for sign and signed-rank statistics, bias formulas for unmeasured confounding, the bounding factor and the E-value |
| `CausalInference/Estimation` | Independent samples, consistency with continuous mapping, asymptotic linearity and its closure properties, asymptotic normality, the delta method, Wald interval coverage with an estimated scale, consistency of the sample covariance ratio and the sample Wald ratio for instrumental variables under a nonzero first stage |

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
