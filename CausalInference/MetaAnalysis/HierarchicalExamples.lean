/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ConjugateBetaBinomial
public import CausalInference.MetaAnalysis.ConjugateGammaPoisson
public import CausalInference.MetaAnalysis.HierarchicalEmpiricalBayes
public import CausalInference.MetaAnalysis.RestrictedContrast
public import CausalInference.MetaAnalysis.RestrictedLikelihoodUnimodal
public import CausalInference.MetaAnalysis.Exchangeable
public import CausalInference.MetaAnalysis.ConjugateMultivariateNormal

/-!
# Worked numbers for conjugate updates, shrinkage and restricted likelihood

* **Normal sample** (`hierExample_normal`): `n = 4` observations of variance `1` and the prior
  `N(0, 1)`: posterior precision `1 + 4 = 5`, prior weight `B = 1/5`; for the data
  `(1, 2, 3, 6)` with mean `3` the posterior mean is `(4/5) · 3 = 12/5`.
* **Multivariate normal** (`hierExample_multivariateNormal`): in two dimensions with
  `Σ₀ = Σ = I`, three observations give the posterior precision `I + 3 I = 4 I`, and with
  `m₀ = 0` the posterior mean is `(1/4) ∑ⱼ yⱼ`.
* **Beta and binomial** (`hierExample_betaBinomial`): the prior `Beta(1, 1)` and `7` successes in
  `10` trials give `Beta(8, 4)`, posterior mean `2/3`; Laplace's rule gives `(7 + 1)/(10 + 2)`.
* **Gamma and Poisson** (`hierExample_gammaPoisson`): the prior `Gamma(2, 1)` and the counts
  `(1, 2, 3)` give `Gamma(8, 4)`, posterior mean `2`.
* **Shrinkage** (`hierExample_shrinkage`): `v = 1`, `τ² = 1` give `B = 1/2`; the mean squared
  error averaged over the units is `1/2` against `1` unshrunk; a fixed unit loses exactly when
  `(θ - μ)² > 3`.
* **REML and ML** (`hierExample_reml`): for `y = (0, 1, 2)`, `S = 2`, the REML estimate is
  `S/2 = 1` and the ML estimate is `S/3 = 2/3`.
* **Spread condition** (`hierExample_spread`): three studies of variance `1` with estimates
  `(0, 1/2, 1/4)` have squared differences at most `1/4 < 1 - 1/3`, so the restricted likelihood
  is maximized only at `τ² = 0`.
* **The urn** (`hierExample_urn`): each of the two outcomes has probability `1/2`, and the event
  of equal draws has probability `0`.

## Main results

* `hierExample_normal`, `hierExample_multivariateNormal`, `hierExample_betaBinomial`,
  `hierExample_gammaPoisson`, `hierExample_shrinkage`, `hierExample_reml`, `hierExample_spread`,
  `hierExample_urn`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory BiasAnalysis.Bayesian
open scoped ENNReal

/-- Four observations of variance `1` with the prior `N(0, 1)`: precision `5`, weight `1/5`. -/
theorem hierExample_normal :
    posteriorPrecision 1 (fun _ : Fin 4 => (1 : ℝ)) = 5 ∧ priorWeight 1 1 4 = 1 / 5 ∧
      posteriorMean 0 1 (fun _ : Fin 4 => (1 : ℝ)) ![1, 2, 3, 6] = 12 / 5 := by
  have hB : priorWeight 1 1 4 = 1 / 5 := by simp only [priorWeight]; norm_num
  refine ⟨?_, hB, ?_⟩
  · rw [posteriorPrecision_equalVar]; norm_num
  · rw [posteriorMean_equalVar one_pos one_pos]
    simp only [Fintype.card_fin, hB]
    simp [regMean, Fin.sum_univ_four]
    norm_num

/-- Two dimensions, `Σ₀ = Σ = I`, three observations: precision `4 I`, and with `m₀ = 0` the
posterior mean `(1/4) ∑ⱼ yⱼ`. -/
theorem hierExample_multivariateNormal (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    posteriorPrecisionMat (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 3 = (4 : ℝ) • 1 ∧
      posteriorMeanVec 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 y =
        (4 : ℝ)⁻¹ • ∑ j, WithLp.ofLp (y j) := by
  have hP : posteriorPrecisionMat (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 3 = (4 : ℝ) • 1 := by
    rw [posteriorPrecisionMat, inv_one, show (4 : ℝ) = 1 + 3 by norm_num, add_smul, one_smul]
    norm_num
  have hinv : ((4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = (4 : ℝ)⁻¹ • 1 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul,
      Matrix.mul_one]
  refine ⟨hP, ?_⟩
  rw [posteriorMeanVec, Fintype.card_fin, hP, hinv, inv_one]
  simp [Matrix.smul_mulVec]

/-- `Beta(1, 1)` and `7` successes in `10` trials: the posterior is `Beta(8, 4)` with mean
`2/3`, which is also Laplace's predictive probability `(7 + 1)/(10 + 2)`. -/
theorem hierExample_betaBinomial :
    normalizedPosterior (betaMeasure 1 1) (fun x => ENNReal.ofReal (binomPMF 10 x 7)) =
        betaMeasure 8 4 ∧
      ∫ p, p ∂normalizedPosterior (betaMeasure 1 1) (fun x => ENNReal.ofReal (binomPMF 10 x 7)) =
        2 / 3 := by
  refine ⟨?_, ?_⟩
  · rw [(betaBinomial_normalizedPosterior one_pos one_pos (by norm_num : 7 ≤ 10)).2]
    norm_num
  · rw [laplace_rule_of_succession (by norm_num : 7 ≤ 10)]
    norm_num

/-- `Gamma(2, 1)` and the counts `(1, 2, 3)`: the posterior is `Gamma(8, 4)` with mean `2`. -/
theorem hierExample_gammaPoisson :
    normalizedPosterior (gammaMeasure 2 1)
        (fun lam => ENNReal.ofReal (poissonLikelihood ![1, 2, 3] lam)) = gammaMeasure 8 4 ∧
      ∫ lam, lam ∂gammaMeasure 8 4 = 2 := by
  refine ⟨?_, ?_⟩
  · rw [(gammaPoisson_posterior two_pos one_pos ![1, 2, 3]).2]
    simp [Fin.sum_univ_three]
    norm_num
  · rw [integral_id_gammaMeasure (by norm_num) (by norm_num)]
    norm_num

/-- `v = 1`, `τ² = 1`: `B = 1/2`, the average mean squared error is `1/2 < 1`, and a fixed unit
loses exactly when `(θ - μ)² > 3`. -/
theorem hierExample_shrinkage :
    shrinkageFactor 1 1 = 1 / 2 ∧ (1 : ℝ) * 1 / (1 + 1) = 1 / 2 ∧ (1 : ℝ) * 1 / (1 + 1) < 1 ∧
      ∀ d : ℝ, (1 < shrinkageFactor 1 1 ^ 2 * d + (1 - shrinkageFactor 1 1) ^ 2 * 1 ↔ 3 < d) := by
  refine ⟨by norm_num [shrinkageFactor], by norm_num, by norm_num, fun d => ?_⟩
  rw [shrinkage_mse_gt_iff one_pos zero_le_one]
  norm_num

/-- For `y = (0, 1, 2)`: `S = 2`, the REML estimate `S/(n-1) = 1`, the ML estimate
`S/n = 2/3`. -/
theorem hierExample_reml :
    regSxx ![(0 : ℝ), 1, 2] = 2 ∧
      regSxx ![(0 : ℝ), 1, 2] / (Fintype.card (Fin 3) - 1) = 1 ∧
      regSxx ![(0 : ℝ), 1, 2] / Fintype.card (Fin 3) = 2 / 3 := by
  have h : regSxx ![(0 : ℝ), 1, 2] = 2 := by
    simp [regSxx, regMean, Fin.sum_univ_three]
    norm_num
  refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> norm_num

/-- Three studies of variance `1` with estimates `(0, 1/2, 1/4)`: the restricted likelihood is
maximized only at `τ² = 0`. -/
theorem hierExample_spread {t : ℝ} (ht : 0 < t) :
    restrictedLogLik (fun _ : Fin 3 => (1 : ℝ)) ![0, 1 / 2, 1 / 4] t <
      restrictedLogLik (fun _ : Fin 3 => (1 : ℝ)) ![0, 1 / 2, 1 / 4] 0 := by
  refine restrictedLogLik_lt_zero_of_spread (vmin := 1) (vmax := 1)
    (D := 1 / 4) (fun _ => le_rfl) (fun _ => le_rfl) (fun i j => ?_) (by norm_num) ht
  fin_cases i <;> fin_cases j <;> norm_num

/-- The urn: each outcome has probability `1/2`, equal draws have probability `0`. -/
theorem hierExample_urn :
    urnLaw {![true, false]} = 2⁻¹ ∧ urnLaw {x | x 0 = x 1} = 0 := by
  refine ⟨?_, ?_⟩
  · simp [urnLaw, Measure.dirac_apply', Set.indicator]
  · have hE : MeasurableSet {x : Fin 2 → Bool | x 0 = x 1} := (Set.toFinite _).measurableSet
    simp [urnLaw, Measure.dirac_apply' _ hE, Set.indicator]

end MetaAnalysis

end CausalInference
