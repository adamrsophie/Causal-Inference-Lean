/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.Examples
public import CausalInference.MetaAnalysis.DerSimonianLaird
public import CausalInference.MetaAnalysis.HartungKnapp
public import CausalInference.MetaAnalysis.Conjugacy
public import CausalInference.MetaAnalysis.RestrictedLikelihood
public import CausalInference.MetaAnalysis.Egger

/-!
# Meta-analysis: worked random effects examples

The three study example of `MetaAnalysis.Examples` (estimates `y = (0, 1, 2)`, within-study
variances `v = (1, 1/2, 1/4)`, weights `(1, 2, 4)`, `∑ wᵢ = 7`, `Q = 26/7`, `c = 4`), continued
with the random effects analysis, every number recomputed:

* **DerSimonian-Laird**: `τ̂²_DL = (26/7 - 2) / 4 = 3/7` (`example_dlTau2`); the random effects
  weights `1 / (vᵢ + 3/7)` are `(7/10, 14/13, 28/19)` with sum `8029/2470`, the DerSimonian-Laird
  pooled estimate is `1420/1147` (`example_dlEstimate`), `Q` with these weights is `2282/1147`
  and the Hartung-Knapp variance estimate is `402610/1315609`
  (`example_hartungKnappVariance`).
* **The random effects model on the example**: on the concrete product space every theorem of
  the random effects files applies with all hypotheses verified: the marginal law, `E[Q]`,
  unbiasedness of the untruncated estimator and the strict bias of the truncated one, the exact
  `t₂` law and coverage of the Hartung-Knapp interval (`example_randomEffectsModel`,
  `example_dlTau2_bias`, `example_hartungKnapp`).
* **Identification** (`example_pointIdentified`, `example_not_pointIdentified_empty`,
  `example_one_study`).
* **Conjugacy**: with `τ² = 0` and the prior `N(0, 1)`, the posterior precision is `1 + 7 = 8` and
  the posterior mean is `(0 + 7 · 10/7) / 8 = 5/4` (`example_posterior`).
* **Restricted likelihood**: the first order conditions and the integrated likelihood identity
  hold on the example (`example_restrictedLogLik`).
* **Egger**: with standard errors `(1, 1/2, 1/4)` and estimates `(0, 1, 2)` the precisions are
  `(1, 2, 4)`, the standardized effects `(0, 2, 8)`, the slope `19/7` and the Egger intercept
  `-3` (`example_eggerIntercept`); with standard errors `√vᵢ` of the example the Egger statistic
  has the exact null law `t₁` (`example_hasLaw_eggerStat`).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset PopulationAdjustment

/-! ### Numbers -/

theorem example_dlTau2Untruncated : dlTau2Untruncated exampleVar exampleY = 3 / 7 := by
  rw [dlTau2Untruncated, example_cochranQ, example_cochranQSlope]
  norm_num

/-- `τ̂²_DL = 3/7` on the example: `Q = 26/7 > k - 1 = 2`, so the truncation is not active. -/
theorem example_dlTau2 : dlTau2 exampleVar exampleY = 3 / 7 := by
  rw [dlTau2, example_dlTau2Untruncated]
  norm_num

theorem example_sum_ivWeight_dl :
    ∑ i, ivWeight (fun i => exampleVar i + 3 / 7) i = 8029 / 2470 := by
  norm_num [ivWeight, exampleVar, Fin.sum_univ_three]

/-- The DerSimonian-Laird pooled estimate of the example is `1420/1147`. -/
theorem example_dlEstimate : dlEstimate exampleVar exampleY = 1420 / 1147 := by
  rw [dlEstimate, example_dlTau2, ivwEstimate, weightedMean]
  norm_num [ivWeight, exampleVar, exampleY, Fin.sum_univ_three]

/-- With the DerSimonian-Laird weights, `Q = 2282/1147` and the Hartung-Knapp variance estimate
is `2282/1147 / (2 · 8029/2470) = 402610/1315609`. -/
theorem example_hartungKnappVariance :
    cochranQ (fun i => exampleVar i + 3 / 7) exampleY = 2282 / 1147 ∧
      hartungKnappVariance (fun i => exampleVar i + 3 / 7) exampleY = 402610 / 1315609 := by
  have hQ : cochranQ (fun i => exampleVar i + 3 / 7) exampleY = 2282 / 1147 := by
    rw [cochranQ, ivwEstimate, weightedMean]
    norm_num [ivWeight, exampleVar, exampleY, Fin.sum_univ_three]
  refine ⟨hQ, ?_⟩
  rw [hartungKnappVariance, hQ, example_sum_ivWeight_dl]
  norm_num

/-! ### The random effects model on the example -/

/-- The concrete product space of the example: study effects `⊗ᵢ N(0, τ²)` and errors
`⊗ᵢ N(0, vᵢ)` with the variances of the example. -/
noncomputable abbrev exampleREMeasure (τ2 : ℝ) : Measure ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
  (Measure.pi fun _ : Fin 3 => gaussianReal 0 τ2.toNNReal).prod
    (Measure.pi fun i => gaussianReal 0 (exampleVar i).toNNReal)

theorem example_isGaussianRandomEffectsModel {τ2 : ℝ} (hτ : 0 ≤ τ2) :
    IsGaussianRandomEffectsModel (exampleREMeasure τ2) (fun i ω => ω.1 i) (fun i ω => ω.2 i)
      τ2 exampleVar :=
  isGaussianRandomEffectsModel_prod exampleVar_pos hτ

/-- **The random effects model on the example**: for `τ² ≥ 0`, the estimates
`Yᵢ = θ + bᵢ + εᵢ` have the law `⊗ᵢ N(θ, vᵢ + τ²)`, form a Gaussian common effect model with
these variances, `E[Q] = 2 + 4 τ²`, and the random effects pooled estimate is unbiased with
variance `1 / ∑ᵢ 1 / (vᵢ + τ²)`. -/
theorem example_randomEffectsModel (θ : ℝ) {τ2 : ℝ} (hτ : 0 ≤ τ2) :
    HasLaw (fun ω i => θ + ω.1 i + ω.2 i)
        (Measure.pi fun i => gaussianReal θ (exampleVar i + τ2).toNNReal) (exampleREMeasure τ2) ∧
      IsGaussianCommonEffectModel (exampleREMeasure τ2) (fun i ω => θ + ω.1 i + ω.2 i) θ
        (fun i => exampleVar i + τ2) ∧
      ∫ ω, cochranQ exampleVar (fun i => θ + ω.1 i + ω.2 i) ∂exampleREMeasure τ2 =
        2 + 4 * τ2 ∧
      ∫ ω, ivwEstimate (fun i => exampleVar i + τ2) (fun i => θ + ω.1 i + ω.2 i)
        ∂exampleREMeasure τ2 = θ := by
  have h := example_isGaussianRandomEffectsModel hτ
  refine ⟨h.hasLaw_pi θ, h.isGaussianCommonEffectModel θ, ?_,
    (h.isRandomEffectsModel.integral_variance_ivwEstimate θ).1⟩
  rw [(h.isRandomEffectsModel.integral_cochranQ θ).2, example_cochranQSlope]
  norm_num
  ring

/-- **The DerSimonian-Laird estimator on the example**: for every `τ² ≥ 0`, the untruncated
estimator is unbiased and the truncated one is strictly biased upward. -/
theorem example_dlTau2_bias (θ : ℝ) {τ2 : ℝ} (hτ : 0 ≤ τ2) :
    ∫ ω, dlTau2Untruncated exampleVar (fun i => θ + ω.1 i + ω.2 i) ∂exampleREMeasure τ2 = τ2 ∧
      τ2 < ∫ ω, dlTau2 exampleVar (fun i => θ + ω.1 i + ω.2 i) ∂exampleREMeasure τ2 :=
  (example_isGaussianRandomEffectsModel hτ).lt_integral_dlTau2 (by simp) θ

/-- **The Hartung-Knapp interval on the example**: with known `τ² ≥ 0` and the random effects
weights, the statistic has the exact law `t₂` and the interval `θ̂ ± c √V̂` covers `θ` with
probability `t₂([-c, c])`. -/
theorem example_hartungKnapp (θ c : ℝ) {τ2 : ℝ} (hτ : 0 ≤ τ2) :
    HasLaw (fun ω => hartungKnappStat (fun i => exampleVar i + τ2) θ
        fun i => θ + ω.1 i + ω.2 i) (studentT 2) (exampleREMeasure τ2) ∧
      exampleREMeasure τ2 {ω | |ivwEstimate (fun i => exampleVar i + τ2)
          (fun i => θ + ω.1 i + ω.2 i) - θ| ≤
        c * √(hartungKnappVariance (fun i => exampleVar i + τ2) fun i => θ + ω.1 i + ω.2 i)} =
        studentT 2 (Set.Icc (-c) c) := by
  have h := example_isGaussianRandomEffectsModel hτ
  exact ⟨h.hasLaw_hartungKnappStat (by simp) (by norm_num) θ,
    h.measure_hartungKnapp_coverage (by simp) (by norm_num) θ c⟩

/-! ### Identification -/

/-- `(θ, τ²)` is point identified for the variances of the example. -/
theorem example_pointIdentified :
    PointIdentified {p : ℝ × ℝ | 0 ≤ p.2}
      (fun p => Measure.pi fun i => gaussianReal p.1 (exampleVar i + p.2).toNNReal) id :=
  pointIdentified_randomEffects exampleVar_pos

/-- With no study `(θ, τ²)` is not identified. -/
theorem example_not_pointIdentified_empty :
    ¬ PointIdentified {p : ℝ × ℝ | 0 ≤ p.2}
      (fun p => Measure.pi fun _ : Fin 0 => gaussianReal p.1 (1 + p.2).toNNReal) id :=
  not_pointIdentified_randomEffects_of_isEmpty fun _ => 1

/-- With one study of variance `1`, `Q` vanishes and the slope is `0`, whatever the data. -/
theorem example_one_study (y : Fin 1 → ℝ) :
    cochranQ (fun _ : Fin 1 => (1 : ℝ)) y = 0 ∧ cochranQSlope (fun _ : Fin 1 => (1 : ℝ)) = 0 :=
  ⟨cochranQ_of_card_eq_one (fun _ => one_pos) (by simp) y,
    cochranQSlope_of_card_eq_one (fun _ => one_pos) (by simp)⟩

/-! ### Conjugacy -/

/-- **Conjugacy on the example**: with `τ² = 0` and the prior `N(0, 1)`, the posterior precision
is `8`, the posterior mean `5/4`, and the posterior is `N(5/4, 1/8)`. -/
theorem example_posterior :
    posteriorPrecision 1 exampleVar = 8 ∧ posteriorMean 0 1 exampleVar exampleY = 5 / 4 ∧
      (∫⁻ θ, ENNReal.ofReal (commonEffectLikelihood exampleVar θ exampleY)
          ∂gaussianReal 0 (1 : ℝ).toNNReal)⁻¹ •
          (gaussianReal 0 (1 : ℝ).toNNReal).withDensity
            (fun θ => ENNReal.ofReal (commonEffectLikelihood exampleVar θ exampleY)) =
        gaussianReal (5 / 4) (1 / 8 : ℝ).toNNReal := by
  have hP : posteriorPrecision 1 exampleVar = 8 := by
    rw [posteriorPrecision, example_sum_ivWeight]; norm_num
  have hM : posteriorMean 0 1 exampleVar exampleY = 5 / 4 := by
    rw [posteriorMean, hP, example_sum_ivWeight, example_ivwEstimate]; norm_num
  refine ⟨hP, hM, ?_⟩
  have h := (posterior_commonEffectLikelihood (θ0 := 0) one_pos exampleVar_pos exampleY).2.2
  rwa [hM, posteriorVariance, hP] at h

/-! ### Restricted likelihood -/

/-- **The restricted likelihood on the example**: the first order conditions hold, and at
`t = 0` the integrated likelihood is `√(2π) (√(2π))⁻³ exp(ℓ_R(0))`. -/
theorem example_restrictedLogLik :
    (∀ t, 0 < t → IsMaxOn (restrictedLogLik exampleVar exampleY) (Set.Ici 0) t →
        ∑ i, ivWeight (fun i => exampleVar i + t) i ^ 2 *
            (exampleY i - ivwEstimate (fun i => exampleVar i + t) exampleY) ^ 2 =
          cochranQSlope fun i => exampleVar i + t) ∧
      ∫ θ, commonEffectLikelihood (fun i => exampleVar i + 0) θ exampleY =
        √(2 * Real.pi) * (√(2 * Real.pi))⁻¹ ^ 3 *
          Real.exp (restrictedLogLik exampleVar exampleY 0) := by
  refine ⟨(restrictedLogLik_firstOrder exampleVar_pos exampleY).2.1, ?_⟩
  have h := integral_commonEffectLikelihood (v := exampleVar) (t := 0)
    (fun i => by simpa using exampleVar_pos i) exampleY
  simpa using h

/-! ### Egger -/

/-- **The Egger intercept on data**: standard errors `(1, 1/2, 1/4)` and estimates `(0, 1, 2)`
give precisions `(1, 2, 4)`, standardized effects `(0, 2, 8)`, slope `19/7` and intercept `-3`. -/
theorem example_eggerIntercept :
    regSlope (fun i => 1 / (![1, 1 / 2, 1 / 4] : Fin 3 → ℝ) i)
        (fun i => exampleY i / (![1, 1 / 2, 1 / 4] : Fin 3 → ℝ) i) = 19 / 7 ∧
      eggerIntercept ![1, 1 / 2, 1 / 4] exampleY = -3 := by
  have hm : regMean (fun i => 1 / (![1, 1 / 2, 1 / 4] : Fin 3 → ℝ) i) = 7 / 3 := by
    rw [regMean]; norm_num [Fin.sum_univ_three]
  have hS : regSxx (fun i => 1 / (![1, 1 / 2, 1 / 4] : Fin 3 → ℝ) i) = 14 / 3 := by
    rw [regSxx, hm]; norm_num [Fin.sum_univ_three]
  have hb : regSlope (fun i => 1 / (![1, 1 / 2, 1 / 4] : Fin 3 → ℝ) i)
      (fun i => exampleY i / (![1, 1 / 2, 1 / 4] : Fin 3 → ℝ) i) = 19 / 7 := by
    rw [regSlope, hS, hm]; norm_num [exampleY, Fin.sum_univ_three]
  refine ⟨hb, ?_⟩
  rw [eggerIntercept, regIntercept, hb, hm, regMean]
  norm_num [exampleY, Fin.sum_univ_three]

/-- **Egger's test on the example, with all hypotheses verified**: in the Gaussian common effect
model with the variances of the example (standard errors `√vᵢ`, two of which differ), the Egger
statistic has the exact null law `t₁`. -/
theorem example_hasLaw_eggerStat (θ : ℝ) :
    HasLaw (eggerStat fun i => √(exampleVar i)) (studentT 1)
      (Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal) := by
  have hse : ∀ i, 0 < √(exampleVar i) := fun i => Real.sqrt_pos.2 (exampleVar_pos i)
  have hv : (fun i => √(exampleVar i) ^ 2) = exampleVar :=
    funext fun i => Real.sq_sqrt (exampleVar_pos i).le
  have h : IsGaussianCommonEffectModel
      (Measure.pi fun i => gaussianReal θ (exampleVar i).toNNReal)
      (fun i x => x i) θ (fun i => √(exampleVar i) ^ 2) := by
    convert isGaussianCommonEffectModel_pi exampleVar_pos θ
  have hd : ∃ i j, √(exampleVar i) ≠ √(exampleVar j) := ⟨0, 2, by
    simp only [exampleVar, Matrix.cons_val_zero, Real.sqrt_one]
    rw [show (![1, 1 / 2, 1 / 4] : Fin 3 → ℝ) 2 = 1 / 4 from rfl,
      show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num⟩
  exact h.hasLaw_eggerStat hse hd (by simp) le_rfl

end MetaAnalysis

end CausalInference
