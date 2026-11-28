/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MaximumLikelihoodNormality
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The normal location family

The family `N(θ, 1)`, `θ ∈ ℝ`, of normal laws with unit variance, as a `ParametricFamily` on `ℝ`
dominated by Lebesgue measure. It is the basic instance on a sample space that is not discrete.

## Main definitions

* `CausalInference.ParametricFamily.normalLocation`: the family, with density
  `(2π)^{-1/2} exp(-(x - θ)²/2)` and `Θ = ℝ`.

## Main results

* `normalLocation_law`: the law of one observation is `gaussianReal θ 1`.
* `normalLocation_score`, `normalLocation_hessLogLik`, `normalLocation_fisherInfo`: the score is
  `x - θ`, the second derivative of the log density is `-1`, and the information is `1`.
* `normalLocation_isRegularAt`: the family is regular at every `θ₀`. On the ball of radius `1` the
  first two derivatives of the density are bounded by
  `3 (2π)^{-1/2} e^{1/2} ((x - θ₀)² + 1) exp(-(x - θ₀)²/4)`, which is integrable.
* `normalLocation_isScoreRegular`: the score is smooth on every ball, with envelope `1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Metric Real
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

/-- The normal location family with unit variance on `ℝ`: the density of `N(θ, 1)` with respect
to Lebesgue measure, for every `θ ∈ ℝ`. -/
noncomputable def normalLocation : ParametricFamily ℝ ℝ where
  ν := volume
  Θ := Set.univ
  density θ x := gaussianPDFReal θ 1 x
  measurable_density θ := measurable_gaussianPDFReal θ 1
  density_nonneg θ _ x := gaussianPDFReal_nonneg θ 1 x
  integrable_density θ _ := integrable_gaussianPDFReal θ 1
  integral_density θ _ := integral_gaussianPDFReal_eq_one θ one_ne_zero

/-- The dominating measure of the normal location family is Lebesgue measure, which is
σ-finite. -/
instance sigmaFinite_normalLocation_ν : SigmaFinite normalLocation.ν :=
  inferInstanceAs (SigmaFinite (volume : Measure ℝ))

/-- The density of the normal location family. -/
lemma normalLocation_density (θ x : ℝ) :
    normalLocation.density θ x = (√(2 * π))⁻¹ * exp (-(x - θ) ^ 2 / 2) := by
  change gaussianPDFReal θ 1 x = _
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]

lemma normalLocation_density_pos (θ x : ℝ) : 0 < normalLocation.density θ x :=
  gaussianPDFReal_pos θ 1 x one_ne_zero

/-- The law of one observation is `N(θ, 1)`. -/
lemma normalLocation_law (θ : ℝ) : normalLocation.law θ = gaussianReal θ 1 := by
  rw [gaussianReal_of_var_ne_zero θ one_ne_zero, gaussianPDF_def]
  rfl

lemma normalLocation_hasDerivAt_density (x u : ℝ) :
    HasDerivAt (fun v ↦ normalLocation.density v x) ((x - u) * normalLocation.density u x) u := by
  simp_rw [normalLocation_density]
  have h := ((((hasDerivAt_id' u).const_sub x).fun_pow 2).neg.div_const 2).exp.const_mul
    (√(2 * π))⁻¹
  convert h using 1
  simp only [Pi.neg_apply]
  ring

lemma normalLocation_densityDeriv (u x : ℝ) :
    normalLocation.densityDeriv u x = (x - u) * normalLocation.density u x :=
  (normalLocation_hasDerivAt_density x u).deriv

lemma normalLocation_hasDerivAt_densityDeriv (x u : ℝ) :
    HasDerivAt (fun v ↦ normalLocation.densityDeriv v x)
      (((x - u) ^ 2 - 1) * normalLocation.density u x) u := by
  simp_rw [normalLocation_densityDeriv]
  have h := ((hasDerivAt_id' u).const_sub x).mul (normalLocation_hasDerivAt_density x u)
  convert h using 1
  ring

lemma normalLocation_densityDeriv2 (u x : ℝ) :
    normalLocation.densityDeriv2 u x = ((x - u) ^ 2 - 1) * normalLocation.density u x :=
  (normalLocation_hasDerivAt_densityDeriv x u).deriv

/-- The score of the normal location family is `x - θ`. -/
lemma normalLocation_score (θ x : ℝ) : normalLocation.score θ x = x - θ := by
  rw [score, normalLocation_densityDeriv, mul_div_assoc,
    div_self (normalLocation_density_pos θ x).ne', mul_one]

lemma normalLocation_logLik (u x : ℝ) :
    normalLocation.logLik u x = log (√(2 * π))⁻¹ + -(x - u) ^ 2 / 2 := by
  rw [logLik, normalLocation_density, log_mul (by positivity) (exp_pos _).ne', log_exp]

lemma normalLocation_hasDerivAt_logLik (x u : ℝ) :
    HasDerivAt (fun v ↦ normalLocation.logLik v x) (normalLocation.score u x) u := by
  simp_rw [normalLocation_logLik, normalLocation_score]
  have h := ((((hasDerivAt_id' u).const_sub x).fun_pow 2).neg.div_const 2).const_add
    (log (√(2 * π))⁻¹)
  convert h using 1
  ring

/-- The second derivative of the log density of the normal location family is `-1`. -/
lemma normalLocation_hessLogLik (θ x : ℝ) : normalLocation.hessLogLik θ x = -1 := by
  have e : (fun u ↦ deriv (fun v ↦ normalLocation.logLik v x) u) = fun u ↦ x - u := by
    funext u
    rw [(normalLocation_hasDerivAt_logLik x u).deriv, normalLocation_score]
  rw [hessLogLik, e]
  exact ((hasDerivAt_id' θ).const_sub x).deriv

lemma normalLocation_hasDerivAt_score (x u : ℝ) :
    HasDerivAt (fun v ↦ normalLocation.score v x) (normalLocation.hessLogLik u x) u := by
  simp_rw [normalLocation_score, normalLocation_hessLogLik]
  exact (hasDerivAt_id' u).const_sub x

/-- The information of the normal location family is `1`. -/
theorem normalLocation_fisherInfo (θ : ℝ) : normalLocation.fisherInfo θ = 1 := by
  rw [fisherInfo, normalLocation_law]
  simp_rw [normalLocation_score]
  have h := variance_eq_integral (μ := gaussianReal θ 1) measurable_id.aemeasurable
  simp only [id] at h
  rw [variance_id_gaussianReal, integral_id_gaussianReal] at h
  rw [← h, NNReal.coe_one]

/-- The envelope of the first two derivatives of the normal density near `θ₀` is integrable. -/
lemma integrable_normal_envelope (θ₀ : ℝ) :
    Integrable fun x : ℝ ↦ 3 * ((√(2 * π))⁻¹ * exp (1 / 2)) *
      ((x - θ₀) ^ 2 * exp (-(1 / 4) * (x - θ₀) ^ 2) + exp (-(1 / 4) * (x - θ₀) ^ 2)) := by
  have hE := (integrable_exp_neg_mul_sq (b := 1 / 4) (by norm_num)).comp_sub_right θ₀
  have hP := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 2)
    (by norm_num)).comp_sub_right θ₀
  simp only [rpow_two] at hP
  exact (hP.add hE).const_mul _

/-- **The normal location family is regular** at every `θ₀`. -/
theorem normalLocation_isRegularAt (θ₀ : ℝ) : normalLocation.IsRegularAt θ₀ := by
  set c : ℝ := (√(2 * π))⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set b : ℝ → ℝ := fun x ↦ 3 * (c * exp (1 / 2)) *
    ((x - θ₀) ^ 2 * exp (-(1 / 4) * (x - θ₀) ^ 2) + exp (-(1 / 4) * (x - θ₀) ^ 2)) with hb
  have hbi : Integrable b volume := integrable_normal_envelope θ₀
  have hf : ∀ x, ∀ u ∈ ball θ₀ 1,
      normalLocation.density u x ≤ c * exp (1 / 2) * exp (-(1 / 4) * (x - θ₀) ^ 2) := by
    intro x u hu
    rw [normalLocation_density, mul_assoc, ← exp_add]
    have hu' : |u - θ₀| < 1 := by rwa [mem_ball, dist_eq_norm, Real.norm_eq_abs] at hu
    have hsq : (u - θ₀) ^ 2 < 1 := by nlinarith [abs_nonneg (u - θ₀), sq_abs (u - θ₀)]
    gcongr
    nlinarith [sq_nonneg (x - u - (u - θ₀))]
  have hA : ∀ x, ∀ u ∈ ball θ₀ 1, |x - u| ≤ 3 * ((x - θ₀) ^ 2 + 1) ∧
      |(x - u) ^ 2 - 1| ≤ 3 * ((x - θ₀) ^ 2 + 1) := by
    intro x u hu
    have hu' : |u - θ₀| < 1 := by rwa [mem_ball, dist_eq_norm, Real.norm_eq_abs] at hu
    have h1 : |x - u| ≤ |x - θ₀| + 1 := by
      have := abs_sub_le x θ₀ u
      rw [abs_sub_comm θ₀ u] at this
      linarith
    have h2 : |x - θ₀| ≤ (x - θ₀) ^ 2 + 1 := by
      nlinarith [sq_abs (x - θ₀), abs_nonneg (x - θ₀), sq_nonneg (|x - θ₀| - 1)]
    refine ⟨by nlinarith, ?_⟩
    rw [abs_le]
    have h3 : (x - u) ^ 2 ≤ (|x - θ₀| + 1) ^ 2 := by
      rw [← sq_abs (x - u)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    constructor <;> nlinarith [sq_nonneg (x - u), sq_abs (x - θ₀), abs_nonneg (x - θ₀)]
  have hbd : ∀ x, ∀ u ∈ ball θ₀ 1, |normalLocation.densityDeriv u x| ≤ b x ∧
      |normalLocation.densityDeriv2 u x| ≤ b x := by
    intro x u hu
    have hfu := hf x u hu
    have hpos := (normalLocation_density_pos u x).le
    obtain ⟨h1, h2⟩ := hA x u hu
    have hE : 0 ≤ c * exp (1 / 2) * exp (-(1 / 4) * (x - θ₀) ^ 2) := by positivity
    have e : b x = 3 * ((x - θ₀) ^ 2 + 1) * (c * exp (1 / 2) * exp (-(1 / 4) * (x - θ₀) ^ 2)) :=
      by rw [hb]; ring
    rw [normalLocation_densityDeriv, normalLocation_densityDeriv2, abs_mul, abs_mul,
      abs_of_nonneg hpos, e]
    exact ⟨mul_le_mul h1 hfu hpos (by positivity), mul_le_mul h2 hfu hpos (by positivity)⟩
  refine ⟨Eventually.of_forall fun u x ↦ iff_of_true (normalLocation_density_pos u x)
    (normalLocation_density_pos θ₀ x), ⟨1, one_pos, Set.subset_univ _, ae_of_all _ fun x ↦ ?_,
    b, b, hbi, hbi, ae_of_all _ fun x u hu ↦ hbd x u hu⟩, ?_⟩
  · simp_rw [normalLocation_density]
    exact (contDiff_const.mul (((contDiff_const.sub contDiff_id).pow 2).neg.div_const 2).exp)
      |>.contDiffOn
  · rw [normalLocation_law]
    have e : normalLocation.score θ₀ = fun x ↦ id x - θ₀ := funext (normalLocation_score θ₀)
    rw [e]
    exact (memLp_id_gaussianReal' 2 (by norm_num)).sub (memLp_const θ₀)

/-- **The score of the normal location family is smooth** on every ball: the score is
`x - θ`, measurable, with derivative `-1`, bounded by the envelope `1`. -/
theorem normalLocation_isScoreRegular (θ₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    normalLocation.IsScoreRegular θ₀ r := by
  have := isProbabilityMeasure_law (F := normalLocation) (θ := θ₀) (Set.mem_univ _)
  have eh : ∀ θ, normalLocation.hessLogLik θ = fun _ ↦ -1 :=
    fun θ ↦ funext (normalLocation_hessLogLik θ)
  refine ⟨hr, ?_, fun θ _ ↦ by rw [eh]; exact measurable_const,
    ae_of_all _ fun x θ _ ↦ normalLocation_hasDerivAt_score x θ, ae_of_all _ fun x ↦ ?_,
    ⟨fun _ ↦ 1, integrable_const _, ae_of_all _ fun x θ _ ↦ ?_⟩⟩
  · have e : normalLocation.score θ₀ = fun x ↦ x - θ₀ := funext (normalLocation_score θ₀)
    rw [e]
    exact measurable_id.sub_const _
  · simp_rw [normalLocation_hessLogLik]
    exact continuousOn_const
  · rw [normalLocation_hessLogLik]
    norm_num

end ParametricFamily

end CausalInference
