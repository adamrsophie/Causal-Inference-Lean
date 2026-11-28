/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolution
public import CausalInference.Estimation.BernoulliLikelihoodTests

/-!
# The Hájek convolution bound for the Bernoulli family

For the Bernoulli family at an interior point `p₀ ∈ (0, 1)` every hypothesis of the local
asymptotic normality, regularity and convolution theorems is checked: the point is regular
(`bernoulli_isRegularAt`), the score is regular on the closed ball of radius
`min p₀ (1 - p₀) / 2` (`bernoulli_isScoreRegular`), the log density has derivative the score on
that ball, and the information `I(p₀) = 1 / (p₀ (1 - p₀))` is positive.

The efficient influence function is `I(p₀)⁻¹ s(p₀; x) = x - p₀`, so the sample proportion is
asymptotically linear in it; hence it is regular in Hájek's sense with limit
`N(0, p₀ (1 - p₀))` and attains the bound `I(p₀)⁻¹ = p₀ (1 - p₀)`. At `p₀ = 1/4` the
information is `16/3` and the bound is `3/16`.

## Main results

* `CausalInference.ParametricFamily.bernoulli_logLikRatio_sub_tendstoInMeasure`: local asymptotic
  normality of the Bernoulli family.
* `CausalInference.ParametricFamily.bernoulliSampleMean_isAsymptoticallyLinear`: the sample
  proportion is asymptotically linear with the efficient influence function `x - p₀`.
* `CausalInference.ParametricFamily.bernoulliSampleMean_isHajekRegular`: it is regular with limit
  `N(0, p₀ (1 - p₀))`.
* `CausalInference.ParametricFamily.bernoulli_hajek_convolution_bound`: every regular estimator
  with limit `N(0, V)` has `p₀ (1 - p₀) ≤ V`; at `p₀ = 1/4`, `3/16 ≤ V`.
* `CausalInference.ParametricFamily.bernoulliSampleMean_attains_hajek_bound`: the sample
  proportion attains the bound, and the equality case of the convolution theorem holds for it.

References: J. Hájek (1970), *A characterization of limiting distributions of regular
estimates*, Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete; A. W. van der
Vaart (1998), *Asymptotic Statistics*, chapter 8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

namespace ParametricFamily

variable {p₀ : ℝ}

/-- The log density of the Bernoulli family has derivative the score on the closed ball of radius
`min p₀ (1 - p₀) / 2`. -/
theorem bernoulli_hasDerivAt_logLik_closedBall (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᵐ z ∂bernoulli.law p₀, ∀ θ ∈ closedBall p₀ (min p₀ (1 - p₀) / 2),
      HasDerivAt (fun u ↦ bernoulli.logLik u z) (bernoulli.score θ z) θ :=
  ae_of_all _ fun z _ ht ↦ bernoulli_hasDerivAt_logLik (mem_Ioo_of_mem_closedBall hp ht) z

/-- The inverse Bernoulli information is `p₀ (1 - p₀)`. -/
theorem bernoulli_inv_fisherInfo (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    (bernoulli.fisherInfo p₀)⁻¹ = p₀ * (1 - p₀) := by
  rw [bernoulli_fisherInfo hp, one_div, inv_inv]

/-- **The efficient influence function of the Bernoulli family** is
`I(p₀)⁻¹ s(p₀; x) = x - p₀`. -/
theorem bernoulli_inv_fisherInfo_mul_score (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) (x : Bool) :
    (bernoulli.fisherInfo p₀)⁻¹ * bernoulli.score p₀ x = successIndicator x - p₀ := by
  have h1 : 1 - p₀ ≠ 0 := by linarith [hp.2]
  have h0 : p₀ ≠ 0 := hp.1.ne'
  rw [bernoulli_inv_fisherInfo hp, bernoulli_score_eq]
  cases x <;> simp [successIndicator] <;> field_simp

/-- The Bernoulli information at `p₀ = 1/4` is `16/3`. -/
theorem bernoulli_fisherInfo_quarter : bernoulli.fisherInfo (1 / 4) = 16 / 3 := by
  rw [bernoulli_fisherInfo ⟨by norm_num, by norm_num⟩]
  norm_num

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → Bool}

/-- **Local asymptotic normality of the Bernoulli family**: on an i.i.d. Bernoulli(`p₀`) sample,
the log likelihood ratio of `p₀ + h/√n` against `p₀` is
`h S_n - h² / (2 p₀ (1 - p₀)) + o_P(1)`. -/
theorem bernoulli_logLikRatio_sub_tendstoInMeasure (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) (h : ℝ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ bernoulli.logLikRatio O p₀ (p₀ + h / √(n : ℝ)) n ω -
      (h * ((√(n : ℝ))⁻¹ * ∑ i ∈ range n, bernoulli.score p₀ (O i ω)) -
        h ^ 2 * (1 / (p₀ * (1 - p₀))) / 2)) atTop 0 := by
  rw [← bernoulli_fisherInfo hp]
  exact logLikRatio_sub_tendstoInMeasure hO hlaw (bernoulli_isRegularAt hp)
    (bernoulli_isScoreRegular hp) (bernoulli_hasDerivAt_logLik_closedBall hp) h

omit [IsProbabilityMeasure μ] in
/-- The sample proportion of the first `n` observations is the sample mean of the success
indicator. -/
theorem bernoulliSampleMean_eq_sampleMean (n : ℕ) (ω : Ω) :
    bernoulliSampleMean n (fun i ↦ O i ω) = sampleMean successIndicator O n ω := by
  rw [bernoulliSampleMean, sampleMean, ← Fin.sum_univ_eq_sum_range
    (fun i ↦ successIndicator (O i ω))]

/-- **The sample proportion is asymptotically linear in the efficient influence function**
`I(p₀)⁻¹ s(p₀; ·)`, on an i.i.d. Bernoulli(`p₀`) sample. -/
theorem bernoulliSampleMean_isAsymptoticallyLinear (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    IsAsymptoticallyLinear (fun n ω ↦ bernoulliSampleMean n fun i ↦ O i ω) p₀
      (fun x ↦ (bernoulli.fisherInfo p₀)⁻¹ * bernoulli.score p₀ x) O μ := by
  have hm : Measurable successIndicator := .of_discrete
  have h2 : MemLp (fun ω ↦ successIndicator (O 0 ω)) 2 μ := by
    refine memLp_of_bounded (a := 0) (b := 1) (Eventually.of_forall fun ω ↦ ?_)
      (hm.comp_aemeasurable (hO.aemeasurable 0)).aestronglyMeasurable 2
    simp only [Function.comp_apply, Set.mem_Icc, successIndicator]
    split_ifs <;> norm_num
  have hmean : μ[fun ω ↦ successIndicator (O 0 ω)] = p₀ := by
    have := isProbabilityMeasure_law (F := bernoulli) hp
    rw [← integral_map (hO.aemeasurable 0) hm.aestronglyMeasurable, hlaw]
    exact bernoulli_mean hp
  have hAL := sampleMean_isAsymptoticallyLinear hm h2
  rw [hmean] at hAL
  have hφ : (fun x ↦ (bernoulli.fisherInfo p₀)⁻¹ * bernoulli.score p₀ x) =
      fun x ↦ successIndicator x - p₀ := funext (bernoulli_inv_fisherInfo_mul_score hp)
  have hT : (fun n ω ↦ bernoulliSampleMean n fun i ↦ O i ω) = sampleMean successIndicator O :=
    funext fun n ↦ funext fun ω ↦ bernoulliSampleMean_eq_sampleMean n ω
  rw [hφ, hT]
  exact hAL

/-- **The sample proportion is regular in Hájek's sense** at every `p₀ ∈ (0, 1)`, with limit
`N(0, p₀ (1 - p₀))`: under `p₀ + h/√n`, `√n (p̂_n - p₀ - h/√n)` converges weakly to
`N(0, p₀ (1 - p₀))` for every `h`. -/
theorem bernoulliSampleMean_isHajekRegular (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulli.IsHajekRegular bernoulliSampleMean p₀ (gaussianReal 0 (p₀ * (1 - p₀)).toNNReal) := by
  have := isProbabilityMeasure_law (F := bernoulli) hp
  obtain ⟨Ω', _, P', O', hP', -, hO', hlaw'⟩ := exists_isIIDSample (bernoulli.law p₀)
  rw [← bernoulli_inv_fisherInfo hp]
  exact isHajekRegular_of_isAsymptoticallyLinear hO' (hlaw' 0).map_eq (bernoulli_isRegularAt hp)
    (bernoulli_isScoreRegular hp) (bernoulli_hasDerivAt_logLik_closedBall hp)
    (bernoulli_fisherInfo_pos hp) measurable_bernoulliSampleMean
    (bernoulliSampleMean_isAsymptoticallyLinear hO' (hlaw' 0).map_eq hp)

/-- **Change of measure for a Bernoulli sample**: for `p₀, p ∈ (0, 1)`, integrating `g` of the
first `n` observations of an i.i.d. Bernoulli(`p₀`) sample against `e^{Λ}` gives the integral of
`g` under the Bernoulli(`p`) sample family. -/
theorem bernoulli_lintegral_mul_exp_logLikRatio (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) {p : ℝ}
    (hp' : p ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) {g : (Fin n → Bool) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g (fun i ↦ O i ω) * ENNReal.ofReal (Real.exp (bernoulli.logLikRatio O p₀ p n ω)) ∂μ =
      ∫⁻ x, g x ∂(bernoulli.pi n).law p :=
  lintegral_mul_exp_logLikRatio hO hlaw hp hp'
    (fun x ↦ ⟨fun _ ↦ bernoulli_density_pos hp x, fun _ ↦ bernoulli_density_pos hp' x⟩) n hg

/-- On an i.i.d. Bernoulli(`p₀`) sample, `√n (p̂_n - p₀)` converges in distribution to
`N(0, p₀ (1 - p₀))`, as a consequence of regularity. -/
theorem bernoulliSampleMean_tendstoInDistribution (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (bernoulliSampleMean n (fun i ↦ O i ω) - p₀))
      atTop id (fun _ ↦ μ) (gaussianReal 0 (p₀ * (1 - p₀)).toNNReal) :=
  (bernoulliSampleMean_isHajekRegular hp).tendstoInDistribution hO hlaw hp

/-- **The tilt identity for the sample proportion**: along a subsequence, the sample proportion
and the normalized score converge jointly to a law `μ'` with marginals `N(0, p₀ (1 - p₀))` and
`N(0, I(p₀))` satisfying the tilt identity. -/
theorem bernoulliSampleMean_tilt (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ' : ProbabilityMeasure (ℝ × ℝ),
      TendstoInDistribution (fun k ω ↦
        (√(φ k : ℝ) * (bernoulliSampleMean (φ k) (fun i ↦ O i ω) - p₀),
          (√(φ k : ℝ))⁻¹ * ∑ i ∈ range (φ k), bernoulli.score p₀ (O i ω))) atTop id
        (fun _ ↦ μ) (μ' : Measure (ℝ × ℝ)) ∧
      (μ' : Measure (ℝ × ℝ)).map Prod.fst = gaussianReal 0 (p₀ * (1 - p₀)).toNNReal ∧
      (μ' : Measure (ℝ × ℝ)).map Prod.snd = gaussianReal 0 (bernoulli.fisherInfo p₀).toNNReal ∧
      ∀ h : ℝ, ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + h) ∂gaussianReal 0 (p₀ * (1 - p₀)).toNNReal =
        ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * bernoulli.fisherInfo p₀ / 2)
          ∂(μ' : Measure (ℝ × ℝ)) :=
  hajek_tilt_subseq hO hlaw (bernoulli_isRegularAt hp) (bernoulli_isScoreRegular hp)
    (bernoulli_hasDerivAt_logLik_closedBall hp) (bernoulli_fisherInfo_pos hp)
    (bernoulliSampleMean_isHajekRegular hp) tendsto_id

/-- **The Hájek bound for the Bernoulli family**: every estimator sequence regular at
`p₀ ∈ (0, 1)` with limit `N(0, V)` has `p₀ (1 - p₀) ≤ V`. -/
theorem bernoulli_hajek_convolution_bound (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    {T : ∀ n, (Fin n → Bool) → ℝ} {V : ℝ≥0}
    (hT : bernoulli.IsHajekRegular T p₀ (gaussianReal 0 V)) : p₀ * (1 - p₀) ≤ V := by
  rw [← bernoulli_inv_fisherInfo hp]
  exact hajek_convolution_bound (bernoulli_isRegularAt hp) (bernoulli_isScoreRegular hp)
    (bernoulli_hasDerivAt_logLik_closedBall hp) (bernoulli_fisherInfo_pos hp) hT

/-- At `p₀ = 1/4` every regular estimator with limit `N(0, V)` has `3/16 ≤ V`. -/
theorem bernoulli_hajek_convolution_bound_quarter {T : ∀ n, (Fin n → Bool) → ℝ} {V : ℝ≥0}
    (hT : bernoulli.IsHajekRegular T (1 / 4) (gaussianReal 0 V)) : 3 / 16 ≤ (V : ℝ) := by
  have h := bernoulli_hajek_convolution_bound ⟨by norm_num, by norm_num⟩ hT
  norm_num at h ⊢
  linarith

/-- **The sample proportion attains the Hájek bound.** Its limit variance `p₀ (1 - p₀)` equals
`I(p₀)⁻¹`, and on every i.i.d. Bernoulli(`p₀`) sample both sides of the equality case of the
convolution theorem hold: the variance equals the bound, and the estimator is asymptotically
linear with the efficient influence function. -/
theorem bernoulliSampleMean_attains_hajek_bound (hO : IsIIDSample O μ)
    (hlaw : μ.map (O 0) = bernoulli.law p₀) (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    ((p₀ * (1 - p₀)).toNNReal : ℝ) = (bernoulli.fisherInfo p₀)⁻¹ ∧
      IsAsymptoticallyLinear (fun n ω ↦ bernoulliSampleMean n fun i ↦ O i ω) p₀
        (fun x ↦ (bernoulli.fisherInfo p₀)⁻¹ * bernoulli.score p₀ x) O μ := by
  have hV : ((p₀ * (1 - p₀)).toNNReal : ℝ) = (bernoulli.fisherInfo p₀)⁻¹ := by
    rw [bernoulli_inv_fisherInfo hp, Real.coe_toNNReal _ (mul_pos hp.1 (by linarith [hp.2])).le]
  refine ⟨hV, (hajek_eq_iff_isAsymptoticallyLinear hO hlaw (bernoulli_isRegularAt hp)
    (bernoulli_isScoreRegular hp) (bernoulli_hasDerivAt_logLik_closedBall hp)
    (bernoulli_fisherInfo_pos hp) (bernoulliSampleMean_isHajekRegular hp)).1 hV⟩

/-- At `p₀ = 1/4` the sample proportion is regular with limit `N(0, 3/16)`, the bound. -/
theorem bernoulliSampleMean_isHajekRegular_quarter :
    bernoulli.IsHajekRegular bernoulliSampleMean (1 / 4)
      (gaussianReal 0 (3 / 16 : ℝ).toNNReal) := by
  have h := bernoulliSampleMean_isHajekRegular (p₀ := 1 / 4) ⟨by norm_num, by norm_num⟩
  norm_num at h ⊢
  exact h

end ParametricFamily

end CausalInference
