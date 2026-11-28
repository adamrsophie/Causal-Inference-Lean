/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LikelihoodTests
public import CausalInference.Estimation.MaximumLikelihood

/-!
# The Bernoulli family: normality of the maximum likelihood estimator and the three tests

For an i.i.d. Bernoulli sample with success probability `p₀ ∈ (ε, 1 - ε)`, the estimator is the
sample mean clipped to `[ε, 1 - ε]`, `θ̂_n = max ε (min (1 - ε) p̂_n)` (the maximum likelihood
estimator over `[ε, 1 - ε]`, `ParametricFamily.bernoulli_isMLE`). Every hypothesis of the
general theorems is verified: the score `s(p; x) = 1/p` or `-1/(1 - p)`, its derivative
`-1/p²` or `-1/(1 - p)²`, regularity, positive information `1 / (p₀ (1 - p₀))`, consistency, and
the score equation, which holds whenever `θ̂_n` lies strictly inside `(ε, 1 - ε)`.

## Main results

* `CausalInference.ParametricFamily.bernoulli_clip_isAsymptoticallyLinear` and
  `bernoulli_clip_tendstoInDistribution`: `√n (θ̂_n - p₀) → N(0, p₀ (1 - p₀))`.
* `CausalInference.ParametricFamily.bernoulli_waldStat_tendstoInDistribution` (known
  information) and `bernoulli_waldStat_hat_tendstoInDistribution` (information `I(θ̂_n)`).
* `CausalInference.ParametricFamily.bernoulli_scoreStat_tendstoInDistribution`.
* `CausalInference.ParametricFamily.bernoulli_lrStat_tendstoInDistribution` (Wilks) and the two
  asymptotic equivalences.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Metric
open scoped Topology ENNReal NNReal

namespace CausalInference

namespace ParametricFamily

/-- The Bernoulli score: `s(p; x) = 1/p` at a success and `-1/(1 - p)` at a failure. -/
theorem bernoulli_score (p : ℝ) (x : Bool) :
    bernoulli.score p x = if x then p⁻¹ else -(1 - p)⁻¹ := by
  cases x <;> simp [score, bernoulli_densityDeriv, bernoulli_density, neg_div]

/-- The Bernoulli score in terms of the success indicator. -/
theorem bernoulli_score_eq (p : ℝ) (x : Bool) :
    bernoulli.score p x = successIndicator x * p⁻¹ - (1 - successIndicator x) * (1 - p)⁻¹ := by
  cases x <;> simp [bernoulli_score, successIndicator]

/-- The derivative of the Bernoulli score in `p ∈ (0, 1)`. -/
theorem bernoulli_hasDerivAt_score {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Bool) :
    HasDerivAt (fun u ↦ bernoulli.score u x) (if x then -(p ^ 2)⁻¹ else -((1 - p) ^ 2)⁻¹) p := by
  have h1 : 1 - p ≠ 0 := by linarith [hp.2]
  simp_rw [bernoulli_score]
  cases x
  · simp only [Bool.false_eq_true, ite_false]
    have := (((hasDerivAt_id' p).const_sub 1).inv h1).neg
    convert this using 1
    field_simp
  · simpa using hasDerivAt_inv hp.1.ne'

/-- The derivative of the Bernoulli log density in `p ∈ (0, 1)` is the score. -/
theorem bernoulli_hasDerivAt_logLik {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Bool) :
    HasDerivAt (fun u ↦ bernoulli.logLik u x) (bernoulli.score p x) p := by
  have h1 : 1 - p ≠ 0 := by linarith [hp.2]
  rw [bernoulli_score]
  cases x
  · simp only [logLik, bernoulli_density, Bool.false_eq_true, ite_false]
    have := ((hasDerivAt_id' p).const_sub 1).log h1
    convert this using 1
    field_simp
  · simpa [logLik, bernoulli_density] using Real.hasDerivAt_log hp.1.ne'

/-- The second derivative of the Bernoulli log density in `p ∈ (0, 1)`. -/
theorem bernoulli_hessLogLik {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (x : Bool) :
    bernoulli.hessLogLik p x = if x then -(p ^ 2)⁻¹ else -((1 - p) ^ 2)⁻¹ := by
  have heq : (fun u ↦ deriv (fun v ↦ bernoulli.logLik v x) u) =ᶠ[𝓝 p]
      fun u ↦ bernoulli.score u x := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with u hu
    exact (bernoulli_hasDerivAt_logLik hu x).deriv
  rw [hessLogLik, heq.deriv_eq, (bernoulli_hasDerivAt_score hp x).deriv]

/-- Points of the closed ball of radius `min p₀ (1 - p₀) / 2` around `p₀` stay at least
`p₀ / 2` away from `0` and `(1 - p₀) / 2` away from `1`. -/
theorem le_of_mem_closedBall_half_min {p₀ t : ℝ}
    (ht : t ∈ closedBall p₀ (min p₀ (1 - p₀) / 2)) :
    p₀ / 2 ≤ t ∧ (1 - p₀) / 2 ≤ 1 - t := by
  rw [mem_closedBall, Real.dist_eq, abs_le] at ht
  have := min_le_left p₀ (1 - p₀)
  have := min_le_right p₀ (1 - p₀)
  constructor <;> linarith [ht.1, ht.2]

/-- The closed ball of radius `min p₀ (1 - p₀) / 2` around `p₀ ∈ (0, 1)` lies in `(0, 1)`. -/
theorem mem_Ioo_of_mem_closedBall {p₀ : ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ closedBall p₀ (min p₀ (1 - p₀) / 2)) : t ∈ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := le_of_mem_closedBall_half_min ht
  exact ⟨by linarith [hp₀.1], by linarith [hp₀.2]⟩

/-- **The Bernoulli score is regular** on the closed ball of radius `min p₀ (1 - p₀) / 2`. -/
theorem bernoulli_isScoreRegular {p₀ : ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulli.IsScoreRegular p₀ (min p₀ (1 - p₀) / 2) := by
  have hq : 0 < 1 - p₀ := by linarith [hp₀.2]
  have hIoo : ∀ t ∈ closedBall p₀ (min p₀ (1 - p₀) / 2), t ∈ Set.Ioo (0 : ℝ) 1 :=
    fun t ht ↦ mem_Ioo_of_mem_closedBall hp₀ ht
  have := isProbabilityMeasure_law (F := bernoulli) hp₀
  refine ⟨half_pos (lt_min hp₀.1 hq), .of_discrete, fun _ _ ↦ .of_discrete,
    ae_of_all _ fun x t ht ↦ ?_, ae_of_all _ fun x ↦ ?_,
    ⟨fun _ ↦ ((p₀ / 2) ^ 2)⁻¹ + (((1 - p₀) / 2) ^ 2)⁻¹, integrable_const _,
      ae_of_all _ fun x t ht ↦ ?_⟩⟩
  · rw [bernoulli_hessLogLik (hIoo t ht)]
    exact bernoulli_hasDerivAt_score (hIoo t ht) x
  · refine ContinuousOn.congr (f := fun u ↦ if x then -(u ^ 2)⁻¹ else -((1 - u) ^ 2)⁻¹) ?_
      fun t ht ↦ bernoulli_hessLogLik (hIoo t ht) x
    cases x
    · exact (((continuousOn_const.sub continuousOn_id).pow 2).inv₀ fun t ht ↦
        pow_ne_zero 2 (by change (1 : ℝ) - t ≠ 0; linarith [(hIoo t ht).2])).neg
    · exact ((continuousOn_id.pow 2).inv₀ fun t ht ↦
        pow_ne_zero 2 (hIoo t ht).1.ne').neg
  · obtain ⟨h1, h2⟩ := le_of_mem_closedBall_half_min ht
    have ha : ((t ^ 2)⁻¹ : ℝ) ≤ ((p₀ / 2) ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos (half_pos hp₀.1) 2) (pow_le_pow_left₀ (half_pos hp₀.1).le h1 2)
    have hb : (((1 - t) ^ 2)⁻¹ : ℝ) ≤ (((1 - p₀) / 2) ^ 2)⁻¹ :=
      inv_anti₀ (pow_pos (half_pos hq) 2) (pow_le_pow_left₀ (half_pos hq).le h2 2)
    have hc : 0 ≤ ((p₀ / 2) ^ 2)⁻¹ := by positivity
    have hd : 0 ≤ (((1 - p₀) / 2) ^ 2)⁻¹ := by positivity
    rw [bernoulli_hessLogLik (hIoo t ht)]
    cases x
    · simp only [Bool.false_eq_true, ite_false, abs_neg]
      rw [abs_of_nonneg (by positivity)]; linarith
    · simp only [ite_true, abs_neg]
      rw [abs_of_nonneg (by positivity)]; linarith

/-- The log density is jointly measurable in the parameter and the observation. -/
theorem measurable_bernoulli_logLik : Measurable fun p : ℝ × Bool ↦ bernoulli.logLik p.1 p.2 := by
  have hs : Measurable successIndicator := .of_discrete
  have : (fun p : ℝ × Bool ↦ bernoulli.logLik p.1 p.2) = fun p ↦
      successIndicator p.2 * Real.log p.1 + (1 - successIndicator p.2) * Real.log (1 - p.1) :=
    funext fun p ↦ bernoulli_log_density p.1 p.2
  rw [this]
  fun_prop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {O : ℕ → Ω → Bool} {ε p₀ : ℝ}

omit [IsProbabilityMeasure μ] in
/-- The clipped sample mean is measurable. -/
theorem aemeasurable_bernoulli_clip (hO : IsIIDSample O μ) (n : ℕ) :
    AEMeasurable (fun ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) μ := by
  have hs : Measurable successIndicator := .of_discrete
  have : AEMeasurable (fun ω ↦ sampleMean successIndicator O n ω) μ :=
    (Finset.aemeasurable_fun_sum _ fun i _ ↦ hs.comp_aemeasurable (hO.aemeasurable i)).const_mul _
  exact aemeasurable_const.max (aemeasurable_const.min this)

/-- **The clipped sample mean solves the score equation** with probability tending to one, when
`p₀` lies strictly inside `(ε, 1 - ε)`. -/
theorem bernoulli_clip_root (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hO : IsIIDSample O μ)
    (hp₀ : p₀ ∈ Set.Ioo ε (1 - ε)) (hlaw : μ.map (O 0) = bernoulli.law p₀) :
    WithProbTendingToOne μ (fun n ↦ {ω | ∑ i ∈ range n, bernoulli.score
      (max ε (min (1 - ε) (sampleMean successIndicator O n ω))) (O i ω) = 0}) := by
  have hθ := bernoulli_clip_isConsistent hε hε2 hO ⟨hp₀.1.le, hp₀.2.le⟩ hlaw
  have hd : 0 < min (p₀ - ε) (1 - ε - p₀) := lt_min (by linarith [hp₀.1]) (by linarith [hp₀.2])
  refine (TendstoInMeasure.withProbTendingToOne_dist_lt hθ hd).mono fun n ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq, abs_lt] at hω ⊢
  set q := sampleMean successIndicator O n ω with hq
  have hm1 := min_le_left (p₀ - ε) (1 - ε - p₀)
  have hm2 := min_le_right (p₀ - ε) (1 - ε - p₀)
  have hlo : ε < max ε (min (1 - ε) q) := by linarith [hω.1]
  have hhi : max ε (min (1 - ε) q) < 1 - ε := by linarith [hω.2]
  have heq : max ε (min (1 - ε) q) = q := by
    rcases le_total q (1 - ε) with h | h
    · rw [min_eq_right h] at hlo ⊢
      exact max_eq_right (le_of_lt (lt_max_iff.1 hlo |>.resolve_left (lt_irrefl ε)))
    · rw [min_eq_left h, max_eq_right (by linarith)] at hhi; exact absurd hhi (lt_irrefl _)
  rw [heq] at hlo hhi ⊢
  have hn : n ≠ 0 := by
    rintro rfl
    simp [hq, sampleMean] at hlo
    linarith
  have hk : ∑ i ∈ range n, successIndicator (O i ω) = n * q := by
    rw [hq, natCast_mul_sampleMean]
  have hq0 : q ≠ 0 := by linarith
  have hq1 : 1 - q ≠ 0 := by linarith
  simp only [bernoulli_score_eq, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, hk]
  field_simp
  ring

variable (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hO : IsIIDSample O μ) (hp₀ : p₀ ∈ Set.Ioo ε (1 - ε))
  (hlaw : μ.map (O 0) = bernoulli.law p₀)

include hε hε2 hO hp₀ hlaw

omit hε hε2 hO hp₀ hlaw in
/-- `p₀ ∈ (0, 1)` when `p₀ ∈ (ε, 1 - ε)` with `ε > 0`. -/
theorem mem_Ioo_of_mem_Ioo_eps (hε : 0 < ε) (hp₀ : p₀ ∈ Set.Ioo ε (1 - ε)) :
    p₀ ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨by linarith [hp₀.1], by linarith [hp₀.2]⟩

/-- **Asymptotic linearity of the clipped Bernoulli MLE** with influence function
`I(p₀)⁻¹ s(p₀; ·)`, that is `x ↦ x - p₀`. -/
theorem bernoulli_clip_isAsymptoticallyLinear :
    IsAsymptoticallyLinear (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀
      (fun z ↦ (bernoulli.fisherInfo p₀)⁻¹ * bernoulli.score p₀ z) O μ :=
  have hp := mem_Ioo_of_mem_Ioo_eps hε hp₀
  mle_isAsymptoticallyLinear_of_root hO hlaw (bernoulli_isRegularAt hp)
    (bernoulli_isScoreRegular hp) (bernoulli_fisherInfo_pos hp)
    (bernoulli_clip_isConsistent hε hε2 hO ⟨hp₀.1.le, hp₀.2.le⟩ hlaw)
    (bernoulli_clip_root hε hε2 hO hp₀ hlaw)

/-- **Asymptotic normality of the clipped Bernoulli MLE**: `√n (θ̂_n - p₀) → N(0, p₀ (1 - p₀))`,
the inverse information. -/
theorem bernoulli_clip_tendstoInDistribution {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → ℝ}
    (hY : HasLaw Y (gaussianReal 0 (p₀ * (1 - p₀)).toNNReal) P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦
      √n * (max ε (min (1 - ε) (sampleMean successIndicator O n ω)) - p₀)) atTop Y
      (fun _ ↦ μ) P' := by
  have hp := mem_Ioo_of_mem_Ioo_eps hε hp₀
  refine mle_tendstoInDistribution hO hlaw (bernoulli_isRegularAt hp)
    (bernoulli_isScoreRegular hp) (bernoulli_fisherInfo_pos hp) (aemeasurable_bernoulli_clip hO)
    (bernoulli_clip_isConsistent hε hε2 hO ⟨hp₀.1.le, hp₀.2.le⟩ hlaw)
    (bernoulli_clip_root hε hε2 hO hp₀ hlaw) ?_
  rwa [bernoulli_fisherInfo hp, one_div, inv_inv]

/-- **The Bernoulli Wald test with known information**: `n (θ̂_n - p₀)² / (p₀ (1 - p₀)) → χ²₁`. -/
theorem bernoulli_waldStat_tendstoInDistribution {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''}
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {W : Ω'' → ℝ}
    (hW : HasLaw W chiSquaredOne P'') :
    TendstoInDistribution
      (waldStat (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀
        (fun _ _ ↦ bernoulli.fisherInfo p₀)) atTop W (fun _ ↦ μ) P'' := by
  have hp := mem_Ioo_of_mem_Ioo_eps hε hp₀
  have hI := bernoulli_fisherInfo_pos hp
  exact waldStat_tendstoInDistribution hI HasLaw.id
    (mle_tendstoInDistribution hO hlaw (bernoulli_isRegularAt hp) (bernoulli_isScoreRegular hp)
      hI (aemeasurable_bernoulli_clip hO)
      (bernoulli_clip_isConsistent hε hε2 hO ⟨hp₀.1.le, hp₀.2.le⟩ hlaw)
      (bernoulli_clip_root hε hε2 hO hp₀ hlaw) HasLaw.id)
    (tendstoInMeasure_const _) (fun _ ↦ aemeasurable_const) hW

/-- **The Bernoulli Wald test with estimated information** `I(θ̂_n) = 1 / (θ̂_n (1 - θ̂_n))`:
`n (θ̂_n - p₀)² / (θ̂_n (1 - θ̂_n)) → χ²₁`. -/
theorem bernoulli_waldStat_hat_tendstoInDistribution {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''}
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {W : Ω'' → ℝ}
    (hW : HasLaw W chiSquaredOne P'') :
    TendstoInDistribution
      (waldStat (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀
        (fun n ω ↦ 1 / (max ε (min (1 - ε) (sampleMean successIndicator O n ω)) *
        (1 - max ε (min (1 - ε) (sampleMean successIndicator O n ω)))))) atTop W
      (fun _ ↦ μ) P'' := by
  have hp := mem_Ioo_of_mem_Ioo_eps hε hp₀
  have hI := bernoulli_fisherInfo_pos hp
  have hθ := bernoulli_clip_isConsistent hε hε2 hO ⟨hp₀.1.le, hp₀.2.le⟩ hlaw
  have hc : ContinuousAt (fun t : ℝ ↦ 1 / (t * (1 - t))) p₀ :=
    continuousAt_const.div (by fun_prop) (mul_ne_zero hp.1.ne' (by linarith [hp.2]))
  have hIh := hθ.comp_continuousAt hc
  rw [← bernoulli_fisherInfo hp] at hIh
  exact waldStat_tendstoInDistribution hI HasLaw.id
    (mle_tendstoInDistribution hO hlaw (bernoulli_isRegularAt hp) (bernoulli_isScoreRegular hp)
      hI (aemeasurable_bernoulli_clip hO) hθ (bernoulli_clip_root hε hε2 hO hp₀ hlaw) HasLaw.id)
    hIh (fun n ↦ by
      have h := aemeasurable_bernoulli_clip (ε := ε) hO n
      exact aemeasurable_const.div (h.mul (aemeasurable_const.sub h))) hW

omit hε hε2 hp₀ in
/-- **The Bernoulli score test**: `(n^{-1/2} ∑ s(p₀; O_i))² p₀ (1 - p₀) → χ²₁`. -/
theorem bernoulli_scoreStat_tendstoInDistribution (hp : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''}
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {W : Ω'' → ℝ}
    (hW : HasLaw W chiSquaredOne P'') :
    TendstoInDistribution (bernoulli.scoreStat O p₀) atTop W (fun _ ↦ μ) P'' :=
  scoreStat_tendstoInDistribution hO hlaw (bernoulli_isRegularAt hp) .of_discrete
    (bernoulli_fisherInfo_pos hp) hW

/-- **Wilks' theorem for the Bernoulli family**: the likelihood ratio statistic of the clipped
MLE converges in distribution to `χ²₁`. -/
theorem bernoulli_lrStat_tendstoInDistribution {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''}
    {P'' : Measure Ω''} [IsProbabilityMeasure P''] {W : Ω'' → ℝ}
    (hW : HasLaw W chiSquaredOne P'') :
    TendstoInDistribution (bernoulli.lrStat O
      (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀) atTop W
      (fun _ ↦ μ) P'' := by
  have hp := mem_Ioo_of_mem_Ioo_eps hε hp₀
  have hs := bernoulli_isScoreRegular hp
  exact lrStat_tendstoInDistribution hO hlaw (bernoulli_isRegularAt hp) hs
    (bernoulli_fisherInfo_pos hp)
    (ae_of_all _ fun z t ht ↦ bernoulli_hasDerivAt_logLik (mem_Ioo_of_mem_closedBall hp ht) z)
    measurable_bernoulli_logLik (aemeasurable_bernoulli_clip hO)
    (bernoulli_clip_isConsistent hε hε2 hO ⟨hp₀.1.le, hp₀.2.le⟩ hlaw)
    (bernoulli_clip_root hε hε2 hO hp₀ hlaw) hW

/-- **Asymptotic equivalence of the three Bernoulli tests**: the likelihood ratio and score
statistics each differ from the Wald statistic by a term tending to zero in probability. -/
theorem bernoulli_tests_asymptoticallyEquivalent :
    TendstoInMeasure μ (bernoulli.lrStat O
        (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀ -
      waldStat (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀
        (fun _ _ ↦ bernoulli.fisherInfo p₀)) atTop 0 ∧
    TendstoInMeasure μ (bernoulli.scoreStat O p₀ -
      waldStat (fun n ω ↦ max ε (min (1 - ε) (sampleMean successIndicator O n ω))) p₀
        (fun _ _ ↦ bernoulli.fisherInfo p₀)) atTop 0 := by
  have hp := mem_Ioo_of_mem_Ioo_eps hε hp₀
  have hs := bernoulli_isScoreRegular hp
  have hθ := bernoulli_clip_isConsistent hε hε2 hO ⟨hp₀.1.le, hp₀.2.le⟩ hlaw
  have hroot := bernoulli_clip_root hε hε2 hO hp₀ hlaw
  refine ⟨lrStat_sub_waldStat_tendstoInMeasure hO hlaw (bernoulli_isRegularAt hp) hs
    (bernoulli_fisherInfo_pos hp)
    (ae_of_all _ fun z t ht ↦ bernoulli_hasDerivAt_logLik (mem_Ioo_of_mem_closedBall hp ht) z)
    (aemeasurable_bernoulli_clip hO) hθ hroot,
    scoreStat_sub_waldStat_tendstoInMeasure hO hlaw (bernoulli_isRegularAt hp) hs
      (bernoulli_fisherInfo_pos hp) hθ hroot⟩

end ParametricFamily

end CausalInference
