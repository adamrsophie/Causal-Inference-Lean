/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyLeastSquares

/-!
# Standardization over a target sample or Monte Carlo draws

When the target covariate law `Q_X` is not available in closed form, the fitted surface is
averaged over draws `X'_1, X'_2, …` from it: the individual covariates of a target sample, or
Monte Carlo draws from a reported covariate distribution. With `m_n` draws and the parameter
`θ̂_n` fitted on `n` trial records, the estimator is the sample mean
`m_n⁻¹ ∑_{i < m_n} h θ̂_n t (X'_i)`, a function of the trial data and of the draws only.

**What is assumed about the data generating law.** The draws are i.i.d. with law `Q_X`
(`IsIIDSample` with `P.map (X'_0) = Q_X`) and the number of draws tends to infinity. The trial
records and the draws are defined on one probability space, and **no independence between the
trial sample and the draws is needed**: both converge in probability, and convergence in
probability is preserved by continuous maps of pairs. The model and transport assumptions are
those of `StandardizationConsistencyMarginal`, with the regularity of the model required on a
neighborhood `U` of `θ₀`: measurability, continuity in the parameter, and an integrable envelope
under `Q_X`. A closed ball inside `U` is compact in a proper parameter space, so the uniform law
of large numbers applies there (`uniform_law_of_large_numbers_real`).

## Main results

* `TendstoUniformlyOnInProbability.comp_tendsto`: the uniform law along a subsequence of sample
  sizes tending to infinity.
* `tendstoInMeasure_sampleMean_fit_armMean`: the target sample mean of the fitted surface
  converges to the target arm mean.
* `tendstoInMeasure_sampleMean_fit_unanchored`, `tendstoInMeasure_sampleMean_fit_anchored`: the
  comparisons with the target sample average.
* `tendstoInMeasure_sampleMean_leastSquares_armMean`,
  `tendstoInMeasure_sampleMean_leastSquares_anchored`: the least squares surface, with every
  regularity condition derived from integrable target design rows.

## References

* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

namespace CausalInference

/-- **The uniform law along a subsequence.** If `Mₙ → M` uniformly on `K` in probability and
`m n → ∞`, then `M_{m n} → M` uniformly on `K` in probability. -/
theorem TendstoUniformlyOnInProbability.comp_tendsto {Ω Θ F : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace F] {μ : MeasureTheory.Measure Ω} {Mn : ℕ → Ω → Θ → F} {M : Θ → F}
    {K : Set Θ} (h : TendstoUniformlyOnInProbability μ Mn M K) {m : ℕ → ℕ}
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) :
    TendstoUniformlyOnInProbability μ (fun n => Mn (m n)) M K :=
  fun δ hδ => (h δ hδ).comp hm

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### The target sample average of a fitted surface -/

section General

variable {Ξ 𝒳 Θ : Type*} [MeasurableSpace Ξ] [MeasurableSpace 𝒳] [MetricSpace Θ]
  [SecondCountableTopology Θ] [ProperSpace Θ] {P : Measure Ξ} [IsProbabilityMeasure P]

/-- **The target sample average of a fitted surface converges to its standardized limit.** For
i.i.d. draws `X'` with law `ν`, `m n → ∞`, a parameter `θ̂ → θ₀` in probability, and surfaces
`h θ` that, on a neighborhood `U` of `θ₀`, are measurable, continuous in the parameter for
almost every `x` and bounded by an integrable envelope, the average
`(m n)⁻¹ ∑_{i < m n} h θ̂_n (X'_i)` converges in probability to `∫ h θ₀ dν`. -/
theorem tendstoInMeasure_sampleMean_fit {Xs : ℕ → Ξ → 𝒳} (hXs : IsIIDSample Xs P)
    {ν : Measure 𝒳} (hν : P.map (Xs 0) = ν) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {h : Θ → 𝒳 → ℝ} {θ₀ : Θ} {U : Set Θ} (hU : U ∈ 𝓝 θ₀) (hmeas : ∀ θ ∈ U, Measurable (h θ))
    (hcont : ∀ᵐ x ∂ν, ContinuousOn (fun θ => h θ x) U) {H : 𝒳 → ℝ} (hH : Integrable H ν)
    (hdom : ∀ᵐ x ∂ν, ∀ θ ∈ U, |h θ x| ≤ H x) {θh : ℕ → Ξ → Θ}
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) :
    TendstoInMeasure P (fun n ω => sampleMean (h (θh n ω)) Xs (m n) ω) atTop
      (fun _ => ∫ x, h θ₀ x ∂ν) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  set K := Metric.closedBall θ₀ (r / 2)
  have hKU : K ⊆ U := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hK : K ∈ 𝓝 θ₀ := Metric.closedBall_mem_nhds θ₀ (by linarith)
  subst hν
  obtain ⟨hc, hu⟩ := uniform_law_of_large_numbers_real (ψ := fun x θ => h θ x) hXs
    (isCompact_closedBall θ₀ (r / 2)) (fun θ hθ => hmeas θ (hKU hθ))
    (hcont.mono fun x hx => hx.mono hKU) hH (hdom.mono fun x hx θ hθ => hx θ (hKU hθ))
  exact (hu.comp_tendsto hm).comp_tendstoInMeasure hK (hc.continuousAt hK) hθ

variable {Ω₁ Ω₂ ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {T : Trial Ω₁ 𝒳 Bool}
  {Q : Population Ω₂ 𝒳 ι} {hθf : Θ → Bool → 𝒳 → ℝ} {θ₀ : Θ} {θh : ℕ → Ξ → Θ}
  {Xs : ℕ → Ξ → 𝒳} {m : ℕ → ℕ}

/-- **The target sample average of the fitted surface is consistent for the target arm mean.**
In a randomized trial (`Trial.IsRandomizedTwoArm`) with integrable potential outcomes and a
correct outcome model (`h θ₀` a version of `E[Y | X, A]`), with absolute constancy of arm `t` of
the trial and treatment `s` of the target, overlap and an integrable target outcome, with the
model regular on a neighborhood `U` of `θ₀` under `Q_X`, and with i.i.d. draws `X'` from `Q_X`
whose number `m n` tends to infinity, the average `(m n)⁻¹ ∑_{i < m n} h θ̂_n t (X'_i)`
converges in probability to `E_Q[Y(s)]` for every `θ̂ → θ₀` in probability. The draws and the
trial sample need not be independent. -/
theorem tendstoInMeasure_sampleMean_fit_armMean [IsProbabilityMeasure T.μ] [IsFiniteMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (hθf θ₀)) (hX₂ : Measurable Q.X)
    {t : Bool} {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    {U : Set Θ} (hU : U ∈ 𝓝 θ₀) (hmeas : ∀ θ ∈ U, Measurable (hθf θ t))
    (hcont : ∀ᵐ x ∂Q.covLaw, ContinuousOn (fun θ => hθf θ t x) U) {H : 𝒳 → ℝ}
    (hH : Integrable H Q.covLaw) (hdom : ∀ᵐ x ∂Q.covLaw, ∀ θ ∈ U, |hθf θ t x| ≤ H x)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) (hXs : IsIIDSample Xs P)
    (hν : P.map (Xs 0) = Q.covLaw) (hm : Tendsto m atTop atTop) :
    TendstoInMeasure P (fun n ω => sampleMean (hθf (θh n ω) t) Xs (m n) ω) atTop
      (fun _ => Q.armMean s) := by
  obtain ⟨-, hval⟩ := integral_covLaw_eq_armMean_of_trial hT.measurable_X hX₂ hYQ
    (hT.isCondMean hYi hreg t) hsi hov
  rw [← hval]
  exact tendstoInMeasure_sampleMean_fit (h := fun θ => hθf θ t) hXs hν hm hU hmeas hcont hH
    hdom hθ

/-- **The unanchored comparison with a target sample average is consistent.** Under the
hypotheses of `tendstoInMeasure_sampleMean_fit_armMean` for arm `t ↦ a`, with a reported mean
`m̂_b` of treatment `b` in the target converging in probability to `E_Q[Y(b)]` and a link `g`
continuous at both target arm means, `g(m̂_b) - g((m n)⁻¹ ∑ h θ̂ t (X'_i))` converges in
probability to the target marginal effect of `b` relative to `a`. -/
theorem tendstoInMeasure_sampleMean_fit_unanchored [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (hθf θ₀)) (hX₂ : Measurable Q.X)
    {t : Bool} {a b : ι} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    {U : Set Θ} (hU : U ∈ 𝓝 θ₀) (hmeas : ∀ θ ∈ U, Measurable (hθf θ t))
    (hcont : ∀ᵐ x ∂Q.covLaw, ContinuousOn (fun θ => hθf θ t x) U) {H : 𝒳 → ℝ}
    (hH : Integrable H Q.covLaw) (hdom : ∀ᵐ x ∂Q.covLaw, ∀ θ ∈ U, |hθf θ t x| ≤ H x)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) (hXs : IsIIDSample Xs P)
    (hν : P.map (Xs 0) = Q.covLaw) (hm : Tendsto m atTop atTop) {mb : ℕ → Ξ → ℝ}
    (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    TendstoInMeasure P
      (fun n ω => g (mb n ω) - g (sampleMean (hθf (θh n ω) t) Xs (m n) ω)) atTop
      (fun _ => Q.marginalEffect g a b) :=
  (hmb.comp_continuousAt hgb).sub
    ((tendstoInMeasure_sampleMean_fit_armMean hT hYi hreg hX₂ hYQ hsi hov hU hmeas hcont hH
      hdom hθ hXs hν hm).comp_continuousAt hga)

/-- **The anchored comparison with a target sample average is consistent.** Both trial arms
`t_a ↦ a` and `t_c ↦ c` are averaged over the draws under the hypotheses of
`tendstoInMeasure_sampleMean_fit_armMean`. With a reported contrast `d̂_bc` converging in
probability to the target marginal effect of `c` relative to `b`, and a link `g` continuous at
the target means of `a` and `c`, the anchored estimator
`g(m̂_c) - g(m̂_a) - d̂_bc`, with `m̂` the target sample averages, converges in probability to the
target marginal effect of `b` relative to `a`. -/
theorem tendstoInMeasure_sampleMean_fit_anchored [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (hθf θ₀)) (hX₂ : Measurable Q.X)
    {ta tc : Bool} {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ) (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y ta) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y tc) Q.μ Q.X (Q.Y c)) (hov : Q.covLaw ≪ T.covLaw)
    {U : Set Θ} (hU : U ∈ 𝓝 θ₀) (hmeas : ∀ t, ∀ θ ∈ U, Measurable (hθf θ t))
    (hcont : ∀ t, ∀ᵐ x ∂Q.covLaw, ContinuousOn (fun θ => hθf θ t x) U) {H : Bool → 𝒳 → ℝ}
    (hH : ∀ t, Integrable (H t) Q.covLaw)
    (hdom : ∀ t, ∀ᵐ x ∂Q.covLaw, ∀ θ ∈ U, |hθf θ t x| ≤ H t x)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) (hXs : IsIIDSample Xs P)
    (hν : P.map (Xs 0) = Q.covLaw) (hm : Tendsto m atTop atTop) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    TendstoInMeasure P
      (fun n ω => g (sampleMean (hθf (θh n ω) tc) Xs (m n) ω) -
        g (sampleMean (hθf (θh n ω) ta) Xs (m n) ω) - dbc n ω) atTop
      (fun _ => Q.marginalEffect g a b) := by
  have ha := tendstoInMeasure_sampleMean_fit_armMean hT hYi hreg hX₂ hYQa hsia hov hU
    (hmeas ta) (hcont ta) (hH ta) (hdom ta) hθ hXs hν hm
  have hc := tendstoInMeasure_sampleMean_fit_armMean hT hYi hreg hX₂ hYQc hsic hov hU
    (hmeas tc) (hcont tc) (hH tc) (hdom tc) hθ hXs hν hm
  have e : Q.marginalEffect g a c - Q.marginalEffect g b c = Q.marginalEffect g a b := by
    simp only [Population.marginalEffect]; ring
  rw [← e]
  exact ((hc.comp_continuousAt hgc).sub (ha.comp_continuousAt hga)).sub hdbc

end General

/-! ### The least squares surface -/

section LeastSquares

variable {Ω₁ Ω₂ Ξ 𝒳 ι κ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [Fintype κ] [DecidableEq κ] {T : Trial Ω₁ 𝒳 Bool}
  {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {z : Bool → 𝒳 → κ → ℝ} {ξ₀ : κ → ℝ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {Xs : ℕ → Ξ → 𝒳} {m : ℕ → ℕ}

omit [DecidableEq κ] in
/-- The linear surface satisfies the regularity conditions of the target sample average on the
unit ball around `ξ₀`, for measurable design coordinates integrable under `ν`. -/
theorem linearSurface_regular_ball {z : 𝒳 → κ → ℝ} (hz : ∀ j, Measurable fun x => z x j)
    {ν : Measure 𝒳} (hzi : ∀ j, Integrable (fun x => z x j) ν) (ξ₀ : κ → ℝ) :
    (∀ ξ : κ → ℝ, Measurable fun x => z x ⬝ᵥ ξ) ∧
      (∀ᵐ x ∂ν, ContinuousOn (fun ξ => z x ⬝ᵥ ξ) (Metric.ball ξ₀ 1)) ∧
      Integrable (fun x => (‖ξ₀‖ + 1) * ∑ j, |z x j|) ν ∧
      ∀ᵐ x ∂ν, ∀ ξ ∈ Metric.ball ξ₀ 1, |z x ⬝ᵥ ξ| ≤ (‖ξ₀‖ + 1) * ∑ j, |z x j| := by
  refine ⟨fun ξ => Finset.measurable_sum _ fun j _ => (hz j).mul_const _,
    ae_of_all _ fun x => (continuous_const.dotProduct continuous_id).continuousOn,
    (linearSurface_dominated hz hzi ξ₀).2.1, ae_of_all _ fun x ξ hξ => ?_⟩
  have hn : ‖ξ‖ ≤ ‖ξ₀‖ + 1 := by
    have h1 := norm_sub_norm_le ξ ξ₀
    rw [Metric.mem_ball, dist_eq_norm] at hξ
    linarith
  have hdot : |z x ⬝ᵥ ξ| ≤ ‖ξ‖ * ∑ j, |z x j| := by
    rw [dotProduct, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa using norm_le_pi_norm ξ j) (abs_nonneg _)
  exact hdot.trans (mul_le_mul_of_nonneg_right hn (Finset.sum_nonneg fun j _ => abs_nonneg _))

/-- **The target sample average of the least squares surface is consistent for the target arm
mean.** In a randomized trial with a linear outcome model (`Trial.LinearOutcomeModel`) and an
i.i.d. sample of its individual records, with absolute constancy of arm `t` of the trial and
treatment `s` of the target, overlap, an integrable target outcome, design coordinates of arm
`t` integrable under `Q_X`, and i.i.d. draws `X'` from `Q_X` whose number `m n` tends to
infinity, the average `(m n)⁻¹ ∑_{i < m n} z(t, X'_i)ᵀξ̂_n` converges in probability to
`E_Q[Y(s)]`. -/
theorem tendstoInMeasure_sampleMean_leastSquares_armMean [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hM : T.LinearOutcomeModel z ξ₀) (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) {t : Bool} {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    (hzQ : ∀ j, Integrable (fun x => z t x j) Q.covLaw) (hXs : IsIIDSample Xs P)
    (hν : P.map (Xs 0) = Q.covLaw) (hm : Tendsto m atTop atTop) :
    TendstoInMeasure P
      (fun n ω => sampleMean (fun x => z t x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse
        O n ω) Xs (m n) ω) atTop (fun _ => Q.armMean s) := by
  obtain ⟨hm', hc, hH, hd⟩ := linearSurface_regular_ball (hM.measurable_z t) hzQ ξ₀
  exact tendstoInMeasure_sampleMean_fit_armMean (hθf := fun ξ a x => z a x ⬝ᵥ ξ) hT
    hM.integrable_Y hM.isOutcomeRegression hX₂ hYQ hsi hov (Metric.ball_mem_nhds ξ₀ one_pos)
    (fun ξ _ => hm' ξ) hc hH hd (hM.tendstoInMeasure hT hO hlaw) hXs hν hm

/-- **The anchored comparison with a target sample average of the least squares surface is
consistent.** Under the hypotheses of `tendstoInMeasure_sampleMean_leastSquares_armMean` for the
arms `t_a ↦ a` and `t_c ↦ c`, with a reported contrast `d̂_bc` converging in probability to the
target marginal effect of `c` relative to `b` and a link `g` continuous at the target means of
`a` and `c`, the anchored estimator converges in probability to the target marginal effect of
`b` relative to `a`. -/
theorem tendstoInMeasure_sampleMean_leastSquares_anchored [IsProbabilityMeasure T.μ]
    [IsFiniteMeasure Q.μ] [IsProbabilityMeasure P] (hT : T.IsRandomizedTwoArm)
    (hM : T.LinearOutcomeModel z ξ₀) (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw)
    (hX₂ : Measurable Q.X) {ta tc : Bool} {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y ta) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y tc) Q.μ Q.X (Q.Y c)) (hov : Q.covLaw ≪ T.covLaw)
    (hzQ : ∀ t j, Integrable (fun x => z t x j) Q.covLaw) (hXs : IsIIDSample Xs P)
    (hν : P.map (Xs 0) = Q.covLaw) (hm : Tendsto m atTop atTop) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    TendstoInMeasure P
      (fun n ω =>
        g (sampleMean (fun x => z tc x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
          Xs (m n) ω) -
        g (sampleMean (fun x => z ta x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse O n ω)
          Xs (m n) ω) - dbc n ω) atTop
      (fun _ => Q.marginalEffect g a b) := by
  have hr := fun t => linearSurface_regular_ball (hM.measurable_z t) (hzQ t) ξ₀
  exact tendstoInMeasure_sampleMean_fit_anchored (hθf := fun ξ a x => z a x ⬝ᵥ ξ) hT
    hM.integrable_Y hM.isOutcomeRegression hX₂ hYQa hYQc hsia hsic hov
    (Metric.ball_mem_nhds ξ₀ one_pos) (fun t ξ _ => (hr t).1 ξ) (fun t => (hr t).2.1)
    (fun t => (hr t).2.2.1) (fun t => (hr t).2.2.2) (hM.tendstoInMeasure hT hO hlaw) hXs hν hm
    hdbc hga hgc

end LeastSquares

end PopulationAdjustment

end CausalInference
