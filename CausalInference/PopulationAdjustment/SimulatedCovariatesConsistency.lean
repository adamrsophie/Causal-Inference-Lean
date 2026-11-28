/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.SimulatedCovariatesIdentification
public import CausalInference.PopulationAdjustment.StandardizationConsistencyTargetSample

/-!
# Consistency of the simulated comparison

The simulated comparison averages the fitted outcome surface of the trial arm over `m_n`
simulated covariate vectors `X'_i = nortaMap μ (Z_i)`, with `Z_0, Z_1, …` i.i.d. `N(0, R)`:
`m_n⁻¹ ∑_{i < m_n} h θ̂_n t (X'_i)`. Its limit is the standardized mean of `h θ₀ t` under the
simulated law (the uniform law of large numbers, `tendstoInMeasure_sampleMean_fit`), which is the
target arm mean under the conditions of `SimulatedCovariatesIdentification`. The draws and the
trial sample may be dependent.

The only assumption about the fit in the general theorems is `hθ : θ̂_n → θ₀` in probability;
for least squares it is derived from the linear outcome model
(`tendstoInMeasure_simulated_leastSquares_armMean`). The simulated sample means are never assumed
to converge: their convergence is the uniform law of large numbers.

## Main results

* `tendstoInMeasure_simulated_fit`: the simulated average converges to the standardized mean
  under the simulated law.
* `tendstoInMeasure_simulated_armMean`, `tendstoInMeasure_simulated_unanchored`: an additive
  conditional mean surface; the limit is the target arm mean and the unanchored target effect.
* `tendstoInMeasure_simulated_leastSquares_armMean`,
  `tendstoInMeasure_simulated_leastSquares_unanchored`: the least squares surface with every
  regularity condition and the convergence of the fit derived.

## References

* J. J. Caro and K. J. Ishak, *No head-to-head trial? Simulate the missing arms*,
  PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix IndirectComparison PointTreatment
  Transport

variable {ι Ω₁ Ω₂ Ξ Θ κ' : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω₁]
  [MeasurableSpace Ω₂] [MeasurableSpace Ξ] {P : Measure Ξ} [IsProbabilityMeasure P]
  {T : Trial Ω₁ (ι → ℝ) Bool} {Q : Population Ω₂ (ι → ℝ) κ'} {R : Matrix ι ι ℝ}
  {μ : ι → Measure ℝ} {Z : ℕ → Ξ → EuclideanSpace ℝ ι} {m : ℕ → ℕ}

section General

variable [MetricSpace Θ] [SecondCountableTopology Θ] [ProperSpace Θ] {h : Θ → Bool → (ι → ℝ) → ℝ}
  {θ₀ : Θ} {θh : ℕ → Ξ → Θ}

/-- **The simulated average converges to the simulated standardized mean.** For i.i.d.
`Z_i ∼ N(0, R)`, `m n → ∞`, a fit `θ̂ → θ₀` in probability and a surface `h θ t` that, on a
neighborhood `U` of `θ₀`, is measurable, continuous in the parameter and dominated by an
integrable envelope under the simulated law, `m_n⁻¹ ∑_{i < m_n} h θ̂_n t (nortaMap μ (Z_i))`
converges in probability to `∫ h θ₀ t d(nortaLaw R μ)`. -/
theorem tendstoInMeasure_simulated_fit (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) (hm : Tendsto m atTop atTop) {t : Bool}
    {U : Set Θ} (hU : U ∈ 𝓝 θ₀) (hmeas : ∀ θ ∈ U, Measurable (h θ t))
    (hcont : ∀ᵐ x ∂nortaLaw R μ, ContinuousOn (fun θ => h θ t x) U) {H : (ι → ℝ) → ℝ}
    (hH : Integrable H (nortaLaw R μ)) (hdom : ∀ᵐ x ∂nortaLaw R μ, ∀ θ ∈ U, |h θ t x| ≤ H x)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) :
    TendstoInMeasure P
      (fun n ω => sampleMean (h (θh n ω) t) (fun i ω => nortaMap μ (Z i ω)) (m n) ω) atTop
      (fun _ => ∫ x, h θ₀ t x ∂nortaLaw R μ) := by
  obtain ⟨hX, hX0⟩ := isIIDSample_nortaMap (μ := μ) hZ hZ0
  exact tendstoInMeasure_sampleMean_fit (h := fun θ => h θ t) hX hX0 hm hU hmeas hcont hH hdom hθ

/-- **Consistency of the simulated comparison for the target arm mean, additive surface.** In a
randomized trial with integrable potential outcomes and a correct outcome model `h θ₀`, with
arm `t` of the trial transported to treatment `s` of the target, overlap, an integrable target
outcome, an additive true surface `h θ₀ t x = c + ∑_j f_j(x_j)` with `f_j` integrable against
the target margins `μ_j`, any correlation matrix `R`, and the regularity of
`tendstoInMeasure_simulated_fit`, the simulated average converges in probability to `E_Q[Y(s)]`
for every fit `θ̂ → θ₀` in probability. -/
theorem tendstoInMeasure_simulated_armMean [IsProbabilityMeasure T.μ] [IsProbabilityMeasure Q.μ]
    (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (h θ₀)) (hX₂ : Measurable Q.X)
    {t : Bool} {s : κ'} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) [∀ j, IsProbabilityMeasure (μ j)]
    (hmarg : ∀ j, Q.covLaw.map (fun x => x j) = μ j) {c : ℝ} {f : ι → ℝ → ℝ}
    (hadd : ∀ x, h θ₀ t x = c + ∑ j, f j (x j)) (hf : ∀ j, Integrable (f j) (μ j))
    {U : Set Θ} (hU : U ∈ 𝓝 θ₀) (hmeas : ∀ θ ∈ U, Measurable (h θ t))
    (hcont : ∀ᵐ x ∂nortaLaw R μ, ContinuousOn (fun θ => h θ t x) U) {H : (ι → ℝ) → ℝ}
    (hH : Integrable H (nortaLaw R μ)) (hdom : ∀ᵐ x ∂nortaLaw R μ, ∀ θ ∈ U, |h θ t x| ≤ H x)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) (hm : Tendsto m atTop atTop) :
    TendstoInMeasure P
      (fun n ω => sampleMean (h (θh n ω) t) (fun i ω => nortaMap μ (Z i ω)) (m n) ω) atTop
      (fun _ => Q.armMean s) := by
  rw [← integral_nortaLaw_eq_armMean_of_additive hR hdiag hmarg hT.measurable_X hX₂ hYQ
    (hT.isCondMean hYi hreg t) hsi hov hadd hf]
  exact tendstoInMeasure_simulated_fit hZ hZ0 hm hU hmeas hcont hH hdom hθ

/-- **Consistency of the unanchored simulated comparison.** Under the hypotheses of
`tendstoInMeasure_simulated_armMean` for arm `t ↦ a`, with a reported target mean `m̂_b` of
treatment `b` converging in probability to `E_Q[Y(b)]` and a link `g` continuous at both
target means, `g(m̂_b) - g(m_n⁻¹ ∑ h θ̂_n t (X'_i))` converges in probability to the target
marginal effect of `b` relative to `a`. -/
theorem tendstoInMeasure_simulated_unanchored [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hYi : ∀ t, Integrable (T.Y t) T.μ)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome (h θ₀)) (hX₂ : Measurable Q.X)
    {t : Bool} {a b : κ'} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) [∀ j, IsProbabilityMeasure (μ j)]
    (hmarg : ∀ j, Q.covLaw.map (fun x => x j) = μ j) {c : ℝ} {f : ι → ℝ → ℝ}
    (hadd : ∀ x, h θ₀ t x = c + ∑ j, f j (x j)) (hf : ∀ j, Integrable (f j) (μ j))
    {U : Set Θ} (hU : U ∈ 𝓝 θ₀) (hmeas : ∀ θ ∈ U, Measurable (h θ t))
    (hcont : ∀ᵐ x ∂nortaLaw R μ, ContinuousOn (fun θ => h θ t x) U) {H : (ι → ℝ) → ℝ}
    (hH : Integrable H (nortaLaw R μ)) (hdom : ∀ᵐ x ∂nortaLaw R μ, ∀ θ ∈ U, |h θ t x| ≤ H x)
    (hθ : TendstoInMeasure P θh atTop fun _ => θ₀) (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) (hm : Tendsto m atTop atTop)
    {mb : ℕ → Ξ → ℝ} (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    TendstoInMeasure P
      (fun n ω => g (mb n ω) -
        g (sampleMean (h (θh n ω) t) (fun i ω => nortaMap μ (Z i ω)) (m n) ω)) atTop
      (fun _ => Q.marginalEffect g a b) :=
  (hmb.comp_continuousAt hgb).sub
    ((tendstoInMeasure_simulated_armMean hT hYi hreg hX₂ hYQ hsi hov hR hdiag hmarg hadd hf hU
      hmeas hcont hH hdom hθ hZ hZ0 hm).comp_continuousAt hga)

end General

section LeastSquares

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {z : Bool → (ι → ℝ) → κ → ℝ} {ξ₀ : κ → ℝ}
  {O : ℕ → Ξ → (ι → ℝ) × Bool × ℝ}

/-- **Consistency of the simulated comparison with a least squares fit.** In a randomized trial
with a linear outcome model `z(a, x)ᵀξ₀` and an i.i.d. sample of its records, with arm `t`
transported to treatment `s` of the target, overlap, an integrable target outcome, an additive
true surface `z(t, x)ᵀξ₀ = c + ∑_j f_j(x_j)` with `f_j` integrable against the target margins
`μ_j`, design coordinates of arm `t` integrable under the simulated law, any correlation matrix
`R` and i.i.d. draws `Z_i ∼ N(0, R)` whose number `m n` tends to infinity, the simulated average
`m_n⁻¹ ∑_{i < m_n} z(t, X'_i)ᵀξ̂_n` converges in probability to `E_Q[Y(s)]`. The convergence of
the least squares fit is derived, not assumed. -/
theorem tendstoInMeasure_simulated_leastSquares_armMean [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hM : T.LinearOutcomeModel z ξ₀)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hX₂ : Measurable Q.X) {t : Bool}
    {s : κ'} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) [∀ j, IsProbabilityMeasure (μ j)]
    (hmarg : ∀ j, Q.covLaw.map (fun x => x j) = μ j) {c : ℝ} {f : ι → ℝ → ℝ}
    (hadd : ∀ x, z t x ⬝ᵥ ξ₀ = c + ∑ j, f j (x j)) (hf : ∀ j, Integrable (f j) (μ j))
    (hzν : ∀ j, Integrable (fun x => z t x j) (nortaLaw R μ)) (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) (hm : Tendsto m atTop atTop) :
    TendstoInMeasure P
      (fun n ω => sampleMean (fun x => z t x ⬝ᵥ leastSquaresFit (recordDesign z) recordResponse
        O n ω) (fun i ω => nortaMap μ (Z i ω)) (m n) ω) atTop (fun _ => Q.armMean s) := by
  obtain ⟨hm', hc, hH, hd⟩ := linearSurface_regular_ball (hM.measurable_z t) hzν ξ₀
  exact tendstoInMeasure_simulated_armMean (h := fun ξ a x => z a x ⬝ᵥ ξ) hT hM.integrable_Y
    hM.isOutcomeRegression hX₂ hYQ hsi hov hR hdiag hmarg hadd hf
    (Metric.ball_mem_nhds ξ₀ one_pos) (fun ξ _ => hm' ξ) hc hH hd
    (hM.tendstoInMeasure hT hO hlaw) hZ hZ0 hm

/-- **Consistency of the unanchored simulated comparison with a least squares fit.** Under the
hypotheses of `tendstoInMeasure_simulated_leastSquares_armMean` for arm `t ↦ a`, a reported
target mean `m̂_b → E_Q[Y(b)]` in probability and a link `g` continuous at both target means,
the unanchored estimator converges in probability to the target marginal effect of `b` relative
to `a`. -/
theorem tendstoInMeasure_simulated_leastSquares_unanchored [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hM : T.LinearOutcomeModel z ξ₀)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = T.ipdLaw) (hX₂ : Measurable Q.X) {t : Bool}
    {a b : κ'} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y t) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    (hR : R.PosSemidef) (hdiag : ∀ i, R i i = 1) [∀ j, IsProbabilityMeasure (μ j)]
    (hmarg : ∀ j, Q.covLaw.map (fun x => x j) = μ j) {c : ℝ} {f : ι → ℝ → ℝ}
    (hadd : ∀ x, z t x ⬝ᵥ ξ₀ = c + ∑ j, f j (x j)) (hf : ∀ j, Integrable (f j) (μ j))
    (hzν : ∀ j, Integrable (fun x => z t x j) (nortaLaw R μ)) (hZ : IsIIDSample Z P)
    (hZ0 : P.map (Z 0) = multivariateGaussian 0 R) (hm : Tendsto m atTop atTop)
    {mb : ℕ → Ξ → ℝ} (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    TendstoInMeasure P
      (fun n ω => g (mb n ω) - g (sampleMean (fun x => z t x ⬝ᵥ leastSquaresFit
        (recordDesign z) recordResponse O n ω) (fun i ω => nortaMap μ (Z i ω)) (m n) ω)) atTop
      (fun _ => Q.marginalEffect g a b) :=
  (hmb.comp_continuousAt hgb).sub
    ((tendstoInMeasure_simulated_leastSquares_armMean hT hM hO hlaw hX₂ hYQ hsi hov hR hdiag
      hmarg hadd hf hzν hZ hZ0 hm).comp_continuousAt hga)

end LeastSquares

end PopulationAdjustment

end CausalInference
