/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.RegularEstimatorBound

/-!
# The efficiency bound for regular estimators of the average effect

The average effect `E[Y(1)] - E[Y(0)]` is, under mean ignorability of both arms, the difference
`Ψ(ν) = E_ν[E_ν[Y | A = 1, W]] - E_ν[E_ν[Y | A = 0, W]]` of regression functionals of the law of
the observed data (`ateRegressionFunctional`). A pathwise gradient of `Ψ` along the score submodels
(`IsPathwiseGradientATE`) is unique up to almost sure equality and equals the efficient influence
function `ateEIF` (`ae_eq_ateEIF_of_isPathwiseGradientATE`). A regular asymptotically linear
estimator of the average effect has a pathwise gradient as influence function
(`isPathwiseGradientATE_of_isRegularAlong`), hence the influence function `ateEIF`
(`ae_eq_ateEIF_of_isRegularAlong`) and the asymptotic variance
`E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])`
(`integral_sq_eq_formula_of_isRegularAlong_ate`).

## Main definitions

* `ateRegressionFunctional`: the average effect as a functional of the population law.
* `IsPathwiseGradientATE`: a pathwise gradient of the average effect.

## Main results

* `isPathwiseGradientATE_ateEIF`, `ae_eq_ateEIF_of_isPathwiseGradientATE`
* `isPathwiseGradientATE_of_isRegularAlong`, `ae_eq_ateEIF_of_isRegularAlong`
* `integral_sq_eq_of_isRegularAlong_ate`, `integral_sq_eq_formula_of_isRegularAlong_ate`
* `tendstoInDistribution_of_isRegularAlong_ate`

## References

* J. Hahn, On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects, *Econometrica* 66 (1998), 315-331.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Topology MissingData PointTreatment

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} [IsProbabilityMeasure P]
  {Os : ℕ → Ω' → 𝒲 × Bool × ℝ} {T : ∀ n, (Fin n → 𝒲 × Bool × ℝ) → ℝ}
  {φ : 𝒲 × Bool × ℝ → ℝ} {L : Measure ℝ}

/-- The average effect as a functional of the population law: the difference of the regression
functionals of the two arms. -/
noncomputable abbrev ateRegressionFunctional (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲) :
    Measure Ω → ℝ :=
  fun ν ↦ armRegressionFunctional A Y W true ν - armRegressionFunctional A Y W false ν

/-- **A pathwise gradient of the average effect.** `ϕ` is a pathwise gradient of the average
effect at `μ` if along every bounded score submodel `(1 + t s(O)) dμ` the functional
`ateRegressionFunctional` has derivative `E_μ[ϕ(O) s(O)]` at `t = 0`. -/
def IsPathwiseGradientATE (μ : Measure Ω) (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (ϕ : 𝒲 × Bool × ℝ → ℝ) : Prop :=
  ∀ s, IsBoundedScore μ (obsData A Y W) s →
    HasDerivAt (fun t ↦ ateRegressionFunctional A Y W (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t))
      (∫ ω, ϕ (obsData A Y W ω) * s (obsData A Y W ω) ∂μ) 0

/-- At the population, the functional is the average effect. -/
theorem ateRegressionFunctional_eq (hW : Measurable W) (hA : Measurable A)
    (hYi : ∀ a, Integrable (Y a) μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) :
    ateRegressionFunctional A Y W μ = ate μ Y := by
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  rw [ateRegressionFunctional, armRegressionFunctional, armRegressionFunctional,
    regressionFunctional_arm_eq hW hA hYi hps hreg true (hmi true) hov.1 (hpos true),
    regressionFunctional_arm_eq hW hA hYi hps hreg false (hmi false) hov.1 (hpos false),
    ate_eq_armMean_sub (hYi true) (hYi false)]

/-- **The efficient influence function is a pathwise gradient of the average effect.** -/
theorem isPathwiseGradientATE_ateEIF (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) :
    IsPathwiseGradientATE μ A Y W (ateEIF e m (ate μ Y)) := fun _ hs ↦
  hasDerivAt_regressionFunctional_ate hW hA hY hYi hps hreg hmi hov hs

/-- **The pathwise gradient of the average effect is unique**: an integrable centered gradient
equals the efficient influence function `ateEIF` almost surely. -/
theorem ae_eq_ateEIF_of_isPathwiseGradientATE (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    {ϕ : 𝒲 × Bool × ℝ → ℝ} (hϕ : Measurable ϕ)
    (hϕI : Integrable (fun ω ↦ ϕ (obsData A Y W ω)) μ)
    (hϕ0 : ∫ ω, ϕ (obsData A Y W ω) ∂μ = 0) (hgrad : IsPathwiseGradientATE μ A Y W ϕ) :
    (fun ω ↦ ϕ (obsData A Y W ω)) =ᵐ[μ] fun ω ↦ ateEIF e m (ate μ Y) (obsData A Y W ω) := by
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  have hg := isPathwiseGradientATE_ateEIF hW hA hY hYi hps hreg hmi hov
  have hEI : Integrable (fun ω ↦ ateEIF e m (ate μ Y) (obsData A Y W ω)) μ := by
    rw [ate_eq_armMean_sub (hYi true) (hYi false)]
    simp only [ateEIF_eq_sub]
    exact (integrable_armEIF hW hA hYi hps hreg true (hmi true) hov.1 (hpos true) _).sub
      (integrable_armEIF hW hA hYi hps hreg false (hmi false) hov.1 (hpos false) _)
  exact ae_eq_of_forall_integral_mul_eq (measurable_obsData hW hA hY) hϕ
    (measurable_ateEIF hps.1 hreg.1 _) hϕI hEI hϕ0
    (integral_ateEIF_eq_zero hW hA hYi hps hreg hmi hov)
    fun s hs ↦ (hgrad s hs).unique (hg s hs)

/-- **The influence function of a regular estimator of the average effect is a pathwise
gradient.** Under mean ignorability of both arms, a correct propensity score and outcome
regression and strict overlap, an estimator that is asymptotically linear at the average effect
with influence function `φ` on an i.i.d. sample of the observed data, and regular along all
bounded score submodels for `ateRegressionFunctional`, has `φ` as a pathwise gradient. -/
theorem isPathwiseGradientATE_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (ate μ Y) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (ateRegressionFunctional A Y W)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    IsPathwiseGradientATE μ A Y W φ := by
  intro s hs
  have hd := hasDerivAt_regressionFunctional_ate hW hA hY hYi hps hreg hmi hov hs
  have hAL' : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω))
      (ateRegressionFunctional A Y W μ) φ Os P := by
    rwa [ateRegressionFunctional_eq hW hA hYi hps hreg hmi hov]
  have := hR.integral_mul_eq (measurable_obsData hW hA hY) hOs hlaw hAL' hs hs hd
  rw [this]
  exact hd

/-- **A regular estimator of the average effect has the efficient influence function.** -/
theorem ae_eq_ateEIF_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (ate μ Y) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (ateRegressionFunctional A Y W)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    (fun ω ↦ φ (obsData A Y W ω)) =ᵐ[μ] fun ω ↦ ateEIF e m (ate μ Y) (obsData A Y W ω) := by
  have hO := measurable_obsData hW hA hY
  have h2 := memLp_comp_obsData_of_sample hO hOs hlaw hAL.measurable hAL.memLp
  refine ae_eq_ateEIF_of_isPathwiseGradientATE hW hA hY hYi hps hreg hmi hov hAL.measurable
    (h2.integrable one_le_two) ?_
    (isPathwiseGradientATE_of_isRegularAlong hW hA hY hYi hps hreg hmi hov hOs hlaw hAL hR)
  rw [← integral_comp_sample_eq hO hOs hlaw hAL.measurable]
  exact hAL.integral_eq_zero

/-- **A regular estimator of the average effect attains the efficiency bound**
`E[ateEIF(O)²]`. -/
theorem integral_sq_eq_of_isRegularAlong_ate (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (ate μ Y) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (ateRegressionFunctional A Y W)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    ∫ ω, φ (Os 0 ω) ^ 2 ∂P = ∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ^ 2 ∂μ := by
  have hO := measurable_obsData hW hA hY
  rw [integral_comp_sample_eq hO hOs hlaw (g := fun z ↦ φ z ^ 2) (hAL.measurable.pow_const 2)]
  refine integral_congr_ae ?_
  filter_upwards [ae_eq_ateEIF_of_isRegularAlong hW hA hY hYi hps hreg hmi hov hOs hlaw hAL hR]
    with ω hω
  simp only [hω]

/-- **The efficient variance of the average effect.** Under the hypotheses of
`integral_sq_eq_of_isRegularAlong_ate` with square integrable outcomes and `v` the regression of
the squared residual, the asymptotic variance of a regular asymptotically linear estimator is
`E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])`. -/
theorem integral_sq_eq_formula_of_isRegularAlong_ate (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω ↦ (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (ate μ Y) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (ateRegressionFunctional A Y W)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    ∫ ω, φ (Os 0 ω) ^ 2 ∂P =
      ∫ ω, v true (W ω) / e (W ω) ∂μ + ∫ ω, v false (W ω) / (1 - e (W ω)) ∂μ +
        Var[cate μ W Y; μ] := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a ↦ (hY2 a).integrable one_le_two
  rw [integral_sq_eq_of_isRegularAlong_ate hW hA hY hYi hps hreg hmi hov hOs hlaw hAL hR,
    integral_ateEIF_sq hW hA hY hY2 hps hreg hv hmi hov]

/-- **Asymptotic normality at the efficiency bound for the average effect.** -/
theorem tendstoInDistribution_of_isRegularAlong_ate (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hOs : IsIIDSample Os P) (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (ate μ Y) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (ateRegressionFunctional A Y W)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (T n (fun i ↦ Os i ω) - ate μ Y))
      atTop id (fun _ ↦ P) (gaussianReal 0
        (∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ^ 2 ∂μ).toNNReal) := by
  have hR' : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ Os i ω) P := fun n ↦
    AEMeasurable.of_eval fun i ↦ hOs.aemeasurable i
  refine hAL.tendstoInDistribution hOs (fun n ↦ (hR.measurable n).comp_aemeasurable (hR' n)) ?_
  rw [integral_sq_eq_of_isRegularAlong_ate hW hA hY hYi hps hreg hmi hov hOs hlaw hAL hR]
  exact HasLaw.id

end Efficiency
end CausalInference
