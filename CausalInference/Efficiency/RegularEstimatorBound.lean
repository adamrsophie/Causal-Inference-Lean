/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.GradientOfRegular

/-!
# The efficiency bound for regular estimators of an arm mean

Let `μ` be a population law with covariates `W`, a binary treatment `A`, potential outcomes `Y`
and observed data `O = (W, A, Y(A))`, under mean ignorability, a correct propensity score and
outcome regression, strict overlap and square integrable outcomes. Let `T_n` be an estimator of
the arm mean `E[Y(a)]` computed from an i.i.d. sample of the observed data, asymptotically linear
at `E[Y(a)]` with influence function `φ` and regular along the score submodels
(`IsRegularAlong` with the class of all bounded scores and the regression functional). Then:

* `φ` is a pathwise gradient of the arm mean (`isPathwiseGradient_of_isRegularAlong`);
* `φ(O) = φ_a(O)` almost surely, with `φ_a = armEIF` the efficient influence function
  (`ae_eq_armEIF_of_isRegularAlong`);
* the asymptotic variance `E[φ(O)²]` equals the efficiency bound `V_a = E[φ_a(O)²]`
  (`integral_sq_eq_of_isRegularAlong`), and `√n (T_n - E[Y(a)])` converges in distribution to
  `N(0, V_a)` (`tendstoInDistribution_of_isRegularAlong`).

In the nonparametric model every bounded mean zero function of the observed data is a score, so
the tangent space is dense in the mean zero square integrable functions. A gradient is
determined by its inner products with all scores, and two gradients agree almost surely
(`ae_eq_armEIF_of_isPathwiseGradient`). Since the influence function of a regular
asymptotically linear estimator is a gradient, all such estimators share the influence function
`φ_a` and are asymptotically equivalent; the bound `V_a` is attained by each of them, not just
bounded from below.

If regularity is only known along a subclass `𝒮` of scores, the influence function is a
gradient along `𝒮` only; it is no longer determined, but its variance still bounds each
submodel bound `ψ'(0)² / E[s(O)²]`, `s ∈ 𝒮` (`integral_sq_mem_upperBounds_of_isRegularAlong`).

None of the results assume that `φ` is a pathwise gradient; regularity implies it.

## Main definitions

* `armRegressionFunctional`: the arm mean as a functional of the population law.

## Main results

* `isPathwiseGradient_of_isRegularAlong`
* `ae_eq_armEIF_of_isRegularAlong`
* `integral_sq_eq_of_isRegularAlong`, `integral_sq_eq_formula_of_isRegularAlong`
* `tendstoInDistribution_of_isRegularAlong`
* `integral_sq_mem_upperBounds_of_isRegularAlong`

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
* J. Hahn, On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects, *Econometrica* 66 (1998), 315-331.
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

/-- The arm mean `E[Y(a)]` as a functional of the population law. -/
noncomputable abbrev armRegressionFunctional (A : Ω → Bool) (Y : Bool → Ω → ℝ) (W : Ω → 𝒲)
    (a : Bool) : Measure Ω → ℝ :=
  fun ν ↦ regressionFunctional ν (arm A a) W (obsOutcome A Y)

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Moments of the influence function on the sample are moments on the observed data. -/
theorem integral_comp_sample_eq (hO : Measurable (obsData A Y W)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W)) {g : 𝒲 × Bool × ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (Os 0 ω) ∂P = ∫ ω, g (obsData A Y W ω) ∂μ := by
  rw [← integral_map (hOs.aemeasurable 0) hg.aestronglyMeasurable, hlaw,
    integral_map hO.aemeasurable hg.aestronglyMeasurable]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem memLp_comp_obsData_of_sample (hO : Measurable (obsData A Y W)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W)) {g : 𝒲 × Bool × ℝ → ℝ} (hg : Measurable g)
    (h2 : MemLp (fun ω ↦ g (Os 0 ω)) 2 P) : MemLp (fun ω ↦ g (obsData A Y W ω)) 2 μ := by
  have h1 : MemLp g 2 (P.map (Os 0)) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable (hOs.aemeasurable 0)).2 h2
  rw [hlaw] at h1
  exact (memLp_map_measure_iff hg.aestronglyMeasurable hO.aemeasurable).1 h1

/-- **The influence function of a regular estimator of an arm mean is a pathwise gradient.**
Under mean ignorability, a correct propensity score and outcome regression and strict overlap,
an estimator that is asymptotically linear at `E[Y(a)]` with influence function `φ` on an i.i.d.
sample of the observed data, and regular along all bounded score submodels, has `φ` as a
pathwise gradient of the arm mean. The derivative along each submodel is
`hasDerivAt_regressionFunctional_arm`; the identity `E[φ s] = ψ'(0)` is
`IsRegularAlong.integral_mul_eq`. -/
theorem isPathwiseGradient_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (armMean μ Y a) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    IsPathwiseGradient μ A Y W a φ := by
  intro s hs
  have hd := hasDerivAt_regressionFunctional_arm hW hA hY hYi hps hreg a hmi hε hpos hs.1
    hs.2.1.choose_spec hs.2.2
  have hAL' : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω))
      (armRegressionFunctional A Y W a μ) φ Os P := by
    rwa [armRegressionFunctional, regressionFunctional_arm_eq hW hA hYi hps hreg a hmi hε hpos]
  have := hR.integral_mul_eq (measurable_obsData hW hA hY) hOs hlaw hAL' hs hs hd
  rw [this]
  exact hd

/-- **A regular estimator of an arm mean has the efficient influence function.** Under the
hypotheses of `isPathwiseGradient_of_isRegularAlong`, `φ(O) = φ_a(O)` almost surely. -/
theorem ae_eq_armEIF_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (armMean μ Y a) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    (fun ω ↦ φ (obsData A Y W ω)) =ᵐ[μ]
      fun ω ↦ armEIF e m a (armMean μ Y a) (obsData A Y W ω) := by
  have hO := measurable_obsData hW hA hY
  have h2 := memLp_comp_obsData_of_sample hO hOs hlaw hAL.measurable hAL.memLp
  refine ae_eq_armEIF_of_isPathwiseGradient hW hA hY hYi hps hreg a hmi hε hpos hAL.measurable
    (h2.integrable one_le_two) ?_
    (isPathwiseGradient_of_isRegularAlong hW hA hY hYi hps hreg a hmi hε hpos hOs hlaw hAL hR)
  rw [← integral_comp_sample_eq hO hOs hlaw hAL.measurable]
  exact hAL.integral_eq_zero

/-- **A regular estimator of an arm mean attains the efficiency bound.** Under the hypotheses of
`isPathwiseGradient_of_isRegularAlong`, the asymptotic variance `E[φ(O)²]` of the estimator is
the efficiency bound `V_a = E[φ_a(O)²]`. -/
theorem integral_sq_eq_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (armMean μ Y a) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    ∫ ω, φ (Os 0 ω) ^ 2 ∂P = ∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ := by
  have hO := measurable_obsData hW hA hY
  rw [integral_comp_sample_eq hO hOs hlaw (g := fun z ↦ φ z ^ 2) (hAL.measurable.pow_const 2)]
  refine integral_congr_ae ?_
  filter_upwards [ae_eq_armEIF_of_isRegularAlong hW hA hY hYi hps hreg a hmi hε hpos hOs hlaw
    hAL hR] with ω hω
  simp only [hω]

/-- **The efficiency bound in closed form.** Under the hypotheses of
`integral_sq_eq_of_isRegularAlong` with square integrable outcomes and `v` the regression of the
squared residual, the asymptotic variance is
`E[v_a(W) / P(A = a | W)] + Var(E[Y(a) | W])`. -/
theorem integral_sq_eq_formula_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω ↦ (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (armMean μ Y a) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    ∫ ω, φ (Os 0 ω) ^ 2 ∂P = ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
      Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a ↦ (hY2 a).integrable one_le_two
  have hO := measurable_obsData hW hA hY
  have h2 := memLp_comp_obsData_of_sample hO hOs hlaw hAL.measurable hAL.memLp
  rw [integral_comp_sample_eq hO hOs hlaw (g := fun z ↦ φ z ^ 2) (hAL.measurable.pow_const 2)]
  refine integral_sq_eq_of_isPathwiseGradient hW hA hY hY2 hps hreg hv a hmi hε hpos
    hAL.measurable (h2.integrable one_le_two) ?_
    (isPathwiseGradient_of_isRegularAlong hW hA hY hYi hps hreg a hmi hε hpos hOs hlaw hAL hR)
  rw [← integral_comp_sample_eq hO hOs hlaw hAL.measurable]
  exact hAL.integral_eq_zero

/-- **Asymptotic normality at the efficiency bound.** Under the hypotheses of
`integral_sq_eq_of_isRegularAlong`, `√n (T_n - E[Y(a)])` converges in distribution to
`N(0, V_a)`, `V_a = E[φ_a(O)²]`. -/
theorem tendstoInDistribution_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (armMean μ Y a) φ Os P)
    (hR : IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s} T L) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (T n (fun i ↦ Os i ω) - armMean μ Y a))
      atTop id (fun _ ↦ P) (gaussianReal 0
        (∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ).toNNReal) := by
  have hR' : ∀ n, AEMeasurable (fun ω (i : Fin n) ↦ Os i ω) P := fun n ↦
    AEMeasurable.of_eval fun i ↦ hOs.aemeasurable i
  refine hAL.tendstoInDistribution hOs (fun n ↦ (hR.measurable n).comp_aemeasurable (hR' n)) ?_
  rw [integral_sq_eq_of_isRegularAlong hW hA hY hYi hps hreg a hmi hε hpos hOs hlaw hAL hR]
  exact HasLaw.id

/-- **The sub-family form of the bound.** If the estimator is regular only along the submodels of
a class `𝒮` of bounded scores, its asymptotic variance `E[φ(O)²]` is still an upper bound of the
submodel bounds `ψ'(0)² / E[s(O)²]` over `s ∈ 𝒮` with `E[s(O)²] > 0`: the influence function is a
gradient along each submodel in `𝒮` and the Cauchy-Schwarz inequality applies. -/
theorem integral_sq_mem_upperBounds_of_isRegularAlong (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W))
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (armMean μ Y a) φ Os P)
    {𝒮 : Set (𝒲 × Bool × ℝ → ℝ)}
    (hR : IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a) 𝒮 T L) :
    ∫ ω, φ (Os 0 ω) ^ 2 ∂P ∈ upperBounds {r | ∃ s ∈ 𝒮, IsBoundedScore μ (obsData A Y W) s ∧
        0 < ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ ∧ ∃ d, HasDerivAt (fun t ↦ regressionFunctional
          (scoreTilt μ (fun ω ↦ s (obsData A Y W ω)) t) (arm A a) W (obsOutcome A Y)) d 0 ∧
        r = d ^ 2 / ∫ ω, s (obsData A Y W ω) ^ 2 ∂μ} := by
  have hO := measurable_obsData hW hA hY
  rintro r ⟨s, hs𝒮, hs, hI, d, hd, rfl⟩
  have hAL' : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω))
      (armRegressionFunctional A Y W a μ) φ Os P := by
    rwa [armRegressionFunctional, regressionFunctional_arm_eq hW hA hYi hps hreg a hmi hε hpos]
  have hgrad := hR.integral_mul_eq hO hOs hlaw hAL' hs𝒮 hs hd
  have h2 := memLp_comp_obsData_of_sample hO hOs hlaw hAL.measurable hAL.memLp
  have hcs := sq_integral_mul_le_mul h2 (hs.memLp hO 2)
  rw [hgrad] at hcs
  rw [integral_comp_sample_eq hO hOs hlaw (g := fun z ↦ φ z ^ 2) (hAL.measurable.pow_const 2),
    div_le_iff₀ hI]
  exact hcs

end Efficiency
end CausalInference
