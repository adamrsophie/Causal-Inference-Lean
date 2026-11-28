/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.InfluenceFunction
public import CausalInference.Estimation.AsymptoticLinear

/-!
# Asymptotic normality of the augmented estimator with the true nuisance functions

Let `O_i = (W_i, A_i, Y_i)` be an i.i.d. sample whose observations have the law of the observed
data `(W, A, Y)` of the population. The oracle augmented estimator of the arm mean is the sample
mean of the augmented summand `aipwScore e m a` with the true score `e` and the true
regression `m`. It is asymptotically linear at `E[Y(a)]` with influence function the efficient
influence function `armEIF`, so `√n (ψ̂ - E[Y(a)])` converges in distribution to the centered
Gaussian with variance `E[v(a, W) / π_a(W)] + Var(E[Y(a) | W])`. The same holds for the average
effect, with variance `E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])`.

## Main results

* `memLp_armEIF`: the efficient influence function is square integrable.
* `isAsymptoticallyLinear_sampleMean_aipwScore`: asymptotic linearity of the oracle estimator of
  the arm mean, as `IsAsymptoticallyLinear`.
* `isAsymptoticallyLinear_sampleMean_aipwScore_ate`: the same for the average effect.
* `tendstoInDistribution_sampleMean_aipwScore`,
  `tendstoInDistribution_sampleMean_aipwScore_ate`: asymptotic normality with the efficient
  variances.

## References

* J. M. Robins, A. Rotnitzky and L. P. Zhao, *Estimation of regression coefficients when some
  regressors are not always observed*, Journal of the American Statistical Association 89
  (1994).
* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66 (1998).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory MissingData PointTreatment Filter

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The efficient influence function of an arm mean is square integrable at the observed data,
for square integrable potential outcomes and `π_a(W) ≥ ε > 0`. -/
theorem memLp_armEIF (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (ψ : ℝ) :
    MemLp (fun ω => armEIF e m a ψ (obsData A Y W ω)) 2 μ := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hpos' : ∀ᵐ ω ∂μ, 0 < armProb e a (W ω) := hpos.mono fun _ h => hε.trans_le h
  have hYo2 := memLp_obsOutcome hA hY hY2
  have hid := hreg.ae_eq_condExp hW hA hYi hps a hmi hpos'
  have hm2 : MemLp (fun ω => m a (W ω)) 2 μ := ((hY2 a).condExp one_le_two).ae_eq hid.symm
  have hR2 := memLp_weightedResidual hA hW hps.1 (hreg.1 a) hYo2 hm2 hε hpos
  exact (hR2.add (hm2.sub (memLp_const ψ))).ae_eq
    (hpos'.mono fun ω h => (armEIF_obsData_eq a ψ h.ne').symm)

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} [IsProbabilityMeasure P]
  {O : ℕ → Ω' → 𝒲 × Bool × ℝ}

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Moments of a function of the first observation are moments under the population when the
observation has the law of the observed data. -/
theorem integral_comp_obs (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hO : AEMeasurable (O 0) P) (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    {f : 𝒲 × Bool × ℝ → ℝ} (hf : Measurable f) :
    ∫ ω, f (O 0 ω) ∂P = ∫ ω, f (obsData A Y W ω) ∂μ := by
  rw [← integral_map hO hf.aestronglyMeasurable, hlaw,
    integral_map (measurable_obsData hW hA hY).aemeasurable hf.aestronglyMeasurable]

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
theorem memLp_comp_obs (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hO : AEMeasurable (O 0) P) (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    {f : 𝒲 × Bool × ℝ → ℝ} (hf : Measurable f)
    (h2 : MemLp (fun ω => f (obsData A Y W ω)) 2 μ) : MemLp (fun ω => f (O 0 ω)) 2 P := by
  have h := (memLp_map_measure_iff hf.aestronglyMeasurable
    (measurable_obsData hW hA hY).aemeasurable).2 h2
  rw [← hlaw] at h
  exact (memLp_map_measure_iff hf.aestronglyMeasurable hO).1 h

/-- **The oracle augmented estimator of an arm mean is asymptotically linear** with the efficient
influence function. For an i.i.d. sample with the law of the observed data, under mean
ignorability of the arm, a correct score and regression, square integrable potential outcomes
and `π_a(W) ≥ ε > 0`, the sample mean of `aipwScore e m a` is asymptotically linear at
`E[Y(a)]` with influence function `armEIF e m a E[Y(a)]`. -/
theorem isAsymptoticallyLinear_sampleMean_aipwScore (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hO : AEMeasurable (O 0) P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W)) :
    IsAsymptoticallyLinear (sampleMean (aipwScore e m a) O) (armMean μ Y a)
      (armEIF e m a (armMean μ Y a)) O P := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a => (hY2 a).integrable one_le_two
  have hf := measurable_aipwScore hps.1 (hreg.1 a)
  have h2 := memLp_armEIF hW hA hY hY2 hps hreg a hmi hε hpos 0
  have h2' : MemLp (fun ω => aipwScore e m a (obsData A Y W ω)) 2 μ :=
    (h2.add (memLp_const 0)).ae_eq (Eventually.of_forall fun ω => by simp [armEIF])
  have hmean : ∫ ω, aipwScore e m a (O 0 ω) ∂P = armMean μ Y a := by
    rw [integral_comp_obs hW hA hY hO hlaw hf]
    have h0 := integral_armEIF_eq_zero hW hA hYi hps hreg a hmi hε hpos
    simp only [armEIF] at h0
    rw [integral_sub (h2'.integrable one_le_two) (integrable_const _), integral_const] at h0
    simpa [sub_eq_zero] using h0
  have h := sampleMean_isAsymptoticallyLinear hf (memLp_comp_obs hW hA hY hO hlaw hf h2')
  rw [hmean] at h
  exact h

/-- **The oracle augmented estimator of an arm mean is asymptotically normal with the efficient
variance**: `√n (ψ̂ - E[Y(a)])` converges in distribution to every variable with law
`N(0, E[v(a, W) / π_a(W)] + Var(E[Y(a) | W]))`. -/
theorem tendstoInDistribution_sampleMean_aipwScore (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Z : Ω'' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
      Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ]).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (sampleMean (aipwScore e m a) O n ω -
      armMean μ Y a)) atTop Z (fun _ => P) P'' := by
  have hAL := isAsymptoticallyLinear_sampleMean_aipwScore hW hA hY hY2 hps hreg a hmi hε hpos
    (hO.aemeasurable 0) hlaw
  have hvar : ∫ ω, armEIF e m a (armMean μ Y a) (O 0 ω) ^ 2 ∂P =
      ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
        Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] := by
    rw [integral_comp_obs hW hA hY (hO.aemeasurable 0) hlaw
      ((measurable_armEIF hps.1 (hreg.1 a) _).pow_const 2)]
    exact integral_armEIF_sq hW hA hY hY2 hps hreg hv a hmi hε hpos
  rw [← hvar] at hZ
  exact hAL.tendstoInDistribution_of_isSampleMeasurable hO
    (isSampleMeasurable_sampleMean (measurable_aipwScore hps.1 (hreg.1 a)) O) hZ

/-- The oracle augmented estimator of the average effect: the difference of the sample means of
the augmented summands of the two arms. -/
theorem isAsymptoticallyLinear_sampleMean_aipwScore_ate (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) (hO : AEMeasurable (O 0) P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W)) :
    IsAsymptoticallyLinear (fun n ω => sampleMean (aipwScore e m true) O n ω -
      sampleMean (aipwScore e m false) O n ω) (ate μ Y) (ateEIF e m (ate μ Y)) O P := by
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  have h := (isAsymptoticallyLinear_sampleMean_aipwScore hW hA hY hY2 hps hreg true (hmi true)
    hov.1 (hpos true) hO hlaw).sub (isAsymptoticallyLinear_sampleMean_aipwScore hW hA hY hY2
      hps hreg false (hmi false) hov.1 (hpos false) hO hlaw)
  rw [ate_eq_armMean_sub ((hY2 true).integrable one_le_two) ((hY2 false).integrable one_le_two)]
  convert h using 1
  funext z
  exact ateEIF_eq_sub _ _ z

/-- **The oracle augmented estimator of the average effect is asymptotically normal with the
efficient variance** `E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])`. -/
theorem tendstoInDistribution_sampleMean_aipwScore_ate (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Z : Ω'' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (∫ ω, v true (W ω) / e (W ω) ∂μ +
      ∫ ω, v false (W ω) / (1 - e (W ω)) ∂μ + Var[cate μ W Y; μ]).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * ((sampleMean (aipwScore e m true) O n ω -
      sampleMean (aipwScore e m false) O n ω) - ate μ Y)) atTop Z (fun _ => P) P'' := by
  have hAL := isAsymptoticallyLinear_sampleMean_aipwScore_ate hW hA hY hY2 hps hreg hmi hov
    (hO.aemeasurable 0) hlaw
  have hvar : ∫ ω, ateEIF e m (ate μ Y) (O 0 ω) ^ 2 ∂P =
      ∫ ω, v true (W ω) / e (W ω) ∂μ + ∫ ω, v false (W ω) / (1 - e (W ω)) ∂μ +
        Var[cate μ W Y; μ] := by
    rw [integral_comp_obs hW hA hY (hO.aemeasurable 0) hlaw
      ((measurable_ateEIF hps.1 hreg.1 _).pow_const 2)]
    exact integral_ateEIF_sq hW hA hY hY2 hps hreg hv hmi hov
  rw [← hvar] at hZ
  refine hAL.tendstoInDistribution hO (fun n => ?_) hZ
  exact (((isSampleMeasurable_sampleMean (measurable_aipwScore hps.1 (hreg.1 true)) O).aemeasurable
    hO n).sub ((isSampleMeasurable_sampleMean (measurable_aipwScore hps.1 (hreg.1 false))
      O).aemeasurable hO n))

end Efficiency
end CausalInference
