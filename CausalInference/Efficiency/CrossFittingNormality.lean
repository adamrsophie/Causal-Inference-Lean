/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.CrossFittingRemainder

/-!
# Asymptotic normality of the cross fitted augmented estimator of an arm mean

Under rate conditions on the learners, the cross fitted augmented estimator
`ψ̂_n = n⁻¹ ∑_k ∑_{i ∈ I_{n,k}} aipwScore ê_{n,k} m̂_{n,k} a (O_i)` of `E[Y(a)]` is
asymptotically linear with the efficient influence function `armEIF e m a E[Y(a)]`
(`isAsymptoticallyLinear_crossFitArm`), hence asymptotically normal with the efficient variance
`E[v(a, W) / π_a(W)] + Var(E[Y(a) | W])` (`tendstoInDistribution_crossFitArm`): it attains the
efficiency bound.

The hypotheses are an i.i.d. sample with the law of the observed data; mean ignorability of the
arm, a correct score and regression, square integrable potential outcomes and
`π_a(W) ≥ ε > 0`; learners jointly measurable in the training data and the covariate, with the
fitted score in `[ε', 1 - ε']`; and, for every fold, out of fold `L²(P_W)` errors of the two
learners tending to zero in probability with product `o_P(n^{-1/2})`. The fold remainders are
`o_P(n^{-1/2})` by `tendstoInMeasure_sqrt_mul_foldRemainder`, and the measurability of the
estimator follows from that of the learners (`aemeasurable_crossFitArm`).

## Main definitions

* None: the file states the limit laws of the estimator `crossFitArm` of
  `CausalInference.Efficiency.CrossFitting`.

## Main results

* `isAsymptoticallyLinear_crossFitArm`: asymptotic linearity with the efficient influence
  function.
* `tendstoInDistribution_crossFitArm`: asymptotic normality with the efficient variance.

## References

* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, The Econometrics
  Journal 21 (2018).
* W. Zheng and M. J. van der Laan, *Cross-validated targeted minimum-loss-based estimation*, in
  *Targeted Learning*, Springer (2011).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory MissingData PointTreatment Filter Finset

variable {K : ℕ} {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} [IsProbabilityMeasure P]
  {O : ℕ → Ω' → 𝒲 × Bool × ℝ}

/-- **The cross fitted estimator of an arm mean is asymptotically linear with the efficient
influence function.** Let `O` be an i.i.d. sample with the law of the observed data. Assume mean
ignorability of the arm `a`, a correct score `e` and regression `m`, square integrable potential
outcomes and `π_a(W) ≥ ε > 0` almost surely. Let the learners `ê_{n,k}`, `m̂_{n,k}` of every
fold be jointly measurable in the training data and the covariate, with the fitted score in
`[ε', 1 - ε']`. If for every fold `k` the out of fold `L²(P_W)` errors
`‖ê_{n,k} - e‖₂` and `‖m̂_{n,k}(a, ·) - m(a, ·)‖₂` (`fitError`) tend to `0` in probability and
`√n ‖ê_{n,k} - e‖₂ ‖m̂_{n,k}(a, ·) - m(a, ·)‖₂ → 0` in probability, then the cross fitted
estimator is asymptotically linear at `E[Y(a)]` with influence function
`armEIF e m a E[Y(a)]`. -/
theorem isAsymptoticallyLinear_crossFitArm (fold : ℕ → ℕ → Fin K)
    {eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ}
    {mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ}
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    (hE : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 => eHat n k p.1 p.2)
    (hM : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 =>
      mHat n k p.1 a p.2)
    {ε' : ℝ} (hε' : 0 < ε') (hEb : ∀ n k t w, ε' ≤ eHat n k t w ∧ eHat n k t w ≤ 1 - ε')
    (herrE : ∀ k, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω)) atTop 0)
    (herrM : ∀ k, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (fun t => mHat n k t a) (m a) (trainingData fold O n k ω)) atTop 0)
    (hprod : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) *
      (fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω) *
        fitError (μ.map W) (fun t => mHat n k t a) (m a) (trainingData fold O n k ω))) atTop 0) :
    IsAsymptoticallyLinear (crossFitArm fold eHat mHat a O) (armMean μ Y a)
      (armEIF e m a (armMean μ Y a)) O P := by
  refine (isAsymptoticallyLinear_sampleMean_aipwScore hW hA hY hY2 hps hreg a hmi hε hpos
    (hO.aemeasurable 0) hlaw).of_tendstoInMeasure_sqrt_mul_sub ?_
  have hrem : ∀ k, TendstoInMeasure P
      (fun (n : ℕ) ω => √n * foldRemainder fold eHat mHat e m a O k n ω) atTop 0 := fun k =>
    tendstoInMeasure_sqrt_mul_foldRemainder fold hW hA hY hY2 hps hreg a hmi hε hpos hO hlaw hE
      hM hε' hEb k (herrE k) (herrM k) (hprod k)
  have h := tendstoInMeasure_finset_sum (μ := P) univ (fun k _ => hrem k)
  convert h using 2 with n
  funext ω
  rw [crossFitArm_sub_sampleMean, mul_sum]

/-- **The cross fitted estimator of an arm mean is asymptotically normal with the efficient
variance**: under the hypotheses of `isAsymptoticallyLinear_crossFitArm`, with `v` the
conditional variance of the outcome given `(W, A)`, `√n (ψ̂_n - E[Y(a)])` converges in
distribution to every variable with law `N(0, E[v(a, W) / π_a(W)] + Var(E[Y(a) | W]))`. -/
theorem tendstoInDistribution_crossFitArm (fold : ℕ → ℕ → Fin K)
    {eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ}
    {mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ}
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    (hE : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 => eHat n k p.1 p.2)
    (hM : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 =>
      mHat n k p.1 a p.2)
    {ε' : ℝ} (hε' : 0 < ε') (hEb : ∀ n k t w, ε' ≤ eHat n k t w ∧ eHat n k t w ≤ 1 - ε')
    (herrE : ∀ k, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω)) atTop 0)
    (herrM : ∀ k, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (fun t => mHat n k t a) (m a) (trainingData fold O n k ω)) atTop 0)
    (hprod : ∀ k, TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) *
      (fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω) *
        fitError (μ.map W) (fun t => mHat n k t a) (m a) (trainingData fold O n k ω))) atTop 0)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Z : Ω'' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
      Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ]).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (crossFitArm fold eHat mHat a O n ω -
      armMean μ Y a)) atTop Z (fun _ => P) P'' := by
  have hAL := isAsymptoticallyLinear_crossFitArm fold hW hA hY hY2 hps hreg a hmi hε hpos hO
    hlaw hE hM hε' hEb herrE herrM hprod
  have hvar : ∫ ω, armEIF e m a (armMean μ Y a) (O 0 ω) ^ 2 ∂P =
      ∫ ω, v a (W ω) / armProb e a (W ω) ∂μ +
        Var[μ[Y a | MeasurableSpace.comap W inferInstance]; μ] := by
    rw [integral_comp_obs hW hA hY (hO.aemeasurable 0) hlaw
      ((measurable_armEIF hps.1 (hreg.1 a) _).pow_const 2)]
    exact integral_armEIF_sq hW hA hY hY2 hps hreg hv a hmi hε hpos
  rw [← hvar] at hZ
  exact hAL.tendstoInDistribution hO (aemeasurable_crossFitArm fold hE hM hO.aemeasurable) hZ

end Efficiency
end CausalInference
