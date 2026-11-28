/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.CrossFittingNormality

/-!
# The cross fitted augmented estimator of the average effect

The cross fitted estimator of the average effect `E[Y(1) - Y(0)]` is the difference of the
cross fitted estimators of the two arm means, with the same folds and the same learners
(`crossFitAte`):
`n⁻¹ ∑_k ∑_{i ∈ I_{n,k}} (aipwScore ê_{n,k} m̂_{n,k} 1 - aipwScore ê_{n,k} m̂_{n,k} 0)(O_i)`.
Under strict overlap and rate conditions on the learners of both arms it is asymptotically
linear with the efficient influence function `ateEIF e m (E[Y(1) - Y(0)])`
(`isAsymptoticallyLinear_crossFitAte`) and asymptotically normal with the efficient variance
`E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W])`
(`tendstoInDistribution_crossFitAte`).

## Main definitions

* `crossFitAte`: the cross fitted augmented estimator of the average effect.

## Main results

* `crossFitAte_eq_sum`: the estimator as one cross fitted sum.
* `isAsymptoticallyLinear_crossFitAte`, `tendstoInDistribution_crossFitAte`.

## References

* J. Hahn, *On the role of the propensity score in efficient semiparametric estimation of
  average treatment effects*, Econometrica 66 (1998).
* V. Chernozhukov, D. Chetverikov, M. Demirer, E. Duflo, C. Hansen, W. Newey and J. Robins,
  *Double/debiased machine learning for treatment and structural parameters*, The Econometrics
  Journal 21 (2018).
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

/-- The **cross fitted augmented estimator of the average effect** `E[Y(1) - Y(0)]`: the
difference of the cross fitted estimators of the two arm means, with the same folds and the same
learners. -/
noncomputable def crossFitAte (fold : ℕ → ℕ → Fin K)
    (eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ)
    (mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ)
    (O : ℕ → Ω' → 𝒲 × Bool × ℝ) (n : ℕ) (ω : Ω') : ℝ :=
  crossFitArm fold eHat mHat true O n ω - crossFitArm fold eHat mHat false O n ω

omit [MeasurableSpace 𝒲] in
/-- The cross fitted estimator of the average effect evaluates, at the units of each fold, the
difference of the fitted augmented summands of the two arms with the nuisances fitted on the
other folds. -/
theorem crossFitAte_eq_sum (fold : ℕ → ℕ → Fin K)
    (eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ)
    (mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ)
    (O : ℕ → Ω' → 𝒲 × Bool × ℝ) (n : ℕ) (ω : Ω') :
    crossFitAte fold eHat mHat O n ω = (n : ℝ)⁻¹ * ∑ k, ∑ i ∈ cvFold fold n k,
      (aipwScore (eHat n k (trainingData fold O n k ω)) (mHat n k (trainingData fold O n k ω))
          true (O i ω) -
        aipwScore (eHat n k (trainingData fold O n k ω)) (mHat n k (trainingData fold O n k ω))
          false (O i ω)) := by
  simp only [crossFitAte, crossFitArm, ← mul_sub, ← sum_sub_distrib]

/-- **The cross fitted estimator of the average effect is asymptotically linear with the
efficient influence function.** Let `O` be an i.i.d. sample with the law of the observed data.
Assume mean ignorability of both arms, a correct score and regression, square integrable
potential outcomes and strict overlap `ε ≤ e(W) ≤ 1 - ε`. Let the learners be jointly measurable
in the training data and the covariate, with the fitted score in `[ε', 1 - ε']`. If for every
fold `k` the out of fold `L²(P_W)` errors `‖ê_{n,k} - e‖₂` and `‖m̂_{n,k}(b, ·) - m(b, ·)‖₂`,
`b ∈ {0, 1}`, tend to `0` in probability and `√n ‖ê_{n,k} - e‖₂ ‖m̂_{n,k}(b, ·) - m(b, ·)‖₂ → 0`
in probability for both arms, then the cross fitted estimator of the average effect is
asymptotically linear at `E[Y(1) - Y(0)]` with influence function
`ateEIF e m (E[Y(1) - Y(0)])`. -/
theorem isAsymptoticallyLinear_crossFitAte (fold : ℕ → ℕ → Fin K)
    {eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ}
    {mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ}
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) (hO : IsIIDSample O P)
    (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    (hE : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 => eHat n k p.1 p.2)
    (hM : ∀ n k b, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 =>
      mHat n k p.1 b p.2)
    {ε' : ℝ} (hε' : 0 < ε') (hEb : ∀ n k t w, ε' ≤ eHat n k t w ∧ eHat n k t w ≤ 1 - ε')
    (herrE : ∀ k, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω)) atTop 0)
    (herrM : ∀ k b, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (fun t => mHat n k t b) (m b) (trainingData fold O n k ω)) atTop 0)
    (hprod : ∀ k b, TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) *
      (fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω) *
        fitError (μ.map W) (fun t => mHat n k t b) (m b) (trainingData fold O n k ω))) atTop 0) :
    IsAsymptoticallyLinear (crossFitAte fold eHat mHat O) (ate μ Y) (ateEIF e m (ate μ Y)) O P := by
  have hpos := le_armProb_of_ae (hov.ae_comp hW.aemeasurable)
  have h := (isAsymptoticallyLinear_crossFitArm fold hW hA hY hY2 hps hreg true (hmi true) hov.1
    (hpos true) hO hlaw hE (fun n k => hM n k true) hε' hEb herrE (fun k => herrM k true)
    (fun k => hprod k true)).sub
    (isAsymptoticallyLinear_crossFitArm fold hW hA hY hY2 hps hreg false (hmi false) hov.1
    (hpos false) hO hlaw hE (fun n k => hM n k false) hε' hEb herrE (fun k => herrM k false)
    (fun k => hprod k false))
  rw [ate_eq_armMean_sub ((hY2 true).integrable one_le_two) ((hY2 false).integrable one_le_two)]
  convert h using 1
  · funext n ω
    rfl
  · funext z
    exact ateEIF_eq_sub _ _ z

/-- **The cross fitted estimator of the average effect is asymptotically normal with the
efficient variance**: under the hypotheses of `isAsymptoticallyLinear_crossFitAte`, with `v` the
conditional variance of the outcome given `(W, A)`, `√n (ψ̂_n - E[Y(1) - Y(0)])` converges in
distribution to every variable with law
`N(0, E[v(1, W) / e(W)] + E[v(0, W) / (1 - e(W))] + Var(E[Y(1) - Y(0) | W]))`. -/
theorem tendstoInDistribution_crossFitAte (fold : ℕ → ℕ → Fin K)
    {eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ}
    {mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ}
    (hW : Measurable W) (hA : Measurable A) (hY : ∀ a, Measurable (Y a))
    (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) {v : Bool → 𝒲 → ℝ}
    (hv : IsOutcomeRegression μ A W (fun ω => (obsOutcome A Y ω - m (A ω) (W ω)) ^ 2) v)
    (hmi : ∀ a, MeanIgnorable μ A W Y a) {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε)
    (hO : IsIIDSample O P) (hlaw : P.map (O 0) = μ.map (obsData A Y W))
    (hE : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 => eHat n k p.1 p.2)
    (hM : ∀ n k b, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 =>
      mHat n k p.1 b p.2)
    {ε' : ℝ} (hε' : 0 < ε') (hEb : ∀ n k t w, ε' ≤ eHat n k t w ∧ eHat n k t w ≤ 1 - ε')
    (herrE : ∀ k, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω)) atTop 0)
    (herrM : ∀ k b, TendstoInMeasure P (fun n ω =>
      fitError (μ.map W) (fun t => mHat n k t b) (m b) (trainingData fold O n k ω)) atTop 0)
    (hprod : ∀ k b, TendstoInMeasure P (fun (n : ℕ) ω => ENNReal.ofReal √(n : ℝ) *
      (fitError (μ.map W) (eHat n k) e (trainingData fold O n k ω) *
        fitError (μ.map W) (fun t => mHat n k t b) (m b) (trainingData fold O n k ω))) atTop 0)
    {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {P'' : Measure Ω''} [IsProbabilityMeasure P'']
    {Z : Ω'' → ℝ} (hZ : HasLaw Z (gaussianReal 0 (∫ ω, v true (W ω) / e (W ω) ∂μ +
      ∫ ω, v false (W ω) / (1 - e (W ω)) ∂μ + Var[cate μ W Y; μ]).toNNReal) P'') :
    TendstoInDistribution (fun (n : ℕ) ω => √n * (crossFitAte fold eHat mHat O n ω - ate μ Y))
      atTop Z (fun _ => P) P'' := by
  have hAL := isAsymptoticallyLinear_crossFitAte fold hW hA hY hY2 hps hreg hmi hov hO hlaw hE hM
    hε' hEb herrE herrM hprod
  have hvar : ∫ ω, ateEIF e m (ate μ Y) (O 0 ω) ^ 2 ∂P =
      ∫ ω, v true (W ω) / e (W ω) ∂μ + ∫ ω, v false (W ω) / (1 - e (W ω)) ∂μ +
        Var[cate μ W Y; μ] := by
    rw [integral_comp_obs hW hA hY (hO.aemeasurable 0) hlaw
      ((measurable_ateEIF hps.1 hreg.1 _).pow_const 2)]
    exact integral_ateEIF_sq hW hA hY hY2 hps hreg hv hmi hov
  rw [← hvar] at hZ
  refine hAL.tendstoInDistribution hO (fun n => ?_) hZ
  exact (aemeasurable_crossFitArm fold hE (fun n k => hM n k true) hO.aemeasurable n).sub
    (aemeasurable_crossFitArm fold hE (fun n k => hM n k false) hO.aemeasurable n)

end Efficiency
end CausalInference
