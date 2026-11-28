/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.OracleNormality
public import CausalInference.Estimation.DeltaMethodSeveralSamples

/-!
# The cross fitted augmented estimator

The units `0, …, n - 1` of a sample of size `n` are split into `K` folds by an assignment
`fold n : ℕ → Fin K`. For each fold `k`, the working score `ê_{n,k}` and the working regression
`m̂_{n,k}` are **fitted on the other folds**: they are functions of the training data
`(O_i)_{i ∈ T_{n,k}}`, `T_{n,k} = {i < n : fold n i ≠ k}`, and of nothing else
(`trainingData`). The cross fitted estimator of the arm mean evaluates the augmented summand with
the nuisances of fold `k` at the units of fold `k`:
`ψ̂_n = n⁻¹ ∑_k ∑_{i ∈ I_{n,k}} aipwScore ê_{n,k} m̂_{n,k} a (O_i)`, with
`I_{n,k} = {i < n : fold n i = k}`.

The difference with the oracle estimator is a sum over the folds of the fold remainders
`R_{n,k} = n⁻¹ ∑_{i ∈ I_{n,k}} (aipwScore ê_{n,k} m̂_{n,k} a - aipwScore e m a)(O_i)`
(`crossFitArm_sub_sampleMean`).

The accuracy of a learner is measured by its `L²` error `fitError`: for a fitted function
`ĥ(t, ·)` built from a training data set `t` and a target `h`, the `L²(P_W)` norm of
`ĥ(t, ·) - h`, a value in `[0, ∞]`. Evaluated at the training data of a fold it is a random
variable, measurable when the learner is jointly measurable (`measurable_fitError`).
The remainder rate and the normality theorems are in
`CausalInference.Efficiency.CrossFittingRemainder` and
`CausalInference.Efficiency.CrossFittingNormality`.

## Main definitions

* `cvFold`, `cvTrain`: the evaluation fold and the training units.
* `trainingData`: the observations of the training units.
* `fitError`: the `L²` error of a fitted function.
* `crossFitArm`: the cross fitted augmented estimator of an arm mean.
* `foldRemainder`: the fold remainder.

## Main results

* `crossFitArm_sub_sampleMean`: the decomposition into fold remainders.
* `measurable_eLpNorm_two`, `measurable_fitError`: measurability of `L²` norms of a jointly
  measurable family.
* `measurable_aipwScore_fitted`, `aemeasurable_crossFitArm`: measurability of the estimator for
  jointly measurable learners.

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
open scoped ENNReal

variable {K : ℕ}

/-- The evaluation fold `I_{n,k} = {i < n : fold n i = k}`. -/
def cvFold (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) : Finset ℕ :=
  (range n).filter fun i => fold n i = k

/-- The training units `T_{n,k} = {i < n : fold n i ≠ k}` of the fold `k`. -/
def cvTrain (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) : Finset ℕ :=
  (range n).filter fun i => fold n i ≠ k

theorem disjoint_cvFold_cvTrain (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) :
    Disjoint (cvFold fold n k) (cvTrain fold n k) := by
  rw [cvFold, cvTrain]
  exact disjoint_filter.2 fun _ _ h h' => h' h

theorem card_cvFold_le (fold : ℕ → ℕ → Fin K) (n : ℕ) (k : Fin K) :
    (cvFold fold n k).card ≤ n :=
  (card_filter_le _ _).trans_eq (card_range n)

variable {Ω' 𝒪 : Type*} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace 𝒪]

/-- The training data of the fold `k`: the observations `(O_i)_{i ∈ T_{n,k}}`. A nuisance is
**fitted on the other folds** when it is a function of `trainingData fold O n k` only. -/
def trainingData (fold : ℕ → ℕ → Fin K) (O : ℕ → Ω' → 𝒪) (n : ℕ) (k : Fin K) (ω : Ω') :
    cvTrain fold n k → 𝒪 := fun i => O i ω

theorem measurable_trainingData (fold : ℕ → ℕ → Fin K) {O : ℕ → Ω' → 𝒪}
    (hO : ∀ i, Measurable (O i)) (n : ℕ) (k : Fin K) :
    Measurable (trainingData fold O n k) :=
  measurable_pi_iff.2 fun i => hO i

theorem aemeasurable_trainingData (fold : ℕ → ℕ → Fin K) {O : ℕ → Ω' → 𝒪} {P : Measure Ω'}
    (hO : ∀ i, AEMeasurable (O i) P) (n : ℕ) (k : Fin K) :
    AEMeasurable (trainingData fold O n k) P :=
  AEMeasurable.of_eval fun i => hO i

section FitError

variable {𝒯 𝒵 𝒲 : Type*} [MeasurableSpace 𝒯] [MeasurableSpace 𝒵] [MeasurableSpace 𝒲]

/-- The `L²(ν)` norms `t ↦ ‖F(t, ·)‖_{L²(ν)}` of the sections of a jointly measurable function
form a measurable function of the parameter `t`. -/
theorem measurable_eLpNorm_two {F : 𝒯 × 𝒵 → ℝ} (hF : Measurable F) (ν : Measure 𝒵)
    [SFinite ν] : Measurable fun t => eLpNorm (fun z => F (t, z)) 2 ν := by
  have h : (fun t => eLpNorm (fun z => F (t, z)) 2 ν) =
      fun t => (∫⁻ z, ‖F (t, z)‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    funext t
    exact eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (hF.comp measurable_prodMk_left).aestronglyMeasurable
  rw [h]
  exact (Measurable.lintegral_prod_right' (hF.eNorm.pow_const _)).pow_const _

/-- **The `L²` error of a fitted function.** For a learner `hHat`, which maps a training data set
`t` to a function `hHat t : 𝒲 → ℝ`, and a target function `h`, `fitError ν hHat h t` is the
`L²(ν)` norm `(∫ (hHat t w - h w)² dν(w))^{1/2}` of the error `hHat t - h`, a value in `[0, ∞]`
(it is `∞` when the error is not square integrable). With `ν = P_W`, the law of the covariate,
and `t` the training data of a fold, it is the out of fold `L²` error of the learner, a random
variable. -/
noncomputable def fitError (ν : Measure 𝒲) (hHat : 𝒯 → 𝒲 → ℝ) (h : 𝒲 → ℝ) (t : 𝒯) : ℝ≥0∞ :=
  eLpNorm (fun w => hHat t w - h w) 2 ν

/-- For a jointly measurable learner and a measurable target, the `L²` error is a measurable
function of the training data. -/
theorem measurable_fitError {ν : Measure 𝒲} [SFinite ν] {hHat : 𝒯 → 𝒲 → ℝ}
    (hHatm : Measurable fun p : 𝒯 × 𝒲 => hHat p.1 p.2) {h : 𝒲 → ℝ} (hm : Measurable h) :
    Measurable (fitError ν hHat h) :=
  measurable_eLpNorm_two (hHatm.sub (hm.comp measurable_snd)) ν

omit [MeasurableSpace 𝒯] in
/-- The `L²` error of a fitted function under the law of a covariate `W` is the `L²` norm of the
error at the covariate. -/
theorem fitError_map {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {W : Ω → 𝒲}
    (hW : Measurable W) {hHat : 𝒯 → 𝒲 → ℝ} {t : 𝒯} (hHatm : Measurable (hHat t)) {h : 𝒲 → ℝ}
    (hm : Measurable h) :
    fitError (μ.map W) hHat h t = eLpNorm (fun ω => hHat t (W ω) - h (W ω)) 2 μ :=
  eLpNorm_map_measure (hHatm.sub hm).aestronglyMeasurable hW.aemeasurable

end FitError

variable {𝒲 : Type*} [MeasurableSpace 𝒲]

/-- The **cross fitted augmented estimator** of the arm mean `E[Y(a)]`: for the learners `eHat`
and `mHat`, which map the training data of a fold to a working score and a working regression,
`ψ̂_n = n⁻¹ ∑_k ∑_{i ∈ I_{n,k}} aipwScore ê_{n,k} m̂_{n,k} a (O_i)`. -/
noncomputable def crossFitArm (fold : ℕ → ℕ → Fin K)
    (eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ)
    (mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ)
    (a : Bool) (O : ℕ → Ω' → 𝒲 × Bool × ℝ) (n : ℕ) (ω : Ω') : ℝ :=
  (n : ℝ)⁻¹ * ∑ k, ∑ i ∈ cvFold fold n k,
    aipwScore (eHat n k (trainingData fold O n k ω)) (mHat n k (trainingData fold O n k ω)) a
      (O i ω)

/-- The fold remainder `R_{n,k} = n⁻¹ ∑_{i ∈ I_{n,k}} (aipwScore ê_{n,k} m̂_{n,k} a -
aipwScore e m a)(O_i)` of the cross fitted estimator. -/
noncomputable def foldRemainder (fold : ℕ → ℕ → Fin K)
    (eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ)
    (mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ)
    (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool) (O : ℕ → Ω' → 𝒲 × Bool × ℝ) (k : Fin K) (n : ℕ)
    (ω : Ω') : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ cvFold fold n k,
    (aipwScore (eHat n k (trainingData fold O n k ω)) (mHat n k (trainingData fold O n k ω)) a
      (O i ω) - aipwScore e m a (O i ω))

omit [MeasurableSpace 𝒲] in
/-- **The cross fitted estimator is the oracle estimator plus the fold remainders.** -/
theorem crossFitArm_sub_sampleMean (fold : ℕ → ℕ → Fin K)
    (eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ)
    (mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ)
    (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool) (O : ℕ → Ω' → 𝒲 × Bool × ℝ) (n : ℕ) (ω : Ω') :
    crossFitArm fold eHat mHat a O n ω - sampleMean (aipwScore e m a) O n ω =
      ∑ k, foldRemainder fold eHat mHat e m a O k n ω := by
  have hfib : ∑ k, ∑ i ∈ cvFold fold n k, aipwScore e m a (O i ω) =
      ∑ i ∈ range n, aipwScore e m a (O i ω) :=
    sum_fiberwise (range n) (fold n) fun i => aipwScore e m a (O i ω)
  simp only [crossFitArm, foldRemainder, sampleMean, ← mul_sum, ← mul_sub, sum_sub_distrib, hfib]

section Measurability

variable {𝒯 : Type*} [MeasurableSpace 𝒯]

/-- The probability `π̂_a` of the arm `a` under a jointly measurable fitted score is jointly
measurable in the training data and the covariate. -/
theorem measurable_armProb_fitted {eHat : 𝒯 → 𝒲 → ℝ}
    (hE : Measurable fun p : 𝒯 × 𝒲 => eHat p.1 p.2) (a : Bool) :
    Measurable fun p : 𝒯 × 𝒲 => armProb (eHat p.1) a p.2 := by
  cases a
  · exact measurable_const.sub hE
  · exact hE

/-- **Joint measurability of the fitted augmented summand**: for jointly measurable learners
`(t, w) ↦ ê(t, w)` and `(t, w) ↦ m̂(t, a, w)`, the map
`(t, z) ↦ aipwScore ê(t, ·) m̂(t, ·) a z` is measurable. -/
theorem measurable_aipwScore_fitted {eHat : 𝒯 → 𝒲 → ℝ} {mHat : 𝒯 → Bool → 𝒲 → ℝ} {a : Bool}
    (hE : Measurable fun p : 𝒯 × 𝒲 => eHat p.1 p.2)
    (hM : Measurable fun p : 𝒯 × 𝒲 => mHat p.1 a p.2) :
    Measurable fun p : 𝒯 × (𝒲 × Bool × ℝ) => aipwScore (eHat p.1) (mHat p.1) a p.2 := by
  have hq : Measurable fun p : 𝒯 × (𝒲 × Bool × ℝ) => (p.1, p.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hp : Measurable fun p : 𝒯 × (𝒲 × Bool × ℝ) => armProb (eHat p.1) a p.2.1 :=
    (measurable_armProb_fitted hE a).comp hq
  have hm : Measurable fun p : 𝒯 × (𝒲 × Bool × ℝ) => mHat p.1 a p.2.1 := hM.comp hq
  have hI : Measurable fun p : 𝒯 × (𝒲 × Bool × ℝ) => armIndicator a p.2 :=
    (measurable_armIndicator a).comp measurable_snd
  have hy : Measurable fun p : 𝒯 × (𝒲 × Bool × ℝ) => p.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact ((hI.mul hy).div hp).sub (((hI.sub hp).div hp).mul hm)

/-- **The cross fitted estimator is almost everywhere measurable** when the learners are jointly
measurable in the training data and the covariate and the observations are almost everywhere
measurable. -/
theorem aemeasurable_crossFitArm (fold : ℕ → ℕ → Fin K)
    {eHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → 𝒲 → ℝ}
    {mHat : (n : ℕ) → (k : Fin K) → (cvTrain fold n k → 𝒲 × Bool × ℝ) → Bool → 𝒲 → ℝ}
    {a : Bool}
    (hE : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 => eHat n k p.1 p.2)
    (hM : ∀ n k, Measurable fun p : (cvTrain fold n k → 𝒲 × Bool × ℝ) × 𝒲 =>
      mHat n k p.1 a p.2)
    {O : ℕ → Ω' → 𝒲 × Bool × ℝ} {P : Measure Ω'} (hO : ∀ i, AEMeasurable (O i) P) (n : ℕ) :
    AEMeasurable (crossFitArm fold eHat mHat a O n) P := by
  refine aemeasurable_const.mul (Finset.aemeasurable_fun_sum _ fun k _ =>
    Finset.aemeasurable_fun_sum _ fun i _ => ?_)
  exact (measurable_aipwScore_fitted (hE n k) (hM n k)).comp_aemeasurable
    ((aemeasurable_trainingData fold hO n k).prodMk (hO i))

end Measurability

end Efficiency
end CausalInference
