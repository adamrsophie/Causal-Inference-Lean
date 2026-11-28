/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Efficiency.AverageEffectBound
public import CausalInference.PointTreatment.Randomized
public import CausalInference.PointTreatment.RegressionConsistency

/-!
# Regular and non-regular estimators of arm means and the average effect

The oracle augmented inverse probability weighted estimator
`T_n = n⁻¹ ∑_{i < n} φ_a⁰(O_i)`, `φ_a⁰ = aipwScore` with the true propensity score and outcome
regression, is regular along all bounded score submodels with limit `N(0, V_a)`
(`isRegularAlong_aipwEstimator`): it is asymptotically linear with influence function the
efficient influence function, which is a pathwise gradient, and a gradient gives regularity
(`isRegularAlong_of_hasDerivAt`).

Adding to it the centered sample mean of a square integrable function `g` of the observed data
with `Var g(O) > 0` keeps it asymptotically linear, with influence function `φ_a + g - E g`, but
makes it non-regular for every limit law (`not_isRegularAlong_perturbedEstimator`): a regular
estimator has the influence function `φ_a` (`ae_eq_armEIF_of_isRegularAlong`). The oracle
estimator of the average effect is regular as well (`isRegularAlong_aipwEstimatorATE`), and all
of this is instantiated in a randomized trial with a binary covariate.

## Main definitions

* `aipwEstimator e m a`: the oracle estimator as a function of the sample.
* `aipwEstimatorATE e m`: the oracle estimator of the average effect.
* `perturbedEstimator e m a g c`: the oracle estimator plus `n⁻¹ ∑ g(O_i) - c`.
* `trialLaw`, `trialA`, `trialW`, `trialY`, `trialE`, `trialM`: the randomized trial.

## Main results

* `isRegularAlong_aipwEstimator`, `isRegularAlong_aipwEstimatorATE`: the oracle estimators are
  regular.
* `isAsymptoticallyLinear_perturbedEstimator`, `not_isRegularAlong_perturbedEstimator`: an
  asymptotically linear estimator that is not regular.
* In the randomized trial `trialLaw` (a fair binary covariate `W`, `P(A = 1) = 1/4`
  independently, `Y(a) = 2 · 1{a ∧ W} + U` with `U` a fair sign):
  `isRegularAlong_aipwEstimator_trial_true` (limit `N(0, 5)`),
  `isRegularAlong_aipwEstimatorATE_trial` (limit `N(0, 19/3)`),
  `integral_armEIF_sq_trial`, `integral_ateEIF_sq_trial` (the efficient variances `5` and
  `19/3`) and `not_isRegularAlong_perturbedEstimator_trial`.

## References

* J. M. Robins, A. Rotnitzky and L. P. Zhao, Estimation of regression coefficients when some
  regressors are not always observed, *Journal of the American Statistical Association* 89
  (1994), 846-866.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
-/

@[expose] public section

namespace CausalInference
namespace Efficiency

open MeasureTheory ProbabilityTheory Filter Topology MissingData PointTreatment Finset

variable {Ω 𝒲 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒲]
  {A : Ω → Bool} {Y : Bool → Ω → ℝ} {W : Ω → 𝒲} {e : 𝒲 → ℝ} {m : Bool → 𝒲 → ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω'} [IsProbabilityMeasure P]
  {Os : ℕ → Ω' → 𝒲 × Bool × ℝ}

/-- The sample mean of `f` over a sample `x` of size `n`. -/
noncomputable def finMean (f : 𝒲 × Bool × ℝ → ℝ) (n : ℕ) (x : Fin n → 𝒲 × Bool × ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, f (x i)

omit [MeasurableSpace 𝒲] in
theorem finMean_sample (f : 𝒲 × Bool × ℝ → ℝ) (n : ℕ) (ω : Ω') :
    finMean f n (fun i ↦ Os i ω) = sampleMean f Os n ω := by
  rw [finMean, sampleMean, Fin.sum_univ_eq_sum_range (fun i ↦ f (Os i ω)) n]

theorem measurable_finMean {f : 𝒲 × Bool × ℝ → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (finMean f n) :=
  measurable_const.mul (Finset.measurable_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i))

/-- The oracle augmented inverse probability weighted estimator of `E[Y(a)]`. -/
noncomputable def aipwEstimator (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool) :
    ∀ n, (Fin n → 𝒲 × Bool × ℝ) → ℝ :=
  finMean (aipwScore e m a)

/-- **The oracle estimator is regular.** Under mean ignorability, a correct propensity score and
outcome regression, strict overlap and square integrable outcomes, on an i.i.d. sample of the
observed data the oracle estimator is regular along all bounded score submodels with limit
`N(0, V_a)`, `V_a = E[φ_a(O)²]`. -/
theorem isRegularAlong_aipwEstimator (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W)) :
    IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s} (aipwEstimator e m a)
      (gaussianReal 0 (∫ ω, armEIF e m a (armMean μ Y a) (obsData A Y W ω) ^ 2 ∂μ).toNNReal) := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a ↦ (hY2 a).integrable one_le_two
  have hAL := isAsymptoticallyLinear_sampleMean_aipwScore hW hA hY hY2 hps hreg a hmi hε hpos
    (hOs.aemeasurable 0) hlaw
  have hAL' : IsAsymptoticallyLinear (fun n ω ↦ aipwEstimator e m a n (fun i ↦ Os i ω))
      (armRegressionFunctional A Y W a μ) (armEIF e m a (armMean μ Y a)) Os P := by
    rw [armRegressionFunctional, regressionFunctional_arm_eq hW hA hYi hps hreg a hmi hε hpos]
    simpa only [aipwEstimator, finMean_sample] using hAL
  exact isRegularAlong_of_hasDerivAt (measurable_obsData hW hA hY) hOs hlaw
    (measurable_finMean (measurable_aipwScore hps.1 (hreg.1 a))) hAL' (fun _ hs ↦ hs)
    fun s hs ↦ hasDerivAt_regressionFunctional_arm hW hA hY hYi hps hreg a hmi hε hpos hs.1
      hs.2.1.choose_spec hs.2.2

/-- The oracle estimator of the average effect: the difference of the two arm estimators. -/
noncomputable def aipwEstimatorATE (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) :
    ∀ n, (Fin n → 𝒲 × Bool × ℝ) → ℝ :=
  fun n x ↦ aipwEstimator e m true n x - aipwEstimator e m false n x

/-- **The oracle estimator of the average effect is regular**, with limit `N(0, E[φ(O)²])`,
`φ = ateEIF`, under mean ignorability of both arms, a correct score and regression, strict
overlap and square integrable outcomes. -/
theorem isRegularAlong_aipwEstimatorATE (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (hmi : ∀ a, MeanIgnorable μ A W Y a)
    {ε : ℝ} (hov : StrictOverlapAE e (μ.map W) ε) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W)) :
    IsRegularAlong μ (obsData A Y W) (ateRegressionFunctional A Y W)
      {s | IsBoundedScore μ (obsData A Y W) s} (aipwEstimatorATE e m)
      (gaussianReal 0 (∫ ω, ateEIF e m (ate μ Y) (obsData A Y W ω) ^ 2 ∂μ).toNNReal) := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a ↦ (hY2 a).integrable one_le_two
  have hAL := isAsymptoticallyLinear_sampleMean_aipwScore_ate hW hA hY hY2 hps hreg hmi hov
    (hOs.aemeasurable 0) hlaw
  have hAL' : IsAsymptoticallyLinear (fun n ω ↦ aipwEstimatorATE e m n (fun i ↦ Os i ω))
      (ateRegressionFunctional A Y W μ) (ateEIF e m (ate μ Y)) Os P := by
    rw [ateRegressionFunctional_eq hW hA hYi hps hreg hmi hov]
    simpa only [aipwEstimatorATE, aipwEstimator, finMean_sample] using hAL
  exact isRegularAlong_of_hasDerivAt (measurable_obsData hW hA hY) hOs hlaw
    (fun n ↦ (measurable_finMean (measurable_aipwScore hps.1 (hreg.1 true)) n).sub
      (measurable_finMean (measurable_aipwScore hps.1 (hreg.1 false)) n)) hAL' (fun _ hs ↦ hs)
    fun s hs ↦ hasDerivAt_regressionFunctional_ate hW hA hY hYi hps hreg hmi hov hs

/-- **An asymptotically linear estimator with another influence function is not regular.** Under
the hypotheses of `ae_eq_armEIF_of_isRegularAlong`, if the influence function `φ` differs from
`φ_a` on a set of positive probability, the estimator is not regular for any limit law. -/
theorem not_isRegularAlong_of_not_ae_eq (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hYi : ∀ a, Integrable (Y a) μ)
    (hps : IsPropensityScore μ A W e) (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m)
    (a : Bool) (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W)) {T : ∀ n, (Fin n → 𝒲 × Bool × ℝ) → ℝ}
    {φ : 𝒲 × Bool × ℝ → ℝ}
    (hAL : IsAsymptoticallyLinear (fun n ω ↦ T n (fun i ↦ Os i ω)) (armMean μ Y a) φ Os P)
    (hne : ¬ (fun ω ↦ φ (obsData A Y W ω)) =ᵐ[μ]
      fun ω ↦ armEIF e m a (armMean μ Y a) (obsData A Y W ω)) (L : Measure ℝ) :
    ¬ IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s} T L := fun hR ↦
  hne (ae_eq_armEIF_of_isRegularAlong hW hA hY hYi hps hreg a hmi hε hpos hOs hlaw hAL hR)

/-- The oracle estimator plus the centered sample mean `n⁻¹ ∑ g(O_i) - c`. -/
noncomputable def perturbedEstimator (e : 𝒲 → ℝ) (m : Bool → 𝒲 → ℝ) (a : Bool)
    (g : 𝒲 × Bool × ℝ → ℝ) (c : ℝ) : ∀ n, (Fin n → 𝒲 × Bool × ℝ) → ℝ :=
  fun n x ↦ aipwEstimator e m a n x + (finMean g n x - c)

/-- **The perturbed estimator is asymptotically linear** at `E[Y(a)]` with influence function
`φ_a + g - E g(O)`, for a measurable `g` with `g(O)` square integrable and `c = E g(O)`. -/
theorem isAsymptoticallyLinear_perturbedEstimator (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W)) {g : 𝒲 × Bool × ℝ → ℝ} (hg : Measurable g)
    (hg2 : MemLp (fun ω ↦ g (Os 0 ω)) 2 P) :
    IsAsymptoticallyLinear
      (fun n ω ↦ perturbedEstimator e m a g (∫ ω, g (obsData A Y W ω) ∂μ) n (fun i ↦ Os i ω))
      (armMean μ Y a) (fun z ↦ armEIF e m a (armMean μ Y a) z +
        (g z - ∫ ω, g (obsData A Y W ω) ∂μ)) Os P := by
  have hAL := isAsymptoticallyLinear_sampleMean_aipwScore hW hA hY hY2 hps hreg a hmi hε hpos
    (hOs.aemeasurable 0) hlaw
  have hc := integral_comp_sample_eq (measurable_obsData hW hA hY) hOs hlaw hg
  have hgAL := sampleMean_isAsymptoticallyLinear (O := Os) hg hg2
  rw [hc] at hgAL
  have hsum := hAL.add (hgAL.sub (IsAsymptoticallyLinear.of_expansion (θhat := fun _ _ ↦
    ∫ ω, g (obsData A Y W ω) ∂μ) (θ := ∫ ω, g (obsData A Y W ω) ∂μ) (φ := fun _ ↦ 0)
    measurable_const (memLp_const 0) (by simp) (r := fun _ _ ↦ 0)
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ by simp [sampleMean])
    (by
      simp only [mul_zero]
      exact tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
        (ae_of_all _ fun _ ↦ tendsto_const_nhds))))
  simp only [sub_self, add_zero, sub_zero] at hsum
  simpa only [perturbedEstimator, aipwEstimator, finMean_sample] using hsum

/-- **The perturbed estimator is not regular.** If moreover `g(O)` is not almost surely
constant, `Var g(O) > 0`, the perturbed estimator is asymptotically linear but not
regular for any limit law. -/
theorem not_isRegularAlong_perturbedEstimator (hW : Measurable W) (hA : Measurable A)
    (hY : ∀ a, Measurable (Y a)) (hY2 : ∀ a, MemLp (Y a) 2 μ) (hps : IsPropensityScore μ A W e)
    (hreg : IsOutcomeRegression μ A W (obsOutcome A Y) m) (a : Bool)
    (hmi : MeanIgnorable μ A W Y a) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ᵐ ω ∂μ, ε ≤ armProb e a (W ω)) (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = μ.map (obsData A Y W)) {g : 𝒲 × Bool × ℝ → ℝ} (hg : Measurable g)
    (hg2 : MemLp (fun ω ↦ g (Os 0 ω)) 2 P)
    (hvar : 0 < ∫ ω, (g (obsData A Y W ω) - ∫ ω, g (obsData A Y W ω) ∂μ) ^ 2 ∂μ)
    (L : Measure ℝ) :
    ¬ IsRegularAlong μ (obsData A Y W) (armRegressionFunctional A Y W a)
      {s | IsBoundedScore μ (obsData A Y W) s}
      (perturbedEstimator e m a g (∫ ω, g (obsData A Y W ω) ∂μ)) L := by
  have hYi : ∀ a, Integrable (Y a) μ := fun a ↦ (hY2 a).integrable one_le_two
  refine not_isRegularAlong_of_not_ae_eq hW hA hY hYi hps hreg a hmi hε hpos hOs hlaw
    (isAsymptoticallyLinear_perturbedEstimator hW hA hY hY2 hps hreg a hmi hε hpos hOs hlaw hg
      hg2) (fun hae ↦ ?_) L
  have h0 : (fun ω ↦ (g (obsData A Y W ω) - ∫ ω, g (obsData A Y W ω) ∂μ) ^ 2) =ᵐ[μ] 0 := by
    filter_upwards [hae] with ω hω
    have : g (obsData A Y W ω) - ∫ ω, g (obsData A Y W ω) ∂μ = 0 := by linarith
    simp [this]
  rw [integral_congr_ae h0] at hvar
  simp at hvar

/-! ### A randomized trial with a binary covariate -/

section Trial

open scoped ENNReal

/-- A fair coin on `Bool`. -/
noncomputable def trialCoin : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance isProbabilityMeasure_trialCoin : IsProbabilityMeasure trialCoin := ⟨by
  simp only [trialCoin, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply,
    measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]⟩

theorem integral_trialCoin (f : Bool → ℝ) : ∫ b, f b ∂trialCoin = (f true + f false) / 2 := by
  rw [trialCoin, integral_smul_measure, integral_add_measure Integrable.of_finite
    Integrable.of_finite, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem integral_trialCoin_prod (f : Bool × Bool → ℝ) :
    ∫ x, f x ∂(trialCoin.prod trialCoin) =
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  rw [integral_prod _ Integrable.of_finite]
  simp only [integral_trialCoin]
  ring

/-- **Coordinates of a product of probability laws are independent.** -/
theorem indepFun_fst_snd_of_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ : Measure α) (μ₂ : Measure β) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] :
    IndepFun Prod.fst Prod.snd (μ₁.prod μ₂) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    measurable_snd.aemeasurable]
  simp

/-- The sample space of the trial: two coins `(c₁, c₂)` that set the treatment
`A = c₁ ∧ c₂`, the covariate `W` and the sign `U` of the noise. -/
abbrev TrialSpace := (Bool × Bool) × (Bool × Bool)

/-- The law of the trial: four independent fair coins. -/
noncomputable def trialLaw : Measure TrialSpace :=
  (trialCoin.prod trialCoin).prod (trialCoin.prod trialCoin)

instance isProbabilityMeasure_trialLaw : IsProbabilityMeasure trialLaw := by
  unfold trialLaw; infer_instance

theorem integral_trialLaw (f : TrialSpace → ℝ) :
    ∫ ω, f ω ∂trialLaw =
      ((f ((true, true), (true, true)) + f ((true, true), (true, false)) +
        f ((true, true), (false, true)) + f ((true, true), (false, false))) +
      (f ((true, false), (true, true)) + f ((true, false), (true, false)) +
        f ((true, false), (false, true)) + f ((true, false), (false, false))) +
      (f ((false, true), (true, true)) + f ((false, true), (true, false)) +
        f ((false, true), (false, true)) + f ((false, true), (false, false))) +
      (f ((false, false), (true, true)) + f ((false, false), (true, false)) +
        f ((false, false), (false, true)) + f ((false, false), (false, false)))) / 16 := by
  rw [trialLaw, integral_prod _ Integrable.of_finite, integral_trialCoin_prod]
  simp only [integral_trialCoin_prod]
  ring

/-- The treatment: `P(A = 1) = 1/4`, independent of everything else. -/
def trialA (ω : TrialSpace) : Bool := ω.1.1 && ω.1.2

/-- The covariate: a fair coin. -/
def trialW (ω : TrialSpace) : Bool := ω.2.1

/-- The sign of the noise: a fair sign. -/
def trialSign (ω : TrialSpace) : ℝ := if ω.2.2 then 1 else -1

/-- The outcome regression `m(a, w) = 2 · 1{a ∧ w}`. -/
def trialM (a w : Bool) : ℝ := if a && w then 2 else 0

/-- The potential outcomes `Y(a) = 2 · 1{a ∧ W} + U`. -/
def trialY (a : Bool) (ω : TrialSpace) : ℝ := trialM a (trialW ω) + trialSign ω

/-- The propensity score `1/4`. -/
noncomputable def trialE : Bool → ℝ := fun _ ↦ 1 / 4

theorem measurable_trialA : Measurable trialA := Measurable.of_discrete
theorem measurable_trialW : Measurable trialW := Measurable.of_discrete
theorem measurable_trialY (a : Bool) : Measurable (trialY a) := Measurable.of_discrete

theorem memLp_trialY (a : Bool) : MemLp (trialY a) 2 trialLaw :=
  MemLp.of_bound (measurable_trialY a).aestronglyMeasurable 3
    (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, trialY, trialM, trialSign]
      split_ifs <;> norm_num)

theorem indepFun_trialA : IndepFun trialA
    (fun ω ↦ (trialW ω, potentialPair trialY ω)) trialLaw :=
  (indepFun_fst_snd_of_prod (trialCoin.prod trialCoin) (trialCoin.prod trialCoin)).comp
    (φ := fun c : Bool × Bool ↦ c.1 && c.2)
    (ψ := fun v : Bool × Bool ↦ (v.1, (trialM false v.1 + (if v.2 then 1 else -1),
      trialM true v.1 + (if v.2 then 1 else -1)))) Measurable.of_discrete Measurable.of_discrete

theorem indepFun_trialSign_trialW :
    IndepFun (fun ω : TrialSpace ↦ ω.2.2) trialW trialLaw := by
  have h := (indepFun_fst_snd_of_prod trialCoin trialCoin).symm
  rw [indepFun_iff_map_prod_eq_prod_map_map measurable_snd.aemeasurable
    measurable_fst.aemeasurable] at h
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) measurable_trialW.aemeasurable,
    show trialW = fun ω : TrialSpace ↦ Prod.fst ω.2 from rfl]
  have hs : trialLaw.map Prod.snd = trialCoin.prod trialCoin := by simp [trialLaw]
  have e : ∀ (γ : Type) [MeasurableSpace γ] (g : Bool × Bool → γ), Measurable g →
      trialLaw.map (fun ω ↦ g ω.2) = (trialCoin.prod trialCoin).map g := fun γ _ g hg ↦ by
    rw [show (fun ω : TrialSpace ↦ g ω.2) = g ∘ Prod.snd from rfl,
      ← Measure.map_map hg measurable_snd, hs]
  rw [e _ (fun v ↦ (v.2, v.1)) (by fun_prop), e _ Prod.snd measurable_snd,
    e _ Prod.fst measurable_fst]
  exact h

theorem trialLaw_real_trialA : trialLaw.real (trialA ⁻¹' {true}) = 1 / 4 := by
  rw [← integral_respInd measurable_trialA, integral_trialLaw]
  norm_num [respInd_apply, trialA]

theorem isPropensityScore_trial : IsPropensityScore trialLaw trialA trialW trialE := by
  have h := isPropensityScore_const_of_indepFun measurable_trialW measurable_trialA
    (indepFun_trialA.comp measurable_id measurable_fst)
  rwa [trialLaw_real_trialA] at h

theorem meanIgnorable_trial (a : Bool) : MeanIgnorable trialLaw trialA trialW trialY a :=
  (indicatorIgnorable_of_indepFun measurable_trialW measurable_trialA measurable_trialY
    indepFun_trialA).meanIgnorable measurable_trialW measurable_trialA measurable_trialY a
    ((memLp_trialY a).integrable one_le_two)

theorem condExp_trialY (a : Bool) :
    trialLaw[trialY a | MeasurableSpace.comap trialW inferInstance] =ᵐ[trialLaw]
      fun ω ↦ trialM a (trialW ω) := by
  have hm : StronglyMeasurable[MeasurableSpace.comap trialW inferInstance]
      (fun ω ↦ trialM a (trialW ω)) :=
    ((Measurable.of_discrete (f := trialM a)).comp (comap_measurable trialW)).stronglyMeasurable
  have hsU : StronglyMeasurable[MeasurableSpace.comap (fun ω : TrialSpace ↦ ω.2.2) inferInstance]
      trialSign :=
    ((Measurable.of_discrete (f := fun b : Bool ↦ if b then (1 : ℝ) else -1)).comp
      (comap_measurable (fun ω : TrialSpace ↦ ω.2.2))).stronglyMeasurable
  have hU0 : ∫ ω, trialSign ω ∂trialLaw = 0 := by
    rw [integral_trialLaw]; norm_num [trialSign]
  have hY : trialY a = (fun ω ↦ trialM a (trialW ω)) + trialSign := rfl
  rw [hY]
  filter_upwards [condExp_add (Integrable.of_finite) (Integrable.of_finite (f := trialSign))
      (MeasurableSpace.comap trialW inferInstance),
    condExp_indep_eq (Measurable.of_discrete (f := fun ω : TrialSpace ↦ ω.2.2)).comap_le
      measurable_trialW.comap_le hsU indepFun_trialSign_trialW] with ω h1 h2
  rw [h1, Pi.add_apply, condExp_of_stronglyMeasurable measurable_trialW.comap_le hm
    Integrable.of_finite, h2, hU0, add_zero]

theorem isOutcomeRegression_trial :
    IsOutcomeRegression trialLaw trialA trialW (obsOutcome trialA trialY) trialM :=
  isOutcomeRegression_of_condExp measurable_trialA
    (fun a ↦ (memLp_trialY a).integrable one_le_two) meanIgnorable_trial
    (fun _ ↦ Measurable.of_discrete) condExp_trialY

theorem le_armProb_trial (a : Bool) :
    ∀ᵐ ω ∂trialLaw, 1 / 4 ≤ armProb trialE a (trialW ω) :=
  Eventually.of_forall fun _ ↦ by cases a <;> norm_num [armProb, trialE]

/-- **The oracle estimator is regular in the trial.** In the randomized trial with
`P(A = 1) = 1/4`, a fair binary covariate `W` and outcomes `Y(a) = 2 · 1{a ∧ W} + U`, `U` a fair
sign, on every i.i.d. sample of the observed data the oracle estimator of `E[Y(a)]` is regular
along all bounded score submodels with limit `N(0, V_a)`. -/
theorem isRegularAlong_aipwEstimator_trial (a : Bool) {Os : ℕ → Ω' → Bool × Bool × ℝ}
    (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = trialLaw.map (obsData trialA trialY trialW)) :
    IsRegularAlong trialLaw (obsData trialA trialY trialW)
      (armRegressionFunctional trialA trialY trialW a)
      {s | IsBoundedScore trialLaw (obsData trialA trialY trialW) s} (aipwEstimator trialE trialM a)
      (gaussianReal 0 (∫ ω, armEIF trialE trialM a (armMean trialLaw trialY a)
        (obsData trialA trialY trialW ω) ^ 2 ∂trialLaw).toNNReal) :=
  isRegularAlong_aipwEstimator measurable_trialW measurable_trialA measurable_trialY memLp_trialY
    isPropensityScore_trial isOutcomeRegression_trial a (meanIgnorable_trial a)
    (by norm_num : (0 : ℝ) < 1 / 4) (le_armProb_trial a) hOs hlaw

theorem armMean_trial_true : armMean trialLaw trialY true = 1 := by
  rw [armMean, integral_trialLaw]
  norm_num [trialY, trialM, trialW, trialSign]

theorem ate_trial : ate trialLaw trialY = 1 := by
  rw [ate, integral_trialLaw]
  norm_num [indivEffect, trialY, trialM, trialW, trialSign]

/-- **The efficient variance of `E[Y(1)]` in the trial is `5`.** -/
theorem integral_armEIF_sq_trial :
    ∫ ω, armEIF trialE trialM true (armMean trialLaw trialY true)
      (obsData trialA trialY trialW ω) ^ 2 ∂trialLaw = 5 := by
  rw [armMean_trial_true, integral_trialLaw]
  norm_num [armEIF, aipwScore, armIndicator, armProb, trialE, trialM, obsData, obsOutcome,
    trialA, trialY, trialW, trialSign]

/-- **The efficient variance of the average effect in the trial is `19/3`.** -/
theorem integral_ateEIF_sq_trial :
    ∫ ω, ateEIF trialE trialM (ate trialLaw trialY) (obsData trialA trialY trialW ω) ^ 2
      ∂trialLaw = 19 / 3 := by
  rw [ate_trial, integral_trialLaw]
  norm_num [ateEIF, aipwScore, armIndicator, armProb, trialE, trialM, obsData, obsOutcome,
    trialA, trialY, trialW, trialSign]

/-- **The oracle estimator of `E[Y(1)]` in the trial is regular with limit `N(0, 5)`.** -/
theorem isRegularAlong_aipwEstimator_trial_true {Os : ℕ → Ω' → Bool × Bool × ℝ}
    (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = trialLaw.map (obsData trialA trialY trialW)) :
    IsRegularAlong trialLaw (obsData trialA trialY trialW)
      (armRegressionFunctional trialA trialY trialW true)
      {s | IsBoundedScore trialLaw (obsData trialA trialY trialW) s}
      (aipwEstimator trialE trialM true) (gaussianReal 0 5) := by
  have h := isRegularAlong_aipwEstimator_trial true hOs hlaw
  rwa [integral_armEIF_sq_trial, show (5 : ℝ).toNNReal = 5 by norm_num] at h

/-- **The oracle estimator of the average effect in the trial is regular with limit
`N(0, 19/3)`.** -/
theorem isRegularAlong_aipwEstimatorATE_trial {Os : ℕ → Ω' → Bool × Bool × ℝ}
    (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = trialLaw.map (obsData trialA trialY trialW)) :
    IsRegularAlong trialLaw (obsData trialA trialY trialW)
      (ateRegressionFunctional trialA trialY trialW)
      {s | IsBoundedScore trialLaw (obsData trialA trialY trialW) s}
      (aipwEstimatorATE trialE trialM) (gaussianReal 0 (19 / 3 : ℝ).toNNReal) := by
  have hov : StrictOverlapAE trialE (trialLaw.map trialW) (1 / 4) :=
    ⟨by norm_num, Eventually.of_forall fun _ ↦ by norm_num [trialE]⟩
  have h := isRegularAlong_aipwEstimatorATE measurable_trialW measurable_trialA measurable_trialY
    memLp_trialY isPropensityScore_trial isOutcomeRegression_trial meanIgnorable_trial hov hOs hlaw
  rwa [integral_ateEIF_sq_trial] at h

/-- The sign of the covariate, `2 · 1{W} - 1`, as a function of the observed data. -/
def covariateSign (z : Bool × Bool × ℝ) : ℝ := if z.1 then 1 else -1

theorem measurable_covariateSign : Measurable covariateSign :=
  (Measurable.of_discrete (f := fun b : Bool ↦ if b then (1 : ℝ) else -1)).comp measurable_fst

/-- **A non-regular asymptotically linear estimator in the trial.** The oracle estimator plus
the sample mean of the covariate sign `2 · 1{W} - 1` (of mean zero) is asymptotically linear at
`E[Y(a)]` with influence function `φ_a + (2 · 1{W} - 1)`, but it is not regular for any limit
law. -/
theorem not_isRegularAlong_perturbedEstimator_trial (a : Bool)
    {Os : ℕ → Ω' → Bool × Bool × ℝ} (hOs : IsIIDSample Os P)
    (hlaw : P.map (Os 0) = trialLaw.map (obsData trialA trialY trialW)) (L : Measure ℝ) :
    IsAsymptoticallyLinear (fun n ω ↦ perturbedEstimator trialE trialM a covariateSign
        (∫ ω, covariateSign (obsData trialA trialY trialW ω) ∂trialLaw) n (fun i ↦ Os i ω))
      (armMean trialLaw trialY a) (fun z ↦ armEIF trialE trialM a (armMean trialLaw trialY a) z +
        (covariateSign z - ∫ ω, covariateSign (obsData trialA trialY trialW ω) ∂trialLaw))
      Os P ∧
    ¬ IsRegularAlong trialLaw (obsData trialA trialY trialW)
      (armRegressionFunctional trialA trialY trialW a)
      {s | IsBoundedScore trialLaw (obsData trialA trialY trialW) s}
      (perturbedEstimator trialE trialM a covariateSign
        (∫ ω, covariateSign (obsData trialA trialY trialW ω) ∂trialLaw)) L := by
  have hg2 : MemLp (fun ω ↦ covariateSign (Os 0 ω)) 2 P :=
    MemLp.of_bound (measurable_covariateSign.comp_aemeasurable
      (hOs.aemeasurable 0)).aestronglyMeasurable 1 (Eventually.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, covariateSign]; split_ifs <;> norm_num)
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  refine ⟨isAsymptoticallyLinear_perturbedEstimator measurable_trialW measurable_trialA
    measurable_trialY memLp_trialY isPropensityScore_trial isOutcomeRegression_trial a
    (meanIgnorable_trial a) hε (le_armProb_trial a) hOs hlaw measurable_covariateSign hg2,
    not_isRegularAlong_perturbedEstimator measurable_trialW measurable_trialA measurable_trialY
    memLp_trialY isPropensityScore_trial isOutcomeRegression_trial a (meanIgnorable_trial a) hε
    (le_armProb_trial a) hOs hlaw measurable_covariateSign hg2 ?_ L⟩
  have h0 : ∫ ω, covariateSign (obsData trialA trialY trialW ω) ∂trialLaw = 0 := by
    rw [integral_trialLaw]; norm_num [covariateSign, obsData, trialW]
  rw [h0, integral_trialLaw]
  norm_num [covariateSign, obsData, trialW]

end Trial

end Efficiency
end CausalInference
