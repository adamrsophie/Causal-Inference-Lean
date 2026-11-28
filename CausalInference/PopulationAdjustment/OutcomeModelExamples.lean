/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.OutcomeModelPlugInBias
public import CausalInference.IndirectComparison.Constancy

/-!
# Concrete outcome models: the plug-in at the mean covariates

All models have one covariate taking the values `±1` with probability `1/2` (`signLaw`), so the
mean covariate is `x̄ = 0`.

* **The logit model** (`outcomeModel_logit_plugIn_bias`): `η_false(x) = x`, `η_true(x) = x + 3/2`
  and risks `σ(η_t)`. The plug-in at the mean covariates is `3/2`; the marginal log odds ratio is
  `log ((r + r⁵ + 2r⁶) / (2 + r + r⁵))` with `r = e^{1/2}`, a number in `(1.22704, 1.22705)`; so
  the bias of the plug-in lies in `(0.27295, 0.27296)`. The averaging gap of the reference arm is
  exactly `0` although the covariate is prognostic for it (the risks `σ(±1)` average to
  `1/2 = σ(0)`), and the averaging gap of the active arm is negative: the curvature of `σ`
  changes sign at `0`, so the sign condition of `arm_gap_ne_zero` cannot be dropped.
* **The identity link** (`outcomeModel_id_plugIn_example`): the linear model
  `η_t(x) = x + 1{t}(1 + 2x)` has plug-in, marginal and average conditional effect `1`, and
  bias `0`; so do the arms `0` and `1` of `sharedExampleModel` and the population whose
  conditional means are this model.
* **The log link** (`outcomeModel_log_arm_gap`): for `m(x) = exp(x)` the response scale gap is
  `(e + e⁻¹)/2 - 1 ≠ 0`, with its Lagrange form, and the link scale gap is nonzero; on the log
  scale the curvature of `log` gives a negative Jensen gap (`outcomeModel_log_concave_gap`).
* **The plug-in limit and the continuity of the estimands** (`outcomeModel_plugIn_limit_example`,
  `outcomeModel_continuity_example`).

## Main results

* `outcomeModel_logit_plugIn_bias`, `outcomeModel_id_plugIn_example`,
  `outcomeModel_log_arm_gap`, `outcomeModel_log_concave_gap`, `outcomeModel_taylor_exp`,
  `outcomeModel_plugIn_limit_example`, `outcomeModel_continuity_example`,
  `outcomeModel_integral_continuity_example`, `outcomeModel_linear_example`,
  `outcomeModel_curvature_example`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory Filter Topology EffectMeasure IndirectComparison

/-! ### The covariate law `signLaw` -/

/-- Every measurable function is integrable under `signLaw`. -/
theorem integrable_signLaw {φ : (Fin 1 → ℝ) → ℝ} (hφ : Measurable φ) : Integrable φ signLaw :=
  (integrable_map_measure hφ.aestronglyMeasurable
    (measurable_of_finite signCov).aemeasurable).2 Integrable.of_finite

/-- The coordinates are integrable under `signLaw`. -/
theorem integrable_coord_signLaw (k : Fin 1) : Integrable (fun x : Fin 1 → ℝ => x k) signLaw :=
  integrable_signLaw (measurable_pi_apply k)

/-- The mean covariate of `signLaw` is `0`. -/
theorem covMean_signLaw : covMean signLaw = 0 := by
  funext k
  rw [covMean, integral_signLaw (measurable_pi_apply k)]
  simp [signCov]

/-- A measurable function with different values at `±1` is not `signLaw`-almost surely
constant. -/
theorem isPrognostic_signLaw {φ : (Fin 1 → ℝ) → ℝ} (hφ : Measurable φ)
    (h : φ (signCov true) ≠ φ (signCov false)) : IsPrognostic signLaw φ := by
  rintro ⟨c, hc⟩
  rw [signLaw, ae_map_iff (measurable_of_finite signCov).aemeasurable
    (measurableSet_eq_fun hφ measurable_const), ae_halfLaw_iff] at hc
  exact h ((hc true).trans (hc false).symm)

/-! ### The logit model -/

/-- The logit outcome model with predictors `η_false(x) = x` and `η_true(x) = x + 3/2`. -/
noncomputable def logitOutcomeModel (t : Bool) (x : Fin 1 → ℝ) : ℝ :=
  Real.sigmoid (interactionPredictor 0 (3 / 2) (fun _ => 1) 0 t x)

/-- The two arms of `logitOutcomeModel` are the risks `logitRefRisk` and `logitActRisk`. -/
theorem logitOutcomeModel_eq :
    logitOutcomeModel false = logitRefRisk ∧ logitOutcomeModel true = logitActRisk := by
  refine ⟨funext fun x => ?_, funext fun x => ?_⟩ <;>
    simp [logitOutcomeModel, logitRefRisk, logitActRisk, interactionPredictor, anchoredPredictor]

/-- Both arms of `logitOutcomeModel` are measurable. -/
theorem measurable_logitOutcomeModel (t : Bool) : Measurable (logitOutcomeModel t) := by
  unfold logitOutcomeModel interactionPredictor; fun_prop

/-- **The plug-in at the mean covariates is biased on the logit scale.** In the logit model the
plug-in is `3/2`, the marginal log odds ratio lies in `(1.22704, 1.22705)`, and the bias of the
plug-in, `J_logit(m_false) - J_logit(m_true)`, lies in `(0.27295, 0.27296)`. The averaging gap
of the reference arm is `0` although the covariate is prognostic for that arm, and the averaging
gap of the active arm is negative. -/
theorem outcomeModel_logit_plugIn_bias :
    plugInEffect logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) = 3 / 2 ∧
      1.22704 < linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) ∧
      linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) < 1.22705 ∧
      plugInEffect logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) -
          linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) =
        averagingGap logit signLaw (logitOutcomeModel false) -
          averagingGap logit signLaw (logitOutcomeModel true) ∧
      0.27295 < plugInEffect logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) -
          linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) ∧
      plugInEffect logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) -
          linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) <
        0.27296 ∧
      IsPrognostic signLaw (interactionPredictor 0 (3 / 2) (fun _ => 1) 0 false) ∧
      averagingGap logit signLaw (logitOutcomeModel false) = 0 ∧
      averagingGap logit signLaw (logitOutcomeModel true) < 0 := by
  have hm : ∀ t x, logit (logitOutcomeModel t x) =
      interactionPredictor 0 (3 / 2) (fun _ => 1) 0 t x := fun t x => logit_sigmoid _
  have hplug : plugInEffect logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) =
      3 / 2 := by
    rw [plugInEffect_interactionPredictor hm, dotProduct_zero, add_zero]
  have hbias := (plugInEffect_sub_linkMarginal integrable_coord_signLaw hm
    fun t => integrable_signLaw (measurable_logitOutcomeModel t)).2
  have heq : linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) =
      linkMarginal logit halfLaw logisticRef logisticAct := by
    rw [logitOutcomeModel_eq.1, logitOutcomeModel_eq.2]
    simp only [linkMarginal, integral_signLaw measurable_logitRefRisk,
      integral_signLaw measurable_logitActRisk, integral_halfLaw, (logitRisk_signCov _).1,
      (logitRisk_signCov _).2]
  have hval := logisticExample_value
  rw [← heq] at hval
  have hgap0 : averagingGap logit signLaw (logitOutcomeModel false) = 0 := by
    have h1 : ∫ x, logitOutcomeModel false x ∂signLaw = 1 / 2 := by
      rw [logitOutcomeModel_eq.1]; exact logit_marginal_not_transported.2.1
    have h2 : ∫ x, logit (logitOutcomeModel false x) ∂signLaw = 0 := by
      simp only [hm]
      rw [integral_interactionPredictor integrable_coord_signLaw, covMean_signLaw]
      simp [interactionPredictor]
    rw [averagingGap, h1, h2, logit_eq_log_div]
    norm_num
  have hnd : IsPrognostic signLaw (interactionPredictor 0 (3 / 2) (fun _ => 1) 0 false) :=
    isPrognostic_signLaw (by unfold interactionPredictor; fun_prop)
      (by norm_num [interactionPredictor, signCov])
  refine ⟨hplug, hval.1, hval.2, hbias, ?_, ?_, hnd, hgap0, ?_⟩
  · rw [hplug]; linarith [hval.2]
  · rw [hplug]; linarith [hval.1]
  · have : 0.27295 < averagingGap logit signLaw (logitOutcomeModel false) -
        averagingGap logit signLaw (logitOutcomeModel true) := by
      rw [← hbias, hplug]; linarith [hval.2]
    linarith

/-! ### The identity link -/

/-- **No bias on the identity link.** For `η_t(x) = x + 1{t}(1 + 2x)` under `signLaw` the plug-in,
the marginal and the average conditional effect are all `1`, and the bias is `0`. The arms `0`
and `1` of `sharedExampleModel` have marginal effect `1` on the identity scale, the plug-in at
the mean covariates; and the population with covariate law `signLaw` whose conditional means are
`η_t` has marginal effect `1`. -/
theorem outcomeModel_id_plugIn_example :
    plugInEffect id signLaw (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) false)
        (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) true) = 1 ∧
      linkMarginal id signLaw (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) false)
        (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) true) = 1 ∧
      linkConditional id signLaw (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) false)
        (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) true) = 1 ∧
      plugInEffect id signLaw (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) false)
          (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) true) -
        linkMarginal id signLaw (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) false)
          (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) true) = 0 ∧
      linkMarginal id signLaw (sharedExampleModel.predictor 0)
        (sharedExampleModel.predictor 1) = 1 ∧
      (⟨signLaw, id, fun t => interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) t⟩ :
        Population (Fin 1 → ℝ) (Fin 1 → ℝ) Bool).marginalEffect id false true = 1 := by
  have hm : ∀ t (x : Fin 1 → ℝ), id (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) t x) =
      interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) t x := fun _ _ => rfl
  have hplug : plugInEffect id signLaw (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) false)
      (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) true) = 1 := by
    rw [plugInEffect_interactionPredictor hm, covMean_signLaw, zero_dotProduct, add_zero]
  obtain ⟨-, h2, h3⟩ := linkMarginal_id_interactionPredictor integrable_coord_signLaw 0 1
    (fun _ => 1) (fun _ => 2)
  have hA := (AnchoredModel.linkMarginal_id_predictor integrable_coord_signLaw
    sharedExampleModel 0 1).1
  set R : Population (Fin 1 → ℝ) (Fin 1 → ℝ) Bool :=
    ⟨signLaw, id, fun t => interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) t⟩
  have hR : IsProbabilityMeasure R.μ := by simp only [R]; infer_instance
  have hmeas : ∀ t, Measurable (interactionPredictor (p := 1) 0 1 (fun _ => 1) (fun _ => 2) t) :=
    fun t => by unfold interactionPredictor; fun_prop
  have hcm : ∀ t, R.IsCondMean t (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) t) :=
    fun t => Population.isCondMean_of_eq_comp measurable_id (hmeas t) rfl
      (integrable_signLaw (hmeas t))
  have hpop := (marginalEffect_id_eq_plugInEffect (Q := R) measurable_id
    (fun k => integrable_coord_signLaw k) (fun t => integrable_signLaw (hmeas t)) hcm).1
  have hcov : R.covLaw = signLaw := by simp only [R, Population.covLaw, Measure.map_id]
  refine ⟨hplug, h2.trans hplug, h3.symm.trans (h2.trans hplug),
    plugInEffect_sub_linkMarginal_id integrable_coord_signLaw 0 1 (fun _ => 1) (fun _ => 2), ?_,
    by rw [hpop, hcov, hplug]⟩
  rw [hA, covMean_signLaw, zero_dotProduct]
  simp [sharedExampleModel]

/-! ### The log link -/

/-- The second derivative of `exp` is `exp`. -/
theorem iteratedDeriv_two_exp (s : ℝ) : iteratedDeriv 2 Real.exp s = Real.exp s := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]

/-- The second derivative of `log` is `s ↦ -1/s²`. -/
theorem iteratedDeriv_two_log (s : ℝ) : iteratedDeriv 2 Real.log s = -(s ^ 2)⁻¹ := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_log', deriv_inv']

/-- **The Taylor form for `exp`**: there is `ξ ∈ [0, 1]` with `e = 1 + 1 + ½ e^ξ`. -/
theorem outcomeModel_taylor_exp :
    ∃ ξ ∈ Set.uIcc (1 : ℝ) 0, Real.exp 1 = 1 + 1 + 1 / 2 * Real.exp ξ := by
  obtain ⟨ξ, hξ, h⟩ := exists_eq_taylor_two_lagrange isOpen_univ Set.ordConnected_univ
    Real.contDiff_exp.contDiffOn (Set.mem_univ (1 : ℝ)) (Set.mem_univ 0)
  refine ⟨ξ, hξ, ?_⟩
  rw [h, Real.deriv_exp, iteratedDeriv_two_exp, Real.exp_zero]
  ring

/-- **A nonzero arm gap on the log link.** For the arm mean `m(x) = exp(x)` (link `log`, predictor
`η(x) = x`) under `signLaw`: the response scale gap is `(e + e⁻¹)/2 - 1`, nonzero, with its
Lagrange form; the link scale gap `log(∫ m) - η(x̄)` is the averaging gap and is nonzero. -/
theorem outcomeModel_log_arm_gap :
    ∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw -
        Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false (covMean signLaw)) =
      (Real.exp 1 + Real.exp (-1)) / 2 - 1 ∧
      ∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw -
        Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false (covMean signLaw)) ≠ 0 ∧
      Real.log (∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw) -
          interactionPredictor 0 0 (fun _ => 1) 0 false (covMean signLaw) =
        averagingGap Real.log signLaw
          (fun x => Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x)) ∧
      Real.log (∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw) -
          interactionPredictor 0 0 (fun _ => 1) 0 false (covMean signLaw) ≠ 0 ∧
      ∃ ξ : (Fin 1 → ℝ) → ℝ,
        ∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw -
            Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false (covMean signLaw)) =
          1 / 2 * ∫ x, (∑ j, (x j - covMean signLaw j) *
            interactionSlope (fun _ => 1) 0 false j) ^ 2 * Real.exp (ξ x) ∂signLaw := by
  have hη : Measurable (interactionPredictor (p := 1) 0 0 (fun _ => (1 : ℝ)) 0 false) := by
    unfold interactionPredictor; fun_prop
  have hmi : Integrable (fun x => Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x))
      signLaw := integrable_signLaw (Real.measurable_exp.comp hη)
  have hval : ∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw =
      (Real.exp 1 + Real.exp (-1)) / 2 := by
    rw [integral_signLaw (f := fun x => Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x))
      (Real.measurable_exp.comp hη)]
    simp [interactionPredictor, signCov]
  have hx0 : interactionPredictor 0 0 (fun _ => (1 : ℝ)) 0 false (covMean signLaw) = 0 := by
    simp [interactionPredictor, covMean_signLaw]
  have hnd : IsPrognostic signLaw (interactionPredictor (p := 1) 0 0 (fun _ => (1 : ℝ)) 0 false) :=
    isPrognostic_signLaw hη (by norm_num [interactionPredictor, signCov])
  obtain ⟨hne, hne'⟩ := arm_gap_ne_zero (g := Real.log) Set.ordConnected_univ
    Real.continuous_exp.continuousOn
    (Or.inl fun s _ => by simpa [iteratedDeriv_two_exp] using Real.exp_pos s)
    integrable_coord_signLaw 0 0 (fun _ => 1) 0 false
    (ae_of_all _ fun _ => Set.mem_univ _) hmi hnd
  have hpos : 0 < (Real.exp 1 + Real.exp (-1)) / 2 := by positivity
  obtain ⟨ξ, -, -, hL⟩ := arm_gap_eq_lagrange isOpen_univ Set.ordConnected_univ
    Real.contDiff_exp.contDiffOn integrable_coord_signLaw 0 0 (fun _ => 1) 0 false
    (ae_of_all _ fun _ => Set.mem_univ _) (Set.mem_univ _) hmi
  refine ⟨by rw [hval, hx0, Real.exp_zero], hne,
    arm_linkGap_eq_averagingGap Real.log_exp integrable_coord_signLaw 0 0 (fun _ => 1) 0 false,
    hne' Real.log_exp Real.log_injOn_pos (by rw [hval]; exact hpos) (Real.exp_pos _), ξ, ?_⟩
  simpa only [iteratedDeriv_two_exp] using hL

/-- **A negative Jensen gap on a concave scale.** On `(0, ∞)` the logarithm has
`log'' (s) = -1/s² < 0`; for the prognostic positive mean `exp(x)` under `signLaw`,
`∫ log ∘ exp(x) dν = 0 < log ((e + e⁻¹)/2)`. -/
theorem outcomeModel_log_concave_gap :
    ∫ x, Real.log (Real.exp (x 0)) ∂signLaw < Real.log (∫ x, Real.exp (x 0) ∂signLaw) := by
  have hm : Measurable fun x : Fin 1 → ℝ => Real.exp (x 0) := by fun_prop
  refine integral_comp_ne_of_iteratedDeriv_neg (U := Set.Ioi 0) Set.ordConnected_Ioi
    (Real.continuousOn_log.mono fun s hs => (Set.mem_Ioi.1 hs).ne') (fun s hs => ?_)
    (integrable_signLaw hm) (ae_of_all _ fun x => Real.exp_pos (x 0))
    (integrable_signLaw (Real.measurable_log.comp hm))
    (isPrognostic_signLaw hm (by norm_num [signCov]))
  · rw [iteratedDeriv_two_log]
    have : 0 < s ^ 2 := pow_pos (Set.mem_Ioi.1 hs) 2
    exact neg_neg_of_pos (inv_pos.2 this)

/-! ### The plug-in limit and the continuity of the estimands -/

/-- **An instance of the plug-in limit**: with the true parameters of the logit model fitted
exactly (constant estimators) and the mean covariate `x̄ = 0`, the plug-in converges in
probability, on any probability space, to the conditional effect `3/2` at the mean
covariates. -/
theorem outcomeModel_plugIn_limit_example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    TendstoInMeasure μ (fun (_ : ℕ) (_ : Ω) => linkContrast logit
        (fun x => Real.sigmoid (interactionPredictor (p := 1) 0 (3 / 2) (fun _ => 1) 0 false x))
        (fun x => Real.sigmoid (interactionPredictor (p := 1) 0 (3 / 2) (fun _ => 1) 0 true x))
        (0 : Fin 1 → ℝ)) atTop
      (fun _ => 3 / 2) := by
  have h := tendstoInMeasure_plugIn (μ := μ) (ν := signLaw) (αh := fun _ _ => 0)
    (β₁h := fun _ _ => fun _ => 1) (α := 0) (β₁ := fun _ => 1) logit_sigmoid
    (tendstoInMeasure_const (3 / 2 : ℝ)) (tendstoInMeasure_const (0 : Fin 1 → ℝ)) (by
      rw [covMean_signLaw]; exact tendstoInMeasure_const (0 : Fin 1 → ℝ))
  have e : plugInEffect logit signLaw
      (fun x => Real.sigmoid (interactionPredictor 0 (3 / 2) (fun _ => 1) 0 false x))
      (fun x => Real.sigmoid (interactionPredictor 0 (3 / 2) (fun _ => 1) 0 true x)) = 3 / 2 :=
    outcomeModel_logit_plugIn_bias.1
  rwa [e] at h

/-- The logit is continuous at every point of `(0, 1)`. -/
theorem continuousAt_logit {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) : ContinuousAt logit q := by
  have h1 : (1 : ℝ) - q ≠ 0 := by linarith [hq.2]
  have h2 : q / (1 - q) ≠ 0 := div_ne_zero hq.1.ne' h1
  have e : logit = fun p => Real.log (p / (1 - p)) := funext logit_eq_log_div
  rw [e]
  exact (Real.continuousAt_log h2).comp (f := fun p : ℝ => p / (1 - p))
    (continuousAt_id.div (continuousAt_const.sub continuousAt_id) h1)

/-- **An instance of the continuity of the estimands.** Shift both arms of the logit model by
`1/(n + 14)`. The shifted surfaces converge to the model in `L¹(signLaw)` and uniformly, so the
marginal log odds ratios converge to that of the model; the plug-ins converge to `3/2`. -/
theorem outcomeModel_continuity_example :
    Tendsto (fun n : ℕ => linkMarginal logit signLaw
        (fun x => logitOutcomeModel false x + 1 / ((n : ℝ) + 14))
        (fun x => logitOutcomeModel true x + 1 / ((n : ℝ) + 14))) atTop
      (𝓝 (linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true))) ∧
    Tendsto (fun n : ℕ => linkMarginal logit signLaw
        (fun x => logitOutcomeModel false x + 1 / ((n : ℝ) + 14))
        (fun x => logitOutcomeModel true x + 1 / ((n : ℝ) + 14))) atTop
      (𝓝 (linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true))) ∧
    Tendsto (fun n : ℕ => plugInEffect logit signLaw
        (fun x => logitOutcomeModel false x + 1 / ((n : ℝ) + 14))
        (fun x => logitOutcomeModel true x + 1 / ((n : ℝ) + 14))) atTop (𝓝 (3 / 2)) := by
  have hi : ∀ t, Integrable (logitOutcomeModel t) signLaw := fun t =>
    integrable_signLaw (measurable_logitOutcomeModel t)
  have hi' : ∀ t, ∀ᶠ n : ℕ in atTop,
      Integrable (fun x => logitOutcomeModel t x + 1 / ((n : ℝ) + 14)) signLaw :=
    fun t => Eventually.of_forall fun n => (hi t).add (integrable_const _)
  have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 14)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 14 tendsto_natCast_atTop_atTop)
  have hL1 : ∀ t, Tendsto (fun n : ℕ =>
      ∫ x, |logitOutcomeModel t x + 1 / ((n : ℝ) + 14) - logitOutcomeModel t x| ∂signLaw) atTop
      (𝓝 0) := fun t => by
    refine hsmall.congr fun n => ?_
    simp only [add_sub_cancel_left]
    rw [integral_const, abs_of_pos (by positivity)]
    simp
  have hu : ∀ t, TendstoUniformlyOn (fun (n : ℕ) x => logitOutcomeModel t x + 1 / ((n : ℝ) + 14))
      (logitOutcomeModel t) atTop Set.univ := fun t => by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.1 hsmall) ε hε] with n hn x _
    rw [Real.dist_eq, sub_zero] at hn
    rw [Real.dist_eq, sub_add_cancel_left, abs_neg]
    exact hn
  have hD : ∀ t, ∫ x, logitOutcomeModel t x ∂signLaw ∈ Set.Ioo (0 : ℝ) 1 := fun t =>
    integral_mem_Ioo_zero_one (hi t) (ae_of_all _ fun x => sigmoid_mem_Ioo _)
  have hc : ∀ t, ContinuousAt logit (∫ x, logitOutcomeModel t x ∂signLaw) := fun t =>
    continuousAt_logit (hD t)
  refine ⟨tendsto_linkMarginal_of_integral_abs_sub (hi false) (hi true) (hi' false) (hi' true)
      (hL1 false) (hL1 true) (hc false) (hc true),
    tendsto_linkMarginal_of_tendstoUniformlyOn (ae_of_all _ fun x => Set.mem_univ x) (hi false)
      (hi true) (hi' false) (hi' true) (hu false) (hu true) (hc false) (hc true), ?_⟩
  have hpt : ∀ t, Tendsto (fun n : ℕ => logitOutcomeModel t (covMean signLaw) + 1 / ((n : ℝ) + 14))
      atTop (𝓝 (logitOutcomeModel t (covMean signLaw))) := fun t => by
    simpa using tendsto_const_nhds.add hsmall
  have hpc : ∀ t, ContinuousAt logit (logitOutcomeModel t (covMean signLaw)) := fun t =>
    continuousAt_logit (sigmoid_mem_Ioo _)
  have h := tendsto_plugInEffect
    (ma' := fun (n : ℕ) x => logitOutcomeModel false x + 1 / ((n : ℝ) + 14))
    (mb' := fun (n : ℕ) x => logitOutcomeModel true x + 1 / ((n : ℝ) + 14))
    (hpt false) (hpt true) (hpc false) (hpc true)
  rwa [outcomeModel_logit_plugIn_bias.1] at h

/-- **An instance of the two forms of continuity of the integral.** Shifting the reference arm of
the logit model by a constant moves its mean by at most the `L¹` distance; under the shifts
`1/(n + 14)` the means converge to the mean of the model in `L¹(signLaw)` and uniformly, and the
marginal log odds ratios converge by continuity of the logit at the two means. -/
theorem outcomeModel_integral_continuity_example :
    |∫ x, (logitOutcomeModel false x + 1 / 2) ∂signLaw - ∫ x, logitOutcomeModel false x ∂signLaw|
        ≤ ∫ x, |logitOutcomeModel false x + 1 / 2 - logitOutcomeModel false x| ∂signLaw ∧
    Tendsto (fun n : ℕ => ∫ x, (logitOutcomeModel false x + 1 / ((n : ℝ) + 14)) ∂signLaw) atTop
      (𝓝 (∫ x, logitOutcomeModel false x ∂signLaw)) ∧
    Tendsto (fun n : ℕ => ∫ x, (logitOutcomeModel true x + 1 / ((n : ℝ) + 14)) ∂signLaw) atTop
      (𝓝 (∫ x, logitOutcomeModel true x ∂signLaw)) ∧
    Tendsto (fun n : ℕ => linkMarginal logit signLaw
        (fun x => logitOutcomeModel false x + 1 / ((n : ℝ) + 14))
        (fun x => logitOutcomeModel true x + 1 / ((n : ℝ) + 14))) atTop
      (𝓝 (linkMarginal logit signLaw (logitOutcomeModel false) (logitOutcomeModel true))) := by
  have hi : ∀ t, Integrable (logitOutcomeModel t) signLaw := fun t =>
    integrable_signLaw (measurable_logitOutcomeModel t)
  have hi' : ∀ t, ∀ᶠ n : ℕ in atTop,
      Integrable (fun x => logitOutcomeModel t x + 1 / ((n : ℝ) + 14)) signLaw :=
    fun t => Eventually.of_forall fun n => (hi t).add (integrable_const _)
  have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 14)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 14 tendsto_natCast_atTop_atTop)
  have hL1 : Tendsto (fun n : ℕ =>
      ∫ x, |logitOutcomeModel false x + 1 / ((n : ℝ) + 14) - logitOutcomeModel false x| ∂signLaw)
      atTop (𝓝 0) := by
    refine hsmall.congr fun n => ?_
    simp only [add_sub_cancel_left]
    rw [integral_const, abs_of_pos (by positivity)]
    simp
  have hu : ∀ t, TendstoUniformlyOn
      (fun (n : ℕ) x => logitOutcomeModel t x + 1 / ((n : ℝ) + 14))
      (logitOutcomeModel t) atTop Set.univ := fun t => by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.1 hsmall) ε hε] with n hn x _
    rw [Real.dist_eq, sub_zero] at hn
    rw [Real.dist_eq, sub_add_cancel_left, abs_neg]
    exact hn
  have hA := tendsto_integral_of_tendsto_integral_abs_sub (hi false) (hi' false) hL1
  have hB := tendsto_integral_of_tendstoUniformlyOn (ae_of_all _ fun x => Set.mem_univ x)
    (hi true) (hi' true) (hu true)
  have hc : ∀ t, ContinuousAt logit (∫ x, logitOutcomeModel t x ∂signLaw) := fun t =>
    continuousAt_logit (integral_mem_Ioo_zero_one (hi t)
      (ae_of_all _ fun x => sigmoid_mem_Ioo _))
  exact ⟨abs_integral_sub_integral_le (hi false) ((hi false).add (integrable_const _)), hA, hB,
    tendsto_linkMarginal hA hB (hc false) (hc true)⟩

/-- **An instance of the lemmas on the linear predictor.** For `η_t(x) = x + 1{t}(1 + 2x)` under
`signLaw`: the active arm changes by the slope `3` times the covariate change (`6` from `-1` to
`1`); the interaction term `2x` is integrable with mean `0`; the active predictor is integrable;
the anchored predictor averages to `1`; on the logit link the average conditional effect of the
logit model is the plug-in `3/2`; without interactions the marginal estimand on the identity
link is `γ = 1`; for the population `(signLaw, id)` the mean covariate is the mean of the
covariate over the sample space; and the plug-in is the logit contrast at `x̄ = 0`. -/
theorem outcomeModel_linear_example :
    interactionPredictor (p := 1) 0 1 (fun _ => 1) (fun _ => 2) true (fun _ => 1) -
        interactionPredictor (p := 1) 0 1 (fun _ => 1) (fun _ => 2) true (fun _ => -1) = 6 ∧
      Integrable (fun x : Fin 1 → ℝ => ∑ j, x j * 2) signLaw ∧
      ∫ x : Fin 1 → ℝ, ∑ j, x j * 2 ∂signLaw = 0 ∧
      Integrable (interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) true) signLaw ∧
      ∫ x, anchoredPredictor 0 (fun _ => 1) 1 (fun _ => 2) x ∂signLaw = 1 ∧
      linkConditional logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) = 3 / 2 ∧
      linkMarginal id signLaw (interactionPredictor 0 1 (fun _ => 1) 0 false)
        (interactionPredictor 0 1 (fun _ => 1) 0 true) = 1 ∧
      covMean (⟨signLaw, id, fun t => interactionPredictor 0 1 (fun _ => 1) (fun _ => 2) t⟩ :
          Population (Fin 1 → ℝ) (Fin 1 → ℝ) Bool).covLaw 0 = ∫ x : Fin 1 → ℝ, x 0 ∂signLaw ∧
      plugInEffect logit signLaw (logitOutcomeModel false) (logitOutcomeModel true) =
        logit (logitOutcomeModel true 0) - logit (logitOutcomeModel false 0) := by
  have hm : ∀ t x, logit (logitOutcomeModel t x) =
      interactionPredictor 0 (3 / 2) (fun _ => 1) 0 t x := fun t x => logit_sigmoid _
  refine ⟨?_, integrable_sum_mul integrable_coord_signLaw (fun _ => 2), ?_,
    integrable_interactionPredictor integrable_coord_signLaw 0 1 _ _ true, ?_, ?_,
    linkMarginal_id_interactionPredictor_of_zero integrable_coord_signLaw 0 1 _,
    covMean_covLaw (Q := ⟨signLaw, id, fun t => interactionPredictor 0 1 (fun _ => 1)
      (fun _ => 2) t⟩) measurable_id 0, by rw [plugInEffect_eq, covMean_signLaw]⟩
  · rw [interactionPredictor_sub_interactionPredictor]
    simp [interactionSlope]
    norm_num
  · rw [integral_sum_mul integrable_coord_signLaw, covMean_signLaw]
    simp
  · rw [integral_anchoredPredictor integrable_coord_signLaw, covMean_signLaw]
    simp [anchoredPredictor]
  · rw [(linkConditional_eq_plugInEffect_interactionPredictor integrable_coord_signLaw hm).2,
      covMean_signLaw, zero_dotProduct, add_zero]

/-- A property of the covariate holding at `±1`, on a measurable set, holds `signLaw`-almost
surely. -/
theorem ae_signLaw_of {P : (Fin 1 → ℝ) → Prop} (hP : MeasurableSet {x | P x})
    (h : ∀ v, P (signCov v)) : ∀ᵐ x ∂signLaw, P x := by
  rw [signLaw, ae_map_iff (measurable_of_finite signCov).aemeasurable hP]
  exact ae_of_all _ h

/-- **An instance of the curvature lemmas.** With the covariate `x ∈ {±1}` of `signLaw`:
the Jensen gap of `exp` has its Lagrange form and is positive, `exp(∫ x) < ∫ exp(x)`; on the log
link with `m(x) = exp(x)` the link scale gap vanishes exactly when the response scale gap does
(the logarithm is injective on `(0, ∞)`); and for the inverse link `log`, concave on `(0, ∞)`,
and the positive predictor `η(x) = 2 + x`, the response scale gap is nonzero. -/
theorem outcomeModel_curvature_example :
    (∃ ξ : (Fin 1 → ℝ) → ℝ, ∫ x, Real.exp (x 0) ∂signLaw - Real.exp (∫ x, x 0 ∂signLaw) =
      1 / 2 * ∫ x, (x 0 - ∫ y, y 0 ∂signLaw) ^ 2 * Real.exp (ξ x) ∂signLaw) ∧
    Real.exp (∫ x, x 0 ∂signLaw) < ∫ x, Real.exp (x 0) ∂signLaw ∧
    (Real.log (∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw) -
          interactionPredictor 0 0 (fun _ => 1) 0 false (covMean signLaw) = 0 ↔
        ∫ x, Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false x) ∂signLaw -
          Real.exp (interactionPredictor 0 0 (fun _ => 1) 0 false (covMean signLaw)) = 0) ∧
    ∫ x, Real.log (interactionPredictor 2 0 (fun _ => 1) 0 false x) ∂signLaw -
        Real.log (interactionPredictor 2 0 (fun _ => 1) 0 false (covMean signLaw)) ≠ 0 := by
  have hx : Measurable fun x : Fin 1 → ℝ => x 0 := measurable_pi_apply 0
  have hnd : IsPrognostic signLaw fun x : Fin 1 → ℝ => x 0 :=
    isPrognostic_signLaw hx (by norm_num [signCov])
  obtain ⟨ξ, -, -, -, hL⟩ := exists_integral_sub_eq_lagrange isOpen_univ Set.ordConnected_univ
    Real.contDiff_exp.contDiffOn (integrable_coord_signLaw 0) (ae_of_all _ fun _ => Set.mem_univ _)
    (Set.mem_univ _) (integrable_signLaw (Real.measurable_exp.comp hx))
  have hη : Measurable (interactionPredictor (p := 1) 0 0 (fun _ => (1 : ℝ)) 0 false) := by
    unfold interactionPredictor; fun_prop
  have hη2 : Measurable (interactionPredictor (p := 1) 2 0 (fun _ => (1 : ℝ)) 0 false) := by
    unfold interactionPredictor; fun_prop
  have hpos2 : ∀ᵐ x ∂signLaw, interactionPredictor 2 0 (fun _ => 1) 0 false x ∈ Set.Ioi 0 :=
    ae_signLaw_of (measurableSet_Ioi.preimage hη2) fun v => by
      cases v <;> norm_num [interactionPredictor, signCov]
  have hgap := (arm_gap_ne_zero (g := Real.exp) (U := Set.Ioi 0) Set.ordConnected_Ioi
    (Real.continuousOn_log.mono fun s hs => (Set.mem_Ioi.1 hs).ne')
    (Or.inr fun s hs => by
      rw [iteratedDeriv_two_log]
      exact neg_neg_of_pos (inv_pos.2 (pow_pos (Set.mem_Ioi.1 hs) 2)))
    integrable_coord_signLaw 2 0 (fun _ => 1) 0 false hpos2
    (integrable_signLaw (Real.measurable_log.comp hη2))
    (isPrognostic_signLaw hη2 (by norm_num [interactionPredictor, signCov]))).1
  refine ⟨⟨ξ, by simpa only [iteratedDeriv_two_exp] using hL⟩,
    integral_comp_ne_of_iteratedDeriv_pos Set.ordConnected_univ Real.continuous_exp.continuousOn
      (fun s _ => by rw [iteratedDeriv_two_exp]; exact Real.exp_pos s) (integrable_coord_signLaw 0)
      (ae_of_all _ fun _ => Set.mem_univ _) (integrable_signLaw (Real.measurable_exp.comp hx)) hnd,
    arm_linkGap_eq_zero_iff Real.log_exp Real.log_injOn_pos 0 0 (fun _ => 1) 0 false
      (integral_pos_of_ae_pos (integrable_signLaw (Real.measurable_exp.comp hη))
        (ae_of_all _ fun _ => Real.exp_pos _)) (Real.exp_pos _), hgap⟩

end PopulationAdjustment

end CausalInference
