/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.BridgeStandardizationLogit
public import CausalInference.PopulationAdjustment.StandardizationInstancesLogistic

/-!
# The multilevel model with the logit link: an instance and two different limits

Two trials of `a = true` against `c = false` with a binary outcome, both following the
multilevel model `logitBridgeModel` with the logit link at the baseline `0`: `γ_c = 0`,
`γ_a = log 3`, `β₁ = 0`, `β₂,c = 0`, `β₂,a = log 3`, so `η_c(u) = 0` and
`η_a(u) = log 3 · (1 + u)`. The covariate takes three values `x ∈ {0, 1, 2}`, uniform in the
trial; the arm is a fair coin; the outcome is `Y(e) = 1[U < k(e, x)]` for a uniform noise `U` on
`{0, ..., 19}`, independent of the rest, with thresholds chosen so that
`P(Y(e) = 1 | x) = σ(η_k(φ(x)))`.

* **A three valued feature: the two limits differ** (`logitBridgeDiffer_limits`). The feature is
  `φ(x) = x - 1 ∈ {-1, 0, 1}`, with the trial mean `0`; the target puts all its mass at `x = 1`,
  so its feature mean is also `t = 0`. The risks of `a` are `1/2, 3/4, 9/10`: not affine in the
  feature. Every hypothesis of `MultilevelModel.commonLimit_logit` holds. The population tilt is
  `0` (the trial already has the feature mean `t`), so the weighted log odds ratio converges to
  the trial marginal log odds ratio `logit (43/60) - logit (1/2) = log (43/17)`, while the
  standardized one converges to the marginal log odds ratio of the multilevel surfaces under the
  target law, `logit (3/4) = log 3`. The two limits differ.
* **A two valued feature: the two limits agree** (`logitBridgeAgree_limits`). The feature is
  `φ(x) = 1[x = 2]`, the target covariate law is `(1/4, 1/4, 1/2)` with the feature mean
  `t = 1/2`. The risks `3/4, 9/10` of `a` and `1/2` of `c` are affine in the feature, and every
  hypothesis of `MultilevelModel.commonLimit_logit_of_affine` holds: both estimators converge to
  `logit (33/40) = log (33/7)`, which is the target marginal log odds ratio
  (`MultilevelModel.commonLimit_logit_marginalEffect`).

## Main definitions

* `logitBridgeModel`, `logitBridgeTrial`, `logitBridgeSample`, `logitBridgeDifferTarget`,
  `logitBridgeAgreeTarget`.

## Main results

* `logitBridgeTrial_isRandomizedTwoArm`, `logitBridgeTrial_isOutcomeRegression`,
  `logitBridgeTrial_law`.
* `logitBridgeDiffer_limits`, `logitBridgeAgree_limits`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport PopulationAdjustment

/-! ### The noise, the covariate law and the outcome -/

/-- The uniform law of the noise on `{0, ..., 19}`. -/
noncomputable def logitBridgeNoise : Measure (Fin 20) := stratumLaw fun _ => 1 / 20

instance : IsProbabilityMeasure logitBridgeNoise :=
  isProbabilityMeasure_stratumLaw ⟨fun _ => by norm_num, by simp⟩

/-- The uniform law of the covariate on `{0, 1, 2}`. -/
noncomputable def logitBridgeCovLaw : Measure (Fin 3) := stratumLaw fun _ => 1 / 3

instance : IsProbabilityMeasure logitBridgeCovLaw :=
  isProbabilityMeasure_stratumLaw ⟨fun _ => by norm_num, by simp⟩

theorem integral_logitBridgeCovLaw (f : Fin 3 → ℝ) :
    ∫ x, f x ∂logitBridgeCovLaw = (f 0 + f 1 + f 2) / 3 := by
  rw [logitBridgeCovLaw, integral_stratumLaw (fun _ => by norm_num), standardizedRisk,
    Fin.sum_univ_three]
  ring

/-- The outcome `1[u < k]` of a noise value `u`. -/
noncomputable def logitBridgeOutcome (k : ℕ) (u : Fin 20) : ℝ := if (u : ℕ) < k then 1 else 0

theorem logitBridgeOutcome_mem (k : ℕ) (u : Fin 20) :
    logitBridgeOutcome k u = 0 ∨ logitBridgeOutcome k u = 1 := by
  unfold logitBridgeOutcome
  split_ifs <;> simp

/-- Averaging the outcome over the noise gives the risk `k/20`, for `k ≤ 20`. -/
theorem integral_logitBridgeOutcome {k : ℕ} (hk : k ≤ 20) :
    ∫ u, logitBridgeOutcome k u ∂logitBridgeNoise = k / 20 := by
  rw [logitBridgeNoise, integral_stratumLaw (fun _ => by norm_num), standardizedRisk]
  simp only [logitBridgeOutcome, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    Fin.card_filter_val_lt, min_eq_right hk]
  ring

/-! ### The trial with thresholds `k` -/

/-- The trial with thresholds `k`: assignment `ω.1.1`, covariate `ω.1.2` and noise `ω.2`,
independent; a fair coin, a uniform covariate on `{0, 1, 2}` and a uniform noise on
`{0, ..., 19}`; the potential outcome `Y(e) = 1[U < k(e, X)]`. -/
noncomputable def logitBridgeTrial (k : Bool → Fin 3 → ℕ) :
    Trial ((Bool × Fin 3) × Fin 20) (Fin 3) Bool where
  μ := (halfLaw.prod logitBridgeCovLaw).prod logitBridgeNoise
  X ω := ω.1.2
  Y e ω := logitBridgeOutcome (k e ω.1.2) ω.2
  A ω := ω.1.1

variable (k : Bool → Fin 3 → ℕ)

instance : IsProbabilityMeasure (logitBridgeTrial k).μ := by
  unfold logitBridgeTrial; infer_instance

theorem logitBridgeTrial_covLaw : (logitBridgeTrial k).covLaw = logitBridgeCovLaw := by
  change ((halfLaw.prod logitBridgeCovLaw).prod logitBridgeNoise).map
    (Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_snd measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul, Measure.map_snd_prod, measure_univ, one_smul]

instance : IsProbabilityMeasure (logitBridgeTrial k).covLaw := by
  rw [logitBridgeTrial_covLaw]; infer_instance

/-- **The trial is randomized.** The assignment is the first factor of the product law, and the
covariate and the potential outcomes are functions of the other two. -/
theorem logitBridgeTrial_isRandomizedTwoArm : (logitBridgeTrial k).IsRandomizedTwoArm where
  measurable_X := measurable_of_finite _
  measurable_A := measurable_of_finite _
  measurable_Y _ := measurable_of_finite _
  indepFun := by
    set G : Fin 3 × Fin 20 → Fin 3 × ℝ × ℝ := fun v =>
      (v.1, (logitBridgeOutcome (k false v.1) v.2, logitBridgeOutcome (k true v.1) v.2))
    have h := indepFun_prod (μ := halfLaw) (ν := logitBridgeCovLaw.prod logitBridgeNoise)
      (X := id) (Y := G) measurable_id (measurable_of_finite G)
    rw [← Measure.prodAssoc_prod] at h
    exact indepFun_comp_of_indepFun_map MeasurableEquiv.prodAssoc.measurable
      (measurable_id.comp measurable_fst) ((measurable_of_finite G).comp measurable_snd) h
  prob_pos := by
    change 0 < ((halfLaw.prod logitBridgeCovLaw).prod logitBridgeNoise).real
      ((fun ω : (Bool × Fin 3) × Fin 20 => ω.1.1) ⁻¹' {true})
    have e : (fun ω : (Bool × Fin 3) × Fin 20 => ω.1.1) ⁻¹' {true} =
        ({true} ×ˢ Set.univ) ×ˢ Set.univ := by ext; simp
    rw [e, measureReal_def, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
      mul_one, mul_one]
    simp [halfLaw, stratumLaw]
  prob_lt_one := by
    change ((halfLaw.prod logitBridgeCovLaw).prod logitBridgeNoise).real
      ((fun ω : (Bool × Fin 3) × Fin 20 => ω.1.1) ⁻¹' {true}) < 1
    have e : (fun ω : (Bool × Fin 3) × Fin 20 => ω.1.1) ⁻¹' {true} =
        ({true} ×ˢ Set.univ) ×ˢ Set.univ := by ext; simp
    rw [e, measureReal_def, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
      mul_one, mul_one]
    simp [halfLaw, stratumLaw]
    norm_num

/-- **The regression of the trial** is `k(A, X)/20`, computed by averaging the outcome over the
independent noise, for thresholds at most `20`. -/
theorem logitBridgeTrial_isOutcomeRegression (hk : ∀ e x, k e x ≤ 20) :
    IsOutcomeRegression (logitBridgeTrial k).μ (logitBridgeTrial k).A (logitBridgeTrial k).X
      (logitBridgeTrial k).obsOutcome fun e x => (k e x : ℝ) / 20 := by
  refine ⟨fun _ => measurable_of_finite _, ?_⟩
  exact condExp_prod_comp_fst (ρ := halfLaw.prod logitBridgeCovLaw) (τ := logitBridgeNoise)
    (W := fun v : Bool × Fin 3 => (v.2, v.1)) (measurable_of_finite _)
    (F := fun ω => logitBridgeOutcome (k ω.1.1 ω.1.2) ω.2) Integrable.of_finite
    (φ := fun c : Fin 3 × Bool => (k c.2 c.1 : ℝ) / 20) (measurable_of_finite _)
    fun v => integral_logitBridgeOutcome (hk v.1 v.2)

/-- The record `((X, A), Y)` of a unit of the trial. -/
noncomputable def logitBridgeRecord (ω : (Bool × Fin 3) × Fin 20) : (Fin 3 × Bool) × ℝ :=
  (((logitBridgeTrial k).X ω, (logitBridgeTrial k).A ω), (logitBridgeTrial k).obsOutcome ω)

/-- **The trial follows the multilevel logistic model** when its risks are the multilevel risks:
if `k(e, x)/20 = σ(z(e, x) ⬝ ipdCoef M μ a c)` in the interaction design of features with the
margin condition at `t`, the records have the law of the logistic family at `ipdCoef M μ a c`. -/
theorem logitBridgeTrial_law {J K : Type*} {p : ℕ} (M : MultilevelModel J K p) (μ : ℝ)
    (a c : K) {φ : Fin 3 → Fin p → ℝ} {t : Fin p → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ v : Fin p → ℝ, ‖v‖ = 1 →
      δ ≤ (logitBridgeTrial k).covLaw.real {x | δ ≤ v ⬝ᵥ (φ x - t)})
    (hk : ∀ e x, k e x ≤ 20)
    (hrisk : ∀ e x, (k e x : ℝ) / 20 =
      Real.sigmoid (featureInteractionDesign φ e x ⬝ᵥ M.ipdCoef μ a c)) :
    (logitBridgeTrial k).μ.map (fun ω => (((logitBridgeTrial k).X ω, (logitBridgeTrial k).A ω),
        (logitBridgeTrial k).obsOutcome ω)) =
      (glmFamily logisticKernel
        ((logitBridgeTrial k).μ.map fun ω => ((logitBridgeTrial k).X ω, (logitBridgeTrial k).A ω))
        (fun q => featureInteractionDesign φ q.2 q.1)
        (measurable_featureInteractionDesign_pair (measurable_of_finite φ))).law
        (M.ipdCoef μ a c) := by
  have hT := logitBridgeTrial_isRandomizedTwoArm k
  have hreg := logitBridgeTrial_isOutcomeRegression k hk
  simp only [hrisk] at hreg
  exact (Trial.LogisticOutcomeModel.of_isOutcomeRegression (ξ₀ := M.ipdCoef μ a c) hT
    (measurable_featureInteractionDesign_pair (measurable_of_finite φ))
    (fun _ => Integrable.of_finite)
    (fun _ hv => featureInteractionDesign_eq_zero_of_ae hT (measurable_of_finite φ) hδ hmargin hv)
    (ae_of_all _ fun ω => logitBridgeOutcome_mem _ _) hreg).law_eq

/-- The law of the sample: infinitely many independent copies of the trial. -/
noncomputable def logitBridgeSampleLaw : Measure (ℕ → (Bool × Fin 3) × Fin 20) :=
  Measure.infinitePi fun _ => (logitBridgeTrial k).μ

instance : IsProbabilityMeasure (logitBridgeSampleLaw k) := by
  unfold logitBridgeSampleLaw; infer_instance

/-- The records of the sample. -/
noncomputable def logitBridgeSample (i : ℕ) (ω : ℕ → (Bool × Fin 3) × Fin 20) :
    (Fin 3 × Bool) × ℝ :=
  logitBridgeRecord k (ω i)

theorem measurable_logitBridgeSample (i : ℕ) : Measurable (logitBridgeSample k i) :=
  (measurable_of_finite (logitBridgeRecord k)).comp (measurable_pi_apply i)

theorem map_logitBridgeSample (i : ℕ) :
    (logitBridgeSampleLaw k).map (logitBridgeSample k i) =
      (logitBridgeTrial k).μ.map (logitBridgeRecord k) := by
  have : logitBridgeSample k i = logitBridgeRecord k ∘ fun x : ℕ → (Bool × Fin 3) × Fin 20 => x i :=
    rfl
  rw [this, ← Measure.map_map (g := logitBridgeRecord k) (measurable_of_finite _)
    (measurable_pi_apply i), logitBridgeSampleLaw, Measure.infinitePi_map_eval]

/-- **The sample is i.i.d.** -/
theorem isIIDSample_logitBridgeSample :
    IsIIDSample (logitBridgeSample k) (logitBridgeSampleLaw k) where
  indep := iIndepFun_infinitePi (P := fun _ => (logitBridgeTrial k).μ)
    fun _ => measurable_of_finite (logitBridgeRecord k)
  ident i := ⟨(measurable_logitBridgeSample k i).aemeasurable,
    (measurable_logitBridgeSample k 0).aemeasurable,
    (map_logitBridgeSample k i).trans (map_logitBridgeSample k 0).symm⟩

/-! ### The multilevel model -/

/-- The multilevel model of the examples: one study, no prognostic effect, `γ_c = 0`,
`γ_a = log 3`, `β₂,c = 0` and `β₂,a = log 3`, with `a = true` and `c = false`. -/
noncomputable def logitBridgeModel : MultilevelModel Unit Bool 1 :=
  ⟨fun _ => 0, fun _ => 0, fun k => if k then Real.log 3 else 0,
    fun k _ => if k then Real.log 3 else 0⟩

theorem logitBridgeModel_surface (k : Bool) (u : Fin 1 → ℝ) :
    logitBridgeModel.surface Real.sigmoid 0 k u =
      Real.sigmoid (if k then Real.log 3 * (1 + u 0) else 0) := by
  simp only [MultilevelModel.surface, MultilevelModel.eta_eq_affine, logitBridgeModel,
    dotProduct, Fin.sum_univ_one, Pi.add_apply]
  cases k <;> simp
  ring

theorem sigmoid_log_three : Real.sigmoid (Real.log 3) = 3 / 4 := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

theorem sigmoid_two_log_three : Real.sigmoid (Real.log 3 * 2) = 9 / 10 := by
  have h9 : Real.log 3 * 2 = Real.log 9 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [Real.sigmoid_def, Real.exp_neg, h9, Real.exp_log (by norm_num)]
  norm_num

theorem logit_div {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    logit (a / b) = Real.log (a / (b - a)) := by
  have hb : 0 < b := ha.trans hab
  simp only [logit, odds]
  congr 1
  field_simp

theorem logit_half : logit (1 / 2) = 0 := by
  rw [logit_div one_pos (by norm_num)]; norm_num

/-! ### A three valued feature: the two limits differ -/

/-- The three valued feature `x - 1`. -/
noncomputable def logitBridgeDifferFeature (x : Fin 3) : Fin 1 → ℝ := fun _ => (x : ℝ) - 1

/-- The thresholds of the three valued example: `10, 15, 18` on the arm `true` and `10` on the
arm `false`, the risks `1/2, 3/4, 9/10` and `1/2`. -/
def logitBridgeDifferK (e : Bool) (x : Fin 3) : ℕ := if e then ![10, 15, 18] x else 10

theorem logitBridgeDifferK_le (e : Bool) (x : Fin 3) : logitBridgeDifferK e x ≤ 20 := by
  cases e <;> fin_cases x <;> simp [logitBridgeDifferK]

theorem logitBridgeDiffer_risk (e : Bool) (x : Fin 3) :
    (logitBridgeDifferK e x : ℝ) / 20 =
      logitBridgeModel.surface Real.sigmoid 0 e (logitBridgeDifferFeature x) := by
  rw [logitBridgeModel_surface]
  cases e <;> fin_cases x <;>
    norm_num [logitBridgeDifferK, logitBridgeDifferFeature, Real.sigmoid_zero, sigmoid_log_three,
      sigmoid_two_log_three]

theorem logitBridgeDiffer_bound (x : Fin 3) : ‖logitBridgeDifferFeature x - 0‖ ≤ 1 := by
  rw [sub_zero, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  fin_cases x <;> simp [logitBridgeDifferFeature]
  norm_num

/-- A singleton of the covariate has probability `1/3` in the trial. -/
theorem logitBridgeTrial_real_singleton (x : Fin 3) :
    (logitBridgeTrial k).covLaw.real {x} = 1 / 3 := by
  rw [logitBridgeTrial_covLaw, measureReal_def, logitBridgeCovLaw]
  simp [stratumLaw, Pi.single_apply]

theorem norm_fin_one_eq {v : Fin 1 → ℝ} (hv : ‖v‖ = 1) : v 0 = 1 ∨ v 0 = -1 := by
  have h : ‖v‖ = ‖v 0‖ := by
    refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
      (norm_le_pi_norm v 0)
    rw [Subsingleton.elim j 0]
  rw [h, Real.norm_eq_abs] at hv
  exact abs_eq zero_le_one |>.1 hv

theorem logitBridgeDiffer_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 3 : ℝ) ≤
    (logitBridgeTrial logitBridgeDifferK).covLaw.real
      {x | 1 / 3 ≤ v ⬝ᵥ (logitBridgeDifferFeature x - 0)} := by
  intro v hv
  rcases norm_fin_one_eq hv with h | h
  · refine (logitBridgeTrial_real_singleton _ 2).symm.le.trans
      (measureReal_mono (fun x hx => ?_) (measure_ne_top _ _))
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, logitBridgeDifferFeature]
    norm_num
  · refine (logitBridgeTrial_real_singleton _ 0).symm.le.trans
      (measureReal_mono (fun x hx => ?_) (measure_ne_top _ _))
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, logitBridgeDifferFeature]
    norm_num

theorem logitBridgeDiffer_law :
    (logitBridgeTrial logitBridgeDifferK).μ.map (fun ω =>
        (((logitBridgeTrial logitBridgeDifferK).X ω, (logitBridgeTrial logitBridgeDifferK).A ω),
        (logitBridgeTrial logitBridgeDifferK).obsOutcome ω)) =
      (glmFamily logisticKernel ((logitBridgeTrial logitBridgeDifferK).μ.map fun ω =>
          ((logitBridgeTrial logitBridgeDifferK).X ω, (logitBridgeTrial logitBridgeDifferK).A ω))
        (fun q => featureInteractionDesign logitBridgeDifferFeature q.2 q.1)
        (measurable_featureInteractionDesign_pair (measurable_of_finite _))).law
        (logitBridgeModel.ipdCoef 0 true false) :=
  logitBridgeTrial_law _ _ _ _ _ (by norm_num) logitBridgeDiffer_margin logitBridgeDifferK_le
    fun e x => by
      rw [logitBridgeDiffer_risk, MultilevelModel.sigmoid_featureInteractionDesign_ipdCoef]
      cases e <;> rfl

/-- The population tilt of the three valued example is `0`: the trial already has the feature
mean `0`. -/
theorem logitBridgeDiffer_tiltMinimizer :
    tiltMinimizer (logitBridgeTrial logitBridgeDifferK).ipdLaw logitBridgeDifferFeature 0 = 0 := by
  have hT := logitBridgeTrial_isRandomizedTwoArm logitBridgeDifferK
  have : IsProbabilityMeasure (logitBridgeTrial logitBridgeDifferK).ipdLaw := by
    rw [Trial.ipdLaw]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_of_finite _).aemeasurable).2
      inferInstance
  refine tiltMinimizer_eq_of_balance (measurable_of_finite _) logitBridgeDiffer_bound
    (by norm_num : (0 : ℝ) < 1 / 3) (commonLimitFollowUp_margin_ipdLaw hT
      (measurable_of_finite _) logitBridgeDiffer_margin) fun j => ?_
  rw [commonLimitFollowUp_integral_ipdLaw_fst hT
    (f := fun x => tiltWeight logitBridgeDifferFeature 0 0 0 x *
      (logitBridgeDifferFeature x j - (0 : Fin 1 → ℝ) j)) (measurable_of_finite _),
    logitBridgeTrial_covLaw, integral_logitBridgeCovLaw]
  simp [tiltWeight, logitBridgeDifferFeature]
  norm_num

/-- Averages under the tilted law of the three valued example are trial averages. -/
theorem logitBridgeDiffer_integral_tilted (f : Fin 3 → ℝ) :
    ∫ x, f x ∂commonLimitFollowUpTilted (logitBridgeTrial logitBridgeDifferK)
      logitBridgeDifferFeature 0 = (f 0 + f 1 + f 2) / 3 := by
  rw [commonLimitFollowUp_integral_tiltedCovLaw (measurable_of_finite _)]
  simp only [commonLimitFollowUpTilt, logitBridgeDiffer_tiltMinimizer, logitBridgeTrial_covLaw,
    integral_logitBridgeCovLaw]
  simp [tiltWeight]
  ring

/-- The target of the three valued example: all its mass at `x = 1`, where the feature is `0`. -/
noncomputable def logitBridgeDifferTarget : Population (Fin 3) (Fin 3) Bool where
  μ := Measure.dirac 1
  X := id
  Y _ _ := 0

theorem logitBridgeDifferTarget_covLaw : logitBridgeDifferTarget.covLaw = Measure.dirac 1 := by
  change (Measure.dirac (1 : Fin 3)).map id = _
  rw [Measure.map_id]

/-- **The two limits differ.** In the three valued example every hypothesis of
`MultilevelModel.commonLimit_logit` holds with `a = true`, `c = false`, `t = 0`, `δ = 1/3`,
`B = 1`, the fit over the closed ball of radius `4` and the target at `x = 1`, whose feature mean
is `t`. The logistic fit converges in probability to `ipdCoef = (0, 0, log 3, log 3)`; the
standardized marginal log odds ratio converges in probability to `log 3`, the marginal log odds
ratio of the multilevel surfaces under the target law; the weighted log odds ratio converges to
`log (43/17)`, the same functional under the tilted law, here the trial covariate law, which has
the feature mean `0`; and the two limits differ. -/
theorem logitBridgeDiffer_limits :
    TendstoInMeasure (logitBridgeSampleLaw logitBridgeDifferK)
      (glmMLE logisticDens (fun q => featureInteractionDesign logitBridgeDifferFeature q.2 q.1)
        (Metric.closedBall 0 4) (logitBridgeSample logitBridgeDifferK))
      atTop (fun _ => logitBridgeModel.ipdCoef 0 true false) ∧
    TendstoInMeasure (logitBridgeSampleLaw logitBridgeDifferK) (fun n ω =>
        linkMarginal logit logitBridgeDifferTarget.covLaw
          (fun x => Real.sigmoid (featureInteractionDesign logitBridgeDifferFeature false x ⬝ᵥ
            glmMLE logisticDens (fun q => featureInteractionDesign logitBridgeDifferFeature q.2 q.1)
              (Metric.closedBall 0 4) (logitBridgeSample logitBridgeDifferK) n ω))
          (fun x => Real.sigmoid (featureInteractionDesign logitBridgeDifferFeature true x ⬝ᵥ
            glmMLE logisticDens (fun q => featureInteractionDesign logitBridgeDifferFeature q.2 q.1)
              (Metric.closedBall 0 4) (logitBridgeSample logitBridgeDifferK) n ω)))
      atTop (fun _ => Real.log 3) ∧
    TendstoInMeasure (logitBridgeSampleLaw logitBridgeDifferK) (fun n ω =>
        logit (sampleBalancedArmMean logitBridgeDifferFeature 0
          (fun i ω => commonLimitReassoc (logitBridgeSample logitBridgeDifferK i ω)) true n ω) -
        logit (sampleBalancedArmMean logitBridgeDifferFeature 0
          (fun i ω => commonLimitReassoc (logitBridgeSample logitBridgeDifferK i ω)) false n ω))
      atTop (fun _ => Real.log (43 / 17)) ∧
    ∫ x, logitBridgeDifferFeature x 0 ∂commonLimitFollowUpTilted
      (logitBridgeTrial logitBridgeDifferK) logitBridgeDifferFeature 0 = 0 ∧
    ∫ x, logitBridgeDifferFeature x 0 ∂logitBridgeDifferTarget.covLaw = 0 ∧
    Real.log 3 ≠ Real.log (43 / 17) := by
  have hT := logitBridgeTrial_isRandomizedTwoArm logitBridgeDifferK
  have : IsProbabilityMeasure logitBridgeDifferTarget.μ := by
    unfold logitBridgeDifferTarget; infer_instance
  have hξ : logitBridgeModel.ipdCoef 0 true false ∈
      (Metric.closedBall 0 4 : Set (Option (Fin 1) ⊕ Option (Fin 1) → ℝ)) := by
    have h3 : Real.log 3 ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    have h0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    rintro (o | o) <;> rcases o with _ | _ <;>
      simp [MultilevelModel.ipdCoef, logitBridgeModel, abs_of_nonneg h0, h3]
  obtain ⟨hfit, hS, hW, htilt⟩ := logitBridgeModel.commonLimit_logit hT (measurable_of_finite _)
    logitBridgeDiffer_bound (by norm_num : (0 : ℝ) < 1 / 3) logitBridgeDiffer_margin
    logitBridgeDiffer_law (isCompact_closedBall _ _) hξ (isIIDSample_logitBridgeSample _)
    (measurable_logitBridgeSample _) (map_logitBridgeSample _ 0)
    (Q := logitBridgeDifferTarget) measurable_id
  have hmap : ∀ (ν : Measure (Fin 3)) (k : Bool),
      ∫ u, logitBridgeModel.surface Real.sigmoid 0 k u ∂(ν.map logitBridgeDifferFeature) =
      ∫ x, logitBridgeModel.surface Real.sigmoid 0 k (logitBridgeDifferFeature x) ∂ν :=
    fun ν k => integral_map (measurable_of_finite _).aemeasurable
      (logitBridgeModel.measurable_surface continuous_sigmoid.measurable 0 k).aestronglyMeasurable
  have hrisk : ∀ (e : Bool) (x : Fin 3),
      logitBridgeModel.surface Real.sigmoid 0 e (logitBridgeDifferFeature x) =
        (logitBridgeDifferK e x : ℝ) / 20 := fun e x => (logitBridgeDiffer_risk e x).symm
  have hSv : linkMarginal logit (logitBridgeDifferTarget.covLaw.map logitBridgeDifferFeature)
      (logitBridgeModel.surface Real.sigmoid 0 false)
      (logitBridgeModel.surface Real.sigmoid 0 true) = Real.log 3 := by
    simp only [linkMarginal, hmap, hrisk, logitBridgeDifferTarget_covLaw, integral_dirac]
    rw [show ((logitBridgeDifferK true 1 : ℕ) : ℝ) / 20 = 3 / 4 by norm_num [logitBridgeDifferK],
      show ((logitBridgeDifferK false 1 : ℕ) : ℝ) / 20 = 1 / 2 by norm_num [logitBridgeDifferK],
      logit_half, logit_div (by norm_num) (by norm_num)]
    norm_num
  have hWv : linkMarginal logit ((commonLimitFollowUpTilted (logitBridgeTrial logitBridgeDifferK)
      logitBridgeDifferFeature 0).map logitBridgeDifferFeature)
      (logitBridgeModel.surface Real.sigmoid 0 false)
      (logitBridgeModel.surface Real.sigmoid 0 true) = Real.log (43 / 17) := by
    simp only [linkMarginal, hmap, hrisk, logitBridgeDiffer_integral_tilted]
    rw [show (((logitBridgeDifferK true 0 : ℕ) : ℝ) / 20 +
        ((logitBridgeDifferK true 1 : ℕ) : ℝ) / 20 +
        ((logitBridgeDifferK true 2 : ℕ) : ℝ) / 20) / 3 = 43 / 60 by
          norm_num [logitBridgeDifferK],
      show (((logitBridgeDifferK false 0 : ℕ) : ℝ) / 20 +
        ((logitBridgeDifferK false 1 : ℕ) : ℝ) / 20 +
        ((logitBridgeDifferK false 2 : ℕ) : ℝ) / 20) / 3 = 1 / 2 by
          norm_num [logitBridgeDifferK],
      logit_half, logit_div (by norm_num) (by norm_num)]
    norm_num
  refine ⟨hfit, hSv ▸ hS, hWv ▸ hW, htilt 0, ?_, ?_⟩
  · rw [logitBridgeDifferTarget_covLaw, integral_dirac]
    simp [logitBridgeDifferFeature]
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (by norm_num : (0 : ℝ) < 3))
      (Set.mem_Ioi.2 (by norm_num : (0 : ℝ) < 43 / 17)) h
    norm_num at this

/-! ### A two valued feature: the two limits agree -/

/-- The two valued feature `1[x = 2]`. -/
noncomputable def logitBridgeAgreeFeature (x : Fin 3) : Fin 1 → ℝ := fun _ => if x = 2 then 1 else 0

/-- The thresholds of the two valued example: `15, 15, 18` on the arm `true` and `10` on the
arm `false`, the risks `3/4, 3/4, 9/10` and `1/2`. -/
def logitBridgeAgreeK (e : Bool) (x : Fin 3) : ℕ := if e then ![15, 15, 18] x else 10

/-- The target feature mean `1/2` of the two valued example. -/
noncomputable def logitBridgeAgreeMean : Fin 1 → ℝ := fun _ => 1 / 2

theorem logitBridgeAgreeK_le (e : Bool) (x : Fin 3) : logitBridgeAgreeK e x ≤ 20 := by
  cases e <;> fin_cases x <;> simp [logitBridgeAgreeK]

theorem logitBridgeAgree_risk (e : Bool) (x : Fin 3) :
    (logitBridgeAgreeK e x : ℝ) / 20 =
      logitBridgeModel.surface Real.sigmoid 0 e (logitBridgeAgreeFeature x) := by
  rw [logitBridgeModel_surface]
  cases e <;> fin_cases x <;>
    norm_num [logitBridgeAgreeK, logitBridgeAgreeFeature, Real.sigmoid_zero, sigmoid_log_three,
      sigmoid_two_log_three]

theorem logitBridgeAgree_bound (x : Fin 3) :
    ‖logitBridgeAgreeFeature x - logitBridgeAgreeMean‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  fin_cases x <;> simp [logitBridgeAgreeFeature, logitBridgeAgreeMean] <;> norm_num

theorem logitBridgeAgree_margin : ∀ v : Fin 1 → ℝ, ‖v‖ = 1 → (1 / 3 : ℝ) ≤
    (logitBridgeTrial logitBridgeAgreeK).covLaw.real
      {x | 1 / 3 ≤ v ⬝ᵥ (logitBridgeAgreeFeature x - logitBridgeAgreeMean)} := by
  intro v hv
  rcases norm_fin_one_eq hv with h | h
  · refine (logitBridgeTrial_real_singleton _ 2).symm.le.trans
      (measureReal_mono (fun x hx => ?_) (measure_ne_top _ _))
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, logitBridgeAgreeFeature, logitBridgeAgreeMean]
    norm_num
  · refine (logitBridgeTrial_real_singleton _ 0).symm.le.trans
      (measureReal_mono (fun x hx => ?_) (measure_ne_top _ _))
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [dotProduct, h, logitBridgeAgreeFeature, logitBridgeAgreeMean]
    norm_num

theorem logitBridgeAgree_law :
    (logitBridgeTrial logitBridgeAgreeK).μ.map (fun ω =>
        (((logitBridgeTrial logitBridgeAgreeK).X ω, (logitBridgeTrial logitBridgeAgreeK).A ω),
        (logitBridgeTrial logitBridgeAgreeK).obsOutcome ω)) =
      (glmFamily logisticKernel ((logitBridgeTrial logitBridgeAgreeK).μ.map fun ω =>
          ((logitBridgeTrial logitBridgeAgreeK).X ω, (logitBridgeTrial logitBridgeAgreeK).A ω))
        (fun q => featureInteractionDesign logitBridgeAgreeFeature q.2 q.1)
        (measurable_featureInteractionDesign_pair (measurable_of_finite _))).law
        (logitBridgeModel.ipdCoef 0 true false) :=
  logitBridgeTrial_law _ _ _ _ _ (by norm_num) logitBridgeAgree_margin logitBridgeAgreeK_le
    fun e x => by
      rw [logitBridgeAgree_risk, MultilevelModel.sigmoid_featureInteractionDesign_ipdCoef]
      cases e <;> rfl

/-- The target covariate law `(1/4, 1/4, 1/2)` of the two valued example. -/
noncomputable def logitBridgeAgreeCovLaw : Measure (Fin 3) := stratumLaw ![1 / 4, 1 / 4, 1 / 2]

theorem logitBridgeAgreeCovLaw_nonneg (v : Fin 3) : (0 : ℝ) ≤ ![1 / 4, 1 / 4, 1 / 2] v := by
  fin_cases v <;> norm_num

instance : IsProbabilityMeasure logitBridgeAgreeCovLaw :=
  isProbabilityMeasure_stratumLaw ⟨logitBridgeAgreeCovLaw_nonneg, by
    rw [Fin.sum_univ_three]; norm_num⟩

theorem integral_logitBridgeAgreeCovLaw (f : Fin 3 → ℝ) :
    ∫ x, f x ∂logitBridgeAgreeCovLaw = f 0 / 4 + f 1 / 4 + f 2 / 2 := by
  rw [logitBridgeAgreeCovLaw, integral_stratumLaw logitBridgeAgreeCovLaw_nonneg, standardizedRisk,
    Fin.sum_univ_three]
  simp
  ring

/-- The target of the two valued example: covariate law `(1/4, 1/4, 1/2)`, and the potential
outcome `Y(e) = 1[U < k(e, X)]` of the trial thresholds, for a uniform noise `U` independent of
the covariate. -/
noncomputable def logitBridgeAgreeTarget : Population (Fin 3 × Fin 20) (Fin 3) Bool where
  μ := logitBridgeAgreeCovLaw.prod logitBridgeNoise
  X ω := ω.1
  Y e ω := logitBridgeOutcome (logitBridgeAgreeK e ω.1) ω.2

instance : IsProbabilityMeasure logitBridgeAgreeTarget.μ := by
  unfold logitBridgeAgreeTarget; infer_instance

theorem logitBridgeAgreeTarget_covLaw : logitBridgeAgreeTarget.covLaw = logitBridgeAgreeCovLaw := by
  change (logitBridgeAgreeCovLaw.prod logitBridgeNoise).map Prod.fst = _
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The conditional risks of the target are the multilevel surfaces at the trial baseline `0`. -/
theorem logitBridgeAgreeTarget_isCondMean (e : Bool) :
    logitBridgeAgreeTarget.IsCondMean e fun x =>
      logitBridgeModel.surface Real.sigmoid 0 e (logitBridgeAgreeFeature x) := by
  refine ⟨measurable_of_finite _, ?_⟩
  refine (condExp_prod_comp_fst (ρ := logitBridgeAgreeCovLaw) (τ := logitBridgeNoise)
    (W := id) measurable_id (F := fun ω => logitBridgeOutcome (logitBridgeAgreeK e ω.1) ω.2)
    Integrable.of_finite (φ := fun x =>
      logitBridgeModel.surface Real.sigmoid 0 e (logitBridgeAgreeFeature x))
    (measurable_of_finite _) fun x => ?_).symm
  rw [integral_logitBridgeOutcome (logitBridgeAgreeK_le e x), logitBridgeAgree_risk]
  rfl

/-- **The two limits agree, and they are the target marginal log odds ratio.** In the two valued
example every hypothesis of `MultilevelModel.commonLimit_logit_of_affine` holds with `a = true`,
`c = false`, `t = 1/2`, `δ = 1/3`, `B = 1` and the fit over the closed ball of radius `4`: the
risks `3/4 + (3/20) u` and `1/2` are affine in the feature `u`. The standardized marginal log odds
ratio and the weighted log odds ratio both converge in probability to `log (33/7)`, and their
difference to `0`. The target follows the multilevel model at the trial baseline, so every
hypothesis of `MultilevelModel.commonLimit_logit_marginalEffect` holds too: the standardized limit
is the target marginal log odds ratio, which is `log (33/7)`. -/
theorem logitBridgeAgree_limits :
    TendstoInMeasure (logitBridgeSampleLaw logitBridgeAgreeK) (fun n ω =>
        linkMarginal logit logitBridgeAgreeTarget.covLaw
          (fun x => Real.sigmoid (featureInteractionDesign logitBridgeAgreeFeature false x ⬝ᵥ
            glmMLE logisticDens (fun q => featureInteractionDesign logitBridgeAgreeFeature q.2 q.1)
              (Metric.closedBall 0 4) (logitBridgeSample logitBridgeAgreeK) n ω))
          (fun x => Real.sigmoid (featureInteractionDesign logitBridgeAgreeFeature true x ⬝ᵥ
            glmMLE logisticDens (fun q => featureInteractionDesign logitBridgeAgreeFeature q.2 q.1)
              (Metric.closedBall 0 4) (logitBridgeSample logitBridgeAgreeK) n ω)))
      atTop (fun _ => Real.log (33 / 7)) ∧
    TendstoInMeasure (logitBridgeSampleLaw logitBridgeAgreeK) (fun n ω =>
        logit (sampleBalancedArmMean logitBridgeAgreeFeature logitBridgeAgreeMean
          (fun i ω => commonLimitReassoc (logitBridgeSample logitBridgeAgreeK i ω)) true n ω) -
        logit (sampleBalancedArmMean logitBridgeAgreeFeature logitBridgeAgreeMean
          (fun i ω => commonLimitReassoc (logitBridgeSample logitBridgeAgreeK i ω)) false n ω))
      atTop (fun _ => Real.log (33 / 7)) ∧
    TendstoInMeasure (logitBridgeSampleLaw logitBridgeAgreeK) (fun n ω =>
        linkMarginal logit logitBridgeAgreeTarget.covLaw
          (fun x => Real.sigmoid (featureInteractionDesign logitBridgeAgreeFeature false x ⬝ᵥ
            glmMLE logisticDens (fun q => featureInteractionDesign logitBridgeAgreeFeature q.2 q.1)
              (Metric.closedBall 0 4) (logitBridgeSample logitBridgeAgreeK) n ω))
          (fun x => Real.sigmoid (featureInteractionDesign logitBridgeAgreeFeature true x ⬝ᵥ
            glmMLE logisticDens (fun q => featureInteractionDesign logitBridgeAgreeFeature q.2 q.1)
              (Metric.closedBall 0 4) (logitBridgeSample logitBridgeAgreeK) n ω)) -
        (logit (sampleBalancedArmMean logitBridgeAgreeFeature logitBridgeAgreeMean
          (fun i ω => commonLimitReassoc (logitBridgeSample logitBridgeAgreeK i ω)) true n ω) -
        logit (sampleBalancedArmMean logitBridgeAgreeFeature logitBridgeAgreeMean
          (fun i ω => commonLimitReassoc (logitBridgeSample logitBridgeAgreeK i ω)) false n ω)))
      atTop (fun _ => 0) ∧
    logitBridgeAgreeTarget.marginalEffect logit false true = Real.log (33 / 7) := by
  have hT := logitBridgeTrial_isRandomizedTwoArm logitBridgeAgreeK
  have hξ : logitBridgeModel.ipdCoef 0 true false ∈
      (Metric.closedBall 0 4 : Set (Option (Fin 1) ⊕ Option (Fin 1) → ℝ)) := by
    have h3 : Real.log 3 ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
    have h0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num)]
    rintro (o | o) <;> rcases o with _ | _ <;>
      simp [MultilevelModel.ipdCoef, logitBridgeModel, abs_of_nonneg h0, h3]
  have hX : Measurable logitBridgeAgreeTarget.X := measurable_fst
  have ht : ∀ j, ∫ x, logitBridgeAgreeFeature x j ∂logitBridgeAgreeTarget.covLaw =
      logitBridgeAgreeMean j := fun j => by
    rw [logitBridgeAgreeTarget_covLaw, integral_logitBridgeAgreeCovLaw]
    simp [logitBridgeAgreeFeature, logitBridgeAgreeMean]
  have haff : ∀ (e : Bool) (x : Fin 3),
      logitBridgeModel.surface Real.sigmoid 0 (if e then true else false)
          (logitBridgeAgreeFeature x) =
        (fun e : Bool => if e then (3 / 4 : ℝ) else 1 / 2) e +
          (fun (e : Bool) (_ : Fin 1) => if e then (3 / 20 : ℝ) else 0) e ⬝ᵥ
            logitBridgeAgreeFeature x := fun e x => by
    rw [show (if e then true else false) = e by cases e <;> rfl, ← logitBridgeAgree_risk]
    cases e <;> fin_cases x <;>
      simp [logitBridgeAgreeK, logitBridgeAgreeFeature, dotProduct] <;> norm_num
  obtain ⟨hS, hW, hD, hval⟩ := logitBridgeModel.commonLimit_logit_of_affine hT
    (measurable_of_finite _) logitBridgeAgree_bound (by norm_num : (0 : ℝ) < 1 / 3)
    logitBridgeAgree_margin logitBridgeAgree_law (isCompact_closedBall _ _) hξ
    (isIIDSample_logitBridgeSample _) (measurable_logitBridgeSample _) (map_logitBridgeSample _ 0)
    hX ht haff
  have hS' := logitBridgeModel.commonLimit_logit_marginalEffect hT
    (measurable_of_finite _) logitBridgeAgree_bound (by norm_num : (0 : ℝ) < 1 / 3)
    logitBridgeAgree_margin logitBridgeAgree_law (isCompact_closedBall _ _) hξ
    (isIIDSample_logitBridgeSample _) (measurable_logitBridgeSample _) (map_logitBridgeSample _ 0)
    hX Integrable.of_finite Integrable.of_finite (logitBridgeAgreeTarget_isCondMean true)
    (logitBridgeAgreeTarget_isCondMean false)
  have hv : logit ((fun e : Bool => if e then (3 / 4 : ℝ) else 1 / 2) true +
        (fun (e : Bool) (_ : Fin 1) => if e then (3 / 20 : ℝ) else 0) true ⬝ᵥ
          logitBridgeAgreeMean) -
      logit ((fun e : Bool => if e then (3 / 4 : ℝ) else 1 / 2) false +
        (fun (e : Bool) (_ : Fin 1) => if e then (3 / 20 : ℝ) else 0) false ⬝ᵥ
          logitBridgeAgreeMean) = Real.log (33 / 7) := by
    rw [show (fun e : Bool => if e then (3 / 4 : ℝ) else 1 / 2) true +
        (fun (e : Bool) (_ : Fin 1) => if e then (3 / 20 : ℝ) else 0) true ⬝ᵥ
          logitBridgeAgreeMean = 33 / 40 by norm_num [dotProduct, logitBridgeAgreeMean],
      show (fun e : Bool => if e then (3 / 4 : ℝ) else 1 / 2) false +
        (fun (e : Bool) (_ : Fin 1) => if e then (3 / 20 : ℝ) else 0) false ⬝ᵥ
          logitBridgeAgreeMean = 1 / 2 by norm_num [dotProduct, logitBridgeAgreeMean],
      logit_half, logit_div (by norm_num) (by norm_num)]
    norm_num
  rw [hv] at hval
  rw [hval] at hS hW
  refine ⟨hS, hW, hD, ?_⟩
  exact tendstoInMeasure_const_unique hS' hS

end NetworkMetaRegression

end CausalInference
