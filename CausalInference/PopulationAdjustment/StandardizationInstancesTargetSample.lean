/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyTargetSample
public import CausalInference.PopulationAdjustment.StandardizationInstancesAnchored

/-!
# Standardization by a target sample average: every hypothesis verified

The target sample form of standardization averages the fitted surface over a sample of target
covariates instead of integrating it against the target covariate law. This file builds a space
that carries two independent i.i.d. sequences, the units of the trial and the units of the
target, and verifies every hypothesis of the target sample theorems in two models.

* **Two independent samples** (`independentSamplesLaw ν₁ ν₂`): the product of the two infinite
  product laws on `(ℕ → Ω₁) × (ℕ → Ω₂)`. Any measurable transformation of the coordinates of
  either factor is an i.i.d. sample (`isIIDSample_independentSamplesLaw_fst`,
  `isIIDSample_independentSamplesLaw_snd`) and the two sequences are independent
  (`indepFun_independentSamplesLaw`). The pullback of an i.i.d. sample along a measurable map is
  an i.i.d. sample (`isIIDSample_comp_of_map`).
* **Least squares**: the trial `lsExampleTrial` with its linear outcome model, the target
  `anchoredInstTarget` and its covariate draws. The target sample average of the fitted arm
  `true` converges to `E_Q[Y(a)] = 3/2` (`targetSampleInst_leastSquares_armMean`), the
  unanchored comparison to `-1/4` (`targetSampleInst_leastSquares_unanchored`) and the anchored
  comparison to `-1/4` (`targetSampleInst_leastSquares_anchored`).
* **Logistic regression**: the trial `logisticInstTrial` with its logistic outcome model, the
  target `logisticInstTarget` and its covariate draws. The target sample average of the fitted
  risk of arm `true` converges to `5/12` (`targetSampleInst_logistic_fit`,
  `targetSampleInst_logistic_armMean`), the unanchored and anchored comparisons on the logit
  scale to `log (14/5)` (`targetSampleInst_logistic_unanchored`,
  `targetSampleInst_logistic_anchored`).

In every instance the number of target draws used at stage `n` is `n`.

## Main definitions

* `independentSamplesLaw`, `targetSampleInstLSRecord`, `targetSampleInstLSDraw`,
  `targetSampleInstLSFit`, `targetSampleInstLogRecord`, `targetSampleInstLogDraw`,
  `targetSampleInstLogFit`.

## Main results

* `isIIDSample_comp_of_map`, `isIIDSample_infinitePi_comp`,
  `isIIDSample_independentSamplesLaw_fst`, `isIIDSample_independentSamplesLaw_snd`,
  `indepFun_independentSamplesLaw`.
* `targetSampleInst_leastSquares_armMean`, `targetSampleInst_leastSquares_unanchored`,
  `targetSampleInst_leastSquares_anchored`, `targetSampleInst_logistic_fit`,
  `targetSampleInst_logistic_armMean`, `targetSampleInst_logistic_unanchored`,
  `targetSampleInst_logistic_anchored`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### Two independent i.i.d. sequences -/

section General

variable {Ω Ω' 𝒪 : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace 𝒪]

/-- **An i.i.d. sample pulls back along a measurable map**: if `O` is an i.i.d. sample under the
image measure `μ ∘ e⁻¹`, then `O ∘ e` is an i.i.d. sample under `μ`. -/
theorem isIIDSample_comp_of_map {O : ℕ → Ω → 𝒪} (hOm : ∀ i, Measurable (O i)) {e : Ω' → Ω}
    (he : Measurable e) {μ : Measure Ω'} [IsProbabilityMeasure μ]
    (h : IsIIDSample O (μ.map e)) : IsIIDSample (fun i => O i ∘ e) μ where
  indep := by
    have hm := h.indep
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => (hOm i).aemeasurable)] at hm
    rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' (fun i => ((hOm i).comp he).aemeasurable)]
    have e1 : (fun ω i => (O i ∘ e) ω) = (fun ω i => O i ω) ∘ e := rfl
    rw [e1, ← Measure.map_map (measurable_pi_iff.2 hOm) he, hm]
    congr 1
    funext i
    rw [Measure.map_map (hOm i) he]
  ident i := ⟨((hOm i).comp he).aemeasurable, ((hOm 0).comp he).aemeasurable, by
    rw [← Measure.map_map (hOm i) he, ← Measure.map_map (hOm 0) he]
    exact (h.ident i).map_eq⟩

/-- The law of a measurable transformation of a coordinate of an infinite product. -/
theorem map_infinitePi_comp_eval (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → 𝒪}
    (hf : Measurable f) (i : ℕ) :
    (Measure.infinitePi fun _ : ℕ => ν).map (fun ω => f (ω i)) = ν.map f := by
  have : (fun ω : ℕ → Ω => f (ω i)) = f ∘ fun ω => ω i := rfl
  rw [this, ← Measure.map_map hf (measurable_pi_apply i), Measure.infinitePi_map_eval]

/-- **The coordinates of an infinite product, transformed, are an i.i.d. sample.** -/
theorem isIIDSample_infinitePi_comp (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → 𝒪}
    (hf : Measurable f) :
    IsIIDSample (fun i (ω : ℕ → Ω) => f (ω i)) (Measure.infinitePi fun _ => ν) where
  indep := iIndepFun_infinitePi (P := fun _ => ν) fun _ => hf
  ident i := ⟨(hf.comp (measurable_pi_apply i)).aemeasurable,
    (hf.comp (measurable_pi_apply 0)).aemeasurable,
    (map_infinitePi_comp_eval ν hf i).trans (map_infinitePi_comp_eval ν hf 0).symm⟩

/-- The law of two independent i.i.d. sequences, with laws `ν₁` and `ν₂`, on
`(ℕ → Ω) × (ℕ → Ω')`. -/
noncomputable def independentSamplesLaw (ν₁ : Measure Ω) (ν₂ : Measure Ω') :
    Measure ((ℕ → Ω) × (ℕ → Ω')) :=
  (Measure.infinitePi fun _ => ν₁).prod (Measure.infinitePi fun _ => ν₂)

variable (ν₁ : Measure Ω) (ν₂ : Measure Ω') [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]

instance : IsProbabilityMeasure (independentSamplesLaw ν₁ ν₂) := by
  unfold independentSamplesLaw; infer_instance

/-- **The first sequence of two independent samples, transformed, is an i.i.d. sample.** -/
theorem isIIDSample_independentSamplesLaw_fst {f : Ω → 𝒪} (hf : Measurable f) :
    IsIIDSample (fun i (ω : (ℕ → Ω) × (ℕ → Ω')) => f (ω.1 i)) (independentSamplesLaw ν₁ ν₂) := by
  refine isIIDSample_comp_of_map (O := fun i (ω : ℕ → Ω) => f (ω i))
    (fun i => hf.comp (measurable_pi_apply i)) measurable_fst ?_
  rw [independentSamplesLaw, Measure.map_fst_prod, measure_univ, one_smul]
  exact isIIDSample_infinitePi_comp ν₁ hf

/-- **The second sequence of two independent samples, transformed, is an i.i.d. sample.** -/
theorem isIIDSample_independentSamplesLaw_snd {f : Ω' → 𝒪} (hf : Measurable f) :
    IsIIDSample (fun i (ω : (ℕ → Ω) × (ℕ → Ω')) => f (ω.2 i)) (independentSamplesLaw ν₁ ν₂) := by
  refine isIIDSample_comp_of_map (O := fun i (ω : ℕ → Ω') => f (ω i))
    (fun i => hf.comp (measurable_pi_apply i)) measurable_snd ?_
  rw [independentSamplesLaw, Measure.map_snd_prod, measure_univ, one_smul]
  exact isIIDSample_infinitePi_comp ν₂ hf

/-- The law of a transformed observation of the first sequence. -/
theorem map_independentSamplesLaw_fst {f : Ω → 𝒪} (hf : Measurable f) (i : ℕ) :
    (independentSamplesLaw ν₁ ν₂).map (fun ω => f (ω.1 i)) = ν₁.map f := by
  have : (fun ω : (ℕ → Ω) × (ℕ → Ω') => f (ω.1 i)) =
      (f ∘ fun ω : ℕ → Ω => ω i) ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map (hf.comp (measurable_pi_apply i)) measurable_fst]
  rw [independentSamplesLaw, Measure.map_fst_prod, measure_univ, one_smul]
  exact map_infinitePi_comp_eval ν₁ hf i

/-- The law of a transformed observation of the second sequence. -/
theorem map_independentSamplesLaw_snd {f : Ω' → 𝒪} (hf : Measurable f) (i : ℕ) :
    (independentSamplesLaw ν₁ ν₂).map (fun ω => f (ω.2 i)) = ν₂.map f := by
  have : (fun ω : (ℕ → Ω) × (ℕ → Ω') => f (ω.2 i)) =
      (f ∘ fun ω : ℕ → Ω' => ω i) ∘ Prod.snd := rfl
  rw [this, ← Measure.map_map (hf.comp (measurable_pi_apply i)) measurable_snd]
  rw [independentSamplesLaw, Measure.map_snd_prod, measure_univ, one_smul]
  exact map_infinitePi_comp_eval ν₂ hf i

/-- **The two sequences are independent.** -/
theorem indepFun_independentSamplesLaw :
    IndepFun (fun ω : (ℕ → Ω) × (ℕ → Ω') => ω.1) (fun ω => ω.2)
      (independentSamplesLaw ν₁ ν₂) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

end General

theorem tendsto_id_nat : Tendsto (fun n : ℕ => n) atTop atTop := tendsto_id

/-! ### Least squares -/

/-- The trial records of the least squares instance on the space of two samples. -/
noncomputable def targetSampleInstLSRecord (i : ℕ) (ω : (ℕ → Bool × Bool) × (ℕ → Bool)) :
    Bool × Bool × ℝ :=
  lsExampleRecord (ω.1 i)

/-- The target covariate draws of the least squares instance. -/
def targetSampleInstLSDraw (i : ℕ) (ω : (ℕ → Bool × Bool) × (ℕ → Bool)) : Bool := ω.2 i

/-- The least squares fit of the least squares instance. -/
noncomputable def targetSampleInstLSFit (n : ℕ) (ω : (ℕ → Bool × Bool) × (ℕ → Bool)) :
    Fin 4 → ℝ :=
  leastSquaresFit (recordDesign lsExampleDesign) recordResponse targetSampleInstLSRecord n ω

/-- The law of the two samples of the least squares instance. -/
noncomputable abbrev targetSampleInstLSLaw : Measure ((ℕ → Bool × Bool) × (ℕ → Bool)) :=
  independentSamplesLaw lsExampleTrial.μ anchoredInstTarget.μ

theorem isIIDSample_targetSampleInstLSRecord :
    IsIIDSample targetSampleInstLSRecord targetSampleInstLSLaw :=
  isIIDSample_independentSamplesLaw_fst _ _ (measurable_of_finite lsExampleRecord)

theorem map_targetSampleInstLSRecord :
    targetSampleInstLSLaw.map (targetSampleInstLSRecord 0) = lsExampleTrial.ipdLaw :=
  map_independentSamplesLaw_fst _ _ (measurable_of_finite lsExampleRecord) 0

theorem isIIDSample_targetSampleInstLSDraw :
    IsIIDSample targetSampleInstLSDraw targetSampleInstLSLaw :=
  isIIDSample_independentSamplesLaw_snd _ _ measurable_id

theorem map_targetSampleInstLSDraw :
    targetSampleInstLSLaw.map (targetSampleInstLSDraw 0) = anchoredInstTarget.covLaw :=
  map_independentSamplesLaw_snd _ _ measurable_id 0

/-- **The target sample average of the least squares fit is consistent for the target arm
mean.** The average `n⁻¹ ∑_{i < n} z(true, X'_i)ᵀξ̂_n` over the target draws converges in
probability to `E_Q[Y(a)] = 3/2`. Every hypothesis of
`tendstoInMeasure_sampleMean_leastSquares_armMean` is verified. -/
theorem targetSampleInst_leastSquares_armMean :
    TendstoInMeasure targetSampleInstLSLaw
      (fun n ω => sampleMean (fun x => lsExampleDesign true x ⬝ᵥ targetSampleInstLSFit n ω)
        targetSampleInstLSDraw n ω) atTop (fun _ => 3 / 2) := by
  rw [← anchoredInstTarget_armMean.1]
  exact tendstoInMeasure_sampleMean_leastSquares_armMean (s := 0)
    lsExampleTrial_isRandomizedTwoArm lsExample_linearOutcomeModel
    isIIDSample_targetSampleInstLSRecord map_targetSampleInstLSRecord measurable_id
    Integrable.of_finite (anchoredInst_structurallyInvariant true 0 rfl)
    anchoredInst_absolutelyContinuous (fun _ => Integrable.of_finite)
    isIIDSample_targetSampleInstLSDraw map_targetSampleInstLSDraw tendsto_id_nat

/-- **The unanchored comparison with a target sample average of the least squares fit is
consistent.** With the reported target mean `5/4 + 1/(n + 1)` of `b`, a deterministic sequence
converging to `E_Q[Y(b)] = 5/4`, the estimator `m̂_b - n⁻¹ ∑_{i < n} z(true, X'_i)ᵀξ̂_n`
converges in probability to `-1/4`. Every hypothesis of
`tendstoInMeasure_sampleMean_fit_unanchored` is verified for the linear surface on the unit ball
around `ξ₀`. -/
theorem targetSampleInst_leastSquares_unanchored :
    TendstoInMeasure targetSampleInstLSLaw
      (fun (n : ℕ) ω => (5 / 4 + 1 / ((n : ℝ) + 1)) -
        sampleMean (fun x => lsExampleDesign true x ⬝ᵥ targetSampleInstLSFit n ω)
          targetSampleInstLSDraw n ω) atTop (fun _ => -1 / 4) := by
  obtain ⟨h0, h1, -⟩ := anchoredInstTarget_armMean
  have hlim : anchoredInstTarget.marginalEffect id 0 1 = -1 / 4 := by
    simp only [Population.marginalEffect, id, h0, h1]; norm_num
  have hmb : TendstoInMeasure targetSampleInstLSLaw
      (fun (n : ℕ) (_ : (ℕ → Bool × Bool) × (ℕ → Bool)) => 5 / 4 + 1 / ((n : ℝ) + 1)) atTop
      (fun _ => anchoredInstTarget.armMean 1) := by
    rw [h1]; exact tendstoInMeasure_add_one_div_succ _ _
  have hr := linearSurface_regular_ball (z := lsExampleDesign true)
    (fun _ => measurable_of_finite _) (ν := anchoredInstTarget.covLaw)
    (fun _ => Integrable.of_finite) lsExampleCoef
  rw [← hlim]
  have h := tendstoInMeasure_sampleMean_fit_unanchored
    (hθf := fun ξ t x => lsExampleDesign t x ⬝ᵥ ξ) (θh := targetSampleInstLSFit)
    (θ₀ := lsExampleCoef) (U := Metric.ball lsExampleCoef 1)
    (H := fun x => (‖lsExampleCoef‖ + 1) * ∑ j, |lsExampleDesign true x j|)
    (mb := fun (n : ℕ) _ => 5 / 4 + 1 / ((n : ℝ) + 1))
    (Xs := targetSampleInstLSDraw) (m := fun n => n)
    (t := true) (a := 0) (b := 1) (g := id) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel.integrable_Y lsExample_linearOutcomeModel.isOutcomeRegression
    measurable_id Integrable.of_finite (anchoredInst_structurallyInvariant true 0 rfl)
    anchoredInst_absolutelyContinuous (Metric.ball_mem_nhds lsExampleCoef one_pos)
    (fun ξ _ => hr.1 ξ) hr.2.1 hr.2.2.1 hr.2.2.2
    (lsExample_linearOutcomeModel.tendstoInMeasure lsExampleTrial_isRandomizedTwoArm
      isIIDSample_targetSampleInstLSRecord map_targetSampleInstLSRecord)
    isIIDSample_targetSampleInstLSDraw map_targetSampleInstLSDraw tendsto_id_nat hmb
    continuousAt_id continuousAt_id
  exact h

/-- **The anchored comparison with a target sample average of the least squares fit is
consistent.** Both fitted arms are averaged over the target draws; with the reported contrast
`-1 + 1/(n + 1)` of `c` against `b` the anchored estimator converges in probability to the
target effect `-1/4` of `b` relative to `a`. Every hypothesis of
`tendstoInMeasure_sampleMean_leastSquares_anchored` is verified. -/
theorem targetSampleInst_leastSquares_anchored :
    TendstoInMeasure targetSampleInstLSLaw
      (fun (n : ℕ) ω =>
        sampleMean (fun x => lsExampleDesign false x ⬝ᵥ targetSampleInstLSFit n ω)
            targetSampleInstLSDraw n ω -
          sampleMean (fun x => lsExampleDesign true x ⬝ᵥ targetSampleInstLSFit n ω)
            targetSampleInstLSDraw n ω - (-1 + 1 / ((n : ℝ) + 1)))
      atTop (fun _ => -1 / 4) := by
  obtain ⟨h0, h1, h2⟩ := anchoredInstTarget_armMean
  have hlim : anchoredInstTarget.marginalEffect id 0 1 = -1 / 4 := by
    simp only [Population.marginalEffect, id, h0, h1]; norm_num
  have hd : TendstoInMeasure targetSampleInstLSLaw
      (fun (n : ℕ) (_ : (ℕ → Bool × Bool) × (ℕ → Bool)) => -1 + 1 / ((n : ℝ) + 1)) atTop
      (fun _ => anchoredInstTarget.marginalEffect id 1 2) := by
    have : anchoredInstTarget.marginalEffect id 1 2 = -1 := by
      simp only [Population.marginalEffect, id, h1, h2]; norm_num
    rw [this]; exact tendstoInMeasure_add_one_div_succ _ _
  rw [← hlim]
  have h := tendstoInMeasure_sampleMean_leastSquares_anchored (ta := true) (tc := false)
    (a := 0) (b := 1) (c := 2) (g := id) (Xs := targetSampleInstLSDraw) (m := fun n => n)
    (O := targetSampleInstLSRecord)
    (dbc := fun (n : ℕ) _ => -1 + 1 / ((n : ℝ) + 1)) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel
    isIIDSample_targetSampleInstLSRecord map_targetSampleInstLSRecord measurable_id
    Integrable.of_finite Integrable.of_finite (anchoredInst_structurallyInvariant true 0 rfl)
    (anchoredInst_structurallyInvariant false 2 rfl) anchoredInst_absolutelyContinuous
    (fun _ _ => Integrable.of_finite) isIIDSample_targetSampleInstLSDraw
    map_targetSampleInstLSDraw tendsto_id_nat hd continuousAt_id continuousAt_id
  exact h

/-! ### Logistic regression -/

/-- The trial records of the logistic instance on the space of two samples. -/
noncomputable def targetSampleInstLogRecord (i : ℕ)
    (ω : (ℕ → (Bool × Bool) × Fin 3) × (ℕ → Bool × Fin 3)) : ((Fin 1 → ℝ) × Bool) × ℝ :=
  logisticInstRecord (ω.1 i)

/-- The target covariate draws of the logistic instance. -/
noncomputable def targetSampleInstLogDraw (i : ℕ)
    (ω : (ℕ → (Bool × Bool) × Fin 3) × (ℕ → Bool × Fin 3)) : Fin 1 → ℝ :=
  logisticInstTarget.X (ω.2 i)

/-- The logistic maximum likelihood fit of the logistic instance. -/
noncomputable def targetSampleInstLogFit (n : ℕ)
    (ω : (ℕ → (Bool × Bool) × Fin 3) × (ℕ → Bool × Fin 3)) :
    Option (Fin 1) ⊕ Option (Fin 1) → ℝ :=
  glmMLE logisticDens (fun c => interactionDesign c.2 c.1) logisticInstBall
    targetSampleInstLogRecord n ω

/-- The law of the two samples of the logistic instance. -/
noncomputable abbrev targetSampleInstLogLaw :
    Measure ((ℕ → (Bool × Bool) × Fin 3) × (ℕ → Bool × Fin 3)) :=
  independentSamplesLaw logisticInstTrial.μ logisticInstTarget.μ

theorem isIIDSample_targetSampleInstLogRecord :
    IsIIDSample targetSampleInstLogRecord targetSampleInstLogLaw :=
  isIIDSample_independentSamplesLaw_fst _ _ (measurable_of_finite logisticInstRecord)

theorem map_targetSampleInstLogRecord :
    targetSampleInstLogLaw.map (targetSampleInstLogRecord 0) =
      logisticInstTrial.μ.map logisticInstRecord :=
  map_independentSamplesLaw_fst _ _ (measurable_of_finite logisticInstRecord) 0

theorem isIIDSample_targetSampleInstLogDraw :
    IsIIDSample targetSampleInstLogDraw targetSampleInstLogLaw :=
  isIIDSample_independentSamplesLaw_snd _ _ (measurable_of_finite _)

theorem map_targetSampleInstLogDraw :
    targetSampleInstLogLaw.map (targetSampleInstLogDraw 0) = logisticInstTarget.covLaw :=
  map_independentSamplesLaw_snd _ _ (measurable_of_finite _) 0

theorem targetSampleInstLogFit_tendstoInMeasure :
    TendstoInMeasure targetSampleInstLogLaw targetSampleInstLogFit atTop
      (fun _ => logisticInstCoef) :=
  logisticInst_logisticOutcomeModel.tendstoInMeasure logisticInstTrial_isRandomizedTwoArm
    (isCompact_closedBall _ _) logisticInstCoef_mem_ball isIIDSample_targetSampleInstLogRecord
    map_targetSampleInstLogRecord

/-- The regularity of the logistic surface of arm `t` under the target covariate law. -/
theorem targetSampleInst_logistic_regular (t : Bool) :
    (∀ ξ ∈ (Set.univ : Set (Option (Fin 1) ⊕ Option (Fin 1) → ℝ)),
        Measurable (logisticInstFitSurface ξ t)) ∧
      (∀ᵐ x ∂logisticInstTarget.covLaw,
        ContinuousOn (fun ξ => logisticInstFitSurface ξ t x) Set.univ) ∧
      Integrable (fun _ => (1 : ℝ)) logisticInstTarget.covLaw ∧
      ∀ᵐ x ∂logisticInstTarget.covLaw,
        ∀ ξ ∈ (Set.univ : Set (Option (Fin 1) ⊕ Option (Fin 1) → ℝ)),
          |logisticInstFitSurface ξ t x| ≤ 1 := by
  have hr := logisticSurface_regular (z := fun c => interactionDesign c.2 c.1)
    logisticInst_logisticOutcomeModel.measurable_z t logisticInstTarget.covLaw
  exact ⟨fun ξ _ => hr.1 ξ, ae_of_all _ fun x => (hr.2.2.2 x).continuousOn, hr.2.1,
    ae_of_all _ fun x ξ _ => hr.2.2.1 ξ x⟩

/-- **The target sample average of the fitted logistic risk converges to its standardized
limit.** The average `n⁻¹ ∑_{i < n} σ(z(X'_i, true)ᵀξ̂_n)` over the target draws converges in
probability to `∫ σ(z(x, true)ᵀξ₀) dQ_X = 2/3 · 1/4 + 1/3 · 3/4 = 5/12`. Every hypothesis of
`tendstoInMeasure_sampleMean_fit` is verified. -/
theorem targetSampleInst_logistic_fit :
    TendstoInMeasure targetSampleInstLogLaw
      (fun n ω => sampleMean (logisticInstFitSurface (targetSampleInstLogFit n ω) true)
        targetSampleInstLogDraw n ω) atTop (fun _ => 5 / 12) := by
  obtain ⟨hm, hc, hH, hd⟩ := targetSampleInst_logistic_regular true
  have hv : ∫ x, logisticInstFitSurface logisticInstCoef true x ∂logisticInstTarget.covLaw =
      5 / 12 := by
    rw [integral_logisticInstTarget_covLaw]
    simp only [logisticInstFitSurface, logisticInst_risk]
    norm_num
  rw [← hv]
  exact tendstoInMeasure_sampleMean_fit isIIDSample_targetSampleInstLogDraw
    map_targetSampleInstLogDraw tendsto_id_nat Filter.univ_mem hm hc hH hd
    targetSampleInstLogFit_tendstoInMeasure

/-- **The target sample average of the fitted logistic risk is consistent for the target arm
mean** `E_Q[Y(a)] = 5/12`. Every hypothesis of `tendstoInMeasure_sampleMean_fit_armMean` is
verified. -/
theorem targetSampleInst_logistic_armMean :
    TendstoInMeasure targetSampleInstLogLaw
      (fun n ω => sampleMean (logisticInstFitSurface (targetSampleInstLogFit n ω) true)
        targetSampleInstLogDraw n ω) atTop (fun _ => 5 / 12) := by
  obtain ⟨hm, hc, hH, hd⟩ := targetSampleInst_logistic_regular true
  rw [← logisticInstTarget_armMean.1]
  exact tendstoInMeasure_sampleMean_fit_armMean (hθf := logisticInstFitSurface) (s := 0)
    logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    logisticInst_isOutcomeRegression (measurable_of_finite _) Integrable.of_finite
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous Filter.univ_mem hm hc hH hd
    targetSampleInstLogFit_tendstoInMeasure isIIDSample_targetSampleInstLogDraw
    map_targetSampleInstLogDraw tendsto_id_nat

/-- **The unanchored logistic comparison with a target sample average is consistent.** With
the reported target mean `2/3 + 1/(n + 1)` of `b`, the estimator
`logit(m̂_b) - logit(n⁻¹ ∑_{i < n} σ(z(X'_i, true)ᵀξ̂_n))` converges in probability to
`log (14/5)`. Every hypothesis of `tendstoInMeasure_sampleMean_fit_unanchored` is verified. -/
theorem targetSampleInst_logistic_unanchored :
    TendstoInMeasure targetSampleInstLogLaw
      (fun (n : ℕ) ω => logit (2 / 3 + 1 / ((n : ℝ) + 1)) -
        logit (sampleMean (logisticInstFitSurface (targetSampleInstLogFit n ω) true)
          targetSampleInstLogDraw n ω)) atTop (fun _ => Real.log (14 / 5)) := by
  obtain ⟨hm, hc, hH, hd⟩ := targetSampleInst_logistic_regular true
  have hmb : TendstoInMeasure targetSampleInstLogLaw
      (fun (n : ℕ) (_ : (ℕ → (Bool × Bool) × Fin 3) × (ℕ → Bool × Fin 3)) =>
        2 / 3 + 1 / ((n : ℝ) + 1)) atTop (fun _ => logisticInstTarget.armMean 1) := by
    rw [logisticInstTarget_armMean.2.1]; exact tendstoInMeasure_add_one_div_succ _ _
  rw [← logisticInstTarget_marginalEffect.2.1]
  exact tendstoInMeasure_sampleMean_fit_unanchored (hθf := logisticInstFitSurface) (a := 0)
    (b := 1) logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    logisticInst_isOutcomeRegression (measurable_of_finite _) Integrable.of_finite
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous Filter.univ_mem hm hc hH hd
    targetSampleInstLogFit_tendstoInMeasure isIIDSample_targetSampleInstLogDraw
    map_targetSampleInstLogDraw tendsto_id_nat hmb (logisticInst_continuousAt_logit 0)
    (logisticInst_continuousAt_logit 1)

/-- **The anchored logistic comparison with a target sample average is consistent.** Both fitted
risks are averaged over the target draws; with the reported contrast `log (7/10) + 1/(n + 1)` of
`c` against `b` the anchored estimator converges in probability to the target marginal log odds
ratio `log (14/5)` of `b` against `a`. Every hypothesis of
`tendstoInMeasure_sampleMean_fit_anchored` is verified. -/
theorem targetSampleInst_logistic_anchored :
    TendstoInMeasure targetSampleInstLogLaw
      (fun (n : ℕ) ω =>
        logit (sampleMean (logisticInstFitSurface (targetSampleInstLogFit n ω) false)
            targetSampleInstLogDraw n ω) -
          logit (sampleMean (logisticInstFitSurface (targetSampleInstLogFit n ω) true)
            targetSampleInstLogDraw n ω) - (Real.log (7 / 10) + 1 / ((n : ℝ) + 1)))
      atTop (fun _ => Real.log (14 / 5)) := by
  have hd : TendstoInMeasure targetSampleInstLogLaw
      (fun (n : ℕ) (_ : (ℕ → (Bool × Bool) × Fin 3) × (ℕ → Bool × Fin 3)) =>
        Real.log (7 / 10) + 1 / ((n : ℝ) + 1)) atTop
      (fun _ => logisticInstTarget.marginalEffect logit 1 2) := by
    rw [logisticInstTarget_marginalEffect.2.2]; exact tendstoInMeasure_add_one_div_succ _ _
  rw [← logisticInstTarget_marginalEffect.2.1]
  exact tendstoInMeasure_sampleMean_fit_anchored (hθf := logisticInstFitSurface) (ta := true)
    (tc := false) (a := 0) (b := 1) (c := 2) logisticInstTrial_isRandomizedTwoArm
    (fun _ => Integrable.of_finite) logisticInst_isOutcomeRegression (measurable_of_finite _)
    Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    logisticInst_absolutelyContinuous Filter.univ_mem
    (fun t => (targetSampleInst_logistic_regular t).1)
    (fun t => (targetSampleInst_logistic_regular t).2.1)
    (fun t => (targetSampleInst_logistic_regular t).2.2.1)
    (fun t => (targetSampleInst_logistic_regular t).2.2.2)
    targetSampleInstLogFit_tendstoInMeasure isIIDSample_targetSampleInstLogDraw
    map_targetSampleInstLogDraw tendsto_id_nat hd (logisticInst_continuousAt_logit 0)
    (logisticInst_continuousAt_logit 2)

end PopulationAdjustment

end CausalInference
