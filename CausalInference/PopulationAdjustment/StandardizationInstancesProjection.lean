/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationInstancesTargetSample

/-!
# The least squares fit under a misspecified linear model: the projection limit

Without a correct model, the least squares fit converges to the coefficient of the linear
projection, `G⁻¹ E[d r]` (`tendstoInMeasure_leastSquaresFit`), and the standardized fit need not
converge to the target mean. This file gives a concrete instance.

* **The trial** (`projInstTrial`): a fair coin `A` and a covariate `X` uniform on three points
  with values `v = -1, 0, 1`, independent. The outcome is `Y(t) = v(X)² + 1[t]`, a quadratic in
  the covariate.
* **The working model** is linear, with design `d(t, x) = (1, v(x), 1[t])`; it is misspecified:
  no coefficient makes `d(t, x)ᵀξ` the regression `E[Y | X, A] = v(X)² + 1[A]`
  (`projInst_isOutcomeRegression`, `projInst_not_isOutcomeRegression`).
* **The projection limit**: the design second moment and the cross moment are
  `G = [[1, 0, 1/2], [0, 2/3, 0], [1/2, 0, 1/2]]` and `E[d Y] = (7/6, 0, 5/6)`, and the fit
  converges in probability to `β* = G⁻¹ E[d Y] = (2/3, 0, 1)` (`projInst_tendstoInMeasure`).
* **The target** (`projInstTarget`) puts probability `1/2` on each of the points with `v = 0` and
  `v = 1`. The standardized fit of arm `t` converges to `2/3 + 1[t]`
  (`projInst_standardized_tendsto`), while the target mean of `Y(t)` is `1/2 + 1[t]`
  (`projInstTarget_armMean`): the standardized limit misses the target mean by `1/6`
  (`projInst_standardized_ne_armMean`).

## Main definitions

* `projInstValue`, `projInstOutcome`, `projInstDesign`, `projInstTrial`, `projInstRecord`,
  `projInstSampleLaw`, `projInstSample`, `projInstCoef`, `projInstTarget`.

## Main results

* `projInst_isOutcomeRegression`, `projInst_not_isOutcomeRegression`,
  `projInst_gram`, `projInst_cross`, `projInst_tendstoInMeasure`,
  `projInst_standardized_tendsto`, `projInstTarget_armMean`, `projInst_standardized_ne_armMean`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The covariate value `v = -1, 0, 1` of the three points. -/
def projInstValue (u : Fin 3) : ℝ := (u : ℝ) - 1

/-- The potential outcome `Y(t) = v(x)² + 1[t]`. -/
noncomputable def projInstOutcome (t : Bool) (u : Fin 3) : ℝ :=
  projInstValue u ^ 2 + if t then 1 else 0

/-- The linear working design `d(t, x) = (1, v(x), 1[t])`. -/
noncomputable def projInstDesign (t : Bool) (u : Fin 3) : Fin 3 → ℝ :=
  ![1, projInstValue u, if t then 1 else 0]

/-- The trial: assignment `ω.1` a fair coin, covariate `ω.2` uniform on three points. -/
noncomputable def projInstTrial : Trial (Bool × Fin 3) (Fin 3) Bool where
  μ := halfLaw.prod logisticInstNoise
  X ω := ω.2
  Y t ω := projInstOutcome t ω.2
  A ω := ω.1

instance : IsProbabilityMeasure projInstTrial.μ := by
  unfold projInstTrial; infer_instance

/-- Integrals in the trial: the average over the six points. -/
theorem integral_projInstTrial (f : Bool × Fin 3 → ℝ) :
    ∫ ω, f ω ∂projInstTrial.μ = (f (true, 0) + f (true, 1) + f (true, 2) + f (false, 0) +
      f (false, 1) + f (false, 2)) / 6 := by
  change ∫ ω, f ω ∂(halfLaw.prod logisticInstNoise) = _
  rw [integral_prod f Integrable.of_finite, integral_halfLaw, integral_logisticInstNoise,
    integral_logisticInstNoise]
  ring

/-- Almost sure statements in the trial hold at every point. -/
theorem ae_projInstTrial_iff {p : Bool × Fin 3 → Prop} :
    (∀ᵐ ω ∂projInstTrial.μ, p ω) ↔ ∀ ω, p ω := by
  refine ⟨fun h ω => ?_, fun h => ae_of_all _ h⟩
  have h1 := Measure.ae_ae_of_ae_prod (μ := halfLaw) (ν := logisticInstNoise) h
  rw [ae_halfLaw_iff] at h1
  exact ae_logisticInstNoise_iff.1 (h1 ω.1) ω.2

/-- **The regression of the trial is the quadratic** `E[Y | X, A] = v(X)² + 1[A]`: the outcome
is a function of the covariate and the assignment. -/
theorem projInst_isOutcomeRegression :
    IsOutcomeRegression projInstTrial.μ projInstTrial.A projInstTrial.X projInstTrial.obsOutcome
      fun a u => projInstOutcome a u := by
  refine ⟨fun _ => measurable_of_finite _, ?_⟩
  have hm : Measurable[MeasurableSpace.comap
      (fun ω => (projInstTrial.X ω, projInstTrial.A ω)) inferInstance]
      projInstTrial.obsOutcome := by
    have e : projInstTrial.obsOutcome =
        (fun c : Fin 3 × Bool => projInstOutcome c.2 c.1) ∘
          fun ω => (projInstTrial.X ω, projInstTrial.A ω) := rfl
    rw [e]
    exact (measurable_of_finite _).comp (comap_measurable _)
  have hW : Measurable fun ω => (projInstTrial.X ω, projInstTrial.A ω) :=
    measurable_of_finite _
  rw [condExp_of_stronglyMeasurable hW.comap_le hm.stronglyMeasurable Integrable.of_finite]
  rfl

/-- **The linear working model is misspecified**: no coefficient makes `d(t, x)ᵀξ` a version of
the regression `E[Y | X, A]`. -/
theorem projInst_not_isOutcomeRegression (ξ : Fin 3 → ℝ) :
    ¬ IsOutcomeRegression projInstTrial.μ projInstTrial.A projInstTrial.X
      projInstTrial.obsOutcome fun a u => projInstDesign a u ⬝ᵥ ξ := by
  intro h
  have hae := h.2.symm.trans projInst_isOutcomeRegression.2
  rw [EventuallyEq, ae_projInstTrial_iff] at hae
  have h0 := hae (false, 0)
  have h1 := hae (false, 1)
  have h2 := hae (false, 2)
  simp [projInstTrial, projInstDesign, projInstOutcome, projInstValue, dotProduct,
    Fin.sum_univ_three] at h0 h1 h2
  linarith

/-! ### The sample and the projection limit -/

/-- The record `(X, A, Y)` of a unit of the trial. -/
noncomputable def projInstRecord (ω : Bool × Fin 3) : Fin 3 × Bool × ℝ :=
  (projInstTrial.X ω, projInstTrial.A ω, projInstTrial.obsOutcome ω)

/-- The law of the sample: infinitely many independent copies of the trial. -/
noncomputable def projInstSampleLaw : Measure (ℕ → Bool × Fin 3) :=
  Measure.infinitePi fun _ => projInstTrial.μ

instance : IsProbabilityMeasure projInstSampleLaw := by
  unfold projInstSampleLaw; infer_instance

/-- The records of the sample. -/
noncomputable def projInstSample (i : ℕ) (ω : ℕ → Bool × Fin 3) : Fin 3 × Bool × ℝ :=
  projInstRecord (ω i)

theorem isIIDSample_projInstSample : IsIIDSample projInstSample projInstSampleLaw :=
  isIIDSample_infinitePi_comp _ (measurable_of_finite projInstRecord)

theorem map_projInstSample :
    projInstSampleLaw.map (projInstSample 0) = projInstTrial.μ.map projInstRecord :=
  map_infinitePi_comp_eval _ (measurable_of_finite projInstRecord) 0

/-- Integrals under the law of a record. -/
theorem integral_map_projInstSample {f : Fin 3 × Bool × ℝ → ℝ} (hf : Measurable f) :
    ∫ o, f o ∂(projInstSampleLaw.map (projInstSample 0)) =
      ∫ ω, f (projInstRecord ω) ∂projInstTrial.μ := by
  rw [map_projInstSample, integral_map (measurable_of_finite _).aemeasurable
    hf.aestronglyMeasurable]

/-- The projection coefficient `β* = (2/3, 0, 1)`. -/
noncomputable def projInstCoef : Fin 3 → ℝ := ![2 / 3, 0, 1]

theorem measurable_projInstDesign (a : Bool) (j : Fin 3) :
    Measurable fun u => projInstDesign a u j :=
  measurable_of_finite _

theorem measurable_projInst_gram (j k : Fin 3) :
    Measurable fun o : Fin 3 × Bool × ℝ =>
      recordDesign projInstDesign o j * recordDesign projInstDesign o k :=
  (measurable_recordDesign measurable_projInstDesign j).mul
    (measurable_recordDesign measurable_projInstDesign k)

theorem measurable_projInst_cross (j : Fin 3) :
    Measurable fun o : Fin 3 × Bool × ℝ =>
      recordDesign projInstDesign o j * recordResponse o :=
  (measurable_recordDesign measurable_projInstDesign j).mul (measurable_snd.comp measurable_snd)

/-- **The design second moment** `G = E[d dᵀ] = [[1, 0, 1/2], [0, 2/3, 0], [1/2, 0, 1/2]]`. -/
theorem projInst_gram :
    (Matrix.of fun j k => ∫ o, recordDesign projInstDesign o j * recordDesign projInstDesign o k
      ∂(projInstSampleLaw.map (projInstSample 0))) =
      !![1, 0, 1 / 2; 0, 2 / 3, 0; 1 / 2, 0, 1 / 2] := by
  ext j k
  rw [Matrix.of_apply, integral_map_projInstSample (measurable_projInst_gram j k),
    integral_projInstTrial]
  fin_cases j <;> fin_cases k <;>
    simp [projInstRecord, recordDesign, projInstDesign, projInstTrial, projInstValue] <;>
    norm_num

/-- **The cross moment** `E[d Y] = (7/6, 0, 5/6)`. -/
theorem projInst_cross :
    (fun j => ∫ o, recordDesign projInstDesign o j * recordResponse o
      ∂(projInstSampleLaw.map (projInstSample 0))) = ![7 / 6, 0, 5 / 6] := by
  funext j
  rw [integral_map_projInstSample (measurable_projInst_cross j), integral_projInstTrial]
  fin_cases j <;>
    simp [projInstRecord, recordDesign, recordResponse, projInstDesign, projInstTrial,
      Trial.obsOutcome, projInstOutcome, projInstValue] <;>
    norm_num

/-- **The projection coefficient solves the normal equations**: `G⁻¹ E[d Y] = (2/3, 0, 1)`. -/
theorem projInst_inv_mulVec :
    (!![1, 0, 1 / 2; 0, 2 / 3, 0; 1 / 2, 0, 1 / 2] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹ *ᵥ
      ![7 / 6, 0, 5 / 6] = projInstCoef := by
  set G : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 1 / 2; 0, 2 / 3, 0; 1 / 2, 0, 1 / 2]
  have hc : (![7 / 6, 0, 5 / 6] : Fin 3 → ℝ) = G *ᵥ projInstCoef := by
    funext i
    fin_cases i <;> simp [G, projInstCoef, mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  have hdet : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    simp [G, Matrix.det_fin_three]
    norm_num
  rw [hc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hdet, Matrix.one_mulVec]

/-- The design second moment of the records is positive definite. -/
theorem projInst_posDef :
    (Matrix.of fun j k => ∫ o, recordDesign projInstDesign o j * recordDesign projInstDesign o k
      ∂(projInstSampleLaw.map (projInstSample 0))).PosDef := by
  refine posDef_gram_of_ae (fun j => MemLp.of_bound
    (measurable_recordDesign measurable_projInstDesign j).aestronglyMeasurable 1
    (ae_of_all _ fun o => ?_)) fun v hv => ?_
  · rcases o with ⟨u, a, _⟩
    fin_cases j <;> fin_cases u <;> cases a <;>
      simp [recordDesign, projInstDesign, projInstValue] <;> norm_num
  · rw [map_projInstSample] at hv
    have hv' := ae_of_ae_map (measurable_of_finite projInstRecord).aemeasurable hv
    rw [ae_projInstTrial_iff] at hv'
    have h0 := hv' (false, 0)
    have h1 := hv' (false, 1)
    have h2 := hv' (true, 1)
    simp [projInstRecord, recordDesign, projInstDesign, projInstTrial, projInstValue,
      dotProduct, Fin.sum_univ_three] at h0 h1 h2
    funext j
    fin_cases j <;> simp <;> linarith

/-- **The least squares fit converges to the projection coefficient** `β* = (2/3, 0, 1)` under
the misspecified linear model. Every hypothesis of `tendstoInMeasure_leastSquaresFit` is
verified. -/
theorem projInst_tendstoInMeasure :
    TendstoInMeasure projInstSampleLaw
      (leastSquaresFit (recordDesign projInstDesign) recordResponse projInstSample) atTop
      (fun _ => projInstCoef) := by
  have h := tendstoInMeasure_leastSquaresFit isIIDSample_projInstSample
    (r := recordResponse) (measurable_recordDesign measurable_projInstDesign)
    (measurable_snd.comp measurable_snd)
    (fun j => MemLp.of_bound
      (measurable_recordDesign measurable_projInstDesign j).aestronglyMeasurable 1
      (ae_of_all _ fun o => by
        rcases o with ⟨u, a, _⟩
        fin_cases j <;> fin_cases u <;> cases a <;>
          simp [recordDesign, projInstDesign, projInstValue] <;> norm_num))
    (by
      rw [map_projInstSample, memLp_map_measure_iff
        (g := recordResponse) (measurable_snd.comp measurable_snd).aestronglyMeasurable
        (measurable_of_finite projInstRecord).aemeasurable]
      exact MemLp.of_discrete)
    projInst_posDef
  rwa [projInst_gram, projInst_cross, projInst_inv_mulVec] at h

/-! ### The target -/

/-- The target covariate law: probability `1/2` on each of the points with `v = 0` and
`v = 1`. -/
noncomputable def projInstTargetLaw : Measure (Fin 3) := stratumLaw ![0, 1 / 2, 1 / 2]

instance : IsProbabilityMeasure projInstTargetLaw :=
  isProbabilityMeasure_stratumLaw ⟨fun v => by fin_cases v <;> norm_num,
    by simp [Fin.sum_univ_three]; norm_num⟩

theorem integral_projInstTargetLaw (f : Fin 3 → ℝ) :
    ∫ u, f u ∂projInstTargetLaw = (f 1 + f 2) / 2 := by
  rw [projInstTargetLaw, integral_stratumLaw (fun v => by fin_cases v <;> norm_num),
    standardizedRisk, Fin.sum_univ_three]
  simp
  ring

/-- The target: covariate law `projInstTargetLaw` and the outcomes of the trial. -/
noncomputable def projInstTarget : Population (Fin 3) (Fin 3) Bool :=
  ⟨projInstTargetLaw, id, projInstOutcome⟩

theorem projInstTarget_covLaw : projInstTarget.covLaw = projInstTargetLaw :=
  Measure.map_id

/-- **The target mean** of `Y(t)` is `1/2 + 1[t]`. -/
theorem projInstTarget_armMean (t : Bool) :
    projInstTarget.armMean t = 1 / 2 + if t then 1 else 0 := by
  change ∫ u, projInstOutcome t u ∂projInstTargetLaw = _
  rw [integral_projInstTargetLaw]
  cases t <;> simp [projInstOutcome, projInstValue] <;> norm_num

/-- **The standardized fit converges to `2/3 + 1[t]`.** The fitted linear surface of arm `t`,
integrated against the target covariate law, converges in probability to
`∫ d(t, x)ᵀβ* dQ_X = 2/3 + 1[t]`. -/
theorem projInst_standardized_tendsto (t : Bool) :
    TendstoInMeasure projInstSampleLaw
      (fun n ω => ∫ x, projInstDesign t x ⬝ᵥ
        leastSquaresFit (recordDesign projInstDesign) recordResponse projInstSample n ω
          ∂projInstTarget.covLaw)
      atTop (fun _ => 2 / 3 + if t then 1 else 0) := by
  set g : (Fin 3 → ℝ) → ℝ := fun β => ∫ x, projInstDesign t x ⬝ᵥ β ∂projInstTarget.covLaw
  have hg : g = fun β => (projInstDesign t 1 ⬝ᵥ β + projInstDesign t 2 ⬝ᵥ β) / 2 := by
    funext β
    simp only [g, projInstTarget_covLaw, integral_projInstTargetLaw]
  have hc : ContinuousAt g projInstCoef := by
    rw [hg]
    exact (((continuous_const.dotProduct continuous_id).add
      (continuous_const.dotProduct continuous_id)).div_const _).continuousAt
  have hv : g projInstCoef = 2 / 3 + if t then 1 else 0 := by
    rw [hg]
    cases t <;> simp [projInstDesign, projInstCoef, projInstValue, dotProduct,
      Fin.sum_univ_three]
  rw [← hv]
  exact projInst_tendstoInMeasure.comp_continuousAt hc

/-- **The standardized limit misses the target mean by `1/6`** in both arms. -/
theorem projInst_standardized_ne_armMean (t : Bool) :
    (2 / 3 + if t then 1 else 0 : ℝ) - projInstTarget.armMean t = 1 / 6 := by
  rw [projInstTarget_armMean]
  ring

end PopulationAdjustment

end CausalInference
