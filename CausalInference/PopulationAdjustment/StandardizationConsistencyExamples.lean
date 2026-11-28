/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationConsistencyLeastSquares
public import CausalInference.PopulationAdjustment.StandardizationExamples

/-!
# A randomized trial with a linear outcome model: every hypothesis verified

A concrete finite model for the large sample theorems of standardization with a least squares
outcome model.

* **The trial** (`lsExampleTrial`): a binary covariate `X` and a binary assignment `A`,
  independent and each equally likely (the law `halfLaw ⊗ halfLaw` on `Bool × Bool`), with
  potential outcomes `Y(t) = 1[X] + 1[t](1 + 1[X])`. The assignment is independent of the
  covariate and the potential outcomes, so the trial is randomized.
* **The outcome model**: the design `z(t, x) = (1, 1[x], 1[t], 1[t] 1[x])` with coefficient
  `ξ₀ = (0, 1, 1, 1)`. The regression `E[Y | X, A]` is `z(A, X) ⬝ ξ₀` and the design second
  moment is positive definite (`lsExample_linearOutcomeModel`).
* **The target** (`lsExampleTarget`): the covariate is `true` with probability `1/4`, and the
  potential outcomes are the same functions of the covariate, so both arms are transported and
  the target covariate law is dominated by the trial covariate law.
* **The sample**: infinitely many independent copies of the trial (`lsExampleSampleLaw`), which
  is an i.i.d. sample of the individual records with the law of the trial.

`lsExample_consistency`: the standardized least squares marginal mean difference converges in
probability to the target marginal mean difference, and that number is `5/4`
(`lsExample_marginalEffect`). `lsExample_unanchored` and `lsExample_anchored` verify the
comparisons with exactly reported aggregate quantities.

## Main definitions

* `lsExampleDesign`, `lsExampleCoef`, `lsExampleOutcome`, `lsExampleTrial`, `lsExampleTarget`,
  `lsExampleSampleLaw`, `lsExampleSample`.

## Main results

* `lsExampleTrial_isRandomizedTwoArm`, `lsExample_linearOutcomeModel`,
  `lsExample_structurallyInvariant`, `lsExample_absolutelyContinuous`,
  `isIIDSample_lsExampleSample`, `lsExample_marginalEffect`, `lsExample_consistency`,
  `lsExample_unanchored`, `lsExample_anchored`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-- The design `z(t, x) = (1, 1[x], 1[t], 1[t] 1[x])` of the example. -/
noncomputable def lsExampleDesign (t x : Bool) : Fin 4 → ℝ :=
  ![1, if x then 1 else 0, if t then 1 else 0, if t && x then 1 else 0]

/-- The coefficient `ξ₀ = (0, 1, 1, 1)` of the example. -/
noncomputable def lsExampleCoef : Fin 4 → ℝ := ![0, 1, 1, 1]

/-- The potential outcome `Y(t) = 1[x] + 1[t](1 + 1[x])` of the example. -/
noncomputable def lsExampleOutcome (t x : Bool) : ℝ :=
  (if x then 1 else 0) + if t then 1 + (if x then 1 else 0) else 0

theorem lsExampleDesign_dotProduct (t x : Bool) :
    lsExampleDesign t x ⬝ᵥ lsExampleCoef = lsExampleOutcome t x := by
  cases t <;> cases x <;>
    norm_num [lsExampleDesign, lsExampleCoef, lsExampleOutcome, dotProduct, Fin.sum_univ_four]

/-- The trial of the example: assignment `ω.1` and covariate `ω.2`, independent and equally
likely. -/
noncomputable def lsExampleTrial : Trial (Bool × Bool) Bool Bool where
  μ := halfLaw.prod halfLaw
  X := Prod.snd
  Y t ω := lsExampleOutcome t ω.2
  A := Prod.fst

instance : IsProbabilityMeasure lsExampleTrial.μ := by
  unfold lsExampleTrial; infer_instance

/-- **The trial of the example is randomized.** -/
theorem lsExampleTrial_isRandomizedTwoArm : lsExampleTrial.IsRandomizedTwoArm where
  measurable_X := measurable_snd
  measurable_A := measurable_fst
  measurable_Y _ := measurable_of_finite _
  indepFun := by
    have h : IndepFun (Prod.fst : Bool × Bool → Bool) Prod.snd (halfLaw.prod halfLaw) :=
      indepFun_prod (X := (id : Bool → Bool)) (Y := (id : Bool → Bool)) measurable_id
        measurable_id
    exact h.comp measurable_id (measurable_of_finite (fun x : Bool =>
      (x, potentialPair (fun t (y : Bool) => lsExampleOutcome t y) x)))
  prob_pos := by
    change 0 < (halfLaw.prod halfLaw).real (Prod.fst ⁻¹' {true})
    rw [measureReal_def, ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    simp [halfLaw, stratumLaw]
  prob_lt_one := by
    change (halfLaw.prod halfLaw).real (Prod.fst ⁻¹' {true}) < 1
    rw [measureReal_def, ← Set.prod_univ, Measure.prod_prod, measure_univ, mul_one]
    simp [halfLaw, stratumLaw]
    norm_num

/-- `halfLaw ⊗ halfLaw`-almost sure statements hold at every point. -/
theorem ae_lsExampleTrial_iff {p : Bool × Bool → Prop} :
    (∀ᵐ ω ∂lsExampleTrial.μ, p ω) ↔ ∀ ω, p ω := by
  refine ⟨fun h ω => ?_, fun h => ae_of_all _ h⟩
  have h2 := Measure.ae_ae_of_ae_prod (μ := halfLaw) (ν := halfLaw) h
  rw [ae_halfLaw_iff] at h2
  exact ae_halfLaw_iff.1 (h2 ω.1) ω.2

/-- **The example satisfies the linear outcome model.** The design coordinates and the potential
outcomes are measurable with finite second moments on the finite trial, the regression of the
outcome on the covariate and the arm is `z(A, X) ⬝ ξ₀`, and the design second moment is
positive definite. -/
theorem lsExample_linearOutcomeModel :
    lsExampleTrial.LinearOutcomeModel lsExampleDesign lsExampleCoef where
  measurable_z _ _ := measurable_of_finite _
  memLp_z a j := MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rcases ω with ⟨_, x⟩
      cases a <;> cases x <;> fin_cases j <;> norm_num [lsExampleDesign, lsExampleTrial])
  memLp_Y t := MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable 3
    (ae_of_all _ fun ω => by
      rcases ω with ⟨_, x⟩
      cases t <;> cases x <;> norm_num [lsExampleTrial, lsExampleOutcome])
  posDef := by
    refine posDef_gram_of_ae (fun j => MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable
      2 (ae_of_all _ fun ω => ?_)) fun v hv => ?_
    · rcases ω with ⟨a, x⟩
      cases a <;> cases x <;> fin_cases j <;> norm_num [lsExampleDesign, lsExampleTrial]
    · rw [ae_lsExampleTrial_iff] at hv
      have h00 := hv (false, false)
      have h01 := hv (false, true)
      have h10 := hv (true, false)
      have h11 := hv (true, true)
      simp [lsExampleTrial, lsExampleDesign, dotProduct, Fin.sum_univ_four] at h00 h01 h10 h11
      funext j
      fin_cases j <;> simp <;> linarith
  isOutcomeRegression := by
    refine ⟨fun _ => measurable_of_finite _, ?_⟩
    have hm : Measurable[MeasurableSpace.comap
        (fun ω => (lsExampleTrial.X ω, lsExampleTrial.A ω)) inferInstance]
        lsExampleTrial.obsOutcome :=
      (measurable_of_finite fun q : Bool × Bool => lsExampleOutcome q.2 q.1).comp
        (comap_measurable _)
    rw [condExp_of_stronglyMeasurable (lsExampleTrial_isRandomizedTwoArm.measurable_X.prodMk
      lsExampleTrial_isRandomizedTwoArm.measurable_A).comap_le hm.stronglyMeasurable
      Integrable.of_finite]
    exact ae_of_all _ fun ω => (lsExampleDesign_dotProduct _ _).symm

/-- The target of the example: the covariate is `true` with probability `1/4`. -/
noncomputable def lsExampleTarget : Population Bool Bool Bool :=
  ⟨standardizationTargetLaw, id, lsExampleOutcome⟩

instance : IsProbabilityMeasure lsExampleTarget.μ := by
  unfold lsExampleTarget; infer_instance

instance : IsProbabilityMeasure lsExampleTarget.covLaw := by
  unfold Population.covLaw; infer_instance

/-- **Both arms are transported**: the regression of each potential outcome on the covariate is
`lsExampleOutcome t` in the trial and in the target. -/
theorem lsExample_structurallyInvariant (t : Bool) :
    StructurallyInvariant lsExampleTrial.μ lsExampleTrial.X (lsExampleTrial.Y t)
      lsExampleTarget.μ lsExampleTarget.X (lsExampleTarget.Y t) := by
  refine ⟨lsExampleOutcome t, (Population.isCommonRegression_iff (P := lsExampleTrial.toPopulation)
    (Q := lsExampleTarget) t _).2 ⟨⟨measurable_of_finite _, ?_⟩, ⟨measurable_of_finite _, ?_⟩⟩⟩
  · have hm : Measurable[MeasurableSpace.comap lsExampleTrial.X inferInstance]
        (lsExampleTrial.Y t) :=
      (measurable_of_finite (lsExampleOutcome t)).comp (comap_measurable _)
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable
      lsExampleTrial_isRandomizedTwoArm.measurable_X.comap_le hm.stronglyMeasurable
      Integrable.of_finite).symm
  · have hm : Measurable[MeasurableSpace.comap lsExampleTarget.X inferInstance]
        (lsExampleTarget.Y t) :=
      (measurable_of_finite (lsExampleOutcome t)).comp (comap_measurable _)
    have hX : Measurable lsExampleTarget.X := measurable_id
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable hX.comap_le hm.stronglyMeasurable
      Integrable.of_finite).symm

/-- **Overlap**: the target covariate law is dominated by the trial covariate law. -/
theorem lsExample_absolutelyContinuous :
    lsExampleTarget.covLaw ≪ lsExampleTrial.covLaw := by
  intro s hs
  have hsrc : lsExampleTrial.covLaw = halfLaw := by
    change (halfLaw.prod halfLaw).map Prod.snd = halfLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  rw [hsrc, measure_eq_zero_iff_ae_notMem, ae_halfLaw_iff] at hs
  rw [Set.eq_empty_of_forall_notMem hs, measure_empty]

/-- The law of the sample: infinitely many independent copies of the trial. -/
noncomputable def lsExampleSampleLaw : Measure (ℕ → Bool × Bool) :=
  Measure.infinitePi fun _ => lsExampleTrial.μ

instance : IsProbabilityMeasure lsExampleSampleLaw := by
  unfold lsExampleSampleLaw; infer_instance

/-- The individual record `(X, A, Y)` of a unit of the trial. -/
noncomputable def lsExampleRecord (ω : Bool × Bool) : Bool × Bool × ℝ :=
  (lsExampleTrial.X ω, lsExampleTrial.A ω, lsExampleTrial.obsOutcome ω)

/-- The individual records of the sample. -/
noncomputable def lsExampleSample (i : ℕ) (ω : ℕ → Bool × Bool) : Bool × Bool × ℝ :=
  lsExampleRecord (ω i)

theorem map_lsExampleSample (i : ℕ) :
    lsExampleSampleLaw.map (lsExampleSample i) = lsExampleTrial.ipdLaw := by
  have : lsExampleSample i = lsExampleRecord ∘ fun x : ℕ → Bool × Bool => x i := rfl
  rw [this, ← Measure.map_map (g := lsExampleRecord) (measurable_of_finite _)
    (measurable_pi_apply i), lsExampleSampleLaw, Measure.infinitePi_map_eval]
  rfl

/-- **The sample of the example is i.i.d.** -/
theorem isIIDSample_lsExampleSample : IsIIDSample lsExampleSample lsExampleSampleLaw where
  indep := iIndepFun_infinitePi (P := fun _ => lsExampleTrial.μ) fun _ => measurable_of_finite _
  ident i := ⟨((measurable_of_finite lsExampleRecord).comp (measurable_pi_apply i)).aemeasurable,
    ((measurable_of_finite lsExampleRecord).comp (measurable_pi_apply 0)).aemeasurable,
    (map_lsExampleSample i).trans (map_lsExampleSample 0).symm⟩

/-- **The limit of the example**: the target marginal mean difference is `5/4`. -/
theorem lsExample_marginalEffect : lsExampleTarget.marginalEffect id false true = 5 / 4 := by
  have hint : ∀ f : Bool → ℝ, ∫ x, f x ∂standardizationTargetLaw = f true / 4 + 3 * f false / 4 :=
    fun f => by
      rw [standardizationTargetLaw, integral_stratumLaw (fun v => by cases v <;> norm_num)]
      simp [standardizedRisk]; ring
  simp only [Population.marginalEffect, Population.armMean, lsExampleTarget, id]
  rw [hint, hint]
  simp [lsExampleOutcome]
  norm_num

/-- **Consistency in the example.** The standardized least squares marginal mean difference
`∫ z(true, x) ⬝ ξ̂ dQ_X - ∫ z(false, x) ⬝ ξ̂ dQ_X` of the example converges in probability to
the target marginal mean difference `5/4`; every hypothesis of
`tendstoInMeasure_leastSquares_linkMarginal` is verified. -/
theorem lsExample_consistency :
    TendstoInMeasure lsExampleSampleLaw
      (fun n ω => linkMarginal id lsExampleTarget.covLaw
        (fun x => lsExampleDesign false x ⬝ᵥ
          leastSquaresFit (recordDesign lsExampleDesign) recordResponse lsExampleSample n ω)
        (fun x => lsExampleDesign true x ⬝ᵥ
          leastSquaresFit (recordDesign lsExampleDesign) recordResponse lsExampleSample n ω))
      atTop (fun _ => 5 / 4) := by
  rw [← lsExample_marginalEffect]
  exact tendstoInMeasure_leastSquares_linkMarginal lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel isIIDSample_lsExampleSample (map_lsExampleSample 0)
    measurable_id Integrable.of_finite Integrable.of_finite (lsExample_structurallyInvariant false)
    (lsExample_structurallyInvariant true) lsExample_absolutelyContinuous
    (fun _ _ => Integrable.of_finite) continuousAt_id continuousAt_id

/-- **The unanchored comparison in the example.** With the arm `false` of the trial standardized
to the target and the target mean of the other treatment reported exactly,
`E_Q[Y(true)] = 7/4`, the unanchored estimator converges in probability to `5/4`; every
hypothesis of `tendstoInMeasure_leastSquares_unanchored` is verified. -/
theorem lsExample_unanchored :
    TendstoInMeasure lsExampleSampleLaw
      (fun n ω => id (lsExampleTarget.armMean true) -
        id (∫ x, lsExampleDesign false x ⬝ᵥ
          leastSquaresFit (recordDesign lsExampleDesign) recordResponse lsExampleSample n ω
            ∂lsExampleTarget.covLaw))
      atTop (fun _ => 5 / 4) := by
  rw [← lsExample_marginalEffect]
  exact tendstoInMeasure_leastSquares_unanchored lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel isIIDSample_lsExampleSample (map_lsExampleSample 0)
    measurable_id Integrable.of_finite (lsExample_structurallyInvariant false)
    lsExample_absolutelyContinuous (fun _ => Integrable.of_finite)
    (tendstoInMeasure_const _) continuousAt_id continuousAt_id

/-- **The anchored comparison in the example.** Both arms of the trial are standardized to the
target, and the contrast of the common comparator `true` against itself is reported exactly as
`0`; the anchored estimator converges in probability to `5/4`. Every hypothesis of
`tendstoInMeasure_leastSquares_anchored` is verified. -/
theorem lsExample_anchored :
    TendstoInMeasure lsExampleSampleLaw
      (fun n ω => linkMarginal id lsExampleTarget.covLaw
        (fun x => lsExampleDesign false x ⬝ᵥ
          leastSquaresFit (recordDesign lsExampleDesign) recordResponse lsExampleSample n ω)
        (fun x => lsExampleDesign true x ⬝ᵥ
          leastSquaresFit (recordDesign lsExampleDesign) recordResponse lsExampleSample n ω) -
        lsExampleTarget.marginalEffect id true true)
      atTop (fun _ => 5 / 4) := by
  rw [← lsExample_marginalEffect]
  exact tendstoInMeasure_leastSquares_anchored (b := true) lsExampleTrial_isRandomizedTwoArm
    lsExample_linearOutcomeModel isIIDSample_lsExampleSample (map_lsExampleSample 0)
    measurable_id Integrable.of_finite Integrable.of_finite (lsExample_structurallyInvariant false)
    (lsExample_structurallyInvariant true) lsExample_absolutelyContinuous
    (fun _ _ => Integrable.of_finite) (tendstoInMeasure_const _) continuousAt_id continuousAt_id

end PopulationAdjustment

end CausalInference
