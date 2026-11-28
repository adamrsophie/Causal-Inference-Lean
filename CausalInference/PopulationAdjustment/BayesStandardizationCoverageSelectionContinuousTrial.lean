/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.BayesStandardizationCoverageSelectionExamples
public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# A randomized trial with a uniform covariate and a logistic outcome model

A concrete model whose records take uncountably many values.

* **The trial** (`unifInstTrial`): a fair coin `A`, a covariate `X` uniform on `[0, 1]` (as the
  vector `x ∈ [0, 1] ⊂ ℝ¹`) and a noise `U` uniform on `[0, 1]`, all independent. The potential
  outcome is `Y(t) = 1[U < r(t)]` with `r(false) = 1/2` and `r(true) = 2/3`.
* **The outcome model**: the interaction design `z(x, t) = (1, x, 1[t], 1[t] x)` with the
  coefficient `ξ₀ = (0, 0, log 2, 0)`: the linear predictor is `log 2` in arm `true` and `0` in
  arm `false`, so `σ(z(x, t) ⬝ ξ₀) = r(t)`. The trial satisfies `Trial.LogisticOutcomeModel`
  (`unifInst_logisticOutcomeModel`). The design has full rank under the uniform covariate law:
  an affine function `c + d x` vanishing almost everywhere on `[0, 1]` has `c = d = 0`
  (`eq_zero_of_ae_add_mul_eq_zero`), since its zero set has at most one point.
* **The target** (`unifInstTarget`): a covariate uniform on `[0, 1]` and the potential outcomes
  of the trial; both arms are transported (`unifInst_structurallyInvariant`).
* **The sample**: infinitely many independent copies of the trial (`unifInstSampleLaw`).

## Main definitions

* `unifInstCov`, `unifInstCoef`, `unifInstRisk`, `unifInstOutcome`, `unifInstTrial`,
  `unifInstCovLaw`, `unifInstTarget`, `unifInstRecord`, `unifInstSampleLaw`, `unifInstSample`,
  `unifInstBall`.

## Main results

* `eq_zero_of_ae_add_mul_eq_zero`, `unifInstTrial_isRandomizedTwoArm`,
  `unifInst_isOutcomeRegression`, `unifInst_logisticOutcomeModel`, `abs_unifInst_design_le`.
* `unifInstTrial_covLaw`, `unifInstTarget_covLaw`, `unifInst_structurallyInvariant`.
* `isIIDSample_unifInstSample`, `unifInstBall_mem_nhds`.
-/

@[expose] public section

open scoped unitInterval

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### Affine functions vanishing almost everywhere on the unit interval -/

/-- **An affine function vanishing almost everywhere on `[0, 1]` is zero**: if `c + x d = 0` for
almost every `x` under the uniform law on `[0, 1]`, then `c = 0` and `d = 0`. -/
theorem eq_zero_of_ae_add_mul_eq_zero {c d : ℝ}
    (h : ∀ᵐ (x : I) ∂(volume : Measure I), c + (x : ℝ) * d = 0) : c = 0 ∧ d = 0 := by
  by_cases hd : d = 0
  · obtain ⟨x, hx⟩ := h.exists
    exact ⟨by simpa [hd] using hx, hd⟩
  · exfalso
    have hs : ({x : I | c + (x : ℝ) * d = 0}).Subsingleton := fun x hx y hy ↦ by
      simp only [mem_ofPred_eq] at hx hy
      exact Subtype.ext (mul_right_cancel₀ hd (by linarith))
    have h0 := (measure_eq_zero_iff_ae_notMem.1 (hs.measure_zero (volume : Measure I)))
    obtain ⟨x, hx1, hx2⟩ := (h.and h0).exists
    exact hx2 hx1

/-! ### The design, the coefficient and the risks -/

/-- The covariate vector `x ∈ [0, 1] ⊂ ℝ¹`. -/
def unifInstCov (x : I) : Fin 1 → ℝ := fun _ ↦ x

theorem measurable_unifInstCov : Measurable unifInstCov :=
  Measurable.of_eval fun _ ↦ measurable_subtype_coe

/-- The coefficient `ξ₀ = (α, β₁, γ, β₂) = (0, 0, log 2, 0)` of the interaction design. -/
noncomputable def unifInstCoef : Option (Fin 1) ⊕ Option (Fin 1) → ℝ
  | .inl none => 0
  | .inl (some _) => 0
  | .inr none => Real.log 2
  | .inr (some _) => 0

/-- The linear predictor of the interaction design. -/
theorem interactionDesign_unifInstCov_dotProduct (t : Bool) (x : I)
    (v : Option (Fin 1) ⊕ Option (Fin 1) → ℝ) :
    interactionDesign t (unifInstCov x) ⬝ᵥ v = v (.inl none) + (x : ℝ) * v (.inl (some 0)) +
      (if t then v (.inr none) + (x : ℝ) * v (.inr (some 0)) else 0) := by
  cases t <;>
    simp [dotProduct, Fintype.sum_sum_type, Fintype.sum_option, interactionDesign, unifInstCov]

/-- The linear predictor at `ξ₀` is `log 2` in arm `true` and `0` in arm `false`, at every
covariate value. -/
theorem unifInst_predictor (t : Bool) (x : Fin 1 → ℝ) :
    interactionDesign t x ⬝ᵥ unifInstCoef = if t then Real.log 2 else 0 := by
  cases t <;>
    simp [dotProduct, Fintype.sum_sum_type, Fintype.sum_option, interactionDesign, unifInstCoef]

/-- The risk of arm `t`: `2/3` in arm `true`, `1/2` in arm `false`. -/
noncomputable def unifInstRisk (t : Bool) : ℝ := if t then 2 / 3 else 1 / 2

theorem unifInstRisk_mem (t : Bool) : unifInstRisk t ∈ Icc (0 : ℝ) 1 := by
  cases t <;> simp [unifInstRisk] <;> norm_num

/-- The risk of the logistic model at `ξ₀` is `r(t)`. -/
theorem unifInst_risk (t : Bool) (x : Fin 1 → ℝ) :
    Real.sigmoid (interactionDesign t x ⬝ᵥ unifInstCoef) = unifInstRisk t := by
  rw [unifInst_predictor]
  cases t
  · simp [unifInstRisk, Real.sigmoid_def]
    norm_num
  · simpa [unifInstRisk] using sigmoid_log_two

/-! ### The trial -/

/-- The potential outcome `1[u < r(t)]`. -/
noncomputable def unifInstOutcome (t : Bool) (u : I) : ℝ :=
  if (u : ℝ) < unifInstRisk t then 1 else 0

theorem measurable_unifInstOutcome (t : Bool) : Measurable (unifInstOutcome t) :=
  Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const) measurable_const
    measurable_const

theorem unifInstOutcome_mem (t : Bool) (u : I) :
    unifInstOutcome t u = 0 ∨ unifInstOutcome t u = 1 := by
  unfold unifInstOutcome
  split_ifs <;> simp

/-- Averaging the potential outcome over the uniform noise gives the risk. -/
theorem integral_unifInstOutcome (t : Bool) :
    ∫ u, unifInstOutcome t u ∂(volume : Measure I) = unifInstRisk t := by
  set p : I := ⟨unifInstRisk t, unifInstRisk_mem t⟩
  have e : unifInstOutcome t = (Iio p).indicator 1 := by
    funext u
    by_cases h : (u : ℝ) < unifInstRisk t
    · have hu : u ∈ Iio p := h
      simp [unifInstOutcome, h, hu]
    · have hu : u ∉ Iio p := h
      simp [unifInstOutcome, h, hu]
  rw [e, integral_indicator_one measurableSet_Iio, measureReal_def, unitInterval.volume_Iio,
    ENNReal.toReal_ofReal (unifInstRisk_mem t).1]

/-- The trial of the example: assignment `ω.1.1`, covariate `ω.1.2` and noise `ω.2`,
independent; the assignment is a fair coin, the covariate and the noise are uniform on
`[0, 1]`. -/
noncomputable def unifInstTrial : Trial ((Bool × I) × I) (Fin 1 → ℝ) Bool where
  μ := (halfLaw.prod volume).prod volume
  X ω := unifInstCov ω.1.2
  Y t ω := unifInstOutcome t ω.2
  A ω := ω.1.1

instance : IsProbabilityMeasure unifInstTrial.μ := by
  unfold unifInstTrial; infer_instance

theorem measurable_unifInstTrial_obsOutcome : Measurable unifInstTrial.obsOutcome := by
  change Measurable fun ω : (Bool × I) × I ↦ unifInstOutcome ω.1.1 ω.2
  have hr : Measurable fun ω : (Bool × I) × I ↦ unifInstRisk ω.1.1 :=
    (measurable_of_countable unifInstRisk).comp (measurable_fst.comp measurable_fst)
  exact Measurable.ite (measurableSet_lt (measurable_subtype_coe.comp measurable_snd) hr)
    measurable_const measurable_const

/-- **The trial of the example is randomized.** The assignment is the first factor of the
product law, and the covariate and the potential outcomes are functions of the other two. -/
theorem unifInstTrial_isRandomizedTwoArm : unifInstTrial.IsRandomizedTwoArm where
  measurable_X := measurable_unifInstCov.comp (measurable_snd.comp measurable_fst)
  measurable_A := measurable_fst.comp measurable_fst
  measurable_Y t := (measurable_unifInstOutcome t).comp measurable_snd
  indepFun := by
    set G : I × I → (Fin 1 → ℝ) × ℝ × ℝ := fun v ↦
      (unifInstCov v.1, (unifInstOutcome false v.2, unifInstOutcome true v.2))
    have hG : Measurable G := (measurable_unifInstCov.comp measurable_fst).prodMk
      (((measurable_unifInstOutcome false).comp measurable_snd).prodMk
        ((measurable_unifInstOutcome true).comp measurable_snd))
    have h := indepFun_prod (μ := halfLaw) (ν := (volume : Measure I).prod volume)
      (X := id) (Y := G) measurable_id hG
    rw [← Measure.prodAssoc_prod] at h
    exact indepFun_comp_of_indepFun_map MeasurableEquiv.prodAssoc.measurable
      (measurable_id.comp measurable_fst) (hG.comp measurable_snd) h
  prob_pos := by
    change 0 < ((halfLaw.prod (volume : Measure I)).prod (volume : Measure I)).real
      ((fun ω : (Bool × I) × I ↦ ω.1.1) ⁻¹' {true})
    have e : (fun ω : (Bool × I) × I ↦ ω.1.1) ⁻¹' {true} =
        ({true} ×ˢ Set.univ) ×ˢ Set.univ := by ext; simp
    rw [e, measureReal_def, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, mul_one]
    simp [halfLaw, stratumLaw]
  prob_lt_one := by
    change ((halfLaw.prod (volume : Measure I)).prod (volume : Measure I)).real
      ((fun ω : (Bool × I) × I ↦ ω.1.1) ⁻¹' {true}) < 1
    have e : (fun ω : (Bool × I) × I ↦ ω.1.1) ⁻¹' {true} =
        ({true} ×ˢ Set.univ) ×ˢ Set.univ := by ext; simp
    rw [e, measureReal_def, Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, mul_one]
    simp [halfLaw, stratumLaw]
    norm_num

/-- The risk surface `m_t(x) = σ(z(x, t) ⬝ ξ₀)` of the example. -/
noncomputable def unifInstSurface (t : Bool) (x : Fin 1 → ℝ) : ℝ :=
  Real.sigmoid (interactionDesign t x ⬝ᵥ unifInstCoef)

theorem measurable_unifInstSurface (t : Bool) : Measurable (unifInstSurface t) :=
  continuous_sigmoid.measurable.comp
    (Finset.measurable_sum _ fun k _ ↦ (measurable_interactionDesign t k).mul_const _)

/-- **The regression of the example**: `E[Y | X, A] = σ(z(X, A) ⬝ ξ₀)`, computed by averaging
the outcome over the independent noise. -/
theorem unifInst_isOutcomeRegression :
    IsOutcomeRegression unifInstTrial.μ unifInstTrial.A unifInstTrial.X
      unifInstTrial.obsOutcome fun a x ↦ unifInstSurface a x := by
  refine ⟨measurable_unifInstSurface, ?_⟩
  exact condExp_prod_comp_fst (ρ := halfLaw.prod (volume : Measure I))
    (τ := (volume : Measure I))
    (W := fun v : Bool × I ↦ (unifInstCov v.2, v.1))
    (measurable_unifInstCov.comp measurable_snd |>.prodMk measurable_fst)
    (F := fun ω ↦ unifInstOutcome ω.1.1 ω.2)
    (integrable_of_ae_zero_or_one measurable_unifInstTrial_obsOutcome
      (ae_of_all _ fun ω ↦ unifInstOutcome_mem _ _))
    (φ := fun c ↦ unifInstSurface c.2 c.1)
    (measurable_from_prod_countable_left fun a ↦ measurable_unifInstSurface a)
    fun v ↦ by
      change ∫ u, unifInstOutcome v.1 u ∂(volume : Measure I) =
        unifInstSurface v.1 (unifInstCov v.2)
      rw [integral_unifInstOutcome, unifInstSurface, unifInst_risk]

/-- The interaction design of the example takes values in `[0, 1]`. -/
lemma abs_unifInst_design_le (ω : (Bool × I) × I) (j : Option (Fin 1) ⊕ Option (Fin 1)) :
    |interactionDesign (unifInstTrial.A ω) (unifInstTrial.X ω) j| ≤ 1 := by
  rcases ω with ⟨⟨a, x⟩, u⟩
  have hx : |(x : ℝ)| ≤ 1 := by rw [abs_of_nonneg x.2.1]; exact x.2.2
  rcases j with (_ | _) | (_ | _) <;> cases a <;>
    simp [interactionDesign, unifInstTrial, unifInstCov, hx]

/-- **The example satisfies the logistic outcome model** over the interaction design at `ξ₀`:
the design is measurable, bounded and of full rank under the uniform covariate law, and the
records have the law of the logistic family. -/
theorem unifInst_logisticOutcomeModel :
    unifInstTrial.LogisticOutcomeModel (fun c ↦ interactionDesign c.2 c.1) unifInstCoef := by
  have hz : ∀ k, Measurable fun c : (Fin 1 → ℝ) × Bool ↦ interactionDesign c.2 c.1 k :=
    fun k ↦ measurable_from_prod_countable_left fun a ↦ measurable_interactionDesign a k
  refine Trial.LogisticOutcomeModel.of_isOutcomeRegression unifInstTrial_isRandomizedTwoArm hz
    (fun j ↦ Integrable.of_bound
      (((hz j).comp (unifInstTrial_isRandomizedTwoArm.measurable_X.prodMk
          unifInstTrial_isRandomizedTwoArm.measurable_A)).aestronglyMeasurable) 1
      (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact abs_unifInst_design_le ω j))
    (fun v hv ↦ ?_)
    (ae_of_all _ fun ω ↦ unifInstOutcome_mem _ _) unifInst_isOutcomeRegression
  have h1 := Measure.ae_ae_of_ae_prod hv
  have h1' : ∀ᵐ w ∂(halfLaw.prod (volume : Measure I)),
      interactionDesign w.1 (unifInstCov w.2) ⬝ᵥ v = 0 :=
    h1.mono fun w hw ↦ by
      obtain ⟨u, hu⟩ := hw.exists
      exact hu
  have h2 := Measure.ae_ae_of_ae_prod h1'
  rw [ae_halfLaw_iff] at h2
  have hf : ∀ᵐ (x : I) ∂(volume : Measure I), v (.inl none) + (x : ℝ) * v (.inl (some 0)) = 0 :=
    (h2 false).mono fun x hx ↦ by
      rw [interactionDesign_unifInstCov_dotProduct] at hx
      simpa using hx
  have ht : ∀ᵐ (x : I) ∂(volume : Measure I), (v (.inl none) + v (.inr none)) +
      (x : ℝ) * (v (.inl (some 0)) + v (.inr (some 0))) = 0 :=
    (h2 true).mono fun x hx ↦ by
      rw [interactionDesign_unifInstCov_dotProduct] at hx
      simp only [ite_true] at hx
      linear_combination hx
  obtain ⟨hf0, hf1⟩ := eq_zero_of_ae_add_mul_eq_zero hf
  obtain ⟨ht0, ht1⟩ := eq_zero_of_ae_add_mul_eq_zero ht
  funext k
  rcases k with (_ | j) | (_ | j)
  · simp only [Pi.zero_apply]; linarith
  · rw [Subsingleton.elim j 0]; simp only [Pi.zero_apply]; linarith
  · simp only [Pi.zero_apply]; linarith
  · rw [Subsingleton.elim j 0]; simp only [Pi.zero_apply]; linarith

/-! ### The covariate laws and the target -/

/-- The uniform covariate law on `[0, 1] ⊂ ℝ¹`. -/
noncomputable def unifInstCovLaw : Measure (Fin 1 → ℝ) := (volume : Measure I).map unifInstCov

instance : IsProbabilityMeasure unifInstCovLaw :=
  (Measure.isProbabilityMeasure_map_iff measurable_unifInstCov.aemeasurable).2 inferInstance

theorem unifInstTrial_covLaw : unifInstTrial.covLaw = unifInstCovLaw := by
  change ((halfLaw.prod (volume : Measure I)).prod (volume : Measure I)).map
    (unifInstCov ∘ Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_unifInstCov (measurable_snd.comp measurable_fst),
    ← Measure.map_map measurable_snd measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul, Measure.map_snd_prod, measure_univ, one_smul, unifInstCovLaw]

/-- The target of the example: covariate `ω.1` uniform on `[0, 1]`, noise `ω.2` uniform on
`[0, 1]`, and the potential outcomes of the trial. -/
noncomputable def unifInstTarget : Population (I × I) (Fin 1 → ℝ) Bool where
  μ := (volume : Measure I).prod volume
  X ω := unifInstCov ω.1
  Y s ω := unifInstOutcome s ω.2

instance : IsProbabilityMeasure unifInstTarget.μ := by
  unfold unifInstTarget; infer_instance

theorem measurable_unifInstTarget_X : Measurable unifInstTarget.X :=
  measurable_unifInstCov.comp measurable_fst

theorem integrable_unifInstTarget_Y (s : Bool) : Integrable (unifInstTarget.Y s) unifInstTarget.μ :=
  integrable_of_ae_zero_or_one ((measurable_unifInstOutcome s).comp measurable_snd)
    (ae_of_all _ fun _ ↦ unifInstOutcome_mem _ _)

theorem unifInstTarget_covLaw : unifInstTarget.covLaw = unifInstCovLaw := by
  change ((volume : Measure I).prod (volume : Measure I)).map (unifInstCov ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_unifInstCov measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul, unifInstCovLaw]

instance : IsProbabilityMeasure unifInstTarget.covLaw := by
  rw [unifInstTarget_covLaw]; infer_instance

/-- **Overlap**: the target covariate law is the trial covariate law. -/
theorem unifInst_absolutelyContinuous : unifInstTarget.covLaw ≪ unifInstTrial.covLaw := by
  rw [unifInstTarget_covLaw, unifInstTrial_covLaw]

/-- **Both arms are transported**: the regression of the potential outcome of arm `t` on the
covariate is the risk surface of arm `t` in the trial and in the target. -/
theorem unifInst_structurallyInvariant (t : Bool) :
    StructurallyInvariant unifInstTrial.μ unifInstTrial.X (unifInstTrial.Y t)
      unifInstTarget.μ unifInstTarget.X (unifInstTarget.Y t) := by
  have hT := unifInstTrial_isRandomizedTwoArm.isCondMean
    (fun s ↦ integrable_of_ae_zero_or_one ((measurable_unifInstOutcome s).comp measurable_snd)
      (ae_of_all _ fun _ ↦ unifInstOutcome_mem _ _)) unifInst_isOutcomeRegression t
  have hQ : (fun ω ↦ unifInstSurface t (unifInstTarget.X ω)) =ᵐ[unifInstTarget.μ]
      unifInstTarget.μ[unifInstTarget.Y t | MeasurableSpace.comap unifInstTarget.X
        inferInstance] :=
    (condExp_prod_comp_fst (ρ := (volume : Measure I)) (τ := (volume : Measure I))
      (W := unifInstCov) measurable_unifInstCov (F := fun ω ↦ unifInstOutcome t ω.2)
      (integrable_unifInstTarget_Y t) (measurable_unifInstSurface t)
      fun x ↦ by
        change ∫ u, unifInstOutcome t u ∂(volume : Measure I) = unifInstSurface t (unifInstCov x)
        rw [integral_unifInstOutcome, unifInstSurface, unifInst_risk]).symm
  exact ⟨unifInstSurface t, hT.1, hT.2, hQ⟩

/-! ### The sample -/

/-- The record `((X, A), Y)` of a unit of the trial. -/
noncomputable def unifInstRecord (ω : (Bool × I) × I) : ((Fin 1 → ℝ) × Bool) × ℝ :=
  ((unifInstTrial.X ω, unifInstTrial.A ω), unifInstTrial.obsOutcome ω)

theorem measurable_unifInstRecord : Measurable unifInstRecord :=
  (unifInstTrial_isRandomizedTwoArm.measurable_X.prodMk
    unifInstTrial_isRandomizedTwoArm.measurable_A).prodMk measurable_unifInstTrial_obsOutcome

/-- The law of the sample: infinitely many independent copies of the trial. -/
noncomputable def unifInstSampleLaw : Measure (ℕ → (Bool × I) × I) :=
  Measure.infinitePi fun _ ↦ unifInstTrial.μ

instance : IsProbabilityMeasure unifInstSampleLaw := by
  unfold unifInstSampleLaw; infer_instance

/-- The records of the sample. -/
noncomputable def unifInstSample (i : ℕ) (ω : ℕ → (Bool × I) × I) : ((Fin 1 → ℝ) × Bool) × ℝ :=
  unifInstRecord (ω i)

theorem map_unifInstSample (i : ℕ) :
    unifInstSampleLaw.map (unifInstSample i) = unifInstTrial.μ.map unifInstRecord := by
  have : unifInstSample i = unifInstRecord ∘ fun x : ℕ → (Bool × I) × I ↦ x i := rfl
  rw [this, ← Measure.map_map (g := unifInstRecord) measurable_unifInstRecord
    (measurable_pi_apply i), unifInstSampleLaw, Measure.infinitePi_map_eval]

/-- **The sample of the example is i.i.d.** -/
theorem isIIDSample_unifInstSample : IsIIDSample unifInstSample unifInstSampleLaw where
  indep := iIndepFun_infinitePi (P := fun _ ↦ unifInstTrial.μ) fun _ ↦ measurable_unifInstRecord
  ident i := ⟨(measurable_unifInstRecord.comp (measurable_pi_apply i)).aemeasurable,
    (measurable_unifInstRecord.comp (measurable_pi_apply 0)).aemeasurable,
    (map_unifInstSample i).trans (map_unifInstSample 0).symm⟩

/-- The parameter set of the fit: the closed ball of radius `1` around `0`. -/
noncomputable def unifInstBall : Set (Option (Fin 1) ⊕ Option (Fin 1) → ℝ) :=
  Metric.closedBall 0 1

/-- The ball of radius `1` is a neighborhood of `ξ₀`, since `0 < log 2 < 1`. -/
lemma unifInstBall_mem_nhds : unifInstBall ∈ 𝓝 unifInstCoef := by
  refine Metric.closedBall_mem_nhds_of_mem ?_
  have h1 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num); linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [mem_ball_zero_iff, pi_norm_lt_iff (by norm_num)]
  rintro ((_ | _) | (_ | _)) <;> simp only [unifInstCoef, Real.norm_eq_abs] <;>
    rw [abs_lt] <;> constructor <;> linarith

end PopulationAdjustment

end CausalInference
