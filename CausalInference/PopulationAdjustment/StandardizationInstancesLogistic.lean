/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.StandardizationInstancesLogisticLaw
public import CausalInference.PopulationAdjustment.OutcomeModelExamples

/-!
# A randomized trial with a logistic outcome model: every hypothesis verified

A concrete finite model for the large sample theorems of standardization with a logistic outcome
model fitted by maximum likelihood.

* **The trial** (`logisticInstTrial`): a fair coin `A`, a binary covariate `X` (as the vector
  `x ∈ {0, 1} ⊂ ℝ¹`) with `P(X = 1) = 1/2`, and a uniform noise `U` on `{0, 1, 2}`, all
  independent. The potential outcome is `Y(t) = 1[U < k(t, X)]` with `k = 1` when the arm matches
  the covariate and `k = 2` otherwise, so `P(Y(t) = 1 | X = x) = 1/3` if `t = x` and `2/3`
  otherwise.
* **The outcome model**: the interaction design `z(x, t) = (1, x, 1[t], 1[t] x)` with the
  coefficient `ξ₀ = (-log 2, 2 log 2, 2 log 2, -4 log 2)`: the linear predictor is `-log 2` when
  `t = x` and `log 2` otherwise, so `σ(z(x, t) ⬝ ξ₀)` is the risk above. The treatment by
  covariate interaction is `-4 log 2 ≠ 0`. The trial satisfies `Trial.LogisticOutcomeModel`
  (`logisticInst_logisticOutcomeModel`), proved from the binary outcome and its regression by
  `Trial.LogisticOutcomeModel.of_isOutcomeRegression`.
* **The target** (`logisticInstTarget`): `P(X = 1) = 3/4`, three treatments `a = 0`, `b = 1`,
  `c = 2`; `a` and `c` have the outcomes of the active arm and the reference arm of the trial,
  `b` has risk `2/3` at every covariate value. The target arm means are `5/12`, `2/3` and `7/12`.
* **The sample**: infinitely many independent copies of the trial (`logisticInstSampleLaw`).

**Limits.** The standardized marginal log odds ratio of `a` against `c` converges to
`log (25/49)` (`logisticInst_linkMarginal`). The conditional plug-in on the logit scale at the
target covariate mean converges to `γ + x̄ β₂ = -log 2` (`logisticInst_conditionalPlugIn`). The
two limits differ: their difference `log (50/49)` lies in `[1/50, 1/49]`
(`logisticInst_conditionalPlugIn_ne_linkMarginal`), which is the difference of the averaging
gaps of the two true surfaces. The unanchored and anchored comparisons of `b` against `a` converge
to `log (14/5)` (`logisticInst_unanchored`, `logisticInst_anchored`); their reported aggregate
quantities are deterministic sequences that converge to the true target quantities.

## Main definitions

* `logisticInstCov`, `logisticInstCoef`, `logisticInstOutcome`, `logisticInstNoise`,
  `logisticInstTrial`, `logisticInstTargetCov`, `logisticInstTarget`, `logisticInstSampleLaw`,
  `logisticInstSample`, `logisticInstBall`.

## Main results

* `logisticInstTrial_isRandomizedTwoArm`, `logisticInst_isOutcomeRegression`,
  `logisticInst_logisticOutcomeModel`, `logisticInst_structurallyInvariant`,
  `logisticInst_absolutelyContinuous`, `isIIDSample_logisticInstSample`.
* `logisticInst_linkMarginal`, `logisticInst_unanchored`, `logisticInst_anchored`,
  `logisticInst_conditionalPlugIn`, `logisticInst_conditionalPlugIn_ne_linkMarginal`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### Two general helpers -/

/-- **Independence is preserved by pulling back along a measurable map**: if `f` and `g` are
independent under the image measure `μ ∘ e⁻¹`, then `f ∘ e` and `g ∘ e` are independent under
`μ`. -/
theorem indepFun_comp_of_indepFun_map {Ω Ω' β γ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {e : Ω → Ω'}
    (he : Measurable e) {f : Ω' → β} {g : Ω' → γ} (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g (μ.map e)) : IndepFun (f ∘ e) (g ∘ e) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have := h s t hs ht
  rwa [Measure.map_apply he ((hf hs).inter (hg ht)), Measure.map_apply he (hf hs),
    Measure.map_apply he (hg ht)] at this

/-- **A deterministic reported quantity**: the sequence `c + 1/(n + 1)` converges in probability
to `c` under every probability law. -/
theorem tendstoInMeasure_add_one_div_succ {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ)
    [IsProbabilityMeasure P] (c : ℝ) :
    TendstoInMeasure P (fun (n : ℕ) (_ : Ξ) => c + 1 / ((n : ℝ) + 1)) atTop (fun _ => c) := by
  refine tendstoInMeasure_of_tendsto_ae (μ := P) (f := fun (n : ℕ) (_ : Ξ) => c + 1 / ((n : ℝ) + 1))
    (g := fun _ => c) (fun n => aestronglyMeasurable_const) (ae_of_all _ fun _ => ?_)
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add c

/-! ### The design, the coefficient and the risks -/

/-- The covariate vector `x ∈ {0, 1} ⊂ ℝ¹` of a binary covariate. -/
def logisticInstCov (b : Bool) : Fin 1 → ℝ := fun _ => if b then 1 else 0

/-- The coefficient `ξ₀ = (α, β₁, γ, β₂) = (-log 2, 2 log 2, 2 log 2, -4 log 2)` of the
interaction design. -/
noncomputable def logisticInstCoef : Option (Fin 1) ⊕ Option (Fin 1) → ℝ
  | .inl none => -Real.log 2
  | .inl (some _) => 2 * Real.log 2
  | .inr none => 2 * Real.log 2
  | .inr (some _) => -(4 * Real.log 2)

/-- The linear predictor of the interaction design at a binary covariate. -/
theorem interactionDesign_logisticInstCov_dotProduct (t b : Bool)
    (v : Option (Fin 1) ⊕ Option (Fin 1) → ℝ) :
    interactionDesign t (logisticInstCov b) ⬝ᵥ v = v (.inl none) +
      (if b then v (.inl (some 0)) else 0) +
      (if t then v (.inr none) + (if b then v (.inr (some 0)) else 0) else 0) := by
  cases t <;> cases b <;>
    simp [dotProduct, Fintype.sum_sum_type, Fintype.sum_option, interactionDesign,
      logisticInstCov]

/-- The linear predictor of the example is `-log 2` when the arm matches the covariate and
`log 2` otherwise. -/
theorem logisticInst_predictor (t b : Bool) :
    interactionDesign t (logisticInstCov b) ⬝ᵥ logisticInstCoef =
      if t = b then -Real.log 2 else Real.log 2 := by
  rw [interactionDesign_logisticInstCov_dotProduct]
  cases t <;> cases b <;> simp [logisticInstCoef] <;> ring

theorem sigmoid_log_two : Real.sigmoid (Real.log 2) = 2 / 3 := by
  rw [Real.sigmoid_def, Real.exp_neg, Real.exp_log two_pos]; norm_num

theorem sigmoid_neg_log_two : Real.sigmoid (-Real.log 2) = 1 / 3 := by
  rw [Real.sigmoid_def, neg_neg, Real.exp_log two_pos]; norm_num

/-- The risk of the example: `1/3` when the arm matches the covariate, `2/3` otherwise. -/
theorem logisticInst_risk (t b : Bool) :
    Real.sigmoid (interactionDesign t (logisticInstCov b) ⬝ᵥ logisticInstCoef) =
      if t = b then 1 / 3 else 2 / 3 := by
  rw [logisticInst_predictor]
  split_ifs
  · exact sigmoid_neg_log_two
  · exact sigmoid_log_two

/-! ### The trial -/

/-- The uniform law of the noise on `{0, 1, 2}`. -/
noncomputable def logisticInstNoise : Measure (Fin 3) := stratumLaw fun _ => 1 / 3

instance : IsProbabilityMeasure logisticInstNoise :=
  isProbabilityMeasure_stratumLaw ⟨fun _ => by norm_num, by simp⟩

theorem integral_logisticInstNoise (f : Fin 3 → ℝ) :
    ∫ u, f u ∂logisticInstNoise = (f 0 + f 1 + f 2) / 3 := by
  rw [logisticInstNoise, integral_stratumLaw (fun _ => by norm_num), standardizedRisk,
    Fin.sum_univ_three]
  ring

theorem ae_logisticInstNoise_iff {p : Fin 3 → Prop} :
    (∀ᵐ u ∂logisticInstNoise, p u) ↔ ∀ u, p u := by
  rw [logisticInstNoise, ae_stratumLaw_iff]
  exact ⟨fun h u => h u (by norm_num), fun h u _ => h u⟩

/-- The potential outcome `1[u < k(t, x)]`, with `k = 1` when `t = x` and `k = 2` otherwise. -/
noncomputable def logisticInstOutcome (t b : Bool) (u : Fin 3) : ℝ :=
  if (u : ℕ) < (if t = b then 1 else 2) then 1 else 0

theorem logisticInstOutcome_mem (t b : Bool) (u : Fin 3) :
    logisticInstOutcome t b u = 0 ∨ logisticInstOutcome t b u = 1 := by
  unfold logisticInstOutcome
  split_ifs <;> simp

/-- Averaging the potential outcome over the noise gives the risk. -/
theorem integral_logisticInstOutcome (t b : Bool) :
    ∫ u, logisticInstOutcome t b u ∂logisticInstNoise =
      Real.sigmoid (interactionDesign t (logisticInstCov b) ⬝ᵥ logisticInstCoef) := by
  rw [integral_logisticInstNoise, logisticInst_risk]
  cases t <;> cases b <;> simp [logisticInstOutcome] <;> norm_num

/-- The trial of the example: assignment `ω.1.1`, covariate `ω.1.2` and noise `ω.2`, independent,
the assignment and the covariate equally likely, the noise uniform. -/
noncomputable def logisticInstTrial : Trial ((Bool × Bool) × Fin 3) (Fin 1 → ℝ) Bool where
  μ := (halfLaw.prod halfLaw).prod logisticInstNoise
  X ω := logisticInstCov ω.1.2
  Y t ω := logisticInstOutcome t ω.1.2 ω.2
  A ω := ω.1.1

instance : IsProbabilityMeasure logisticInstTrial.μ := by
  unfold logisticInstTrial; infer_instance

/-- Almost sure statements in the trial hold at every point. -/
theorem ae_logisticInstTrial_iff {p : (Bool × Bool) × Fin 3 → Prop} :
    (∀ᵐ ω ∂logisticInstTrial.μ, p ω) ↔ ∀ ω, p ω := by
  refine ⟨fun h ω => ?_, fun h => ae_of_all _ h⟩
  have h1 := Measure.ae_ae_of_ae_prod (μ := halfLaw.prod halfLaw) (ν := logisticInstNoise) h
  have h2 := Measure.ae_ae_of_ae_prod (μ := halfLaw) (ν := halfLaw) h1
  rw [ae_halfLaw_iff] at h2
  have h3 := ae_halfLaw_iff.1 (h2 ω.1.1) ω.1.2
  exact ae_logisticInstNoise_iff.1 h3 ω.2

/-- **The trial of the example is randomized.** The assignment is the first factor of the
product law, and the covariate and the potential outcomes are functions of the other two. -/
theorem logisticInstTrial_isRandomizedTwoArm : logisticInstTrial.IsRandomizedTwoArm where
  measurable_X := measurable_of_finite _
  measurable_A := measurable_of_finite _
  measurable_Y _ := measurable_of_finite _
  indepFun := by
    set G : Bool × Fin 3 → (Fin 1 → ℝ) × ℝ × ℝ := fun v =>
      (logisticInstCov v.1, (logisticInstOutcome false v.1 v.2, logisticInstOutcome true v.1 v.2))
    have h := indepFun_prod (μ := halfLaw) (ν := halfLaw.prod logisticInstNoise)
      (X := id) (Y := G) measurable_id (measurable_of_finite G)
    rw [← Measure.prodAssoc_prod] at h
    exact indepFun_comp_of_indepFun_map MeasurableEquiv.prodAssoc.measurable
      (measurable_id.comp measurable_fst) ((measurable_of_finite G).comp measurable_snd) h
  prob_pos := by
    change 0 < ((halfLaw.prod halfLaw).prod logisticInstNoise).real
      ((fun ω : (Bool × Bool) × Fin 3 => ω.1.1) ⁻¹' {true})
    have e : (fun ω : (Bool × Bool) × Fin 3 => ω.1.1) ⁻¹' {true} =
        ({true} ×ˢ Set.univ) ×ˢ Set.univ := by ext; simp
    rw [e, measureReal_def, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
      mul_one, mul_one]
    simp [halfLaw, stratumLaw]
  prob_lt_one := by
    change ((halfLaw.prod halfLaw).prod logisticInstNoise).real
      ((fun ω : (Bool × Bool) × Fin 3 => ω.1.1) ⁻¹' {true}) < 1
    have e : (fun ω : (Bool × Bool) × Fin 3 => ω.1.1) ⁻¹' {true} =
        ({true} ×ˢ Set.univ) ×ˢ Set.univ := by ext; simp
    rw [e, measureReal_def, Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ,
      mul_one, mul_one]
    simp [halfLaw, stratumLaw]
    norm_num

/-- The risk surface `m_t(x) = σ(z(x, t) ⬝ ξ₀)` of the example. -/
noncomputable def logisticInstSurface (t : Bool) (x : Fin 1 → ℝ) : ℝ :=
  Real.sigmoid (interactionDesign t x ⬝ᵥ logisticInstCoef)

theorem measurable_logisticInstSurface (t : Bool) : Measurable (logisticInstSurface t) :=
  continuous_sigmoid.measurable.comp
    (Finset.measurable_sum _ fun k _ => (measurable_interactionDesign t k).mul_const _)

/-- **The regression of the example**: `E[Y | X, A] = σ(z(X, A) ⬝ ξ₀)`, computed by averaging
the outcome over the independent noise (`condExp_prod_comp_fst`). -/
theorem logisticInst_isOutcomeRegression :
    IsOutcomeRegression logisticInstTrial.μ logisticInstTrial.A logisticInstTrial.X
      logisticInstTrial.obsOutcome fun a x => logisticInstSurface a x := by
  refine ⟨measurable_logisticInstSurface, ?_⟩
  exact condExp_prod_comp_fst (ρ := halfLaw.prod halfLaw) (τ := logisticInstNoise)
    (W := fun v : Bool × Bool => (logisticInstCov v.2, v.1)) (measurable_of_finite _)
    (F := fun ω => logisticInstOutcome ω.1.1 ω.1.2 ω.2) Integrable.of_finite
    (φ := fun c => logisticInstSurface c.2 c.1)
    (measurable_from_prod_countable_left fun a => measurable_logisticInstSurface a)
    fun v => integral_logisticInstOutcome v.1 v.2

/-- **The example satisfies the logistic outcome model** over the interaction design at `ξ₀`:
the design is measurable, integrable and of full rank, and the records have the law of the
logistic family. -/
theorem logisticInst_logisticOutcomeModel :
    logisticInstTrial.LogisticOutcomeModel (fun c => interactionDesign c.2 c.1)
      logisticInstCoef := by
  refine Trial.LogisticOutcomeModel.of_isOutcomeRegression logisticInstTrial_isRandomizedTwoArm
    (fun k => measurable_from_prod_countable_left fun a => measurable_interactionDesign a k)
    (fun _ => Integrable.of_finite) (fun v hv => ?_)
    (ae_of_all _ fun ω => logisticInstOutcome_mem _ _ _) logisticInst_isOutcomeRegression
  rw [ae_logisticInstTrial_iff] at hv
  have h : ∀ a b : Bool, interactionDesign a (logisticInstCov b) ⬝ᵥ v = 0 := fun a b =>
    hv ((a, b), 0)
  have h00 := h false false
  have h01 := h false true
  have h10 := h true false
  have h11 := h true true
  simp only [interactionDesign_logisticInstCov_dotProduct, ite_true, ite_false,
    Bool.false_eq_true] at h00 h01 h10 h11
  funext k
  rcases k with (_ | j) | (_ | j)
  · simp only [Pi.zero_apply]; linarith
  · rw [Subsingleton.elim j 0]; simp only [Pi.zero_apply]; linarith
  · simp only [Pi.zero_apply]; linarith
  · rw [Subsingleton.elim j 0]; simp only [Pi.zero_apply]; linarith

/-! ### The target -/

/-- The target covariate law: `X = 1` with probability `3/4`. -/
noncomputable def logisticInstTargetCov : Measure Bool :=
  stratumLaw fun v => if v then 3 / 4 else 1 / 4

instance : IsProbabilityMeasure logisticInstTargetCov :=
  isProbabilityMeasure_stratumLaw ⟨fun v => by cases v <;> norm_num, by simp; norm_num⟩

/-- The target potential outcomes of the treatments `a = 0`, `b = 1`, `c = 2`: `a` and `c` as
the active and the reference arm of the trial, `b` with risk `2/3` at every covariate value. -/
noncomputable def logisticInstTargetOutcome (s : Fin 3) (b : Bool) (u : Fin 3) : ℝ :=
  if s = 0 then logisticInstOutcome true b u
  else if s = 1 then (if (u : ℕ) < 2 then 1 else 0)
  else logisticInstOutcome false b u

/-- The target of the example: covariate `ω.1` with `P(X = 1) = 3/4` and the uniform noise
`ω.2`. -/
noncomputable def logisticInstTarget : Population (Bool × Fin 3) (Fin 1 → ℝ) (Fin 3) where
  μ := logisticInstTargetCov.prod logisticInstNoise
  X ω := logisticInstCov ω.1
  Y s ω := logisticInstTargetOutcome s ω.1 ω.2

instance : IsProbabilityMeasure logisticInstTarget.μ := by
  unfold logisticInstTarget; infer_instance

theorem measurableEmbedding_logisticInstCov : MeasurableEmbedding logisticInstCov :=
  ⟨fun a b h => by
    have := congrFun h 0
    cases a <;> cases b <;> simp_all [logisticInstCov],
    measurable_of_finite _, fun s _ => (s.toFinite.image _).measurableSet⟩

theorem logisticInstTarget_covLaw :
    logisticInstTarget.covLaw = logisticInstTargetCov.map logisticInstCov := by
  change (logisticInstTargetCov.prod logisticInstNoise).map (logisticInstCov ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul]

instance : IsProbabilityMeasure logisticInstTarget.covLaw := by
  rw [logisticInstTarget_covLaw]; infer_instance

/-- Integrals under the target covariate law. -/
theorem integral_logisticInstTarget_covLaw (f : (Fin 1 → ℝ) → ℝ) :
    ∫ x, f x ∂logisticInstTarget.covLaw =
      f (logisticInstCov false) / 4 + 3 * f (logisticInstCov true) / 4 := by
  rw [logisticInstTarget_covLaw, measurableEmbedding_logisticInstCov.integral_map,
    logisticInstTargetCov, integral_stratumLaw (fun v => by cases v <;> norm_num),
    standardizedRisk, Fintype.sum_bool]
  simp only [ite_true, ite_false, Bool.false_eq_true]
  ring

theorem logisticInstTrial_covLaw : logisticInstTrial.covLaw = halfLaw.map logisticInstCov := by
  change ((halfLaw.prod halfLaw).prod logisticInstNoise).map
    (logisticInstCov ∘ Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map (measurable_of_finite _) (measurable_snd.comp measurable_fst),
    ← Measure.map_map measurable_snd measurable_fst, Measure.map_fst_prod, measure_univ,
    one_smul, Measure.map_snd_prod, measure_univ, one_smul]

/-- **Overlap**: the target covariate law is dominated by the trial covariate law. -/
theorem logisticInst_absolutelyContinuous :
    logisticInstTarget.covLaw ≪ logisticInstTrial.covLaw := by
  rw [logisticInstTarget_covLaw, logisticInstTrial_covLaw]
  refine Measure.AbsolutelyContinuous.map (fun s hs => ?_) (measurable_of_finite _)
  rw [measure_eq_zero_iff_ae_notMem, ae_halfLaw_iff] at hs
  rw [Set.eq_empty_of_forall_notMem hs, measure_empty]

/-- The regression of the target outcome of `s` on the covariate is the surface of the trial arm
standing for `s`. -/
theorem logisticInstTarget_isCondMean (s : Fin 3) (t : Bool)
    (hst : ∀ b u, logisticInstTargetOutcome s b u = logisticInstOutcome t b u) :
    logisticInstTarget.IsCondMean s (logisticInstSurface t) := by
  refine ⟨measurable_logisticInstSurface t, ?_⟩
  refine (condExp_prod_comp_fst (ρ := logisticInstTargetCov) (τ := logisticInstNoise)
    (W := logisticInstCov) (measurable_of_finite _)
    (F := fun ω => logisticInstTargetOutcome s ω.1 ω.2) Integrable.of_finite
    (measurable_logisticInstSurface t) fun b => ?_).symm
  simp only [hst]
  exact integral_logisticInstOutcome t b

/-- **The arms of the trial are transported**: arm `true` stands for `a = 0` and arm `false` for
`c = 2`; the regression of the potential outcome on the covariate is the risk surface in the
trial and in the target. -/
theorem logisticInst_structurallyInvariant (t : Bool) (s : Fin 3)
    (hst : ∀ b u, logisticInstTargetOutcome s b u = logisticInstOutcome t b u) :
    StructurallyInvariant logisticInstTrial.μ logisticInstTrial.X (logisticInstTrial.Y t)
      logisticInstTarget.μ logisticInstTarget.X (logisticInstTarget.Y s) := by
  have hT := logisticInstTrial_isRandomizedTwoArm.isCondMean
    (fun _ => Integrable.of_finite) logisticInst_isOutcomeRegression t
  exact ⟨logisticInstSurface t, hT.1, hT.2, (logisticInstTarget_isCondMean s t hst).2⟩

theorem logisticInstTarget_outcome_zero (b : Bool) (u : Fin 3) :
    logisticInstTargetOutcome 0 b u = logisticInstOutcome true b u := by
  simp [logisticInstTargetOutcome]

theorem logisticInstTarget_outcome_two (b : Bool) (u : Fin 3) :
    logisticInstTargetOutcome 2 b u = logisticInstOutcome false b u := by
  simp [logisticInstTargetOutcome]

/-- The target arm means: `5/12` for `a = 0`, `2/3` for `b = 1`, `7/12` for `c = 2`. -/
theorem logisticInstTarget_armMean :
    logisticInstTarget.armMean 0 = 5 / 12 ∧ logisticInstTarget.armMean 1 = 2 / 3 ∧
      logisticInstTarget.armMean 2 = 7 / 12 := by
  have h : ∀ s, logisticInstTarget.armMean s =
      (∫ u, logisticInstTargetOutcome s false u ∂logisticInstNoise) / 4 +
        3 * (∫ u, logisticInstTargetOutcome s true u ∂logisticInstNoise) / 4 := fun s => by
    simp only [Population.armMean, logisticInstTarget]
    rw [integral_prod _ Integrable.of_finite, logisticInstTargetCov,
      integral_stratumLaw (fun v => by cases v <;> norm_num), standardizedRisk, Fintype.sum_bool]
    simp only [ite_true, ite_false, Bool.false_eq_true]
    ring
  refine ⟨?_, ?_, ?_⟩ <;> rw [h] <;>
    simp [integral_logisticInstNoise, logisticInstTargetOutcome, logisticInstOutcome] <;>
    norm_num

/-! ### The sample and the fit -/

/-- The record `((X, A), Y)` of a unit of the trial. -/
noncomputable def logisticInstRecord (ω : (Bool × Bool) × Fin 3) : ((Fin 1 → ℝ) × Bool) × ℝ :=
  ((logisticInstTrial.X ω, logisticInstTrial.A ω), logisticInstTrial.obsOutcome ω)

/-- The law of the sample: infinitely many independent copies of the trial. -/
noncomputable def logisticInstSampleLaw : Measure (ℕ → (Bool × Bool) × Fin 3) :=
  Measure.infinitePi fun _ => logisticInstTrial.μ

instance : IsProbabilityMeasure logisticInstSampleLaw := by
  unfold logisticInstSampleLaw; infer_instance

/-- The records of the sample. -/
noncomputable def logisticInstSample (i : ℕ) (ω : ℕ → (Bool × Bool) × Fin 3) :
    ((Fin 1 → ℝ) × Bool) × ℝ :=
  logisticInstRecord (ω i)

theorem map_logisticInstSample (i : ℕ) :
    logisticInstSampleLaw.map (logisticInstSample i) =
      logisticInstTrial.μ.map logisticInstRecord := by
  have : logisticInstSample i = logisticInstRecord ∘ fun x : ℕ → (Bool × Bool) × Fin 3 => x i :=
    rfl
  rw [this, ← Measure.map_map (g := logisticInstRecord) (measurable_of_finite _)
    (measurable_pi_apply i), logisticInstSampleLaw, Measure.infinitePi_map_eval]

/-- **The sample of the example is i.i.d.** -/
theorem isIIDSample_logisticInstSample :
    IsIIDSample logisticInstSample logisticInstSampleLaw where
  indep := iIndepFun_infinitePi (P := fun _ => logisticInstTrial.μ)
    fun _ => measurable_of_finite logisticInstRecord
  ident i := ⟨((measurable_of_finite logisticInstRecord).comp
      (measurable_pi_apply i)).aemeasurable,
    ((measurable_of_finite logisticInstRecord).comp (measurable_pi_apply 0)).aemeasurable,
    (map_logisticInstSample i).trans (map_logisticInstSample 0).symm⟩

/-- The parameter set of the fit: the closed ball of radius `4` around `0`. -/
noncomputable def logisticInstBall : Set (Option (Fin 1) ⊕ Option (Fin 1) → ℝ) :=
  Metric.closedBall 0 4

theorem logisticInstCoef_mem_ball : logisticInstCoef ∈ logisticInstBall := by
  have h1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num); linarith
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [logisticInstBall, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  rintro ((_ | _) | (_ | _)) <;> simp only [logisticInstCoef, Real.norm_eq_abs] <;>
    rw [abs_le] <;> constructor <;> linarith

/-- The logistic maximum likelihood fit of the example over `logisticInstBall`. -/
noncomputable def logisticInstFit (n : ℕ) (ω : ℕ → (Bool × Bool) × Fin 3) :
    Option (Fin 1) ⊕ Option (Fin 1) → ℝ :=
  glmMLE logisticDens (fun c => interactionDesign c.2 c.1) logisticInstBall logisticInstSample n ω

/-- **The fit of the example is consistent** for `ξ₀`. -/
theorem logisticInstFit_tendstoInMeasure :
    TendstoInMeasure logisticInstSampleLaw logisticInstFit atTop (fun _ => logisticInstCoef) :=
  logisticInst_logisticOutcomeModel.tendstoInMeasure logisticInstTrial_isRandomizedTwoArm
    (isCompact_closedBall _ _) logisticInstCoef_mem_ball isIIDSample_logisticInstSample
    (map_logisticInstSample 0)

/-! ### The limits -/

theorem logit_two_thirds : logit (2 / 3) = Real.log 2 := by
  rw [logit_eq_log_div]; norm_num

theorem logit_one_third : logit (1 / 3) = -Real.log 2 := by
  rw [logit_eq_log_div]; norm_num; rw [one_div, Real.log_inv]

theorem logit_five_twelfths : logit (5 / 12) = Real.log 5 - Real.log 7 := by
  rw [logit_eq_log_div, ← Real.log_div (by norm_num) (by norm_num)]; norm_num

theorem logit_seven_twelfths : logit (7 / 12) = Real.log 7 - Real.log 5 := by
  rw [logit_eq_log_div, ← Real.log_div (by norm_num) (by norm_num)]; norm_num

/-- **The target marginal log odds ratios**: `a` against `c` is `log (25/49)`, `b` against `a` is
`log (14/5)`, `c` against `b` is `log (7/10)`. -/
theorem logisticInstTarget_marginalEffect :
    logisticInstTarget.marginalEffect logit 2 0 = Real.log (25 / 49) ∧
      logisticInstTarget.marginalEffect logit 0 1 = Real.log (14 / 5) ∧
      logisticInstTarget.marginalEffect logit 1 2 = Real.log (7 / 10) := by
  obtain ⟨h0, h1, h2⟩ := logisticInstTarget_armMean
  have e1 : Real.log (25 / 49) = 2 * (Real.log 5 - Real.log 7) := by
    rw [show (25 / 49 : ℝ) = (5 / 7) ^ 2 by norm_num, Real.log_pow,
      Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  have e2 : Real.log (14 / 5) = Real.log 2 + Real.log 7 - Real.log 5 := by
    rw [show (14 / 5 : ℝ) = 2 * 7 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
  have e3 : Real.log (7 / 10) = Real.log 7 - Real.log 2 - Real.log 5 := by
    rw [show (7 / 10 : ℝ) = 7 / (2 * 5) by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num)]
    ring
  simp only [Population.marginalEffect, h0, h1, h2, logit_two_thirds, logit_five_twelfths,
    logit_seven_twelfths, e1, e2, e3]
  refine ⟨by ring, by ring, by ring⟩

/-- The logit is continuous at the three target arm means. -/
theorem logisticInst_continuousAt_logit (s : Fin 3) :
    ContinuousAt logit (logisticInstTarget.armMean s) := by
  obtain ⟨h0, h1, h2⟩ := logisticInstTarget_armMean
  fin_cases s
  · change ContinuousAt logit (logisticInstTarget.armMean 0)
    rw [h0]; exact continuousAt_logit ⟨by norm_num, by norm_num⟩
  · change ContinuousAt logit (logisticInstTarget.armMean 1)
    rw [h1]; exact continuousAt_logit ⟨by norm_num, by norm_num⟩
  · change ContinuousAt logit (logisticInstTarget.armMean 2)
    rw [h2]; exact continuousAt_logit ⟨by norm_num, by norm_num⟩

/-- **The standardized logistic marginal log odds ratio of the example is consistent.** The
marginal log odds ratio of the fitted surfaces of the arms `false ↦ c` and `true ↦ a`,
standardized to the target covariate law, converges in probability to `log (25/49)`. Every
hypothesis of `tendstoInMeasure_logistic_linkMarginal` is verified. -/
theorem logisticInst_linkMarginal :
    TendstoInMeasure logisticInstSampleLaw
      (fun n ω => linkMarginal logit logisticInstTarget.covLaw
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstFit n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω)))
      atTop (fun _ => Real.log (25 / 49)) := by
  rw [← logisticInstTarget_marginalEffect.1]
  exact tendstoInMeasure_logistic_linkMarginal (t₀ := false) (t₁ := true) (s₀ := 2) (s₁ := 0)
    logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    logisticInst_logisticOutcomeModel (isCompact_closedBall _ _) logisticInstCoef_mem_ball
    isIIDSample_logisticInstSample (map_logisticInstSample 0) (measurable_of_finite _)
    Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous (logisticInst_continuousAt_logit 2)
    (logisticInst_continuousAt_logit 0)

/-- The fitted logistic surface `(ξ, t, x) ↦ σ(z(x, t) ⬝ ξ)`. -/
noncomputable def logisticInstFitSurface (ξ : Option (Fin 1) ⊕ Option (Fin 1) → ℝ) (t : Bool)
    (x : Fin 1 → ℝ) : ℝ :=
  Real.sigmoid (interactionDesign t x ⬝ᵥ ξ)

/-- **The unanchored comparison of the example is consistent.** The arm `true` of the trial
stands for `a`; the reported mean of `b` in the target is the deterministic sequence
`2/3 + 1/(n + 1)`, which converges to the target mean `2/3` of `b`. The unanchored estimator
`logit(m̂_b) - logit(∫ σ(z(x, true) ⬝ ξ̂) dQ_X)` converges in probability to `log (14/5)`. Every
hypothesis of `tendstoInMeasure_unanchored_fit` is verified for the logistic fit. -/
theorem logisticInst_unanchored :
    TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) ω => logit (2 / 3 + 1 / ((n : ℝ) + 1)) -
        logit (∫ x, Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω)
          ∂logisticInstTarget.covLaw))
      atTop (fun _ => Real.log (14 / 5)) := by
  rw [← logisticInstTarget_marginalEffect.2.1]
  have hr := logisticSurface_regular (z := fun c => interactionDesign c.2 c.1)
    logisticInst_logisticOutcomeModel.measurable_z true logisticInstTarget.covLaw
  have hmb : TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) (_ : ℕ → (Bool × Bool) × Fin 3) => 2 / 3 + 1 / ((n : ℝ) + 1)) atTop
      (fun _ => logisticInstTarget.armMean 1) := by
    rw [logisticInstTarget_armMean.2.1]
    exact tendstoInMeasure_add_one_div_succ _ _
  exact tendstoInMeasure_unanchored_fit (h := logisticInstFitSurface) (t := true) (a := 0)
    (b := 1) logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    (logisticInst_logisticOutcomeModel.isOutcomeRegression logisticInstTrial_isRandomizedTwoArm
      fun _ => Integrable.of_finite) (measurable_of_finite _) Integrable.of_finite
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous
    (Eventually.of_forall fun ξ => (hr.1 ξ).aestronglyMeasurable) hr.2.1
    (Eventually.of_forall fun ξ => ae_of_all _ (hr.2.2.1 ξ))
    (ae_of_all _ fun x => (hr.2.2.2 x).continuousAt) logisticInstFit_tendstoInMeasure hmb
    (logisticInst_continuousAt_logit 0) (logisticInst_continuousAt_logit 1)

/-- **The anchored comparison of the example is consistent.** The trial compares `a` (arm
`true`) with the common comparator `c` (arm `false`); the reported contrast of `c` against `b` is
the deterministic sequence `log (7/10) + 1/(n + 1)`, which converges to the target marginal log
odds ratio `log (7/10)` of `c` against `b`. The anchored estimator converges in probability to
the target marginal log odds ratio `log (14/5)` of `b` against `a`. Every hypothesis of
`tendstoInMeasure_logistic_anchored` is verified. -/
theorem logisticInst_anchored :
    TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) ω => linkMarginal logit logisticInstTarget.covLaw
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω))
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstFit n ω)) -
          (Real.log (7 / 10) + 1 / ((n : ℝ) + 1)))
      atTop (fun _ => Real.log (14 / 5)) := by
  rw [← logisticInstTarget_marginalEffect.2.1]
  have hd : TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) (_ : ℕ → (Bool × Bool) × Fin 3) => Real.log (7 / 10) + 1 / ((n : ℝ) + 1))
      atTop (fun _ => logisticInstTarget.marginalEffect logit 1 2) := by
    rw [logisticInstTarget_marginalEffect.2.2]
    exact tendstoInMeasure_add_one_div_succ _ _
  exact tendstoInMeasure_logistic_anchored (ta := true) (tc := false) (a := 0) (b := 1) (c := 2)
    logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    logisticInst_logisticOutcomeModel (isCompact_closedBall _ _) logisticInstCoef_mem_ball
    isIIDSample_logisticInstSample (map_logisticInstSample 0) (measurable_of_finite _)
    Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    logisticInst_absolutelyContinuous hd (logisticInst_continuousAt_logit 0)
    (logisticInst_continuousAt_logit 2)

/-- The target covariate mean is `x̄ = 3/4`. -/
theorem logisticInstTarget_covMean : covMean logisticInstTarget.covLaw = fun _ => 3 / 4 := by
  funext k
  simp only [covMean, integral_logisticInstTarget_covLaw, logisticInstCov]
  norm_num

/-- **The averaging gaps of the two true surfaces** under the target covariate law: `log (7/5) -
log 2 / 2` for the reference arm and `log (5/7) + log 2 / 2` for the active arm; their
difference is `-log (50/49)`. -/
theorem logisticInst_averagingGap :
    averagingGap logit logisticInstTarget.covLaw (logisticInstSurface false) -
        averagingGap logit logisticInstTarget.covLaw (logisticInstSurface true) =
      -Real.log (50 / 49) := by
  have e : Real.log (50 / 49) = Real.log 2 + 2 * (Real.log 5 - Real.log 7) := by
    rw [show (50 / 49 : ℝ) = 2 * (5 / 7) ^ 2 by norm_num, Real.log_mul (by norm_num)
      (by norm_num), Real.log_pow, Real.log_div (by norm_num) (by norm_num)]
    push_cast; ring
  simp only [averagingGap, integral_logisticInstTarget_covLaw, logisticInstSurface,
    logisticInst_risk]
  norm_num
  rw [logit_seven_twelfths, logit_five_twelfths, logit_one_third, logit_two_thirds, e]
  ring

/-- **The conditional plug-in of the example converges to `-log 2`.** The fitted log odds ratio
`γ̂ + x̂ β̂₂` at a reported target covariate mean `x̂ = 3/4 + 1/(n + 1)` (a deterministic sequence
converging to `x̄ = 3/4`) converges in probability to `γ + x̄ β₂ = 2 log 2 - 3 log 2 = -log 2`.
Every hypothesis of `tendstoInMeasure_logistic_conditionalPlugIn` is verified; its limit
`Δ_Q + J(m₀) - J(m₁)` is computed as `log (25/49) - log (50/49)`. -/
theorem logisticInst_conditionalPlugIn :
    TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) ω => linkContrast logit
        (fun x => Real.sigmoid (interactionDesign false x ⬝ᵥ logisticInstFit n ω))
        (fun x => Real.sigmoid (interactionDesign true x ⬝ᵥ logisticInstFit n ω))
        (fun _ => 3 / 4 + 1 / ((n : ℝ) + 1)))
      atTop (fun _ => -Real.log 2) := by
  have hx : TendstoInMeasure logisticInstSampleLaw
      (fun (n : ℕ) (_ : ℕ → (Bool × Bool) × Fin 3) (_ : Fin 1) => 3 / 4 + 1 / ((n : ℝ) + 1))
      atTop (fun _ => covMean logisticInstTarget.covLaw) := by
    rw [logisticInstTarget_covMean]
    exact tendstoInMeasure_pi fun _ => tendstoInMeasure_add_one_div_succ _ _
  have h := tendstoInMeasure_logistic_conditionalPlugIn (s₀ := 2) (s₁ := 0)
    logisticInstTrial_isRandomizedTwoArm (fun _ => Integrable.of_finite)
    logisticInst_logisticOutcomeModel (isCompact_closedBall _ _) logisticInstCoef_mem_ball
    isIIDSample_logisticInstSample (map_logisticInstSample 0) (measurable_of_finite _)
    Integrable.of_finite Integrable.of_finite
    (logisticInst_structurallyInvariant false 2 logisticInstTarget_outcome_two)
    (logisticInst_structurallyInvariant true 0 logisticInstTarget_outcome_zero)
    logisticInst_absolutelyContinuous
    (fun _ => (integrable_map_measure (measurable_pi_apply _).aestronglyMeasurable
      (measurable_of_finite _).aemeasurable).2 Integrable.of_finite) hx
  have e : logisticInstTarget.marginalEffect logit 2 0 +
      (averagingGap logit logisticInstTarget.covLaw (logisticInstSurface false) -
        averagingGap logit logisticInstTarget.covLaw (logisticInstSurface true)) =
      -Real.log 2 := by
    rw [logisticInstTarget_marginalEffect.1, logisticInst_averagingGap,
      show (50 / 49 : ℝ) = 2 * (25 / 49) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [← e]
  exact h

/-- **The marginal and the conditional limits differ.** The standardized marginal log odds ratio
converges to `log (25/49)` and the conditional plug-in to `-log 2`; the difference is
`log (50/49)`, a number in `[1/50, 1/49]`, so the conditional plug-in is not consistent for the
marginal log odds ratio in this model. -/
theorem logisticInst_conditionalPlugIn_ne_linkMarginal :
    Real.log (25 / 49) - -Real.log 2 = Real.log (50 / 49) ∧ 1 / 50 ≤ Real.log (50 / 49) ∧
      Real.log (50 / 49) ≤ 1 / 49 ∧ Real.log (25 / 49) ≠ -Real.log 2 := by
  have e : Real.log (25 / 49) - -Real.log 2 = Real.log (50 / 49) := by
    rw [show (50 / 49 : ℝ) = 2 * (25 / 49) by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlo : 1 / 50 ≤ Real.log (50 / 49) := by
    have := Real.one_sub_inv_le_log_of_pos (x := 50 / 49) (by norm_num)
    norm_num at this ⊢; linarith
  have hhi : Real.log (50 / 49) ≤ 1 / 49 := by
    have := Real.log_le_sub_one_of_pos (x := 50 / 49) (by norm_num)
    norm_num at this ⊢; linarith
  refine ⟨e, hlo, hhi, fun h => ?_⟩
  rw [h, sub_self] at e
  linarith

end PopulationAdjustment

end CausalInference
