/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralTrial
public import CausalInference.PopulationAdjustment.CommonLimitLinear

/-!
# The common limit of weighting and standardization with random target moments

The common limit theorems of `CommonLimitLinear` fix the reported target moments `t` and assume
bounded features. Here the reported target moments are random, `tₙ = Gₙ(W)`, computed from data
`W` independent of the index sample (the reported summary of another study, or the mean of a
target sample), converging in probability to the target feature means `t`; the features may be
unbounded, under the interior condition and exponential moments of the trial feature law.

The two estimators use the same reported moments.

* The **weighted estimate** of arm `a`: the weighted arm mean with the entropy balancing weights
  at `tₙ` (`sampleBalancedArmMean`).
* The **standardized estimate** of arm `a` at the reported moments: the least squares fit `ξ̂` of
  the interaction design of the features, `z(a, x) = (1, φ(x), 1[a], 1[a]φ(x))`, evaluated at the
  reported feature means, `z(a, tₙ)ᵀξ̂ = α̂_a + β̂_aᵀ tₙ` (`reportedMomentsArmFit`).

Both converge in probability to `α_a + β_aᵀ t`, which is the target arm mean when the arm is
transported (`commonLimit_reportedMoments_armMean`), and their difference converges in
probability to `0`. The same holds for the unanchored comparison and the anchored comparison on a
link scale continuous at the target means (`commonLimit_reportedMoments_unanchored`,
`commonLimit_reportedMoments_anchored`), and for the anchored comparison on the identity scale
under relative constancy only (`commonLimit_reportedMoments_anchored_identity`).

**Conditions.** A randomized two arm trial with potential outcomes of finite second moments and a
regression linear in the interaction design of measurable features; an i.i.d. sample of its
records; the interior condition at `t` for the trial feature law with all exponential moments of
`‖φ(X) - t‖`; reported moments converging to `t` from independent data; a bounded conditional
residual variance of each arm used. The linear outcome model (finite second moments of the
design and a positive definite design second moment) is proved from these conditions
(`Trial.linearOutcomeModel_of_interior`); the regressions of the arms, the
square integrable residuals and the target conditional mean functions are proved as well.

## Main definitions

* `reportedMomentsArmFit`: the least squares fit of the interaction design at reported moments.

## Main results

* `posDef_featureInteractionDesign_gram_of_interior`,
  `Trial.linearOutcomeModel_of_interior`.
* `commonLimit_reportedMoments_arm`: both estimators of an arm converge to `α_a + β_aᵀ t`.
* `commonLimit_reportedMoments_armMean`, `commonLimit_reportedMoments_unanchored`,
  `commonLimit_reportedMoments_anchored`, `commonLimit_reportedMoments_anchored_identity`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* D. M. Phillippo, A. E. Ades, S. Dias, S. Palmer, K. R. Abrams and N. J. Welton, *Methods for
  population-adjusted indirect comparisons in health technology appraisal*, Medical Decision
  Making 38 (2018).
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

/-! ### The linear outcome model under the interior condition -/

section Model

variable {Ω₁ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] {p : ℕ}
  {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ} {T : Trial Ω₁ 𝒳 Bool}

/-- **The features have finite second moments under a finite exponential moment**: if
`E[exp ‖φ(X) - t‖] < ∞` under the covariate law, every coordinate of `φ(X)` is square integrable
in the trial. -/
theorem memLp_feature_of_integrable_exp [IsProbabilityMeasure T.μ] (hX : Measurable T.X)
    (hφ : Measurable φ)
    (hexp : Integrable (fun x => Real.exp (1 * ‖φ x - t‖)) T.covLaw) (j : Fin p) :
    MemLp (fun ω => φ (T.X ω) j) 2 T.μ := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hX
  have hsq : Integrable (fun x => ‖φ x - t‖ ^ 2) T.covLaw :=
    integrable_sq_norm_of_integrable_exp (g := fun x => ‖φ x - t‖) (hφ.sub_const t).norm
      (fun _ => norm_nonneg _) le_rfl hexp
  have hj : Measurable fun x => φ x j := (measurable_pi_apply j).comp hφ
  have h2 : MemLp (fun x => φ x j) 2 T.covLaw := by
    refine (memLp_two_iff_integrable_sq hj.aestronglyMeasurable).2 ?_
    refine ((hsq.const_mul 2).add (integrable_const (2 * ‖t‖ ^ 2))).mono'
      (hj.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : |φ x j| ≤ ‖φ x - t‖ + ‖t‖ :=
      calc |φ x j| = ‖φ x j‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖φ x‖ := norm_le_pi_norm (φ x) j
        _ = ‖(φ x - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖φ x - t‖ + ‖t‖ := norm_add_le _ _
    have h3 : φ x j ^ 2 ≤ (‖φ x - t‖ + ‖t‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖φ x - t‖ - ‖t‖)]
  rw [Population.covLaw] at h2
  exact (memLp_map_measure_iff (by rw [← Population.covLaw]; exact hj.aestronglyMeasurable)
    hX.aemeasurable).1 h2

/-- **The design second moment of the interaction design is positive definite under the interior
condition**, for features with a finite exponential moment, possibly unbounded: if
`z(A, X)ᵀv = 0` almost surely, randomization gives `z(a, X)ᵀv = 0` almost surely in each arm,
and the margin implied by the interior condition forces each affine function of the features to
vanish, so `v = 0`. -/
theorem posDef_featureInteractionDesign_gram_of_interior [IsProbabilityMeasure T.μ]
    (hT : T.IsRandomizedTwoArm) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : Integrable (fun x => Real.exp (1 * ‖φ x - t‖)) T.covLaw) :
    (Matrix.of fun j k => ∫ ω, featureInteractionDesign φ (T.A ω) (T.X ω) j *
      featureInteractionDesign φ (T.A ω) (T.X ω) k ∂T.μ).PosDef := by
  have : IsProbabilityMeasure T.covLaw := T.isProbabilityMeasure_covLaw hT.measurable_X
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin_of_mem_interior_map (ν := T.covLaw) hφ hint
  have hφX := memLp_feature_of_integrable_exp hT.measurable_X hφ hexp
  have hz2 : ∀ a k, MemLp (fun ω => featureInteractionDesign φ a (T.X ω) k) 2 T.μ := by
    intro a k
    rcases k with (_ | j) | (_ | j) <;> cases a <;>
      simp only [featureInteractionDesign, interactionDesign, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact memLp_const _ | exact hφX j
  have hd2 : ∀ k, MemLp (fun ω => featureInteractionDesign φ (T.A ω) (T.X ω) k) 2 T.μ :=
    fun k => memLp_two_select (f := fun a ω => featureInteractionDesign φ a (T.X ω) k)
      hT.measurable_A (fun a => (measurable_featureInteractionDesign hφ a k).comp hT.measurable_X)
      fun a => hz2 a k
  refine posDef_gram_of_ae hd2 fun v hv => ?_
  have hsm : ∀ a, Measurable fun x => featureInteractionDesign φ a x ⬝ᵥ v := fun a =>
    Finset.measurable_sum _ fun k _ => (measurable_featureInteractionDesign hφ a k).mul_const _
  have harm : ∀ a : Bool, ∀ᵐ x ∂T.covLaw, featureInteractionDesign φ a x ⬝ᵥ v = 0 := by
    intro a
    have hS : MeasurableSet {x | ¬ featureInteractionDesign φ a x ⬝ᵥ v = 0} :=
      (measurableSet_eq_fun (hsm a) measurable_const).compl
    rw [ae_iff, Population.covLaw, Measure.map_apply hT.measurable_X hS]
    have h0 : T.μ (T.X ⁻¹' {x | ¬ featureInteractionDesign φ a x ⬝ᵥ v = 0} ∩ T.A ⁻¹' {a}) = 0 :=
      measure_mono_null (fun ω hω => by
        obtain ⟨h1, h2⟩ := hω
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff] at h1 h2 ⊢
        rw [h2]; exact h1) (ae_iff.1 hv)
    rw [hT.indepFun_X_A.measure_inter_preimage_eq_mul _ _ hS (measurableSet_singleton a)]
      at h0
    have hpa : T.μ (T.A ⁻¹' {a}) ≠ 0 := by
      intro h
      have := hT.prob_arm_pos a
      rw [measureReal_def, h, ENNReal.toReal_zero] at this
      exact lt_irrefl _ this
    exact (mul_eq_zero.1 h0).resolve_right hpa
  have hf := eq_zero_of_ae_affine_of_margin hφ hδ hmargin ((harm false).mono fun x hx => by
    rw [featureInteractionDesign_dotProduct] at hx; simpa using hx)
  have ht := eq_zero_of_ae_affine_of_margin hφ hδ hmargin
    (c := interactionIntercept v + interactionEffect v)
    (w := interactionMain v + interactionModifier v) ((harm true).mono fun x hx => by
      rw [featureInteractionDesign_dotProduct] at hx; simpa [add_dotProduct] using hx)
  obtain ⟨hmain, hint0⟩ := hf
  obtain ⟨hmod, heff⟩ := ht
  rw [hint0, zero_add] at heff
  rw [hmain, zero_add] at hmod
  funext k
  rcases k with (_ | j) | (_ | j)
  · exact hint0
  · exact congrFun hmain j
  · exact heff
  · exact congrFun hmod j

/-- **A randomized trial with a regression linear in the interaction design of the features is a
linear outcome model under the interior condition**, for measurable features with a finite
exponential moment `E[exp ‖φ(X) - t‖]`, possibly unbounded, and potential outcomes of finite
second moments. -/
theorem _root_.CausalInference.IndirectComparison.Trial.linearOutcomeModel_of_interior
    [IsProbabilityMeasure T.μ] (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hφ : Measurable φ) (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : Integrable (fun x => Real.exp (1 * ‖φ x - t‖)) T.covLaw)
    {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ}
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀) :
    T.LinearOutcomeModel (featureInteractionDesign φ) ξ₀ where
  measurable_z a k := measurable_featureInteractionDesign hφ a k
  memLp_z a k := by
    have hφX := memLp_feature_of_integrable_exp hT.measurable_X hφ hexp
    rcases k with (_ | j) | (_ | j) <;> cases a <;>
      simp only [featureInteractionDesign, interactionDesign, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact memLp_const _ | exact hφX j
  memLp_Y := hY2
  posDef := posDef_featureInteractionDesign_gram_of_interior hT hφ hint hexp
  isOutcomeRegression := hreg

end Model

/-! ### The two estimators of an arm at reported moments -/

section Arm

variable {Ω₁ Ξ 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ξ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲} {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **The standardized estimate of arm `a` at reported feature means `s`**: the least squares fit
`ξ̂` of the interaction design of the features evaluated at `s`, `z(a, s)ᵀξ̂ = α̂_a + β̂_aᵀ s`. -/
noncomputable def reportedMomentsArmFit (φ : 𝒳 → Fin p → ℝ) (O : ℕ → Ξ → 𝒳 × Bool × ℝ)
    (s : Fin p → ℝ) (a : Bool) (n : ℕ) (ω : Ξ) : ℝ :=
  interactionDesign a s ⬝ᵥ leastSquaresFit (recordDesign (featureInteractionDesign φ))
    recordResponse O n ω

omit [MeasurableSpace 𝒳] in
/-- The interaction design is continuous in the covariate vector. -/
theorem continuous_interactionDesign (a : Bool) :
    Continuous fun s : Fin p → ℝ => interactionDesign a s := by
  refine continuous_pi fun k => ?_
  rcases k with (_ | j) | (_ | j) <;> cases a <;>
    simp only [interactionDesign, Bool.false_eq_true, ↓reduceIte]
  all_goals first | exact continuous_const | exact continuous_apply j

/-- **Both estimators of an arm converge to `α_a + β_aᵀ t` at random reported moments.** Let `T`
be a randomized two arm trial whose potential outcomes have finite second moments and whose
regression is linear in the interaction design of measurable features,
`E[Y | X, A] = z(A, X)ᵀξ₀`; let the interior condition at `t` hold for the trial feature law with
all exponential moments of `‖φ(X) - t‖`, and the conditional residual variance of arm `a` be
bounded. Let `O` be a measurable i.i.d. sample of the records, and `tₙ = Gₙ(W) → t` in
probability with `W` independent of the sample. Then the weighted arm mean and the standardized
estimate `z(a, tₙ)ᵀξ̂`, both at the reported moments `tₙ`, converge in probability to
`z(a, t)ᵀξ₀ = α_a + β_aᵀ t`. -/
theorem commonLimit_reportedMoments_arm [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) (a : Bool) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω)
        (interactionDesign a t ⬝ᵥ ξ₀) P ∧
      TendstoInMeasure P (fun n ω => reportedMomentsArmFit φ O (G n (W ω)) a n ω) atTop
        (fun _ => interactionDesign a t ⬝ᵥ ξ₀) := by
  have hM := T.linearOutcomeModel_of_interior hT hY2 hφ hint (hexp 1) hreg
  have hYo : Measurable T.obsOutcome :=
    measurable_obsOutcome (A := T.A) (Y := T.Y) hT.measurable_A hT.measurable_Y
  have hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ := by
    cases a
    · exact hT.indepFun.comp measurable_id (measurable_fst.prodMk measurable_snd.fst)
    · exact hT.indepFun.comp measurable_id (measurable_fst.prodMk measurable_snd.snd)
  have hm : T.IsCondMean a (fun x => featureInteractionDesign φ a x ⬝ᵥ ξ₀) :=
    hT.isCondMean hM.integrable_Y hM.isOutcomeRegression a
  have hres2 : Integrable (fun ω => (T.Y a ω - featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) ^ 2)
      T.μ := by
    have hd2 : MemLp (fun ω => featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) 2 T.μ := by
      simp only [dotProduct]
      exact memLp_finsetSum _ fun j _ => (hM.memLp_z a j).mul_const _
    exact ((hY2 a).sub hd2).integrable_sq
  have hval : (interactionIntercept ξ₀ + if a then interactionEffect ξ₀ else 0) +
      (interactionMain ξ₀ + if a then interactionModifier ξ₀ else 0) ⬝ᵥ t =
        interactionDesign a t ⬝ᵥ ξ₀ :=
    (featureInteractionDesign_dotProduct (fun s => s) a t ξ₀).symm
  have hW1 := sampleBalancedArmMean_isConsistent_trial_general hT.measurable_X hT.measurable_A
    hYo a (hT.measurable_Y a) hrand hO hOm hlaw hφ hint hexp hW hWO hG htm (hT.prob_arm_pos a)
    hm hres2 hvar (featureInteractionDesign_dotProduct φ a · ξ₀)
  rw [hval] at hW1
  refine ⟨hW1, ?_⟩
  have hc : Continuous fun q : (Option (Fin p) ⊕ Option (Fin p) → ℝ) × (Fin p → ℝ) =>
      interactionDesign a q.2 ⬝ᵥ q.1 :=
    ((continuous_interactionDesign a).comp continuous_snd).dotProduct continuous_fst
  exact ((hM.tendstoInMeasure hT hO hlaw).prodMk htm).comp_continuousAt hc.continuousAt

omit [MeasurableSpace 𝒳] in
/-- The mean of the regression of the interaction design under a law with integrable features of
means `t` is the design at `t`: `∫ z(a, x)ᵀξ dν = z(a, t)ᵀξ`; the regression is integrable. -/
theorem integral_featureInteractionDesign_dotProduct [MeasurableSpace 𝒳] {ν : Measure 𝒳}
    [IsProbabilityMeasure ν] (hφi : ∀ k, Integrable (fun x => φ x k) ν)
    (ht : ∀ k, ∫ x, φ x k ∂ν = t k) (a : Bool) (ξ : Option (Fin p) ⊕ Option (Fin p) → ℝ) :
    Integrable (fun x => featureInteractionDesign φ a x ⬝ᵥ ξ) ν ∧
      ∫ x, featureInteractionDesign φ a x ⬝ᵥ ξ ∂ν = interactionDesign a t ⬝ᵥ ξ := by
  have e : (fun x => featureInteractionDesign φ a x ⬝ᵥ ξ) = fun x =>
      (interactionIntercept ξ + if a then interactionEffect ξ else 0) +
        (interactionMain ξ + if a then interactionModifier ξ else 0) ⬝ᵥ φ x :=
    funext fun x => featureInteractionDesign_dotProduct φ a x ξ
  rw [e, integral_affine_features_of_integrable hφi ht,
    ← featureInteractionDesign_dotProduct (fun s => s) a t ξ]
  exact ⟨(integrable_const _).add (integrable_finsetSum _ fun k _ => (hφi k).const_mul _), rfl⟩

end Arm

/-! ### The target quantities -/

section Target

variable {Ω₁ Ω₂ Ξ 𝒳 ι 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool}
  {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ}
  {t : Fin p → ℝ} {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲}
  {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **Weighting and standardization at random reported moments share their limit: the target
arm mean.** Under the conditions of `commonLimit_reportedMoments_arm` for arm `a`, let `Q` be a
target population with probability law, measurable covariates, integrable features of means `t`,
integrable `Y(s)`, absolute constancy of arm `a` of the trial and treatment `s` of the target, and
overlap `Q_X ≪ T_X`. Then the weighted arm mean and the standardized estimate `z(a, tₙ)ᵀξ̂` at the
random reported moments `tₙ` both converge in probability to `E_Q[Y(s)]`, and their difference
converges in probability to `0`. -/
theorem commonLimit_reportedMoments_armMean [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ)
    (hφ : Measurable φ) (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) (a : Bool) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - featureInteractionDesign φ a (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {s : ι} (hYQ : Integrable (Q.Y s) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y a) Q.μ Q.X (Q.Y s)) (hov : Q.covLaw ≪ T.covLaw) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (Q.armMean s) P ∧
      TendstoInMeasure P (fun n ω => reportedMomentsArmFit φ O (G n (W ω)) a n ω) atTop
        (fun _ => Q.armMean s) ∧
      TendstoInMeasure P (fun n ω => reportedMomentsArmFit φ O (G n (W ω)) a n ω -
        sampleBalancedArmMean φ (G n (W ω)) O a n ω) atTop (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  have hM := T.linearOutcomeModel_of_interior hT hY2 hφ hint (hexp 1) hreg
  obtain ⟨hW1, hS1⟩ := commonLimit_reportedMoments_arm hT hY2 hφ hint hexp hreg hO hOm hlaw hW
    hWO hG htm a hvar
  have hlim : interactionDesign a t ⬝ᵥ ξ₀ = Q.armMean s := by
    rw [← (hM.isCondMean_target hT hX₂ hsi hov).integral_eq hX₂ hYQ]
    exact ((integral_featureInteractionDesign_dotProduct hQφ ht a ξ₀).2).symm
  rw [hlim] at hW1 hS1
  exact ⟨hW1, hS1, tendstoInMeasure_sub_zero_of_same_limit hS1 hW1⟩

/-- **The unanchored comparisons at random reported moments share their limit.** Under the
hypotheses of `commonLimit_reportedMoments_armMean` for the index arm `true ↦ a`, with a reported
mean `m̂_b` of treatment `b` converging in probability to `E_Q[Y(b)]` and a link `g` continuous at
the two target means, the weighted comparison `g(m̂_b) - g(μ̂_true)` and the standardized
comparison `g(m̂_b) - g(z(true, tₙ)ᵀξ̂)` both converge in probability to the target marginal effect
of `b` relative to `a`, and their difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_unanchored [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y true ω - featureInteractionDesign φ true (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b : ι} (hYQ : Integrable (Q.Y a) Q.μ)
    (hsi : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a)) (hov : Q.covLaw ≪ T.covLaw)
    {mb : ℕ → Ξ → ℝ} (hmb : TendstoInMeasure P mb atTop fun _ => Q.armMean b) {g : ℝ → ℝ}
    (hga : ContinuousAt g (Q.armMean a)) (hgb : ContinuousAt g (Q.armMean b)) :
    IsConsistent (fun n ω => g (mb n ω) - g (sampleBalancedArmMean φ (G n (W ω)) O true n ω))
        (Q.marginalEffect g a b) P ∧
      TendstoInMeasure P (fun n ω => g (mb n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) atTop
        (fun _ => Q.marginalEffect g a b) ∧
      TendstoInMeasure P (fun n ω => (g (mb n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) -
          (g (mb n ω) - g (sampleBalancedArmMean φ (G n (W ω)) O true n ω))) atTop
        (fun _ => 0) := by
  obtain ⟨hW1, hS1, -⟩ := commonLimit_reportedMoments_armMean hT hY2 hφ hint hexp hreg hO hOm
    hlaw hW hWO hG htm true hvar hX₂ hQφ ht hYQ hsi hov
  have hW' := (hmb.comp_continuousAt hgb).sub (hW1.comp_continuousAt hga)
  have hS' := (hmb.comp_continuousAt hgb).sub (hS1.comp_continuousAt hga)
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

/-- **The anchored comparisons on a link scale at random reported moments share their limit.**
Under the hypotheses of `commonLimit_reportedMoments_armMean` for both arms, `true ↦ a` and
`false ↦ c` (both arms transported, both conditional residual variances bounded), with a reported
contrast `d̂_bc` converging in probability to the target marginal effect of `c` relative to `b`,
and a link `g` continuous at the target means of `a` and `c`, the weighted anchored comparison
`(g(μ̂_false) - g(μ̂_true)) - d̂_bc` and the standardized anchored comparison
`(g(z(false, tₙ)ᵀξ̂) - g(z(true, tₙ)ᵀξ̂)) - d̂_bc` both converge in probability to the target
marginal effect of `b` relative to `a`, and their difference converges in probability to `0`. -/
theorem commonLimit_reportedMoments_anchored [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) {σ2 : ℝ}
    (hvar : ∀ e : Bool, T.μ[fun ω => (T.Y e ω - featureInteractionDesign φ e (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hsia : StructurallyInvariant T.μ T.X (T.Y true) Q.μ Q.X (Q.Y a))
    (hsic : StructurallyInvariant T.μ T.X (T.Y false) Q.μ Q.X (Q.Y c))
    (hov : Q.covLaw ≪ T.covLaw) {dbc : ℕ → Ξ → ℝ} {g : ℝ → ℝ}
    (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect g b c)
    (hga : ContinuousAt g (Q.armMean a)) (hgc : ContinuousAt g (Q.armMean c)) :
    IsConsistent (fun n ω => (g (sampleBalancedArmMean φ (G n (W ω)) O false n ω) -
        g (sampleBalancedArmMean φ (G n (W ω)) O true n ω)) - dbc n ω)
        (Q.marginalEffect g a b) P ∧
      TendstoInMeasure P (fun n ω => (g (reportedMomentsArmFit φ O (G n (W ω)) false n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) - dbc n ω) atTop
        (fun _ => Q.marginalEffect g a b) ∧
      TendstoInMeasure P (fun n ω => ((g (reportedMomentsArmFit φ O (G n (W ω)) false n ω) -
        g (reportedMomentsArmFit φ O (G n (W ω)) true n ω)) - dbc n ω) -
          ((g (sampleBalancedArmMean φ (G n (W ω)) O false n ω) -
            g (sampleBalancedArmMean φ (G n (W ω)) O true n ω)) - dbc n ω)) atTop
        (fun _ => 0) := by
  obtain ⟨hWa, hSa, -⟩ := commonLimit_reportedMoments_armMean hT hY2 hφ hint hexp hreg hO hOm
    hlaw hW hWO hG htm true (hvar true) hX₂ hQφ ht hYQa hsia hov
  obtain ⟨hWc, hSc, -⟩ := commonLimit_reportedMoments_armMean hT hY2 hφ hint hexp hreg hO hOm
    hlaw hW hWO hG htm false (hvar false) hX₂ hQφ ht hYQc hsic hov
  have hlim : g (Q.armMean c) - g (Q.armMean a) - Q.marginalEffect g b c =
      Q.marginalEffect g a b := by
    simp only [Population.marginalEffect]; ring
  have hW' := isConsistent_link_contrast hWa hWc hdbc hga hgc
  have hS' := isConsistent_link_contrast hSa hSc hdbc hga hgc
  rw [hlim] at hW' hS'
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

/-- **The anchored comparisons on the identity scale at random reported moments share their
limit under relative constancy only.** Under the conditions of `commonLimit_reportedMoments_arm`
for both arms (no constancy of the arms themselves), let the conditional contrast
`z(false, ·)ᵀξ₀ - z(true, ·)ᵀξ₀` of the trial be the conditional mean of `Y(c) - Y(a)` in a
target population `Q` with probability law, measurable covariates, integrable features of means
`t` and integrable `Y(a)`, `Y(c)` (relative constancy on the identity scale). With a reported
contrast `d̂_bc` converging in probability to `E_Q[Y(c)] - E_Q[Y(b)]`, the weighted and the
standardized anchored comparisons on the identity scale at the random reported moments both
converge in probability to `E_Q[Y(b)] - E_Q[Y(a)]`, and their difference converges in probability
to `0`. -/
theorem commonLimit_reportedMoments_anchored_identity [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q.μ] (hT : T.IsRandomizedTwoArm)
    (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    (hreg : IsOutcomeRegression T.μ T.A T.X T.obsOutcome
      fun a x => featureInteractionDesign φ a x ⬝ᵥ ξ₀)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P) (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t)) {σ2 : ℝ}
    (hvar : ∀ e : Bool, T.μ[fun ω => (T.Y e ω - featureInteractionDesign φ e (T.X ω) ⬝ᵥ ξ₀) ^ 2 |
      MeasurableSpace.comap T.X inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    (hX₂ : Measurable Q.X) (hQφ : ∀ k, Integrable (fun x => φ x k) Q.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂Q.covLaw = t k) {a b c : ι} (hYQa : Integrable (Q.Y a) Q.μ)
    (hYQc : Integrable (Q.Y c) Q.μ)
    (hrel : (fun ω => featureInteractionDesign φ false (Q.X ω) ⬝ᵥ ξ₀ -
        featureInteractionDesign φ true (Q.X ω) ⬝ᵥ ξ₀) =ᵐ[Q.μ]
      Q.μ[fun ω => Q.Y c ω - Q.Y a ω | MeasurableSpace.comap Q.X inferInstance])
    {dbc : ℕ → Ξ → ℝ} (hdbc : TendstoInMeasure P dbc atTop fun _ => Q.marginalEffect id b c) :
    IsConsistent (fun n ω => (sampleBalancedArmMean φ (G n (W ω)) O false n ω -
        sampleBalancedArmMean φ (G n (W ω)) O true n ω) - dbc n ω)
        (Q.marginalEffect id a b) P ∧
      TendstoInMeasure P (fun n ω => (reportedMomentsArmFit φ O (G n (W ω)) false n ω -
        reportedMomentsArmFit φ O (G n (W ω)) true n ω) - dbc n ω) atTop
        (fun _ => Q.marginalEffect id a b) ∧
      TendstoInMeasure P (fun n ω => ((reportedMomentsArmFit φ O (G n (W ω)) false n ω -
        reportedMomentsArmFit φ O (G n (W ω)) true n ω) - dbc n ω) -
          ((sampleBalancedArmMean φ (G n (W ω)) O false n ω -
            sampleBalancedArmMean φ (G n (W ω)) O true n ω) - dbc n ω)) atTop
        (fun _ => 0) := by
  have : IsProbabilityMeasure Q.covLaw := Q.isProbabilityMeasure_covLaw hX₂
  obtain ⟨hWt, hSt⟩ := commonLimit_reportedMoments_arm hT hY2 hφ hint hexp hreg hO hOm hlaw hW
    hWO hG htm true (hvar true)
  obtain ⟨hWf, hSf⟩ := commonLimit_reportedMoments_arm hT hY2 hφ hint hexp hreg hO hOm hlaw hW
    hWO hG htm false (hvar false)
  obtain ⟨hif, hef⟩ := integral_featureInteractionDesign_dotProduct hQφ ht false ξ₀
  obtain ⟨hit, het⟩ := integral_featureInteractionDesign_dotProduct hQφ ht true ξ₀
  have hid : ∫ ω, (Q.Y c ω - Q.Y a ω) ∂Q.μ =
      ∫ x, (featureInteractionDesign φ false x ⬝ᵥ ξ₀ - featureInteractionDesign φ true x ⬝ᵥ ξ₀)
        ∂Q.covLaw :=
    Transport.integral_eq_integral_map_of_condExp (Y := fun ω => Q.Y c ω - Q.Y a ω)
      (f := fun x => featureInteractionDesign φ false x ⬝ᵥ ξ₀ -
        featureInteractionDesign φ true x ⬝ᵥ ξ₀) hX₂ (hYQc.sub hYQa)
      ((measurable_linearSurface (measurable_featureInteractionDesign hφ) ξ₀ false).sub
        (measurable_linearSurface (measurable_featureInteractionDesign hφ) ξ₀ true)) hrel
  rw [integral_sub hYQc hYQa, integral_sub hif hit, hef, het] at hid
  have hval : id (interactionDesign false t ⬝ᵥ ξ₀) - id (interactionDesign true t ⬝ᵥ ξ₀) -
      Q.marginalEffect id b c = Q.marginalEffect id a b := by
    simp only [Population.marginalEffect, Population.armMean, id] at hid ⊢
    linarith
  have hW' := isConsistent_link_contrast hWt hWf hdbc continuousAt_id continuousAt_id
  have hS' := isConsistent_link_contrast hSt hSf hdbc continuousAt_id continuousAt_id
  rw [hval] at hW' hS'
  exact ⟨hW', hS', tendstoInMeasure_sub_zero_of_same_limit hS' hW'⟩

end Target

end PopulationAdjustment

end CausalInference
