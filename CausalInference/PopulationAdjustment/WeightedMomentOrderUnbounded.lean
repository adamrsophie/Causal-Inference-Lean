/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderCommonLimit
public import CausalInference.PopulationAdjustment.WeightedMomentOrderInstances
public import CausalInference.PopulationAdjustment.CommonLimitExamples

/-!
# The common limit of weighting and standardization with an unbounded feature

The common limit theorems under one exponential moment
(`commonLimit_reportedMoments_arm_of_isMinOn`, `_armMean_of_isMinOn`, `_unanchored_of_isMinOn`)
are instantiated here on a trial with an unbounded feature whose exponential moments of high order
are infinite.

**The trial.** The coin trial over the standard exponential feature law
(`sharpInstTrial momentOrderExpLaw sharpInstOutcome`): `X` is standard exponential, the
assignment is a fair coin independent of `X`, and `Y(true) = 1 + 2X`, `Y(false) = X`. The
regression is linear in the interaction design `z(a, x)` with the coefficients `ξ₀`: intercept
`0`, main effect `1`, treatment effect `1`, interaction `1` (`commonLimitExampleCoef`). The trial
is a randomized two arm trial (`isRandomizedTwoArm_sharpInstTrial`), the regression is the
outcome regression (`unboundedInst_regression`), and both potential outcomes are square
integrable (`unboundedInst_memLp`).

**The target.** The covariate of the target population is uniform on `[1, 2]`
(`unboundedInstTarget`), with mean `3/2`; its law is absolutely continuous with respect to the
exponential law (`unboundedInstTarget_absolutelyContinuous`), and both arms are transported.

**The limits.** At `t = 3/2` the population dual minimizer is `β* = 1/3` and the moment of order
`κ = 3/4 > 2 β* = 2/3` is finite, while `E[exp(κ |X - t|)] = ∞` for `κ ≥ 1`. With reported moments
`tₙ = 3/2 + 1/(n + 1) → 3/2`:

* both estimators of arm `true` converge in probability to `1 + 2 · 3/2 = 4`
  (`unboundedInst_arm`), and this is the target mean `E_Q[Y(true)] = 4`
  (`unboundedInst_armMean`);
* with the target mean `E_Q[Y(false)] = 3/2` reported exactly, both unanchored comparisons of
  `false` against `true` converge in probability to `3/2 - 4 = -5/2`
  (`unboundedInst_unanchored`).

## Main definitions

* `unboundedInstReported`, `unboundedInstTarget`.

## Main results

* `isRandomizedTwoArm_sharpInstTrial`, `sharpInstTrial_isOutcomeRegression`.
* `unboundedInst_regression`, `unboundedInst_memLp`, `unboundedInst_variance`.
* `unboundedInst_arm`, `unboundedInst_armMean`, `unboundedInst_unanchored`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport
open scoped ENNReal

/-! ### The coin trial as a randomized two arm trial -/

section CoinTrial

variable {p : ℕ} {lam : Measure (Fin p → ℝ)} {f : Bool → (Fin p → ℝ) → ℝ}

/-- **The coin trial is a randomized two arm trial** for measurable outcome functions. -/
theorem isRandomizedTwoArm_sharpInstTrial [IsProbabilityMeasure lam]
    (hf : ∀ a, Measurable (f a)) : (sharpInstTrial lam f).IsRandomizedTwoArm where
  measurable_X := measurable_fst
  measurable_A := measurable_snd
  measurable_Y a := (hf a).comp measurable_fst
  indepFun := by
    have h := indepFun_prod (μ := lam) (ν := halfLaw) (X := (id : (Fin p → ℝ) → (Fin p → ℝ)))
      (Y := (id : Bool → Bool)) measurable_id measurable_id
    exact h.symm.comp measurable_id
      (measurable_id.prodMk ((hf false).prodMk (hf true)))
  prob_pos := by rw [sharpInstTrial_prob_arm]; norm_num
  prob_lt_one := by rw [sharpInstTrial_prob_arm]; norm_num

/-- **The outcome functions are the outcome regression of the coin trial**: for measurable and
integrable `f a`, `E[Y | X, A] = f A X`. -/
theorem sharpInstTrial_isOutcomeRegression [IsProbabilityMeasure lam]
    (hf : ∀ a, Measurable (f a)) (hfi : ∀ a, Integrable (f a) lam) :
    IsOutcomeRegression (sharpInstTrial lam f).μ (sharpInstTrial lam f).A
      (sharpInstTrial lam f).X (sharpInstTrial lam f).obsOutcome f := by
  refine ⟨hf, ?_⟩
  set T := sharpInstTrial lam f
  have hq : Measurable fun q : (Fin p → ℝ) × Bool => f q.2 q.1 :=
    measurable_from_prod_countable_left fun a => hf a
  have heq : T.obsOutcome = fun ω => (fun q : (Fin p → ℝ) × Bool => f q.2 q.1) (T.X ω, T.A ω) :=
    rfl
  have hle : MeasurableSpace.comap (fun ω => (T.X ω, T.A ω)) inferInstance ≤
      (inferInstance : MeasurableSpace ((Fin p → ℝ) × Bool)) :=
    (measurable_fst.prodMk measurable_snd).comap_le
  have hm : StronglyMeasurable[MeasurableSpace.comap (fun ω => (T.X ω, T.A ω)) inferInstance]
      T.obsOutcome := by
    rw [heq]; exact (hq.comp (comap_measurable _)).stronglyMeasurable
  have hi : Integrable T.obsOutcome T.μ := by
    have h1 : Integrable (fun ω : (Fin p → ℝ) × Bool => f true ω.1) T.μ :=
      (hfi true).comp_fst halfLaw
    have h0 : Integrable (fun ω : (Fin p → ℝ) × Bool => f false ω.1) T.μ :=
      (hfi false).comp_fst halfLaw
    refine (h1.norm.add h0.norm).mono' (hq.comp
      (measurable_fst.prodMk measurable_snd)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    change ‖f ω.2 ω.1‖ ≤ ‖f true ω.1‖ + ‖f false ω.1‖
    cases ω.2 <;> simp
  rw [condExp_of_stronglyMeasurable hle hm hi]
  exact Filter.EventuallyEq.of_eq rfl

end CoinTrial

/-! ### The exponential instance -/

section Instance

/-- The reported feature means `tₙ = 3/2 + 1/(n + 1)` of the instances. -/
noncomputable def unboundedInstReported (n : ℕ) : Fin 1 → ℝ :=
  featureLineVec (3 / 2 + 1 / ((n : ℝ) + 1))

theorem tendsto_unboundedInstReported :
    Tendsto unboundedInstReported atTop (𝓝 (featureLineVec (3 / 2))) :=
  tendsto_pi_nhds.2 fun _ => by
    simpa [unboundedInstReported, featureLineVec] using
      (tendsto_const_nhds (x := (3 / 2 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem tendstoInMeasure_unboundedInstReported :
    TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
      (fun n (_ : ℕ → (Fin 1 → ℝ) × Bool) => unboundedInstReported n) atTop
      (fun _ => featureLineVec (3 / 2)) :=
  tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    (ae_of_all _ fun _ => tendsto_unboundedInstReported)

/-- The outcomes of the instance are the regression of the interaction design with the
coefficients `commonLimitExampleCoef`: `z(true, x)ᵀξ₀ = 1 + 2x` and `z(false, x)ᵀξ₀ = x`. -/
theorem featureInteractionDesign_dotProduct_sharpInstOutcome (a : Bool) (x : Fin 1 → ℝ) :
    featureInteractionDesign id a x ⬝ᵥ commonLimitExampleCoef = sharpInstOutcome a x := by
  have hI : interactionIntercept commonLimitExampleCoef = 0 := by
    simp [interactionIntercept, commonLimitExampleCoef]
  have hE : interactionEffect commonLimitExampleCoef = 1 := by
    simp [interactionEffect, commonLimitExampleCoef]
  have hM : interactionMain commonLimitExampleCoef = fun _ => 1 := funext fun j => by
    simp [interactionMain, commonLimitExampleCoef]
  have hD : interactionModifier commonLimitExampleCoef = fun _ => 1 := funext fun j => by
    simp [interactionModifier, commonLimitExampleCoef]
  rw [featureInteractionDesign_dotProduct, hI, hE, hM, hD]
  cases a <;> simp only [sharpInstOutcome, dotProduct, Fin.sum_univ_one, Bool.false_eq_true,
    ↓reduceIte, Pi.add_apply, Pi.zero_apply, id] <;> ring

theorem integrable_sharpInstOutcome_momentOrderExpLaw (a : Bool) :
    Integrable (sharpInstOutcome a) momentOrderExpLaw := by
  have hexp := (integrable_exp_momentOrderExpLaw_iff (3 / 2) (3 / 4)).2 (by norm_num)
  cases a
  · rw [show sharpInstOutcome false = fun x => 0 + featureLineVec 1 ⬝ᵥ x from
      funext fun x => by simp [sharpInstOutcome, featureLineVec, dotProduct]]
    exact integrable_affine_of_integrable_exp_pos (by norm_num) hexp 0 _
  · rw [show sharpInstOutcome true = fun x => 1 + featureLineVec 2 ⬝ᵥ x from
      funext sharpInstOutcome_true]
    exact integrable_affine_of_integrable_exp_pos (by norm_num) hexp 1 _

/-- **The regression of the instance is the outcome regression**, linear in the interaction
design. -/
theorem unboundedInst_regression :
    IsOutcomeRegression (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).A
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).X
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).obsOutcome
      fun a x => featureInteractionDesign id a x ⬝ᵥ commonLimitExampleCoef := by
  have h := sharpInstTrial_isOutcomeRegression measurable_sharpInstOutcome
    integrable_sharpInstOutcome_momentOrderExpLaw
  have he : (fun a x => featureInteractionDesign id a x ⬝ᵥ commonLimitExampleCoef) =
      sharpInstOutcome := funext fun a => funext fun x =>
    featureInteractionDesign_dotProduct_sharpInstOutcome a x
  rwa [he]

/-- **Both potential outcomes of the instance are square integrable**: they are affine in the
exponential covariate, whose coordinates are square integrable. -/
theorem unboundedInst_memLp (a : Bool) :
    MemLp ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).Y a) 2
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ := by
  set T := sharpInstTrial momentOrderExpLaw sharpInstOutcome
  have hexp : Integrable (fun x => Real.exp (3 / 4 * ‖id x - featureLineVec (3 / 2)‖))
      T.covLaw := by
    rw [sharpInstTrial_covLaw]
    exact (integrable_exp_momentOrderExpLaw_iff (3 / 2) (3 / 4)).2 (by norm_num)
  have hX : MemLp (fun ω => id (T.X ω) 0) 2 T.μ :=
    memLp_feature_of_integrable_exp_pos measurable_fst measurable_id (by norm_num) hexp 0
  cases a
  · exact hX
  · exact (memLp_const 1).add (hX.const_mul 2)

/-- The outcomes of the instance have no residual about the regression, so the conditional
variance is `0`. -/
theorem unboundedInst_variance (a : Bool) :
    (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ[fun ω =>
      ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).Y a ω -
        featureInteractionDesign id a ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).X ω)
          ⬝ᵥ commonLimitExampleCoef) ^ 2 |
      MeasurableSpace.comap (sharpInstTrial momentOrderExpLaw sharpInstOutcome).X inferInstance]
      ≤ᵐ[(sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ] fun _ => 0 := by
  have h0 : (fun ω => ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).Y a ω -
      featureInteractionDesign id a ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).X ω)
        ⬝ᵥ commonLimitExampleCoef) ^ 2) = 0 := funext fun ω => by
    rw [featureInteractionDesign_dotProduct_sharpInstOutcome]; simp [sharpInstTrial]
  rw [h0, condExp_zero]
  rfl

/-- **The weighting hypotheses of the instance** at `t = 3/2`: the interior condition, the
minimizer `β* = 1/3`, and the moment of order `κ = 3/4 > 2 β*`. -/
theorem unboundedInst_weighting :
    featureLineVec (3 / 2) ∈ interior (closedConvexHull ℝ
      ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw.map id).support) ∧
    IsMinOn (sharpDualObjective (sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw id
      (featureLineVec (3 / 2))) Set.univ (featureLineVec (1 - 1 / (3 / 2))) ∧
    Integrable (fun x => Real.exp (3 / 4 * ‖id x - featureLineVec (3 / 2)‖))
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw ∧
    2 * (1 : ℕ) * ‖featureLineVec (1 - 1 / (3 / 2 : ℝ))‖ < 3 / 4 := by
  rw [sharpInstTrial_covLaw, Measure.map_id]
  refine ⟨mem_interior_momentOrderExpLaw (by norm_num),
    isMinOn_sharpDualObjective_momentOrderExpLaw (by norm_num),
    (integrable_exp_momentOrderExpLaw_iff _ _).2 (by norm_num), ?_⟩
  rw [norm_featureLineVec]; norm_num [abs_of_pos]

theorem unboundedInst_designValue (a : Bool) :
    interactionDesign a (featureLineVec (3 / 2)) ⬝ᵥ commonLimitExampleCoef =
      if a then 4 else 3 / 2 := by
  change featureInteractionDesign id a (featureLineVec (3 / 2)) ⬝ᵥ _ = _
  rw [featureInteractionDesign_dotProduct_sharpInstOutcome]
  cases a <;> norm_num [sharpInstOutcome, featureLineVec]

/-- **An instance of `commonLimit_reportedMoments_arm_of_isMinOn` with an unbounded feature.**
In the exponential coin trial, the weighted arm mean and the standardized estimate of arm `true`
at the reported moments `tₙ → 3/2` both converge in probability to `4`. -/
theorem unboundedInst_arm :
    IsConsistent (fun n ω => sampleBalancedArmMean id (unboundedInstReported n)
        (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) 4
        (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          (unboundedInstReported n) true n ω) atTop (fun _ => 4) := by
  obtain ⟨hint, hmin, hexp, hκ⟩ := unboundedInst_weighting
  have h := commonLimit_reportedMoments_arm_of_isMinOn (W := fun _ => ())
    (G := fun n _ => unboundedInstReported n)
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id hint hmin hexp hκ unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_unboundedInstReported true (unboundedInst_variance true)
  rw [unboundedInst_designValue] at h
  exact h

/-! ### The target population -/

/-- The target population of the instance: the covariate is uniform on `[1, 2]` and the outcomes
are those of the trial, `Y(true) = 1 + 2X`, `Y(false) = X`. -/
noncomputable def unboundedInstTarget : Population ℝ (Fin 1 → ℝ) Bool :=
  ⟨volume.restrict (Set.Icc 1 2), featureLineVec, fun a ω => sharpInstOutcome a (featureLineVec ω)⟩

instance : IsProbabilityMeasure unboundedInstTarget.μ :=
  ⟨by simp [unboundedInstTarget, Real.volume_Icc]; norm_num⟩

theorem integrableOn_Icc_one_two {g : ℝ → ℝ} (hg : Continuous g) :
    Integrable g unboundedInstTarget.μ :=
  hg.integrableOn_Icc

theorem integral_unboundedInstTarget_id :
    ∫ x, x ∂unboundedInstTarget.μ = 3 / 2 := by
  change ∫ x in Set.Icc (1 : ℝ) 2, x = 3 / 2
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    integral_id]
  norm_num

/-- **The target law is absolutely continuous with respect to the exponential law**: on `[1, 2]`
the exponential density is at least `exp(-2)`. -/
theorem unboundedInstTarget_absolutelyContinuous :
    unboundedInstTarget.covLaw ≪
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).covLaw := by
  rw [sharpInstTrial_covLaw, momentOrderExpLaw]
  refine Measure.AbsolutelyContinuous.map ?_ measurable_featureLineVec
  refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
  have hmS : Measurable (S.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hS
  have hle : ENNReal.ofReal (Real.exp (-2)) * volume.restrict (Set.Icc (1 : ℝ) 2) S ≤
      expMeasure 1 S := by
    calc ENNReal.ofReal (Real.exp (-2)) * volume.restrict (Set.Icc (1 : ℝ) 2) S
        = ∫⁻ x in Set.Icc (1 : ℝ) 2, ENNReal.ofReal (Real.exp (-2)) * S.indicator 1 x := by
          rw [lintegral_const_mul _ hmS, lintegral_indicator_one hS]
      _ ≤ ∫⁻ x in Set.Icc (1 : ℝ) 2, ENNReal.ofReal (Real.exp (-x)) * S.indicator 1 x :=
          setLIntegral_mono ((by fun_prop : Measurable fun x : ℝ =>
            ENNReal.ofReal (Real.exp (-x))).mul hmS) fun x hx => by
            exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
              (Real.exp_le_exp.2 (by linarith [hx.2]))) (by simp)
      _ ≤ ∫⁻ x in Set.Ici 0, ENNReal.ofReal (Real.exp (-x)) * S.indicator 1 x :=
          lintegral_mono_set fun x hx => Set.mem_Ici.2 (by linarith [hx.1])
      _ = expMeasure 1 S := by
          rw [← lintegral_expMeasure_one hmS, lintegral_indicator_one hS]
  rw [hS0, nonpos_iff_eq_zero, mul_eq_zero] at hle
  change volume.restrict (Set.Icc (1 : ℝ) 2) S = 0
  exact hle.resolve_left (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem unboundedInstTarget_featureMean (k : Fin 1) :
    ∫ x, x k ∂unboundedInstTarget.covLaw = featureLineVec (3 / 2) k := by
  change ∫ x, x k ∂(unboundedInstTarget.μ.map featureLineVec) = _
  rw [integral_map measurable_featureLineVec.aemeasurable
    (by fun_prop : Measurable fun x : Fin 1 → ℝ => x k).aestronglyMeasurable]
  exact integral_unboundedInstTarget_id

theorem unboundedInstTarget_featureIntegrable (k : Fin 1) :
    Integrable (fun x => x k) unboundedInstTarget.covLaw := by
  change Integrable _ (unboundedInstTarget.μ.map featureLineVec)
  rw [integrable_map_measure
    (by fun_prop : Measurable fun x : Fin 1 → ℝ => x k).aestronglyMeasurable
    measurable_featureLineVec.aemeasurable]
  exact integrableOn_Icc_one_two continuous_id

theorem unboundedInstTarget_integrable (a : Bool) :
    Integrable (unboundedInstTarget.Y a) unboundedInstTarget.μ := by
  cases a
  · exact integrableOn_Icc_one_two continuous_id
  · exact integrableOn_Icc_one_two (continuous_const.add (continuous_const.mul continuous_id))

/-- **Both arms are transported**: the regression of `Y(a)` on the covariate is
`sharpInstOutcome a` in the trial and in the target. -/
theorem unboundedInst_structurallyInvariant (a : Bool) :
    StructurallyInvariant (sharpInstTrial momentOrderExpLaw sharpInstOutcome).μ
      (sharpInstTrial momentOrderExpLaw sharpInstOutcome).X
      ((sharpInstTrial momentOrderExpLaw sharpInstOutcome).Y a)
      unboundedInstTarget.μ unboundedInstTarget.X (unboundedInstTarget.Y a) := by
  obtain ⟨-, -, -, -, -, -, hm, -, -⟩ := sharpInstTrial_hypotheses measurable_sharpInstOutcome a
    (integrable_sharpInstOutcome_momentOrderExpLaw a)
  refine ⟨sharpInstOutcome a, (Population.isCommonRegression_iff
    (P := (sharpInstTrial momentOrderExpLaw sharpInstOutcome).toPopulation)
    (Q := unboundedInstTarget) a _).2 ⟨hm, ?_⟩⟩
  exact Population.isCondMean_of_eq_comp measurable_featureLineVec (measurable_sharpInstOutcome a)
    rfl (unboundedInstTarget_integrable a)

theorem unboundedInstTarget_armMean_true : unboundedInstTarget.armMean true = 4 := by
  change ∫ x, (1 + 2 * x) ∂unboundedInstTarget.μ = 4
  rw [integral_add (integrableOn_Icc_one_two (g := fun _ => (1 : ℝ)) continuous_const)
    (integrableOn_Icc_one_two (g := fun x => 2 * x) (continuous_const.mul continuous_id)),
    integral_const_mul]
  rw [integral_unboundedInstTarget_id, integral_const, probReal_univ]
  norm_num

theorem unboundedInstTarget_armMean_false : unboundedInstTarget.armMean false = 3 / 2 :=
  integral_unboundedInstTarget_id

/-- **An instance of `commonLimit_reportedMoments_armMean_of_isMinOn` with an unbounded
feature.** Both estimators of arm `true` at the reported moments `tₙ → 3/2` converge in
probability to the target mean `E_Q[Y(true)] = 4`, and their difference converges in probability
to `0`. -/
theorem unboundedInst_armMean :
    IsConsistent (fun n ω => sampleBalancedArmMean id (unboundedInstReported n)
        (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) 4
        (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          (unboundedInstReported n) true n ω) atTop (fun _ => 4) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => reportedMomentsArmFit id (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          (unboundedInstReported n) true n ω - sampleBalancedArmMean id (unboundedInstReported n)
            (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) atTop
        (fun _ => 0) := by
  obtain ⟨hint, hmin, hexp, hκ⟩ := unboundedInst_weighting
  have h := commonLimit_reportedMoments_armMean_of_isMinOn (W := fun _ => ())
    (G := fun n _ => unboundedInstReported n)
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id hint hmin hexp hκ unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_unboundedInstReported true (unboundedInst_variance true)
    measurable_featureLineVec unboundedInstTarget_featureIntegrable
    unboundedInstTarget_featureMean (unboundedInstTarget_integrable true)
    (unboundedInst_structurallyInvariant true) unboundedInstTarget_absolutelyContinuous
  rw [unboundedInstTarget_armMean_true] at h
  exact h

/-- **An instance of `commonLimit_reportedMoments_unanchored_of_isMinOn` with an unbounded
feature.** With the target mean of `Y(false)` reported exactly (`m̂_b = E_Q[Y(false)] = 3/2`) and
the identity link, the weighted and the standardized unanchored comparisons of `false` against
`true` both converge in probability to `3/2 - 4 = -5/2`, and their difference converges in
probability to `0`. -/
theorem unboundedInst_unanchored :
    IsConsistent (fun n ω => id (unboundedInstTarget.armMean false) - id (sampleBalancedArmMean
        id (unboundedInstReported n) (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          true n ω)) (-5 / 2) (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => id (unboundedInstTarget.armMean false) - id (reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (unboundedInstReported n)
            true n ω)) atTop (fun _ => -5 / 2) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun n ω => (id (unboundedInstTarget.armMean false) - id (reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome) (unboundedInstReported n)
            true n ω)) - (id (unboundedInstTarget.armMean false) - id (sampleBalancedArmMean
              id (unboundedInstReported n) (sharpInstSample momentOrderExpLaw sharpInstOutcome)
                true n ω))) atTop (fun _ => 0) := by
  obtain ⟨hint, hmin, hexp, hκ⟩ := unboundedInst_weighting
  have h := commonLimit_reportedMoments_unanchored_of_isMinOn (W := fun _ => ())
    (G := fun n _ => unboundedInstReported n) (a := true) (b := false)
    (mb := fun _ _ => unboundedInstTarget.armMean false) (g := id)
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id hint hmin hexp hκ unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    tendstoInMeasure_unboundedInstReported (unboundedInst_variance true)
    measurable_featureLineVec unboundedInstTarget_featureIntegrable
    unboundedInstTarget_featureMean (unboundedInstTarget_integrable true)
    (unboundedInst_structurallyInvariant true) unboundedInstTarget_absolutelyContinuous
    (tendstoInMeasure_const _) continuousAt_id continuousAt_id
  have he : unboundedInstTarget.marginalEffect id true false = -5 / 2 := by
    rw [Population.marginalEffect, unboundedInstTarget_armMean_true,
      unboundedInstTarget_armMean_false]
    norm_num
  rw [he] at h
  exact h

end Instance

end PopulationAdjustment

end CausalInference
