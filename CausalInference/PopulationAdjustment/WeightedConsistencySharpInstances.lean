/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedConsistencyGeneralExamples
public import CausalInference.PopulationAdjustment.StandardizationInstancesTargetSample

/-!
# The weighted estimator on concrete trials: every hypothesis discharged

The general consistency theorem of the weighted arm mean
(`sampleBalancedArmMean_isConsistent_trial_general`) takes the primitives of a randomized trial,
an i.i.d. sample of its records, the interior condition, exponential moments and converging
reported targets. This file builds trials and samples in which every one of these hypotheses is
proved, and computes the limit as a number.

**The trials** (`sharpInstTrial lam f`): the covariate is a feature vector `X` with law `lam`,
the assignment `A` is a fair coin independent of `X` (the law `lam ⊗ halfLaw` on
`(Fin p → ℝ) × Bool`), and the potential outcomes are deterministic functions `Y(a) = f a X`.
The randomization, the positive arm probability, the conditional mean function `f a`, the zero
residual and its conditional variance are derived (`sharpInstTrial_hypotheses`).

**The samples.** The records `(X, A, Y)` of infinitely many independent copies of the trial form
an i.i.d. sample whose law is the individual data law of the trial
(`isIIDSample_sharpInstSample`, `map_sharpInstSample`); with a second independent sequence of
target feature draws (`independentSamplesLaw`) the reported target is the sample mean of the
draws, a random target independent of the index sample.

**The instances.**

* The three point law on `{-1, 0, 1}` with outcome `Y(true) = 1 + 2X`, the deterministic targets
  `tₙ = 1 / (n + 1) → 0`: the weighted arm mean converges in probability to `1`
  (`sharpInst_threePoint_consistent`).
* The standard Gaussian feature law, unbounded, with the same outcome and the targets
  `tₙ = 1 + 1 / (n + 1) → 1`: the limit is `3` (`sharpInst_gaussian_consistent`).
* The three point trial with the reported target the mean of the first `n` draws of an
  independent sample from the three point law, a random target converging to `0`: the limit is
  `1` (`sharpInst_randomTarget_consistent`).
* The Gaussian trial with the reported target the mean of the first `n` draws of an independent
  sample from the Gaussian law with mean `1`: the limit is `3`, while the unweighted arm mean
  converges to `1` (`sharpInst_randomTarget_gaussian_consistent`).

## Main definitions

* `sharpInstTrial`, `sharpInstRecord`, `sharpInstSample`, `sharpInstLaw`,
  `sharpInstTwoSample`, `sharpInstTwoLaw`, `sharpInstDrawMean`, `sharpInstOutcome`,
  `sharpInstShiftedGaussian`.

## Main results

* `sharpInstTrial_covLaw`, `sharpInstTrial_hypotheses`, `isIIDSample_sharpInstSample`,
  `map_sharpInstSample`, `integrable_affine_of_integrable_exp`.
* `sharpInst_consistent_of_tendsto`, `sharpInst_consistent_of_drawMean`: the general theorem with
  every trial and sample hypothesis discharged.
* `sharpInst_threePoint_consistent`, `sharpInst_gaussian_consistent`,
  `sharpInst_randomTarget_consistent`, `sharpInst_randomTarget_gaussian_consistent`.

## References

* J. E. Signorovitch and coauthors, PharmacoEconomics 28 (2010).
* J. Hainmueller, *Entropy balancing for causal effects: a multivariate reweighting method to
  produce balanced samples in observational studies*, Political Analysis 20 (2012).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure

variable {p : ℕ}

/-! ### The coin trial over a feature law -/

section Trial

/-- **The coin trial over a feature law**: the covariate `X` has law `lam`, the assignment is a
fair coin independent of `X`, and the potential outcomes are `Y(a) = f a X`. -/
noncomputable def sharpInstTrial (lam : Measure (Fin p → ℝ)) (f : Bool → (Fin p → ℝ) → ℝ) :
    Trial ((Fin p → ℝ) × Bool) (Fin p → ℝ) Bool where
  μ := lam.prod halfLaw
  X := Prod.fst
  Y a ω := f a ω.1
  A := Prod.snd

variable (lam : Measure (Fin p → ℝ)) (f : Bool → (Fin p → ℝ) → ℝ)

instance [IsProbabilityMeasure lam] : IsProbabilityMeasure (sharpInstTrial lam f).μ := by
  unfold sharpInstTrial; infer_instance

/-- The covariate law of the coin trial is the feature law. -/
theorem sharpInstTrial_covLaw : (sharpInstTrial lam f).covLaw = lam := by
  change (lam.prod halfLaw).map Prod.fst = lam
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Each arm of the coin trial has probability `1/2`. -/
theorem sharpInstTrial_prob_arm [IsProbabilityMeasure lam] (a : Bool) :
    (sharpInstTrial lam f).μ.real ((sharpInstTrial lam f).A ⁻¹' {a}) = 1 / 2 := by
  change (lam.prod halfLaw).real (Prod.snd ⁻¹' {a}) = 1 / 2
  rw [measureReal_def, ← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul]
  cases a <;> simp [halfLaw, stratumLaw]

variable {lam f}

/-- **The trial hypotheses of the coin trial.** For a measurable outcome function `f a`
integrable under `lam`: the covariates, the assignment, the observed outcome and `Y(a)` are
measurable, the assignment is independent of `(X, Y(a))`, the arm `a` has positive probability,
`f a` is a conditional mean function of `Y(a)`, and the residual `Y(a) - f a X` vanishes, so it
is square integrable with conditional variance at most `0`. -/
theorem sharpInstTrial_hypotheses [IsProbabilityMeasure lam] (hf : ∀ a, Measurable (f a))
    (a : Bool) (hfi : Integrable (f a) lam) :
    Measurable (sharpInstTrial lam f).X ∧ Measurable (sharpInstTrial lam f).A ∧
      Measurable (sharpInstTrial lam f).obsOutcome ∧ Measurable ((sharpInstTrial lam f).Y a) ∧
      IndepFun (sharpInstTrial lam f).A
        (fun ω => ((sharpInstTrial lam f).X ω, (sharpInstTrial lam f).Y a ω))
        (sharpInstTrial lam f).μ ∧
      0 < (sharpInstTrial lam f).μ.real ((sharpInstTrial lam f).A ⁻¹' {a}) ∧
      (sharpInstTrial lam f).IsCondMean a (f a) ∧
      Integrable (fun ω => ((sharpInstTrial lam f).Y a ω - f a ((sharpInstTrial lam f).X ω)) ^ 2)
        (sharpInstTrial lam f).μ ∧
      (sharpInstTrial lam f).μ[fun ω => ((sharpInstTrial lam f).Y a ω -
          f a ((sharpInstTrial lam f).X ω)) ^ 2 |
        MeasurableSpace.comap (sharpInstTrial lam f).X inferInstance]
          ≤ᵐ[(sharpInstTrial lam f).μ] fun _ => (0 : ℝ) := by
  have hX : Measurable (sharpInstTrial lam f).X := measurable_fst
  have hA : Measurable (sharpInstTrial lam f).A := measurable_snd
  have hY : ∀ b, Measurable ((sharpInstTrial lam f).Y b) := fun b => (hf b).comp measurable_fst
  have hzero : (fun ω => ((sharpInstTrial lam f).Y a ω - f a ((sharpInstTrial lam f).X ω)) ^ 2)
      = 0 := funext fun ω => by simp [sharpInstTrial]
  refine ⟨hX, hA, measurable_obsOutcome_bool hA (hY true) (hY false), hY a, ?_, ?_, ?_, ?_, ?_⟩
  · have h := indepFun_prod (μ := lam) (ν := halfLaw) (X := (id : (Fin p → ℝ) → (Fin p → ℝ)))
      (Y := (id : Bool → Bool)) measurable_id measurable_id
    exact h.symm.comp measurable_id (measurable_id.prodMk (hf a))
  · rw [sharpInstTrial_prob_arm]; norm_num
  · exact Population.isCondMean_of_eq_comp hX (hf a) rfl (hfi.comp_fst halfLaw)
  · rw [hzero]; exact integrable_zero _ _ _
  · rw [hzero, condExp_zero]
    exact ae_of_all _ fun _ => le_refl _

end Trial

/-! ### The i.i.d. sample of records -/

section Sample

variable (lam : Measure (Fin p → ℝ)) (f : Bool → (Fin p → ℝ) → ℝ)

/-- The record `(X, A, Y)` of a unit of the coin trial. -/
noncomputable def sharpInstRecord (ω : (Fin p → ℝ) × Bool) : (Fin p → ℝ) × Bool × ℝ :=
  ((sharpInstTrial lam f).X ω, (sharpInstTrial lam f).A ω, (sharpInstTrial lam f).obsOutcome ω)

/-- The law of the sample: infinitely many independent copies of the coin trial. -/
noncomputable def sharpInstLaw : Measure (ℕ → (Fin p → ℝ) × Bool) :=
  Measure.infinitePi fun _ => (sharpInstTrial lam f).μ

instance [IsProbabilityMeasure lam] : IsProbabilityMeasure (sharpInstLaw lam f) := by
  unfold sharpInstLaw; infer_instance

/-- The records of the sample. -/
noncomputable def sharpInstSample (i : ℕ) (ω : ℕ → (Fin p → ℝ) × Bool) : (Fin p → ℝ) × Bool × ℝ :=
  sharpInstRecord lam f (ω i)

variable {lam f}

theorem measurable_sharpInstRecord (hf : ∀ a, Measurable (f a)) :
    Measurable (sharpInstRecord lam f) :=
  measurable_fst.prodMk (measurable_snd.prodMk (measurable_obsOutcome_bool measurable_snd
    ((hf true).comp measurable_fst) ((hf false).comp measurable_fst)))

/-- **The sample of records is i.i.d.** -/
theorem isIIDSample_sharpInstSample [IsProbabilityMeasure lam] (hf : ∀ a, Measurable (f a)) :
    IsIIDSample (sharpInstSample lam f) (sharpInstLaw lam f) :=
  isIIDSample_infinitePi_comp _ (measurable_sharpInstRecord hf)

theorem measurable_sharpInstSample (hf : ∀ a, Measurable (f a)) (i : ℕ) :
    Measurable (sharpInstSample lam f i) :=
  (measurable_sharpInstRecord hf).comp (measurable_pi_apply i)

/-- **The law of a record is the individual data law of the trial.** -/
theorem map_sharpInstSample [IsProbabilityMeasure lam] (hf : ∀ a, Measurable (f a)) (i : ℕ) :
    (sharpInstLaw lam f).map (sharpInstSample lam f i) = (sharpInstTrial lam f).ipdLaw :=
  map_infinitePi_comp_eval _ (measurable_sharpInstRecord hf) i

end Sample

/-! ### Consistency with every hypothesis discharged -/

section Consistency

variable {lam : Measure (Fin p → ℝ)} {f : Bool → (Fin p → ℝ) → ℝ}

/-- An affine function of the features is integrable under a law with a finite exponential
moment `E[exp ‖y - t‖]`. -/
theorem integrable_affine_of_integrable_exp [IsProbabilityMeasure lam] {t : Fin p → ℝ}
    (hexp : Integrable (fun y => Real.exp (1 * ‖y - t‖)) lam) (c : ℝ) (d : Fin p → ℝ) :
    Integrable (fun y => c + d ⬝ᵥ y) lam := by
  have hn : Integrable (fun y => ‖y - t‖) lam :=
    hexp.mono' (measurable_id.sub_const t).norm.aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_norm, one_mul]
      linarith [Real.add_one_le_exp ‖y - t‖])
  have h : (fun y => c + d ⬝ᵥ y) = fun y => (c + d ⬝ᵥ t) + d ⬝ᵥ (y - t) := funext fun y => by
    rw [dotProduct_sub]; ring
  rw [h]
  refine (integrable_const _).add ((hn.const_mul (p * ‖d‖)).mono' ?_ (ae_of_all _ fun y => ?_))
  · exact ((continuous_const.dotProduct continuous_id).measurable.comp
      (measurable_id.sub_const t)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, mul_assoc]
    exact abs_dotProduct_le_mul_norm d _

/-- **Consistency in the coin trial at deterministic targets, every trial and sample hypothesis
discharged.** For a feature law `lam` whose closed convex hull of the support has `t` in its
interior and with all exponential moments of `‖y - t‖`, measurable outcome functions, and the
outcome of arm `a` affine in the features, `f a x = c + dᵀx`, the weighted arm mean of the
records of the coin trial at targets `tₙ → t` is consistent for `c + dᵀt`. -/
theorem sharpInst_consistent_of_tendsto [IsProbabilityMeasure lam] (hf : ∀ a, Measurable (f a))
    {t : Fin p → ℝ} (hint : t ∈ interior (closedConvexHull ℝ lam.support))
    (hexp : ∀ κ : ℝ, Integrable (fun y => Real.exp (κ * ‖y - t‖)) lam)
    {tn : ℕ → Fin p → ℝ} (htn : Tendsto tn atTop (𝓝 t)) (a : Bool) {c : ℝ} {d : Fin p → ℝ}
    (haff : ∀ x, f a x = c + d ⬝ᵥ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean id (tn n) (sharpInstSample lam f) a n ω)
      (c + d ⬝ᵥ t) (sharpInstLaw lam f) := by
  have hfi : Integrable (f a) lam := by
    rw [show f a = fun x => c + d ⬝ᵥ x from funext haff]
    exact integrable_affine_of_integrable_exp (hexp 1) c d
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses hf a hfi
  exact sampleBalancedArmMean_isConsistent_trial_general hX hA hYo a hYa hrand
    (isIIDSample_sharpInstSample hf) (measurable_sharpInstSample hf) (map_sharpInstSample hf 0)
    measurable_id (t := t) (by rw [Measure.map_id, sharpInstTrial_covLaw]; exact hint)
    (by rw [sharpInstTrial_covLaw]; exact hexp) (W := fun _ => ()) measurable_const
    (indepFun_const_left _ _) (G := fun n _ => tn n) (fun _ => measurable_const)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => htn)) hq hm hres2 hvar (a0 := c) (b := d) haff

variable (lam f) in
/-- The law of two independent samples: copies of the coin trial and target feature draws with
law `lam₂`. -/
noncomputable abbrev sharpInstTwoLaw (lam₂ : Measure (Fin p → ℝ)) :
    Measure ((ℕ → (Fin p → ℝ) × Bool) × (ℕ → Fin p → ℝ)) :=
  independentSamplesLaw (sharpInstTrial lam f).μ lam₂

variable (lam f) in
/-- The records of the coin trial on the space of two samples. -/
noncomputable def sharpInstTwoSample (i : ℕ) (ω : (ℕ → (Fin p → ℝ) × Bool) × (ℕ → Fin p → ℝ)) :
    (Fin p → ℝ) × Bool × ℝ :=
  sharpInstRecord lam f (ω.1 i)

/-- The mean `n⁻¹ ∑_{i < n} wᵢ` of the first `n` target feature draws, the reported target. -/
noncomputable def sharpInstDrawMean (n : ℕ) (w : ℕ → Fin p → ℝ) : Fin p → ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, w i

theorem measurable_sharpInstDrawMean (n : ℕ) :
    Measurable (sharpInstDrawMean (p := p) n) := by
  unfold sharpInstDrawMean; fun_prop

/-- **Consistency in the coin trial at a random target, every hypothesis discharged.** The
reported target is the mean of the first `n` draws of an independent i.i.d. sample from a law
`lam₂` with integrable features and mean `t`. Under the interior and moment conditions at `t`
for the trial feature law `lam` and the outcome of arm `a` affine in the features, the weighted
arm mean at the random target is consistent for `c + dᵀt`. The convergence of the target is the
law of large numbers, its independence from the index sample is that of the two sequences. -/
theorem sharpInst_consistent_of_drawMean [IsProbabilityMeasure lam] (hf : ∀ a, Measurable (f a))
    {t : Fin p → ℝ} (hint : t ∈ interior (closedConvexHull ℝ lam.support))
    (hexp : ∀ κ : ℝ, Integrable (fun y => Real.exp (κ * ‖y - t‖)) lam)
    {lam₂ : Measure (Fin p → ℝ)} [IsProbabilityMeasure lam₂] (hi₂ : Integrable id lam₂)
    (hmean : ∫ y, y ∂lam₂ = t) (a : Bool) {c : ℝ} {d : Fin p → ℝ}
    (haff : ∀ x, f a x = c + d ⬝ᵥ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean id (sharpInstDrawMean n ω.2)
      (sharpInstTwoSample lam f) a n ω) (c + d ⬝ᵥ t) (sharpInstTwoLaw lam f lam₂) := by
  have hfi : Integrable (f a) lam := by
    rw [show f a = fun x => c + d ⬝ᵥ x from funext haff]
    exact integrable_affine_of_integrable_exp (hexp 1) c d
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses hf a hfi
  have hrec := measurable_sharpInstRecord (lam := lam) hf
  have hO : IsIIDSample (sharpInstTwoSample lam f) (sharpInstTwoLaw lam f lam₂) :=
    isIIDSample_independentSamplesLaw_fst _ _ hrec
  have hOm : ∀ i, Measurable (sharpInstTwoSample lam f i) := fun i =>
    hrec.comp ((measurable_pi_apply i).comp measurable_fst)
  have hlaw : (sharpInstTwoLaw lam f lam₂).map (sharpInstTwoSample lam f 0) =
      (sharpInstTrial lam f).ipdLaw :=
    map_independentSamplesLaw_fst _ _ hrec 0
  have hW2 : IsIIDSample (fun i (ω : (ℕ → (Fin p → ℝ) × Bool) × (ℕ → Fin p → ℝ)) => ω.2 i)
      (sharpInstTwoLaw lam f lam₂) := isIIDSample_independentSamplesLaw_snd _ _ measurable_id
  have hmap2 : (sharpInstTwoLaw lam f lam₂).map
      (fun ω : (ℕ → (Fin p → ℝ) × Bool) × (ℕ → Fin p → ℝ) => id (ω.2 0)) = lam₂ := by
    rw [map_independentSamplesLaw_snd _ _ measurable_id 0, Measure.map_id]
  have hm0 : Measurable fun ω : (ℕ → (Fin p → ℝ) × Bool) × (ℕ → Fin p → ℝ) => id (ω.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  have hi : Integrable (fun ω : (ℕ → (Fin p → ℝ) × Bool) × (ℕ → Fin p → ℝ) => id (ω.2 0))
      (sharpInstTwoLaw lam f lam₂) := by
    rw [← hmap2] at hi₂
    exact (integrable_map_measure (g := id) measurable_id.aestronglyMeasurable
      hm0.aemeasurable).1 hi₂
  have hlim : (sharpInstTwoLaw lam f lam₂)[fun ω => id (ω.2 0)] = t := by
    have h := integral_map (μ := sharpInstTwoLaw lam f lam₂) (f := id) hm0.aemeasurable
      measurable_id.aestronglyMeasurable
    rw [hmap2] at h
    rw [← hmean]
    exact h.symm
  have htm := hW2.tendstoInMeasure_smul_sum measurable_id hi
  rw [hlim] at htm
  have hWO : IndepFun (fun ω : (ℕ → (Fin p → ℝ) × Bool) × (ℕ → Fin p → ℝ) => ω.2)
      (fun ω k => sharpInstTwoSample lam f k ω) (sharpInstTwoLaw lam f lam₂) :=
    (indepFun_independentSamplesLaw _ _).symm.comp measurable_id
      (Measurable.of_eval fun k => hrec.comp (measurable_pi_apply k))
  exact sampleBalancedArmMean_isConsistent_trial_general hX hA hYo a hYa hrand hO hOm hlaw
    measurable_id (t := t) (by rw [Measure.map_id, sharpInstTrial_covLaw]; exact hint)
    (by rw [sharpInstTrial_covLaw]; exact hexp) measurable_snd hWO
    (G := sharpInstDrawMean) measurable_sharpInstDrawMean htm hq hm hres2 hvar
    (a0 := c) (b := d) haff

end Consistency

/-! ### The instances in numbers -/

section Numbers

/-- The outcomes of the instances: `Y(true) = 1 + 2X` and `Y(false) = X`, for a scalar feature. -/
def sharpInstOutcome (a : Bool) (x : Fin 1 → ℝ) : ℝ := if a then 1 + 2 * x 0 else x 0

theorem measurable_sharpInstOutcome (a : Bool) : Measurable (sharpInstOutcome a) := by
  cases a
  · exact measurable_pi_apply 0
  · exact measurable_const.add (measurable_const.mul (measurable_pi_apply 0))

/-- The outcome of arm `true` is affine in the feature: `1 + 2X = 1 + (2)ᵀX`. -/
theorem sharpInstOutcome_true (x : Fin 1 → ℝ) :
    sharpInstOutcome true x = 1 + featureLineVec 2 ⬝ᵥ x := by
  simp [sharpInstOutcome, featureLineVec, dotProduct]

/-- **The three point instance.** The covariate follows the three point law on `{-1, 0, 1}`, the
assignment is a fair coin, `Y(true) = 1 + 2X`, and the reported targets are
`tₙ = 1 / (n + 1) → 0`. The weighted arm mean of arm `true` converges in probability to `1`. -/
theorem sharpInst_threePoint_consistent :
    IsConsistent (fun n ω => sampleBalancedArmMean id (featureLineVec (1 / ((n : ℝ) + 1)))
      (sharpInstSample threePointLaw sharpInstOutcome) true n ω) 1
      (sharpInstLaw threePointLaw sharpInstOutcome) := by
  have h := sharpInst_consistent_of_tendsto measurable_sharpInstOutcome
    zero_mem_interior_threePointLaw (fun κ => integrable_exp_threePointLaw κ 0)
    (tn := fun n : ℕ => featureLineVec (1 / ((n : ℝ) + 1)))
    (tendsto_pi_nhds.2 fun _ => tendsto_one_div_add_atTop_nhds_zero_nat) true
    sharpInstOutcome_true
  simpa using h

/-- **The Gaussian instance, unbounded features and a nonzero target.** The covariate follows the
standard Gaussian law, the assignment is a fair coin, `Y(true) = 1 + 2X`, and the reported targets
are `tₙ = 1 + 1 / (n + 1) → 1`. The weighted arm mean of arm `true` converges in probability to
`3`. -/
theorem sharpInst_gaussian_consistent :
    IsConsistent (fun n ω => sampleBalancedArmMean id (featureLineVec (1 + 1 / ((n : ℝ) + 1)))
      (sharpInstSample gaussianFeatureLaw sharpInstOutcome) true n ω) 3
      (sharpInstLaw gaussianFeatureLaw sharpInstOutcome) := by
  have htn : Tendsto (fun n : ℕ => featureLineVec (1 + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (featureLineVec 1)) := tendsto_pi_nhds.2 fun _ => by
    simpa [featureLineVec] using
      (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
  have h := sharpInst_consistent_of_tendsto measurable_sharpInstOutcome
    (mem_interior_gaussian (featureLineVec 1)) (fun κ => integrable_exp_gaussian κ _) htn true
    sharpInstOutcome_true
  have hv : 1 + featureLineVec 2 ⬝ᵥ featureLineVec 1 = 3 := by
    simp [featureLineVec, dotProduct]; norm_num
  rw [hv] at h
  exact h

/-- The features of the three point law are integrable. -/
theorem integrable_id_threePointLaw : Integrable id threePointLaw := by
  have hd : ∀ r : ℝ, Integrable id (Measure.dirac (featureLineVec r)) := fun r =>
    integrable_dirac' measurable_id.stronglyMeasurable eNorm_lt_top
  exact (((hd (-1)).add_measure (hd 0)).add_measure (hd 1)).smul_measure (by simp)

/-- The mean of the three point law is `0`. -/
theorem integral_id_threePointLaw : ∫ y, y ∂threePointLaw = 0 := by
  have hd : ∀ r : ℝ, Integrable (fun y : Fin 1 → ℝ => y) (Measure.dirac (featureLineVec r)) :=
    fun r =>
    integrable_dirac' measurable_id.stronglyMeasurable eNorm_lt_top
  rw [threePointLaw, integral_smul_measure, integral_add_measure ((hd _).add_measure (hd _))
    (hd _), integral_add_measure (hd _) (hd _), integral_dirac, integral_dirac, integral_dirac]
  have : featureLineVec (-1) + featureLineVec 0 + featureLineVec 1 = 0 := funext fun _ => by
    simp [featureLineVec]
  rw [this, smul_zero]

/-- **The random target instance.** The trial is the three point trial with `Y(true) = 1 + 2X`;
the reported target at stage `n` is the mean of the first `n` draws of an independent i.i.d.
sample from the three point law, a random target converging to `0` by the law of large numbers.
The weighted arm mean of arm `true` converges in probability to `1`. -/
theorem sharpInst_randomTarget_consistent :
    IsConsistent (fun n ω => sampleBalancedArmMean id (sharpInstDrawMean n ω.2)
      (sharpInstTwoSample threePointLaw sharpInstOutcome) true n ω) 1
      (sharpInstTwoLaw threePointLaw sharpInstOutcome threePointLaw) := by
  have h := sharpInst_consistent_of_drawMean measurable_sharpInstOutcome
    zero_mem_interior_threePointLaw (fun κ => integrable_exp_threePointLaw κ 0)
    integrable_id_threePointLaw integral_id_threePointLaw true sharpInstOutcome_true
  simpa using h

/-- A Gaussian law of scalar features with mean `1` and variance `1`, the law of the target
draws of the second random target instance. -/
noncomputable def sharpInstShiftedGaussian : Measure (Fin 1 → ℝ) :=
  (gaussianReal 1 1).map featureLineVec

instance : IsProbabilityMeasure sharpInstShiftedGaussian := by
  unfold sharpInstShiftedGaussian; infer_instance

theorem featureLineVec_eq_smul (r : ℝ) : featureLineVec r = r • featureLineVec 1 :=
  funext fun _ => by simp [featureLineVec]

/-- The features of the shifted Gaussian law are integrable with mean `1`. -/
theorem sharpInstShiftedGaussian_moments :
    Integrable id sharpInstShiftedGaussian ∧
      ∫ y, y ∂sharpInstShiftedGaussian = featureLineVec 1 := by
  have hi : Integrable (fun r : ℝ => r) (gaussianReal 1 1) :=
    (memLp_id_gaussianReal (μ := 1) (v := 1) 1).integrable le_rfl
  have hf : Integrable featureLineVec (gaussianReal 1 1) := by
    rw [show featureLineVec = fun r : ℝ => r • featureLineVec 1 from funext featureLineVec_eq_smul]
    exact hi.smul_const _
  refine ⟨?_, ?_⟩
  · rw [sharpInstShiftedGaussian, integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_featureLineVec.aemeasurable]
    exact hf
  · rw [sharpInstShiftedGaussian, integral_map (f := fun y : Fin 1 → ℝ => y)
      measurable_featureLineVec.aemeasurable measurable_id.aestronglyMeasurable]
    have e : ∫ r, featureLineVec r ∂gaussianReal 1 1 =
        ∫ r, r • featureLineVec 1 ∂gaussianReal 1 1 :=
      integral_congr_ae (ae_of_all _ featureLineVec_eq_smul)
    rw [e, integral_smul_const, integral_id_gaussianReal, one_smul]

/-- **The random target instance where the weighting matters.** The trial covariate is standard
Gaussian with `Y(true) = 1 + 2X`, so the unweighted arm mean converges to `1`; the reported target
at stage `n` is the mean of the first `n` draws of an independent i.i.d. sample from the
Gaussian law with mean `1`. The weighted arm mean of arm `true` converges in probability to the
mean `3` of the outcome at the target feature mean. -/
theorem sharpInst_randomTarget_gaussian_consistent :
    IsConsistent (fun n ω => sampleBalancedArmMean id (sharpInstDrawMean n ω.2)
      (sharpInstTwoSample gaussianFeatureLaw sharpInstOutcome) true n ω) 3
      (sharpInstTwoLaw gaussianFeatureLaw sharpInstOutcome sharpInstShiftedGaussian) := by
  have h := sharpInst_consistent_of_drawMean measurable_sharpInstOutcome
    (mem_interior_gaussian (featureLineVec 1)) (fun κ => integrable_exp_gaussian κ _)
    sharpInstShiftedGaussian_moments.1 sharpInstShiftedGaussian_moments.2 true
    sharpInstOutcome_true
  have hv : 1 + featureLineVec 2 ⬝ᵥ featureLineVec 1 = 3 := by
    simp [featureLineVec, dotProduct]; norm_num
  rw [hv] at h
  exact h

end Numbers

end PopulationAdjustment

end CausalInference
