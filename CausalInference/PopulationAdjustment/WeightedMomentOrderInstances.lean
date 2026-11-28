/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderNecessity
public import CausalInference.PopulationAdjustment.WeightedConsistencySharpInstances

/-!
# A trial with exponential features under one exponential moment

The coin trial over a feature law (`sharpInstTrial`) with every hypothesis of the consistency
theorem under one exponential moment discharged (`momentOrderInst_consistent_of_isMinOn`), and a
concrete instance in which exponential moments of all orders fail, so that only the theorem of
one order applies.

**The instance.** The covariate follows the standard exponential law (`momentOrderExpLaw`), the
assignment is a fair coin, `Y(true) = 1 + 2X`, and the reported targets are
`tₙ = 3/2 + 1/(n + 1) → 3/2`. The population dual minimizer is `β* = 1 - 2/3 = 1/3`, the moment
`E[exp(κ |X - 3/2|)]` is finite exactly for `κ < 1` (`not_forall_integrable_exp_momentOrderExpLaw`),
and `κ = 3/4 > 2 β* = 2/3` is admissible. The weighted arm mean converges in probability to
`1 + 2 · 3/2 = 4` (`momentOrderInst_exponential_consistent`), while the unweighted arm mean
converges to `E[1 + 2X] = 3`.

## Main definitions

* `momentOrderExpLaw`: the standard exponential law of a scalar feature.

## Main results

* `integrable_affine_of_integrable_exp_pos`, `momentOrderInst_consistent_of_isMinOn`.
* `mem_interior_momentOrderExpLaw`, `isMinOn_sharpDualObjective_momentOrderExpLaw`,
  `integrable_exp_momentOrderExpLaw_iff`, `not_forall_integrable_exp_momentOrderExpLaw`.
* `momentOrderInst_exponential_consistent`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison

variable {p : ℕ}

section Consistency

variable {lam : Measure (Fin p → ℝ)} {f : Bool → (Fin p → ℝ) → ℝ}

/-- An affine function of the features is integrable under a law with a finite exponential
moment `E[exp(κ ‖y - t‖)]` of some order `κ > 0`, since `‖y - t‖ ≤ κ⁻¹ exp(κ ‖y - t‖)`. -/
theorem integrable_affine_of_integrable_exp_pos [IsProbabilityMeasure lam] {t : Fin p → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hexp : Integrable (fun y => Real.exp (κ * ‖y - t‖)) lam) (c : ℝ)
    (d : Fin p → ℝ) : Integrable (fun y => c + d ⬝ᵥ y) lam := by
  have hn : Integrable (fun y => ‖y - t‖) lam :=
    (hexp.const_mul κ⁻¹).mono' (measurable_id.sub_const t).norm.aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_norm, le_inv_mul_iff₀ hκ]
        linarith [Real.add_one_le_exp (κ * ‖y - t‖)])
  have h : (fun y => c + d ⬝ᵥ y) = fun y => (c + d ⬝ᵥ t) + d ⬝ᵥ (y - t) := funext fun y => by
    rw [dotProduct_sub]; ring
  rw [h]
  refine (integrable_const _).add ((hn.const_mul (p * ‖d‖)).mono' ?_ (ae_of_all _ fun y => ?_))
  · exact ((continuous_const.dotProduct continuous_id).measurable.comp
      (measurable_id.sub_const t)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, mul_assoc]
    exact abs_dotProduct_le_mul_norm d _

/-- **Consistency in the coin trial under one exponential moment, every trial and sample
hypothesis discharged.** For a feature law `lam` with `t` in the interior of the closed convex
hull of its support, a minimizer `β*` of `E[exp(βᵀ(y - t))]` under `lam`, a finite moment
`E[exp(κ ‖y - t‖)]` of one order `κ > 2 p ‖β*‖`, measurable outcome functions and the outcome of
arm `a` affine in the features, the weighted arm mean of the records of the coin trial at targets
`tₙ → t` is consistent for `c + dᵀt`. -/
theorem momentOrderInst_consistent_of_isMinOn [IsProbabilityMeasure lam]
    (hf : ∀ a, Measurable (f a)) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ lam.support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective lam id t) Set.univ βs)
    {κ : ℝ} (hexp : Integrable (fun y => Real.exp (κ * ‖y - t‖)) lam) (hκ : 2 * p * ‖βs‖ < κ)
    {tn : ℕ → Fin p → ℝ} (htn : Tendsto tn atTop (𝓝 t)) (a : Bool) {c : ℝ} {d : Fin p → ℝ}
    (haff : ∀ x, f a x = c + d ⬝ᵥ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean id (tn n) (sharpInstSample lam f) a n ω)
      (c + d ⬝ᵥ t) (sharpInstLaw lam f) := by
  have hκ0 : 0 < κ := lt_of_le_of_lt (by positivity) hκ
  have hfi : Integrable (f a) lam := by
    rw [show f a = fun x => c + d ⬝ᵥ x from funext haff]
    exact integrable_affine_of_integrable_exp_pos hκ0 hexp c d
  obtain ⟨hX, hA, hYo, hYa, hrand, hq, hm, hres2, hvar⟩ := sharpInstTrial_hypotheses hf a hfi
  exact sampleBalancedArmMean_isConsistent_trial_of_isMinOn hX hA hYo a hYa hrand
    (isIIDSample_sharpInstSample hf) (measurable_sharpInstSample hf) (map_sharpInstSample hf 0)
    measurable_id (t := t) (by rw [Measure.map_id, sharpInstTrial_covLaw]; exact hint)
    (by rw [sharpInstTrial_covLaw]; exact hmin) (by rw [sharpInstTrial_covLaw]; exact hexp) hκ
    (W := fun _ => ()) measurable_const
    (indepFun_const_left _ _) (G := fun n _ => tn n) (fun _ => measurable_const)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => htn)) hq hm hres2 hvar (a0 := c) (b := d) haff

end Consistency

/-! ### The exponential feature law -/

section Exponential

open Set

/-- The standard exponential law of a scalar feature. -/
noncomputable def momentOrderExpLaw : Measure (Fin 1 → ℝ) := (expMeasure 1).map featureLineVec

instance : IsProbabilityMeasure momentOrderExpLaw := by
  unfold momentOrderExpLaw
  exact (Measure.isProbabilityMeasure_map_iff measurable_featureLineVec.aemeasurable).2
    inferInstance

/-- The standard exponential law charges every interval `(a, b)` with `0 ≤ a < b`. -/
theorem expMeasure_pos_of_Ioo_subset {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S : Set ℝ}
    (hSm : MeasurableSet S) (hS : Ioo a b ⊆ S) : 0 < expMeasure 1 S := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x)) * S.indicator 1 x :=
    (by fun_prop : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x))).mul
      (measurable_one.indicator hSm)
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-b)) * volume (Ioo a b) := by
        rw [Real.volume_Ioo]
        exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
          (ENNReal.ofReal_pos.2 (by linarith)).ne'
    _ = ∫⁻ _ in Ioo a b, ENNReal.ofReal (Real.exp (-b)) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Ioo a b, ENNReal.ofReal (Real.exp (-x)) * S.indicator 1 x :=
        setLIntegral_mono hm fun x hx => by
          rw [indicator_of_mem (hS hx), Pi.one_apply, mul_one]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hx.2]))
    _ ≤ ∫⁻ x in Ici 0, ENNReal.ofReal (Real.exp (-x)) * S.indicator 1 x :=
        lintegral_mono_set fun x hx => mem_Ici.2 (ha.trans hx.1.le)
    _ = expMeasure 1 S := by
        rw [← lintegral_expMeasure_one (measurable_one.indicator hSm),
          lintegral_indicator_one hSm]

/-- **The interior condition for the exponential law**: every `t > 0` is in the interior of the
closed convex hull of the support. -/
theorem mem_interior_momentOrderExpLaw {t : ℝ} (ht : 0 < t) :
    featureLineVec t ∈ interior (closedConvexHull ℝ momentOrderExpLaw.support) := by
  refine mem_interior_closedConvexHull_iff_measure_pos.2 fun v hv => ?_
  have hv0 : v 0 ≠ 0 := fun h => hv (funext fun i => by fin_cases i; exact h)
  have hset : MeasurableSet {y : Fin 1 → ℝ | 0 < v ⬝ᵥ (y - featureLineVec t)} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [momentOrderExpLaw, Measure.map_apply measurable_featureLineVec hset]
  have hpre : featureLineVec ⁻¹' {y : Fin 1 → ℝ | 0 < v ⬝ᵥ (y - featureLineVec t)} =
      {x : ℝ | 0 < v 0 * (x - t)} := by
    ext x; simp only [Set.mem_preimage, Set.mem_ofPred_eq, dotProduct_featureLineVec_sub]
  rw [hpre]
  have hm : MeasurableSet {x : ℝ | 0 < v 0 * (x - t)} :=
    measurableSet_lt measurable_const (by fun_prop)
  rcases lt_or_gt_of_ne hv0 with hneg | hpos
  · exact expMeasure_pos_of_Ioo_subset le_rfl ht hm fun x hx => by
      simp only [Set.mem_ofPred_eq]; nlinarith [hx.2]
  · exact expMeasure_pos_of_Ioo_subset ht.le (lt_add_one t) hm fun x hx => by
      simp only [Set.mem_ofPred_eq]; nlinarith [hx.1]

/-- The dual objective of the exponential feature law is that of the exponential law with the
feature `featureLineVec`. -/
theorem sharpDualObjective_momentOrderExpLaw (t : ℝ) :
    sharpDualObjective momentOrderExpLaw id (featureLineVec t) =
      sharpDualObjective (expMeasure 1) featureLineVec (featureLineVec t) := by
  funext β
  have hm : Measurable fun y : Fin 1 → ℝ =>
      ENNReal.ofReal (Real.exp (β ⬝ᵥ (id y - featureLineVec t))) := by fun_prop
  rw [sharpDualObjective, momentOrderExpLaw, lintegral_map hm measurable_featureLineVec]
  rfl

/-- The population dual minimizer of the exponential feature law at `t > 0` is `1 - 1/t`. -/
theorem isMinOn_sharpDualObjective_momentOrderExpLaw {t : ℝ} (ht : 0 < t) :
    IsMinOn (sharpDualObjective momentOrderExpLaw id (featureLineVec t)) Set.univ
      (featureLineVec (1 - 1 / t)) := by
  rw [sharpDualObjective_momentOrderExpLaw]
  exact isMinOn_sharpDualObjective_expMeasure ht

/-- The exponential moments of the exponential feature law: finite exactly for `κ < 1`. -/
theorem integrable_exp_momentOrderExpLaw_iff (t κ : ℝ) :
    Integrable (fun y => Real.exp (κ * ‖y - featureLineVec t‖)) momentOrderExpLaw ↔ κ < 1 := by
  have hm : Measurable fun y : Fin 1 → ℝ => Real.exp (κ * ‖y - featureLineVec t‖) := by
    fun_prop
  rw [momentOrderExpLaw, integrable_map_measure hm.aestronglyMeasurable
    measurable_featureLineVec.aemeasurable]
  exact integrable_exp_norm_expMeasure_iff t κ

/-- **Exponential moments of all orders fail for the exponential feature law**, so the theorems
assuming them do not apply to it. -/
theorem not_forall_integrable_exp_momentOrderExpLaw (t : ℝ) :
    ¬ ∀ κ : ℝ, Integrable (fun y => Real.exp (κ * ‖y - featureLineVec t‖)) momentOrderExpLaw :=
  fun h => lt_irrefl _ ((integrable_exp_momentOrderExpLaw_iff t 1).1 (h 1))

/-- **The exponential instance.** The covariate follows the standard exponential law, the
assignment is a fair coin, `Y(true) = 1 + 2X`, and the reported targets are
`tₙ = 3/2 + 1/(n + 1) → 3/2`. With `β* = 1/3` and the order `κ = 3/4 > 2/3`, the weighted arm mean
of arm `true` converges in probability to `4`. -/
theorem momentOrderInst_exponential_consistent :
    IsConsistent (fun n ω => sampleBalancedArmMean id
      (featureLineVec (3 / 2 + 1 / ((n : ℝ) + 1)))
      (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) 4
      (sharpInstLaw momentOrderExpLaw sharpInstOutcome) := by
  have ht : (0 : ℝ) < 3 / 2 := by norm_num
  have htn : Tendsto (fun n : ℕ => featureLineVec (3 / 2 + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (featureLineVec (3 / 2))) := tendsto_pi_nhds.2 fun _ => by
    simpa [featureLineVec] using
      (tendsto_const_nhds (x := (3 / 2 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hκ : 2 * (1 : ℕ) * ‖featureLineVec (1 - 1 / (3 / 2 : ℝ))‖ < 3 / 4 := by
    rw [norm_featureLineVec]; norm_num [abs_of_pos]
  have h := momentOrderInst_consistent_of_isMinOn measurable_sharpInstOutcome
    (mem_interior_momentOrderExpLaw ht) (isMinOn_sharpDualObjective_momentOrderExpLaw ht)
    ((integrable_exp_momentOrderExpLaw_iff _ _).2 (by norm_num)) hκ htn true
    sharpInstOutcome_true
  have hv : 1 + featureLineVec 2 ⬝ᵥ featureLineVec (3 / 2) = 4 := by
    simp [featureLineVec, dotProduct]; norm_num
  rw [hv] at h
  exact h

end Exponential

end PopulationAdjustment

end CausalInference
