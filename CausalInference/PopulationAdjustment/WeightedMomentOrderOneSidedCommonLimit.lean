/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderOneSidedLine
public import CausalInference.PopulationAdjustment.WeightedMomentOrderUnbounded

/-!
# The common limit of an arm under one sided moments

Both estimators of an arm, the entropy balancing weighted arm mean and the standardized least
squares estimate at the reported moments, converge in probability to `z(a, t)ᵀξ₀` under one sided
moments (`commonLimit_reportedMoments_arm_of_isMinOn_oneSided`): a norm moment
`E[exp(s ‖φ(X) - t‖)] < ∞` of some order `s > 0` and the directional moment
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`, in place of one moment of order
`κ > 2 p ‖β*‖` (`commonLimit_reportedMoments_arm_of_isMinOn`). The least squares side needs only
the second moments of the features, which the norm moment of order `s` gives.

**An instance outside the range of the norm condition.** For the exponential coin trial with
`Y(true) = 1 + 2X`, `Y(false) = X` at `t = 1/3` (`β* = -2`), no order `κ` with a finite moment has
`κ > 2 |β*|`, while both estimators of arm `true` at `tₙ = 1/3 + 1/(n + 1)` converge in
probability to `1 + 2 · 1/3 = 5/3` (`unboundedInst_arm_one_third`).

## Main results

* `commonLimit_reportedMoments_arm_of_isMinOn_oneSided`, `unboundedInst_arm_one_third`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open MeasureTheory ProbabilityTheory Filter Topology Matrix EffectMeasure IndirectComparison
  PointTreatment Transport

section Arm

variable {Ω₁ Ξ 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ξ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲} {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **Both estimators of an arm converge to `z(a, t)ᵀξ₀` under one sided moments.** The
hypotheses of `commonLimit_reportedMoments_arm_of_isMinOn`, with the moment of order
`κ > 2 p ‖β*‖` replaced by `E[exp(s ‖φ(X) - t‖)] < ∞` for some `s > 0` and
`E[exp(2 (1 + ε) β*ᵀ(φ(X) - t))] < ∞` for some `ε > 0`, both under the covariate law. Then the
weighted arm mean and the standardized estimate `z(a, tₙ)ᵀξ̂` at the reported moments `tₙ`
converge in probability to `z(a, t)ᵀξ₀`. -/
theorem commonLimit_reportedMoments_arm_of_isMinOn_oneSided [IsProbabilityMeasure T.μ]
    [IsProbabilityMeasure P]
    (hT : T.IsRandomizedTwoArm) (hY2 : ∀ a, MemLp (T.Y a) 2 T.μ) (hφ : Measurable φ)
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    {βs : Fin p → ℝ} (hmin : IsMinOn (sharpDualObjective T.covLaw φ t) Set.univ βs)
    {s : ℝ} (hs : 0 < s) (hexp : Integrable (fun x => Real.exp (s * ‖φ x - t‖)) T.covLaw)
    {ε : ℝ} (hε : 0 < ε)
    (hdir : Integrable (fun x => Real.exp (2 * (1 + ε) * (βs ⬝ᵥ (φ x - t)))) T.covLaw)
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
  have hφX := memLp_feature_of_integrable_exp_pos hT.measurable_X hφ hs hexp
  have hM := T.linearOutcomeModel_of_interior_of_memLp hT hY2 hφ hint hφX hreg
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
  have hW1 := sampleBalancedArmMean_isConsistent_trial_of_isMinOn_oneSided hT.measurable_X
    hT.measurable_A hYo a (hT.measurable_Y a) hrand hO hOm hlaw hφ hint hmin hs hexp hε hdir hW
    hWO hG htm (hT.prob_arm_pos a) hm hres2 hvar (featureInteractionDesign_dotProduct φ a · ξ₀)
  rw [hval] at hW1
  refine ⟨hW1, ?_⟩
  have hc : Continuous fun q : (Option (Fin p) ⊕ Option (Fin p) → ℝ) × (Fin p → ℝ) =>
      interactionDesign a q.2 ⬝ᵥ q.1 :=
    ((continuous_interactionDesign a).comp continuous_snd).dotProduct continuous_fst
  exact ((hM.tendstoInMeasure hT hO hlaw).prodMk htm).comp_continuousAt hc.continuousAt

end Arm

section Instance

/-- **An instance of `commonLimit_reportedMoments_arm_of_isMinOn_oneSided` at `t = 1/3`.** In the
exponential coin trial, the weighted arm mean and the standardized estimate of arm `true` at the
reported moments `tₙ = 1/3 + 1/(n + 1) → 1/3` both converge in probability to `5/3`. Here
`β* = -2` and no finite moment has an order `κ > 2 |β*|`
(`not_exists_order_directional_momentOrderExpLaw_one_third`). -/
theorem unboundedInst_arm_one_third :
    IsConsistent (fun n ω => sampleBalancedArmMean id
        (featureLineVec (1 / 3 + 1 / ((n : ℝ) + 1)))
        (sharpInstSample momentOrderExpLaw sharpInstOutcome) true n ω) (5 / 3)
        (sharpInstLaw momentOrderExpLaw sharpInstOutcome) ∧
      TendstoInMeasure (sharpInstLaw momentOrderExpLaw sharpInstOutcome)
        (fun (n : ℕ) ω => reportedMomentsArmFit id
          (sharpInstSample momentOrderExpLaw sharpInstOutcome)
          (featureLineVec (1 / 3 + 1 / ((n : ℝ) + 1))) true n ω) atTop (fun _ => 5 / 3) := by
  have ht : (0 : ℝ) < 1 / 3 := by norm_num
  obtain ⟨hexp, ε, hε, hdir⟩ := oneSided_hypotheses_momentOrderExpLaw ht (by norm_num)
  have htn : Tendsto (fun n : ℕ => featureLineVec (1 / 3 + 1 / ((n : ℝ) + 1))) atTop
      (𝓝 (featureLineVec (1 / 3))) := tendsto_pi_nhds.2 fun _ => by
    simpa [featureLineVec] using
      (tendsto_const_nhds (x := (1 / 3 : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcov := sharpInstTrial_covLaw (lam := momentOrderExpLaw) (f := sharpInstOutcome)
  have h := commonLimit_reportedMoments_arm_of_isMinOn_oneSided (W := fun _ => ())
    (G := fun n _ => featureLineVec (1 / 3 + 1 / ((n : ℝ) + 1))) (t := featureLineVec (1 / 3))
    (isRandomizedTwoArm_sharpInstTrial measurable_sharpInstOutcome) unboundedInst_memLp
    measurable_id (by rw [hcov, Measure.map_id]; exact mem_interior_momentOrderExpLaw ht)
    (by rw [hcov]; exact isMinOn_sharpDualObjective_momentOrderExpLaw ht)
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by rw [hcov]; exact hexp) hε (by rw [hcov]; exact hdir) unboundedInst_regression
    (isIIDSample_sharpInstSample measurable_sharpInstOutcome)
    (measurable_sharpInstSample measurable_sharpInstOutcome)
    (map_sharpInstSample measurable_sharpInstOutcome 0) measurable_const
    (indepFun_const_left _ _) (fun _ => measurable_const)
    (tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all _ fun _ => htn)) true (unboundedInst_variance true)
  have hv : interactionDesign true (featureLineVec (1 / 3)) ⬝ᵥ commonLimitExampleCoef = 5 / 3 := by
    change featureInteractionDesign id true (featureLineVec (1 / 3)) ⬝ᵥ _ = _
    rw [featureInteractionDesign_dotProduct_sharpInstOutcome]
    norm_num [sharpInstOutcome, featureLineVec]
  rw [hv] at h
  exact h

end Instance

end PopulationAdjustment

end CausalInference
