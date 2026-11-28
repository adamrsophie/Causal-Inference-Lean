/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.WeightedMomentOrderSetting
public import CausalInference.PopulationAdjustment.WeightedMomentOrderCommonLimit
public import CausalInference.PopulationAdjustment.WeightedMomentOrderReparam

/-!
# The theorems under exponential moments of all orders as corollaries

The consistency theorems for the trial of a setting, the common limit theorems at random
reported moments and the theorem for features in a proper affine subspace assume
`E[exp(κ ‖φ(X) - t‖)] < ∞` for every `κ`. Their versions with a minimizer `β*` of the population
dual objective and one moment of order `κ > 2 p ‖β*‖` imply them: under the interior condition,
moments of all orders give such a minimizer and such a moment
(`exists_isMinOn_sharpDualObjective_of_allOrders`). Each theorem `X` is restated here as
`X_of_allOrders`, with the same hypotheses and conclusion, and proved from `X_of_isMinOn`.

The only additional step is that the covariate law is a probability measure when the law of the
records is that of a measurable record of a probability space
(`isProbabilityMeasure_covLaw_of_map_eq`).

## Main results

* `isProbabilityMeasure_covLaw_of_map_eq`.
* `anchoredWeightedEstimate_isConsistent_setting_of_allOrders`,
  `unanchoredWeightedEstimate_isConsistent_setting_of_allOrders`.
* `commonLimit_reportedMoments_arm_of_allOrders`,
  `commonLimit_reportedMoments_armMean_of_allOrders`,
  `commonLimit_reportedMoments_unanchored_of_allOrders`,
  `commonLimit_reportedMoments_anchored_of_allOrders`,
  `commonLimit_reportedMoments_anchored_identity_of_allOrders`.
* `sampleBalancedArmMean_isConsistent_trial_reparam_of_allOrders`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology ENNReal

namespace CausalInference

namespace PopulationAdjustment

open PointTreatment IndirectComparison EffectMeasure Transport

section Law

variable {Ω₁ 𝒳 ι : Type*} [MeasurableSpace Ω₁] [MeasurableSpace 𝒳] [MeasurableSpace ι]

/-- **The covariate law of a trial is a probability measure when the law of its records is the
law of a measurable record of a probability space.** -/
theorem isProbabilityMeasure_covLaw_of_map_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Trial Ω₁ 𝒳 ι} (hX : Measurable T.X) (hA : Measurable T.A)
    (hYo : Measurable T.obsOutcome) {O : ℕ → Ω → 𝒳 × ι × ℝ} (hOm : ∀ i, Measurable (O i))
    (hlaw : P.map (O 0) = T.ipdLaw) : IsProbabilityMeasure T.covLaw := by
  have hf : Measurable fun ω => (T.X ω, T.A ω, T.obsOutcome ω) := hX.prodMk (hA.prodMk hYo)
  have : IsProbabilityMeasure (T.μ.map fun ω => (T.X ω, T.A ω, T.obsOutcome ω)) := by
    change IsProbabilityMeasure T.ipdLaw
    rw [← hlaw]
    exact (Measure.isProbabilityMeasure_map_iff (hOm 0).aemeasurable).2 inferInstance
  have : IsProbabilityMeasure T.μ := Measure.isProbabilityMeasure_of_map hf.aemeasurable
  exact T.isProbabilityMeasure_covLaw hX

end Law

section Setting

variable {Ω₁ Ω₂ Ω₃ Ω 𝒳 ι 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [MeasurableSpace Ω₃] [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [DecidableEq ι] [MeasurableSpace 𝒲] {p : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`anchoredWeightedEstimate_isConsistent_setting` as a corollary.** The hypotheses and the
conclusion of `anchoredWeightedEstimate_isConsistent_setting`. Exponential moments of all orders
give a minimizer `β*` of the population dual objective and a finite moment of some order `κ >
2p‖β*‖` (`exists_isMinOn_sharpDualObjective_of_allOrders`), and
`anchoredWeightedEstimate_isConsistent_setting_of_isMinOn` applies. -/
theorem anchoredWeightedEstimate_isConsistent_setting_of_allOrders
    {S : AnchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.ipdTrial.μ] [IsFiniteMeasure S.agdTrial.μ]
    [IsProbabilityMeasure S.target.μ] {m₁ m₂ m : ι → 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions id Set.univ m₁ m₂ m) (hac : S.a ≠ S.c)
    (hA : Measurable S.ipdTrial.A) (hYa : Measurable (S.ipdTrial.Y S.a))
    (hYc : Measurable (S.ipdTrial.Y S.c))
    (hAac : ∀ᵐ ω ∂S.ipdTrial.μ, S.ipdTrial.A ω = S.a ∨ S.ipdTrial.A ω = S.c)
    (hra : IndepFun S.ipdTrial.A (fun ω => (S.ipdTrial.X ω, S.ipdTrial.Y S.a ω)) S.ipdTrial.μ)
    (hrc : IndepFun S.ipdTrial.A (fun ω => (S.ipdTrial.X ω, S.ipdTrial.Y S.c ω)) S.ipdTrial.μ)
    (hqa : 0 < S.ipdTrial.μ.real (S.ipdTrial.A ⁻¹' {S.a}))
    (hqc : 0 < S.ipdTrial.μ.real (S.ipdTrial.A ⁻¹' {S.c}))
    {R : ℕ → Ω → 𝒳 × ι × ℝ} (hR : IsIIDSample R P) (hRm : ∀ i, Measurable (R i))
    (hlaw : P.map (R 0) = S.ipdTrial.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (S.ipdTrial.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) S.ipdTrial.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWR : IndepFun W (fun ω k => R k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hrA : Integrable (fun ω => (S.ipdTrial.Y S.a ω - m₁ S.a (S.ipdTrial.X ω)) ^ 2)
      S.ipdTrial.μ)
    (hrC : Integrable (fun ω => (S.ipdTrial.Y S.c ω - m₁ S.c (S.ipdTrial.X ω)) ^ 2)
      S.ipdTrial.μ) {σ2 : ℝ}
    (hvA : S.ipdTrial.μ[fun ω => (S.ipdTrial.Y S.a ω - m₁ S.a (S.ipdTrial.X ω)) ^ 2 |
      MeasurableSpace.comap S.ipdTrial.X inferInstance] ≤ᵐ[S.ipdTrial.μ] fun _ => σ2)
    (hvC : S.ipdTrial.μ[fun ω => (S.ipdTrial.Y S.c ω - m₁ S.c (S.ipdTrial.X ω)) ^ 2 |
      MeasurableSpace.comap S.ipdTrial.X inferInstance] ≤ᵐ[S.ipdTrial.μ] fun _ => σ2)
    {a0 c0 : ℝ} {b d : Fin p → ℝ} (hafA : ∀ x, m₁ S.a x = a0 + b ⬝ᵥ φ x)
    (hafC : ∀ x, m₁ S.c x = c0 + d ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k) {dBC : ℕ → Ω → ℝ}
    (hd : IsConsistent dBC (∫ x, linkContrast id (m₂ S.b) (m₂ S.c) x ∂S.target.covLaw) P) :
    IsConsistent (fun n => anchoredWeightedEstimate id
        (fun ω => balancingWeights fun i : Fin n => φ (R i ω).1 - G n (W ω))
        (fun ω i => (R i ω).2.1) (fun ω i => (R i ω).2.2) S.a S.c (dBC n))
      (S.target.marginalEffect id S.a S.b) P := by
  have hX := hS.measurable_ipd
  obtain ⟨-, hR'm, hlaw', -⟩ :=
    S.ipdTrial.isIIDSample_twoArmRecord hac hX hA hYa hYc hAac hR hRm hlaw
  have hA' := S.ipdTrial.measurable_twoArmView_A hA S.a S.c
  have : IsProbabilityMeasure S.ipdTrial.covLaw :=
    isProbabilityMeasure_covLaw_of_map_eq (T := S.ipdTrial.twoArmView S.a S.c) hX hA'
      (measurable_obsOutcome_bool hA' hYa hYc) hR'm hlaw'
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hφ hint hexp
  exact anchoredWeightedEstimate_isConsistent_setting_of_isMinOn (hS := hS) (hac := hac) (hA := hA)
    (hYa := hYa) (hYc := hYc) (hAac := hAac) (hra := hra) (hrc := hrc) (hqa := hqa) (hqc := hqc)
    (hR := hR) (hRm := hRm) (hlaw := hlaw) (hφ := hφ) (hint := hint) (hexp := hexp1) (hW := hW)
    (hWR := hWR) (hG := hG) (htm := htm) (hrA := hrA) (hrC := hrC) (hvA := hvA) (hvC := hvC)
    (hafA := hafA) (hafC := hafC) (hQφ := hQφ) (ht := ht) (hd := hd) (hmin := hmin) (hκ := hκ)

/-- **`unanchoredWeightedEstimate_isConsistent_setting` as a corollary.** The hypotheses and the
conclusion of `unanchoredWeightedEstimate_isConsistent_setting`. Exponential moments of all orders
give a minimizer `β*` of the population dual objective and a finite moment of some order `κ >
2p‖β*‖` (`exists_isMinOn_sharpDualObjective_of_allOrders`), and
`unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn` applies. -/
theorem unanchoredWeightedEstimate_isConsistent_setting_of_allOrders
    {S : UnanchoredSetting Ω₁ Ω₂ Ω₃ 𝒳 ι}
    [IsFiniteMeasure S.sourceA.μ] [IsFiniteMeasure S.sourceB.μ]
    [IsProbabilityMeasure S.target.μ] {D : Set ℝ} {ma mb : 𝒳 → ℝ}
    (hS : S.IdentificationAssumptions D ma mb) {T : Trial Ω₁ 𝒳 ι}
    (hsrc : T.toPopulation = S.sourceA) {c : ι} (hac : S.a ≠ c)
    (hA : Measurable T.A) (hYa : Measurable (T.Y S.a)) (hYc : Measurable (T.Y c))
    (hAac : ∀ᵐ ω ∂T.μ, T.A ω = S.a ∨ T.A ω = c)
    (hra : IndepFun T.A (fun ω => (T.X ω, T.Y S.a ω)) T.μ)
    (hqa : 0 < T.μ.real (T.A ⁻¹' {S.a}))
    {R : ℕ → Ω → 𝒳 × ι × ℝ} (hR : IsIIDSample R P) (hRm : ∀ i, Measurable (R i))
    (hlaw : P.map (R 0) = T.ipdLaw)
    {φ : 𝒳 → Fin p → ℝ} (hφ : Measurable φ) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map φ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖φ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWR : IndepFun W (fun ω k => R k ω) P)
    {G : ℕ → 𝒲 → Fin p → ℝ} (hG : ∀ n, Measurable (G n))
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => t))
    (hres2 : Integrable (fun ω => (T.Y S.a ω - ma (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y S.a ω - ma (T.X ω)) ^ 2 | MeasurableSpace.comap T.X
      inferInstance] ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, ma x = a0 + b ⬝ᵥ φ x)
    (hQφ : ∀ k, Integrable (fun x => φ x k) S.target.covLaw)
    (ht : ∀ k, ∫ x, φ x k ∂S.target.covLaw = t k)
    {mB : ℕ → Ω → ℝ} (hmB : IsConsistent mB (∫ x, mb x ∂S.target.covLaw) P) {g : ℝ → ℝ}
    (hga : ContinuousAt g (S.target.armMean S.a)) (hgb : ContinuousAt g (S.target.armMean S.b)) :
    IsConsistent (fun n ω => g (mB n ω) - g (weightedArmMean
        (balancingWeights fun i : Fin n => φ (R i ω).1 - G n (W ω))
        (fun i => (R i ω).2.1) (fun i => (R i ω).2.2) S.a))
      (S.target.marginalEffect g S.a S.b) P := by
  have hX : Measurable T.X := by
    have := hS.measurable_sourceA
    rw [← hsrc] at this
    exact this
  obtain ⟨-, hR'm, hlaw', -⟩ := T.isIIDSample_twoArmRecord hac hX hA hYa hYc hAac hR hRm hlaw
  have hA' := T.measurable_twoArmView_A hA S.a c
  have : IsProbabilityMeasure T.covLaw :=
    isProbabilityMeasure_covLaw_of_map_eq (T := T.twoArmView S.a c) hX hA'
      (measurable_obsOutcome_bool hA' hYa hYc) hR'm hlaw'
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hφ hint hexp
  exact unanchoredWeightedEstimate_isConsistent_setting_of_isMinOn (hS := hS) (hsrc := hsrc)
    (hac := hac) (hA := hA) (hYa := hYa) (hYc := hYc) (hAac := hAac) (hra := hra) (hqa := hqa)
    (hR := hR) (hRm := hRm) (hlaw := hlaw) (hφ := hφ) (hint := hint) (hexp := hexp1) (hW := hW)
    (hWR := hWR) (hG := hG) (htm := htm) (hres2 := hres2) (hvar := hvar) (haff := haff) (hQφ := hQφ)
    (ht := ht) (hmB := hmB) (hga := hga) (hgb := hgb) (hmin := hmin) (hκ := hκ)

end Setting

section Arm

variable {Ω₁ Ξ 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ξ] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ξ}
  {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ} {t : Fin p → ℝ}
  {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲} {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **`commonLimit_reportedMoments_arm` as a corollary.** The hypotheses and the conclusion of
`commonLimit_reportedMoments_arm`. Exponential moments of all orders give a minimizer `β*` of the
population dual objective and a finite moment of some order `κ > 2p‖β*‖`
(`exists_isMinOn_sharpDualObjective_of_allOrders`), and `commonLimit_reportedMoments_arm_of_isMinOn`
applies. -/
theorem commonLimit_reportedMoments_arm_of_allOrders
    [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
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
  have := T.isProbabilityMeasure_covLaw hT.measurable_X
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hφ hint hexp
  exact commonLimit_reportedMoments_arm_of_isMinOn (hT := hT) (hY2 := hY2) (hφ := hφ) (hint := hint)
    (hexp := hexp1) (hreg := hreg) (hO := hO) (hOm := hOm) (hlaw := hlaw) (hW := hW) (hWO := hWO)
    (hG := hG) (htm := htm) (a := a) (hvar := hvar) (hmin := hmin) (hκ := hκ)

end Arm

section Target

variable {Ω₁ Ω₂ Ξ 𝒳 ι 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒲] {p : ℕ} {T : Trial Ω₁ 𝒳 Bool}
  {Q : Population Ω₂ 𝒳 ι} {P : Measure Ξ} {O : ℕ → Ξ → 𝒳 × Bool × ℝ} {φ : 𝒳 → Fin p → ℝ}
  {t : Fin p → ℝ} {ξ₀ : Option (Fin p) ⊕ Option (Fin p) → ℝ} {W : Ξ → 𝒲}
  {G : ℕ → 𝒲 → Fin p → ℝ}

/-- **`commonLimit_reportedMoments_armMean` as a corollary.** The hypotheses and the conclusion of
`commonLimit_reportedMoments_armMean`. Exponential moments of all orders give a minimizer `β*` of
the population dual objective and a finite moment of some order `κ > 2p‖β*‖`
(`exists_isMinOn_sharpDualObjective_of_allOrders`), and
`commonLimit_reportedMoments_armMean_of_isMinOn` applies. -/
theorem commonLimit_reportedMoments_armMean_of_allOrders
    [IsProbabilityMeasure T.μ] [IsProbabilityMeasure P]
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
  have := T.isProbabilityMeasure_covLaw hT.measurable_X
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hφ hint hexp
  exact commonLimit_reportedMoments_armMean_of_isMinOn (hT := hT) (hY2 := hY2) (hφ := hφ)
    (hint := hint) (hexp := hexp1) (hreg := hreg) (hO := hO) (hOm := hOm) (hlaw := hlaw) (hW := hW)
    (hWO := hWO) (hG := hG) (htm := htm) (a := a) (hvar := hvar) (hX₂ := hX₂) (hQφ := hQφ)
    (ht := ht) (hYQ := hYQ) (hsi := hsi) (hov := hov) (hmin := hmin) (hκ := hκ)

/-- **`commonLimit_reportedMoments_unanchored` as a corollary.** The hypotheses and the conclusion
of `commonLimit_reportedMoments_unanchored`. Exponential moments of all orders give a minimizer `β*`
of the population dual objective and a finite moment of some order `κ > 2p‖β*‖`
(`exists_isMinOn_sharpDualObjective_of_allOrders`), and
`commonLimit_reportedMoments_unanchored_of_isMinOn` applies. -/
theorem commonLimit_reportedMoments_unanchored_of_allOrders [IsProbabilityMeasure T.μ]
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
  have := T.isProbabilityMeasure_covLaw hT.measurable_X
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hφ hint hexp
  exact commonLimit_reportedMoments_unanchored_of_isMinOn (hT := hT) (hY2 := hY2) (hφ := hφ)
    (hint := hint) (hexp := hexp1) (hreg := hreg) (hO := hO) (hOm := hOm) (hlaw := hlaw) (hW := hW)
    (hWO := hWO) (hG := hG) (htm := htm) (hvar := hvar) (hX₂ := hX₂) (hQφ := hQφ) (ht := ht)
    (hYQ := hYQ) (hsi := hsi) (hov := hov) (hmb := hmb) (hga := hga) (hgb := hgb) (hmin := hmin)
    (hκ := hκ)

/-- **`commonLimit_reportedMoments_anchored` as a corollary.** The hypotheses and the conclusion of
`commonLimit_reportedMoments_anchored`. Exponential moments of all orders give a minimizer `β*` of
the population dual objective and a finite moment of some order `κ > 2p‖β*‖`
(`exists_isMinOn_sharpDualObjective_of_allOrders`), and
`commonLimit_reportedMoments_anchored_of_isMinOn` applies. -/
theorem commonLimit_reportedMoments_anchored_of_allOrders [IsProbabilityMeasure T.μ]
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
  have := T.isProbabilityMeasure_covLaw hT.measurable_X
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hφ hint hexp
  exact commonLimit_reportedMoments_anchored_of_isMinOn (hT := hT) (hY2 := hY2) (hφ := hφ)
    (hint := hint) (hexp := hexp1) (hreg := hreg) (hO := hO) (hOm := hOm) (hlaw := hlaw) (hW := hW)
    (hWO := hWO) (hG := hG) (htm := htm) (hvar := hvar) (hX₂ := hX₂) (hQφ := hQφ) (ht := ht)
    (hYQa := hYQa) (hYQc := hYQc) (hsia := hsia) (hsic := hsic) (hov := hov) (hdbc := hdbc)
    (hga := hga) (hgc := hgc) (hmin := hmin) (hκ := hκ)

/-- **`commonLimit_reportedMoments_anchored_identity` as a corollary.** The hypotheses and the
conclusion of `commonLimit_reportedMoments_anchored_identity`. Exponential moments of all orders
give a minimizer `β*` of the population dual objective and a finite moment of some order `κ >
2p‖β*‖` (`exists_isMinOn_sharpDualObjective_of_allOrders`), and
`commonLimit_reportedMoments_anchored_identity_of_isMinOn` applies. -/
theorem commonLimit_reportedMoments_anchored_identity_of_allOrders [IsProbabilityMeasure T.μ]
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
  have := T.isProbabilityMeasure_covLaw hT.measurable_X
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hφ hint hexp
  exact commonLimit_reportedMoments_anchored_identity_of_isMinOn (hT := hT) (hY2 := hY2) (hφ := hφ)
    (hint := hint) (hexp := hexp1) (hreg := hreg) (hO := hO) (hOm := hOm) (hlaw := hlaw) (hW := hW)
    (hWO := hWO) (hG := hG) (htm := htm) (hvar := hvar) (hX₂ := hX₂) (hQφ := hQφ) (ht := ht)
    (hYQa := hYQa) (hYQc := hYQc) (hrel := hrel) (hdbc := hdbc) (hmin := hmin) (hκ := hκ)

end Target

section Reparam

variable {Ω₁ Ω 𝒳 𝒲 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  [MeasurableSpace 𝒲] {p q : ℕ} {T : Trial Ω₁ 𝒳 Bool} {P : Measure Ω} [IsProbabilityMeasure P]
  {O : ℕ → Ω → 𝒳 × Bool × ℝ}

/-- **`sampleBalancedArmMean_isConsistent_trial_reparam` as a corollary.** The hypotheses and the
conclusion of `sampleBalancedArmMean_isConsistent_trial_reparam`. Exponential moments of all orders
give a minimizer `β*` of the population dual objective and a finite moment of some order `κ >
2p‖β*‖` (`exists_isMinOn_sharpDualObjective_of_allOrders`), and
`sampleBalancedArmMean_isConsistent_trial_reparam_of_isMinOn` applies. -/
theorem sampleBalancedArmMean_isConsistent_trial_reparam_of_allOrders (hX : Measurable T.X)
    (hA : Measurable T.A) (hYo : Measurable T.obsOutcome) (a : Bool)
    (hYa : Measurable (T.Y a)) (hrand : IndepFun T.A (fun ω => (T.X ω, T.Y a ω)) T.μ)
    (hO : IsIIDSample O P) (hOm : ∀ i, Measurable (O i)) (hlaw : P.map (O 0) = T.ipdLaw)
    {φ : 𝒳 → Fin q → ℝ} (hφ : Measurable φ) {ψ : 𝒳 → Fin p → ℝ} (hψ : Measurable ψ)
    {M : Matrix (Fin q) (Fin p) ℝ} {N : Matrix (Fin p) (Fin q) ℝ} (hNM : N * M = 1)
    {c : Fin q → ℝ} (hrep : ∀ᵐ x ∂T.covLaw, φ x = c + M *ᵥ ψ x) {t : Fin p → ℝ}
    (hint : t ∈ interior (closedConvexHull ℝ (T.covLaw.map ψ).support))
    (hexp : ∀ κ : ℝ, Integrable (fun x => Real.exp (κ * ‖ψ x - t‖)) T.covLaw)
    {W : Ω → 𝒲} (hW : Measurable W) (hWO : IndepFun W (fun ω k => O k ω) P)
    {G : ℕ → 𝒲 → Fin q → ℝ} (hG : ∀ n, Measurable (G n))
    (hGE : ∀ n w, ∃ u, G n w = c + M *ᵥ u)
    (htm : TendstoInMeasure P (fun n ω => G n (W ω)) atTop (fun _ => c + M *ᵥ t))
    (hq : 0 < T.μ.real (T.A ⁻¹' {a})) {m : 𝒳 → ℝ} (hm : T.IsCondMean a m)
    (hres2 : Integrable (fun ω => (T.Y a ω - m (T.X ω)) ^ 2) T.μ) {σ2 : ℝ}
    (hvar : T.μ[fun ω => (T.Y a ω - m (T.X ω)) ^ 2 | MeasurableSpace.comap T.X inferInstance]
      ≤ᵐ[T.μ] fun _ => σ2)
    {a0 : ℝ} {b : Fin p → ℝ} (haff : ∀ x, m x = a0 + b ⬝ᵥ ψ x) :
    IsConsistent (fun n ω => sampleBalancedArmMean φ (G n (W ω)) O a n ω) (a0 + b ⬝ᵥ t) P := by
  have := isProbabilityMeasure_covLaw_of_map_eq hX hA hYo hOm hlaw
  obtain ⟨βs, hmin, κ, hexp1, hκ⟩ :=
    exists_isMinOn_sharpDualObjective_of_allOrders hψ hint hexp
  exact sampleBalancedArmMean_isConsistent_trial_reparam_of_isMinOn (hX := hX) (hA := hA)
    (hYo := hYo) (a := a) (hYa := hYa) (hrand := hrand) (hO := hO) (hOm := hOm) (hlaw := hlaw)
    (hφ := hφ) (hψ := hψ) (hNM := hNM) (hrep := hrep) (hint := hint) (hexp := hexp1) (hW := hW)
    (hWO := hWO) (hG := hG) (hGE := hGE) (htm := htm) (hq := hq) (hm := hm) (hres2 := hres2)
    (hvar := hvar) (haff := haff) (hmin := hmin) (hκ := hκ)

end Reparam

end PopulationAdjustment

end CausalInference
