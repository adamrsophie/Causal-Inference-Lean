/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStage

/-!
# Two-stage estimation with several types of switching

TSD 24, Section 4.2.3.1 ("Adjusting for multiple types of switching") allows several
subsequent treatments, each with its own effect. Here every adjusted switcher has a type
`κ ω` in a finite set of subsequent treatments, and the structural model has one parameter
`θ k` per type. This is the positive companion of `TwoStageTrial.not_pooled_of_ne`, which shows
that a single pooled parameter cannot recover the untreated times when the effects differ.

## Main results

* `TwoStageTrial.typePop`: the stage-one population of type `k`, the switchers of type `k`
  together with the non-switchers.
* `TwoStageTrial.modelOn_typePop`: the structural model with type-specific parameters gives the
  structural model with parameter `θ k` on the population of type `k`.
* `TwoStageTrial.typeStageOne_eq_zero`, `TwoStageTrial.typeStageOne_eq_zero_iff`: stage one run
  within each type against the non-switchers has the true type-specific parameter as a root,
  the unique one under relevance.
* `TwoStageTrial.typeAdjusted_eq`: transforming each switcher with the parameter of its type
  recovers the untreated time.
* `TwoStageTrial.typeAnalysis_meanContrast`: the stage-two contrast with the control arm
  transformed type by type is the hypothetical estimand
  `SwitchingTrial.hypotheticalEffect`.
-/

@[expose] public section

open MeasureTheory Finset

namespace CausalInference

namespace StructuralNested

namespace TwoStageTrial

variable {Ω : Type*} (M : TwoStageTrial Ω) {𝓚 : Type*}

/-- The structural model with one parameter per type of subsequent treatment: every patient
follows `U = adjusted B (θ (κ ω))`, so adjusted switchers of type `k` have the time ratio
`exp (θ k)` after `B`, and non-switchers are untreated. -/
def TypeModel (B : Ω → ℝ) (κ : Ω → 𝓚) (θ : 𝓚 → ℝ) : Prop :=
  (M.toSwitchingTrial B).FollowsModel fun ω => θ (κ ω)

/-- The transformation with the parameter of each patient's type. -/
noncomputable def typeAdjusted (B : Ω → ℝ) (κ : Ω → 𝓚) (θ : 𝓚 → ℝ) (ω : Ω) : ℝ :=
  M.adjusted B (θ (κ ω)) ω

/-- **Transforming each switcher with the parameter of its type recovers the untreated time.** -/
theorem typeAdjusted_eq {B : Ω → ℝ} {κ : Ω → 𝓚} {θ : 𝓚 → ℝ} (h : M.TypeModel B κ θ) :
    M.typeAdjusted B κ θ = M.U :=
  funext fun ω => (M.U_eq_of_followsModel h ω).symm

section StageOne

variable [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝓚] {𝓛 : Type*} [Fintype 𝓛] [DecidableEq 𝓛]

/-- The stage-one population of type `k` within `P`: the adjusted switchers of type `k` and the
non-switchers. -/
def typePop (P : Finset Ω) (κ : Ω → 𝓚) (k : 𝓚) : Finset Ω :=
  P.filter fun ω => M.X ω = false ∨ κ ω = k

omit [Fintype Ω] [DecidableEq Ω] in
/-- The type-specific structural model gives the structural model with parameter `θ k` on the
population of type `k`: switchers of type `k` have the parameter `θ k`, and non-switchers have
no treated time. -/
theorem modelOn_typePop {B : Ω → ℝ} {κ : Ω → 𝓚} {θ : 𝓚 → ℝ} (h : M.TypeModel B κ θ)
    (P : Finset Ω) (k : 𝓚) : M.ModelOn (M.typePop P κ k) B (θ k) := by
  intro ω hω
  rw [M.U_eq_of_followsModel h ω]
  rcases (mem_filter.1 hω).2 with hX | hk
  · rw [M.adjusted_of_not_switch B _ hX, M.adjusted_of_not_switch B _ hX]
  · rw [hk]

/-- **Stage one within each type has the true type-specific parameter as a root.** Under the
type-specific structural model, no unmeasured confounding at the secondary baseline for the
comparison of the switchers of type `k` with the non-switchers, and positivity, the stage-one
equation on the population of type `k` vanishes at `θ k`. -/
theorem typeStageOne_eq_zero {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {w : 𝓛 → ℝ}
    {B : Ω → ℝ} {κ : Ω → 𝓚} {θ : 𝓚 → ℝ} (h : M.TypeModel B κ θ) {k : 𝓚}
    (hnuc : M.BaselineNUC p (M.typePop P κ k) L)
    (hpos : M.BaselinePositive p (M.typePop P κ k) L w) :
    M.stageOne p (M.typePop P κ k) L w B (θ k) = 0 :=
  M.stageOne_eq_zero (M.modelOn_typePop h P k) hnuc hpos

/-- Under relevance for the type `k`, `θ k` is the only root. -/
theorem typeStageOne_eq_zero_iff {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛} {w : 𝓛 → ℝ}
    {B : Ω → ℝ} {κ : Ω → 𝓚} {θ : 𝓚 → ℝ} (h : M.TypeModel B κ θ) {k : 𝓚}
    (hnuc : M.BaselineNUC p (M.typePop P κ k) L)
    (hpos : M.BaselinePositive p (M.typePop P κ k) L w)
    (hrel : 0 < M.stageOneSlope p (M.typePop P κ k) L w B) (ψ : ℝ) :
    M.stageOne p (M.typePop P κ k) L w B ψ = 0 ↔ ψ = θ k :=
  M.stageOne_eq_zero_iff (M.typeStageOne_eq_zero h hnuc hpos) hrel ψ

end StageOne

section StageTwo

variable [MeasurableSpace Ω] {μ : Measure Ω}

/-- The analysis data with the control arm transformed type by type. -/
noncomputable def typeAnalysisTime (B : Ω → ℝ) (κ : Ω → 𝓚) (θ : 𝓚 → ℝ) (ω : Ω) : ℝ :=
  if M.R ω then M.T ω else M.typeAdjusted B κ θ ω

/-- **The stage-two contrast with type-specific parameters targets the hypothetical
estimand**: if the control arm follows the type-specific structural model, the mean contrast of
the experimental arm as observed against the control arm transformed type by type is
`E[T | R = 1] - E[U | R = 0]`. -/
theorem typeAnalysis_meanContrast (B : Ω → ℝ) {κ : Ω → 𝓚} {θ : 𝓚 → ℝ}
    (hR : Measurable M.R) (h : ∀ ω, M.R ω = false → M.U ω = M.typeAdjusted B κ θ ω) :
    (M.toSwitchingTrial B).meanContrast μ (M.typeAnalysisTime B κ θ) =
      (M.toSwitchingTrial B).hypotheticalEffect μ := by
  have e1 := (armMean_armLaw_congr (μ := μ) (N := M.toSwitchingTrial B)
    (f := M.typeAnalysisTime B κ θ) (g := M.T) hR (r := true) fun ω hω => by
      have hω' : M.R ω = true := hω
      simp [typeAnalysisTime, hω']).1
  have e0 := (armMean_armLaw_congr (μ := μ) (N := M.toSwitchingTrial B)
    (f := M.typeAnalysisTime B κ θ) (g := M.U) hR (r := false) fun ω hω => by
      have hω' : M.R ω = false := hω
      simp [typeAnalysisTime, hω', h ω hω']).1
  rw [SwitchingTrial.meanContrast, SwitchingTrial.hypotheticalEffect, e1, e0]
  rfl

/-- The type-specific structural model in the whole trial gives the hypothesis of
`typeAnalysis_meanContrast`. -/
theorem typeAnalysis_meanContrast_of_typeModel (B : Ω → ℝ) {κ : Ω → 𝓚} {θ : 𝓚 → ℝ}
    (hR : Measurable M.R) (h : M.TypeModel B κ θ) :
    (M.toSwitchingTrial B).meanContrast μ (M.typeAnalysisTime B κ θ) =
      (M.toSwitchingTrial B).hypotheticalEffect μ :=
  M.typeAnalysis_meanContrast B hR fun ω _ => (congrFun (M.typeAdjusted_eq h) ω).symm

end StageTwo

end TwoStageTrial

end StructuralNested

end CausalInference
