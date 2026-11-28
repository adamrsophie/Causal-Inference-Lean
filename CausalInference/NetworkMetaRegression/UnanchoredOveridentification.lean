/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredLocalIdentification

/-!
# Overidentification from aggregate subgroup means

Let study `j_B` report the aggregate means `θ_z` of `b` in `Z` subgroups with covariate laws
`F_1, …, F_Z`. Under shared prognostic effects the slope of `b` is the slope `β` of `a`, which
the individual data identify, and each subgroup alone identifies the cell intercept of `b` as
the calibrated shift `c_z = c_{F_z}(β, θ_z)`. With two or more subgroups the model therefore
imposes the **testable restriction** `c_1 = … = c_Z` on the data
(`calibratedShift_subgroups_eq`); data violating it come from no model with shared prognostic
effects (`unanchoredSubgroupData_ne_of_calibratedShift_ne`), and such data exist
(`unanchoredSubgroupData_ne_instance`).

## Main definitions

* `MultilevelModel.unanchoredSubgroupData`.

## Main results

* `calibratedShift_subgroups_eq`, `unanchoredSubgroupData_ne_of_calibratedShift_ne`,
  `calibratedShift_subgroups_eq_instance`,
  `unanchoredSubgroupData_ne_instance`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory NetworkMetaAnalysis

namespace MultilevelModel

variable {J K : Type*} {p Z : ℕ}

/-- The **unanchored data with aggregate subgroup means**: the individual data law of `a` in study
`j_A` (as in `unanchoredData`) and the aggregate means of `b` in study `j_B` in the subgroups with
covariate laws `F z`. -/
noncomputable def unanchoredSubgroupData (π : Kernel ℝ ℝ) {ginv : ℝ → ℝ} (hginv : Measurable ginv)
    (FA : Measure (Fin p → ℝ)) (F : Fin Z → Measure (Fin p → ℝ)) (jA jB : J) (a b : K)
    (M : MultilevelModel J K p) : Measure ((Fin p → ℝ) × ℝ) × (Fin Z → ℝ) :=
  (FA ⊗ₘ π.comap (M.surface ginv (M.μ jA) a) (M.measurable_surface hginv _ a),
    fun z => M.armMean ginv (M.μ jB) (F z) b)

variable {ginv : ℝ → ℝ} {F : Fin Z → Measure (Fin p → ℝ)} [∀ z, IsProbabilityMeasure (F z)]
  {jA jB : J} {a b : K}

/-- **The testable restriction.** Let `g⁻¹` be strictly increasing and let `a` and `b` share
their effect modifiers in `M`, with integrable aggregate integrands of `b` under every subgroup
law. Then the calibrated shifts at the slope of `a` and the subgroup means of `b` are the same in
any two subgroups `z`, `z'` (both are the cell intercept `μ_{j_B} + γ_b`). -/
theorem calibratedShift_subgroups_eq (hmono : StrictMono ginv) {M : MultilevelModel J K p}
    (hM : M.SharedEffectModifiers {a, b})
    (hint : ∀ z s, Integrable (fun x => ginv (s + x ⬝ᵥ M.cellSlope b)) (F z)) (z z' : Fin Z) :
    calibratedShift (F z) ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) (F z) b) =
      calibratedShift (F z') ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) (F z') b) := by
  have h : ∀ z, calibratedShift (F z) ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) (F z) b) =
      M.cellIntercept jB b := fun z =>
    ((unanchored_estimand_eq_calibrated (jA := jB) hmono (FB := F z) ⟨hM, hint z⟩
      (F z) id).1).symm
  rw [h z, h z']

/-- **Data violating the restriction come from no model with shared prognostic effects.** Let
the outcome kernel be indexed by its mean, `g⁻¹` strictly increasing, and `F_A` finite of full
affine rank. If the calibrated shifts at the slope of `a` of the subgroup means of `M` differ in
two subgroups, then no model `N` with shared effect modifiers for `{a, b}` (and integrable
aggregate integrands) has the data of `M`. -/
theorem unanchoredSubgroupData_ne_of_calibratedShift_ne {π : Kernel ℝ ℝ} [IsMarkovKernel π]
    (hπ : ∀ θ, ∫ y, y ∂π θ = θ) (hmono : StrictMono ginv) {FA : Measure (Fin p → ℝ)}
    [IsFiniteMeasure FA] (hFA : AffineRank FA) {M : MultilevelModel J K p} {z z' : Fin Z}
    (hne : calibratedShift (F z) ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) (F z) b) ≠
      calibratedShift (F z') ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) (F z') b))
    {N : MultilevelModel J K p} (hN : N.SharedEffectModifiers {a, b})
    (hint : ∀ z s, Integrable (fun x => ginv (s + x ⬝ᵥ N.cellSlope b)) (F z)) :
    unanchoredSubgroupData π hmono.monotone.measurable FA F jA jB a b N ≠
      unanchoredSubgroupData π hmono.monotone.measurable FA F jA jB a b M := by
  intro h
  simp only [unanchoredSubgroupData, Prod.mk.injEq] at h
  have hae := ae_surface_eq_of_compProd_eq hπ (fun x => Kernel.comap_apply _ _ x)
    (fun x => Kernel.comap_apply _ _ x) h.1
  have hslope : N.cellSlope a = M.cellSlope a := (cell_eq_of_ae_surface_eq hmono hFA hae).2
  have hz := calibratedShift_subgroups_eq (jB := jB) hmono hN hint z z'
  rw [hslope, congrFun h.2 z, congrFun h.2 z'] at hz
  exact hne hz

/-- **Instance of the testable restriction**: one covariate, the identity link, the subgroups
`δ_0`, `δ_1` and the model with cell intercept `μ_{j_B} + γ_b = 2` and common slope `1`; its
subgroup means of `b` are `2` and `3`, and both calibrated shifts are `2`. -/
theorem calibratedShift_subgroups_eq_instance :
    let M : MultilevelModel Bool Bool 1 := ⟨fun _ => 2, fun _ => 1, 0, 0⟩
    M.armMean id (M.μ false) (twoPointSubgroups 0) false = 2 ∧
      M.armMean id (M.μ false) (twoPointSubgroups 1) false = 3 ∧
      calibratedShift (twoPointSubgroups 0) id (M.cellSlope true)
          (M.armMean id (M.μ false) (twoPointSubgroups 0) false) =
        calibratedShift (twoPointSubgroups 1) id (M.cellSlope true)
          (M.armMean id (M.μ false) (twoPointSubgroups 1) false) := by
  intro M
  refine ⟨?_, ?_, calibratedShift_subgroups_eq strictMono_id
    (by rw [sharedEffectModifiers_iff]; intro _ _ _ _; rfl)
    (fun z s => by fin_cases z <;> exact integrable_dirac (by simp)) 0 1⟩ <;>
    simp [M, armMean, surface, eta, metaRegressionPredictor, twoPointSubgroups, dotProduct,
      show (2 : ℝ) + 1 = 3 by norm_num]

/-- **Instance: the restriction can fail.** One covariate, the identity link, the outcome
kernel `θ ↦ δ_θ`, `F_A = binaryLaw (1/2)` and the subgroups `δ_0`, `δ_1`. The model with all
parameters `0` except `β₂,b = 1` has subgroup means `0` and `1` of `b` and slope `0` of `a`, so
its calibrated shifts are `0` and `1`; no model with shared prognostic effects has its data. -/
theorem unanchoredSubgroupData_ne_instance :
    let M : MultilevelModel Bool Bool 1 := ⟨0, 0, 0, Function.update 0 false 1⟩
    calibratedShift (twoPointSubgroups 0) id (M.cellSlope true)
        (M.armMean id (M.μ false) (twoPointSubgroups 0) false) = 0 ∧
      calibratedShift (twoPointSubgroups 1) id (M.cellSlope true)
        (M.armMean id (M.μ false) (twoPointSubgroups 1) false) = 1 ∧
      ∀ N : MultilevelModel Bool Bool 1, N.SharedEffectModifiers {true, false} →
        unanchoredSubgroupData (Kernel.deterministic id measurable_id)
            (strictMono_id (α := ℝ)).monotone.measurable (binaryLaw (1 / 2)) twoPointSubgroups
            true false true false N ≠
          unanchoredSubgroupData (Kernel.deterministic id measurable_id)
            (strictMono_id (α := ℝ)).monotone.measurable (binaryLaw (1 / 2)) twoPointSubgroups
            true false true false M := by
  intro M
  have hshift : ∀ (z : Fin 2) (θ : ℝ),
      calibratedShift (twoPointSubgroups z) id (M.cellSlope true) θ = θ := fun z θ => by
    have hint : ∀ c, Integrable (fun x : Fin 1 → ℝ => id (c + x ⬝ᵥ M.cellSlope true))
        (twoPointSubgroups z) := fun c => by
      fin_cases z <;> exact integrable_dirac (by simp)
    have h0 : M.cellSlope true = 0 := by
      funext i; simp [M, cellSlope]
    have := calibratedShift_eq (F := twoPointSubgroups z) strictMono_id hint (c := θ)
    simpa [shiftMean, h0] using this
  have h0 : calibratedShift (twoPointSubgroups 0) id (M.cellSlope true)
      (M.armMean id (M.μ false) (twoPointSubgroups 0) false) = 0 := by
    rw [hshift]
    simp [M, armMean, surface, eta, metaRegressionPredictor, twoPointSubgroups, dotProduct]
  have h1 : calibratedShift (twoPointSubgroups 1) id (M.cellSlope true)
      (M.armMean id (M.μ false) (twoPointSubgroups 1) false) = 1 := by
    rw [hshift]
    simp [M, armMean, surface, eta, metaRegressionPredictor, twoPointSubgroups, dotProduct]
  refine ⟨h0, h1, fun N hN => ?_⟩
  have : IsFiniteMeasure (binaryLaw (1 / 2)) := by
    have := isProbabilityMeasure_binaryLaw_half; infer_instance
  have hπ : ∀ θ, ∫ y, y ∂(Kernel.deterministic (id : ℝ → ℝ) measurable_id) θ = θ := fun θ => by
    rw [Kernel.deterministic_apply, integral_dirac]; rfl
  refine unanchoredSubgroupData_ne_of_calibratedShift_ne (z := 0) (z' := 1) hπ strictMono_id
    affineRank_binaryLaw_half (by rw [h0, h1]; norm_num) hN fun z s => ?_
  fin_cases z <;> exact integrable_dirac (by simp)

end MultilevelModel

end NetworkMetaRegression

end CausalInference
