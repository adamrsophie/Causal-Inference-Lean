/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredEnvelope

/-!
# The models compatible with unanchored data form a continuous graph

Without shared prognostic effects the parameters `w = (β₂,b, γ_b)` of the comparator arm `b`
enter the unanchored data (`MultilevelModel.unanchoredData`) only through the aggregate mean
`θ_B` of `b` in study `j_B`. For every interaction `β` exactly one effect solves the calibration
equation: `Γ(β) = c(β₁ + β, θ_B) - μ_{j_B}` (`MultilevelModel.calibratedArmEffect`), with `c` the
calibrated shift under `F_B`. This file shows:

* **Continuity** (`MultilevelModel.continuous_calibratedArmEffect`): under a local envelope for
  `F_B`, `Γ` is continuous on `ℝ^p`, for a continuous, strictly increasing `g⁻¹`.
* **The solution set is the graph of `Γ`**
  (`MultilevelModel.unanchoredData_withArm_eq_iff`): the model `M.withArm b w` has the
  unanchored data of `M` exactly when `γ_b = Γ(β₂,b)`; among the models that differ from `M`
  only in the parameters of `b`, those with the data of `M` are exactly the models
  `M.withArm b (β, Γ β)` (`MultilevelModel.withArm_unanchoredData_eq_set`).
* **The solution set is homeomorphic to `ℝ^p`**
  (`MultilevelModel.nonempty_homeomorph_unanchoredSolutions`): `β ↦ (β, Γ β)` is a homeomorphism
  of `ℝ^p` onto the set of parameter pairs `(β₂,b, γ_b) ∈ ℝ^p × ℝ` compatible with the data. The
  model type carries no topology, so the topological statement is made for the parameter pair.

## Main definitions

* `graphHomeomorph`: the homeomorphism of a space onto the graph of a continuous function.
* `MultilevelModel.calibratedArmEffect`.

## Main results

* `MultilevelModel.continuous_calibratedArmEffect`,
  `MultilevelModel.unanchoredData_withArm_eq_iff`, `MultilevelModel.withArm_unanchoredData_eq_set`,
  `MultilevelModel.nonempty_homeomorph_unanchoredSolutions`.
* `unanchoredSolutions_instance`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology

variable {p : ℕ}

/-! ### The graph of a continuous function -/

/-- The **homeomorphism of `X` onto the graph** `{(x, y) | y = f x}` of a continuous function
`f : X → Y`: `x ↦ (x, f x)`, with inverse the first coordinate. -/
def graphHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) : X ≃ₜ {q : X × Y // q.2 = f q.1} where
  toFun x := ⟨(x, f x), rfl⟩
  invFun q := q.1.1
  left_inv _ := rfl
  right_inv q := Subtype.ext (Prod.ext rfl q.2.symm)
  continuous_toFun := (continuous_id.prodMk hf).subtype_mk _
  continuous_invFun := continuous_fst.comp continuous_subtype_val

namespace MultilevelModel

variable {J K : Type*}

/-- The **calibrated effect** of the comparator arm at interaction `β`: the effect `γ` that gives
the arm mean `θ` under `F` at the baseline `μ_{j_B}` with slope `β₁ + β`, that is
`c(β₁ + β, θ) - μ_{j_B}` with `c` the calibrated shift. -/
noncomputable def calibratedArmEffect (F : Measure (Fin p → ℝ)) (ginv : ℝ → ℝ)
    (M : MultilevelModel J K p) (jB : J) (θ : ℝ) (β : Fin p → ℝ) : ℝ :=
  calibratedShift F ginv (M.β₁ + β) θ - M.μ jB

variable {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F] {ginv : ℝ → ℝ}

/-- Under a local envelope, every mean in the range of a continuous, strictly increasing `g⁻¹`
is attained by the shift mean of every slope. -/
theorem exists_shiftMean_eq_of_mem_range (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hE : LocalEnvelope F ginv) (β : Fin p → ℝ) {θ : ℝ} (hθ : θ ∈ Set.range ginv) :
    ∃ c, shiftMean F ginv (fun x => x ⬝ᵥ β) c = θ := by
  have hdot : Measurable fun x : Fin p → ℝ => x ⬝ᵥ β :=
    (by unfold dotProduct; fun_prop : Continuous fun x : Fin p → ℝ => x ⬝ᵥ β).measurable
  rw [← range_shiftMean hmono hcont hdot fun c => hE.integrable hcont c β] at hθ
  exact hθ

/-- The arm mean of a model lies in the range of a continuous, strictly increasing `g⁻¹`, under
a local envelope. -/
theorem armMean_mem_range (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hE : LocalEnvelope F ginv) (M : MultilevelModel J K p) (α : ℝ) (k : K) :
    M.armMean ginv α F k ∈ Set.range ginv := by
  have hdot : Measurable fun x : Fin p → ℝ => x ⬝ᵥ M.cellSlope k :=
    (by unfold dotProduct; fun_prop :
      Continuous fun x : Fin p → ℝ => x ⬝ᵥ M.cellSlope k).measurable
  rw [← range_shiftMean hmono hcont hdot fun c => hE.integrable hcont c _]
  exact ⟨_, (armMean_eq_shiftMean ginv M α F k).symm⟩

/-- **The calibrated effect is continuous.** For a continuous, strictly increasing `g⁻¹` with a
local envelope under the probability law `F` and a mean `θ` in the range of `g⁻¹`, the map
`β ↦ c(β₁ + β, θ) - μ_{j_B}` is continuous on `ℝ^p`. At each `β` the mean `θ` is attained by
some shift, and the calibrated shift is jointly continuous there
(`continuousAt_calibratedShift`). -/
theorem continuous_calibratedArmEffect (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hE : LocalEnvelope F ginv) (M : MultilevelModel J K p) (jB : J) {θ : ℝ}
    (hθ : θ ∈ Set.range ginv) : Continuous (calibratedArmEffect F ginv M jB θ) := by
  refine continuous_iff_continuousAt.2 fun β => ?_
  obtain ⟨c, hc⟩ := exists_shiftMean_eq_of_mem_range hmono hcont hE (M.β₁ + β) hθ
  have h := continuousAt_calibratedShift hmono hcont hE (M.β₁ + β) c
  rw [hc] at h
  have hin : ContinuousAt (fun β' : Fin p → ℝ => (M.β₁ + β', θ)) β := by fun_prop
  exact (h.comp (f := fun β' : Fin p → ℝ => (M.β₁ + β', θ)) hin).sub continuousAt_const

/-- The calibrated effect solves the calibration equation, and it is the only solution: the
arm mean of `M.withArm k w` at baseline `μ_{j_B}` is `θ` exactly when `w.2 = Γ(w.1)`. -/
theorem armMean_withArm_eq_iff [DecidableEq K] (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hE : LocalEnvelope F ginv) (M : MultilevelModel J K p) (k : K)
    (jB : J) {θ : ℝ} (hθ : θ ∈ Set.range ginv) (w : (Fin p → ℝ) × ℝ) :
    (M.withArm k w).armMean ginv ((M.withArm k w).μ jB) F k = θ ↔
      w.2 = calibratedArmEffect F ginv M jB θ w.1 := by
  have hex := exists_shiftMean_eq_of_mem_range hmono hcont hE (M.β₁ + w.1) hθ
  have hcal := shiftMean_calibratedShift hex
  rw [withArm_μ, armMean_withArm, coefMean_eq_shiftMean, calibratedArmEffect]
  constructor
  · intro h
    have := (shiftMean_strictMono hmono fun c => hE.integrable hcont c (M.β₁ + w.1)).injective
      (h.trans hcal.symm)
    linarith
  · intro h
    rw [show M.μ jB + w.2 = calibratedShift F ginv (M.β₁ + w.1) θ by linarith]
    exact hcal

variable {π : Kernel ℝ ℝ} {FA : Measure (Fin p → ℝ)} {jA jB : J} {a b : K} [DecidableEq K]

/-- **The parameter pairs compatible with the unanchored data form the graph of `Γ`.** For a
continuous, strictly increasing `g⁻¹` with a local envelope under `F_B` and `a ≠ b`, the model
`M.withArm b w` has the unanchored data of `M` exactly when `γ_b = Γ(β₂,b)`, where `Γ` is the
calibrated effect at the reported mean `θ_B` of `b` in `M`. -/
theorem unanchoredData_withArm_eq_iff (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hE : LocalEnvelope F ginv) (hab : a ≠ b) (M : MultilevelModel J K p)
    (w : (Fin p → ℝ) × ℝ) :
    unanchoredData π hmono.monotone.measurable FA F jA jB a b (M.withArm b w) =
        unanchoredData π hmono.monotone.measurable FA F jA jB a b M ↔
      w.2 = calibratedArmEffect F ginv M jB (M.armMean ginv (M.μ jB) F b) w.1 := by
  rw [← armMean_withArm_eq_iff hmono hcont hE M b jB
    (armMean_mem_range hmono hcont hE M _ b) w]
  constructor
  · intro h
    simp only [unanchoredData, Prod.mk.injEq] at h
    exact h.2
  · intro h
    refine unanchoredData_congr ?_ h
    rw [withArm_μ, surface_withArm_of_ne ginv M hab]

/-- **The models differing from `M` only in the parameters of `b` and having its data** are
exactly the models `M.withArm b (β, Γ β)`, `β ∈ ℝ^p`. -/
theorem withArm_unanchoredData_eq_set (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hE : LocalEnvelope F ginv) (hab : a ≠ b) (M : MultilevelModel J K p) :
    {N | N ∈ Set.range (M.withArm b) ∧
        unanchoredData π hmono.monotone.measurable FA F jA jB a b N =
          unanchoredData π hmono.monotone.measurable FA F jA jB a b M} =
      Set.range fun β => M.withArm b
        (β, calibratedArmEffect F ginv M jB (M.armMean ginv (M.μ jB) F b) β) := by
  ext N
  constructor
  · rintro ⟨⟨w, rfl⟩, h⟩
    exact ⟨w.1, congrArg (M.withArm b)
      (Prod.ext rfl ((unanchoredData_withArm_eq_iff hmono hcont hE hab M w).1 h).symm)⟩
  · rintro ⟨β, rfl⟩
    exact ⟨⟨_, rfl⟩, (unanchoredData_withArm_eq_iff hmono hcont hE hab M _).2 rfl⟩

/-- The interaction of `b` in `M.withArm b w` is `w.1`. -/
theorem withArm_β₂_self (M : MultilevelModel J K p) (k : K) (w : (Fin p → ℝ) × ℝ) :
    (M.withArm k w).β₂ k = w.1 := by
  simp [withArm]

/-- **The parameters compatible with the unanchored data are homeomorphic to `ℝ^p`.** Under the
hypotheses of `unanchoredData_withArm_eq_iff`, `β ↦ (β, Γ β)` is a homeomorphism of `ℝ^p` onto
the set of pairs `w = (β₂,b, γ_b)` for which `M.withArm b w` has the unanchored data of `M`; its
inverse is the first coordinate. -/
theorem nonempty_homeomorph_unanchoredSolutions (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hE : LocalEnvelope F ginv) (hab : a ≠ b)
    (M : MultilevelModel J K p) :
    ∃ e : (Fin p → ℝ) ≃ₜ {w : (Fin p → ℝ) × ℝ //
        unanchoredData π hmono.monotone.measurable FA F jA jB a b (M.withArm b w) =
          unanchoredData π hmono.monotone.measurable FA F jA jB a b M},
      ∀ β, (e β : (Fin p → ℝ) × ℝ) =
        (β, calibratedArmEffect F ginv M jB (M.armMean ginv (M.μ jB) F b) β) := by
  have hΓ := continuous_calibratedArmEffect hmono hcont hE M jB
    (armMean_mem_range hmono hcont hE M (M.μ jB) b)
  have hset : ∀ w : (Fin p → ℝ) × ℝ,
      unanchoredData π hmono.monotone.measurable FA F jA jB a b (M.withArm b w) =
          unanchoredData π hmono.monotone.measurable FA F jA jB a b M ↔
        w.2 = calibratedArmEffect F ginv M jB (M.armMean ginv (M.μ jB) F b) w.1 :=
    unanchoredData_withArm_eq_iff hmono hcont hE hab M
  exact ⟨(graphHomeomorph hΓ).trans ((Homeomorph.refl _).subtype fun w => (hset w).symm),
    fun β => rfl⟩

end MultilevelModel

/-! ### An instance -/

/-- **Instance of the graph theorems.** One covariate, the identity link, `F_B = binaryLaw (1/2)`,
comparator `b = false` in study `j_B = false`, and the model `⟨0, 0, 0, 0⟩`. The reported mean
is `0`, the calibrated effect is `Γ(β) = -β/2`, the model `M.withArm b w` has the data of the
model `⟨0, 0, 0, 0⟩` exactly when `γ_b = -β₂,b/2`, and this set of pairs is homeomorphic to `ℝ`
by `β ↦ (β, -β/2)`. -/
theorem unanchoredSolutions_instance :
    let M : MultilevelModel Bool Bool 1 := ⟨0, 0, 0, 0⟩
    M.armMean id (M.μ false) (binaryLaw (1 / 2)) false = 0 ∧
      (∀ β, M.calibratedArmEffect (binaryLaw (1 / 2)) id false 0 β = -(β 0) / 2) ∧
      (∀ w : (Fin 1 → ℝ) × ℝ,
        MultilevelModel.unanchoredData (Kernel.deterministic id measurable_id)
            strictMono_id.monotone.measurable (binaryLaw (1 / 2)) (binaryLaw (1 / 2)) true false
            true false (M.withArm false w) =
          MultilevelModel.unanchoredData (Kernel.deterministic id measurable_id)
            strictMono_id.monotone.measurable (binaryLaw (1 / 2)) (binaryLaw (1 / 2)) true false
            true false M ↔ w.2 = -(w.1 0) / 2) ∧
      ∃ e : (Fin 1 → ℝ) ≃ₜ {w : (Fin 1 → ℝ) × ℝ //
          MultilevelModel.unanchoredData (Kernel.deterministic id measurable_id)
              strictMono_id.monotone.measurable (binaryLaw (1 / 2)) (binaryLaw (1 / 2)) true
              false true false (M.withArm false w) =
            MultilevelModel.unanchoredData (Kernel.deterministic id measurable_id)
              strictMono_id.monotone.measurable (binaryLaw (1 / 2)) (binaryLaw (1 / 2)) true
              false true false M},
        ∀ β, (e β : (Fin 1 → ℝ) × ℝ) = (β, -(β 0) / 2) := by
  intro M
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have hE : LocalEnvelope (binaryLaw (1 / 2)) id :=
    localEnvelope_id fun _ => integrable_binaryLaw _ _
  have hmean : M.armMean id (M.μ false) (binaryLaw (1 / 2)) false = 0 := by
    simp [M, MultilevelModel.armMean, MultilevelModel.surface, MultilevelModel.eta,
      NetworkMetaAnalysis.metaRegressionPredictor]
  have hΓ : ∀ β, M.calibratedArmEffect (binaryLaw (1 / 2)) id false 0 β = -(β 0) / 2 := by
    intro β
    have hsm : shiftMean (binaryLaw (1 / 2)) id (fun x => x ⬝ᵥ (M.β₁ + β)) (-(β 0) / 2) = 0 := by
      rw [shiftMean, integral_binaryLaw ⟨by norm_num, by norm_num⟩]
      simp [M, dotProduct]
      ring
    have := calibratedShift_eq (F := binaryLaw (1 / 2)) strictMono_id (β := M.β₁ + β)
      (fun c => hE.integrable continuous_id c _) (c := -(β 0) / 2)
    rw [hsm] at this
    rw [MultilevelModel.calibratedArmEffect]
    simpa [M] using this
  have hiff := fun w => MultilevelModel.unanchoredData_withArm_eq_iff
    (π := Kernel.deterministic id measurable_id) (FA := binaryLaw (1 / 2)) (jA := true)
    (jB := false) (a := true) (b := false) strictMono_id continuous_id hE (by decide) M w
  obtain ⟨e, he⟩ := MultilevelModel.nonempty_homeomorph_unanchoredSolutions
    (π := Kernel.deterministic id measurable_id) (FA := binaryLaw (1 / 2)) (jA := true)
    (jB := false) (a := true) (b := false) strictMono_id continuous_id hE (by decide) M
  rw [hmean] at hiff he
  refine ⟨hmean, hΓ, fun w => by rw [hiff w, hΓ], e, fun β => by rw [he β, hΓ]⟩

end NetworkMetaRegression

end CausalInference
