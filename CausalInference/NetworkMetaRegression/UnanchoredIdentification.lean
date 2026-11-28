/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredModel
public import CausalInference.NetworkMetaRegression.SharedModifiersSensitivity

/-!
# Identification in the unanchored network

In the unanchored network (`MultilevelModel.unanchoredData`) the individual data of study `j_A`
determine the surface of `a`, hence its cell intercept `μ_{j_A} + γ_a` and cell slope
`β₁ + β₂,a` (for a covariate law of full affine rank); the aggregate mean of `b` in study `j_B`
is one number. Under **shared prognostic effects** (shared effect modifiers for `{a, b}`) the
slope of `b` is that of `a`, and the aggregate mean determines the cell intercept of `b`, as the
unique root of the calibration equation `∫ g⁻¹(c + xᵀβ) F_B(dx) = θ_B` (`calibratedShift`).
Without shared prognostic effects the slope of `b` is not identified.

## Main definitions

* `calibratedShift F ginv β θ`: the root `c` of `∫ g⁻¹(c + xᵀβ) dF = θ` when there is one.
* `MultilevelModel.unanchoredClass`: the models with shared effect modifiers for `{a, b}` and
  integrable aggregate integrands of `b`.

## Main results

* `unanchored_identified`: the cell parameters of `a` and the cell intercept of `b` are point
  identified on `unanchoredClass`; `unanchored_estimand_identified`: so is the marginal estimand
  of `b` against `a` in every target, with the explicit plug in formula
  `unanchored_estimand_eq_calibrated`.
* `exists_withArm_unanchoredData_eq`: without shared prognostic effects every slope of `b` is
  compatible with the data, so the cell slope of `b` is not point identified
  (`not_pointIdentified_cellSlope_unanchored`).
* `not_pointIdentified_target_armMean_unanchored`: without shared prognostic effects the target
  mean of `b` is not identified, by two concrete models.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory EffectMeasure IndirectComparison NetworkMetaAnalysis

variable {p : ℕ}

/-! ### The calibrated shift -/

/-- The **calibrated shift**: the solution `c` of `∫ g⁻¹(c + xᵀβ) F(dx) = θ` when it exists
(and `0` otherwise). -/
noncomputable def calibratedShift (F : Measure (Fin p → ℝ)) (ginv : ℝ → ℝ) (β : Fin p → ℝ)
    (θ : ℝ) : ℝ :=
  open Classical in
  if h : ∃ c, shiftMean F ginv (fun x => x ⬝ᵥ β) c = θ then h.choose else 0

/-- The calibrated shift solves the calibration equation whenever it is solvable. -/
theorem shiftMean_calibratedShift {F : Measure (Fin p → ℝ)} {ginv : ℝ → ℝ} {β : Fin p → ℝ}
    {θ : ℝ} (h : ∃ c, shiftMean F ginv (fun x => x ⬝ᵥ β) c = θ) :
    shiftMean F ginv (fun x => x ⬝ᵥ β) (calibratedShift F ginv β θ) = θ := by
  unfold calibratedShift
  split_ifs
  exact h.choose_spec

/-- For a strictly increasing `g⁻¹` and integrable integrands under a probability law, the
calibrated shift at an attained mean is the shift that attains it. -/
theorem calibratedShift_eq {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F] {ginv : ℝ → ℝ}
    (hmono : StrictMono ginv) {β : Fin p → ℝ}
    (hint : ∀ c, Integrable (fun x => ginv (c + x ⬝ᵥ β)) F) {c : ℝ} :
    calibratedShift F ginv β (shiftMean F ginv (fun x => x ⬝ᵥ β) c) = c :=
  (shiftMean_strictMono hmono hint).injective (shiftMean_calibratedShift ⟨c, rfl⟩)

namespace MultilevelModel

variable {J K : Type*}

/-! ### Identification under shared prognostic effects -/

/-- The **model class of the unanchored identification theorem**: shared effect modifiers for
`{a, b}` and, for every intercept `s`, an integrable aggregate integrand
`g⁻¹(s + xᵀ(β₁ + β₂,b))` under the covariate law `F_B`. -/
def unanchoredClass (ginv : ℝ → ℝ) (FB : Measure (Fin p → ℝ)) (a b : K) :
    Set (MultilevelModel J K p) :=
  {M | M.SharedEffectModifiers {a, b} ∧ ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ M.cellSlope b)) FB}

variable {π : Kernel ℝ ℝ} [IsMarkovKernel π] {ginv : ℝ → ℝ} {FA FB : Measure (Fin p → ℝ)}
  [IsFiniteMeasure FA] [IsProbabilityMeasure FB] {jA jB : J} {a b : K}

/-- **Identification in the unanchored network.** Let the outcome kernel `π` be indexed by its
mean (`∫ y ∂π θ = θ`), `g⁻¹` strictly increasing, the individual data covariate law `F_A` finite
of full affine rank and `F_B` a probability law. On `unanchoredClass`, the unanchored data
determine the cell intercept `μ_{j_A} + γ_a` and cell slope `β₁ + β₂,a` of `a` and the cell
intercept `μ_{j_B} + γ_b` of `b`; the cell slope of `b` equals that of `a`. -/
theorem unanchored_identified (hπ : ∀ θ, ∫ y, y ∂π θ = θ) (hmono : StrictMono ginv)
    (hFA : AffineRank FA) :
    PointIdentified (unanchoredClass ginv FB a b)
      (unanchoredData π hmono.monotone.measurable FA FB jA jB a b)
      (fun M : MultilevelModel J K p =>
        (M.cellIntercept jA a, M.cellSlope a, M.cellIntercept jB b)) := by
  intro M hM M' hM' h
  simp only [unanchoredData, Prod.mk.injEq] at h
  have hae := ae_surface_eq_of_compProd_eq hπ (fun x => Kernel.comap_apply _ _ x)
    (fun x => Kernel.comap_apply _ _ x) h.1
  obtain ⟨h1, h2⟩ := cell_eq_of_ae_surface_eq hmono hFA hae
  have hsb : M.cellSlope b = M'.cellSlope b := by
    rw [← (sharedEffectModifiers_pair_iff_cellSlope M a b).1 hM.1,
      ← (sharedEffectModifiers_pair_iff_cellSlope M' a b).1 hM'.1]
    exact h2
  have h3 := intercept_eq_of_armMean_eq hmono hsb hM.2 h.2
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- **The target estimand is identified.** Under the hypotheses of `unanchored_identified`, the
marginal estimand `g(∫ m_B dF*) - g(∫ m_A dF*)` of the surfaces of `b` (baseline `μ_{j_B}`) and
`a` (baseline `μ_{j_A}`) is point identified on `unanchoredClass`, for every target covariate
law `F*` and every scale `g`. -/
theorem unanchored_estimand_identified (hπ : ∀ θ, ∫ y, y ∂π θ = θ) (hmono : StrictMono ginv)
    (hFA : AffineRank FA) (Fs : Measure (Fin p → ℝ)) (g : ℝ → ℝ) :
    PointIdentified (unanchoredClass ginv FB a b)
      (unanchoredData π hmono.monotone.measurable FA FB jA jB a b)
      (fun M : MultilevelModel J K p =>
        linkMarginal g Fs (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b)) := by
  intro M hM M' hM' h
  have := unanchored_identified hπ hmono hFA M hM M' hM' h
  simp only [Prod.mk.injEq] at this
  obtain ⟨h1, h2, h3⟩ := this
  have hsb : M.cellSlope b = M'.cellSlope b := by
    rw [← (sharedEffectModifiers_pair_iff_cellSlope M a b).1 hM.1,
      ← (sharedEffectModifiers_pair_iff_cellSlope M' a b).1 hM'.1, h2]
  simp only [surface_eq_cell, h1, h2, h3, hsb]

/-- **The plug in formula.** On `unanchoredClass`, the cell intercept of `b` is the calibrated
shift of the slope of `a` at the aggregate mean `θ_B` of `b`, and the target estimand is the
standardized comparison
`g(∫ g⁻¹(c(β, θ_B) + xᵀβ) dF*) - g(∫ g⁻¹(α + xᵀβ) dF*)` of the identified cell parameters
`α = μ_{j_A} + γ_a`, `β = β₁ + β₂,a` and `c(β, θ_B)` the calibrated shift. -/
theorem unanchored_estimand_eq_calibrated (hmono : StrictMono ginv) {M : MultilevelModel J K p}
    (hM : M ∈ unanchoredClass ginv FB a b) (Fs : Measure (Fin p → ℝ)) (g : ℝ → ℝ) :
    M.cellIntercept jB b =
        calibratedShift FB ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) FB b) ∧
      linkMarginal g Fs (M.surface ginv (M.μ jA) a) (M.surface ginv (M.μ jB) b) =
        g (∫ x, ginv (calibratedShift FB ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) FB b) +
            x ⬝ᵥ M.cellSlope a) ∂Fs) -
          g (∫ x, ginv (M.cellIntercept jA a + x ⬝ᵥ M.cellSlope a) ∂Fs) := by
  have hs := (sharedEffectModifiers_pair_iff_cellSlope M a b).1 hM.1
  have hc : calibratedShift FB ginv (M.cellSlope a) (M.armMean ginv (M.μ jB) FB b) =
      M.cellIntercept jB b := by
    rw [armMean_eq_cell, ← hs]
    exact calibratedShift_eq hmono (hs ▸ hM.2)
  refine ⟨hc.symm, ?_⟩
  rw [hc, linkMarginal, surface_eq_cell, surface_eq_cell, hs]

omit [IsMarkovKernel π] in
/-- **Instance of the identification theorems.** One covariate, the identity link, the outcome
kernel `θ ↦ δ_θ`, `F_A = binaryLaw (1/2)` and `F_B = binaryLaw (1/4)`. The theorem applies, and
for the model with cell intercepts `1` (of `a`) and `2` (of `b`) and common slope `1`, the
aggregate mean of `b` is `9/4`, its calibrated shift is `2`, and the estimand under
`binaryLaw (1/2)` on the identity scale is `1`. -/
theorem unanchored_identified_instance :
    let M : MultilevelModel Bool Bool 1 := ⟨fun j => if j then 1 else 2, fun _ => 1, 0, 0⟩
    PointIdentified (unanchoredClass id (binaryLaw (1 / 4)) true false)
      (unanchoredData (Kernel.deterministic id measurable_id)
        (strictMono_id (α := ℝ)).monotone.measurable (binaryLaw (1 / 2)) (binaryLaw (1 / 4))
        true false true false)
      (fun M : MultilevelModel Bool Bool 1 => linkMarginal id (binaryLaw (1 / 2))
        (M.surface id (M.μ true) true) (M.surface id (M.μ false) false)) ∧
      M ∈ unanchoredClass id (binaryLaw (1 / 4)) true false ∧
      M.armMean id (M.μ false) (binaryLaw (1 / 4)) false = 9 / 4 ∧
      calibratedShift (binaryLaw (1 / 4)) id (M.cellSlope true)
        (M.armMean id (M.μ false) (binaryLaw (1 / 4)) false) = 2 ∧
      linkMarginal id (binaryLaw (1 / 2)) (M.surface id (M.μ true) true)
        (M.surface id (M.μ false) false) = 1 := by
  intro M
  have : IsProbabilityMeasure (binaryLaw (1 / 4)) :=
    isProbabilityMeasure_binaryLaw ⟨by norm_num, by norm_num⟩
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have hπ : ∀ θ, ∫ y, y ∂(Kernel.deterministic (id : ℝ → ℝ) measurable_id) θ = θ := fun θ => by
    rw [Kernel.deterministic_apply, integral_dirac]; rfl
  have hM : M ∈ unanchoredClass id (binaryLaw (1 / 4)) true false :=
    ⟨by rw [sharedEffectModifiers_iff]; intro _ _ _ _; rfl, fun s => integrable_binaryLaw _ _⟩
  have hθ : M.armMean id (M.μ false) (binaryLaw (1 / 4)) false = 9 / 4 := by
    rw [armMean, integral_binaryLaw ⟨by norm_num, by norm_num⟩]
    simp [M, surface, eta, metaRegressionPredictor, dotProduct]
    norm_num
  have hc := (unanchored_estimand_eq_calibrated (jA := true) (jB := false) strictMono_id hM
    (binaryLaw (1 / 2)) id).1
  refine ⟨unanchored_estimand_identified hπ strictMono_id affineRank_binaryLaw_half _ _, hM, hθ,
    ?_, ?_⟩
  · rw [← hc]; simp [M, cellIntercept]
  · rw [linkMarginal, integral_binaryLaw ⟨by norm_num, by norm_num⟩,
      integral_binaryLaw ⟨by norm_num, by norm_num⟩]
    simp [M, surface, eta, metaRegressionPredictor, dotProduct]
    norm_num

/-! ### Without shared prognostic effects -/

section NotShared

variable [DecidableEq K]

omit [IsMarkovKernel π] [IsFiniteMeasure FA] in
/-- **Every slope of `b` is compatible with the data.** Let `g⁻¹` be continuous and strictly
increasing, `F_B` a probability law under which every `g⁻¹(c + xᵀ(β₁ + β))` is integrable, and
`a ≠ b`. For every model `M` and every `β` there is a `γ` such that `M.withArm b (β, γ)` (the
model with `(β₂,b, γ_b)` replaced by `(β, γ)`) has the same unanchored data as `M`. -/
theorem exists_withArm_unanchoredData_eq (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hab : a ≠ b) (M : MultilevelModel J K p)
    (hint : ∀ (β : Fin p → ℝ) (c : ℝ), Integrable (fun x => ginv (c + x ⬝ᵥ (M.β₁ + β))) FB)
    (β : Fin p → ℝ) :
    ∃ γ, unanchoredData π hmono.monotone.measurable FA FB jA jB a b (M.withArm b (β, γ)) =
      unanchoredData π hmono.monotone.measurable FA FB jA jB a b M := by
  have hdot : Measurable fun x : Fin p → ℝ => x ⬝ᵥ (M.β₁ + M.β₂ b) :=
    (by unfold dotProduct; fun_prop : Continuous fun x : Fin p → ℝ =>
      x ⬝ᵥ (M.β₁ + M.β₂ b)).measurable
  have hθ : M.armMean ginv (M.μ jB) FB b ∈ Set.range ginv := by
    rw [← range_shiftMean hmono hcont hdot (hint (M.β₂ b))]
    exact ⟨_, (armMean_eq_shiftMean ginv M (M.μ jB) FB b).symm⟩
  obtain ⟨Γ, hΓ⟩ := withArm_solution_graph hmono hcont M b (M.μ jB) hint hθ
  refine ⟨Γ β, unanchoredData_congr ?_ ?_⟩
  · rw [withArm_μ, surface_withArm_of_ne ginv M hab]
  · rw [withArm_μ]
    exact (hΓ (β, Γ β)).2 rfl

omit [IsMarkovKernel π] [IsFiniteMeasure FA] [DecidableEq K] in
/-- **The slope of `b` is not identified without shared prognostic effects.** Under the
hypotheses of `exists_withArm_unanchoredData_eq` with at least one covariate, on the class of
models whose aggregate integrands of `b` are integrable for every slope and intercept, the cell
slope of `b` is not point identified, provided the class is not empty. -/
theorem not_pointIdentified_cellSlope_unanchored (hmono : StrictMono ginv)
    (hcont : Continuous ginv) (hab : a ≠ b) (hp : 0 < p) {M : MultilevelModel J K p}
    (hM : ∀ (β : Fin p → ℝ) (c : ℝ), Integrable (fun x => ginv (c + x ⬝ᵥ (M.β₁ + β))) FB) :
    ¬PointIdentified
      {N : MultilevelModel J K p | ∀ (β : Fin p → ℝ) (c : ℝ),
        Integrable (fun x => ginv (c + x ⬝ᵥ (N.β₁ + β))) FB}
      (unanchoredData π hmono.monotone.measurable FA FB jA jB a b) (fun N => N.cellSlope b) := by
  classical
  intro h
  obtain ⟨γ, hγ⟩ := exists_withArm_unanchoredData_eq (π := π) (FA := FA) (jA := jA) (jB := jB)
    hmono hcont hab M hM (M.β₂ b + Pi.single ⟨0, hp⟩ 1)
  have := h _ (by simpa [withArm_β₁] using hM) _ hM hγ
  have h2 := congrFun this ⟨0, hp⟩
  simp [cellSlope, withArm] at h2

omit [IsMarkovKernel π] in
/-- **The target mean of `b` is not identified without shared prognostic effects.** Let
`g⁻¹` be strictly increasing, `a ≠ b`, one covariate and `F_B` the point mass at `0`. The model
`⟨0, 0, 0, 0⟩` and the model with `β₂,b = 1` (all else `0`) have the same unanchored data, but
under the target point mass at `1` the target means of `b` are `g⁻¹(0)` and `g⁻¹(1)`; and the
target estimand of `b` against `a` differs on every scale `g` inverting `g⁻¹`. -/
theorem not_pointIdentified_target_armMean_unanchored (hmono : StrictMono ginv) (hab : a ≠ b)
    (FA₁ : Measure (Fin 1 → ℝ)) :
    let M₁ : MultilevelModel J K 1 := ⟨0, 0, 0, Function.update 0 b 1⟩
    unanchoredData π hmono.monotone.measurable FA₁ (Measure.dirac 0) jA jB a b M₁ =
        unanchoredData π hmono.monotone.measurable FA₁ (Measure.dirac 0) jA jB a b ⟨0, 0, 0, 0⟩ ∧
      ¬PointIdentified (Set.univ : Set (MultilevelModel J K 1))
        (unanchoredData π hmono.monotone.measurable FA₁ (Measure.dirac 0) jA jB a b)
        (fun N => N.armMean ginv (N.μ jB) (Measure.dirac fun _ => 1) b) ∧
      ∀ g : ℝ → ℝ, (∀ y, g (ginv y) = y) →
        ¬PointIdentified (Set.univ : Set (MultilevelModel J K 1))
          (unanchoredData π hmono.monotone.measurable FA₁ (Measure.dirac 0) jA jB a b)
          (fun N => linkMarginal g (Measure.dirac fun _ => 1) (N.surface ginv (N.μ jA) a)
            (N.surface ginv (N.μ jB) b)) := by
  intro M₁
  have hdata : unanchoredData π hmono.monotone.measurable FA₁ (Measure.dirac 0) jA jB a b M₁ =
      unanchoredData π hmono.monotone.measurable FA₁ (Measure.dirac 0) jA jB a b ⟨0, 0, 0, 0⟩ := by
    refine unanchoredData_congr ?_ ?_
    · funext x
      simp [M₁, surface, eta, metaRegressionPredictor, Function.update_of_ne hab]
    · simp [M₁, armMean, surface, eta, metaRegressionPredictor]
  have hmean : M₁.armMean ginv (M₁.μ jB) (Measure.dirac fun _ => 1) b = ginv 1 ∧
      (⟨0, 0, 0, 0⟩ : MultilevelModel J K 1).armMean ginv 0 (Measure.dirac fun _ => 1) b =
        ginv 0 := by
    constructor <;> simp [M₁, armMean, surface, eta, metaRegressionPredictor, dotProduct]
  refine ⟨hdata, fun h => ?_, fun g hg h => ?_⟩
  · have := h _ trivial _ trivial hdata
    simp only at this
    rw [hmean.1] at this
    have h0 := hmean.2
    simp only [Pi.zero_apply] at this h0
    rw [h0] at this
    exact absurd (hmono.injective this) one_ne_zero
  · have := h _ trivial _ trivial hdata
    simp only [linkMarginal] at this
    have ha : ∫ x, M₁.surface ginv (M₁.μ jA) a x ∂(Measure.dirac fun _ => (1 : ℝ)) =
        ∫ x, (⟨0, 0, 0, 0⟩ : MultilevelModel J K 1).surface ginv 0 a x
          ∂(Measure.dirac fun _ => (1 : ℝ)) := by
      simp [M₁, surface, eta, metaRegressionPredictor, Function.update_of_ne hab]
    have hb1 : ∫ x, M₁.surface ginv (M₁.μ jB) b x ∂(Measure.dirac fun _ => (1 : ℝ)) = ginv 1 :=
      hmean.1
    have hb0 : ∫ x, (⟨0, 0, 0, 0⟩ : MultilevelModel J K 1).surface ginv 0 b x
        ∂(Measure.dirac fun _ => (1 : ℝ)) = ginv 0 := hmean.2
    simp only [Pi.zero_apply] at this
    rw [ha, hb1, hb0, hg, hg] at this
    norm_num at this

end NotShared

/-- **Instance of the non identification theorems**: two studies and two treatments indexed by
`Bool`, one covariate, the logit link `Real.sigmoid`, `F_A = binaryLaw (1/2)`, the outcome
kernel `θ ↦ δ_θ`, and `F_B = binaryLaw (1/2)` for the slope, `δ_0` for the target mean. -/
theorem not_pointIdentified_unanchored_instance :
    ¬PointIdentified
        {N : MultilevelModel Bool Bool 1 | ∀ (β : Fin 1 → ℝ) (c : ℝ),
          Integrable (fun x => Real.sigmoid (c + x ⬝ᵥ (N.β₁ + β))) (binaryLaw (1 / 2))}
        (unanchoredData (Kernel.deterministic id measurable_id)
          Real.sigmoid_strictMono.monotone.measurable (binaryLaw (1 / 2)) (binaryLaw (1 / 2))
          true false true false) (fun N => N.cellSlope false) ∧
      ¬PointIdentified (Set.univ : Set (MultilevelModel Bool Bool 1))
        (unanchoredData (Kernel.deterministic id measurable_id)
          Real.sigmoid_strictMono.monotone.measurable (binaryLaw (1 / 2)) (Measure.dirac 0)
          true false true false)
        (fun N => N.armMean Real.sigmoid (N.μ false) (Measure.dirac fun _ => 1) false) := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  exact ⟨not_pointIdentified_cellSlope_unanchored (M := ⟨0, 0, 0, 0⟩)
      Real.sigmoid_strictMono continuous_sigmoid (by decide) one_pos
      fun _ _ => integrable_binaryLaw _ _,
    (not_pointIdentified_target_armMean_unanchored Real.sigmoid_strictMono (by decide) _).2.1⟩

end MultilevelModel

end NetworkMetaRegression

end CausalInference
