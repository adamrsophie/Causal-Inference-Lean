/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.PrincipalStrata
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The local average treatment effect theorem

Identification of the complier average causal effect by the Wald ratio, for a binary instrument
and a binary treatment: Imbens and Angrist (1994, *Identification and estimation of local average
treatment effects*) and Angrist, Imbens and Rubin (1996, *Identification of causal effects using
instrumental variables*).

## Main definitions

* `CausalInference.IVModel.complierEffect`: the complier average causal effect
  `E[Y z true - Y z false | compliers]`.

## Main results

* `IVModel.complierEffect_eq_of_exclusion`: under exclusion alone, the complier effect does not
  depend on the instrument value indexing the outcomes.
* `IVModel.firstStage_eq`: under instrument independence, the first stage equals
  `P(compliers) - P(defiers)`; `IVModel.firstStage_eq_measure_compliers`: under monotonicity
  as well, it equals `P(compliers)`.
* `IVModel.measureReal_alwaysTakers_eq`, `IVModel.measureReal_neverTakers_eq`: under
  independence and monotonicity, `P(always-takers) = E[Dobs | Z = false]` and
  `P(never-takers) = 1 - E[Dobs | Z = true]`.
* `IVModel.relevance_iff`: under independence and monotonicity, relevance is equivalent to
  `0 < P(compliers)`.
* `IVModel.reducedForm_eq`: under exclusion, independence and integrable responses `Y z (D z)`,
  the reduced form equals `E[(Y 1 - Y 0) 1_compliers] - E[(Y 1 - Y 0) 1_defiers]`.
* `IVModel.wald_eq_complierEffect`: the LATE theorem. Under exclusion, independence,
  monotonicity, relevance (which includes positive mass of both instrument arms) and integrable
  responses `Y z (D z)`, the Wald ratio equals the complier average causal effect.
  `IVModel.LATEAssumptions.wald_eq` is the same statement with the hypotheses bundled in
  `IVModel.LATEAssumptions`; `IVModel.wald_eq_complierEffect_of_integrable` assumes instead that
  every potential outcome is integrable.
* `IVModel.complierMean_true_eq`, `IVModel.complierMean_false_eq`: the complier means of each
  potential outcome, `E[Y 1 | C] = (E[Yobs Dobs | Z = 1] - E[Yobs Dobs | Z = 0]) / firstStage`
  and `E[Y 0 | C] = (E[Yobs (1 - Dobs) | Z = 0] - E[Yobs (1 - Dobs) | Z = 1]) / firstStage`.
* `IVModel.wald_eq_effectTreated`: one-sided noncompliance. If `D false = false` almost surely,
  the Wald ratio is the average effect on the treated `E[Y 1 - Y 0 | Dobs = true]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace IVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- The complier average causal effect `E[Y z true - Y z false | compliers]` at instrument
value `z`: the mean unit-level effect under the conditional measure `μ[|compliers]`. -/
noncomputable def complierEffect (μ : Measure Ω) (z : Bool) : ℝ :=
  ∫ ω, M.effect z ω ∂μ[|M.compliers]

/-- A conditional mean given `s` is `μ(s)⁻¹ ∫_s f` (both sides vanish when `μ(s) = 0`). -/
theorem integral_cond_eq_inv_mul (s : Set Ω) (f : Ω → ℝ) :
    ∫ ω, f ω ∂μ[|s] = (μ.real s)⁻¹ * ∫ ω in s, f ω ∂μ := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, ← measureReal_def,
    smul_eq_mul]

/-- First-stage decomposition: under instrument independence and `0 < P(Z = z)` for both
values `z`, `E[Dobs | Z = true] - E[Dobs | Z = false] = P(compliers) - P(defiers)`. -/
theorem firstStage_eq [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) :
    M.firstStage μ = μ.real M.compliers - μ.real M.defiers := by
  rw [firstStage, M.condMean_DobsReal hI h₁, M.condMean_DobsReal hI h₀,
    ← integral_sub (M.integrable_DReal true) (M.integrable_DReal false)]
  simp_rw [M.DReal_sub_DReal]
  have hC : Integrable (M.compliers.indicator 1) μ :=
    (integrable_const (1 : ℝ)).indicator M.measurableSet_compliers
  have hD : Integrable (M.defiers.indicator 1) μ :=
    (integrable_const (1 : ℝ)).indicator M.measurableSet_defiers
  rw [integral_sub hC hD,
    integral_indicator_one M.measurableSet_compliers,
    integral_indicator_one M.measurableSet_defiers]

/-- First-stage decomposition under monotonicity: the first stage equals `P(compliers)`. -/
theorem firstStage_eq_measure_compliers [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₁ : μ (M.instrumentEq true) ≠ 0)
    (h₀ : μ (M.instrumentEq false) ≠ 0) :
    M.firstStage μ = μ.real M.compliers := by
  rw [M.firstStage_eq hI h₁ h₀, measureReal_def, measureReal_def,
    M.measure_defiers_eq_zero hM, ENNReal.toReal_zero, sub_zero]

/-- The always-taker share is identified: under instrument independence, monotonicity and
`P(Z = false) ≠ 0`, `P(always-takers) = E[Dobs | Z = false]`. -/
theorem measureReal_alwaysTakers_eq [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₀ : μ (M.instrumentEq false) ≠ 0) :
    μ.real M.alwaysTakers = M.condMean μ M.DobsReal false := by
  rw [M.condMean_DobsReal hI h₀, M.integral_DReal, measureReal_congr (M.ae_eq_alwaysTakers hM)]

/-- The never-taker share is identified: under instrument independence, monotonicity and
`P(Z = true) ≠ 0`, `P(never-takers) = 1 - E[Dobs | Z = true]`. -/
theorem measureReal_neverTakers_eq [IsProbabilityMeasure μ] (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₁ : μ (M.instrumentEq true) ≠ 0) :
    μ.real M.neverTakers = 1 - M.condMean μ M.DobsReal true := by
  rw [M.condMean_DobsReal hI h₁, M.integral_DReal, ← measureReal_congr (M.ae_eq_neverTakers hM),
    probReal_compl_eq_one_sub (M.measurableSet_D_eq_true true)]

/-- Under independence and monotonicity, relevance (both instrument arms of positive mass and a
nonzero first stage) holds if and only if the compliers have positive probability. -/
theorem relevance_iff [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₁ : μ (M.instrumentEq true) ≠ 0)
    (h₀ : μ (M.instrumentEq false) ≠ 0) :
    M.Relevance μ ↔ 0 < μ.real M.compliers := by
  rw [Relevance, M.firstStage_eq_measure_compliers hI hM h₁ h₀]
  exact ⟨fun h ↦ measureReal_nonneg.lt_of_ne' h.2.2, fun h ↦ ⟨h₁, h₀, h.ne'⟩⟩

/-- Under the exclusion restriction, `Y z d = Y z' d` almost surely for all `z`, `z'`, `d`. -/
theorem Exclusion.ae_eq {M : IVModel Ω} (hE : M.Exclusion μ) (z z' d : Bool) :
    M.Y z d =ᵐ[μ] M.Y z' d := by
  cases z <;> cases z'
  · rfl
  · exact (hE d).symm
  · exact hE d
  · rfl

/-- Under the exclusion restriction alone, the complier average causal effect does not depend
on the instrument value `z` indexing the potential outcomes. -/
theorem complierEffect_eq_of_exclusion (hE : M.Exclusion μ) (z z' : Bool) :
    M.complierEffect μ z = M.complierEffect μ z' := by
  refine integral_congr_ae (cond_absolutelyContinuous.ae_le ?_)
  filter_upwards [hE.ae_eq z z' true, hE.ae_eq z z' false] with ω h1 h2
  simp [effect, h1, h2]

/-- Under exclusion and integrable responses `Y z (D z)`, the unit-level effect restricted to
the compliers is integrable: on the compliers it equals `Y true (D true) - Y false (D false)`
almost surely. -/
theorem integrable_indicator_compliers_effect (hE : M.Exclusion μ)
    (hY : ∀ z, Integrable (M.YD z) μ) (z : Bool) :
    Integrable (M.compliers.indicator (M.effect z)) μ := by
  refine (((hY true).sub (hY false)).indicator M.measurableSet_compliers).congr ?_
  filter_upwards [hE.ae_eq true z true, hE.ae_eq false z false] with ω h1 h2
  by_cases h : ω ∈ M.compliers
  · have h' := mem_compliers.1 h
    simp [Set.indicator, h, YD, effect, h'.1, h'.2, h1, h2]
  · simp [Set.indicator, h]

/-- Under exclusion and integrable responses `Y z (D z)`, the unit-level effect restricted to
the defiers is integrable: on the defiers it equals `Y false (D false) - Y true (D true)`
almost surely. -/
theorem integrable_indicator_defiers_effect (hE : M.Exclusion μ)
    (hY : ∀ z, Integrable (M.YD z) μ) (z : Bool) :
    Integrable (M.defiers.indicator (M.effect z)) μ := by
  refine (((hY false).sub (hY true)).indicator M.measurableSet_defiers).congr ?_
  filter_upwards [hE.ae_eq true z false, hE.ae_eq false z true] with ω h1 h2
  by_cases h : ω ∈ M.defiers
  · have h' := mem_defiers.1 h
    simp [Set.indicator, h, YD, effect, h'.1, h'.2, h1, h2]
  · simp [Set.indicator, h]

/-- Reduced-form decomposition: under the exclusion restriction, instrument independence,
integrable responses `Y z (D z)` for both `z`, and `P(Z = z) ≠ 0` for both values `z`,
`E[Yobs | Z = true] - E[Yobs | Z = false] = E[(Y 1 - Y 0) 1_compliers] - E[(Y 1 - Y 0) 1_defiers]`,
where `Y d` is `Y z d` for any fixed instrument value `z`. -/
theorem reducedForm_eq [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hY : ∀ z, Integrable (M.YD z) μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) (z : Bool) :
    M.reducedForm μ =
      ∫ ω in M.compliers, M.effect z ω ∂μ - ∫ ω in M.defiers, M.effect z ω ∂μ := by
  rw [reducedForm, M.condMean_Yobs hI h₁ (hY true), M.condMean_Yobs hI h₀ (hY false),
    ← integral_sub (hY true) (hY false),
    ← integral_indicator M.measurableSet_compliers, ← integral_indicator M.measurableSet_defiers,
    ← integral_sub (M.integrable_indicator_compliers_effect hE hY z)
      (M.integrable_indicator_defiers_effect hE hY z)]
  refine integral_congr_ae ?_
  filter_upwards [hE.ae_eq true z true, hE.ae_eq true z false, hE.ae_eq false z true,
    hE.ae_eq false z false] with ω h₁ h₂ h₃ h₄
  have key := M.sub_eq_indicator_sub_indicator (M.Y z) ω
  have hT : M.YD true ω = M.Y z (M.D true ω) ω := by
    simp only [YD]; cases M.D true ω
    · exact h₂
    · exact h₁
  have hF : M.YD false ω = M.Y z (M.D false ω) ω := by
    simp only [YD]; cases M.D false ω
    · exact h₄
    · exact h₃
  rw [hT, hF, key]
  rfl

/-- The reduced-form decomposition assuming every potential outcome `Y z d` integrable. -/
theorem reducedForm_eq_of_integrable [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hY : ∀ z d, Integrable (M.Y z d) μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) (z : Bool) :
    M.reducedForm μ =
      ∫ ω in M.compliers, M.effect z ω ∂μ - ∫ ω in M.defiers, M.effect z ω ∂μ :=
  M.reducedForm_eq hE hI (fun z ↦ M.integrable_Y_D (hY z) z) h₁ h₀ z

/-- **The LATE theorem** (Imbens and Angrist, 1994). Assume the exclusion restriction,
instrument independence, monotonicity, relevance (`P(Z = true) ≠ 0`, `P(Z = false) ≠ 0` and a
nonzero first stage; under the other assumptions the last is `0 < P(compliers)`, see
`IVModel.relevance_iff`), and integrable responses `Y z (D z)` for both instrument values. Then
the Wald ratio
`(E[Yobs | Z = true] - E[Yobs | Z = false]) / (E[Dobs | Z = true] - E[Dobs | Z = false])`
equals the complier average causal effect `E[Y z true - Y z false | compliers]`, for either
instrument value `z`.

Without relevance the compliers would be null and the equation would hold only as `0 = 0`, by
Lean's conventions for `x / 0` and for conditioning on a null set. Relevance excludes that
degenerate case and makes both sides genuine: the Wald ratio is then a quotient by a nonzero first
stage of differences of conditional means given events of positive mass, and `μ[|compliers]` is a
probability measure. -/
theorem wald_eq_complierEffect [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ) (hR : M.Relevance μ)
    (hY : ∀ z, Integrable (M.YD z) μ) (z : Bool) :
    M.wald μ = M.complierEffect μ z := by
  have hFS := M.firstStage_eq_measure_compliers hI hM hR.1 hR.2.1
  have hC : μ.real M.compliers ≠ 0 := hFS ▸ hR.2.2
  rw [wald, div_eq_iff hR.2.2, M.reducedForm_eq hE hI hY hR.1 hR.2.1 z, hFS,
    setIntegral_measure_zero _ (M.measure_defiers_eq_zero hM), sub_zero, complierEffect,
    integral_cond_eq_inv_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]

/-- The LATE theorem assuming every potential outcome `Y z d` integrable (a stronger
integrability hypothesis than in `IVModel.wald_eq_complierEffect`). -/
theorem wald_eq_complierEffect_of_integrable [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ) (hR : M.Relevance μ)
    (hY : ∀ z d, Integrable (M.Y z d) μ) (z : Bool) :
    M.wald μ = M.complierEffect μ z :=
  M.wald_eq_complierEffect hE hI hM hR (fun z ↦ M.integrable_Y_D (hY z) z) z

/-- The hypotheses of the LATE theorem, bundled: exclusion, instrument independence,
monotonicity, relevance (including positive mass of both instrument arms), and integrable
responses `Y z (D z)`. -/
structure LATEAssumptions (μ : Measure Ω) : Prop where
  exclusion : M.Exclusion μ
  independence : M.InstrumentIndependence μ
  monotonicity : M.Monotonicity μ
  relevance : M.Relevance μ
  integrable : ∀ z, Integrable (M.YD z) μ

/-- The LATE assumptions follow from exclusion, independence, monotonicity, relevance and
integrability of every potential outcome `Y z d`. -/
theorem LATEAssumptions.of_integrable {M : IVModel Ω} (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ) (hR : M.Relevance μ)
    (hY : ∀ z d, Integrable (M.Y z d) μ) : M.LATEAssumptions μ :=
  ⟨hE, hI, hM, hR, fun z ↦ M.integrable_Y_D (hY z) z⟩

/-- The LATE theorem in bundled form: under `LATEAssumptions` the Wald ratio equals the complier
average causal effect. -/
theorem LATEAssumptions.wald_eq [IsProbabilityMeasure μ] {M : IVModel Ω}
    (h : M.LATEAssumptions μ) (z : Bool) : M.wald μ = M.complierEffect μ z :=
  M.wald_eq_complierEffect h.exclusion h.independence h.monotonicity h.relevance h.integrable z

/-! ### Complier means of each potential outcome -/

/-- `∫_{D true = 1} f = ∫_compliers f + ∫_always-takers f`. -/
theorem setIntegral_D_true_eq {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω in {ω | M.D true ω = true}, f ω ∂μ =
      ∫ ω in M.compliers, f ω ∂μ + ∫ ω in M.alwaysTakers, f ω ∂μ := by
  have hA : MeasurableSet M.alwaysTakers := M.measurableSet_stratum _
  rw [← integral_indicator (M.measurableSet_D_eq_true true),
    ← integral_indicator M.measurableSet_compliers, ← integral_indicator hA,
    ← integral_add (hf.indicator M.measurableSet_compliers) (hf.indicator hA)]
  congr 1
  funext ω
  simp only [Set.indicator, mem_compliers, mem_alwaysTakers, Set.mem_ofPred_eq]
  rcases Bool.eq_false_or_eq_true (M.D false ω) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (M.D true ω) with h1 | h1 <;> simp [h0, h1]

/-- `∫_{D false = 0} f = ∫_compliers f + ∫_never-takers f`. -/
theorem setIntegral_D_false_compl_eq {f : Ω → ℝ} (hf : Integrable f μ) :
    ∫ ω in {ω | M.D false ω = true}ᶜ, f ω ∂μ =
      ∫ ω in M.compliers, f ω ∂μ + ∫ ω in M.neverTakers, f ω ∂μ := by
  have hN : MeasurableSet M.neverTakers := M.measurableSet_stratum _
  rw [← integral_indicator (M.measurableSet_D_eq_true false).compl,
    ← integral_indicator M.measurableSet_compliers, ← integral_indicator hN,
    ← integral_add (hf.indicator M.measurableSet_compliers) (hf.indicator hN)]
  congr 1
  funext ω
  simp only [Set.indicator, mem_compliers, mem_neverTakers, Set.mem_compl_iff,
    Set.mem_ofPred_eq]
  rcases Bool.eq_false_or_eq_true (M.D false ω) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (M.D true ω) with h1 | h1 <;> simp [h0, h1]

/-- Under exclusion, instrument independence, `P(Z = z') ≠ 0` and integrable `Y z' (D z')`:
`E[Yobs Dobs | Z = z'] = ∫_{D z' = 1} Y z true`, for any instrument value `z` indexing the
outcome. -/
theorem condMean_Yobs_mul_DobsReal [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) {z' : Bool} (hz : μ (M.instrumentEq z') ≠ 0)
    (hY : Integrable (M.YD z') μ) (z : Bool) :
    M.condMean μ (fun ω ↦ M.Yobs ω * M.DobsReal ω) z' =
      ∫ ω in {ω | M.D z' ω = true}, M.Y z true ω ∂μ := by
  have hint : Integrable (fun ω ↦ M.Y z' (M.D z' ω) ω * boolToReal (M.D z' ω)) μ := by
    refine (hY.indicator (M.measurableSet_D_eq_true z')).congr (ae_of_all _ fun ω ↦ ?_)
    by_cases h : M.D z' ω = true <;> simp [Set.indicator, YD, h]
  rw [show (fun ω ↦ M.Yobs ω * M.DobsReal ω) =
      fun ω ↦ (fun d y ↦ y * boolToReal d) (M.Dobs ω) (M.Yobs ω) from rfl,
    M.condMean_obs hI hz (fun d y ↦ y * boolToReal d) (fun _ ↦ measurable_id.mul_const _) hint,
    ← integral_indicator (M.measurableSet_D_eq_true z')]
  refine integral_congr_ae ?_
  filter_upwards [hE.ae_eq z' z true] with ω hω
  by_cases h : M.D z' ω = true <;> simp [Set.indicator, h, hω]

/-- Under exclusion, instrument independence, `P(Z = z') ≠ 0` and integrable `Y z' (D z')`:
`E[Yobs (1 - Dobs) | Z = z'] = ∫_{D z' = 0} Y z false`. -/
theorem condMean_Yobs_mul_one_sub_DobsReal [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) {z' : Bool} (hz : μ (M.instrumentEq z') ≠ 0)
    (hY : Integrable (M.YD z') μ) (z : Bool) :
    M.condMean μ (fun ω ↦ M.Yobs ω * (1 - M.DobsReal ω)) z' =
      ∫ ω in {ω | M.D z' ω = true}ᶜ, M.Y z false ω ∂μ := by
  have hint : Integrable (fun ω ↦ M.Y z' (M.D z' ω) ω * (1 - boolToReal (M.D z' ω))) μ := by
    refine (hY.indicator (M.measurableSet_D_eq_true z').compl).congr (ae_of_all _ fun ω ↦ ?_)
    by_cases h : M.D z' ω = true <;> simp [Set.indicator, YD, h]
  rw [show (fun ω ↦ M.Yobs ω * (1 - M.DobsReal ω)) =
      fun ω ↦ (fun d y ↦ y * (1 - boolToReal d)) (M.Dobs ω) (M.Yobs ω) from rfl,
    M.condMean_obs hI hz (fun d y ↦ y * (1 - boolToReal d)) (fun _ ↦ measurable_id.mul_const _)
      hint,
    ← integral_indicator (M.measurableSet_D_eq_true z').compl]
  refine integral_congr_ae ?_
  filter_upwards [hE.ae_eq z' z false] with ω hω
  by_cases h : M.D z' ω = true <;> simp [Set.indicator, h, hω]

/-- Under exclusion, `Y z (D z' ω) ω` is integrable when `Y z' (D z')` is. -/
theorem integrable_Y_D_of_YD (hE : M.Exclusion μ) {z' : Bool} (hY : Integrable (M.YD z') μ)
    (z : Bool) : Integrable (fun ω ↦ M.Y z (M.D z' ω) ω) μ := by
  refine hY.congr ?_
  filter_upwards [hE.ae_eq z' z true, hE.ae_eq z' z false] with ω h1 h2
  simp only [YD]
  cases M.D z' ω
  · exact h2
  · exact h1

/-- **Complier mean of the treated potential outcome** (Imbens and Rubin, 1997, *Estimating
outcome distributions for compliers in instrumental variables models*). Under exclusion,
instrument independence, monotonicity, relevance and integrable responses `Y z (D z)`:
`E[Y z true | compliers] = (E[Yobs Dobs | Z = 1] - E[Yobs Dobs | Z = 0]) / firstStage`. -/
theorem complierMean_true_eq [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ) (hR : M.Relevance μ)
    (hY : ∀ z, Integrable (M.YD z) μ) (z : Bool) :
    ∫ ω, M.Y z true ω ∂μ[|M.compliers] =
      (M.condMean μ (fun ω ↦ M.Yobs ω * M.DobsReal ω) true -
        M.condMean μ (fun ω ↦ M.Yobs ω * M.DobsReal ω) false) / M.firstStage μ := by
  have hA : MeasurableSet M.alwaysTakers := M.measurableSet_stratum _
  have hsplit := M.setIntegral_D_true_eq (M.integrable_Y_D_of_YD hE (hY true) z)
  rw [setIntegral_congr_fun (M.measurableSet_D_eq_true true) (g := M.Y z true)
      fun ω hω ↦ by simp only [Set.mem_ofPred_eq] at hω; simp [hω],
    setIntegral_congr_fun M.measurableSet_compliers (g := M.Y z true)
      fun ω hω ↦ by simp [(mem_compliers.1 hω).2],
    setIntegral_congr_fun hA (g := M.Y z true)
      fun ω hω ↦ by simp [(mem_alwaysTakers.1 hω).2]] at hsplit
  rw [M.condMean_Yobs_mul_DobsReal hE hI hR.1 (hY true) z,
    M.condMean_Yobs_mul_DobsReal hE hI hR.2.1 (hY false) z, hsplit,
    setIntegral_congr_set (M.ae_eq_alwaysTakers hM), add_sub_cancel_right,
    M.firstStage_eq_measure_compliers hI hM hR.1 hR.2.1, integral_cond_eq_inv_mul,
    div_eq_inv_mul]

/-- **Complier mean of the untreated potential outcome.** Under the same assumptions,
`E[Y z false | compliers] = (E[Yobs (1 - Dobs) | Z = 0] - E[Yobs (1 - Dobs) | Z = 1]) /
firstStage`. -/
theorem complierMean_false_eq [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ) (hR : M.Relevance μ)
    (hY : ∀ z, Integrable (M.YD z) μ) (z : Bool) :
    ∫ ω, M.Y z false ω ∂μ[|M.compliers] =
      (M.condMean μ (fun ω ↦ M.Yobs ω * (1 - M.DobsReal ω)) false -
        M.condMean μ (fun ω ↦ M.Yobs ω * (1 - M.DobsReal ω)) true) / M.firstStage μ := by
  have hN : MeasurableSet M.neverTakers := M.measurableSet_stratum _
  have hsplit := M.setIntegral_D_false_compl_eq (M.integrable_Y_D_of_YD hE (hY false) z)
  rw [setIntegral_congr_fun (M.measurableSet_D_eq_true false).compl (g := M.Y z false)
      fun ω hω ↦ by
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Bool.not_eq_true] at hω; simp [hω],
    setIntegral_congr_fun M.measurableSet_compliers (g := M.Y z false)
      fun ω hω ↦ by simp [(mem_compliers.1 hω).1],
    setIntegral_congr_fun hN (g := M.Y z false)
      fun ω hω ↦ by simp [(mem_neverTakers.1 hω).1]] at hsplit
  rw [M.condMean_Yobs_mul_one_sub_DobsReal hE hI hR.2.1 (hY false) z,
    M.condMean_Yobs_mul_one_sub_DobsReal hE hI hR.1 (hY true) z, hsplit,
    setIntegral_congr_set (M.ae_eq_neverTakers hM), add_sub_cancel_right,
    M.firstStage_eq_measure_compliers hI hM hR.1 hR.2.1, integral_cond_eq_inv_mul,
    div_eq_inv_mul]

/-- The complier mean of the treated potential outcome under the bundled LATE assumptions. -/
theorem LATEAssumptions.complierMean_true_eq [IsProbabilityMeasure μ] {M : IVModel Ω}
    (h : M.LATEAssumptions μ) (z : Bool) :
    ∫ ω, M.Y z true ω ∂μ[|M.compliers] =
      (M.condMean μ (fun ω ↦ M.Yobs ω * M.DobsReal ω) true -
        M.condMean μ (fun ω ↦ M.Yobs ω * M.DobsReal ω) false) / M.firstStage μ :=
  M.complierMean_true_eq h.exclusion h.independence h.monotonicity h.relevance h.integrable z

/-- The complier mean of the untreated potential outcome under the bundled LATE assumptions. -/
theorem LATEAssumptions.complierMean_false_eq [IsProbabilityMeasure μ] {M : IVModel Ω}
    (h : M.LATEAssumptions μ) (z : Bool) :
    ∫ ω, M.Y z false ω ∂μ[|M.compliers] =
      (M.condMean μ (fun ω ↦ M.Yobs ω * (1 - M.DobsReal ω)) false -
        M.condMean μ (fun ω ↦ M.Yobs ω * (1 - M.DobsReal ω)) true) / M.firstStage μ :=
  M.complierMean_false_eq h.exclusion h.independence h.monotonicity h.relevance h.integrable z

/-! ### One-sided noncompliance -/

/-- The set of potential-variable vectors of a complier. -/
def complierPot : Set Potentials := {w | w.1 false = false ∧ w.1 true = true}

theorem measurableSet_complierPot : MeasurableSet complierPot :=
  ((measurable_fst_eval false) (measurableSet_singleton false)).inter
    ((measurable_fst_eval true) (measurableSet_singleton true))

theorem compliers_eq_preimage : M.compliers = M.potentials ⁻¹' complierPot := by
  ext ω; simp [mem_compliers, complierPot, potentials]

/-- **One-sided noncompliance.** Assume the exclusion restriction, instrument independence,
relevance, integrable responses `Y z (D z)`, and that no unit takes the treatment when the
instrument is `false` (`D false = false` almost surely; this implies monotonicity). Then the Wald
ratio equals the average treatment effect on the treated `E[Y z true - Y z false | Dobs = true]`.
Under these assumptions `P(Dobs = true) = P(Z = true) P(compliers) > 0`, so the right side is a
genuine conditional mean. -/
theorem wald_eq_effectTreated [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hR : M.Relevance μ) (hY : ∀ z, Integrable (M.YD z) μ)
    (hOne : ∀ᵐ ω ∂μ, M.D false ω = false) (z : Bool) :
    M.wald μ = ∫ ω, M.effect z ω ∂μ[|{ω | M.Dobs ω = true}] := by
  have hM : M.Monotonicity μ := by
    filter_upwards [hOne] with ω h
    rw [h]; exact Bool.false_le _
  set S := M.instrumentEq true ∩ M.compliers with hSdef
  have hT : ({ω | M.Dobs ω = true} : Set Ω) =ᵐ[μ] S := by
    filter_upwards [hOne] with ω h
    simp only [hSdef, Set.mem_inter_iff, instrumentEq, Set.mem_preimage,
      Set.mem_singleton_iff, mem_compliers, Dobs, h, true_and]
    cases M.Z ω <;> simp [h]
  have hcond : μ[|{ω | M.Dobs ω = true}] = μ[|S] := by
    simp only [ProbabilityTheory.cond, Measure.restrict_congr_set hT, measure_congr hT]
  have hS : μ.real S = μ.real (M.instrumentEq true) * μ.real M.compliers := by
    simp only [measureReal_def]
    rw [hSdef, M.compliers_eq_preimage, instrumentEq,
      indepFun_iff_measure_inter_preimage_eq_mul.1 hI _ _ (measurableSet_singleton true)
        measurableSet_complierPot, ENNReal.toReal_mul]
  have hp : μ.real (M.instrumentEq true) ≠ 0 :=
    fun h ↦ hR.1 ((measureReal_eq_zero_iff).1 h)
  -- the effect restricted to the compliers, as a function of the potential variables
  set φ : Potentials → ℝ := complierPot.indicator fun w ↦ w.2 z true - w.2 z false
  have hφ : Measurable φ :=
    ((measurable_snd_eval z true).sub (measurable_snd_eval z false)).indicator
      measurableSet_complierPot
  have hfun : (fun ω ↦ φ (M.potentials ω)) = M.compliers.indicator (M.effect z) := by
    funext ω
    simp only [φ, Set.indicator]
    split_ifs with h1 h2 h2
    · rfl
    · rw [M.compliers_eq_preimage] at h2; exact absurd h1 h2
    · rw [M.compliers_eq_preimage] at h2; exact absurd h2 h1
    · rfl
  have hint := M.integrable_indicator_compliers_effect hE hY z
  have hc : ∫ ω, M.compliers.indicator (M.effect z) ω ∂μ[|M.instrumentEq true] =
      ∫ ω, M.compliers.indicator (M.effect z) ω ∂μ := by
    have := M.condMean_potentials hI hR.1 hφ (hfun ▸ hint)
    rwa [hfun] at this
  have hSint : ∫ ω in S, M.effect z ω ∂μ =
      μ.real (M.instrumentEq true) * ∫ ω in M.compliers, M.effect z ω ∂μ := by
    rw [hSdef, ← setIntegral_indicator M.measurableSet_compliers,
      ← integral_indicator M.measurableSet_compliers (f := M.effect z), ← hc,
      integral_cond_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
  rw [M.wald_eq_complierEffect hE hI hM hR hY z, complierEffect, hcond,
    integral_cond_eq_inv_mul, integral_cond_eq_inv_mul, hSint, hS, mul_inv]
  calc (μ.real M.compliers)⁻¹ * ∫ ω in M.compliers, M.effect z ω ∂μ
      = ((μ.real (M.instrumentEq true))⁻¹ * μ.real (M.instrumentEq true)) *
          ((μ.real M.compliers)⁻¹ * ∫ ω in M.compliers, M.effect z ω ∂μ) := by
        rw [inv_mul_cancel₀ hp, one_mul]
    _ = _ := by ring

end IVModel

end CausalInference
