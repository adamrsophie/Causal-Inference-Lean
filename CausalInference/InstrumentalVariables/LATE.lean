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

* `IVModel.firstStage_eq`: under instrument independence, the first stage equals
  `P(compliers) - P(defiers)`; `IVModel.firstStage_eq_measure_compliers`: under monotonicity
  as well, it equals `P(compliers)`.
* `IVModel.relevance_iff`: under independence and monotonicity, relevance is equivalent to
  `0 < P(compliers)`.
* `IVModel.reducedForm_eq`: under exclusion and independence, the reduced form equals
  `E[(Y 1 - Y 0) 1_compliers] - E[(Y 1 - Y 0) 1_defiers]`.
* `IVModel.wald_eq_complierEffect`: the LATE theorem. Under exclusion, independence,
  monotonicity, relevance, `0 < P(Z = true) < 1` and integrable potential outcomes, the Wald
  ratio equals the complier average causal effect. `IVModel.LATEAssumptions.wald_eq` is the
  same statement with the hypotheses bundled in `IVModel.LATEAssumptions`.
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

theorem integrable_DReal [IsFiniteMeasure μ] (z : Bool) : Integrable (M.DReal z) μ := by
  refine Integrable.of_bound
    (measurable_boolToReal.comp (M.measurable_D z)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [DReal, boolToReal]
  split_ifs <;> simp

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

/-- Under independence and monotonicity, relevance (a nonzero first stage) holds if and only if
the compliers have positive probability. -/
theorem relevance_iff [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₁ : μ (M.instrumentEq true) ≠ 0)
    (h₀ : μ (M.instrumentEq false) ≠ 0) :
    M.Relevance μ ↔ 0 < μ.real M.compliers := by
  rw [Relevance, M.firstStage_eq_measure_compliers hI hM h₁ h₀]
  exact ⟨fun h ↦ measureReal_nonneg.lt_of_ne' h, ne_of_gt⟩

/-- Under the exclusion restriction, `Y z d = Y z' d` almost surely for all `z`, `z'`, `d`. -/
theorem Exclusion.ae_eq {M : IVModel Ω} (hE : M.Exclusion μ) (z z' d : Bool) :
    M.Y z d =ᵐ[μ] M.Y z' d := by
  cases z <;> cases z'
  · rfl
  · exact (hE d).symm
  · exact hE d
  · rfl

/-- Reduced-form decomposition: under the exclusion restriction, instrument independence,
integrable potential outcomes and `0 < P(Z = z)` for both values `z`,
`E[Yobs | Z = true] - E[Yobs | Z = false] = E[(Y 1 - Y 0) 1_compliers] - E[(Y 1 - Y 0) 1_defiers]`,
where `Y d` is `Y z d` for any fixed instrument value `z`. -/
theorem reducedForm_eq [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hY : ∀ z d, Integrable (M.Y z d) μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) (z : Bool) :
    M.reducedForm μ =
      ∫ ω in M.compliers, M.effect z ω ∂μ - ∫ ω in M.defiers, M.effect z ω ∂μ := by
  have hτ : Integrable (M.effect z) μ := (hY z true).sub (hY z false)
  have hT : Integrable (M.YD true) μ := M.integrable_Y_D (hY true) true
  have hF : Integrable (M.YD false) μ := M.integrable_Y_D (hY false) false
  rw [reducedForm, M.condMean_Yobs hI h₁, M.condMean_Yobs hI h₀,
    ← integral_sub hT hF,
    ← integral_indicator M.measurableSet_compliers, ← integral_indicator M.measurableSet_defiers,
    ← integral_sub (hτ.indicator M.measurableSet_compliers)
      (hτ.indicator M.measurableSet_defiers)]
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

/-- **The LATE theorem** (Imbens and Angrist, 1994). Assume the exclusion restriction,
instrument independence, monotonicity, relevance (a nonzero first stage; under the other
assumptions this is `0 < P(compliers)`, see `IVModel.relevance_iff`), `0 < P(Z = true) < 1`, and
integrable potential outcomes. Then the Wald ratio
`(E[Yobs | Z = true] - E[Yobs | Z = false]) / (E[Dobs | Z = true] - E[Dobs | Z = false])`
equals the complier average causal effect `E[Y z true - Y z false | compliers]`, for either
instrument value `z`.

Without relevance the compliers would be null and the equation would hold only as `0 = 0`, by
Lean's conventions for `x / 0` and for conditioning on a null set. Relevance excludes that
degenerate case and makes both sides genuine: the Wald ratio is then a quotient by a nonzero first
stage, and `μ[|compliers]` is a probability measure. -/
theorem wald_eq_complierEffect [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ) (hR : M.Relevance μ)
    (hY : ∀ z d, Integrable (M.Y z d) μ) (hpos : 0 < μ (M.instrumentEq true))
    (hlt : μ (M.instrumentEq true) < 1) (z : Bool) :
    M.wald μ = M.complierEffect μ z := by
  have h₁ : μ (M.instrumentEq true) ≠ 0 := hpos.ne'
  have h₀ : μ (M.instrumentEq false) ≠ 0 := by
    have hc : M.instrumentEq false = (M.instrumentEq true)ᶜ := by
      ext ω; simp [instrumentEq]
    rw [hc, prob_compl_eq_one_sub (M.measurableSet_instrumentEq true)]
    exact (tsub_pos_of_lt hlt).ne'
  have hFS := M.firstStage_eq_measure_compliers hI hM h₁ h₀
  have hC : μ.real M.compliers ≠ 0 := hFS ▸ hR
  rw [wald, div_eq_iff hR, M.reducedForm_eq hE hI hY h₁ h₀ z, hFS,
    setIntegral_measure_zero _ (M.measure_defiers_eq_zero hM), sub_zero, complierEffect,
    ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, ← measureReal_def,
    smul_eq_mul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]

/-- The hypotheses of the LATE theorem, bundled: exclusion, instrument independence,
monotonicity, relevance, `0 < P(Z = true) < 1`, and integrable potential outcomes. -/
structure LATEAssumptions (μ : Measure Ω) : Prop where
  exclusion : M.Exclusion μ
  independence : M.InstrumentIndependence μ
  monotonicity : M.Monotonicity μ
  relevance : M.Relevance μ
  integrable : ∀ z d, Integrable (M.Y z d) μ
  instrument_pos : 0 < μ (M.instrumentEq true)
  instrument_lt_one : μ (M.instrumentEq true) < 1

/-- The LATE theorem in bundled form: under `LATEAssumptions` the Wald ratio equals the complier
average causal effect. -/
theorem LATEAssumptions.wald_eq [IsProbabilityMeasure μ] {M : IVModel Ω}
    (h : M.LATEAssumptions μ) (z : Bool) : M.wald μ = M.complierEffect μ z :=
  M.wald_eq_complierEffect h.exclusion h.independence h.monotonicity h.relevance h.integrable
    h.instrument_pos h.instrument_lt_one z

end IVModel

end CausalInference
