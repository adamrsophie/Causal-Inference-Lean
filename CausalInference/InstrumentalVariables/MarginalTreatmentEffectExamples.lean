/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.MarginalTreatmentEffect
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A latent index model with a decreasing marginal treatment effect

A worked latent index model (`CausalInference.LatentIndexModel`) on `Fin 3 × ℝ`: the instrument
is uniform on three values with thresholds `1 / 4`, `1 / 2`, `3 / 4`, independent of a resistance
`V` uniform on the unit interval; `Y₀ = 0` and `Y₁ = 1 - V`, so the marginal treatment effect is
`MTE(v) = 1 - v`. Units with low resistance gain most and select into treatment first (selection
on gains), and the treatment parameters separate:

* average treatment effect `1 / 2` (`MTEExample.ate_eq`);
* effect on the treated `17 / 24` (`MTEExample.att_eq`), with `P(D = 1) = 1 / 2`;
* effect on the untreated `7 / 24` (`MTEExample.atu_eq`);
* Wald ratios `5 / 8` between the first two instrument values and `3 / 8` between the last two,
  the LATEs of the bands `(1 / 4, 1 / 2]` and `(1 / 2, 3 / 4]` (`MTEExample.wald_01`,
  `MTEExample.wald_12`);
* `MTEExample.parameters_distinct`: ATE, ATT and the two LATEs are four different numbers.

Every number is computed from the general results of
`CausalInference.InstrumentalVariables.MarginalTreatmentEffect` and the integral
`∫_{(a, b]} (1 - v) dv = (b - a) - (b² - a²) / 2`. The same population with a constant gain
(`MTEExample.constModel`) has all parameters equal to `2` (`MTEExample.constModel_collapse`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace MTEExample

/-- The uniform law on the unit interval. -/
noncomputable def unitLaw : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitLaw := ⟨by simp [unitLaw]⟩

/-- The sample space: an instrument value in `Fin 3` and a resistance in `ℝ`. -/
abbrev Space : Type := Fin 3 × ℝ

/-- The instrument is uniform on its three values, independent of a resistance that is
uniform on the unit interval. -/
noncomputable def P : Measure Space := (uniformOn (Set.univ : Set (Fin 3))).prod unitLaw

instance : IsProbabilityMeasure P := by unfold P; infer_instance

/-- The marginal treatment effect of the example: `m(v) = 1 - v`. Units with low resistance
(the first to take the treatment) gain most. -/
def mte (v : ℝ) : ℝ := 1 - v

/-- The thresholds of the three instrument values: `1 / 4`, `1 / 2`, `3 / 4`. -/
noncomputable def threshold : Fin 3 → ℝ := ![1 / 4, 1 / 2, 3 / 4]

/-- The latent index model: `Y₀ = 0`, `Y₁ = 1 - V`, the resistance is the second coordinate
and the instrument the first. -/
noncomputable def model : LatentIndexModel Space (Fin 3) where
  Y₀ _ := 0
  Y₁ ω := mte ω.2
  V ω := ω.2
  Z ω := ω.1
  p := threshold
  measurable_Y₀ := measurable_const
  measurable_Y₁ := measurable_const.sub measurable_snd
  measurable_V := measurable_snd
  measurable_Z := measurable_fst
  measurable_p := measurable_of_countable _

open LatentIndexModel

theorem measurable_mte : Measurable mte := measurable_const.sub measurable_id

theorem map_fst : P.map Prod.fst = uniformOn (Set.univ : Set (Fin 3)) := by
  rw [P, Measure.map_fst_prod, measure_univ, one_smul]

theorem map_snd : P.map Prod.snd = unitLaw := by
  rw [P, Measure.map_snd_prod, measure_univ, one_smul]

theorem uniformResistance : model.UniformResistance P := map_snd

theorem instrumentIndependence : model.InstrumentIndependence P :=
  indepFun_prod (X := id) (Y := fun v : ℝ ↦ ((0 : ℝ), mte v, v)) measurable_id
    (measurable_const.prodMk (measurable_mte.prodMk measurable_id))

theorem integrable_mte_snd : Integrable (fun ω : Space ↦ mte ω.2) P := by
  have h : Integrable mte unitLaw :=
    (continuous_const.sub continuous_id).integrableOn_Icc
  rw [← map_snd] at h
  exact (integrable_map_measure measurable_mte.aestronglyMeasurable
    measurable_snd.aemeasurable).1 h

theorem gain_eq : model.gain = mte ∘ model.V := by
  funext ω; simp [LatentIndexModel.gain, model]

theorem isMTE : model.IsMTE P mte := by
  refine ⟨measurable_mte, ?_⟩
  rw [gain_eq, condExp_of_stronglyMeasurable model.comap_V_le
    (measurable_mte.comp (comap_measurable model.V)).stronglyMeasurable]
  exact integrable_mte_snd

theorem integrable_Y₀ : Integrable model.Y₀ P := integrable_const _

theorem integrable_Y₁ : Integrable model.Y₁ P := integrable_mte_snd

theorem integrable_gain : Integrable model.gain P := by
  rw [gain_eq]; exact integrable_mte_snd

theorem measure_instrument (z : Fin 3) : P (model.Z ⁻¹' {z}) = 3⁻¹ := by
  have : model.Z ⁻¹' {z} = {z} ×ˢ (Set.univ : Set ℝ) := by ext ω; simp [model]
  rw [this, P, Measure.prod_prod, measure_univ, mul_one, uniformOn_univ]
  simp

theorem measure_instrument_ne_zero (z : Fin 3) : P (model.Z ⁻¹' {z}) ≠ 0 := by
  rw [measure_instrument]; simp

theorem threshold_mem (z : Fin 3) : threshold z ∈ Icc (0 : ℝ) 1 := by
  fin_cases z <;> norm_num [threshold]

/-- `∫_{(a, b]} (1 - v) dv = (b - a) - (b² - a²) / 2`. -/
theorem setIntegral_mte (a b : ℝ) (hab : a ≤ b) :
    ∫ v in Ioc a b, mte v = (b - a) - (b ^ 2 - a ^ 2) / 2 := by
  rw [← intervalIntegral.integral_of_le hab]
  simp only [mte]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id,
    integral_id, intervalIntegral.integral_const, smul_eq_mul, mul_one]

/-- The cumulative MTE: `∫₀^q (1 - v) dv = q - q² / 2` for `q` in the unit interval. -/
theorem mteIntegral_mte {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    mteIntegral mte q = q - q ^ 2 / 2 := by
  have h := mteIntegral_sub (isMTE.integrable_indicator uniformResistance) le_rfl hq.1 hq.2
  have h0 : mteIntegral mte 0 = 0 := intervalIntegral.integral_same
  rw [h0, sub_zero, setIntegral_mte 0 q hq.1] at h
  rw [h]; ring

/-- The average treatment effect of the example is `1 / 2`. -/
theorem ate_eq : ∫ ω, model.gain ω ∂P = 1 / 2 := by
  rw [isMTE.integral_gain uniformResistance integrable_gain, setIntegral_mte 0 1 zero_le_one]
  norm_num

theorem integral_uniform (f : Fin 3 → ℝ) :
    ∫ z, f z ∂(uniformOn (Set.univ : Set (Fin 3))) = (f 0 + f 1 + f 2) / 3 := by
  rw [integral_fintype .of_finite]
  simp [uniformOn_univ, measureReal_def, Fin.sum_univ_three]
  ring

/-- The probability of treatment of the example is `1 / 2`. -/
theorem prob_treated : P.real {ω | model.D ω = true} = 1 / 2 := by
  rw [measureReal_treated uniformResistance instrumentIndependence threshold_mem]
  change ∫ z, threshold z ∂(P.map Prod.fst) = 1 / 2
  rw [map_fst, integral_uniform]
  norm_num [threshold]

/-- The gain of the treated: `E[(Y₁ - Y₀) 1{D = 1}] = 17 / 48`. -/
theorem treated_gain : ∫ ω, {ω | model.D ω = true}.indicator model.gain ω ∂P = 17 / 48 := by
  rw [isMTE.integral_indicator_treated_gain uniformResistance instrumentIndependence
    integrable_gain]
  change ∫ z, mteIntegral mte (threshold z) ∂(P.map Prod.fst) = 17 / 48
  rw [map_fst, integral_uniform, mteIntegral_mte (threshold_mem 0),
    mteIntegral_mte (threshold_mem 1), mteIntegral_mte (threshold_mem 2)]
  norm_num [threshold]

/-- The effect on the treated of the example is `17 / 24`. -/
theorem att_eq : model.att P = 17 / 24 := by
  rw [LatentIndexModel.att, IVModel.integral_cond_eq_inv_mul,
    ← integral_indicator model.measurableSet_D, treated_gain, prob_treated]
  norm_num

/-- The effect on the untreated of the example is `7 / 24`. -/
theorem atu_eq : model.atu P = 7 / 24 := by
  have h := integral_add_compl model.measurableSet_D integrable_gain
  rw [← integral_indicator model.measurableSet_D, treated_gain, ate_eq] at h
  rw [LatentIndexModel.atu, IVModel.integral_cond_eq_inv_mul, setOf_D_false,
    probReal_compl_eq_one_sub model.measurableSet_D, prob_treated, eq_sub_of_add_eq' h]
  norm_num

/-- The Wald ratio between the instrument values `0` and `1` (thresholds `1 / 4` and `1 / 2`)
is `5 / 8`, the LATE of the resistance band `(1 / 4, 1 / 2]`. -/
theorem wald_01 : model.wald P 0 1 = 5 / 8 ∧ model.lateBetween P (1 / 4) (1 / 2) = 5 / 8 := by
  obtain ⟨h1, h2⟩ := isMTE.wald_eq uniformResistance instrumentIndependence integrable_Y₀
    integrable_Y₁ (measure_instrument_ne_zero 0) (measure_instrument_ne_zero 1)
    (by norm_num [model, threshold]) (by norm_num [model, threshold])
    (by norm_num [model, threshold])
  have hv : model.wald P 0 1 = 5 / 8 := by
    rw [h1]
    simp only [model, threshold]
    norm_num [setIntegral_mte]
  refine ⟨hv, ?_⟩
  rw [← hv, h2]
  simp [model, threshold]

/-- The Wald ratio between the instrument values `1` and `2` (thresholds `1 / 2` and `3 / 4`)
is `3 / 8`, the LATE of the resistance band `(1 / 2, 3 / 4]`. -/
theorem wald_12 : model.wald P 1 2 = 3 / 8 ∧ model.lateBetween P (1 / 2) (3 / 4) = 3 / 8 := by
  obtain ⟨h1, h2⟩ := isMTE.wald_eq uniformResistance instrumentIndependence integrable_Y₀
    integrable_Y₁ (measure_instrument_ne_zero 1) (measure_instrument_ne_zero 2)
    (by norm_num [model, threshold]) (by norm_num [model, threshold])
    (by norm_num [model, threshold])
  have hv : model.wald P 1 2 = 3 / 8 := by
    rw [h1]
    simp only [model, threshold]
    norm_num [setIntegral_mte]
  refine ⟨hv, ?_⟩
  rw [← hv, h2]
  simp [model, threshold]

/-- **Four different numbers.** In the latent index model `MTEExample.model`, with the
nonconstant MTE `1 - v`, the average treatment effect is `1 / 2`, the effect on the treated
`17 / 24`, the effect on the untreated `7 / 24`, and the two Wald ratios (the LATEs of the
bands `(1 / 4, 1 / 2]` and `(1 / 2, 3 / 4]`) are `5 / 8` and `3 / 8`. The first four listed
in the statement (ATE, ATT and the two LATEs) are pairwise distinct. -/
theorem parameters_distinct :
    ∫ ω, model.gain ω ∂P = 1 / 2 ∧ model.att P = 17 / 24 ∧ model.atu P = 7 / 24 ∧
      model.wald P 0 1 = 5 / 8 ∧ model.wald P 1 2 = 3 / 8 ∧
      [∫ ω, model.gain ω ∂P, model.att P, model.wald P 0 1, model.wald P 1 2].Nodup := by
  refine ⟨ate_eq, att_eq, atu_eq, wald_01.1, wald_12.1, ?_⟩
  rw [ate_eq, att_eq, wald_01.1, wald_12.1]
  norm_num

/-! ### A constant MTE -/

/-- The same population with a constant gain `2`: `Y₀ = 0`, `Y₁ = 2`. -/
noncomputable def constModel : LatentIndexModel Space (Fin 3) where
  Y₀ _ := 0
  Y₁ _ := 2
  V ω := ω.2
  Z ω := ω.1
  p := threshold
  measurable_Y₀ := measurable_const
  measurable_Y₁ := measurable_const
  measurable_V := measurable_snd
  measurable_Z := measurable_fst
  measurable_p := measurable_of_countable _

theorem constModel_isMTE : constModel.IsMTE P fun _ ↦ 2 := by
  refine ⟨measurable_const, ?_⟩
  have e : constModel.gain = fun _ ↦ (2 : ℝ) := by
    funext ω; simp [LatentIndexModel.gain, constModel]
  rw [e, condExp_const constModel.comap_V_le]
  rfl

theorem constModel_uniform : constModel.UniformResistance P := map_snd

theorem constModel_independence : constModel.InstrumentIndependence P :=
  indepFun_prod (X := id) (Y := fun v : ℝ ↦ ((0 : ℝ), (2 : ℝ), v)) measurable_id
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem constModel_prob_treated : P.real {ω | constModel.D ω = true} = 1 / 2 := by
  rw [measureReal_treated constModel_uniform constModel_independence threshold_mem]
  change ∫ z, threshold z ∂(P.map Prod.fst) = 1 / 2
  rw [map_fst, integral_uniform]
  norm_num [threshold]

theorem constModel_treated_ne_zero : P {ω | constModel.D ω = true} ≠ 0 := by
  intro h
  have hr := constModel_prob_treated
  rw [measureReal_def, h, ENNReal.toReal_zero] at hr
  norm_num at hr

theorem constModel_untreated_ne_zero : P {ω | constModel.D ω = false} ≠ 0 := by
  intro h
  have hr : P.real {ω | constModel.D ω = false} = 0 := by
    rw [measureReal_def, h, ENNReal.toReal_zero]
  rw [setOf_D_false, probReal_compl_eq_one_sub constModel.measurableSet_D,
    constModel_prob_treated] at hr
  norm_num at hr

/-- **With a constant MTE all the parameters coincide.** In `MTEExample.constModel` (same
instrument, thresholds and resistance, constant gain `2`), the average treatment effect, the
effect on the treated, the effect on the untreated and every band LATE equal `2`
(`LatentIndexModel.IsMTE.collapse_of_const`). -/
theorem constModel_collapse :
    ∫ ω, constModel.gain ω ∂P = 2 ∧ constModel.att P = 2 ∧ constModel.atu P = 2 ∧
      ∀ q q', 0 ≤ q → q < q' → q' ≤ 1 → constModel.lateBetween P q q' = 2 :=
  constModel_isMTE.collapse_of_const constModel_uniform constModel_independence threshold_mem
    (integrable_const _ |>.sub (integrable_const _)) (Filter.Eventually.of_forall fun _ ↦ rfl)
    constModel_treated_ne_zero constModel_untreated_ne_zero

end MTEExample

end CausalInference
