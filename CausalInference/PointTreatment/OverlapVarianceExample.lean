/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PointTreatment.OverlapVariance
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Point treatment: a population with vanishing overlap and bounded variance

A vanishing minimum propensity does not force the variance of the weighted arm mean to diverge:
the variance is governed by the mean `E[1 / π_a(W)]` (`IndicatorIgnorable.variance_ipwTerm`),
which can stay bounded. This file constructs, for each `ε ∈ (0, 1/2]`, a population in which
the smallest propensity is `ε` and the variance of the Horvitz and Thompson term of the treated
arm is exactly `4 - 4ε`, which tends to `4` as `ε → 0`.

**The construction.** The covariate is `W = (S, Σ)`: a stratum `S` with `P(S = 1) = 4ε²` and a
fair sign `Σ`, independent. Treatment is assigned by a uniform draw `V` on `(0, 1)`,
independent of `W`: `A = 1{V < e(W)}`, with propensity `e = ε` in the stratum `S = 1` and
`e = (1 + 2ε)/4` in the stratum `S = 0`. Both potential outcomes are the sign, `Y(1) = Y(0) = ±1`.
Then `e(W)` is the propensity score (`isPropensityScore_drawAssign`, a general fact about
assignment by a uniform draw), ignorability holds because the potential outcomes are a function
of `W` (`indicatorIgnorable_of_potentialPair_eq`), `E[Y(1)] = 0`, `Y(1)² = 1`, and
`E[1 / e(W)] = 4ε² / ε + (1 - 4ε²) · 4 / (1 + 2ε) = 4 - 4ε`.

## Main definitions

* `unitUniform`: the uniform law on `(0, 1)`.
* `drawAssign e`: assignment `1{V < e(W)}` by a uniform draw.
* `boolLaw p`: the law on `Bool` with mass `p` at `true`.
* `overlapProp ε`, `overlapLaw ε`, `overlapOutcome`: the constructed population.

## Main results

* `isPropensityScore_drawAssign`, `indicatorIgnorable_of_potentialPair_eq`.
* `overlapExample_variance`: the variance is `4 - 4ε` while the smallest propensity is `ε`.
* `tendsto_overlapExample_variance`: the variance tends to `4` as `ε → 0`.
-/

@[expose] public section

namespace CausalInference

namespace PointTreatment

open MeasureTheory ProbabilityTheory MissingData Set Filter Topology

/-! ### Assignment by a uniform draw -/

/-- The uniform law on `(0, 1)`. -/
noncomputable def unitUniform : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure unitUniform := ⟨by simp [unitUniform]⟩

theorem unitUniform_real_Iio {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : unitUniform.real (Iio c) = c := by
  have hs : Iio c ∩ Ioo 0 1 = Ioo 0 c := by
    ext x
    simp only [mem_inter_iff, mem_Iio, mem_Ioo]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, by linarith [h.2]⟩⟩
  rw [measureReal_def, unitUniform, Measure.restrict_apply measurableSet_Iio, hs,
    Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal h0]

variable {𝒲 : Type*} [MeasurableSpace 𝒲]

/-- Assignment by a uniform draw: the unit `(w, v)` is treated when `v < e(w)`. -/
noncomputable def drawAssign (e : 𝒲 → ℝ) (ω : 𝒲 × ℝ) : Bool := decide (ω.2 < e ω.1)

theorem measurable_drawAssign {e : 𝒲 → ℝ} (he : Measurable e) : Measurable (drawAssign e) := by
  refine measurable_to_bool ?_
  have : drawAssign e ⁻¹' {true} = {ω | ω.2 < e ω.1} := by ext ω; simp [drawAssign]
  rw [this]
  exact measurableSet_lt measurable_snd (he.comp measurable_fst)

/-- **Assignment by a uniform draw has propensity score `e`.** On `𝒲 × ℝ` with the law
`P ⊗ unitUniform`, if `e` is measurable with values in `[0, 1]`, then `e(W)` is a version of
`P(A = 1 | W)` for `A = 1{V < e(W)}`, `W` the first coordinate and `V` the second. -/
theorem isPropensityScore_drawAssign (P : Measure 𝒲) [IsProbabilityMeasure P] {e : 𝒲 → ℝ}
    (he : Measurable e) (he01 : ∀ w, 0 ≤ e w ∧ e w ≤ 1) :
    IsPropensityScore (P.prod unitUniform) (drawAssign e) Prod.fst e := by
  have hA := measurable_drawAssign he
  have hei : Integrable (fun ω : 𝒲 × ℝ => e ω.1) (P.prod unitUniform) :=
    Integrable.of_bound (C := 1) (he.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (he01 _).1]; exact (he01 _).2)
  refine ⟨he, (ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le
    (integrable_respInd hA) (fun _ _ _ => hei.integrableOn) ?_
    (he.comp (comap_measurable Prod.fst)).aestronglyMeasurable).symm⟩
  rintro _ ⟨B, hB, rfl⟩ _
  rw [← Set.prod_univ, setIntegral_prod _ hei.integrableOn,
    setIntegral_prod _ (integrable_respInd hA).integrableOn]
  refine setIntegral_congr_fun hB fun w _ => ?_
  have hind : (fun v : ℝ => respInd (drawAssign e) (w, v)) = (Iio (e w)).indicator 1 := by
    funext v
    by_cases h : v < e w <;> simp [respInd_apply, drawAssign, Set.indicator, h]
  simp only [Measure.restrict_univ]
  rw [hind, integral_indicator_one measurableSet_Iio, unitUniform_real_Iio (he01 w).1 (he01 w).2,
    integral_const, probReal_univ, one_smul]

/-- **Potential outcomes that are functions of the covariates are ignorable.** If
`(Y(0), Y(1)) = f(W)` for a measurable `f`, the indicator form of ignorability holds for every
treatment: `σ(W, Y(0), Y(1)) = σ(W)`. -/
theorem indicatorIgnorable_of_potentialPair_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → Bool} {W : Ω → 𝒲} {Y : Bool → Ω → ℝ} {f : 𝒲 → ℝ × ℝ} (hf : Measurable f)
    (hY : ∀ ω, potentialPair Y ω = f (W ω)) : IndicatorIgnorable μ A W Y := by
  have heq : MeasurableSpace.comap (fun ω => (W ω, potentialPair Y ω)) inferInstance =
      MeasurableSpace.comap W inferInstance := by
    refine le_antisymm ?_
      (measurable_fst.comp (comap_measurable fun ω => (W ω, potentialPair Y ω))).comap_le
    have hfun : (fun ω => (W ω, potentialPair Y ω)) = (fun w => (w, f w)) ∘ W := by
      funext ω; simp [hY]
    rw [hfun]
    exact ((measurable_id.prodMk hf).comp (comap_measurable W)).comap_le
  unfold IndicatorIgnorable
  rw [heq]

/-! ### The constructed population -/

/-- The law on `Bool` with mass `p` at `true` and `1 - p` at `false`. -/
noncomputable def boolLaw (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true + ENNReal.ofReal (1 - p) • Measure.dirac false

theorem isProbabilityMeasure_boolLaw {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (boolLaw p) :=
  ⟨by simp [boolLaw, ← ENNReal.ofReal_add h0 (sub_nonneg.2 h1)]⟩

theorem integral_boolLaw {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (f : Bool → ℝ) :
    ∫ b, f b ∂(boolLaw p) = p * f true + (1 - p) * f false := by
  rw [boolLaw, integral_add_measure (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top)
    (Integrable.of_finite.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (sub_nonneg.2 h1), smul_eq_mul, smul_eq_mul]

/-- The propensity of the constructed population: `ε` in the stratum `S = 1`, `(1 + 2ε)/4` in
the stratum `S = 0`. The covariate is `(S, Σ)`. -/
noncomputable def overlapProp (ε : ℝ) (w : Bool × Bool) : ℝ := if w.1 then ε else (1 + 2 * ε) / 4

/-- The covariate law: `P(S = 1) = 4ε²` and a fair sign `Σ`, independent. -/
noncomputable def overlapCovLaw (ε : ℝ) : Measure (Bool × Bool) :=
  (boolLaw (4 * ε ^ 2)).prod (boolLaw (1 / 2))

/-- The law of the constructed population on `(Bool × Bool) × ℝ`: the covariate and an
independent uniform draw. -/
noncomputable def overlapLaw (ε : ℝ) : Measure ((Bool × Bool) × ℝ) :=
  (overlapCovLaw ε).prod unitUniform

/-- Both potential outcomes are the sign `Σ = ±1`. -/
def overlapOutcome (_ : Bool) (ω : (Bool × Bool) × ℝ) : ℝ := if ω.1.2 then 1 else -1

section Example

variable {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
include hε0 hε1

theorem isProbabilityMeasure_overlapCovLaw : IsProbabilityMeasure (overlapCovLaw ε) := by
  have := isProbabilityMeasure_boolLaw (p := 4 * ε ^ 2) (by positivity) (by nlinarith)
  have := isProbabilityMeasure_boolLaw (p := 1 / 2) (by norm_num) (by norm_num)
  unfold overlapCovLaw
  infer_instance

theorem integral_overlapCovLaw (f : Bool × Bool → ℝ) :
    ∫ w, f w ∂(overlapCovLaw ε) = 4 * ε ^ 2 * (f (true, true) + f (true, false)) / 2 +
      (1 - 4 * ε ^ 2) * (f (false, true) + f (false, false)) / 2 := by
  have := isProbabilityMeasure_boolLaw (p := 4 * ε ^ 2) (by positivity) (by nlinarith)
  have := isProbabilityMeasure_boolLaw (p := 1 / 2) (by norm_num) (by norm_num)
  rw [overlapCovLaw, integral_prod _ Integrable.of_finite,
    integral_boolLaw (by positivity) (by nlinarith)]
  simp only [integral_boolLaw (p := 1 / 2) (by norm_num) (by norm_num)]
  ring

/-- **The constructed population.** For `0 < ε ≤ 1/2`, the propensity score of the
constructed population is `overlapProp ε`, ignorability holds, its smallest value is `ε`, the
treated arm mean is `0`, and the variance of the Horvitz and Thompson term of the treated arm
is `4 - 4ε`. -/
theorem overlapExample_variance :
    IsPropensityScore (overlapLaw ε) (drawAssign (overlapProp ε)) Prod.fst (overlapProp ε) ∧
    IndicatorIgnorable (overlapLaw ε) (drawAssign (overlapProp ε)) Prod.fst overlapOutcome ∧
    (∀ w, ε ≤ overlapProp ε w) ∧ overlapProp ε (true, true) = ε ∧
    armMean (overlapLaw ε) overlapOutcome true = 0 ∧
    variance (ipwTerm (drawAssign (overlapProp ε)) overlapOutcome Prod.fst (overlapProp ε) true)
      (overlapLaw ε) = 4 - 4 * ε := by
  have := isProbabilityMeasure_overlapCovLaw hε0 hε1
  have : IsProbabilityMeasure (overlapLaw ε) := by unfold overlapLaw; infer_instance
  have he : Measurable (overlapProp ε) := Measurable.of_discrete
  have hpos : ∀ w, 0 < overlapProp ε w := fun w => by
    unfold overlapProp; split_ifs <;> positivity
  have hle : ∀ w, ε ≤ overlapProp ε w := fun w => by
    unfold overlapProp; split_ifs <;> linarith
  have he01 : ∀ w, 0 ≤ overlapProp ε w ∧ overlapProp ε w ≤ 1 := fun w => by
    refine ⟨(hpos w).le, ?_⟩
    unfold overlapProp; split_ifs <;> linarith
  have hps := isPropensityScore_drawAssign (overlapCovLaw ε) he he01
  have hign : IndicatorIgnorable (overlapLaw ε) (drawAssign (overlapProp ε)) Prod.fst
      overlapOutcome :=
    indicatorIgnorable_of_potentialPair_eq
      (f := fun w : Bool × Bool => ((if w.2 then 1 else -1 : ℝ), (if w.2 then 1 else -1 : ℝ)))
      Measurable.of_discrete fun ω => rfl
  have hY : ∀ a, Measurable (overlapOutcome a) := fun a =>
    (Measurable.of_discrete (f := fun w : Bool × Bool => (if w.2 then 1 else -1 : ℝ))).comp
      measurable_fst
  -- functions of the covariate
  have hfst : ∀ g : Bool × Bool → ℝ, Integrable (fun ω : (Bool × Bool) × ℝ => g ω.1)
      (overlapLaw ε) ∧
      ∫ ω, g ω.1 ∂(overlapLaw ε) = ∫ w, g w ∂(overlapCovLaw ε) := fun g => by
    have hmap : (overlapLaw ε).map Prod.fst = overlapCovLaw ε := by
      rw [overlapLaw, Measure.map_fst_prod]; simp
    refine ⟨?_, ?_⟩
    · have hg : Integrable g ((overlapLaw ε).map Prod.fst) := hmap ▸ Integrable.of_finite
      exact hg.comp_measurable measurable_fst
    · rw [overlapLaw, integral_fun_fst]; simp
  have hmean : armMean (overlapLaw ε) overlapOutcome true = 0 := by
    change ∫ ω, (fun w : Bool × Bool => if w.2 then (1 : ℝ) else -1) ω.1 ∂(overlapLaw ε) = 0
    rw [(hfst fun w => if w.2 then 1 else -1).2, integral_overlapCovLaw hε0 hε1]
    norm_num
  have hsq : (fun ω => overlapOutcome true ω ^ 2 / armProb (overlapProp ε) true ω.1) =
      fun ω => (fun w => 1 / overlapProp ε w) ω.1 := by
    funext ω; simp only [overlapOutcome, armProb_true]; split_ifs <;> norm_num
  have hint : Integrable (fun ω => overlapOutcome true ω ^ 2 /
      armProb (overlapProp ε) true ω.1) (overlapLaw ε) := by
    rw [hsq]; exact (hfst fun w => 1 / overlapProp ε w).1
  refine ⟨hps, hign, hle, by simp [overlapProp], hmean, ?_⟩
  rw [hign.variance_ipwTerm measurable_fst (measurable_drawAssign he) hY hps true
    (Eventually.of_forall fun ω => hpos ω.1) (hfst fun w => if w.2 then 1 else -1).1 hint,
    hmean, hsq, (hfst fun w => 1 / overlapProp ε w).2, integral_overlapCovLaw hε0 hε1]
  simp only [overlapProp, ite_true, Bool.false_eq_true, ite_false]
  have : (1 + 2 * ε) ≠ 0 := by linarith
  field_simp
  ring

end Example

/-- **The variance stays bounded as overlap vanishes.** In the constructed population the
smallest propensity is `ε`, while the variance of the Horvitz and Thompson term of the treated
arm, `4 - 4ε`, tends to `4` as `ε → 0` from above. -/
theorem tendsto_overlapExample_variance :
    Tendsto (fun ε => variance (ipwTerm (drawAssign (overlapProp ε)) overlapOutcome Prod.fst
      (overlapProp ε) true) (overlapLaw ε)) (𝓝[>] 0) (𝓝 4) := by
  have h : Tendsto (fun ε : ℝ => 4 - 4 * ε) (𝓝[>] 0) (𝓝 4) := by
    have : Tendsto (fun ε : ℝ => 4 - 4 * ε) (𝓝 0) (𝓝 (4 - 4 * 0)) :=
      (continuous_const.sub (continuous_const.mul continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
  exact ((overlapExample_variance hε.1 hε.2.le).2.2.2.2.2).symm

end PointTreatment

end CausalInference
