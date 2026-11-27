/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.Counterexamples
public import CausalInference.PartialIdentification.Manski

/-!
# Bounds on the average treatment effect with a binary instrument

Partial identification of the average treatment effect in the binary instrumental variable model
`CausalInference.IVModel` with outcomes in `[lo, hi]`, following Robins (1989), Manski (1990,
*Nonparametric bounds on treatment effects*) and Balke and Pearl (1997, *Bounds on treatment
effects from studies with imperfect compliance*), and the testable implications of the IV
assumptions.

## Main definitions

* `CausalInference.IVBounds.obsMean`: a conditional mean `E[h(D, Y) | Z = z]` computed from an
  observation map `ω ↦ (Z ω, D ω, Y ω)` alone.
* `IVBounds.lowerBound`, `IVBounds.upperBound`: the IV bounds
  `E[Y 1{D=1} | Z=1] - E[Y 1{D=0} | Z=0] + lo P(D=0 | Z=1) - hi P(D=1 | Z=0)` and the same with
  `lo` and `hi` exchanged; `IVBounds.lowerBoundSwap`, `IVBounds.upperBoundSwap`: the same with the
  instrument arms swapped.
* `IVBounds.models`: exclusion, instrument independence, monotonicity, positive instrument
  probabilities, outcomes in `[lo, hi]`.
* `IVModel.refill`: the model with the never-takers' treated outcome and the always-takers'
  untreated outcome replaced by constants; it has the same observed data.
* `MeanIndependence.MeanIndependent`: mean independence of the potential outcomes from an
  instrument.

## Main results

* `IVModel.ate_mem_Icc_bounds`: under exclusion and independence the average treatment effect lies
  in `[lowerBound, upperBound]`; `IVModel.ate_mem_Icc_boundsSwap`: the same for the bounds with the
  instrument arms swapped; `IVModel.ate_mem_Icc_bounds_inter`: hence in the intersection of the
  two intervals.
* `IVBounds.upperBound_sub_lowerBound`: from the definitions alone, the width is
  `(hi - lo) (P(D=0 | Z=1) + P(D=1 | Z=0))`; `IVModel.upperBound_sub_lowerBound`: under
  independence and monotonicity it is `(hi - lo) (1 - P(compliers))`.
* `IVModel.ate_eq_sum_strata`, `IVModel.ate_eq_strata_cond`: under monotonicity,
  `ATE = P(C) CACE + P(AT) E[Y 1 - Y 0 | AT] + P(NT) E[Y 1 - Y 0 | NT]`;
  `IVModel.obsMean_yTreated_false`, `IVModel.obsMean_yUntreated_true`,
  `IVModel.obsMean_treatedInd_false`, `IVModel.obsMean_untreatedInd_true` identify
  `∫_AT Y 1`, `∫_NT Y 0`, `P(AT)` and `P(NT)`; `IVModel.meanY1_eq`, `IVModel.meanY0_eq` show that
  `∫_NT Y 1` and `∫_AT Y 0` are the only unidentified parts.
* `IVBounds.identifiedSet_ate`: sharpness. Under the assumptions of `IVBounds.models` the
  identified set is exactly `[lowerBound, upperBound]`; `IVBounds.exists_model_ate_eq_lowerBound`
  and `IVBounds.exists_model_ate_eq_upperBound` exhibit the endpoint models.
* `MeanIndependence.meanY1_mem_Icc`, `MeanIndependence.meanY0_mem_Icc`,
  `MeanIndependence.ate_mem_Icc`: the bounds of Manski (1990) under mean independence, the
  intersection over instrument values of the worst-case bounds; `MeanIndependence.Icc_meanY1_subset`
  and `MeanIndependence.Icc_meanY0_subset`: they are at least as tight as the no-assumption bounds.
* `IVModel.instrumentalInequality_treated`, `IVModel.instrumentalInequality_untreated` and their
  observed-law versions: `P(Y ∈ B, D = 1 | Z = 1) ≥ P(Y ∈ B, D = 1 | Z = 0)` and
  `P(Y ∈ B, D = 0 | Z = 0) ≥ P(Y ∈ B, D = 0 | Z = 1)` for every measurable `B` (for a binary
  outcome, `B = {y}`).
* `IVBounds.violatingLaw_lt`, `IVBounds.not_assumptions_of_law_eq_violatingLaw`: a concrete
  observed-data law with a binary outcome violating the first inequality, so no model with that
  law satisfies exclusion, independence and monotonicity.

## Implementation notes

The bound inclusion needs only exclusion and instrument independence. Under monotonicity these
bounds are the ones obtained from the stratum decomposition; Balke and Pearl (1997) show that
they then coincide with their linear-programming bounds. That coincidence is not formalized here;
sharpness is proved directly by construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

/-- For a finite measure, `μ(s) E[f | s] = ∫_s f`, where `E[f | s]` is the integral against the
conditional measure `μ[|s]`. If `μ(s) = 0` both sides vanish; the identity carries no
information then, and every use below either has `μ(s) > 0` or does not divide by `μ(s)`. -/
theorem measureReal_mul_integral_cond {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (s : Set Ω) (f : Ω → ℝ) :
    μ.real s * ∫ ω, f ω ∂μ[|s] = ∫ ω in s, f ω ∂μ := by
  rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
    ← measureReal_def]
  by_cases h : μ.real s = 0
  · have : μ s = 0 := (measureReal_eq_zero_iff).1 h
    rw [h, zero_mul, Measure.restrict_eq_zero.2 this, integral_zero_measure]
  · rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]

namespace IVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- With bounded potential outcomes every potential outcome is integrable. -/
theorem integrable_Y_of_bounded [IsFiniteMeasure μ] {lo hi : ℝ}
    (hb : ∀ z d ω, M.Y z d ω ∈ Icc lo hi) (z d : Bool) : Integrable (M.Y z d) μ :=
  Manski.integrable_of_mem_Icc (M.measurable_Y z d) (hb z d)

end IVModel

namespace IVBounds

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The conditional mean `E[h(D, Y) | Z = z]` computed from an observation map
`o : Ω → Bool × Bool × ℝ` (instrument, treatment, outcome): the integral of `h (o ω).2.1 (o ω).2.2`
against `μ` conditioned on `{ω | (o ω).1 = z}`. It depends on the model only through `o`. -/
noncomputable def obsMean (μ : Measure Ω) (o : Ω → Bool × Bool × ℝ) (h : Bool → ℝ → ℝ)
    (z : Bool) : ℝ :=
  ∫ ω, h (o ω).2.1 (o ω).2.2 ∂μ[|(fun ω ↦ (o ω).1) ⁻¹' {z}]

/-- `Y 1{D = 1}`. -/
def yTreated (d : Bool) (y : ℝ) : ℝ := if d then y else 0

/-- `Y 1{D = 0}`. -/
def yUntreated (d : Bool) (y : ℝ) : ℝ := if d then 0 else y

/-- `1{D = 1}`. -/
def treatedInd (d : Bool) (_ : ℝ) : ℝ := if d then 1 else 0

/-- `1{D = 0}`. -/
def untreatedInd (d : Bool) (_ : ℝ) : ℝ := if d then 0 else 1

theorem measurable_yTreated (d : Bool) : Measurable (yTreated d) := by
  cases d
  · exact measurable_const
  · exact measurable_id

theorem measurable_yUntreated (d : Bool) : Measurable (yUntreated d) := by
  cases d
  · exact measurable_id
  · exact measurable_const

theorem measurable_treatedInd (d : Bool) : Measurable (treatedInd d) := measurable_const

theorem measurable_untreatedInd (d : Bool) : Measurable (untreatedInd d) := measurable_const

/-- The lower IV bound on the average treatment effect, a function of the observation `o` alone:
`E[Y 1{D=1} | Z=1] - E[Y 1{D=0} | Z=0] + lo P(D=0 | Z=1) - hi P(D=1 | Z=0)`. -/
noncomputable def lowerBound (μ : Measure Ω) (lo hi : ℝ) (o : Ω → Bool × Bool × ℝ) : ℝ :=
  obsMean μ o yTreated true - obsMean μ o yUntreated false + lo * obsMean μ o untreatedInd true -
    hi * obsMean μ o treatedInd false

/-- The upper IV bound on the average treatment effect, a function of the observation `o` alone:
`E[Y 1{D=1} | Z=1] - E[Y 1{D=0} | Z=0] + hi P(D=0 | Z=1) - lo P(D=1 | Z=0)`. -/
noncomputable def upperBound (μ : Measure Ω) (lo hi : ℝ) (o : Ω → Bool × Bool × ℝ) : ℝ :=
  obsMean μ o yTreated true - obsMean μ o yUntreated false + hi * obsMean μ o untreatedInd true -
    lo * obsMean μ o treatedInd false

/-- The IV lower bound with the instrument arms swapped, a function of the observation `o`
alone: `E[Y 1{D=1} | Z=0] - E[Y 1{D=0} | Z=1] + lo P(D=0 | Z=0) - hi P(D=1 | Z=1)`. For a binary
outcome (`lo = 0`, `hi = 1`) it is `P(Y=1, D=1 | Z=0) + P(Y=0, D=0 | Z=1) - 1`. -/
noncomputable def lowerBoundSwap (μ : Measure Ω) (lo hi : ℝ) (o : Ω → Bool × Bool × ℝ) : ℝ :=
  obsMean μ o yTreated false - obsMean μ o yUntreated true + lo * obsMean μ o untreatedInd false -
    hi * obsMean μ o treatedInd true

/-- The IV upper bound with the instrument arms swapped:
`E[Y 1{D=1} | Z=0] - E[Y 1{D=0} | Z=1] + hi P(D=0 | Z=0) - lo P(D=1 | Z=1)`. For a binary outcome
it is `1 - P(Y=0, D=1 | Z=0) - P(Y=1, D=0 | Z=1)`. -/
noncomputable def upperBoundSwap (μ : Measure Ω) (lo hi : ℝ) (o : Ω → Bool × Bool × ℝ) : ℝ :=
  obsMean μ o yTreated false - obsMean μ o yUntreated true + hi * obsMean μ o untreatedInd false -
    lo * obsMean μ o treatedInd true

/-- **Width of the IV bounds, without assumptions.** For any measure and any observation map,
`upperBound - lowerBound = (hi - lo) (P(D=0 | Z=1) + P(D=1 | Z=0))`: the width is `hi - lo` times
the sum of the two noncompliance rates. This follows from the definitions alone. -/
theorem upperBound_sub_lowerBound (μ : Measure Ω) (lo hi : ℝ) (o : Ω → Bool × Bool × ℝ) :
    upperBound μ lo hi o - lowerBound μ lo hi o =
      (hi - lo) * (obsMean μ o untreatedInd true + obsMean μ o treatedInd false) := by
  rw [upperBound, lowerBound]; ring

end IVBounds

namespace IVModel

open IVBounds

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- An observed conditional mean of the model is the corresponding functional of its observed
data. -/
theorem condMean_eq_obsMean (h : Bool → ℝ → ℝ) (z : Bool) :
    M.condMean μ (fun ω ↦ h (M.Dobs ω) (M.Yobs ω)) z = obsMean μ M.observed h z := rfl

/-- Identification of `E[Y z 1 · 1{D z' = 1}]`: under exclusion and instrument independence,
`E[Y 1{D=1} | Z=z'] = ∫_{D z' = 1} Y z 1`, for any instrument value `z` used to index `Y`. -/
theorem obsMean_yTreated [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) {z' : Bool} (hz : μ (M.instrumentEq z') ≠ 0) {z : Bool}
    (hY : Integrable (M.Y z true) μ) :
    obsMean μ M.observed yTreated z' = ∫ ω in {ω | M.D z' ω = true}, M.Y z true ω ∂μ := by
  have hint : Integrable (fun ω ↦ yTreated (M.D z' ω) (M.Y z' (M.D z' ω) ω)) μ := by
    refine ((hY.congr (hE.ae_eq z z' true)).indicator (M.measurableSet_D_eq_true z')).congr
      (ae_of_all _ fun ω ↦ ?_)
    by_cases h : M.D z' ω = true <;> simp [Set.indicator, yTreated, h]
  rw [← condMean_eq_obsMean, M.condMean_obs hI hz _ measurable_yTreated hint,
    ← integral_indicator (M.measurableSet_D_eq_true z')]
  refine integral_congr_ae ?_
  filter_upwards [hE.ae_eq z' z true] with ω hω
  by_cases h : M.D z' ω = true <;> simp [Set.indicator, yTreated, h, hω]

/-- Identification of `E[Y z 0 · 1{D z' = 0}]`: under exclusion and instrument independence,
`E[Y 1{D=0} | Z=z'] = ∫_{D z' = 0} Y z 0`. -/
theorem obsMean_yUntreated [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) {z' : Bool} (hz : μ (M.instrumentEq z') ≠ 0) {z : Bool}
    (hY : Integrable (M.Y z false) μ) :
    obsMean μ M.observed yUntreated z' = ∫ ω in {ω | M.D z' ω = true}ᶜ, M.Y z false ω ∂μ := by
  have hint : Integrable (fun ω ↦ yUntreated (M.D z' ω) (M.Y z' (M.D z' ω) ω)) μ := by
    refine ((hY.congr (hE.ae_eq z z' false)).indicator
      (M.measurableSet_D_eq_true z').compl).congr (ae_of_all _ fun ω ↦ ?_)
    by_cases h : M.D z' ω = true <;> simp [Set.indicator, yUntreated, h]
  rw [← condMean_eq_obsMean, M.condMean_obs hI hz _ measurable_yUntreated hint,
    ← integral_indicator (M.measurableSet_D_eq_true z').compl]
  refine integral_congr_ae ?_
  filter_upwards [hE.ae_eq z' z false] with ω hω
  by_cases h : M.D z' ω = true <;> simp [Set.indicator, yUntreated, h, hω]

/-- Under instrument independence, `P(D = 1 | Z = z') = P(D z' = 1)`. -/
theorem obsMean_treatedInd [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ) {z' : Bool}
    (hz : μ (M.instrumentEq z') ≠ 0) :
    obsMean μ M.observed treatedInd z' = μ.real {ω | M.D z' ω = true} := by
  have hint : Integrable (fun ω ↦ treatedInd (M.D z' ω) (M.Y z' (M.D z' ω) ω)) μ :=
    (M.integrable_DReal z').congr (ae_of_all _ fun ω ↦ by
      by_cases h : M.D z' ω = true <;> simp [DReal, treatedInd, h])
  rw [← condMean_eq_obsMean, M.condMean_obs hI hz _ measurable_treatedInd hint,
    ← integral_indicator_one (M.measurableSet_D_eq_true z')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  by_cases h : M.D z' ω = true <;> simp [Set.indicator, treatedInd, h]

/-- Under instrument independence, `P(D = 0 | Z = z') = P(D z' = 0)`. -/
theorem obsMean_untreatedInd [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ) {z' : Bool}
    (hz : μ (M.instrumentEq z') ≠ 0) :
    obsMean μ M.observed untreatedInd z' = μ.real {ω | M.D z' ω = true}ᶜ := by
  have hint : Integrable (fun ω ↦ untreatedInd (M.D z' ω) (M.Y z' (M.D z' ω) ω)) μ :=
    ((integrable_const (1 : ℝ)).sub (M.integrable_DReal z')).congr (ae_of_all _ fun ω ↦ by
      by_cases h : M.D z' ω = true <;> simp [DReal, untreatedInd, h])
  rw [← condMean_eq_obsMean, M.condMean_obs hI hz _ measurable_untreatedInd hint,
    ← integral_indicator_one (M.measurableSet_D_eq_true z').compl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  by_cases h : M.D z' ω = true <;> simp [Set.indicator, untreatedInd, h]

/-! ### The bounds -/

/-- The IV bound inclusion for an arbitrary choice of arms: under the exclusion restriction,
instrument independence, `P(Z = z₁) ≠ 0`, `P(Z = z₀) ≠ 0` and potential outcomes in `[lo, hi]`,
`E[Y z 1 - Y z 0]` lies between
`E[Y 1{D=1} | Z=z₁] - E[Y 1{D=0} | Z=z₀] + lo P(D=0 | Z=z₁) - hi P(D=1 | Z=z₀)` and the same with
`lo` and `hi` exchanged. The arm `z₁` is used for the treated mean `E[Y 1]` and the arm `z₀` for
the untreated mean `E[Y 0]`. -/
theorem ate_mem_Icc_arms [IsFiniteMeasure μ] {lo hi : ℝ} (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) {z₁ z₀ : Bool} (h₁ : μ (M.instrumentEq z₁) ≠ 0)
    (h₀ : μ (M.instrumentEq z₀) ≠ 0) (hb : ∀ z d ω, M.Y z d ω ∈ Icc lo hi) (z : Bool) :
    M.ate μ z ∈ Icc
      (obsMean μ M.observed yTreated z₁ - obsMean μ M.observed yUntreated z₀ +
        lo * obsMean μ M.observed untreatedInd z₁ - hi * obsMean μ M.observed treatedInd z₀)
      (obsMean μ M.observed yTreated z₁ - obsMean μ M.observed yUntreated z₀ +
        hi * obsMean μ M.observed untreatedInd z₁ - lo * obsMean μ M.observed treatedInd z₀) := by
  have e1 := Manski.integral_mem_Icc_of_eqOn (μ := μ) (M.measurableSet_D_eq_true z₁)
    (M.measurable_Y z true) (hb z true) (y := M.Y z true) (fun _ _ ↦ rfl)
  have e0 := Manski.integral_mem_Icc_of_eqOn (μ := μ) (M.measurableSet_D_eq_true z₀).compl
    (M.measurable_Y z false) (hb z false) (y := M.Y z false) (fun _ _ ↦ rfl)
  rw [compl_compl] at e0
  simp only [ate, effect]
  rw [integral_sub (M.integrable_Y_of_bounded hb z true) (M.integrable_Y_of_bounded hb z false),
    M.obsMean_yTreated hE hI h₁ (M.integrable_Y_of_bounded hb z true),
    M.obsMean_yUntreated hE hI h₀ (M.integrable_Y_of_bounded hb z false),
    M.obsMean_untreatedInd hI h₁, M.obsMean_treatedInd hI h₀]
  constructor <;> linarith [e1.1, e1.2, e0.1, e0.2]

/-- **IV bounds on the average treatment effect** (Robins 1989; Manski 1990). Assume the exclusion
restriction, instrument independence, `P(Z = z) ≠ 0` for both instrument values, and potential
outcomes with values in `[lo, hi]`. Then for either instrument value `z` indexing the outcomes,
`E[Y z 1 - Y z 0]` lies between `lowerBound` and `upperBound`:
`E[Y 1{D=1} | Z=1] - E[Y 1{D=0} | Z=0] + lo P(D=0 | Z=1) - hi P(D=1 | Z=0)` and the same with
`lo` and `hi` exchanged. Both endpoints are functionals of the observed data.

The argument splits `E[Y 1]` over `{D 1 = 1}`, where it is identified from the arm `Z = 1`, and
its complement, where it is bounded by `lo` and `hi`, and splits `E[Y 0]` likewise using the arm
`Z = 0`. Monotonicity is not needed for the inclusion, and without it the interval is valid but
not claimed to be sharp; monotonicity enters the stratum interpretation
(`meanY1_eq`, `meanY0_eq`), the complier form of the width (`upperBound_sub_lowerBound`) and
sharpness within monotone models (`identifiedSet_ate`).

The hypotheses are stronger than the population-level conditions under which Hernan and Robins
(*Causal Inference: What If*) state the natural bounds: the exclusion restriction is imposed unit
by unit (almost surely), not only on the means `E[Y^{z,d}]`, and instrument independence is joint
independence of `Z` and all potential variables, not marginal exchangeability for each `(z, d)`.
-/
theorem ate_mem_Icc_bounds [IsFiniteMeasure μ] {lo hi : ℝ} (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (h₁ : μ (M.instrumentEq true) ≠ 0)
    (h₀ : μ (M.instrumentEq false) ≠ 0) (hb : ∀ z d ω, M.Y z d ω ∈ Icc lo hi) (z : Bool) :
    M.ate μ z ∈ Icc (lowerBound μ lo hi M.observed) (upperBound μ lo hi M.observed) :=
  M.ate_mem_Icc_arms hE hI h₁ h₀ hb z

/-- **IV bounds with the instrument arms swapped.** Under the same assumptions as
`ate_mem_Icc_bounds`, `E[Y z 1 - Y z 0]` lies between `lowerBoundSwap` and `upperBoundSwap`,
which use the arm `Z = 0` for the treated mean and the arm `Z = 1` for the untreated mean. -/
theorem ate_mem_Icc_boundsSwap [IsFiniteMeasure μ] {lo hi : ℝ} (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (h₁ : μ (M.instrumentEq true) ≠ 0)
    (h₀ : μ (M.instrumentEq false) ≠ 0) (hb : ∀ z d ω, M.Y z d ω ∈ Icc lo hi) (z : Bool) :
    M.ate μ z ∈ Icc (lowerBoundSwap μ lo hi M.observed) (upperBoundSwap μ lo hi M.observed) :=
  M.ate_mem_Icc_arms hE hI h₀ h₁ hb z

/-- **Intersection of the two arm orderings.** Under the assumptions of `ate_mem_Icc_bounds`,
the average treatment effect lies in the intersection of the two intervals,
`[max lowerBound lowerBoundSwap, min upperBound upperBoundSwap]`. No sharpness claim is made
for this intersection. -/
theorem ate_mem_Icc_bounds_inter [IsFiniteMeasure μ] {lo hi : ℝ} (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (h₁ : μ (M.instrumentEq true) ≠ 0)
    (h₀ : μ (M.instrumentEq false) ≠ 0) (hb : ∀ z d ω, M.Y z d ω ∈ Icc lo hi) (z : Bool) :
    M.ate μ z ∈ Icc (max (lowerBound μ lo hi M.observed) (lowerBoundSwap μ lo hi M.observed))
      (min (upperBound μ lo hi M.observed) (upperBoundSwap μ lo hi M.observed)) := by
  have h := M.ate_mem_Icc_bounds hE hI h₁ h₀ hb z
  have h' := M.ate_mem_Icc_boundsSwap hE hI h₁ h₀ hb z
  exact ⟨max_le h.1 h'.1, le_min h.2 h'.2⟩

/-- **Width of the IV bounds under monotonicity.** Under instrument independence, monotonicity
and `P(Z = z) ≠ 0` for both `z`, the IV bounds have width `(hi - lo) (1 - P(compliers))`. It is
the assumption-free width `IVBounds.upperBound_sub_lowerBound` rewritten with the identified
never-taker and always-taker shares. -/
theorem upperBound_sub_lowerBound [IsProbabilityMeasure μ] {lo hi : ℝ}
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) :
    upperBound μ lo hi M.observed - lowerBound μ lo hi M.observed =
      (hi - lo) * (1 - μ.real M.compliers) := by
  have hFS := M.firstStage_eq_measure_compliers hI hM h₁ h₀
  rw [firstStage, M.condMean_DobsReal hI h₁, M.condMean_DobsReal hI h₀, M.integral_DReal,
    M.integral_DReal] at hFS
  rw [IVBounds.upperBound_sub_lowerBound, M.obsMean_untreatedInd hI h₁,
    M.obsMean_treatedInd hI h₀, probReal_compl_eq_one_sub (M.measurableSet_D_eq_true true), ← hFS]
  ring

/-! ### Principal strata -/

/-- Stratum decomposition of the average treatment effect: under monotonicity and integrable
potential outcomes, `E[Y z 1 - Y z 0]` is the sum of the integrals of the unit-level effect over
the compliers, the always-takers and the never-takers. -/
theorem ate_eq_sum_strata (hM : M.Monotonicity μ) {z : Bool}
    (hY : ∀ d, Integrable (M.Y z d) μ) :
    M.ate μ z = ∫ ω in M.compliers, M.effect z ω ∂μ + ∫ ω in M.alwaysTakers, M.effect z ω ∂μ +
      ∫ ω in M.neverTakers, M.effect z ω ∂μ := by
  have hτ : Integrable (M.effect z) μ := (hY true).sub (hY false)
  have hpt : ∀ ω, M.effect z ω = M.compliers.indicator (M.effect z) ω +
      M.alwaysTakers.indicator (M.effect z) ω + M.neverTakers.indicator (M.effect z) ω +
      M.defiers.indicator (M.effect z) ω := by
    intro ω
    simp only [Set.indicator, mem_compliers, mem_alwaysTakers, mem_neverTakers, mem_defiers]
    cases M.D false ω <;> cases M.D true ω <;> simp
  have hC := M.measurableSet_compliers
  have hA : MeasurableSet M.alwaysTakers := M.measurableSet_stratum _
  have hN : MeasurableSet M.neverTakers := M.measurableSet_stratum _
  have hdef : ∫ ω, M.defiers.indicator (M.effect z) ω ∂μ = 0 := by
    rw [integral_indicator M.measurableSet_defiers,
      Measure.restrict_eq_zero.2 (M.measure_defiers_eq_zero hM), integral_zero_measure]
  rw [ate, integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add, integral_add,
    integral_add, hdef, add_zero, integral_indicator hC, integral_indicator hA,
    integral_indicator hN]
  all_goals first
    | exact hτ.indicator hC | exact hτ.indicator hA | exact hτ.indicator hN
    | exact hτ.indicator M.measurableSet_defiers
    | exact (hτ.indicator hC).add (hτ.indicator hA)
    | exact ((hτ.indicator hC).add (hτ.indicator hA)).add (hτ.indicator hN)

/-- The stratum decomposition in conditional form:
`ATE = P(C) CACE + P(AT) E[Y 1 - Y 0 | AT] + P(NT) E[Y 1 - Y 0 | NT]`, where each conditional
mean is an integral against the conditional measure. A stratum of probability zero contributes
zero, as it should; no division by its probability occurs. -/
theorem ate_eq_strata_cond [IsFiniteMeasure μ] (hM : M.Monotonicity μ) {z : Bool}
    (hY : ∀ d, Integrable (M.Y z d) μ) :
    M.ate μ z = μ.real M.compliers * M.complierEffect μ z +
      μ.real M.alwaysTakers * ∫ ω, M.effect z ω ∂μ[|M.alwaysTakers] +
      μ.real M.neverTakers * ∫ ω, M.effect z ω ∂μ[|M.neverTakers] := by
  rw [complierEffect, measureReal_mul_integral_cond, measureReal_mul_integral_cond,
    measureReal_mul_integral_cond]
  exact M.ate_eq_sum_strata hM hY

/-- The always-taker share is identified: `P(D = 1 | Z = 0) = P(AT)`. -/
theorem obsMean_treatedInd_false [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₀ : μ (M.instrumentEq false) ≠ 0) :
    obsMean μ M.observed treatedInd false = μ.real M.alwaysTakers := by
  rw [M.obsMean_treatedInd hI h₀, measureReal_congr (M.ae_eq_alwaysTakers hM)]

/-- The never-taker share is identified: `P(D = 0 | Z = 1) = P(NT)`. -/
theorem obsMean_untreatedInd_true [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₁ : μ (M.instrumentEq true) ≠ 0) :
    obsMean μ M.observed untreatedInd true = μ.real M.neverTakers := by
  rw [M.obsMean_untreatedInd hI h₁, measureReal_congr (M.ae_eq_neverTakers hM)]

/-- The treated outcome of the always-takers is identified:
`E[Y 1{D=1} | Z=0] = ∫_AT Y z 1`. Dividing by `P(D = 1 | Z = 0) = P(AT)`, when positive, gives
`E[Y 1 | AT]`. -/
theorem obsMean_yTreated_false [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₀ : μ (M.instrumentEq false) ≠ 0) {z : Bool} (hY : Integrable (M.Y z true) μ) :
    obsMean μ M.observed yTreated false = ∫ ω in M.alwaysTakers, M.Y z true ω ∂μ := by
  rw [M.obsMean_yTreated hE hI h₀ hY, setIntegral_congr_set (M.ae_eq_alwaysTakers hM)]

/-- The untreated outcome of the never-takers is identified:
`E[Y 1{D=0} | Z=1] = ∫_NT Y z 0`. -/
theorem obsMean_yUntreated_true [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) {z : Bool} (hY : Integrable (M.Y z false) μ) :
    obsMean μ M.observed yUntreated true = ∫ ω in M.neverTakers, M.Y z false ω ∂μ := by
  rw [M.obsMean_yUntreated hE hI h₁ hY, setIntegral_congr_set (M.ae_eq_neverTakers hM)]

/-- `E[Y z 1] = E[Y 1{D=1} | Z=1] + ∫_NT Y z 1`: the only unidentified part of the treated mean
is the treated outcome of the never-takers. -/
theorem meanY1_eq [IsFiniteMeasure μ] (hE : M.Exclusion μ) (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₁ : μ (M.instrumentEq true) ≠ 0) {z : Bool}
    (hY : Integrable (M.Y z true) μ) :
    ∫ ω, M.Y z true ω ∂μ =
      obsMean μ M.observed yTreated true + ∫ ω in M.neverTakers, M.Y z true ω ∂μ := by
  rw [← integral_add_compl (M.measurableSet_D_eq_true true) hY, M.obsMean_yTreated hE hI h₁ hY,
    setIntegral_congr_set (M.ae_eq_neverTakers hM)]

/-- `E[Y z 0] = E[Y 1{D=0} | Z=0] + ∫_AT Y z 0`: the only unidentified part of the untreated mean
is the untreated outcome of the always-takers. -/
theorem meanY0_eq [IsFiniteMeasure μ] (hE : M.Exclusion μ) (hI : M.InstrumentIndependence μ)
    (hM : M.Monotonicity μ) (h₀ : μ (M.instrumentEq false) ≠ 0) {z : Bool}
    (hY : Integrable (M.Y z false) μ) :
    ∫ ω, M.Y z false ω ∂μ =
      obsMean μ M.observed yUntreated false + ∫ ω in M.alwaysTakers, M.Y z false ω ∂μ := by
  rw [← integral_add_compl (M.measurableSet_D_eq_true false) hY, M.obsMean_yUntreated hE hI h₀ hY,
    setIntegral_congr_set (M.ae_eq_alwaysTakers hM), add_comm]


/-! ### Sharpness -/

/-- A set of potential-variable vectors defined by a condition on the pair of potential
treatments is measurable. -/
theorem measurableSet_treatmentPair (p : Bool × Bool → Prop) :
    MeasurableSet {w : Potentials | p (w.1 false, w.1 true)} :=
  ((measurable_fst_eval false).prodMk (measurable_fst_eval true))
    (Set.to_countable {q | p q}).measurableSet

/-- Refilling the unobserved potential outcomes: on the never-takers (`D 0 = D 1 = 0`) the
treated outcome is set to `c1`, on the always-takers (`D 0 = D 1 = 1`) the untreated outcome is
set to `c0`, for both instrument values; the potential treatments and all other potential
outcomes are unchanged. -/
def refillPot (c1 c0 : ℝ) (w : Potentials) : Potentials :=
  (w.1, fun z d ↦ if d then (if (!w.1 false && !w.1 true) = true then c1 else w.2 z true)
    else (if (w.1 false && w.1 true) = true then c0 else w.2 z false))

theorem measurable_refillPot (c1 c0 : ℝ) : Measurable (refillPot c1 c0) := by
  refine measurable_fst.prodMk (Measurable.of_eval fun z ↦ Measurable.of_eval fun d ↦ ?_)
  cases d
  · change Measurable fun w : Potentials ↦
      if (w.1 false && w.1 true) = true then c0 else w.2 z false
    exact Measurable.ite (measurableSet_treatmentPair fun q ↦ (q.1 && q.2) = true)
      measurable_const (measurable_snd_eval z false)
  · change Measurable fun w : Potentials ↦
      if (!w.1 false && !w.1 true) = true then c1 else w.2 z true
    exact Measurable.ite (measurableSet_treatmentPair fun q ↦ (!q.1 && !q.2) = true)
      measurable_const (measurable_snd_eval z true)

/-- The model `M` with its unobserved potential outcomes refilled by `refillPot c1 c0`: the
treated outcome of the never-takers becomes `c1` and the untreated outcome of the always-takers
becomes `c0`. -/
def refill (c1 c0 : ℝ) : IVModel Ω where
  Z := M.Z
  D := M.D
  Y z d ω := (refillPot c1 c0 (M.potentials ω)).2 z d
  measurable_Z := M.measurable_Z
  measurable_D := M.measurable_D
  measurable_Y z d :=
    (measurable_snd_eval z d).comp ((measurable_refillPot c1 c0).comp M.measurable_potentials)

/-- Refilling never changes the observed data: the refilled outcomes are never observed. -/
theorem observed_refill (c1 c0 : ℝ) : (M.refill c1 c0).observed = M.observed := by
  funext ω
  simp only [observed, Yobs, Dobs, refill, refillPot, potentials]
  rcases Bool.eq_false_or_eq_true (M.D false ω) with h0 | h0 <;>
    rcases Bool.eq_false_or_eq_true (M.D true ω) with h1 | h1 <;>
    cases M.Z ω <;> simp [h0, h1]

theorem refill_exclusion (hE : M.Exclusion μ) (c1 c0 : ℝ) : (M.refill c1 c0).Exclusion μ := by
  intro d
  filter_upwards [hE true, hE false] with ω h1 h0
  cases d <;> simp [refill, refillPot, potentials, h1, h0]

theorem refill_independence (hI : M.InstrumentIndependence μ) (c1 c0 : ℝ) :
    (M.refill c1 c0).InstrumentIndependence μ :=
  hI.comp measurable_id (measurable_refillPot c1 c0)

/-- Refilling leaves the instrument and the potential treatments unchanged, so the first stage
and hence relevance are unchanged. -/
theorem refill_relevance_iff (c1 c0 : ℝ) : (M.refill c1 c0).Relevance μ ↔ M.Relevance μ :=
  Iff.rfl

theorem refill_bounded {lo hi : ℝ} (hb : ∀ z d ω, M.Y z d ω ∈ Icc lo hi) {c1 c0 : ℝ}
    (hc1 : c1 ∈ Icc lo hi) (hc0 : c0 ∈ Icc lo hi) :
    ∀ z d ω, (M.refill c1 c0).Y z d ω ∈ Icc lo hi := by
  intro z d ω
  cases d
  · by_cases h : (M.D false ω && M.D true ω) = true <;>
      simp only [refill, refillPot, potentials, h] <;> first | exact hc0 | exact hb _ _ _
  · by_cases h : (!M.D false ω && !M.D true ω) = true <;>
      simp only [refill, refillPot, potentials, h] <;> first | exact hc1 | exact hb _ _ _

/-- The average treatment effect of the refilled model:
`E[Y 1{D=1} | Z=1] - E[Y 1{D=0} | Z=0] + c1 P(D=0 | Z=1) - c0 P(D=1 | Z=0)`. -/
theorem ate_refill [IsFiniteMeasure μ] {lo hi : ℝ} (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0)
    (hb : ∀ z d ω, M.Y z d ω ∈ Icc lo hi) {c1 c0 : ℝ} (hc1 : c1 ∈ Icc lo hi)
    (hc0 : c0 ∈ Icc lo hi) (z : Bool) :
    (M.refill c1 c0).ate μ z = obsMean μ M.observed yTreated true -
      obsMean μ M.observed yUntreated false + c1 * obsMean μ M.observed untreatedInd true -
      c0 * obsMean μ M.observed treatedInd false := by
  set M' := M.refill c1 c0 with hM'
  have hb' := M.refill_bounded hb hc1 hc0
  have hE' := M.refill_exclusion hE c1 c0
  have hI' := M.refill_independence hI c1 c0
  have e1 := M'.meanY1_eq hE' hI' hM h₁ (M'.integrable_Y_of_bounded hb' z true)
  have e0 := M'.meanY0_eq hE' hI' hM h₀ (M'.integrable_Y_of_bounded hb' z false)
  have hN : MeasurableSet M.neverTakers := M.measurableSet_stratum _
  have hA : MeasurableSet M.alwaysTakers := M.measurableSet_stratum _
  have n1 : ∫ ω in M'.neverTakers, M'.Y z true ω ∂μ = c1 * μ.real M.neverTakers := by
    rw [show M'.neverTakers = M.neverTakers from rfl,
      setIntegral_congr_fun hN (g := fun _ ↦ c1) fun ω hω ↦ by
        have h := mem_neverTakers.1 hω
        simp [M', refill, refillPot, potentials, h.1, h.2],
      setIntegral_const, smul_eq_mul, mul_comm]
  have a0 : ∫ ω in M'.alwaysTakers, M'.Y z false ω ∂μ = c0 * μ.real M.alwaysTakers := by
    rw [show M'.alwaysTakers = M.alwaysTakers from rfl,
      setIntegral_congr_fun hA (g := fun _ ↦ c0) fun ω hω ↦ by
        have h := mem_alwaysTakers.1 hω
        simp [M', refill, refillPot, potentials, h.1, h.2],
      setIntegral_const, smul_eq_mul, mul_comm]
  simp only [ate, effect]
  rw [integral_sub (M'.integrable_Y_of_bounded hb' z true) (M'.integrable_Y_of_bounded hb' z false),
    e1, e0, n1, a0, M.observed_refill, M.obsMean_untreatedInd_true hI hM h₁,
    M.obsMean_treatedInd_false hI hM h₀]
  ring

end IVModel

namespace IVBounds

open IVModel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The maintained assumptions for the IV bounds, as a class of models on the fixed `(Ω, μ)`:
the exclusion restriction, instrument independence, monotonicity, `P(Z = z) ≠ 0` for both
instrument values, and potential outcomes with values in `[lo, hi]`. -/
def models (μ : Measure Ω) (lo hi : ℝ) : Set (IVModel Ω) :=
  {M | M.Exclusion μ ∧ M.InstrumentIndependence μ ∧ M.Monotonicity μ ∧
    μ (M.instrumentEq true) ≠ 0 ∧ μ (M.instrumentEq false) ≠ 0 ∧ ∀ z d ω, M.Y z d ω ∈ Icc lo hi}

variable {μ : Measure Ω} {lo hi : ℝ}

theorem refill_mem_models {M : IVModel Ω} (hM : M ∈ models μ lo hi) {c1 c0 : ℝ}
    (hc1 : c1 ∈ Icc lo hi) (hc0 : c0 ∈ Icc lo hi) : M.refill c1 c0 ∈ models μ lo hi :=
  ⟨M.refill_exclusion hM.1 c1 c0, M.refill_independence hM.2.1 c1 c0, hM.2.2.1, hM.2.2.2.1,
    hM.2.2.2.2.1, M.refill_bounded hM.2.2.2.2.2 hc1 hc0⟩

/-- **Sharpness of the IV bounds** (the identified set). Under exclusion, instrument
independence, monotonicity, positive instrument probabilities and outcomes in `[lo, hi]`, the
identified set of the average treatment effect at the observed data of any model `M` of the
class is exactly `[lowerBound, upperBound]`. Each value is attained by refilling the treated
outcome of the never-takers and the untreated outcome of the always-takers with constants
(`IVModel.refill`).

The observation is the realized observed-data map `ω ↦ (Z ω, Dobs ω, Yobs ω)` on the fixed
probability space `(Ω, μ)`; models differ in their potential outcomes. This observation is finer
than the observed-data law, so the sharpness statement is at least as strong as sharpness for
the law (models with equal observation maps have equal laws). -/
theorem identifiedSet_ate [IsFiniteMeasure μ] {M : IVModel Ω} (hM : M ∈ models μ lo hi)
    (z : Bool) :
    identifiedSet (models μ lo hi) IVModel.observed (fun M' ↦ M'.ate μ z) M.observed =
      Icc (lowerBound μ lo hi M.observed) (upperBound μ lo hi M.observed) := by
  ext t
  constructor
  · rintro ⟨M', ⟨hM', hobs⟩, rfl⟩
    rw [← hobs]
    exact M'.ate_mem_Icc_bounds hM'.1 hM'.2.1 hM'.2.2.2.1 hM'.2.2.2.2.1 hM'.2.2.2.2.2 z
  · intro ht
    obtain ⟨ω, -⟩ := nonempty_of_measure_ne_zero hM.2.2.2.1
    have hlh : lo ≤ hi := (hM.2.2.2.2.2 true true ω).1.trans (hM.2.2.2.2.2 true true ω).2
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := Manski.exists_combo_of_mem_Icc ht
    have hc1 := Manski.combo_mem_Icc ha hb hab hlh
    have hc0 := Manski.combo_mem_Icc hb ha (by rw [add_comm, hab]) hlh
    refine mem_identifiedSet.2 ⟨M.refill (a * lo + b * hi) (b * lo + a * hi),
      refill_mem_models hM hc1 hc0, M.observed_refill _ _, ?_⟩
    rw [M.ate_refill hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2 hc1 hc0,
      lowerBound, upperBound]
    linear_combination (obsMean μ M.observed yTreated true -
      obsMean μ M.observed yUntreated false) * hab.symm

/-- The lower IV bound is attained: some model of the class with the same observed data (hence
the same observed-data law) has average treatment effect equal to `lowerBound`. -/
theorem exists_model_ate_eq_lowerBound [IsFiniteMeasure μ] {M : IVModel Ω}
    (hM : M ∈ models μ lo hi) (z : Bool) :
    ∃ M' ∈ models μ lo hi, M'.observed = M.observed ∧
      μ.map M'.observed = μ.map M.observed ∧ M'.ate μ z = lowerBound μ lo hi M.observed := by
  obtain ⟨ω, -⟩ := nonempty_of_measure_ne_zero hM.2.2.2.1
  have hlh : lo ∈ Icc lo hi ∧ hi ∈ Icc lo hi :=
    ⟨⟨le_rfl, (hM.2.2.2.2.2 true true ω).1.trans (hM.2.2.2.2.2 true true ω).2⟩,
      ⟨(hM.2.2.2.2.2 true true ω).1.trans (hM.2.2.2.2.2 true true ω).2, le_rfl⟩⟩
  refine ⟨M.refill lo hi, refill_mem_models hM hlh.1 hlh.2, M.observed_refill _ _,
    by rw [M.observed_refill], ?_⟩
  rw [M.ate_refill hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2 hlh.1 hlh.2,
    lowerBound]

/-- The upper IV bound is attained: some model of the class with the same observed data (hence
the same observed-data law) has average treatment effect equal to `upperBound`. -/
theorem exists_model_ate_eq_upperBound [IsFiniteMeasure μ] {M : IVModel Ω}
    (hM : M ∈ models μ lo hi) (z : Bool) :
    ∃ M' ∈ models μ lo hi, M'.observed = M.observed ∧
      μ.map M'.observed = μ.map M.observed ∧ M'.ate μ z = upperBound μ lo hi M.observed := by
  obtain ⟨ω, -⟩ := nonempty_of_measure_ne_zero hM.2.2.2.1
  have hlh : lo ∈ Icc lo hi ∧ hi ∈ Icc lo hi :=
    ⟨⟨le_rfl, (hM.2.2.2.2.2 true true ω).1.trans (hM.2.2.2.2.2 true true ω).2⟩,
      ⟨(hM.2.2.2.2.2 true true ω).1.trans (hM.2.2.2.2.2 true true ω).2, le_rfl⟩⟩
  refine ⟨M.refill hi lo, refill_mem_models hM hlh.2 hlh.1, M.observed_refill _ _,
    by rw [M.observed_refill], ?_⟩
  rw [M.ate_refill hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2.1 hM.2.2.2.2.2 hlh.2 hlh.1,
    upperBound]

end IVBounds

/-! ### Bounds under mean independence (Manski 1990) -/

namespace MeanIndependence

open Manski

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Mean independence of the potential outcomes from a binary instrument `Zi`:
`E[Y1 | Zi = z] = E[Y1]` and `E[Y0 | Zi = z] = E[Y0]` for both instrument values, the
conditional means being integrals against `μ[|Zi = z]`. The condition is imposed only for
instrument values of positive probability, since conditioning on a null event is meaningless;
the theorems below assume both values have positive probability. -/
def MeanIndependent (μ : Measure Ω) (Zi : Ω → Bool) (m : POModel Ω) : Prop :=
  ∀ z, μ (Zi ⁻¹' {z}) ≠ 0 →
    meanY1 (μ[|Zi ⁻¹' {z}]) m = meanY1 μ m ∧ meanY0 (μ[|Zi ⁻¹' {z}]) m = meanY0 μ m

/-- A finite mean is the weighted average of the two conditional means given `s` and `sᶜ`:
`∫ g = μ(s) E[g | s] + μ(sᶜ) E[g | sᶜ]`. -/
theorem integral_eq_cond_add_cond [IsFiniteMeasure μ] {s : Set Ω} (hs : MeasurableSet s)
    {g : Ω → ℝ} (hg : Integrable g μ) :
    μ.real s * ∫ ω, g ω ∂μ[|s] + μ.real sᶜ * ∫ ω, g ω ∂μ[|sᶜ] = ∫ ω, g ω ∂μ := by
  rw [measureReal_mul_integral_cond, measureReal_mul_integral_cond, integral_add_compl hs hg]

theorem boundY1_eq_integral {ν : Measure Ω} [IsFiniteMeasure ν] {A : Ω → Bool}
    (hA : Measurable A) (c : ℝ) (y : Ω → ℝ) : boundY1 ν A c y = ∫ ω, (treated A).indicator y ω ∂ν +
      c * ∫ ω, (treated A)ᶜ.indicator 1 ω ∂ν := by
  rw [boundY1, integral_indicator (measurableSet_treated hA),
    integral_indicator_one (μ := ν) (measurableSet_treated hA).compl]

theorem boundY0_eq_integral {ν : Measure Ω} [IsFiniteMeasure ν] {A : Ω → Bool}
    (hA : Measurable A) (c : ℝ) (y : Ω → ℝ) : boundY0 ν A c y = ∫ ω, (treated A)ᶜ.indicator y ω ∂ν +
      c * ∫ ω, (treated A).indicator 1 ω ∂ν := by
  rw [boundY0, integral_indicator (measurableSet_treated hA).compl,
    integral_indicator_one (μ := ν) (measurableSet_treated hA)]

/-- The no-assumption Manski bound for `E[Y1]` is the `P(s)`-weighted average of the Manski
bounds computed within `s` and within `sᶜ`. -/
theorem boundY1_eq_weighted [IsFiniteMeasure μ] {A : Ω → Bool} (hA : Measurable A) {s : Set Ω}
    (hs : MeasurableSet s) (c : ℝ) {y : Ω → ℝ} (hy : Integrable y μ) :
    boundY1 μ A c y = μ.real s * boundY1 (μ[|s]) A c y + μ.real sᶜ * boundY1 (μ[|sᶜ]) A c y := by
  have hT := measurableSet_treated hA
  have e1 := integral_eq_cond_add_cond hs (hy.indicator hT)
  have e2 := integral_eq_cond_add_cond (g := (treated A)ᶜ.indicator 1) hs
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hT.compl)
  rw [boundY1_eq_integral hA, boundY1_eq_integral hA, boundY1_eq_integral hA, ← e1, ← e2]
  ring

/-- The no-assumption Manski bound for `E[Y0]` is the `P(s)`-weighted average of the Manski
bounds computed within `s` and within `sᶜ`. -/
theorem boundY0_eq_weighted [IsFiniteMeasure μ] {A : Ω → Bool} (hA : Measurable A) {s : Set Ω}
    (hs : MeasurableSet s) (c : ℝ) {y : Ω → ℝ} (hy : Integrable y μ) :
    boundY0 μ A c y = μ.real s * boundY0 (μ[|s]) A c y + μ.real sᶜ * boundY0 (μ[|sᶜ]) A c y := by
  have hT := measurableSet_treated hA
  have e1 := integral_eq_cond_add_cond hs (hy.indicator hT.compl)
  have e2 := integral_eq_cond_add_cond (g := (treated A).indicator 1) hs
    ((integrable_const (μ := μ) (1 : ℝ)).indicator hT)
  rw [boundY0_eq_integral hA, boundY0_eq_integral hA, boundY0_eq_integral hA, ← e1, ← e2]
  ring

/-- Convex combinations lie between the minimum and the maximum: if `p, q ≥ 0` and
`p + q = 1`, then `[max a b, min c d] ⊆ [p a + q b, p c + q d]`. -/
theorem Icc_max_min_subset {p q a b c d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    Icc (max a b) (min c d) ⊆ Icc (p * a + q * b) (p * c + q * d) := by
  rintro t ⟨h1, h2⟩
  have i1 := mul_le_mul_of_nonneg_left (le_max_left a b) hp
  have i2 := mul_le_mul_of_nonneg_left (le_max_right a b) hq
  have i3 := mul_le_mul_of_nonneg_left (min_le_left c d) hp
  have i4 := mul_le_mul_of_nonneg_left (min_le_right c d) hq
  have e1 : p * max a b + q * max a b = max a b := by rw [← add_mul, hpq, one_mul]
  have e2 : p * min c d + q * min c d = min c d := by rw [← add_mul, hpq, one_mul]
  constructor <;> linarith

omit [MeasurableSpace Ω] in
theorem preimage_false_eq_compl (Zi : Ω → Bool) : Zi ⁻¹' {false} = (Zi ⁻¹' {true})ᶜ := by
  ext ω; simp

variable {A Zi : Ω → Bool} {lo hi : ℝ} {m : POModel Ω}

/-- **Mean-independence bounds on `E[Y1]`** (Manski 1990). If the potential outcomes are mean
independent of the instrument `Zi`, both instrument values have positive probability, and the
potential outcomes are bounded in `[lo, hi]`, then `E[Y1]` lies in the intersection over `z` of
the worst-case bounds computed within `{Zi = z}`: between `max_z` of the conditional lower
bounds and `min_z` of the conditional upper bounds. -/
theorem meanY1_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) (hm : m ∈ boundedModels lo hi)
    (hMI : MeanIndependent μ Zi m) (hz : ∀ z, μ (Zi ⁻¹' {z}) ≠ 0) :
    meanY1 μ m ∈ Icc
      (max (boundY1 (μ[|Zi ⁻¹' {true}]) A lo (observed A m))
        (boundY1 (μ[|Zi ⁻¹' {false}]) A lo (observed A m)))
      (min (boundY1 (μ[|Zi ⁻¹' {true}]) A hi (observed A m))
        (boundY1 (μ[|Zi ⁻¹' {false}]) A hi (observed A m))) := by
  have h1 := Manski.meanY1_mem_Icc (μ := μ[|Zi ⁻¹' {true}]) hA hm
  have h0 := Manski.meanY1_mem_Icc (μ := μ[|Zi ⁻¹' {false}]) hA hm
  rw [(hMI true (hz true)).1] at h1
  rw [(hMI false (hz false)).1] at h0
  exact ⟨max_le h1.1 h0.1, le_min h1.2 h0.2⟩

/-- **Mean-independence bounds on `E[Y0]`** (Manski 1990): the intersection over `z` of the
worst-case bounds for `E[Y0]` computed within `{Zi = z}`. -/
theorem meanY0_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) (hm : m ∈ boundedModels lo hi)
    (hMI : MeanIndependent μ Zi m) (hz : ∀ z, μ (Zi ⁻¹' {z}) ≠ 0) :
    meanY0 μ m ∈ Icc
      (max (boundY0 (μ[|Zi ⁻¹' {true}]) A lo (observed A m))
        (boundY0 (μ[|Zi ⁻¹' {false}]) A lo (observed A m)))
      (min (boundY0 (μ[|Zi ⁻¹' {true}]) A hi (observed A m))
        (boundY0 (μ[|Zi ⁻¹' {false}]) A hi (observed A m))) := by
  have h1 := Manski.meanY0_mem_Icc (μ := μ[|Zi ⁻¹' {true}]) hA hm
  have h0 := Manski.meanY0_mem_Icc (μ := μ[|Zi ⁻¹' {false}]) hA hm
  rw [(hMI true (hz true)).2] at h1
  rw [(hMI false (hz false)).2] at h0
  exact ⟨max_le h1.1 h0.1, le_min h1.2 h0.2⟩

/-- **Mean-independence bounds on the average treatment effect**: combining the bounds on
`E[Y1]` and `E[Y0]`, `max_z L1_z - min_z U0_z ≤ E[Y1] - E[Y0] ≤ min_z U1_z - max_z L0_z`. -/
theorem ate_mem_Icc [IsFiniteMeasure μ] (hA : Measurable A) (hm : m ∈ boundedModels lo hi)
    (hMI : MeanIndependent μ Zi m) (hz : ∀ z, μ (Zi ⁻¹' {z}) ≠ 0) :
    ate μ m ∈ Icc
      (max (boundY1 (μ[|Zi ⁻¹' {true}]) A lo (observed A m))
          (boundY1 (μ[|Zi ⁻¹' {false}]) A lo (observed A m)) -
        min (boundY0 (μ[|Zi ⁻¹' {true}]) A hi (observed A m))
          (boundY0 (μ[|Zi ⁻¹' {false}]) A hi (observed A m)))
      (min (boundY1 (μ[|Zi ⁻¹' {true}]) A hi (observed A m))
          (boundY1 (μ[|Zi ⁻¹' {false}]) A hi (observed A m)) -
        max (boundY0 (μ[|Zi ⁻¹' {true}]) A lo (observed A m))
          (boundY0 (μ[|Zi ⁻¹' {false}]) A lo (observed A m))) := by
  have h1 := meanY1_mem_Icc hA hm hMI hz
  have h0 := meanY0_mem_Icc hA hm hMI hz
  exact ⟨by unfold ate; linarith [h1.1, h0.2], by unfold ate; linarith [h1.2, h0.1]⟩

/-- The mean-independence bounds on `E[Y1]` are at least as tight as the no-assumption Manski
bounds: for a probability measure and a measurable binary `Zi`, the interval
`[max_z L_z, min_z U_z]` is contained in `[L, U]`, because `L` and `U` are the
`P(Zi = z)`-weighted averages of `L_z` and `U_z`. -/
theorem Icc_meanY1_subset [IsProbabilityMeasure μ] (hA : Measurable A) (hZ : Measurable Zi)
    {y : Ω → ℝ} (hy : Integrable y μ) :
    Icc (max (boundY1 (μ[|Zi ⁻¹' {true}]) A lo y) (boundY1 (μ[|Zi ⁻¹' {false}]) A lo y))
        (min (boundY1 (μ[|Zi ⁻¹' {true}]) A hi y) (boundY1 (μ[|Zi ⁻¹' {false}]) A hi y)) ⊆
      Icc (boundY1 μ A lo y) (boundY1 μ A hi y) := by
  have hs : MeasurableSet (Zi ⁻¹' {true}) := hZ (measurableSet_singleton true)
  rw [boundY1_eq_weighted hA hs lo hy, boundY1_eq_weighted hA hs hi hy,
    preimage_false_eq_compl]
  exact Icc_max_min_subset measureReal_nonneg measureReal_nonneg
    (by rw [probReal_compl_eq_one_sub hs]; ring)

/-- The mean-independence bounds on `E[Y0]` are at least as tight as the no-assumption Manski
bounds. -/
theorem Icc_meanY0_subset [IsProbabilityMeasure μ] (hA : Measurable A) (hZ : Measurable Zi)
    {y : Ω → ℝ} (hy : Integrable y μ) :
    Icc (max (boundY0 (μ[|Zi ⁻¹' {true}]) A lo y) (boundY0 (μ[|Zi ⁻¹' {false}]) A lo y))
        (min (boundY0 (μ[|Zi ⁻¹' {true}]) A hi y) (boundY0 (μ[|Zi ⁻¹' {false}]) A hi y)) ⊆
      Icc (boundY0 μ A lo y) (boundY0 μ A hi y) := by
  have hs : MeasurableSet (Zi ⁻¹' {true}) := hZ (measurableSet_singleton true)
  rw [boundY0_eq_weighted hA hs lo hy, boundY0_eq_weighted hA hs hi hy,
    preimage_false_eq_compl]
  exact Icc_max_min_subset measureReal_nonneg measureReal_nonneg
    (by rw [probReal_compl_eq_one_sub hs]; ring)

end MeanIndependence

/-! ### Testable implications -/

/-- Conditioning commutes with pushforward: `(f_* μ)[T | S] = μ[f⁻¹ T | f⁻¹ S]`. -/
theorem map_cond_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {f : α → β} (hf : Measurable f) {S T : Set β} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (μ.map f)[T | S] = μ[f ⁻¹' T | f ⁻¹' S] := by
  rw [cond_apply hS, cond_apply (hf hS), Measure.map_apply hf hS,
    Measure.map_apply hf (hS.inter hT), preimage_inter]

namespace IVBounds

/-- The observed event `{D = d, Y ∈ B}` in the space `Bool × Bool × ℝ` of observed data
`(Z, D, Y)`. -/
def obsEvent (d : Bool) (B : Set ℝ) : Set (Bool × Bool × ℝ) := {x | x.2.1 = d ∧ x.2.2 ∈ B}

theorem measurableSet_obsEvent (d : Bool) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet (obsEvent d B) :=
  ((measurable_fst.comp measurable_snd) (measurableSet_singleton d)).inter
    ((measurable_snd.comp measurable_snd) hB)

end IVBounds

namespace IVModel

open IVBounds

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- Under instrument independence and `P(Z = z) ≠ 0`,
`P(D = d, Y ∈ B | Z = z) = P(D z = d, Y z d ∈ B)` for every measurable `B`. -/
theorem cond_obs_event [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ) {z : Bool}
    (hz : μ (M.instrumentEq z) ≠ 0) (d : Bool) {B : Set ℝ} (hB : MeasurableSet B) :
    μ[{ω | M.Dobs ω = d ∧ M.Yobs ω ∈ B} | M.instrumentEq z] =
      μ {ω | M.D z ω = d ∧ M.Y z d ω ∈ B} := by
  have hT : MeasurableSet {w : Potentials | w.1 z = d ∧ w.2 z d ∈ B} :=
    ((measurable_fst_eval z) (measurableSet_singleton d)).inter ((measurable_snd_eval z d) hB)
  have hset : M.instrumentEq z ∩ {ω | M.Dobs ω = d ∧ M.Yobs ω ∈ B} =
      M.Z ⁻¹' {z} ∩ M.potentials ⁻¹' {w | w.1 z = d ∧ w.2 z d ∈ B} := by
    ext ω
    simp only [instrumentEq, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq,
      potentials, Dobs, Yobs]
    constructor
    · rintro ⟨h0, h1, h2⟩
      subst h0
      rw [h1] at h2
      exact ⟨rfl, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      subst h0
      exact ⟨rfl, h1, by rw [h1]; exact h2⟩
  rw [cond_apply (M.measurableSet_instrumentEq z), hset,
    indepFun_iff_measure_inter_preimage_eq_mul.1 hI _ _ (measurableSet_singleton z) hT,
    ← mul_assoc, ← instrumentEq, ENNReal.inv_mul_cancel hz (measure_ne_top _ _), one_mul]
  rfl

/-- **Instrumental inequality for the treated** (Balke and Pearl 1997, in the form implied by
monotonicity). Under exclusion, instrument independence, monotonicity and `P(Z = z) ≠ 0` for both
`z`, for every measurable outcome set `B`:
`P(Y ∈ B, D = 1 | Z = 0) ≤ P(Y ∈ B, D = 1 | Z = 1)`. The difference is the probability that a
complier has treated outcome in `B`. For a binary outcome take `B = {y}`. -/
theorem instrumentalInequality_treated [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) {B : Set ℝ}
    (hB : MeasurableSet B) :
    μ[{ω | M.Dobs ω = true ∧ M.Yobs ω ∈ B} | M.instrumentEq false] ≤
      μ[{ω | M.Dobs ω = true ∧ M.Yobs ω ∈ B} | M.instrumentEq true] := by
  rw [M.cond_obs_event hI h₀ true hB, M.cond_obs_event hI h₁ true hB]
  refine measure_mono_ae ?_
  filter_upwards [hM, hE true] with ω hm he
  rintro ⟨h1, h2⟩
  refine ⟨?_, by rw [mem_ofPred_eq, he]; exact h2⟩
  rw [h1] at hm
  cases h : M.D true ω
  · rw [h] at hm; exact absurd hm (by decide)
  · rfl

/-- **Instrumental inequality for the untreated.** Under the same assumptions, for every
measurable outcome set `B`: `P(Y ∈ B, D = 0 | Z = 1) ≤ P(Y ∈ B, D = 0 | Z = 0)`. The difference
is the probability that a complier has untreated outcome in `B`. -/
theorem instrumentalInequality_untreated [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) {B : Set ℝ}
    (hB : MeasurableSet B) :
    μ[{ω | M.Dobs ω = false ∧ M.Yobs ω ∈ B} | M.instrumentEq true] ≤
      μ[{ω | M.Dobs ω = false ∧ M.Yobs ω ∈ B} | M.instrumentEq false] := by
  rw [M.cond_obs_event hI h₀ false hB, M.cond_obs_event hI h₁ false hB]
  refine measure_mono_ae ?_
  filter_upwards [hM, hE false] with ω hm he
  rintro ⟨h1, h2⟩
  refine ⟨?_, by rw [mem_ofPred_eq, ← he]; exact h2⟩
  rw [h1] at hm
  cases h : M.D false ω
  · rfl
  · rw [h] at hm; exact absurd hm (by decide)

/-- The instrumental inequality for the treated, stated for the observed-data law
`ν = μ.map (Z, Dobs, Yobs)`: `ν(D = 1, Y ∈ B | Z = 0) ≤ ν(D = 1, Y ∈ B | Z = 1)`. -/
theorem law_instrumentalInequality_treated [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) {B : Set ℝ}
    (hB : MeasurableSet B) :
    (μ.map M.observed)[obsEvent true B | Prod.fst ⁻¹' {false}] ≤
      (μ.map M.observed)[obsEvent true B | Prod.fst ⁻¹' {true}] := by
  rw [map_cond_apply M.measurable_observed (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent true hB),
    map_cond_apply M.measurable_observed (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent true hB)]
  exact M.instrumentalInequality_treated hE hI hM h₁ h₀ hB

/-- The instrumental inequality for the untreated, stated for the observed-data law:
`ν(D = 0, Y ∈ B | Z = 1) ≤ ν(D = 0, Y ∈ B | Z = 0)`. -/
theorem law_instrumentalInequality_untreated [IsFiniteMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hM : M.Monotonicity μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0) {B : Set ℝ}
    (hB : MeasurableSet B) :
    (μ.map M.observed)[obsEvent false B | Prod.fst ⁻¹' {true}] ≤
      (μ.map M.observed)[obsEvent false B | Prod.fst ⁻¹' {false}] := by
  rw [map_cond_apply M.measurable_observed (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent false hB),
    map_cond_apply M.measurable_observed (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent false hB)]
  exact M.instrumentalInequality_untreated hE hI hM h₁ h₀ hB

end IVModel

namespace IVBounds

open IVCounterexample

/-- A binary IV model on `Bool × Fin 3` used to produce a violating observed-data law: a fair coin
`Z` is drawn independently of a unit uniform on `{0, 1, 2}`; units `0` and `1` take the
treatment exactly when `Z = 1`, unit `2` exactly when `Z = 0`; the outcome is binary, equal to
`1` only for unit `2` when treated. -/
def binaryModel : IVModel (Space 3) where
  Z := Prod.fst
  D z ω := if ω.2 = 2 then !z else z
  Y _ d ω := if d then (if ω.2 = 2 then 1 else 0) else 0
  measurable_Z := measurable_fst
  measurable_D _ := measurable_of_countable _
  measurable_Y _ _ := measurable_of_countable _

theorem binaryModel_independence : binaryModel.InstrumentIndependence (P 3) :=
  indepFun_fst fun u ↦ binaryModel.potentials (true, u)

theorem binaryModel_instrument_ne_zero (z : Bool) : P 3 (binaryModel.instrumentEq z) ≠ 0 := by
  rw [measure_instrumentEq_fst binaryModel rfl]; simp

/-- A concrete observed-data law on `Bool × Bool × ℝ` with a binary outcome: the law of
`(Z, Dobs, Yobs)` in `binaryModel`. -/
noncomputable def violatingLaw : Measure (Bool × Bool × ℝ) := (P 3).map binaryModel.observed

/-- The law `violatingLaw` violates the instrumental inequality for the treated with
`B = {1}`: `P(D = 1, Y = 1 | Z = 1) = 0 < P(D = 1, Y = 1 | Z = 0)`. -/
theorem violatingLaw_lt :
    violatingLaw[obsEvent true {1} | Prod.fst ⁻¹' {true}] <
      violatingLaw[obsEvent true {1} | Prod.fst ⁻¹' {false}] := by
  rw [violatingLaw, map_cond_apply binaryModel.measurable_observed
      (measurable_fst (measurableSet_singleton _)) (measurableSet_obsEvent true
        (measurableSet_singleton 1)),
    map_cond_apply binaryModel.measurable_observed
      (measurable_fst (measurableSet_singleton _)) (measurableSet_obsEvent true
        (measurableSet_singleton 1))]
  change (P 3)[|binaryModel.instrumentEq true]
      {ω | binaryModel.Dobs ω = true ∧ binaryModel.Yobs ω ∈ ({1} : Set ℝ)} <
    (P 3)[|binaryModel.instrumentEq false]
      {ω | binaryModel.Dobs ω = true ∧ binaryModel.Yobs ω ∈ ({1} : Set ℝ)}
  rw [binaryModel.cond_obs_event binaryModel_independence (binaryModel_instrument_ne_zero true)
      true (measurableSet_singleton 1),
    binaryModel.cond_obs_event binaryModel_independence (binaryModel_instrument_ne_zero false)
      true (measurableSet_singleton 1)]
  have hempty : {ω : Space 3 | binaryModel.D true ω = true ∧
      binaryModel.Y true true ω ∈ ({1} : Set ℝ)} = ∅ := by
    ext ⟨b, u⟩
    fin_cases u <;> simp [binaryModel]
  rw [hempty, measure_empty, pos_iff_ne_zero]
  exact fun h ↦ measure_singleton_ne_zero ((true, 2) : Space 3)
    (measure_mono_null (by simp [binaryModel]) h)

/-- **The IV assumptions are falsifiable.** No binary IV model, on any probability space, whose
observed-data law is `violatingLaw` satisfies the exclusion restriction, instrument independence
and monotonicity. (Both instrument values have probability `1 / 2` under `violatingLaw`, so the
positivity conditions of the instrumental inequalities hold automatically.) -/
theorem not_assumptions_of_law_eq_violatingLaw {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsFiniteMeasure μ'] (M' : IVModel Ω')
    (hlaw : μ'.map M'.observed = violatingLaw) :
    ¬ (M'.Exclusion μ' ∧ M'.InstrumentIndependence μ' ∧ M'.Monotonicity μ') := by
  rintro ⟨hE, hI, hM⟩
  have hpos : ∀ z, μ' (M'.instrumentEq z) ≠ 0 := by
    intro z
    have h := Measure.map_apply M'.measurable_observed
      (μ := μ') (measurable_fst (measurableSet_singleton z))
    rw [hlaw, violatingLaw, Measure.map_apply binaryModel.measurable_observed
      (measurable_fst (measurableSet_singleton z))] at h
    change P 3 (binaryModel.instrumentEq z) = μ' (M'.instrumentEq z) at h
    rw [← h, measure_instrumentEq_fst binaryModel rfl]
    simp
  have h := M'.law_instrumentalInequality_treated hE hI hM (hpos true) (hpos false)
    (measurableSet_singleton 1)
  rw [hlaw] at h
  exact absurd h (not_le.2 violatingLaw_lt)

end IVBounds

end CausalInference
