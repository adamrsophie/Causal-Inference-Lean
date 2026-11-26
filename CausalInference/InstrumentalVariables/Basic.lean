/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Independence.Basic

/-!
# Instrumental variables: the model and the identifying assumptions

A binary instrument `Z`, a binary treatment, and a real outcome, in the potential outcomes
framework of Imbens and Angrist (1994, *Identification and estimation of local average treatment
effects*) and Angrist, Imbens and Rubin (1996, *Identification of causal effects using
instrumental variables*).

## Main definitions

* `CausalInference.IVModel`: an instrument `Z : Ω → Bool`, potential treatments `D z : Ω → Bool`
  and potential outcomes `Y z d : Ω → ℝ`, all measurable.
* `IVModel.Dobs`, `IVModel.Yobs`: the observed treatment `D (Z ω) ω` and the observed outcome
  `Y (Z ω) (Dobs ω) ω`. Consistency is built into these definitions.
* `IVModel.observed`: the observed data `(Z, Dobs, Yobs)`.
* `IVModel.potentials`: the vector of all potential treatments and outcomes of a unit.
* `IVModel.condMean`: the conditional mean `E[f | Z = z]`, an integral against `μ[|Z = z]`.
* The assumptions, each a separate `Prop`: `IVModel.Exclusion`, `IVModel.InstrumentIndependence`,
  `IVModel.Relevance`, `IVModel.Monotonicity`.

## Main results

* `IVModel.condMean_potentials`: under instrument independence, conditioning on `Z = z` does
  not change the mean of any function of the potential variables.
* `IVModel.condMean_DobsReal`, `IVModel.condMean_Yobs`: `E[Dobs | Z = z] = E[D z]` and
  `E[Yobs | Z = z] = E[Y z (D z)]` under instrument independence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

/-- A binary instrumental variable model on a sample space `Ω`: a measurable binary instrument
`Z`, measurable potential treatments `D z` (the treatment a unit takes when the instrument is set
to `z`), and measurable potential outcomes `Y z d` (the outcome when the instrument is set to `z`
and the treatment to `d`). -/
structure IVModel (Ω : Type*) [MeasurableSpace Ω] where
  /-- The instrument. -/
  Z : Ω → Bool
  /-- The potential treatment under instrument value `z`. -/
  D : Bool → Ω → Bool
  /-- The potential outcome under instrument value `z` and treatment value `d`. -/
  Y : Bool → Bool → Ω → ℝ
  measurable_Z : Measurable Z
  measurable_D : ∀ z, Measurable (D z)
  measurable_Y : ∀ z d, Measurable (Y z d)

namespace IVModel

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω)

/-- The real coding of a binary value: `1` for `true` and `0` for `false`. -/
def boolToReal (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem boolToReal_true : boolToReal true = 1 := rfl

@[simp] theorem boolToReal_false : boolToReal false = 0 := rfl

/-- The observed treatment `Dobs ω = D (Z ω) ω`: the potential treatment under the realized
instrument value (treatment consistency, built into the definition). -/
def Dobs (ω : Ω) : Bool := M.D (M.Z ω) ω

/-- The observed outcome `Yobs ω = Y (Z ω) (Dobs ω) ω`: the potential outcome under the realized
instrument and treatment values (outcome consistency, built into the definition). -/
def Yobs (ω : Ω) : ℝ := M.Y (M.Z ω) (M.Dobs ω) ω

/-- The observed data of the unit `ω`: the triple `(Z ω, Dobs ω, Yobs ω)`. Its law under `μ`,
`μ.map M.observed`, is the observed-data law. -/
def observed (ω : Ω) : Bool × Bool × ℝ := (M.Z ω, M.Dobs ω, M.Yobs ω)

/-- The observed treatment coded as a real number, `1` if treated and `0` otherwise. -/
def DobsReal (ω : Ω) : ℝ := boolToReal (M.Dobs ω)

/-- The potential treatment `D z` coded as a real number. -/
def DReal (z : Bool) (ω : Ω) : ℝ := boolToReal (M.D z ω)

/-- The outcome a unit would have if the instrument were set to `z` and the treatment were left
to respond to it: `Y z (D z ω) ω`. -/
def YD (z : Bool) (ω : Ω) : ℝ := M.Y z (M.D z ω) ω

/-- The type of the vector of all potential variables of a unit: the two potential treatments
and the four potential outcomes. -/
abbrev Potentials : Type := (Bool → Bool) × (Bool → Bool → ℝ)

/-- The vector of all potential treatments and potential outcomes of the unit `ω`. -/
def potentials (ω : Ω) : Potentials := (fun z ↦ M.D z ω, fun z d ↦ M.Y z d ω)

/-- The event `{Z = z}`. -/
def instrumentEq (z : Bool) : Set Ω := M.Z ⁻¹' {z}

/-- The conditional mean `E[f | Z = z]`, the integral of `f` against the conditional probability
measure `μ[|Z = z]`. -/
noncomputable def condMean (μ : Measure Ω) (f : Ω → ℝ) (z : Bool) : ℝ :=
  ∫ ω, f ω ∂μ[|M.instrumentEq z]

/-- The first stage `E[Dobs | Z = true] - E[Dobs | Z = false]`. -/
noncomputable def firstStage (μ : Measure Ω) : ℝ :=
  M.condMean μ M.DobsReal true - M.condMean μ M.DobsReal false

/-- The reduced form `E[Yobs | Z = true] - E[Yobs | Z = false]`. -/
noncomputable def reducedForm (μ : Measure Ω) : ℝ :=
  M.condMean μ M.Yobs true - M.condMean μ M.Yobs false

/-- The Wald ratio: the reduced form divided by the first stage. -/
noncomputable def wald (μ : Measure Ω) : ℝ := M.reducedForm μ / M.firstStage μ

/-- The unit-level treatment effect `Y z true ω - Y z false ω` at instrument value `z`. Under
the exclusion restriction it does not depend on `z` up to a null set. -/
def effect (z : Bool) (ω : Ω) : ℝ := M.Y z true ω - M.Y z false ω

/-- The average treatment effect `E[Y z true - Y z false]` at instrument value `z`. -/
noncomputable def ate (μ : Measure Ω) (z : Bool) : ℝ := ∫ ω, M.effect z ω ∂μ

/-! ### The identifying assumptions -/

/-- The exclusion restriction: almost surely, the potential outcome `Y z d` does not depend on
the instrument value `z`. -/
def Exclusion (μ : Measure Ω) : Prop := ∀ d, M.Y true d =ᵐ[μ] M.Y false d

/-- Instrument independence: the instrument `Z` is independent of the vector of all potential
treatments and potential outcomes. -/
def InstrumentIndependence (μ : Measure Ω) : Prop := IndepFun M.Z M.potentials μ

/-- Relevance: the first stage `E[Dobs | Z = true] - E[Dobs | Z = false]` is nonzero. -/
def Relevance (μ : Measure Ω) : Prop := M.firstStage μ ≠ 0

/-- Monotonicity: almost surely, a unit that takes the treatment when the instrument is `false`
also takes it when the instrument is `true` (`D false ≤ D true` with `false < true`). -/
def Monotonicity (μ : Measure Ω) : Prop := ∀ᵐ ω ∂μ, M.D false ω ≤ M.D true ω

/-! ### Measurability -/

theorem measurable_potentials : Measurable M.potentials :=
  (Measurable.of_eval M.measurable_D).prodMk
    (Measurable.of_eval fun z ↦ Measurable.of_eval (M.measurable_Y z))

theorem measurableSet_instrumentEq (z : Bool) : MeasurableSet (M.instrumentEq z) :=
  M.measurable_Z (measurableSet_singleton z)

/-! ### Conditioning on the instrument -/

variable {μ : Measure Ω}

/-- Under instrument independence, the law of the vector of potential variables given `Z = z`
equals its unconditional law, provided `P(Z = z) ≠ 0`. -/
theorem map_potentials_cond [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ) {z : Bool}
    (hz : μ (M.instrumentEq z) ≠ 0) :
    (μ[|M.instrumentEq z]).map M.potentials = μ.map M.potentials := by
  ext t ht
  rw [instrumentEq] at hz ⊢
  rw [Measure.map_apply M.measurable_potentials ht, Measure.map_apply M.measurable_potentials ht,
    cond_apply (M.measurable_Z (measurableSet_singleton z)),
    indepFun_iff_measure_inter_preimage_eq_mul.1 hI _ _ (measurableSet_singleton z) ht,
    ← mul_assoc, ENNReal.inv_mul_cancel hz (measure_ne_top _ _), one_mul]

/-- Under instrument independence and `P(Z = z) ≠ 0`, the conditional mean given `Z = z` of a
measurable function of the potential variables equals its unconditional mean. -/
theorem condMean_potentials [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ) {z : Bool}
    (hz : μ (M.instrumentEq z) ≠ 0) {φ : Potentials → ℝ} (hφ : Measurable φ) :
    M.condMean μ (fun ω ↦ φ (M.potentials ω)) z = ∫ ω, φ (M.potentials ω) ∂μ := by
  rw [condMean, ← integral_map M.measurable_potentials.aemeasurable hφ.aestronglyMeasurable,
    M.map_potentials_cond hI hz,
    integral_map M.measurable_potentials.aemeasurable hφ.aestronglyMeasurable]

/-- Two functions that agree on the event `{Z = z}` have the same conditional mean given
`Z = z`. -/
theorem condMean_congr {f g : Ω → ℝ} {z : Bool} (h : ∀ ω ∈ M.instrumentEq z, f ω = g ω) :
    M.condMean μ f z = M.condMean μ g z :=
  integral_congr_ae ((ae_cond_mem (M.measurableSet_instrumentEq z)).mono h)

theorem measurable_boolToReal : Measurable boolToReal := measurable_of_countable _

theorem measurable_fst_eval (z : Bool) : Measurable fun w : Potentials ↦ w.1 z :=
  (measurable_pi_apply z).comp measurable_fst

theorem measurable_snd_eval (z d : Bool) : Measurable fun w : Potentials ↦ w.2 z d :=
  (measurable_pi_apply d).comp ((measurable_pi_apply z).comp measurable_snd)

/-- The map sending the potential variables to `Y z (D z')` is measurable. -/
theorem measurable_snd_eval_fst (z z' : Bool) :
    Measurable fun w : Potentials ↦ w.2 z (w.1 z') := by
  have h : (fun w : Potentials ↦ w.2 z (w.1 z')) =
      fun w ↦ if w.1 z' = true then w.2 z true else w.2 z false := by
    funext w; cases w.1 z' <;> rfl
  rw [h]
  exact Measurable.ite ((measurable_fst_eval z') (measurableSet_singleton true))
    (measurable_snd_eval z true) (measurable_snd_eval z false)

/-- The outcome `Y z (D z' ω) ω` is measurable. -/
theorem measurable_Y_D (z z' : Bool) : Measurable fun ω ↦ M.Y z (M.D z' ω) ω :=
  (measurable_snd_eval_fst z z').comp M.measurable_potentials

/-- If both potential outcomes `Y z true` and `Y z false` are integrable, so is
`Y z (D z' ω) ω`. -/
theorem integrable_Y_D {z : Bool} (hY : ∀ d, Integrable (M.Y z d) μ) (z' : Bool) :
    Integrable (fun ω ↦ M.Y z (M.D z' ω) ω) μ := by
  refine ((hY true).norm.add (hY false).norm).mono'
    (M.measurable_Y_D z z').aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
  cases M.D z' ω <;> simp

/-- Under instrument independence and `P(Z = z) ≠ 0`: `E[Dobs | Z = z] = E[D z]`. -/
theorem condMean_DobsReal [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ) {z : Bool}
    (hz : μ (M.instrumentEq z) ≠ 0) :
    M.condMean μ M.DobsReal z = ∫ ω, M.DReal z ω ∂μ := by
  rw [M.condMean_congr (g := M.DReal z) fun ω hω ↦ by
    simp only [instrumentEq, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [DobsReal, DReal, Dobs, hω]]
  exact M.condMean_potentials hI hz (measurable_boolToReal.comp (measurable_fst_eval z))

/-- Under instrument independence and `P(Z = z) ≠ 0`: `E[Yobs | Z = z] = E[Y z (D z)]`. -/
theorem condMean_Yobs [IsFiniteMeasure μ] (hI : M.InstrumentIndependence μ) {z : Bool}
    (hz : μ (M.instrumentEq z) ≠ 0) :
    M.condMean μ M.Yobs z = ∫ ω, M.YD z ω ∂μ := by
  rw [M.condMean_congr (g := M.YD z) fun ω hω ↦ by
    simp only [instrumentEq, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [Yobs, YD, Dobs, hω]]
  exact M.condMean_potentials hI hz (measurable_snd_eval_fst z z)

end IVModel

end CausalInference
