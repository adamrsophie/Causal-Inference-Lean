/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.LATE
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.UniformOn

/-!
# Counterexamples for binary instrumental variables

Concrete finite models showing that the hypotheses of the LATE theorem
(`CausalInference.IVModel.wald_eq_complierEffect`) cannot simply be dropped, and that the IV
assumptions identify only the complier effect, in line with Imbens and Angrist (1994,
*Identification and estimation of local average treatment effects*).

Each model lives on `Bool × Fin n`, for `n ≠ 0`, with the product of the uniform distributions;
the instrument
is the first coordinate and all potential variables are functions of the second, so instrument
independence follows from independence of the coordinates of a product measure.

## Main results

* `IVCounterexample.wald_ne_of_not_monotonicity`: a model satisfying exclusion, instrument
  independence, relevance, `0 < P(Z = true) < 1` and integrability, but not monotonicity (in
  either direction, so not by a relabeling of the instrument), whose
  Wald ratio (`-2`) differs from both the complier average causal effect (`1`) and the average
  treatment effect (`2`).
* `IVCounterexample.ate_not_identified`, with `IVCounterexample.modelB_assumptions`: two models
  with the same observed-data law, both satisfying all the assumptions of the LATE theorem, with
  different average treatment effects.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace IVCounterexample

/-! ### Finite product models -/

variable {n : ℕ}

/-- The sample space `Bool × Fin n`: the first coordinate is the instrument, the second is a
unit type that carries all potential variables. -/
abbrev Space (n : ℕ) : Type := Bool × Fin n

/-- The product of the uniform distributions on `Bool` and on `Fin n`: the instrument is a fair
coin, drawn independently of a unit type that is uniform on `Fin n`. This reading requires
`n ≠ 0`: for `n = 0` the sample space is empty and `P 0` is the zero measure. Accordingly the
probability-measure instance and every lemma below that uses it assume `[NeZero n]`. -/
noncomputable def P (n : ℕ) : Measure (Space n) :=
  (uniformOn (Set.univ : Set Bool)).prod (uniformOn (Set.univ : Set (Fin n)))

instance [NeZero n] : IsProbabilityMeasure (P n) := by unfold P; infer_instance

theorem measure_singleton_ne_zero (ω : Space n) : P n {ω} ≠ 0 := by
  rw [P, ← Set.singleton_prod_singleton, Measure.prod_prod, uniformOn_univ, uniformOn_univ]
  simp

/-- The integral of a function of the unit type is its average over `Fin n`. -/
theorem integral_snd [NeZero n] (g : Fin n → ℝ) : ∫ ω, g ω.2 ∂P n = (∑ u, g u) / n := by
  rw [P, integral_fun_snd, probReal_univ, one_smul, integral_fintype (.of_finite)]
  simp [uniformOn_univ, measureReal_def, div_eq_inv_mul, Finset.mul_sum]

/-- The integral of a function that depends only on the unit coordinate is its average over
the units. -/
theorem integral_of_snd [NeZero n] (f : Space n → ℝ) (hf : ∀ ω, f ω = f (true, ω.2)) :
    ∫ ω, f ω ∂P n = (∑ u, f (true, u)) / n := by
  rw [← integral_snd]
  exact integral_congr_ae (Filter.Eventually.of_forall hf)

/-- Each instrument value has probability `1 / 2`. -/
theorem measure_fst_preimage [NeZero n] (z : Bool) : P n (Prod.fst ⁻¹' {z}) = 2⁻¹ := by
  rw [P, ← Set.prod_univ, Measure.prod_prod, uniformOn_univ, uniformOn_univ]
  simp [ENNReal.div_self (Nat.cast_ne_zero.2 (NeZero.ne n)) (ENNReal.natCast_ne_top n)]

/-- In a product model the instrument `Prod.fst` is independent of every function of the unit
coordinate. -/
theorem indepFun_fst [NeZero n] {β : Type*} [MeasurableSpace β] (h : Fin n → β) :
    IndepFun Prod.fst (fun ω : Space n ↦ h ω.2) (P n) :=
  indepFun_prod (X := id) measurable_id (measurable_of_countable h)

theorem measure_instrumentEq_fst [NeZero n] (M : IVModel (Space n)) (hZ : M.Z = Prod.fst)
    (z : Bool) : P n (M.instrumentEq z) = 2⁻¹ := by
  rw [IVModel.instrumentEq, hZ, measure_fst_preimage]

theorem instrument_pos_lt_one [NeZero n] (M : IVModel (Space n)) (hZ : M.Z = Prod.fst) :
    0 < P n (M.instrumentEq true) ∧ P n (M.instrumentEq true) < 1 := by
  rw [measure_instrumentEq_fst M hZ]
  exact ⟨by simp, ENNReal.inv_lt_one.2 (by norm_num)⟩

/-! ### Counterexample (a): monotonicity fails -/

/-- Counterexample (a), on `Bool × Fin 3`: units `0` and `1` are compliers with unit-level
effect `1`; unit `2` is a defier with unit-level effect `4`. The outcome is the effect if treated
and `0` otherwise, whatever the instrument value. -/
def modelA : IVModel (Space 3) where
  Z := Prod.fst
  D z ω := if ω.2 = 2 then !z else z
  Y _ d ω := if d then (if ω.2 = 2 then 4 else 1) else 0
  measurable_Z := measurable_fst
  measurable_D _ := measurable_of_countable _
  measurable_Y _ _ := measurable_of_countable _

theorem modelA_exclusion : modelA.Exclusion (P 3) := fun _ ↦ Filter.EventuallyEq.rfl

theorem modelA_independence : modelA.InstrumentIndependence (P 3) :=
  indepFun_fst fun u ↦ modelA.potentials (true, u)

theorem modelA_instrument_ne_zero (z : Bool) : P 3 (modelA.instrumentEq z) ≠ 0 := by
  rw [measure_instrumentEq_fst modelA rfl]; simp

theorem modelA_firstStage : modelA.firstStage (P 3) = 1 / 3 := by
  rw [IVModel.firstStage,
    modelA.condMean_DobsReal modelA_independence (modelA_instrument_ne_zero true),
    modelA.condMean_DobsReal modelA_independence (modelA_instrument_ne_zero false),
    integral_of_snd _ fun _ ↦ rfl, integral_of_snd _ fun _ ↦ rfl]
  simp [Fin.sum_univ_three, modelA, IVModel.DReal]
  norm_num

theorem modelA_relevance : modelA.Relevance (P 3) := by
  refine ⟨modelA_instrument_ne_zero true, modelA_instrument_ne_zero false, ?_⟩
  rw [modelA_firstStage]; norm_num

theorem modelA_reducedForm : modelA.reducedForm (P 3) = -2 / 3 := by
  rw [IVModel.reducedForm,
    modelA.condMean_Yobs modelA_independence (modelA_instrument_ne_zero true) .of_finite,
    modelA.condMean_Yobs modelA_independence (modelA_instrument_ne_zero false) .of_finite,
    integral_of_snd _ fun _ ↦ rfl, integral_of_snd _ fun _ ↦ rfl]
  simp [Fin.sum_univ_three, modelA, IVModel.YD]
  norm_num

theorem modelA_wald : modelA.wald (P 3) = -2 := by
  rw [IVModel.wald, modelA_reducedForm, modelA_firstStage]; norm_num

theorem modelA_ate (z : Bool) : modelA.ate (P 3) z = 2 := by
  rw [IVModel.ate, integral_of_snd _ fun _ ↦ rfl]
  simp [Fin.sum_univ_three, modelA, IVModel.effect]
  norm_num

theorem modelA_complierEffect (z : Bool) : modelA.complierEffect (P 3) z = 1 := by
  have hC : P 3 modelA.compliers ≠ 0 := fun h ↦ measure_singleton_ne_zero ((true, 0) : Space 3)
    (measure_mono_null (by simp [IVModel.mem_compliers, modelA]) h)
  have := cond_isProbabilityMeasure (μ := P 3) hC
  rw [IVModel.complierEffect]
  refine (integral_congr_ae (g := fun _ ↦ (1 : ℝ)) ?_).trans (by simp)
  refine ((ae_cond_mem modelA.measurableSet_compliers).mono fun ω hω ↦ ?_)
  rw [IVModel.mem_compliers] at hω
  have h2 : ω.2 ≠ 2 := fun h ↦ by simp [modelA, h] at hω
  simp [IVModel.effect, modelA, h2]

theorem modelA_not_monotonicity : ¬ modelA.Monotonicity (P 3) := by
  rw [IVModel.Monotonicity, ae_iff]
  exact fun h ↦ measure_singleton_ne_zero ((true, 2) : Space 3)
    (measure_mono_null (by simp [modelA]) h)

/-- Monotonicity fails in `modelA` in the reversed direction as well: the compliers (units `0`
and `1`) violate `D true ≤ D false`. -/
theorem modelA_not_reversed_monotonicity :
    ¬ ∀ᵐ ω ∂P 3, modelA.D true ω ≤ modelA.D false ω := by
  rw [ae_iff]
  exact fun h ↦ measure_singleton_ne_zero ((true, 0) : Space 3)
    (measure_mono_null (by simp [modelA]) h)

/-- **Counterexample (a)**: without monotonicity the Wald ratio need not be the complier effect
or the average treatment effect. In `modelA` the exclusion restriction, instrument independence,
relevance, `0 < P(Z = true) < 1` and integrability hold, and monotonicity fails in both
directions (`D false ≤ D true` fails because of the defier, `D true ≤ D false` because of the
compliers), so the failure is not an artifact of the labeling of the instrument; the Wald ratio
is `-2`, while the complier average causal effect is `1` and the average treatment effect is
`2`. -/
theorem wald_ne_of_not_monotonicity :
    modelA.Exclusion (P 3) ∧ modelA.InstrumentIndependence (P 3) ∧ modelA.Relevance (P 3) ∧
      0 < P 3 (modelA.instrumentEq true) ∧ P 3 (modelA.instrumentEq true) < 1 ∧
      (∀ z d, Integrable (modelA.Y z d) (P 3)) ∧ ¬ modelA.Monotonicity (P 3) ∧
      (¬ ∀ᵐ ω ∂P 3, modelA.D true ω ≤ modelA.D false ω) ∧
      ∀ z, modelA.wald (P 3) ≠ modelA.complierEffect (P 3) z ∧
        modelA.wald (P 3) ≠ modelA.ate (P 3) z := by
  refine ⟨modelA_exclusion, modelA_independence, modelA_relevance,
    (instrument_pos_lt_one modelA rfl).1, (instrument_pos_lt_one modelA rfl).2,
    fun _ _ ↦ .of_finite, modelA_not_monotonicity, modelA_not_reversed_monotonicity,
    fun z ↦ ⟨?_, ?_⟩⟩
  · rw [modelA_wald, modelA_complierEffect]; norm_num
  · rw [modelA_wald, modelA_ate]; norm_num

/-! ### Counterexample (b): the average treatment effect is not identified -/

/-- Counterexample (b), on `Bool × Fin 2`, indexed by `c : ℝ`: unit `0` is a complier whose
outcome is `1` if treated and `0` otherwise; unit `1` is a never-taker whose outcome is `0` if
untreated and `c` if treated. The treated outcome of a never-taker is never observed. -/
def modelB (c : ℝ) : IVModel (Space 2) where
  Z := Prod.fst
  D z ω := if ω.2 = 0 then z else false
  Y _ d ω := if d then (if ω.2 = 0 then 1 else c) else 0
  measurable_Z := measurable_fst
  measurable_D _ := measurable_of_countable _
  measurable_Y _ _ := measurable_of_countable _

theorem modelB_independence (c : ℝ) : (modelB c).InstrumentIndependence (P 2) :=
  indepFun_fst fun u ↦ (modelB c).potentials (true, u)

theorem modelB_instrument_ne_zero (c : ℝ) (z : Bool) : P 2 ((modelB c).instrumentEq z) ≠ 0 := by
  rw [measure_instrumentEq_fst (modelB c) rfl]; simp

theorem modelB_firstStage (c : ℝ) : (modelB c).firstStage (P 2) = 1 / 2 := by
  rw [IVModel.firstStage,
    (modelB c).condMean_DobsReal (modelB_independence c) (modelB_instrument_ne_zero c true),
    (modelB c).condMean_DobsReal (modelB_independence c) (modelB_instrument_ne_zero c false),
    integral_of_snd _ fun _ ↦ rfl, integral_of_snd _ fun _ ↦ rfl]
  simp [modelB, IVModel.DReal]

/-- Every `modelB c` satisfies all the hypotheses of the LATE theorem. -/
theorem modelB_assumptions (c : ℝ) : (modelB c).LATEAssumptions (P 2) where
  exclusion _ := Filter.EventuallyEq.rfl
  independence := modelB_independence c
  monotonicity := Filter.Eventually.of_forall fun ω ↦ by
    by_cases h : ω.2 = 0 <;> simp [modelB, h]
  relevance := ⟨modelB_instrument_ne_zero c true, modelB_instrument_ne_zero c false,
    by rw [modelB_firstStage]; norm_num⟩
  integrable _ := .of_finite

/-- The observed data `(Z, Dobs, Yobs)` of `modelB c` do not depend on `c`. -/
theorem modelB_observed (c c' : ℝ) : (modelB c).observed = (modelB c').observed := by
  funext ω
  obtain ⟨b, u⟩ := ω
  fin_cases u <;> cases b <;> simp [IVModel.observed, IVModel.Yobs, IVModel.Dobs, modelB]

/-- The average treatment effect of `modelB c` is `(1 + c) / 2`. -/
theorem modelB_ate (c : ℝ) (z : Bool) : (modelB c).ate (P 2) z = (1 + c) / 2 := by
  rw [IVModel.ate, integral_of_snd _ fun _ ↦ rfl]
  simp [modelB, IVModel.effect]

/-- **Counterexample (b)**: the IV assumptions do not identify the average treatment effect.
The models `modelB 0` and `modelB 1` share the sample space, the probability measure and the
observed-data law (the law of `(Z, Dobs, Yobs)`), both satisfy exclusion, instrument
independence, monotonicity, relevance (with `0 < P(Z = true) < 1`) and integrability, and their
average treatment effects are `1 / 2` and `1`. -/
theorem ate_not_identified :
    (modelB 0).LATEAssumptions (P 2) ∧ (modelB 1).LATEAssumptions (P 2) ∧
      (P 2).map (modelB 0).observed = (P 2).map (modelB 1).observed ∧
      ∀ z, (modelB 0).ate (P 2) z ≠ (modelB 1).ate (P 2) z := by
  refine ⟨modelB_assumptions 0, modelB_assumptions 1, by rw [modelB_observed 0 1], fun z ↦ ?_⟩
  rw [modelB_ate, modelB_ate]; norm_num

end IVCounterexample

end CausalInference
