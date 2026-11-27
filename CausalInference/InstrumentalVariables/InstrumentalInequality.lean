/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.BalkePearl

/-!
# The instrumental inequality

Testable implications of the instrumental variable model that do not use monotonicity: the
instrumental inequality of Pearl (2009, *Causality*, 2nd edition, Section 8.4, equations (8.21)
and (8.22); Pearl 1995). In contrast with the monotone inequalities
`IVModel.instrumentalInequality_treated` and `IVModel.instrumentalInequality_untreated` of
`Bounds.lean` (equation (8.24)), these follow from the exclusion restriction and instrument
independence alone.

## Main definitions

* `CausalInference.FiniteIV.Weights`: for finite instrument, treatment and outcome types `Z`,
  `X`, `Y`, a distribution on the response functions `(f, g)` with `f : Z → X` (compliance) and
  `g : X → Y` (response); `FiniteIV.obs`: the induced `P(y, x | z)`.
* `IVResponse.violatingTable`, `IVBounds.exclusionViolatingLaw`: a table and an observed law
  violating (8.21).

## Main results

* `IVResponse.instrumentalInequality_binary`: the four inequalities (8.21) for every weight of
  the binary response-type model.
* `IVResponse.binaryIVConstraints_iff`: for binary variables, nonnegativity, normalization and
  (8.21) are not only necessary but also sufficient for a table to be induced by some weight.
* `FiniteIV.instrumentalInequality`: the general finite instrumental inequality (8.22),
  `max_x Σ_y max_z P(y, x | z) ≤ 1`; `FiniteIV.sum_obs_le_one`: the same for any choice
  `y ↦ ζ y` of instrument values.
* `IVModel.instrumentalInequality`: for an `IVModel` with real outcomes, under exclusion and
  instrument independence, `P(D = x, Y ∈ B | Z = z) + P(D = x, Y ∉ B | Z = z') ≤ 1` for every
  measurable `B`; for binary outcomes and `B = {0}` or `{1}` these are (8.21).
  `IVModel.law_instrumentalInequality`: the same for the observed-data law.
* `IVResponse.not_exists_obs_eq_violatingTable`: no weight induces `violatingTable`.
* `IVBounds.not_exclusion_and_independence_of_law_eq`: no `IVModel`, on any probability space,
  whose observed-data law is `exclusionViolatingLaw` satisfies exclusion and instrument
  independence; monotonicity plays no role.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

/-! ### The binary case -/

namespace IVResponse

/-- **The instrumental inequalities (8.21)** (Pearl 2009, Section 8.4). For every weight `q` on
the sixteen compliance and response types, the induced table satisfies
`P(y0, x0 | z0) + P(y1, x0 | z1) ≤ 1`, `P(y0, x1 | z0) + P(y1, x1 | z1) ≤ 1`,
`P(y1, x0 | z0) + P(y0, x0 | z1) ≤ 1` and `P(y1, x1 | z0) + P(y0, x1 | z1) ≤ 1`. -/
theorem instrumentalInequality_binary (q : Weights) :
    obs q false false false + obs q true false true ≤ 1 ∧
      obs q false true false + obs q true true true ≤ 1 ∧
      obs q true false false + obs q false false true ≤ 1 ∧
      obs q true true false + obs q false true true ≤ 1 :=
  let h := binaryIVConstraints_obs q
  ⟨h.ineq₁, h.ineq₂, h.ineq₃, h.ineq₄⟩

/-- **For binary variables the instrumental inequalities are the only constraints.** A table
`p y x z` is induced by some weight on the sixteen compliance and response types if and only if
its entries are nonnegative, each instrument arm sums to one, and the four inequalities (8.21)
hold. Sufficiency is the vertex construction of `exists_weights_ace_eq_lower`. -/
theorem binaryIVConstraints_iff {p : Observable} :
    BinaryIVConstraints p ↔ ∃ q : Weights, obs q = p :=
  ⟨exists_obs_eq, fun ⟨q, hq⟩ ↦ hq ▸ binaryIVConstraints_obs q⟩

/-- A table violating (8.21): under `z0` every unit has `y0, x0`, under `z1` every unit has
`y1, x0`, so `P(y0, x0 | z0) + P(y1, x0 | z1) = 2`. -/
noncomputable def violatingTable : Observable := mkTable 1 0 0 0 0 1 0 0

/-- **A table that no instrumental variable model generates.** `violatingTable` satisfies
nonnegativity and normalization but violates the first inequality of (8.21), so it is not
induced by any weight on the compliance and response types: no model with the exclusion
restriction and an instrument independent of the types produces it, whatever the compliance
behavior. -/
theorem not_exists_obs_eq_violatingTable : ¬ ∃ q : Weights, obs q = violatingTable := by
  rintro ⟨q, hq⟩
  have h := (instrumentalInequality_binary q).1
  rw [hq] at h
  norm_num [violatingTable, mkTable] at h

end IVResponse

/-! ### The general finite case -/

namespace FiniteIV

variable {Z X Y : Type*} [Fintype Z] [Fintype X] [Fintype Y] [DecidableEq Z] [DecidableEq X]
  [DecidableEq Y]

/-- For finite instrument, treatment and outcome types, the response-function model: a
distribution on pairs `(f, g)` of a compliance function `f : Z → X` and a response function
`g : X → Y` (the canonical partition of Pearl 2009, Section 8.2.2). -/
abbrev Weights (Z X Y : Type*) [Fintype Z] [Fintype X] [Fintype Y] [DecidableEq Z]
    [DecidableEq X] :=
  FiniteDist ((Z → X) × (X → Y))

/-- The observable `P(y, x | z)` of the response-function model: the total weight of the pairs
`(f, g)` with `f z = x` and `g x = y`. The same weight is used for every `z` (the instrument is
independent of the response functions) and the outcome depends on `z` only through `x`
(exclusion). -/
def obs (q : Weights Z X Y) (y : Y) (x : X) (z : Z) : ℝ :=
  ∑ r, if r.1 z = x ∧ r.2 x = y then q r else 0

/-- The instrumental inequality for an arbitrary choice of instrument values: for every
treatment value `x` and every map `ζ : Y → Z`, `Σ_y P(y, x | ζ y) ≤ 1`. Each `P(y, x | ζ y)` is
at most `P(g x = y)`, and these sum to one over `y`. -/
theorem sum_obs_le_one (q : Weights Z X Y) (x : X) (ζ : Y → Z) :
    ∑ y, obs q y x (ζ y) ≤ 1 := by
  calc ∑ y, obs q y x (ζ y) ≤ ∑ y, ∑ r, if r.2 x = y then q r else 0 := by
        refine Finset.sum_le_sum fun y _ ↦ Finset.sum_le_sum fun r _ ↦ ?_
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact absurd h1.2 h2
        · exact q.nonneg r
        · exact le_rfl
    _ = ∑ r, q r := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun r _ ↦ by simp
    _ = 1 := q.sum_eq_one

/-- **The instrumental inequality (8.22)** (Pearl 2009, Section 8.4; Pearl 1995). For finite
instrument, treatment and outcome types and every response-function model,
`Σ_y max_z P(y, x | z) ≤ 1` for every treatment value `x`, that is,
`max_x Σ_y max_z P(y, x | z) ≤ 1`. -/
theorem instrumentalInequality [Nonempty Z] (q : Weights Z X Y) (x : X) :
    ∑ y, Finset.univ.sup' Finset.univ_nonempty (fun z ↦ obs q y x z) ≤ 1 := by
  choose ζ hζ using fun y : Y ↦
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun z ↦ obs q y x z)
  calc ∑ y, Finset.univ.sup' Finset.univ_nonempty (fun z ↦ obs q y x z)
      = ∑ y, obs q y x (ζ y) := Finset.sum_congr rfl fun y _ ↦ (hζ y).2
    _ ≤ 1 := sum_obs_le_one q x ζ

end FiniteIV

/-! ### The inequality for an `IVModel` -/

namespace IVModel

open IVBounds

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- **The instrumental inequality for an `IVModel`** (Pearl 2009, (8.21), extended to real
outcomes). Under the exclusion restriction and instrument independence, for instrument values
`z`, `z'` of positive probability, every treatment value `x` and every measurable set `B`:
`P(D = x, Y ∈ B | Z = z) + P(D = x, Y ∉ B | Z = z') ≤ 1`. Monotonicity is not assumed. Both
events force the same untreated or treated potential outcome `Y x` to lie in `B` and in its
complement, respectively. -/
theorem instrumentalInequality [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) {z z' : Bool} (hz : μ (M.instrumentEq z) ≠ 0)
    (hz' : μ (M.instrumentEq z') ≠ 0) (x : Bool) {B : Set ℝ} (hB : MeasurableSet B) :
    μ[{ω | M.Dobs ω = x ∧ M.Yobs ω ∈ B} | M.instrumentEq z] +
      μ[{ω | M.Dobs ω = x ∧ M.Yobs ω ∈ Bᶜ} | M.instrumentEq z'] ≤ 1 := by
  rw [M.cond_obs_event hI hz x hB, M.cond_obs_event hI hz' x hB.compl]
  have hs : MeasurableSet (M.Y false x ⁻¹' B) := M.measurable_Y false x hB
  calc μ {ω | M.D z ω = x ∧ M.Y z x ω ∈ B} + μ {ω | M.D z' ω = x ∧ M.Y z' x ω ∈ Bᶜ}
      ≤ μ (M.Y false x ⁻¹' B) + μ (M.Y false x ⁻¹' B)ᶜ := by
        refine add_le_add (measure_mono_ae ?_) (measure_mono_ae ?_)
        · filter_upwards [hE.ae_eq z false x] with ω hω
          rintro ⟨-, h⟩
          change M.Y false x ω ∈ B
          rw [← hω]; exact h
        · filter_upwards [hE.ae_eq z' false x] with ω hω
          rintro ⟨-, h⟩
          change M.Y false x ω ∉ B
          rw [← hω]; exact h
    _ = 1 := by rw [measure_add_measure_compl hs, measure_univ]

/-- The instrumental inequality stated for the observed-data law `ν = μ.map (Z, Dobs, Yobs)`:
`ν(D = x, Y ∈ B | Z = z) + ν(D = x, Y ∉ B | Z = z') ≤ 1`. -/
theorem law_instrumentalInequality [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) {z z' : Bool} (hz : μ (M.instrumentEq z) ≠ 0)
    (hz' : μ (M.instrumentEq z') ≠ 0) (x : Bool) {B : Set ℝ} (hB : MeasurableSet B) :
    (μ.map M.observed)[obsEvent x B | Prod.fst ⁻¹' {z}] +
      (μ.map M.observed)[obsEvent x Bᶜ | Prod.fst ⁻¹' {z'}] ≤ 1 := by
  rw [map_cond_apply M.measurable_observed (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent x hB),
    map_cond_apply M.measurable_observed (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent x hB.compl)]
  exact M.instrumentalInequality hE hI hz hz' x hB

end IVModel

/-! ### An observed law refuting exclusion and independence -/

namespace IVBounds

open IVCounterexample

/-- A model on `Bool × Fin 1` whose observed-data law violates (8.21): a fair coin `Z`, nobody
is treated, and the outcome equals the instrument, `Y z d = 1` if `z = 1` and `0` otherwise.
It violates the exclusion restriction. -/
def directEffectModel : IVModel (Space 1) where
  Z := Prod.fst
  D _ _ := false
  Y z _ _ := if z then 1 else 0
  measurable_Z := measurable_fst
  measurable_D _ := measurable_const
  measurable_Y _ _ := measurable_const

theorem directEffectModel_independence : directEffectModel.InstrumentIndependence (P 1) :=
  indepFun_fst fun u ↦ directEffectModel.potentials (true, u)

theorem directEffectModel_instrument_ne_zero (z : Bool) :
    P 1 (directEffectModel.instrumentEq z) ≠ 0 := by
  rw [measure_instrumentEq_fst directEffectModel rfl]; simp

/-- The observed-data law of `directEffectModel`, a law on `Bool × Bool × ℝ`. -/
noncomputable def exclusionViolatingLaw : Measure (Bool × Bool × ℝ) :=
  (P 1).map directEffectModel.observed

/-- `exclusionViolatingLaw` violates (8.21) with `x = 0` and `B = {0}`:
`P(D = 0, Y = 0 | Z = 0) + P(D = 0, Y ≠ 0 | Z = 1) = 2`. -/
theorem exclusionViolatingLaw_eq_two :
    exclusionViolatingLaw[obsEvent false {0} | Prod.fst ⁻¹' {false}] +
      exclusionViolatingLaw[obsEvent false {0}ᶜ | Prod.fst ⁻¹' {true}] = 2 := by
  rw [exclusionViolatingLaw,
    map_cond_apply directEffectModel.measurable_observed
      (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent false (measurableSet_singleton 0)),
    map_cond_apply directEffectModel.measurable_observed
      (measurable_fst (measurableSet_singleton _))
      (measurableSet_obsEvent false (measurableSet_singleton 0).compl)]
  change (P 1)[|directEffectModel.instrumentEq false]
      {ω | directEffectModel.Dobs ω = false ∧ directEffectModel.Yobs ω ∈ ({0} : Set ℝ)} +
    (P 1)[|directEffectModel.instrumentEq true]
      {ω | directEffectModel.Dobs ω = false ∧ directEffectModel.Yobs ω ∈ ({0} : Set ℝ)ᶜ} = 2
  rw [directEffectModel.cond_obs_event directEffectModel_independence
      (directEffectModel_instrument_ne_zero false) false (measurableSet_singleton 0),
    directEffectModel.cond_obs_event directEffectModel_independence
      (directEffectModel_instrument_ne_zero true) false (measurableSet_singleton 0).compl]
  have h0 : {ω : Space 1 | directEffectModel.D false ω = false ∧
      directEffectModel.Y false false ω ∈ ({0} : Set ℝ)} = univ := by
    ext ω; simp [directEffectModel]
  have h1 : {ω : Space 1 | directEffectModel.D true ω = false ∧
      directEffectModel.Y true false ω ∈ ({0} : Set ℝ)ᶜ} = univ := by
    ext ω; simp [directEffectModel]
  rw [h0, h1, measure_univ]
  norm_num

/-- **The instrumental inequality refutes exclusion and independence without monotonicity.**
No binary IV model, on any probability space, whose observed-data law is
`exclusionViolatingLaw` satisfies both the exclusion restriction and instrument independence.
(Both instrument values have probability `1 / 2` under this law.) Unlike
`IVBounds.not_assumptions_of_law_eq_violatingLaw`, monotonicity is not among the refuted
assumptions. -/
theorem not_exclusion_and_independence_of_law_eq {Ω' : Type*} [MeasurableSpace Ω']
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] (M' : IVModel Ω')
    (hlaw : μ'.map M'.observed = exclusionViolatingLaw) :
    ¬ (M'.Exclusion μ' ∧ M'.InstrumentIndependence μ') := by
  rintro ⟨hE, hI⟩
  have hpos : ∀ z, μ' (M'.instrumentEq z) ≠ 0 := by
    intro z
    have h := Measure.map_apply M'.measurable_observed
      (μ := μ') (measurable_fst (measurableSet_singleton z))
    rw [hlaw, exclusionViolatingLaw, Measure.map_apply directEffectModel.measurable_observed
      (measurable_fst (measurableSet_singleton z))] at h
    change P 1 (directEffectModel.instrumentEq z) = μ' (M'.instrumentEq z) at h
    rw [← h, measure_instrumentEq_fst directEffectModel rfl]
    simp
  have h := M'.law_instrumentalInequality hE hI (hpos false) (hpos true) false
    (measurableSet_singleton 0)
  rw [hlaw, exclusionViolatingLaw_eq_two] at h
  norm_num at h

end IVBounds

end CausalInference
