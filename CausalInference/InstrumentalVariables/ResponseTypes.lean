/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Basic.FiniteDistribution
public import CausalInference.InstrumentalVariables.Bounds

/-!
# Compliance and response types for a binary instrument, treatment and outcome

The finite response-variable model of Pearl (2009, *Causality*, 2nd edition, Section 8.2.2),
following Balke and Pearl (1997, *Bounds on treatment effects from studies with imperfect
compliance*). With a binary instrument `Z`, treatment `X` and outcome `Y`, every unit has a
compliance type `r_x ∈ {0, 1, 2, 3}` (never-taker, complier, defier, always-taker; equation
(8.6)) and a response type `r_y ∈ {0, 1, 2, 3}` (never recover, helped, hurt, always recover;
equation (8.7)). A model is a weight `q_{jk} = P(r_x = j, r_y = k)` on the sixteen pairs
(equation (8.11)).

## Main definitions

* `CausalInference.IVResponse.respond`: the four functions `Bool → Bool` indexed by a type in
  `Fin 4`: constant `false`, identity, negation, constant `true`.
* `IVResponse.Weights`: a finite distribution on `Fin 4 × Fin 4`, the weights `q_{jk}`.
* `IVResponse.Observable`: a table `p y x z`, read as `P(y, x | z)`.
* `IVResponse.obs`: the observable `P(y, x | z)` induced by a weight `q` (the linear map
  `p = R q` of Section 8.2.3).
* `IVResponse.probTreated`, `IVResponse.probUntreated`: `P(y1 | do(x1))` and `P(y1 | do(x0))`
  (equations (8.8), (8.9)); `IVResponse.ace`: the average causal effect (8.12).
* `IVModel.typeOf`: the compliance and response type of a unit of an `IVModel` whose outcomes
  are coded `0` and `1`; `IVModel.responseLaw`: its law.

## Main results

* `IVResponse.obs_fff` and its seven companions: the eight equations `p = R q` of Section 8.2.3.
* `IVResponse.ace_eq_sub`: `ACE = P(y1 | do(x1)) - P(y1 | do(x0))` (equation (8.10)).
* `IVModel.obs_responseLaw`: under exclusion, instrument independence and binary outcomes, the
  law of the response type of the model generates its observed conditional law
  `P(Dobs = x, Yobs = y | Z = z)`.
* `IVModel.ace_responseLaw`: under the same assumptions, the average causal effect of the law of
  the response type is the average treatment effect of the model.
* `IVResponse.realModel_spec`: the converse. Every response-type law `q` and every instrument
  probability `0 ≤ π ≤ 1` are realized by an `IVModel` (`IVResponse.realModel` under
  `IVResponse.realMeasure q`, on `Bool × Fin 4 × Fin 4`) with exclusion, instrument
  independence, binary outcomes, `P(Z = z1) = π`, response law `q` and average treatment effect
  `ace q`.

Binary outcomes (`IVModel.BinaryOutcome`) are assumed almost surely, not pointwise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference

namespace IVResponse

/-- The four functions from `Bool` to `Bool`, indexed by `Fin 4` as in equations (8.6) and (8.7)
of Pearl (2009): `0` is constant `false`, `1` is the identity, `2` is negation, `3` is constant
`true`. As a compliance type (input the instrument, output the treatment) these are the
never-taker, the complier, the defier and the always-taker; as a response type (input the
treatment, output the outcome) they are never recover, helped, hurt and always recover. -/
def respond : Fin 4 → Bool → Bool
  | 0, _ => false
  | 1, b => b
  | 2, b => !b
  | 3, _ => true

@[simp] theorem respond_zero (b : Bool) : respond 0 b = false := rfl

@[simp] theorem respond_one (b : Bool) : respond 1 b = b := rfl

@[simp] theorem respond_two (b : Bool) : respond 2 b = !b := rfl

@[simp] theorem respond_three (b : Bool) : respond 3 b = true := rfl

/-- The weights `q_{jk} = P(r_x = j, r_y = k)` of the sixteen compliance and response types
(equation (8.11)): nonnegative reals summing to one. -/
abbrev Weights : Type := FiniteDist (Fin 4 × Fin 4)

/-- An observable table `p y x z`, read as `P(Y = y, X = x | Z = z)`; Pearl writes `p_{yx.z}`
with `0` for `false` and `1` for `true`. -/
abbrev Observable : Type := Bool → Bool → Bool → ℝ

/-- The observable induced by the weights `q`: `P(y, x | z)` is the total weight of the types
`(j, k)` with `respond j z = x` and `respond k x = y`. This is the linear map `p = R q` of
Pearl (2009, Section 8.2.3), and it encodes the two assumptions of the model: the outcome
responds to the instrument only through the treatment (exclusion), and the type is independent
of the instrument (the same `q` is used for both values of `z`). -/
def obs (q : Weights) : Observable := fun y x z ↦
  ∑ s, if respond s.1 z = x ∧ respond s.2 x = y then q s else 0

/-- `P(y1 | do(x1)) = P(r_y = 1) + P(r_y = 3)` (equation (8.8)). -/
def probTreated (q : Weights) : ℝ := ∑ j, (q (j, 1) + q (j, 3))

/-- `P(y1 | do(x0)) = P(r_y = 2) + P(r_y = 3)` (equation (8.9)). -/
def probUntreated (q : Weights) : ℝ := ∑ j, (q (j, 2) + q (j, 3))

/-- The average causal effect `ACE(X → Y) = P(r_y = 1) - P(r_y = 2)` written in the weights
(equation (8.12)): `q01 + q11 + q21 + q31 - q02 - q12 - q22 - q32`. -/
def ace (q : Weights) : ℝ := ∑ j, (q (j, 1) - q (j, 2))

/-- Equation (8.10): `ACE = P(y1 | do(x1)) - P(y1 | do(x0))`. -/
theorem ace_eq_sub (q : Weights) : ace q = probTreated q - probUntreated q := by
  simp only [ace, probTreated, probUntreated, Fin.sum_univ_four]; ring

/-- The sum of the sixteen weights, written out. -/
theorem sum_weights (q : Weights) :
    q (0, 0) + q (0, 1) + q (0, 2) + q (0, 3) + q (1, 0) + q (1, 1) + q (1, 2) + q (1, 3) +
      q (2, 0) + q (2, 1) + q (2, 2) + q (2, 3) + q (3, 0) + q (3, 1) + q (3, 2) + q (3, 3) =
      1 := by
  have h := q.sum_eq_one
  simp only [Fintype.sum_prod_type, Fin.sum_univ_four] at h
  linarith

theorem ace_eq (q : Weights) :
    ace q = q (0, 1) + q (1, 1) + q (2, 1) + q (3, 1) - q (0, 2) - q (1, 2) - q (2, 2) -
      q (3, 2) := by
  simp only [ace, Fin.sum_univ_four]; ring

/-! ### The eight equations `p = R q` -/

/-- `p00.0 = q00 + q01 + q10 + q11`. -/
theorem obs_fff (q : Weights) :
    obs q false false false = q (0, 0) + q (0, 1) + q (1, 0) + q (1, 1) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- `p00.1 = q00 + q01 + q20 + q21`. -/
theorem obs_fft (q : Weights) :
    obs q false false true = q (0, 0) + q (0, 1) + q (2, 0) + q (2, 1) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- `p01.0 = q20 + q22 + q30 + q32`. -/
theorem obs_ftf (q : Weights) :
    obs q false true false = q (2, 0) + q (2, 2) + q (3, 0) + q (3, 2) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- `p01.1 = q10 + q12 + q30 + q32`. -/
theorem obs_ftt (q : Weights) :
    obs q false true true = q (1, 0) + q (1, 2) + q (3, 0) + q (3, 2) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- `p10.0 = q02 + q03 + q12 + q13`. -/
theorem obs_tff (q : Weights) :
    obs q true false false = q (0, 2) + q (0, 3) + q (1, 2) + q (1, 3) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- `p10.1 = q02 + q03 + q22 + q23`. -/
theorem obs_tft (q : Weights) :
    obs q true false true = q (0, 2) + q (0, 3) + q (2, 2) + q (2, 3) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- `p11.0 = q21 + q23 + q31 + q33`. -/
theorem obs_ttf (q : Weights) :
    obs q true true false = q (2, 1) + q (2, 3) + q (3, 1) + q (3, 3) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- `p11.1 = q11 + q13 + q31 + q33`. -/
theorem obs_ttt (q : Weights) :
    obs q true true true = q (1, 1) + q (1, 3) + q (3, 1) + q (3, 3) := by
  simp [obs, Fintype.sum_prod_type, Fin.sum_univ_four]; ring

/-- Every entry of an induced observable is nonnegative. -/
theorem obs_nonneg (q : Weights) (y x z : Bool) : 0 ≤ obs q y x z :=
  Finset.sum_nonneg fun s _ ↦ by split_ifs <;> simp [q.nonneg s]

/-- For each instrument value the four entries of an induced observable sum to one. -/
theorem obs_sum (q : Weights) (z : Bool) :
    obs q false false z + obs q false true z + obs q true false z + obs q true true z = 1 := by
  have h := sum_weights q
  cases z
  · rw [obs_fff, obs_ftf, obs_tff, obs_ttf]; linarith
  · rw [obs_fft, obs_ftt, obs_tft, obs_ttt]; linarith

end IVResponse

/-! ### The response type of a unit of an `IVModel` -/

namespace IVModel

open IVResponse

/-- The type in `Fin 4` of the function `Bool → Bool` with value `a` at `false` and `b` at
`true`. -/
def typeCode (a b : Bool) : Fin 4 := if a then (if b then 3 else 2) else (if b then 1 else 0)

@[simp] theorem respond_typeCode (a b v : Bool) :
    respond (typeCode a b) v = if v then b else a := by
  cases a <;> cases b <;> cases v <;> rfl

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- Binary outcomes: almost surely, every potential outcome takes the value `0` or `1`. Values
on a null set are not constrained, so changing a potential outcome on a null set (which changes
neither the observed law nor the average treatment effect) preserves the hypothesis. -/
def BinaryOutcome (μ : Measure Ω) : Prop := ∀ z d, ∀ᵐ ω ∂μ, M.Y z d ω = 0 ∨ M.Y z d ω = 1

/-- Pointwise binary outcomes are binary almost surely. -/
theorem BinaryOutcome.of_forall (h : ∀ z d ω, M.Y z d ω = 0 ∨ M.Y z d ω = 1) :
    M.BinaryOutcome μ :=
  fun z d ↦ Filter.Eventually.of_forall (h z d)

/-- The potential outcome `Y false d` read as a boolean: `true` when it equals `1`. The
instrument value `false` is a convention; under the exclusion restriction `Y true d = Y false d`
almost surely. -/
noncomputable def outcomeBool (d : Bool) (ω : Ω) : Bool := decide (M.Y false d ω = 1)

/-- The compliance and response type `(r_x, r_y)` of the unit `ω`: `r_x` codes the pair of
potential treatments `(D false ω, D true ω)` and `r_y` codes the pair of potential outcomes
`(Y false false ω, Y false true ω)`, both through `typeCode`, so that
`respond r_x z = D z ω` and, for binary outcomes, `respond r_y x = true` exactly when
`Y false x ω = 1`. -/
noncomputable def typeOf (ω : Ω) : Fin 4 × Fin 4 :=
  (typeCode (M.D false ω) (M.D true ω), typeCode (M.outcomeBool false ω) (M.outcomeBool true ω))

theorem measurable_outcomeBool (d : Bool) : Measurable (M.outcomeBool d) := by
  refine measurable_to_bool ?_
  have h : M.outcomeBool d ⁻¹' {true} = M.Y false d ⁻¹' {1} := by
    ext ω; simp [outcomeBool]
  rw [h]
  exact M.measurable_Y false d (measurableSet_singleton 1)

theorem measurable_typeOf : Measurable M.typeOf := by
  have h : M.typeOf = (fun w : Bool × Bool × Bool × Bool ↦
      (typeCode w.1 w.2.1, typeCode w.2.2.1 w.2.2.2)) ∘
      fun ω ↦ (M.D false ω, M.D true ω, M.outcomeBool false ω, M.outcomeBool true ω) := rfl
  rw [h]
  exact (measurable_of_countable _).comp ((M.measurable_D false).prodMk
    ((M.measurable_D true).prodMk
      ((M.measurable_outcomeBool false).prodMk (M.measurable_outcomeBool true))))

/-- The probability of a set of types is the sum of the probabilities of its members. -/
theorem measureReal_preimage_typeOf [IsFiniteMeasure μ] (T : Finset (Fin 4 × Fin 4)) :
    μ.real (M.typeOf ⁻¹' ↑T) = ∑ s ∈ T, μ.real (M.typeOf ⁻¹' {s}) := by
  rw [measureReal_def, ← sum_measure_preimage_singleton T
      (fun s _ ↦ M.measurable_typeOf (measurableSet_singleton s)),
    ENNReal.toReal_sum (fun s _ ↦ measure_ne_top μ _)]
  rfl

/-- The law of the compliance and response type of a unit: the weight of `(j, k)` is
`μ(typeOf = (j, k))`. -/
noncomputable def responseLaw (μ : Measure Ω) [IsProbabilityMeasure μ] : Weights where
  mass s := μ.real (M.typeOf ⁻¹' {s})
  nonneg _ := measureReal_nonneg
  sum_eq_one := by
    rw [← M.measureReal_preimage_typeOf Finset.univ, Finset.coe_univ, Set.preimage_univ,
      probReal_univ]

theorem responseLaw_apply [IsProbabilityMeasure μ] (s : Fin 4 × Fin 4) :
    M.responseLaw μ s = μ.real (M.typeOf ⁻¹' {s}) := rfl

/-- The probability that the type satisfies a predicate `P` is the total weight of `P` under
the law of the type. -/
theorem measureReal_typeOf_setOf [IsProbabilityMeasure μ] (P : Fin 4 × Fin 4 → Prop)
    [DecidablePred P] :
    μ.real {ω | P (M.typeOf ω)} = ∑ s, if P s then M.responseLaw μ s else 0 := by
  have h : {ω | P (M.typeOf ω)} = M.typeOf ⁻¹' ↑(Finset.univ.filter P) := by ext; simp
  rw [h, measureReal_preimage_typeOf, Finset.sum_filter]
  rfl

/-- **The law of the response type generates the observed law.** Assume the exclusion
restriction, instrument independence, binary outcomes and `P(Z = z) ≠ 0`. Then
`P(Dobs = x, Yobs = y | Z = z)` (with `y` coded `0` or `1`) is the entry `obs q y x z` of the
observable induced by the law `q` of the compliance and response type: the observed conditional
law of the model is `R q` in the notation of Pearl (2009, Section 8.2.3). -/
theorem obs_responseLaw [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hB : M.BinaryOutcome μ) {z : Bool}
    (hz : μ (M.instrumentEq z) ≠ 0) (y x : Bool) :
    (μ[|M.instrumentEq z]).real {ω | M.Dobs ω = x ∧ M.Yobs ω = boolToReal y} =
      obs (M.responseLaw μ) y x z := by
  have h1 := M.cond_obs_event hI hz x (measurableSet_singleton (boolToReal y))
  have hset : {ω | M.Dobs ω = x ∧ M.Yobs ω = boolToReal y} =
      {ω | M.Dobs ω = x ∧ M.Yobs ω ∈ ({boolToReal y} : Set ℝ)} := rfl
  have hae : {ω | M.D z ω = x ∧ M.Y z x ω ∈ ({boolToReal y} : Set ℝ)} =ᵐ[μ]
      {ω | respond (M.typeOf ω).1 z = x ∧ respond (M.typeOf ω).2 x = y} := by
    filter_upwards [hE.ae_eq z false x, hB false x] with ω hω hb
    cases z <;> cases x <;> cases y <;> rcases hb with hb | hb <;>
      simp [typeOf, outcomeBool, hω, hb]
  rw [measureReal_def, hset, h1, measure_congr hae, ← measureReal_def,
    M.measureReal_typeOf_setOf fun s ↦ respond s.1 z = x ∧ respond s.2 x = y]
  rfl

/-- **The average causal effect of the response law is the average treatment effect.** Under
the exclusion restriction and binary outcomes, `ace q = E[Y z 1 - Y z 0]` for the law `q` of
the compliance and response type and either instrument value `z`. -/
theorem ace_responseLaw [IsProbabilityMeasure μ] (hE : M.Exclusion μ) (hB : M.BinaryOutcome μ)
    (z : Bool) : ace (M.responseLaw μ) = M.ate μ z := by
  have hs : ∀ d, MeasurableSet {ω | respond (M.typeOf ω).2 d = true} := fun d ↦
    M.measurable_typeOf
      (Set.to_countable {s : Fin 4 × Fin 4 | respond s.2 d = true}).measurableSet
  have h : ∀ d, M.Y z d =ᵐ[μ] {ω | respond (M.typeOf ω).2 d = true}.indicator 1 := by
    intro d
    filter_upwards [hE.ae_eq z false d, hB false d] with ω hω hb
    rcases hb with hb | hb <;> cases d <;>
      simp [Set.indicator, typeOf, outcomeBool, hω, hb]
  have hint : ∀ d, Integrable (M.Y z d) μ := fun d ↦
    ((integrable_const (1 : ℝ)).indicator (hs d)).congr (h d).symm
  have hY : ∀ d, ∫ ω, M.Y z d ω ∂μ = μ.real {ω | respond (M.typeOf ω).2 d = true} := by
    intro d
    rw [integral_congr_ae (h d), integral_indicator_one (hs d)]
  simp only [ate, effect]
  rw [integral_sub (hint true) (hint false), hY, hY,
    M.measureReal_typeOf_setOf fun s ↦ respond s.2 true = true,
    M.measureReal_typeOf_setOf fun s ↦ respond s.2 false = true, ace_eq]
  simp [Fintype.sum_prod_type, Fin.sum_univ_four]
  ring

end IVModel

/-! ### Realizing a response-type law by an `IVModel` -/

namespace IVResponse

open IVModel

/-- The probability `P(Z = z)` of an instrument with `P(z1) = π`. -/
def instrumentWeight (π : ℝ) (z : Bool) : ℝ := if z then π else 1 - π

/-- The law of an instrument with `P(z1) = π`, for `0 ≤ π ≤ 1`. -/
def instrumentDist {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) : FiniteDist Bool where
  mass := instrumentWeight π
  nonneg z := by cases z <;> simp [instrumentWeight] <;> linarith
  sum_eq_one := by simp [instrumentWeight]

/-- The sample space of the realization: an instrument value and a compliance and response
type. -/
abbrev RealSpace : Type := Bool × (Fin 4 × Fin 4)

/-- The law of the realization: the instrument, with `P(z1) = π`, is drawn independently of the
type, whose law is `q`. -/
noncomputable def realMeasure (q : Weights) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    Measure RealSpace :=
  (instrumentDist h0 h1).toMeasure.prod q.toMeasure

instance (q : Weights) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    IsProbabilityMeasure (realMeasure q h0 h1) := by
  unfold realMeasure; infer_instance

/-- The `IVModel` realizing the response-type model: the instrument is the first coordinate,
a unit of type `(j, k)` takes the treatment `respond j z` under the instrument value `z` and
has outcome `1` under treatment `d` exactly when `respond k d = true`, whatever `z`. -/
def realModel : IVModel RealSpace where
  Z := Prod.fst
  D z ω := respond ω.2.1 z
  Y _ d ω := boolToReal (respond ω.2.2 d)
  measurable_Z := measurable_fst
  measurable_D _ := measurable_of_countable _
  measurable_Y _ _ := measurable_of_countable _

variable (q : Weights) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1)

theorem realModel_exclusion (μ : Measure RealSpace) : realModel.Exclusion μ :=
  fun _ ↦ Filter.EventuallyEq.rfl

theorem realModel_independence : realModel.InstrumentIndependence (realMeasure q h0 h1) :=
  indepFun_prod (X := id) (Y := fun t ↦ realModel.potentials (true, t)) measurable_id
    (measurable_of_countable _)

theorem realModel_binaryOutcome (μ : Measure RealSpace) : realModel.BinaryOutcome μ :=
  BinaryOutcome.of_forall _ fun _ d ω ↦ by
    cases respond ω.2.2 d <;> simp [realModel, boolToReal]

/-- In the realization `P(Z = z)` is `π` for `z = z1` and `1 - π` for `z = z0`. -/
theorem realMeasure_instrumentEq (z : Bool) :
    (realMeasure q h0 h1).real (realModel.instrumentEq z) = instrumentWeight π z := by
  have hz : realModel.instrumentEq z = ({z} : Set Bool) ×ˢ (Set.univ : Set (Fin 4 × Fin 4)) :=
    (Set.prod_univ).symm
  rw [hz, measureReal_def, realMeasure, Measure.prod_prod, measure_univ, mul_one,
    ← Finset.coe_singleton, FiniteDist.toMeasure_real_finset]
  simp [FiniteDist.prob, instrumentDist]

/-- The type of a unit of the realization is its second coordinate. -/
theorem realModel_typeOf (ω : RealSpace) : realModel.typeOf ω = ω.2 := by
  have ho : ∀ d, realModel.outcomeBool d ω = respond ω.2.2 d := fun d ↦ by
    unfold outcomeBool
    cases h : respond ω.2.2 d <;> simp [realModel, h, boolToReal]
  have hc : ∀ j : Fin 4, typeCode (respond j false) (respond j true) = j := fun j ↦ by
    fin_cases j <;> rfl
  rw [typeOf, ho, ho, hc]
  exact hc ω.2.1 ▸ rfl

/-- **The realization has response law `q`.** -/
theorem realModel_responseLaw : realModel.responseLaw (realMeasure q h0 h1) = q := by
  ext s
  have hs : realModel.typeOf ⁻¹' {s} = (Set.univ : Set Bool) ×ˢ ({s} : Set (Fin 4 × Fin 4)) := by
    ext ω; simp [realModel_typeOf]
  rw [responseLaw_apply, hs, measureReal_def, realMeasure, Measure.prod_prod, measure_univ,
    one_mul, ← Finset.coe_singleton, FiniteDist.toMeasure_real_finset]
  simp [FiniteDist.prob]

/-- **Realization of a response-type law** (the converse of `IVModel.obs_responseLaw`). For
every weight `q` on the sixteen compliance and response types and every `0 ≤ π ≤ 1`, the model
`realModel` under the law `realMeasure q`, in which the instrument with `P(z1) = π` is drawn
independently of a type with law `q`, satisfies the exclusion restriction, instrument
independence and binary outcomes, has `P(Z = z1) = π`, response law `q` and average treatment
effect `ace q`. For `0 < π < 1` both instrument arms have positive probability, so its observed
conditional law is `obs q` (`IVModel.obsTable_realModel` in `BalkePearl.lean`). -/
theorem realModel_spec :
    realModel.Exclusion (realMeasure q h0 h1) ∧
      realModel.InstrumentIndependence (realMeasure q h0 h1) ∧
      realModel.BinaryOutcome (realMeasure q h0 h1) ∧
      (realMeasure q h0 h1).real (realModel.instrumentEq true) = π ∧
      realModel.responseLaw (realMeasure q h0 h1) = q ∧
      ∀ z, realModel.ate (realMeasure q h0 h1) z = ace q := by
  refine ⟨realModel_exclusion _, realModel_independence q h0 h1, realModel_binaryOutcome _,
    by rw [realMeasure_instrumentEq]; rfl, realModel_responseLaw q h0 h1, fun z ↦ ?_⟩
  rw [← realModel.ace_responseLaw (realModel_exclusion _) (realModel_binaryOutcome _) z,
    realModel_responseLaw]

end IVResponse

end CausalInference
