/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.BalkePearl

/-!
# The effect of treatment on the treated in the response-type model

The effect of treatment on the treated (ETT) of Pearl (2009, *Causality*, 2nd edition,
Section 8.2.5, equations (8.18) to (8.20)), in the binary response-type model of
`CausalInference.IVResponse` with an instrument `Z` drawn independently of the types, with
`P(z1) = π`.

## Main definitions

* `CausalInference.IVResponse.probTreatedGiven`: `P(x1 | z)` of a table.
* `IVResponse.probX1`: `P(x1) = π P(x1 | z1) + (1 - π) P(x1 | z0)`.
* `IVResponse.probOutcomeAndTreated`: `P(Y_{x_d} = y1, X = x1)`.
* `IVResponse.ett`: `ETT = P(Y_{x1} = y1 | x1) - P(Y_{x0} = y1 | x1)` (equation (8.18)).
* `IVResponse.obsJoint`: the observed joint law `P(y, x, z) = P(z) P(y, x | z)`;
  `IVResponse.condTable`, `IVResponse.armMass`, `IVResponse.treatedMass`: its conditional
  table, its instrument arms and its treated mass.

## Main results

* `IVResponse.ett_eq_of_noIntrusion_algebraic`, `IVResponse.ett_mem_Icc_algebraic`: the
  identities in the weights behind (8.20) and (8.19), with both rows read off the structural
  table `obs q`.
* `IVResponse.condTable_obsJoint`: for `0 < π < 1` the conditional table of the observed law is
  the structural table.
* `IVResponse.ett_eq_of_noIntrusion`: identification under no intrusion (equation (8.20)): if
  `0 < π < 1` and the observed law has `P(x1 | z0) = 0`, then
  `ETT = (P(y1 | z1) - P(y1 | z0)) / P(x1 | z1)`.
* `IVResponse.ett_mem_Icc`: the natural bounds (8.19) in terms of the observed law, for
  `0 < π < 1`.
* `IVResponse.ett_not_identified_at_one`, `IVResponse.not_exists_ett_eq_of_obsJoint_at_one`: at
  `π = 1` two populations with no intrusion have the same observed law and effects on the treated
  `1` and `0`, so both instrument arms are needed.
* `IVResponse.ett_pointWeights`: without no intrusion the formula (8.20) can fail.
* `IVResponse.ett_lipid`: for the cholestyramine data of Section 8.2.6, `ETT = 0.465 / 0.612`.
* `IVModel.ett_responseLaw_eq_of_noIntrusion`: (8.20) for an `IVModel` with binary outcomes,
  with the rows taken from its observed conditional law.

The measure-theoretic counterpart of (8.20) for an `IVModel` with real outcomes is
`IVModel.wald_eq_effectTreated` in `LATE.lean`: under one-sided noncompliance the Wald ratio is
the average effect on the treated. It is not repeated here.

## Implementation notes

The printed value `ETT = 0.465 / 0.610 = 0.762` in Section 8.2.6 rounds the compliance rate
`P(x1 | z1) = 0.139 + 0.473 = 0.612` to `0.61` before dividing; from the printed table the exact
value is `0.465 / 0.612 = 0.7598...` (`ett_lipid_bounds`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace CausalInference

namespace IVResponse

/-- `P(x1 | z) = P(y0, x1 | z) + P(y1, x1 | z)` for a table `p`. -/
def probTreatedGiven (p : Observable) (z : Bool) : ℝ := p false true z + p true true z

/-- `P(Y_{x_d} = y1, X = x1)` in the response-type model with weights `q` and an instrument
independent of the types with `P(z1) = π`: the sum over `z` of `P(z)` times the weight of the
types `(j, k)` with `respond j z = true` (treated under `z`) and `respond k d = true` (outcome
`y1` under treatment `d`). -/
def probOutcomeAndTreated (q : Weights) (π : ℝ) (d : Bool) : ℝ :=
  ∑ z, instrumentWeight π z * ∑ s, if respond s.1 z = true ∧ respond s.2 d = true then q s else 0

/-- `P(x1) = π P(x1 | z1) + (1 - π) P(x1 | z0)`. -/
def probX1 (q : Weights) (π : ℝ) : ℝ :=
  π * probTreatedGiven (obs q) true + (1 - π) * probTreatedGiven (obs q) false

/-- **The effect of treatment on the treated** (Pearl 2009, (8.18)):
`ETT = P(Y_{x1} = y1 | x1) - P(Y_{x0} = y1 | x1)`, the difference of the two joint probabilities
`P(Y_{x_d} = y1, X = x1)` divided by `P(x1)`. It is a difference of conditional probabilities
only when `0 ≤ π ≤ 1` and the treated mass `P(x1)` is positive; the theorems below assume
`P(x1) > 0`, and the observational ones `0 < π < 1`. Otherwise Lean's `x / 0 = 0` makes the
quotient meaningless. -/
noncomputable def ett (q : Weights) (π : ℝ) : ℝ :=
  (probOutcomeAndTreated q π true - probOutcomeAndTreated q π false) / probX1 q π

theorem probOutcomeAndTreated_true (q : Weights) (π : ℝ) :
    probOutcomeAndTreated q π true =
      π * (q (1, 1) + q (1, 3) + q (3, 1) + q (3, 3)) +
        (1 - π) * (q (2, 1) + q (2, 3) + q (3, 1) + q (3, 3)) := by
  simp [probOutcomeAndTreated, instrumentWeight, Fintype.sum_prod_type, Fin.sum_univ_four]
  ring

theorem probOutcomeAndTreated_false (q : Weights) (π : ℝ) :
    probOutcomeAndTreated q π false =
      π * (q (1, 2) + q (1, 3) + q (3, 2) + q (3, 3)) +
        (1 - π) * (q (2, 2) + q (2, 3) + q (3, 2) + q (3, 3)) := by
  simp [probOutcomeAndTreated, instrumentWeight, Fintype.sum_prod_type, Fin.sum_univ_four]
  ring

/-- **The algebraic identity behind (8.20)** (Pearl 2009; Bloom 1984). If no type is treated
under `z0` in the structural table `obs q` (`P(x1 | z0) = 0`), `π > 0` and `P(x1 | z1) > 0`, then
`ett q π = (P(y1 | z1) - P(y1 | z0)) / P(x1 | z1)`, where both rows are read off the structural
table `obs q`. This is an identity in the weights, not an identification result: the row `z0`
of `obs q` is observed only when `P(z0) = 1 - π > 0`, and at `π = 1` the effect on the treated is
not determined by the observed law (`ett_not_identified_at_one`). The observational reading,
with `0 < π < 1` and the rows taken from the observed law, is `ett_eq_of_noIntrusion`. Without
no intrusion the identity fails (`ett_pointWeights`). -/
theorem ett_eq_of_noIntrusion_algebraic (q : Weights) {π : ℝ} (hπ : 0 < π)
    (hni : probTreatedGiven (obs q) false = 0) (hpos : 0 < probTreatedGiven (obs q) true) :
    ett q π = itt (obs q) / probTreatedGiven (obs q) true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    weights_nonneg q
  simp only [probTreatedGiven, obs_ftf, obs_ttf, obs_ftt, obs_ttt] at hni hpos
  have e8 : q (2, 0) = 0 := by linarith
  have e9 : q (2, 1) = 0 := by linarith
  have e10 : q (2, 2) = 0 := by linarith
  have e11 : q (2, 3) = 0 := by linarith
  have e12 : q (3, 0) = 0 := by linarith
  have e13 : q (3, 1) = 0 := by linarith
  have e14 : q (3, 2) = 0 := by linarith
  have e15 : q (3, 3) = 0 := by linarith
  have hX : probX1 q π = π * (q (1, 0) + q (1, 2) + q (1, 1) + q (1, 3)) := by
    simp only [probX1, probTreatedGiven, obs_ftf, obs_ttf, obs_ftt, obs_ttt]
    rw [e8, e9, e10, e11, e12, e13, e14, e15]; ring
  rw [ett, hX, probOutcomeAndTreated_true, probOutcomeAndTreated_false]
  simp only [itt, probTreatedGiven, obs_tft, obs_ttt, obs_tff, obs_ttf, obs_ftt]
  simp only [e9, e10, e11, e12, e13, e14, e15]
  rw [div_eq_div_iff (mul_pos hπ (by linarith)).ne' (ne_of_gt (by linarith))]
  ring

/-- **The algebraic inequalities behind the natural bounds (8.19).** For every weight `q` and
`π > 0` with `P(x1) > 0`:
`(P(y1 | z1) - P(y1 | z0)) / (P(x1) / π) - P(y0, x1 | z0) / P(x1) ≤ ETT` and
`ETT ≤ (P(y1 | z1) - P(y1 | z0)) / (P(x1) / π) + P(y1, x1 | z0) / P(x1)`,
with the rows read off the structural table `obs q`. Monotonicity is not assumed. The gaps are
`P(r_x ∈ {2, 3}, r_y ∈ {0, 1}) / P(x1)` and `P(r_x ∈ {2, 3}, r_y ∈ {2, 3}) / P(x1)`: the units
treated under `z0` with untreated outcome `y0`, respectively `y1`.

As for `ett_eq_of_noIntrusion_algebraic`, this is an identity in the weights; the observational
reading, with `0 < π < 1` and the rows taken from the observed law, is `ett_mem_Icc`. The
hypothesis `_hπ` is not used by the proof: with Lean's convention `x / 0 = 0` both sides would
still compare. It is required so that `P(x1) / P(z1)` is a quotient by a positive probability, as
in the printed formula. -/
theorem ett_mem_Icc_algebraic (q : Weights) {π : ℝ} (_hπ : 0 < π) (hX : 0 < probX1 q π) :
    ett q π ∈ Icc (itt (obs q) / (probX1 q π / π) - obs q false true false / probX1 q π)
      (itt (obs q) / (probX1 q π / π) + obs q true true false / probX1 q π) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ :=
    weights_nonneg q
  have hN : probOutcomeAndTreated q π true - probOutcomeAndTreated q π false =
      π * itt (obs q) - obs q false true false + (q (2, 0) + q (2, 1) + q (3, 0) + q (3, 1)) := by
    rw [probOutcomeAndTreated_true, probOutcomeAndTreated_false]
    simp only [itt, obs_tft, obs_ttt, obs_tff, obs_ttf, obs_ftf]
    ring
  have hN' : probOutcomeAndTreated q π true - probOutcomeAndTreated q π false =
      π * itt (obs q) + obs q true true false - (q (2, 2) + q (2, 3) + q (3, 2) + q (3, 3)) := by
    rw [probOutcomeAndTreated_true, probOutcomeAndTreated_false]
    simp only [itt, obs_tft, obs_ttt, obs_tff, obs_ttf]
    ring
  rw [ett, div_div_eq_mul_div, mul_comm (itt (obs q)) π, ← sub_div, ← add_div]
  constructor
  · exact div_le_div_of_nonneg_right (by rw [hN]; linarith) hX.le
  · exact div_le_div_of_nonneg_right (by rw [hN']; linarith) hX.le

/-- The weight with all its mass on the type `s`. -/
def pointWeights (s : Fin 4 × Fin 4) : Weights where
  mass s' := if s' = s then 1 else 0
  nonneg s' := by split_ifs <;> norm_num
  sum_eq_one := by simp

/-- **Without no intrusion, (8.20) fails.** If every unit is an always-taker who is helped by
the treatment (all weight on the type `(3, 1)`), then `P(x1 | z0) = 1`, `P(x1 | z1) = 1` and
`ETT = 1` for every `π`, while `(P(y1 | z1) - P(y1 | z0)) / P(x1 | z1) = 0`. -/
theorem ett_pointWeights (π : ℝ) :
    probTreatedGiven (obs (pointWeights (3, 1))) false = 1 ∧
      probTreatedGiven (obs (pointWeights (3, 1))) true = 1 ∧
      ett (pointWeights (3, 1)) π = 1 ∧
      itt (obs (pointWeights (3, 1))) /
        probTreatedGiven (obs (pointWeights (3, 1))) true = 0 := by
  have hX : probX1 (pointWeights (3, 1)) π = 1 := by
    simp [probX1, probTreatedGiven, obs_ftf, obs_ttf, obs_ftt, obs_ttt, pointWeights]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [probTreatedGiven, obs_ftf, obs_ttf, pointWeights]
  · simp [probTreatedGiven, obs_ftt, obs_ttt, pointWeights]
  · rw [ett, hX, probOutcomeAndTreated_true, probOutcomeAndTreated_false]
    simp [pointWeights]
  · simp [itt, probTreatedGiven, obs_tft, obs_ttt, obs_tff, obs_ttf, pointWeights]

/-! ### The observed law and the observational reading -/

/-- The observed joint law `P(Y = y, X = x, Z = z) = P(z) P(y, x | z)` of the response-type
model with weights `q` and an instrument drawn independently of the types with `P(z1) = π`.
This is everything an observer of `(Z, X, Y)` sees. -/
def obsJoint (q : Weights) (π : ℝ) (y x z : Bool) : ℝ := instrumentWeight π z * obs q y x z

/-- The mass `P(Z = z) = Σ_{y, x} J y x z` of the instrument arm `z` of a joint table `J`. -/
def armMass (J : Bool → Bool → Bool → ℝ) (z : Bool) : ℝ :=
  J false false z + J false true z + J true false z + J true true z

/-- The conditional table `P(y, x | z) = J y x z / P(Z = z)` of a joint table `J`. It is a
genuine conditional probability only when `P(Z = z) > 0`; for an empty arm Lean's convention
`x / 0 = 0` gives the zero row, which carries no information. -/
noncomputable def condTable (J : Bool → Bool → Bool → ℝ) : Observable :=
  fun y x z ↦ J y x z / armMass J z

/-- The total mass `P(X = x1) = Σ_{y, z} J y x1 z` of the treated in a joint table `J`. -/
def treatedMass (J : Bool → Bool → Bool → ℝ) : ℝ :=
  J false true false + J true true false + J false true true + J true true true

/-- The arm masses of the observed law are the instrument probabilities `π` and `1 - π`. -/
theorem armMass_obsJoint (q : Weights) (π : ℝ) (z : Bool) :
    armMass (obsJoint q π) z = instrumentWeight π z := by
  have h := obs_sum q z
  simp only [armMass, obsJoint]
  linear_combination instrumentWeight π z * h

/-- **The rows of the structural table are observed when both arms are.** For `0 < π < 1`, the
conditional table of the observed law is the structural table: `P(y, x | z) = obs q y x z` for
both values of `z`. -/
theorem condTable_obsJoint (q : Weights) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1) :
    condTable (obsJoint q π) = obs q := by
  funext y x z
  have hw : instrumentWeight π z ≠ 0 := by
    cases z <;> simp [instrumentWeight] <;> linarith
  rw [condTable, armMass_obsJoint, obsJoint, mul_div_cancel_left₀ _ hw]

/-- The treated mass of the observed law is `P(x1)`. -/
theorem treatedMass_obsJoint (q : Weights) (π : ℝ) : treatedMass (obsJoint q π) = probX1 q π := by
  simp only [treatedMass, obsJoint, probX1, probTreatedGiven, instrumentWeight]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  ring

/-- **Identification of ETT under no intrusion** (Pearl 2009, Section 8.2.5, (8.20); Bloom
1984). Let `0 < π < 1`, so that both instrument arms are observed, and write `J` for the observed
joint law of `(Z, X, Y)` and `P(y, x | z)` for its conditional table. If no unit is treated under
`z0` (`P(x1 | z0) = 0`) and `P(x1 | z1) > 0`, then
`ETT = (P(y1 | z1) - P(y1 | z0)) / P(x1 | z1)`. Every quantity in the hypotheses and on the right
is a function of the observed law. Both arms are needed: at `π = 1` the conclusion has no
observational content (`ett_not_identified_at_one`). -/
theorem ett_eq_of_noIntrusion (q : Weights) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1)
    (hni : probTreatedGiven (condTable (obsJoint q π)) false = 0)
    (hpos : 0 < probTreatedGiven (condTable (obsJoint q π)) true) :
    ett q π = itt (condTable (obsJoint q π)) /
      probTreatedGiven (condTable (obsJoint q π)) true := by
  rw [condTable_obsJoint q hπ0 hπ1] at hni hpos ⊢
  exact ett_eq_of_noIntrusion_algebraic q hπ0 hni hpos

/-- **Natural bounds on ETT** (Pearl 2009, Section 8.2.5, (8.19)). Let `0 < π < 1`, write `J`
for the observed joint law of `(Z, X, Y)`, `P(y, x | z)` for its conditional table,
`P(x1) = treatedMass J` and `P(z1) = armMass J true`, and assume `P(x1) > 0`. Then
`(P(y1 | z1) - P(y1 | z0)) / (P(x1) / P(z1)) - P(y0, x1 | z0) / P(x1) ≤ ETT` and
`ETT ≤ (P(y1 | z1) - P(y1 | z0)) / (P(x1) / P(z1)) + P(y1, x1 | z0) / P(x1)`.
Monotonicity is not assumed; the bounds are functions of the observed law. -/
theorem ett_mem_Icc (q : Weights) {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1)
    (hX : 0 < treatedMass (obsJoint q π)) :
    ett q π ∈ Icc
      (itt (condTable (obsJoint q π)) /
          (treatedMass (obsJoint q π) / armMass (obsJoint q π) true) -
        condTable (obsJoint q π) false true false / treatedMass (obsJoint q π))
      (itt (condTable (obsJoint q π)) /
          (treatedMass (obsJoint q π) / armMass (obsJoint q π) true) +
        condTable (obsJoint q π) true true false / treatedMass (obsJoint q π)) := by
  rw [treatedMass_obsJoint] at hX ⊢
  rw [condTable_obsJoint q hπ0 hπ1, armMass_obsJoint]
  exact ett_mem_Icc_algebraic q hπ0 hX

/-- **At `π = 1` the effect on the treated is not identified.** Put all weight either on helped
compliers (type `(1, 1)`) or on compliers who always recover (type `(1, 3)`), and let every
unit be encouraged (`π = 1`). Both populations satisfy no intrusion and have `P(x1) = 1`, and
both produce the same observed law (every unit has `Z = z1`, `X = x1`, `Y = y1`), but their
effects on the treated are `1` and `0`. The row `z0` of the structural table, used by
`ett_eq_of_noIntrusion_algebraic`, is not observed. -/
theorem ett_not_identified_at_one :
    obsJoint (pointWeights (1, 1)) 1 = obsJoint (pointWeights (1, 3)) 1 ∧
      probTreatedGiven (obs (pointWeights (1, 1))) false = 0 ∧
      probTreatedGiven (obs (pointWeights (1, 3))) false = 0 ∧
      probX1 (pointWeights (1, 1)) 1 = 1 ∧ probX1 (pointWeights (1, 3)) 1 = 1 ∧
      ett (pointWeights (1, 1)) 1 = 1 ∧ ett (pointWeights (1, 3)) 1 = 0 := by
  have hX1 : probX1 (pointWeights (1, 1)) 1 = 1 := by
    simp [probX1, probTreatedGiven, obs_ftt, obs_ttt, pointWeights]
  have hX3 : probX1 (pointWeights (1, 3)) 1 = 1 := by
    simp [probX1, probTreatedGiven, obs_ftt, obs_ttt, pointWeights]
  refine ⟨?_, ?_, ?_, hX1, hX3, ?_, ?_⟩
  · funext y x z
    cases y <;> cases x <;> cases z <;>
      simp [obsJoint, instrumentWeight, obs_fff, obs_fft, obs_ftf, obs_ftt, obs_tff, obs_tft,
        obs_ttf, obs_ttt, pointWeights]
  · simp [probTreatedGiven, obs_ftf, obs_ttf, pointWeights]
  · simp [probTreatedGiven, obs_ftf, obs_ttf, pointWeights]
  · rw [ett, hX1, probOutcomeAndTreated_true, probOutcomeAndTreated_false]
    simp [pointWeights]
  · rw [ett, hX3, probOutcomeAndTreated_true, probOutcomeAndTreated_false]
    simp [pointWeights]

/-- No function of the observed law gives the effect on the treated at `π = 1`, even among
populations with no intrusion and `P(x1) > 0`. -/
theorem not_exists_ett_eq_of_obsJoint_at_one :
    ¬ ∃ F : (Bool → Bool → Bool → ℝ) → ℝ, ∀ q : Weights,
      probTreatedGiven (obs q) false = 0 → 0 < probX1 q 1 → ett q 1 = F (obsJoint q 1) := by
  rintro ⟨F, hF⟩
  obtain ⟨hJ, hn1, hn3, hX1, hX3, he1, he3⟩ := ett_not_identified_at_one
  have h1 := hF _ hn1 (by rw [hX1]; norm_num)
  have h3 := hF _ hn3 (by rw [hX3]; norm_num)
  rw [he1, hJ] at h1
  rw [he3, ← h1] at h3
  norm_num at h3

/-- **ETT for the cholestyramine data** (Pearl 2009, Section 8.2.6). If both instrument arms
are observed (`0 < π < 1`; the trial randomized into two groups of roughly equal size) and the
conditional table of the observed law is the printed table `lipid`, then there is no intrusion
(`P(x1 | z0) = 0`) and `ETT = 0.465 / 0.612`. -/
theorem ett_lipid {q : Weights} {π : ℝ} (hπ0 : 0 < π) (hπ1 : π < 1)
    (hq : condTable (obsJoint q π) = lipid) :
    ett q π = 465 / 612 := by
  rw [ett_eq_of_noIntrusion q hπ0 hπ1 (by rw [hq]; norm_num [probTreatedGiven, lipid, mkTable])
      (by rw [hq]; norm_num [probTreatedGiven, lipid, mkTable]), hq]
  norm_num [itt, probTreatedGiven, lipid, mkTable]

/-- The value `0.465 / 0.612` lies in `(0.759, 0.760)`, and for `P(z1) = 1/2` (the printed
value) some weight has observed conditional table `lipid`, so `ett_lipid` is not vacuous. The
printed `0.762` comes from rounding `0.612` to `0.61`: `0.465 / 0.61 > 0.762`. -/
theorem ett_lipid_bounds :
    (∃ q : Weights, condTable (obsJoint q (1 / 2)) = lipid) ∧
      759 / 1000 < (465 / 612 : ℝ) ∧ (465 / 612 : ℝ) < 760 / 1000 ∧
      762 / 1000 < (465 / 610 : ℝ) := by
  obtain ⟨q, hq⟩ := exists_obs_eq binaryIVConstraints_lipid
  exact ⟨⟨q, by rw [condTable_obsJoint q (by norm_num) (by norm_num), hq]⟩, by norm_num,
    by norm_num, by norm_num⟩

end IVResponse

/-! ### The effect on the treated of an `IVModel` with binary outcomes -/

namespace IVModel

open IVResponse

variable {Ω : Type*} [MeasurableSpace Ω] (M : IVModel Ω) {μ : Measure Ω}

/-- **Identification of ETT for an `IVModel`** (Pearl 2009, (8.20)). Assume the exclusion
restriction, instrument independence, binary outcomes and `P(Z = z) ≠ 0` for both `z` (that is,
`0 < P(z1) < 1`). If the observed conditional law has `P(Dobs = 1 | Z = 0) = 0` and
`P(Dobs = 1 | Z = 1) > 0`, then the effect on the treated of the law of the response type, with
`π = P(Z = 1)`, is the observed ratio `(P(y1 | z1) - P(y1 | z0)) / P(x1 | z1)`. Both rows come
from the observed law through `obsTable_eq`. -/
theorem ett_responseLaw_eq_of_noIntrusion [IsProbabilityMeasure μ] (hE : M.Exclusion μ)
    (hI : M.InstrumentIndependence μ) (hB : M.BinaryOutcome μ)
    (h₁ : μ (M.instrumentEq true) ≠ 0) (h₀ : μ (M.instrumentEq false) ≠ 0)
    (hni : probTreatedGiven (M.obsTable μ) false = 0)
    (hpos : 0 < probTreatedGiven (M.obsTable μ) true) :
    ett (M.responseLaw μ) (μ.real (M.instrumentEq true)) =
      itt (M.obsTable μ) / probTreatedGiven (M.obsTable μ) true := by
  rw [M.obsTable_eq hE hI hB h₁ h₀] at hni hpos ⊢
  exact ett_eq_of_noIntrusion_algebraic _ (lt_of_le_of_ne measureReal_nonneg
    (Ne.symm fun h ↦ h₁ ((measureReal_eq_zero_iff).1 h))) hni hpos

end IVModel

end CausalInference
