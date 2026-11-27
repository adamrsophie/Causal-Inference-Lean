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

## Main results

* `IVResponse.ett_eq_of_noIntrusion`: identification under no intrusion (equation (8.20)): if
  `P(x1 | z0) = 0` then `ETT = (P(y1 | z1) - P(y1 | z0)) / P(x1 | z1)`.
* `IVResponse.ett_mem_Icc`: the natural bounds (8.19),
  `ETT ≥ (P(y1 | z1) - P(y1 | z0)) / (P(x1) / P(z1)) - P(y0, x1 | z0) / P(x1)` and
  `ETT ≤ (P(y1 | z1) - P(y1 | z0)) / (P(x1) / P(z1)) + P(y1, x1 | z0) / P(x1)`.
* `IVResponse.ett_pointWeights`: without no intrusion the formula (8.20) can fail.
* `IVResponse.ett_lipid`: for the cholestyramine data of Section 8.2.6, `ETT = 0.465 / 0.612`.

The measure-theoretic counterpart of (8.20) for an `IVModel` with real outcomes is
`IVModel.wald_eq_effectTreated` in `LATE.lean`: under one-sided noncompliance the Wald ratio is
the average effect on the treated. It is not repeated here.

## Implementation notes

The printed value `ETT = 0.465 / 0.610 = 0.762` in Section 8.2.6 rounds the compliance rate
`P(x1 | z1) = 0.139 + 0.473 = 0.612` to `0.61` before dividing; from the printed table the exact
value is `0.465 / 0.612 = 0.7598...` (`ett_lipid_bounds`).
-/

@[expose] public section

open Set

namespace CausalInference

namespace IVResponse

/-- `P(x1 | z) = P(y0, x1 | z) + P(y1, x1 | z)` for a table `p`. -/
def probTreatedGiven (p : Observable) (z : Bool) : ℝ := p false true z + p true true z

/-- The probability `P(Z = z)` of an instrument with `P(z1) = π`. -/
def instrumentWeight (π : ℝ) (z : Bool) : ℝ := if z then π else 1 - π

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
`P(Y_{x_d} = y1, X = x1)` divided by `P(x1)`. The theorems below assume `P(x1) > 0`, so the
quotient is a genuine conditional probability. -/
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

/-- **Identification of ETT under no intrusion** (Pearl 2009, (8.20); Bloom 1984). If no unit
is treated under `z0` (`P(x1 | z0) = 0`), `P(z1) = π > 0` and `P(x1 | z1) > 0`, then
`ETT = (P(y1 | z1) - P(y1 | z0)) / P(x1 | z1)`. The identity holds for every `π > 0`; only
`π ≤ 1` makes `1 - π` the probability of `z0`. Without no intrusion it fails
(`ett_pointWeights`). -/
theorem ett_eq_of_noIntrusion (q : Weights) {π : ℝ} (hπ : 0 < π)
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

/-- **Natural bounds on ETT** (Pearl 2009, (8.19)). For every weight `q` and instrument
probability `P(z1) = π > 0` with `P(x1) > 0`:
`(P(y1 | z1) - P(y1 | z0)) / (P(x1) / P(z1)) - P(y0, x1 | z0) / P(x1) ≤ ETT` and
`ETT ≤ (P(y1 | z1) - P(y1 | z0)) / (P(x1) / P(z1)) + P(y1, x1 | z0) / P(x1)`.
Monotonicity is not assumed. The gaps are `P(r_x ∈ {2, 3}, r_y ∈ {0, 1}) / P(x1)` and
`P(r_x ∈ {2, 3}, r_y ∈ {2, 3}) / P(x1)`: the units treated under `z0` with untreated outcome
`y0`, respectively `y1`.

As in `ett_eq_of_noIntrusion`, only `π ≤ 1` makes `1 - π` a probability; the inequalities hold for
every `π > 0`. The hypothesis `_hπ` is not used by the proof: with Lean's convention `x / 0 = 0`
both sides would still compare. It is required so that `P(x1) / P(z1)` is a quotient by a positive
probability, as in the printed formula. -/
theorem ett_mem_Icc (q : Weights) {π : ℝ} (_hπ : 0 < π) (hX : 0 < probX1 q π) :
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

/-- **ETT for the cholestyramine data** (Pearl 2009, Section 8.2.6). For every weight inducing
the printed table `lipid` and every instrument probability `π > 0`, there is no intrusion
(`P(x1 | z0) = 0`) and `ETT = 0.465 / 0.612`. -/
theorem ett_lipid {q : Weights} (hq : obs q = lipid) {π : ℝ} (hπ : 0 < π) :
    ett q π = 465 / 612 := by
  rw [ett_eq_of_noIntrusion q hπ (by rw [hq]; norm_num [probTreatedGiven, lipid, mkTable])
      (by rw [hq]; norm_num [probTreatedGiven, lipid, mkTable]), hq]
  norm_num [itt, probTreatedGiven, lipid, mkTable]

/-- The value `0.465 / 0.612` lies in `(0.759, 0.760)`, and some weight induces the table
`lipid`, so `ett_lipid` is not vacuous. The printed `0.762` comes from rounding `0.612` to
`0.61`: `0.465 / 0.61 > 0.762`. -/
theorem ett_lipid_bounds :
    (∃ q : Weights, obs q = lipid) ∧ 759 / 1000 < (465 / 612 : ℝ) ∧ (465 / 612 : ℝ) < 760 / 1000 ∧
      762 / 1000 < (465 / 610 : ℝ) :=
  ⟨exists_obs_eq binaryIVConstraints_lipid, by norm_num, by norm_num, by norm_num⟩

end IVResponse

end CausalInference
