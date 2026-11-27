/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Tactic.NormNum
public import CausalInference.Attribution.Bounds

/-!
# Worked examples of probabilities of causation

The numerical examples of Pearl (2009), Section 9.3, and of the Primer, Section 4.5.1, checked
by computation in the response-type model of `CausalInference.Attribution.Definitions`.

## Main results

* Example 9.3.1 (betting against a fair coin): `coinBet_pY`, `coinBet_condY` and the values
  `PN = PS = 1`, `PNS = 1/2` of `CausalInference.Attribution.Bounds`; the bookie model gives
  the same data with `PN = PS = PNS = 0`.
* Example 9.3.2 (the firing squad): `firingSquad` has `P(y_x) = 1`, `P(y_x') = 1/2`,
  `PNS = 1/2`, `PN = 0`, `PS = 1`; it is monotonic but not exogenous, and the formulas (9.29),
  (9.30) of Theorem 9.2.15 give back `PN` and `PS` from the data (equations (9.42), (9.43)).
* Example 9.3.3 (radiation and leukemia, Table 9.1): under exogeneity and monotonicity, the
  exact values `PNS = 33211/204111908`, `PN = 33211/88539`, `PS = 33211/204056580`
  (`radiation_pns`, `radiation_pn`, `radiation_ps`), with a model realizing the data. The book
  prints the rounded values `0.0001625`, `0.37535` and `37.544%`; the exact values are
  approximately `0.00016271`, `0.37510`, `0.00016275` (`radiation_pn_bounds`).
* Failure cases: the coin bet model is exogenous but not monotonic, and the formulas (9.21),
  (9.28), (9.29) fail in it (`coinBet_pns_ne`, `coinBet_pn_ne`); the firing squad is monotonic
  but not exogenous, and (9.21), (9.11) fail in it (`firingSquad_pns_ne`, `firingSquad_pn_ne`).
* Example 9.3.4 (legal responsibility, Table 9.2; Primer Example 4.5.1, Table 4.5): every model
  compatible with the experimental and observational data has `PN = 1`, without assuming
  monotonicity (`legal_pn_eq_one`); the data are realized by a model (`legalModel`); the
  experimental excess risk ratio is `0.125` (`legal_experimental_err`), and the Primer's
  decomposition (4.41) reads `ERR + CF = -13 + 14 = 1` (`legal_err`, `legal_cf`).

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press,
  2009, Section 9.3.
* J. Pearl, M. Glymour, N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley, 2016,
  Section 4.5.1, Example 4.5.1.
-/

@[expose] public section

namespace CausalInference

namespace Attribution

namespace ResponseModel

/-! ### Example 9.3.1: betting against a fair coin -/

/-- In the coin bet model, `P(y_x) = P(y_x') = P(y) = 1/2`. -/
theorem coinBet_pY : coinBet.pY1 = 1 / 2 ∧ coinBet.pY0 = 1 / 2 ∧ coinBet.pY = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [coinBet, pY1_eq, pY0_eq, pY_eq, pXY_true_true, pXY_false_true] <;> norm_num

/-- In the coin bet model, `P(y | x) = P(y | x') = 1/2`. -/
theorem coinBet_condY : coinBet.condY true = 1 / 2 ∧ coinBet.condY false = 1 / 2 := by
  refine ⟨?_, ?_⟩ <;>
    simp [coinBet, condY, pXY_true_true, pXY_false_true, pX_true, pX_false] <;> norm_num

/-! ### Example 9.3.2: the firing squad -/

/-- The firing squad of Pearl (2009), Example 9.3.2. The court order `U` is a fair coin;
rifleman `A` shoots (`X`) exactly when ordered; the prisoner dies (`Y`) if `A` or `B` shoots,
and `B` shoots exactly when ordered. So `Y1 = 1` and `Y0 = U = X`: the cell
`(X, Y0, Y1) = (1, 1, 1)` and the cell `(0, 0, 1)` each have mass `1/2`. -/
noncomputable def firingSquad : ResponseModel :=
  ofCells (fun x y0 y1 => if y1 = true ∧ y0 = x then 1 / 2 else 0)
    (by intro x y0 y1; split_ifs <;> norm_num) (by norm_num)

/-- Equation (9.37): `P(y_x) = 1`. -/
theorem firingSquad_pY1 : firingSquad.pY1 = 1 := by
  simp [firingSquad, pY1_eq]; norm_num

/-- Equation (9.38): `P(y_x') = 1/2`. -/
theorem firingSquad_pY0 : firingSquad.pY0 = 1 / 2 := by
  simp [firingSquad, pY0_eq]

/-- Equation (9.39): `PNS = 1/2`. -/
theorem firingSquad_pns : firingSquad.PNS = 1 / 2 := by
  simp [firingSquad, pns_eq]

/-- `PN = 0`: rifleman `A`'s shot was not necessary for the death. -/
theorem firingSquad_pn : firingSquad.PN = 0 := by
  simp [firingSquad, pn_eq]

/-- `PS = 1`: rifleman `A`'s shot would have been sufficient. -/
theorem firingSquad_ps : firingSquad.PS = 1 := by
  simp [firingSquad, ps_eq, pXY_false_false]

theorem firingSquad_monotonic : firingSquad.Monotonic := by
  intro x; cases x <;> simp [firingSquad]

/-- The firing squad is not exogenous: `P(y | x') = 0` while `P(y_x') = 1/2`. -/
theorem not_exogenous_firingSquad : ¬ firingSquad.Exogenous := fun h => by
  have hx' : 0 < firingSquad.pX false := by simp [firingSquad, pX_false]
  have := firingSquad.condY_false_of_exogenous h hx'
  rw [firingSquad_pY0] at this
  simp [firingSquad, condY, pXY_false_true] at this

/-- Equations (9.42), (9.43): the monotone formulas (9.29), (9.30) applied to the data
`P(x, y) = P(x', y') = 1/2`, `P(y_x) = 1`, `P(y_x') = 1/2` give `PN = 0` and `PS = 1`. -/
theorem firingSquad_formulas :
    (firingSquad.pY - firingSquad.pY0) / firingSquad.pXY true true = 0 ∧
      (firingSquad.pY1 - firingSquad.pY) / firingSquad.pXY false false = 1 := by
  have h11 : 0 < firingSquad.pXY true true := by simp [firingSquad, pXY_true_true]
  have h00 : 0 < firingSquad.pXY false false := by simp [firingSquad, pXY_false_false]
  rw [← firingSquad.pn_eq_of_monotonic firingSquad_monotonic h11,
    ← firingSquad.ps_eq_of_monotonic firingSquad_monotonic h00]
  exact ⟨firingSquad_pn, firingSquad_ps⟩

/-! ### Example 9.3.3: radiation and leukemia (Table 9.1) -/

/-- Under exogeneity and monotonicity, the data of Table 9.1 (`P(y | x) = 30/69160`,
`P(y | x') = 16/59026`) give `PNS = 33211/204111908` (equation (9.45), exact value). -/
theorem radiation_pns (m : ResponseModel) (hexo : m.Exogenous) (hmono : m.Monotonic)
    (hx : 0 < m.pX true) (hx' : 0 < m.pX false) (hT : m.condY true = 30 / 69160)
    (hF : m.condY false = 16 / 59026) : m.PNS = 33211 / 204111908 := by
  rw [m.pns_eq_of_exogenous_of_monotonic hexo hmono hx hx', hT, hF]; norm_num

/-- Under exogeneity and monotonicity, the data of Table 9.1 give `PN = 33211/88539`
(equation (9.46), exact value). -/
theorem radiation_pn (m : ResponseModel) (hexo : m.Exogenous) (hmono : m.Monotonic)
    (h11 : 0 < m.pXY true true) (hx' : 0 < m.pX false) (hT : m.condY true = 30 / 69160)
    (hF : m.condY false = 16 / 59026) : m.PN = 33211 / 88539 := by
  rw [m.pn_eq_of_exogenous_of_monotonic hexo hmono h11 hx', hT, hF]; norm_num

/-- Under exogeneity and monotonicity, the data of Table 9.1 give `PS = 33211/204056580`
(equation (9.47), exact value). -/
theorem radiation_ps (m : ResponseModel) (hexo : m.Exogenous) (hmono : m.Monotonic)
    (h00 : 0 < m.pXY false false) (hx : 0 < m.pX true) (hT : m.condY true = 30 / 69160)
    (hF : m.condY false = 16 / 59026) : m.PS = 33211 / 204056580 := by
  rw [m.ps_eq_of_exogenous_of_monotonic hexo hmono h00 hx, hT, hF]; norm_num

/-- The exact value of `PN` in Example 9.3.3 lies strictly between `0.3750` and `0.3752`, so
the printed `0.37535` is a rounding slip. -/
theorem radiation_pn_bounds : (0.3750 : ℝ) < 33211 / 88539 ∧ (33211 : ℝ) / 88539 < 0.3752 := by
  norm_num

/-- The response-type law of the radiation witness: monotone, with
`P(Y0 = 1, Y1 = 1) = 16/59026` and `P(Y0 = 0, Y1 = 1) = 30/69160 - 16/59026`. -/
noncomputable def radiationTypes : Bool → Bool → ℝ
  | false, true => 30 / 69160 - 16 / 59026
  | true, true => 16 / 59026
  | true, false => 0
  | false, false => 1 - 30 / 69160

/-- A model realizing the hypotheses of `radiation_pns`, `radiation_pn`, `radiation_ps`: `X`
is a fair coin independent of the response type `radiationTypes`. -/
noncomputable def radiationModel : ResponseModel :=
  ofCells (fun _ y0 y1 => radiationTypes y0 y1 / 2)
    (by intro x y0 y1; cases y0 <;> cases y1 <;> simp [radiationTypes] <;> norm_num)
    (by simp [radiationTypes]; norm_num)

theorem radiationModel_hyps : radiationModel.Exogenous ∧ radiationModel.Monotonic ∧
    0 < radiationModel.pXY true true ∧ 0 < radiationModel.pXY false false ∧
    radiationModel.condY true = 30 / 69160 ∧ radiationModel.condY false = 16 / 59026 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y0 y1
    cases x <;> cases y0 <;> cases y1 <;>
      simp [radiationModel, pX_true, pX_false, pR_eq, radiationTypes] <;> norm_num
  · intro x; cases x <;> simp [radiationModel, radiationTypes]
  · simp [radiationModel, pXY_true_true, radiationTypes]; norm_num
  · simp [radiationModel, pXY_false_false, radiationTypes]; norm_num
  · simp [radiationModel, condY, pXY_true_true, pX_true, radiationTypes]; norm_num
  · simp [radiationModel, condY, pXY_false_true, pX_false, radiationTypes]; norm_num

/-! ### Example 9.3.4: legal responsibility from combined data (Table 9.2) -/

/-- Pearl (2009), Example 9.3.4, and Primer Example 4.5.1: with the data of Table 9.2
(`P(x, y) = 2/2000`, `P(x', y) = 28/2000` observationally, `P(y_x') = 14/1000`
experimentally), every model has `PN = 1`. No monotonicity is assumed: the lower bound (11.42)
equals one. -/
theorem legal_pn_eq_one (m : ResponseModel) (h11 : m.pXY true true = 1 / 1000)
    (h01 : m.pXY false true = 14 / 1000) (hY0 : m.pY0 = 14 / 1000) : m.PN = 1 := by
  have hpos : 0 < m.pXY true true := by rw [h11]; norm_num
  obtain ⟨hl, hu⟩ := m.pn_mem_Icc_comb hpos
  rw [pY_eq, h11, h01, hY0] at hl
  norm_num at hl
  exact le_antisymm (le_trans hu (min_le_left _ _)) hl

/-- A model realizing the full data of Table 9.2: observationally `P(x, y) = 1/1000`,
`P(x, y') = 499/1000`, `P(x', y) = 14/1000`, `P(x', y') = 486/1000`; experimentally
`P(y_x) = 16/1000`, `P(y_x') = 14/1000`. -/
noncomputable def legalModel : ResponseModel :=
  ofCells
    (fun x y0 y1 => match x, y0, y1 with
      | true, false, true => 1 / 1000
      | true, false, false => 499 / 1000
      | false, true, true => 14 / 1000
      | false, false, true => 1 / 1000
      | false, false, false => 485 / 1000
      | _, _, _ => 0)
    (by intro x y0 y1; cases x <;> cases y0 <;> cases y1 <;> norm_num) (by norm_num)

theorem legalModel_data : legalModel.pXY true true = 1 / 1000 ∧
    legalModel.pXY true false = 499 / 1000 ∧ legalModel.pXY false true = 14 / 1000 ∧
    legalModel.pXY false false = 486 / 1000 ∧ legalModel.pY1 = 16 / 1000 ∧
    legalModel.pY0 = 14 / 1000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [legalModel, pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false,
      pY1_eq, pY0_eq] <;> norm_num

theorem legalModel_pn : legalModel.PN = 1 :=
  legal_pn_eq_one legalModel legalModel_data.1 legalModel_data.2.2.1 legalModel_data.2.2.2.2.2

/-- Equation (9.54): the experimental excess risk ratio
`(P(y_x) - P(y_x')) / P(y_x) = (0.016 - 0.014) / 0.016 = 0.125`. -/
theorem legal_experimental_err :
    ((16 / 1000 : ℝ) - 14 / 1000) / (16 / 1000) = 0.125 := by
  norm_num

/-- Primer equations (4.39), (4.40), (4.41): with `P(x) = P(x') = 1/2`, the observational
excess risk ratio `(P(y | x) - P(y | x')) / P(y | x) = (0.002 - 0.028) / 0.002` equals `-13`. -/
theorem legal_err (m : ResponseModel) (h11 : m.pXY true true = 1 / 1000)
    (h01 : m.pXY false true = 14 / 1000) (hx : m.pX true = 1 / 2) (hx' : m.pX false = 1 / 2) :
    (m.condY true - m.condY false) / m.condY true = -13 := by
  rw [condY, condY, h11, h01, hx, hx']; norm_num

/-- Primer equation (4.41): the confounding factor
`(P(y | x') - P(y_x')) / P(x, y) = (0.028 - 0.014) / 0.001` equals `14`. -/
theorem legal_cf (m : ResponseModel) (h11 : m.pXY true true = 1 / 1000)
    (h01 : m.pXY false true = 14 / 1000) (hx' : m.pX false = 1 / 2)
    (hY0 : m.pY0 = 14 / 1000) :
    (m.condY false - m.pY0) / m.pXY true true = 14 := by
  rw [condY, h01, hx', hY0, h11]; norm_num

/-! ### Failure of the identification formulas outside their assumptions -/

/-- The coin bet model is exogenous (the bet is independent of the coin). -/
theorem coinBet_exogenous : coinBet.Exogenous := by
  intro x y0 y1
  cases x <;> cases y0 <;> cases y1 <;> simp [coinBet, pX_true, pX_false, pR_eq] <;> norm_num

/-- Without monotonicity, the risk difference formula (9.21) and the monotone formula (9.28)
fail even under exogeneity: in the coin bet model `PNS = 1/2`, while
`P(y | x) - P(y | x') = P(y_x) - P(y_x') = 0`. -/
theorem coinBet_pns_ne : coinBet.PNS ≠ coinBet.condY true - coinBet.condY false ∧
    coinBet.PNS ≠ coinBet.pY1 - coinBet.pY0 := by
  rw [coinBet_pns, coinBet_condY.1, coinBet_condY.2, coinBet_pY.1, coinBet_pY.2.1]
  norm_num

/-- Without monotonicity, the formula (9.29) fails even under exogeneity: in the coin bet model
`PN = 1`, while `(P(y) - P(y_x')) / P(x, y) = 0`. -/
theorem coinBet_pn_ne : coinBet.PN ≠ (coinBet.pY - coinBet.pY0) / coinBet.pXY true true := by
  rw [coinBet_pn, coinBet_pY.2.1, coinBet_pY.2.2]
  norm_num

/-- Without exogeneity, the risk difference formula (9.21) fails even under monotonicity: in the
firing squad `PNS = 1/2`, while `P(y | x) - P(y | x') = 1`. -/
theorem firingSquad_pns_ne :
    firingSquad.PNS ≠ firingSquad.condY true - firingSquad.condY false := by
  have hT : firingSquad.condY true = 1 := by
    simp [firingSquad, condY, pXY_true_true, pX_true]
  have hF : firingSquad.condY false = 0 := by
    simp [firingSquad, condY, pXY_false_true]
  rw [firingSquad_pns, hT, hF]
  norm_num

/-- Without exogeneity, the relation (9.11) `PN = PNS / P(y | x)` fails: in the firing squad
`PN = 0`, while `PNS / P(y | x) = 1/2`. -/
theorem firingSquad_pn_ne : firingSquad.PN ≠ firingSquad.PNS / firingSquad.condY true := by
  have hT : firingSquad.condY true = 1 := by
    simp [firingSquad, condY, pXY_true_true, pX_true]
  rw [firingSquad_pn, firingSquad_pns, hT]
  norm_num

end ResponseModel

end Attribution

end CausalInference
