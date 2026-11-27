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
  (`radiation_pns`, `radiation_pn`, `radiation_ps`), with a model realizing all four cells of
  the table (`radiationModel_table`, `radiationModel_hyps`). The book
  prints the rounded values `0.0001625`, `0.37535` and `37.544%`; the exact values are
  approximately `0.00016271`, `0.37510`, `0.00016275` (`radiation_pn_bounds`).
* Failure cases: the coin bet model is exogenous but not monotonic, and the formulas (9.21),
  (9.28), (9.29) fail in it (`coinBet_pns_ne`, `coinBet_pn_ne`); the firing squad is monotonic
  but not exogenous, and (9.21), (9.11) fail in it (`firingSquad_pns_ne`, `firingSquad_pn_ne`).
* Primer Example 4.4.3 and Study Question 4.5.1 (irradiation and remission): `PNS = 1/4`
  under monotonicity (`remission_pns`); with the observational data of the study question and
  unknown treatment prevalence, `PN ≥ 9/70` (`remission_pn_ge`) and the sharp set of `PN` values
  is `[9/70, 1]` (`remission_identifiedSet_pn`); the reading in the solution manual is
  infeasible (`remission_manual_infeasible`).
* Example 9.3.4 (legal responsibility, Table 9.2; Primer Example 4.5.1, Table 4.5): every model
  compatible with the experimental and observational data has `PN = 1`, without assuming
  monotonicity (`legal_pn_eq_one`); the data are realized by a model (`legalModel`); the
  experimental excess risk ratio is `0.125` (`legal_experimental_err`), and the Primer's
  decomposition (4.41) reads `ERR + CF = -13 + 14 = 1` (`legal_err`, `legal_cf`).

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press,
  2009, Section 9.3.
* J. Pearl, M. Glymour, N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley, 2016,
  Example 4.4.3, Section 4.5.1, Example 4.5.1, Study Question 4.5.1.
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

/-- Both conditioning events of the firing squad have positive probability:
`P(x, y) = P(x', y') = 1/2`, so its `PN` and `PS` are genuine conditional probabilities. -/
theorem firingSquad_mem_positiveModels : firingSquad ∈ positiveModels := by
  constructor <;> simp [firingSquad, pXY_true_true, pXY_false_false]

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

theorem radiationTypes_nonneg : ∀ a b, 0 ≤ radiationTypes a b := by
  intro a b; cases a <;> cases b <;> simp [radiationTypes] <;> norm_num

theorem radiationTypes_sum : radiationTypes false false + radiationTypes false true +
    radiationTypes true false + radiationTypes true true = 1 := by
  simp only [radiationTypes]; ring

/-- A model realizing the full Table 9.1 and the hypotheses of `radiation_pns`, `radiation_pn`,
`radiation_ps`: high exposure `X` has the table's margin `P(x) = 69160/128186` and is independent
of the response type `radiationTypes`. -/
noncomputable def radiationModel : ResponseModel :=
  bernModel (69160 / 128186) radiationTypes (by norm_num) (by norm_num) radiationTypes_nonneg
    radiationTypes_sum

/-- `radiationModel` reproduces all four cells of Table 9.1 (total `128186`): deaths `30` and
survivals `69130` under high exposure, deaths `16` and survivals `59010` under low exposure. -/
theorem radiationModel_table : radiationModel.pXY true true = 30 / 128186 ∧
    radiationModel.pXY true false = 69130 / 128186 ∧
    radiationModel.pXY false true = 16 / 128186 ∧
    radiationModel.pXY false false = 59010 / 128186 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [radiationModel, bernModel_w, pXY_true_true, pXY_true_false, pXY_false_true,
      pXY_false_false, radiationTypes] <;> norm_num

theorem radiationModel_hyps : radiationModel.Exogenous ∧ radiationModel.Monotonic ∧
    0 < radiationModel.pXY true true ∧ 0 < radiationModel.pXY false false ∧
    radiationModel.condY true = 30 / 69160 ∧ radiationModel.condY false = 16 / 59026 := by
  obtain ⟨h11, h10, h01, h00⟩ := radiationModel_table
  have hx : radiationModel.pX true = 69160 / 128186 := bernModel_pX_true _ _ _ _
  have hx' : radiationModel.pX false = 59026 / 128186 := by
    linarith [radiationModel.pX_add_pX]
  refine ⟨bernModel_exogenous _ _ _ _, ?_, by rw [h11]; norm_num, by rw [h00]; norm_num, ?_, ?_⟩
  · intro x; simp [radiationModel, bernModel_w, radiationTypes]
  · rw [condY, h11, hx]; norm_num
  · rw [condY, h01, hx']; norm_num

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

/-! ### Primer Example 4.4.3 and Study Question 4.5.1: irradiation and remission

`X = 1` is lumpectomy plus irradiation, `Y = 1` is remission. The randomized trial reports
recurrence in `14%` of irradiated and `39%` of non-irradiated patients, so `P(y_x) = 0.86` and
`P(y_x') = 0.61`. Study Question 4.5.1 adds observational data: `P(y') = 0.3` and
`P(x' | y') = 0.7`, so `P(x', y') = 0.21`, `P(x, y') = 0.09`, `P(y) = 0.7`; the treatment
prevalence is not given, so `d = P(x, y)` ranges over `[0.09, 0.70]` (the lower end is forced
by `P(x', y) ≤ P(y_x')`, see `exists_combObs_eq_iff`).

The published solution manual of the Primer reads the recurrence rates `0.39` and `0.14` as
the remission probabilities `P(y | do(x))` and `P(y | do(x'))` and takes `P(x) = 1`,
obtaining `0.62`. Both steps are inconsistent with the data: `P(y) ≤ P(y_x) + P(y_x')` holds
in every model, while
`0.7 > 0.39 + 0.14` (`remission_manual_infeasible`), and `P(x', y') = 0.21` forces
`P(x) ≤ 0.79`. With the trial read correctly, the lower bound (4.30) is `0.09 / d`, whose least
value over the compatible `d` is `9/70 ≈ 0.129`, and the sharp set of `PN` values is
`[9/70, 1]` (`remission_identifiedSet_pn`). -/

/-- Primer Example 4.4.3, equations (4.26) and (4.42): under monotonicity, the trial gives the
patient facing the decision `PNS = 0.86 - 0.61 = 1/4` (the book writes `0.39 - 0.14 = 0.25`,
the same difference of recurrence rates). -/
theorem remission_pns (m : ResponseModel) (hmono : m.Monotonic) (h1 : m.pY1 = 86 / 100)
    (h0 : m.pY0 = 61 / 100) : m.PNS = 1 / 4 := by
  rw [m.pns_eq_of_monotonic hmono, h1, h0]; norm_num

/-- The reading of Study Question 4.5.1 in the Primer's solution manual is infeasible: no model has
`P(y) = 0.7` with `P(y_x) = 0.39` and `P(y_x') = 0.14`, since `P(y) ≤ P(y_x) + P(y_x')`. -/
theorem remission_manual_infeasible :
    ¬ ∃ m : ResponseModel, m.pY = 7 / 10 ∧ m.pY1 = 39 / 100 ∧ m.pY0 = 14 / 100 := by
  rintro ⟨m, hy, h1, h0⟩
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := m.nonneg_cells
  rw [pY_eq, pXY_true_true, pXY_false_true] at hy
  rw [pY1_eq] at h1
  rw [pY0_eq] at h0
  linarith

/-- Study Question 4.5.1: every model with the trial marginals `P(y_x) = 0.86`,
`P(y_x') = 0.61` and the observational cells `P(x, y') = 0.09`, `P(x', y') = 0.21` (and
`P(x, y) > 0`) has `PN ≥ 9/70`, by the lower bound (4.30), whatever the treatment prevalence. -/
theorem remission_pn_ge (m : ResponseModel) (h11 : 0 < m.pXY true true)
    (h10 : m.pXY true false = 9 / 100) (h00 : m.pXY false false = 21 / 100)
    (h0 : m.pY0 = 61 / 100) : 9 / 70 ≤ m.PN := by
  have hs := m.sum_cells
  have q01 : 0 ≤ m.pXY false true := by
    rw [pXY_false_true]; linarith [m.nonneg false true false, m.nonneg false true true]
  have hsum : m.pXY true true + m.pXY true false + m.pXY false true + m.pXY false false = 1 := by
    rw [pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false]; linarith
  obtain ⟨hl, -⟩ := m.pn_mem_Icc_comb h11
  refine le_trans ?_ (le_trans (le_max_right _ _) hl)
  rw [pY_eq, h0, le_div_iff₀ h11]
  nlinarith

/-- The cells of a monotonic model with the data of Study Question 4.5.1 and `P(x, y) = d`, in
the order `(X, Y0, Y1)`: `(0,0,0) = 0.05`, `(0,0,1) = 0.16`, `(0,1,0) = 0`, `(0,1,1) = 0.70 - d`,
`(1,0,0) = 0.09`, `(1,0,1) = 0.09`, `(1,1,0) = 0`, `(1,1,1) = d - 0.09`. -/
noncomputable def remissionCells (d : ℝ) : Bool → Bool → Bool → ℝ
  | false, false, false => 5 / 100
  | false, false, true => 16 / 100
  | false, true, false => 0
  | false, true, true => 70 / 100 - d
  | true, false, false => 9 / 100
  | true, false, true => 9 / 100
  | true, true, false => 0
  | true, true, true => d - 9 / 100

/-- The model with cells `remissionCells d`, for `0.09 ≤ d ≤ 0.70`. -/
noncomputable def remissionModel (d : ℝ) (hd : d ∈ Set.Icc (9 / 100) (70 / 100)) :
    ResponseModel :=
  ofCells (remissionCells d)
    (by
      obtain ⟨h1, h2⟩ := hd
      intro x y0 y1; cases x <;> cases y0 <;> cases y1 <;> simp only [remissionCells] <;>
        linarith)
    (by simp only [remissionCells]; ring)

/-- `remissionModel d` is monotonic, reproduces the data of Study Question 4.5.1 with
`P(x, y) = d`, and has `PN = 0.09 / d`: the lower bound (4.30) is attained. -/
theorem remissionModel_spec (d : ℝ) (hd : d ∈ Set.Icc (9 / 100) (70 / 100)) :
    (remissionModel d hd).Monotonic ∧ (remissionModel d hd).pXY true true = d ∧
      (remissionModel d hd).pXY true false = 9 / 100 ∧
      (remissionModel d hd).pXY false false = 21 / 100 ∧
      (remissionModel d hd).pY1 = 86 / 100 ∧ (remissionModel d hd).pY0 = 61 / 100 ∧
      (remissionModel d hd).PN = 9 / 100 / d := by
  have e : ∀ x y0 y1, (remissionModel d hd).w x y0 y1 = remissionCells d x y0 y1 :=
    fun _ _ _ => rfl
  refine ⟨fun x => by cases x <;> rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pXY_true_true, e, e]; simp only [remissionCells]; ring
  · rw [pXY_true_false, e, e]; simp only [remissionCells]; norm_num
  · rw [pXY_false_false, e, e]; simp only [remissionCells]; norm_num
  · rw [pY1_eq, e, e, e, e]; simp only [remissionCells]; ring
  · rw [pY0_eq, e, e, e, e]; simp only [remissionCells]; ring
  · rw [pn_eq, pXY_true_true, e, e]; simp only [remissionCells]; ring_nf

/-- The data of Study Question 4.5.1 that do not involve the treatment prevalence:
`(P(x, y'), P(x', y'), P(y_x), P(y_x'))`. -/
noncomputable def remissionObs (m : ResponseModel) : ℝ × ℝ × ℝ × ℝ :=
  (m.pXY true false, m.pXY false false, m.pY1, m.pY0)

/-- Study Question 4.5.1, sharp answer: over all models with `P(x, y) > 0` and the data
`P(x, y') = 0.09`, `P(x', y') = 0.21`, `P(y_x) = 0.86`, `P(y_x') = 0.61` (treatment prevalence
unknown), the set of values of `PN` is exactly `[9/70, 1]`. Every value is attained by a
monotonic model (`remissionModel`). -/
theorem remission_identifiedSet_pn :
    identifiedSet {m | 0 < m.pXY true true} remissionObs PN
      (9 / 100, 21 / 100, 86 / 100, 61 / 100) = Set.Icc (9 / 70) 1 := by
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m, h11, hm, rfl⟩
    simp only [remissionObs, Prod.mk.injEq] at hm
    obtain ⟨h10, h00, -, h0⟩ := hm
    exact ⟨m.remission_pn_ge h11 h10 h00 h0,
      le_trans (m.pn_mem_Icc_comb h11).2 (min_le_left _ _)⟩
  · rintro ⟨hl, hu⟩
    have hp : 0 < p := lt_of_lt_of_le (by norm_num) hl
    have hd : 9 / 100 / p ∈ Set.Icc (9 / 100 : ℝ) (70 / 100) := by
      constructor
      · rw [le_div_iff₀ hp]; nlinarith
      · rw [div_le_iff₀ hp]; nlinarith
    obtain ⟨-, h11, h10, h00, h1, h0, hpn⟩ := remissionModel_spec _ hd
    refine ⟨remissionModel _ hd, ?_, ?_, ?_⟩
    · change 0 < (remissionModel _ hd).pXY true true
      rw [h11]; positivity
    · simp only [remissionObs, h10, h00, h1, h0]
    · rw [hpn, div_div_cancel₀ (by norm_num)]

/-! ### Failure of the identification formulas outside their assumptions -/

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
