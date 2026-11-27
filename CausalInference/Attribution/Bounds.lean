/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import CausalInference.PartialIdentification.IdentifiedSet
public import CausalInference.Attribution.Identification

/-!
# Bounds on the probabilities of causation

Partial identification of `PN`, `PS`, `PNS` in the finite response-type model of
`CausalInference.Attribution.Definitions`: with no assumption beyond consistency, and under
exogeneity.

## Main results

* Experimental data alone (Pearl 2009, Theorem 9.2.10 and the remark after its proof):
  `max 0 (P(y_x) - P(y_x')) ≤ PNS ≤ min (P(y_x)) (P(y'_x'))` (`pns_mem_Icc_exp`), and the
  bounds are sharp: `identifiedSet_pns_exp` shows that for any experimental marginals
  `a, b ∈ [0, 1]` the identified set of `PNS` is exactly this interval;
  `exists_exogenous_of_mem_Icc_exp` shows every value is attained by an exogenous model.
* Theorem 9.2.10 in its literal conditional form (`pns_mem_Icc_cond`, under weak exogeneity)
  with its sharpness for every joint law of `(X, Y)` with `0 < P(x) < 1`
  (`identifiedSet_pns_cond`); the bounds (9.13) on `PN` and their `PS` counterpart in
  conditional form (`pn_mem_Icc_cond`, `ps_mem_Icc_cond`, under weak exogeneity); and
  Corollary 9.2.12 as identified sets on exogenous models: `I / a` for `PN` and `I / (1 - b)`
  for `PS`, where `I` is the sharp `PNS` interval at experimental marginals `(a, b)`
  (`identifiedSet_pn_exp`, `identifiedSet_ps_exp`). The witnesses are `bernModel`: `X`
  Bernoulli, independent of the response type.
* Experimental and observational data combined (Tian and Pearl 2000; Pearl 2009, Section
  11.9.2, equations (11.41) to (11.43); Primer equation (4.30)): validity of the bounds on
  `PNS` (`pns_mem_Icc_comb`), `PN` (`pn_mem_Icc_comb`) and `PS` (`ps_mem_Icc_comb`), and
  their sharpness: `identifiedSet_pns_comb`, `identifiedSet_pn_comb`, `identifiedSet_ps_comb`
  identify the set of values compatible with the joint law of `(X, Y)` and the experimental
  marginals as exactly the closed interval between the bounds.
* Feasibility of supplied combined data (`exists_combObs_eq_iff`; under monotonicity
  `exists_monotonic_combObs_eq_iff`), and infeasible data whose bound formulas still give the
  nominal interval `[0, 1]` for `PN` (`infeasibleData_nominal`).
* Primer equation (4.31): the inner terms of the `PN` bounds as excess risk ratio plus
  confounding factor (`pn_lower_eq_err_add_cf`, `pn_upper_eq_err_add_q_add_cf`).
* Non-identification (Pearl 2009, Example 9.3.1): the coin bet model and the bookie model
  agree on all experimental and observational quantities, have positive `P(x, y)` and
  `P(x', y')`, but have `PN = 1` and `PN = 0` (`not_pointIdentified_pn`; likewise for `PS`
  and `PNS`). Both models are exogenous, so non-identification holds on the class of positive
  exogenous models (`not_pointIdentified_pn_exogenous`, `_ps_exogenous`, `_pns_exogenous`).
  Under monotonicity `PN` is point identified (`pointIdentified_pn_of_monotonic`).

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press,
  2009, Sections 9.2.2, 9.3.1 and 11.9.2 (Theorem 9.2.10, Corollary 9.2.12).
* J. Tian, J. Pearl (2000), as cited in Pearl (2009), Section 11.9.2, for the combined-data
  bounds and their sharpness.
* J. Pearl, M. Glymour, N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley, 2016,
  Section 4.5.1, equations (4.30) to (4.34).
-/

@[expose] public section

namespace CausalInference

namespace Attribution

namespace ResponseModel

/-! ### Experimental data alone -/

/-- The experimental observation: the pair `(P(y_x), P(y_x'))`. -/
def expObs (m : ResponseModel) : ℝ × ℝ := (m.pY1, m.pY0)

/-- Pearl (2009), bounds (9.9) with `P(y_x)`, `P(y_x')` in place of the conditional
probabilities (the remark after the proof of Theorem 9.2.10), from the Fréchet bounds (9.10):
`max 0 (P(y_x) - P(y_x')) ≤ PNS ≤ min (P(y_x)) (1 - P(y_x'))`. Valid for every model. -/
theorem pns_mem_Icc_exp (m : ResponseModel) :
    m.PNS ∈ Set.Icc (max 0 (m.pY1 - m.pY0)) (min m.pY1 (1 - m.pY0)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
  have hs := m.sum_cells
  rw [pns_eq, pY1_eq, pY0_eq]
  constructor
  · exact max_le (by linarith) (by linarith)
  · exact le_min (by linarith) (by linarith)

/-- The cell table of the sharpness witness for the experimental bounds: `X` is a fair coin
independent of the response type, and the response types `(Y0, Y1) = (0, 1), (1, 1), (1, 0),
(0, 0)` have masses `p`, `a - p`, `b - a + p`, `1 - b - p`. -/
noncomputable def expCells (a b p : ℝ) : Bool → Bool → Bool → ℝ := fun _ y0 y1 =>
  (match y0, y1 with
    | false, true => p
    | true, true => a - p
    | true, false => b - a + p
    | false, false => 1 - b - p) / 2

/-- Sharpness of the experimental bounds on `PNS` (Pearl 2009, Theorem 9.2.10, in the form
with experimental quantities): for any `a, b` and any `p` with
`max 0 (a - b) ≤ p ≤ min a (1 - b)` there is a model with `P(y_x) = a`, `P(y_x') = b`,
`PNS = p`, in which moreover `X` is exogenous. -/
theorem exists_exogenous_of_mem_Icc_exp {a b p : ℝ}
    (hp : p ∈ Set.Icc (max 0 (a - b)) (min a (1 - b))) :
    ∃ m : ResponseModel, m.Exogenous ∧ m.pY1 = a ∧ m.pY0 = b ∧ m.PNS = p := by
  obtain ⟨hl, hu⟩ := hp
  rw [max_le_iff] at hl
  rw [le_min_iff] at hu
  obtain ⟨hl1, hl2⟩ := hl
  obtain ⟨hu1, hu2⟩ := hu
  let m := ofCells (expCells a b p)
    (by intro x y0 y1; cases y0 <;> cases y1 <;> simp [expCells] <;> linarith)
    (by simp [expCells]; ring)
  refine ⟨m, ?_, ?_, ?_, ?_⟩
  · intro x y0 y1
    cases x <;> cases y0 <;> cases y1 <;>
      simp [m, pX_true, pX_false, pR_eq, expCells] <;> ring
  · simp [m, pY1_eq, expCells]; ring
  · simp [m, pY0_eq, expCells]; ring
  · simp [m, pns_eq, expCells]

/-- The identified set of `PNS` from experimental data alone is exactly the interval
`[max 0 (a - b), min a (1 - b)]` at the experimental observation `(P(y_x), P(y_x')) = (a, b)`.
Both bounds are therefore sharp. (When `(a, b)` is not attainable, both sides are empty.) -/
theorem identifiedSet_pns_exp (a b : ℝ) :
    identifiedSet Set.univ expObs PNS (a, b) = Set.Icc (max 0 (a - b)) (min a (1 - b)) := by
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m, -, hm, rfl⟩
    simp only [expObs, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact m.pns_mem_Icc_exp
  · intro hp
    obtain ⟨m, -, h1, h0, hpm⟩ := exists_exogenous_of_mem_Icc_exp hp
    exact ⟨m, trivial, by simp [expObs, h1, h0], hpm⟩

/-! ### Theorem 9.2.10 and Corollary 9.2.12 in conditional form

A model in which `X` is a Bernoulli variable independent of the response type: these models
are exactly the exogenous ones with a given treatment prevalence and a given response-type law,
and they serve as sharpness witnesses for every bound under exogeneity. -/

/-- The cells of the model in which `X = 1` with probability `π`, independently of the response
type `(Y0, Y1)`, whose law is `r`. -/
noncomputable def bernCells (π : ℝ) (r : Bool → Bool → ℝ) : Bool → Bool → Bool → ℝ :=
  fun x y0 y1 => (if x then π else 1 - π) * r y0 y1

/-- The model with `X` Bernoulli with parameter `π`, independent of the response type with law
`r`. -/
noncomputable def bernModel (π : ℝ) (r : Bool → Bool → ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hr : ∀ a b, 0 ≤ r a b)
    (hsum : r false false + r false true + r true false + r true true = 1) : ResponseModel :=
  ofCells (bernCells π r)
    (fun x y0 y1 => mul_nonneg (by cases x <;> simp [hπ0, hπ1]) (hr y0 y1))
    (by simp only [bernCells, ite_true, Bool.false_eq_true, ite_false]; linear_combination hsum)

section bernModel

variable {π : ℝ} {r : Bool → Bool → ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hr : ∀ a b, 0 ≤ r a b)
  (hsum : r false false + r false true + r true false + r true true = 1)

theorem bernModel_w (x y0 y1 : Bool) :
    (bernModel π r hπ0 hπ1 hr hsum).w x y0 y1 = (if x then π else 1 - π) * r y0 y1 := rfl

theorem bernModel_pX_true : (bernModel π r hπ0 hπ1 hr hsum).pX true = π := by
  simp only [pX_true, bernModel_w, ite_true]
  linear_combination π * hsum

theorem bernModel_pR (a b : Bool) : (bernModel π r hπ0 hπ1 hr hsum).pR a b = r a b := by
  simp only [pR_eq, bernModel_w, ite_true, Bool.false_eq_true, ite_false]
  ring

theorem bernModel_exogenous : (bernModel π r hπ0 hπ1 hr hsum).Exogenous := by
  intro x y0 y1
  rw [bernModel_pR]
  have h1 := bernModel_pX_true hπ0 hπ1 hr hsum
  have h0 := (bernModel π r hπ0 hπ1 hr hsum).pX_add_pX
  cases x
  · rw [show (bernModel π r hπ0 hπ1 hr hsum).pX false = 1 - π by linarith, bernModel_w]
    simp
  · rw [h1, bernModel_w]; simp

theorem bernModel_pY1 : (bernModel π r hπ0 hπ1 hr hsum).pY1 = r false true + r true true := by
  rw [pY1_eq_pR, bernModel_pR, bernModel_pR]

theorem bernModel_pY0 : (bernModel π r hπ0 hπ1 hr hsum).pY0 = r true false + r true true := by
  rw [pY0_eq_pR, bernModel_pR, bernModel_pR]

theorem bernModel_pns : (bernModel π r hπ0 hπ1 hr hsum).PNS = r false true := by
  rw [pns_eq, ← pR_eq, bernModel_pR]

end bernModel

/-- The response-type law of the sharpness witness for the bounds (9.9): the types
`(Y0, Y1) = (0, 1), (1, 1), (1, 0), (0, 0)` have masses `p`, `a - p`, `b - a + p`,
`1 - b - p`. -/
def expTypes (a b p : ℝ) : Bool → Bool → ℝ
  | false, true => p
  | true, true => a - p
  | true, false => b - a + p
  | false, false => 1 - b - p

/-- Sharpness of the bounds (9.9) with prescribed treatment prevalence: for any `π ∈ [0, 1]`
and any `p` with `max 0 (a - b) ≤ p ≤ min a (1 - b)` there is an exogenous model with
`P(x) = π`, `P(y_x) = a`, `P(y_x') = b` and `PNS = p`. -/
theorem exists_exogenous_bern {π a b p : ℝ} (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hp : p ∈ Set.Icc (max 0 (a - b)) (min a (1 - b))) :
    ∃ m : ResponseModel, m.Exogenous ∧ m.pX true = π ∧ m.pY1 = a ∧ m.pY0 = b ∧ m.PNS = p := by
  obtain ⟨hl, hu⟩ := hp
  rw [max_le_iff] at hl
  rw [le_min_iff] at hu
  have hr : ∀ c d, 0 ≤ expTypes a b p c d := by
    intro c d; cases c <;> cases d <;> simp only [expTypes] <;> linarith
  have hsum : expTypes a b p false false + expTypes a b p false true +
      expTypes a b p true false + expTypes a b p true true = 1 := by
    simp only [expTypes]; ring
  refine ⟨bernModel π (expTypes a b p) hπ0 hπ1 hr hsum, bernModel_exogenous _ _ _ _,
    bernModel_pX_true _ _ _ _, ?_, ?_, ?_⟩
  · rw [bernModel_pY1]; simp only [expTypes]; ring
  · rw [bernModel_pY0]; simp only [expTypes]; ring
  · rw [bernModel_pns]; rfl

/-- Pearl (2009), Theorem 9.2.10, equation (9.9), in its literal conditional form: under
exogeneity, with `P(x) > 0` and `P(x') > 0`,
`max 0 (P(y | x) - P(y | x')) ≤ PNS ≤ min (P(y | x)) (P(y' | x'))`. Only weak exogeneity is
assumed (each potential outcome independent of `X`), as Pearl notes after Definition 9.2.9. -/
theorem pns_mem_Icc_cond (m : ResponseModel) (hw : m.WeakExogenous) (hx : 0 < m.pX true)
    (hx' : 0 < m.pX false) :
    m.PNS ∈ Set.Icc (max 0 (m.condY true - m.condY false))
      (min (m.condY true) (1 - m.condY false)) := by
  rw [m.condY_true_of_weakExogenous hw hx, m.condY_false_of_weakExogenous hw hx']
  exact m.pns_mem_Icc_exp

/-- The conditional observation `(P(x), P(y | x), P(y | x'))`, which determines the joint law of
`(X, Y)` when `0 < P(x) < 1`. -/
noncomputable def condObs (m : ResponseModel) : ℝ × ℝ × ℝ :=
  (m.pX true, m.condY true, m.condY false)

/-- Sharpness in Theorem 9.2.10 (Pearl 2009): for every joint law of `(X, Y)` with
`0 < P(x) < 1`, given by `(P(x), P(y | x), P(y | x')) = (π, a, b)`, the set of values of `PNS`
over weakly exogenous models is exactly `[max 0 (a - b), min a (1 - b)]`. Every value is
attained by a strongly exogenous model (`exists_exogenous_bern`). -/
theorem identifiedSet_pns_cond {π a b : ℝ} (hπ : π ∈ Set.Ioo 0 1) :
    identifiedSet {m | m.WeakExogenous ∧ 0 < m.pX true ∧ 0 < m.pX false} condObs PNS
      (π, a, b) = Set.Icc (max 0 (a - b)) (min a (1 - b)) := by
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m, ⟨hw, hx, hx'⟩, hm, rfl⟩
    simp only [condObs, Prod.mk.injEq] at hm
    obtain ⟨-, rfl, rfl⟩ := hm
    exact m.pns_mem_Icc_cond hw hx hx'
  · intro hp
    obtain ⟨m, hexo, hπm, h1, h0, hpm⟩ := exists_exogenous_bern hπ.1.le hπ.2.le hp
    have hx : 0 < m.pX true := hπm ▸ hπ.1
    have hx' : 0 < m.pX false := by linarith [m.pX_add_pX, hπ.2]
    refine ⟨m, ⟨hexo.weakExogenous, hx, hx'⟩, ?_, hpm⟩
    simp only [condObs, m.condY_true_of_exogenous hexo hx, m.condY_false_of_exogenous hexo hx',
      hπm, h1, h0]

/-- Pearl (2009), bounds (9.13) on `PN` under exogeneity, in conditional form:
`max 0 (P(y | x) - P(y | x')) / P(y | x) ≤ PN ≤ min (P(y | x)) (P(y' | x')) / P(y | x)`,
assuming `P(x, y) > 0` and `P(x') > 0`. Pearl derives (9.13) from (9.11), which needs strong
exogeneity; the bounds themselves hold under weak exogeneity, proved here directly from the
cells of the arm `X = 1`. -/
theorem pn_mem_Icc_cond (m : ResponseModel) (hw : m.WeakExogenous) (h11 : 0 < m.pXY true true)
    (hx' : 0 < m.pX false) :
    m.PN ∈ Set.Icc (max 0 (m.condY true - m.condY false) / m.condY true)
      (min (m.condY true) (1 - m.condY false) / m.condY true) := by
  have hx := m.pX_true_pos h11
  rw [m.condY_true_of_weakExogenous hw hx, m.condY_false_of_weakExogenous hw hx']
  have e1 := hw.1 true
  have e0 := hw.2 true
  have hpx := m.pX_eq_cells true
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
  have hpos : 0 < m.pX true * m.pY1 := by rw [← e1, ← pXY_true_true]; exact h11
  have ha : 0 < m.pY1 := pos_of_mul_pos_right hpos hx.le
  have hpn : m.PN = m.w true false true / m.pX true / m.pY1 := by
    rw [pn_eq, pXY_true_true, e1, div_div]
  rw [hpn]
  constructor
  · refine div_le_div_of_nonneg_right ?_ ha.le
    rw [le_div_iff₀ hx]
    refine max_mul_of_nonneg _ _ hx.le ▸ max_le (by simpa using h2) ?_
    linarith
  · refine div_le_div_of_nonneg_right ?_ ha.le
    rw [div_le_iff₀ hx]
    refine min_mul_of_nonneg _ _ hx.le ▸ le_min (by linarith) ?_
    linarith

/-- Bounds on `PS` under exogeneity, in conditional form (the `PS` counterpart of (9.13), which
Pearl states after Theorem 9.2.11):
`max 0 (P(y | x) - P(y | x')) / P(y' | x') ≤ PS ≤ min (P(y | x)) (P(y' | x')) / P(y' | x')`,
assuming `P(x', y') > 0` and `P(x) > 0`. Weak exogeneity suffices, as for `pn_mem_Icc_cond`. -/
theorem ps_mem_Icc_cond (m : ResponseModel) (hw : m.WeakExogenous)
    (h00 : 0 < m.pXY false false) (hx : 0 < m.pX true) :
    m.PS ∈ Set.Icc (max 0 (m.condY true - m.condY false) / (1 - m.condY false))
      (min (m.condY true) (1 - m.condY false) / (1 - m.condY false)) := by
  have hx' := m.pX_false_pos h00
  rw [m.condY_true_of_weakExogenous hw hx, m.condY_false_of_weakExogenous hw hx']
  have e1 := hw.1 false
  have e0 := hw.2 false
  have hpx := m.pX_eq_cells false
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
  have h00' : m.pXY false false = m.pX false * (1 - m.pY0) := by
    rw [pXY_false_false]; linear_combination -hpx - e0
  have hb : 0 < 1 - m.pY0 := pos_of_mul_pos_right (h00' ▸ h00) hx'.le
  have hps : m.PS = m.w false false true / m.pX false / (1 - m.pY0) := by
    rw [ps_eq, h00', div_div]
  rw [hps]
  constructor
  · refine div_le_div_of_nonneg_right ?_ hb.le
    rw [le_div_iff₀ hx']
    refine max_mul_of_nonneg _ _ hx'.le ▸ max_le (by simpa using h6) ?_
    linarith
  · refine div_le_div_of_nonneg_right ?_ hb.le
    rw [div_le_iff₀ hx']
    refine min_mul_of_nonneg _ _ hx'.le ▸ le_min (by linarith) ?_
    linarith

/-- Pearl (2009), Corollary 9.2.12, as an identified set: in exogenous models with
`P(x, y) > 0`, the set of values of `PN` compatible with the experimental marginals
`(P(y_x), P(y_x')) = (a, b)`, `a > 0`, is exactly `I / a`, where
`I = [max 0 (a - b), min a (1 - b)]` is the sharp interval of `PNS`. -/
theorem identifiedSet_pn_exp {a b : ℝ} (ha : 0 < a) :
    identifiedSet {m | m.Exogenous ∧ 0 < m.pXY true true} expObs PN (a, b) =
      Set.Icc (max 0 (a - b) / a) (min a (1 - b) / a) := by
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m, ⟨hexo, h11⟩, hm, rfl⟩
    simp only [expObs, Prod.mk.injEq] at hm
    obtain ⟨h1, h0⟩ := hm
    rw [m.pn_eq_pns_div_of_exogenous hexo h11, m.condY_true_of_exogenous hexo (m.pX_true_pos h11),
      h1]
    obtain ⟨hl, hu⟩ := m.pns_mem_Icc_exp
    rw [h1, h0] at hl hu
    exact ⟨div_le_div_of_nonneg_right hl ha.le, div_le_div_of_nonneg_right hu ha.le⟩
  · rintro ⟨hl, hu⟩
    rw [div_le_iff₀ ha] at hl
    rw [le_div_iff₀ ha] at hu
    obtain ⟨m, hexo, hπ, h1, h0, hpm⟩ :=
      exists_exogenous_bern (π := 1 / 2) (by norm_num) (by norm_num) ⟨hl, hu⟩
    have h11 : 0 < m.pXY true true := by
      rw [pXY_true_true, hexo.weakExogenous.1 true, hπ, h1]; positivity
    refine ⟨m, ⟨hexo, h11⟩, by simp [expObs, h1, h0], ?_⟩
    rw [m.pn_eq_pns_div_of_exogenous hexo h11, m.condY_true_of_exogenous hexo (m.pX_true_pos h11),
      h1, hpm, mul_div_cancel_right₀ _ ha.ne']

/-- The `PS` counterpart of Corollary 9.2.12, as an identified set: in exogenous models with
`P(x', y') > 0`, the set of values of `PS` compatible with the experimental marginals
`(P(y_x), P(y_x')) = (a, b)`, `b < 1`, is exactly `I / (1 - b)`, where
`I = [max 0 (a - b), min a (1 - b)]` is the sharp interval of `PNS`. -/
theorem identifiedSet_ps_exp {a b : ℝ} (hb : b < 1) :
    identifiedSet {m | m.Exogenous ∧ 0 < m.pXY false false} expObs PS (a, b) =
      Set.Icc (max 0 (a - b) / (1 - b)) (min a (1 - b) / (1 - b)) := by
  have hb' : 0 < 1 - b := sub_pos.2 hb
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m, ⟨hexo, h00⟩, hm, rfl⟩
    simp only [expObs, Prod.mk.injEq] at hm
    obtain ⟨h1, h0⟩ := hm
    rw [m.ps_eq_pns_div_of_exogenous hexo h00,
      m.condY_false_of_exogenous hexo (m.pX_false_pos h00), h0]
    obtain ⟨hl, hu⟩ := m.pns_mem_Icc_exp
    rw [h1, h0] at hl hu
    exact ⟨div_le_div_of_nonneg_right hl hb'.le, div_le_div_of_nonneg_right hu hb'.le⟩
  · rintro ⟨hl, hu⟩
    rw [div_le_iff₀ hb'] at hl
    rw [le_div_iff₀ hb'] at hu
    obtain ⟨m, hexo, hπ, h1, h0, hpm⟩ :=
      exists_exogenous_bern (π := 1 / 2) (by norm_num) (by norm_num) ⟨hl, hu⟩
    have hx' : m.pX false = 1 / 2 := by linarith [m.pX_add_pX]
    have h00 : 0 < m.pXY false false := by
      have e : m.pXY false false = m.pX false * (1 - m.pY0) := by
        rw [pXY_false_false]
        linear_combination -(m.pX_eq_cells false) - hexo.weakExogenous.2 false
      rw [e, hx', h0]; positivity
    refine ⟨m, ⟨hexo, h00⟩, by simp [expObs, h1, h0], ?_⟩
    rw [m.ps_eq_pns_div_of_exogenous hexo h00,
      m.condY_false_of_exogenous hexo (m.pX_false_pos h00), h0, hpm,
      mul_div_cancel_right₀ _ hb'.ne']

/-! ### Experimental and observational data combined -/

/-- The combined observation: the observational joint law of `(X, Y)` together with the
experimental marginals `P(y_x)` and `P(y_x')`. -/
@[ext]
structure CombinedData where
  /-- The observational law `P(X = a, Y = b)`. -/
  pXY : Bool → Bool → ℝ
  /-- The experimental quantity `P(y_x)`. -/
  pY1 : ℝ
  /-- The experimental quantity `P(y_x')`. -/
  pY0 : ℝ

/-- The combined observation of a model. -/
def combObs (m : ResponseModel) : CombinedData := ⟨m.pXY, m.pY1, m.pY0⟩

/-- Tian and Pearl bounds on `PNS` from combined data (Pearl 2009, equation (11.41)):
`max {0, P(y_x) - P(y_x'), P(y) - P(y_x'), P(y_x) - P(y)} ≤ PNS` and
`PNS ≤ min {P(y_x), P(y'_x'), P(x, y) + P(x', y'), P(y_x) - P(y_x') + P(x, y') + P(x', y)}`.
Valid for every model. -/
theorem pns_mem_Icc_comb (m : ResponseModel) :
    m.PNS ∈ Set.Icc (max (max (max 0 (m.pY1 - m.pY0)) (m.pY - m.pY0)) (m.pY1 - m.pY))
      (min (min (min m.pY1 (1 - m.pY0)) (m.pXY true true + m.pXY false false))
        (m.pY1 - m.pY0 + m.pXY true false + m.pXY false true)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
  have hs := m.sum_cells
  rw [pY_eq, pns_eq, pY1_eq, pY0_eq, pXY_true_true, pXY_true_false, pXY_false_true,
    pXY_false_false]
  constructor
  · exact max_le (max_le (max_le (by linarith) (by linarith)) (by linarith)) (by linarith)
  · exact le_min (le_min (le_min (by linarith) (by linarith)) (by linarith)) (by linarith)

/-- Tian and Pearl bounds on `PN` from combined data (Pearl 2009, equation (11.42); Primer
equation (4.30)): `max {0, (P(y) - P(y_x')) / P(x, y)} ≤ PN ≤
min {1, (P(y'_x') - P(x', y')) / P(x, y)}`, assuming `P(x, y) > 0`. The lower bound is the
monotone estimand (9.29), which is thus a lower bound without monotonicity. -/
theorem pn_mem_Icc_comb (m : ResponseModel) (h11 : 0 < m.pXY true true) :
    m.PN ∈ Set.Icc (max 0 ((m.pY - m.pY0) / m.pXY true true))
      (min 1 ((1 - m.pY0 - m.pXY false false) / m.pXY true true)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
  have hs := m.sum_cells
  have hP := h11
  rw [pXY_true_true] at hP
  rw [pn_eq, pY_eq, pY0_eq, pXY_true_true, pXY_false_true, pXY_false_false]
  constructor
  · refine max_le (div_nonneg h2 hP.le) ?_
    exact div_le_div_of_nonneg_right (by linarith) hP.le
  · refine le_min ((div_le_one hP).2 (by linarith)) ?_
    exact div_le_div_of_nonneg_right (by linarith) hP.le

/-- Tian and Pearl bounds on `PS` from combined data (Pearl 2009, equation (11.43)):
`max {0, (P(y_x) - P(y)) / P(x', y')} ≤ PS ≤ min {1, (P(y_x) - P(x, y)) / P(x', y')}`,
assuming `P(x', y') > 0`. The lower bound is the monotone estimand (9.30). -/
theorem ps_mem_Icc_comb (m : ResponseModel) (h00 : 0 < m.pXY false false) :
    m.PS ∈ Set.Icc (max 0 ((m.pY1 - m.pY) / m.pXY false false))
      (min 1 ((m.pY1 - m.pXY true true) / m.pXY false false)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
  have hs := m.sum_cells
  have hP := h00
  rw [pXY_false_false] at hP
  rw [ps_eq, pY_eq, pY1_eq, pXY_true_true, pXY_false_true, pXY_false_false]
  constructor
  · refine max_le (div_nonneg h6 hP.le) ?_
    exact div_le_div_of_nonneg_right (by linarith) hP.le
  · refine le_min ((div_le_one hP).2 (by linarith)) ?_
    exact div_le_div_of_nonneg_right (by linarith) hP.le

/-- The cell table obtained from `m` by moving mass within each treatment arm so that the
helped type `(Y0, Y1) = (0, 1)` has mass `α` in the arm `X = 1` and `β` in the arm `X = 0`,
keeping the observational law of `(X, Y)` and the experimental marginals. -/
def armCells (m : ResponseModel) (α β : ℝ) : Bool → Bool → Bool → ℝ
  | true, false, true => α
  | true, true, true => m.w true false true + m.w true true true - α
  | true, true, false => m.w true true false - m.w true false true + α
  | true, false, false => m.w true false false + m.w true false true - α
  | false, false, true => β
  | false, true, true => m.w false false true + m.w false true true - β
  | false, true, false => m.w false true false - m.w false false true + β
  | false, false, false => m.w false false false + m.w false false true - β

/-- Every pair `(α, β)` of helped masses in the two arms that satisfies the stated linear
constraints is realized by a model with the same combined observation as `m`. The constraints
are exactly the nonnegativity of the eight cells of `armCells m α β`. -/
theorem exists_combObs_eq (m : ResponseModel) {α β : ℝ}
    (hα0 : 0 ≤ α) (hα1 : m.pY - m.pY0 ≤ α) (hα2 : α ≤ m.pXY true true)
    (hα3 : α ≤ 1 - m.pY0 - m.pXY false false)
    (hβ0 : 0 ≤ β) (hβ1 : m.pY1 - m.pY ≤ β) (hβ2 : β ≤ m.pY1 - m.pXY true true)
    (hβ3 : β ≤ m.pXY false false) :
    ∃ m' : ResponseModel, m'.combObs = m.combObs ∧ m'.w true false true = α ∧
      m'.w false false true = β := by
  have hs := m.sum_cells
  simp only [pY_eq, pY0_eq, pY1_eq, pXY_true_true, pXY_false_true, pXY_false_false]
    at hα1 hα2 hα3 hβ1 hβ2 hβ3
  let m' := ofCells (armCells m α β)
    (by intro x y0 y1; cases x <;> cases y0 <;> cases y1 <;> simp only [armCells] <;> linarith)
    (by simp only [armCells]; linarith)
  refine ⟨m', ?_, rfl, rfl⟩
  have e : ∀ x y0 y1, m'.w x y0 y1 = armCells m α β x y0 y1 := fun _ _ _ => rfl
  ext a b
  · cases a <;> cases b <;>
      simp only [combObs, pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false, e,
        armCells] <;> ring
  · simp only [combObs, pY1_eq, e, armCells]; ring
  · simp only [combObs, pY0_eq, e, armCells]; ring

theorem eq_of_combObs_eq {m m' : ResponseModel} (h : m'.combObs = m.combObs) :
    m'.pXY = m.pXY ∧ m'.pY1 = m.pY1 ∧ m'.pY0 = m.pY0 ∧ m'.pY = m.pY := by
  have hxy : m'.pXY = m.pXY := congrArg CombinedData.pXY h
  refine ⟨hxy, congrArg CombinedData.pY1 h, congrArg CombinedData.pY0 h, ?_⟩
  rw [pY_eq, pY_eq, hxy]

/-- Sharpness of the Tian and Pearl bounds on `PN` (Pearl 2009, equation (11.42); Section
11.9.2 attributes sharpness to Tian and Pearl 2000): at the combined observation of any
model with `P(x, y) > 0`, the identified set of `PN` is exactly the closed
interval between the bounds. -/
theorem identifiedSet_pn_comb (m : ResponseModel) (h11 : 0 < m.pXY true true) :
    identifiedSet Set.univ combObs PN m.combObs =
      Set.Icc (max 0 ((m.pY - m.pY0) / m.pXY true true))
        (min 1 ((1 - m.pY0 - m.pXY false false) / m.pXY true true)) := by
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m', -, hm, rfl⟩
    obtain ⟨hxy, -, h0, hy⟩ := eq_of_combObs_eq hm
    have h11' : 0 < m'.pXY true true := by rw [hxy]; exact h11
    have := m'.pn_mem_Icc_comb h11'
    rwa [hxy, h0, hy] at this
  · rintro ⟨hl, hu⟩
    rw [max_le_iff, div_le_iff₀ h11] at hl
    rw [le_min_iff, le_div_iff₀ h11] at hu
    obtain ⟨hl0, hl1⟩ := hl
    obtain ⟨hu0, hu1⟩ := hu
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
    obtain ⟨m', hm', hα, -⟩ := m.exists_combObs_eq (α := p * m.pXY true true)
      (β := m.w false false true) (mul_nonneg hl0 h11.le) (by linarith)
      (by nlinarith) (by linarith) h6
      (by simp only [pY1_eq, pY_eq, pXY_true_true, pXY_false_true]; linarith)
      (by simp only [pY1_eq, pXY_true_true]; linarith)
      (by simp only [pXY_false_false]; linarith)
    refine ⟨m', trivial, hm', ?_⟩
    obtain ⟨hxy, -⟩ := eq_of_combObs_eq hm'
    rw [pn_eq, hα, hxy, mul_div_cancel_right₀ _ h11.ne']

/-- Sharpness of the Tian and Pearl bounds on `PS` (Pearl 2009, equation (11.43); Section
11.9.2 attributes sharpness to Tian and Pearl 2000): at the combined observation of any
model with `P(x', y') > 0`, the identified set of `PS` is exactly the
closed interval between the bounds. -/
theorem identifiedSet_ps_comb (m : ResponseModel) (h00 : 0 < m.pXY false false) :
    identifiedSet Set.univ combObs PS m.combObs =
      Set.Icc (max 0 ((m.pY1 - m.pY) / m.pXY false false))
        (min 1 ((m.pY1 - m.pXY true true) / m.pXY false false)) := by
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m', -, hm, rfl⟩
    obtain ⟨hxy, h1, -, hy⟩ := eq_of_combObs_eq hm
    have h00' : 0 < m'.pXY false false := by rw [hxy]; exact h00
    have := m'.ps_mem_Icc_comb h00'
    rwa [hxy, h1, hy] at this
  · rintro ⟨hl, hu⟩
    rw [max_le_iff, div_le_iff₀ h00] at hl
    rw [le_min_iff, le_div_iff₀ h00] at hu
    obtain ⟨hl0, hl1⟩ := hl
    obtain ⟨hu0, hu1⟩ := hu
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
    have hs := m.sum_cells
    obtain ⟨m', hm', -, hβ⟩ := m.exists_combObs_eq (α := m.w true false true)
      (β := p * m.pXY false false) h2
      (by simp only [pY0_eq, pY_eq, pXY_true_true, pXY_false_true]; linarith)
      (by simp only [pXY_true_true]; linarith)
      (by simp only [pY0_eq, pXY_false_false]; linarith)
      (mul_nonneg hl0 h00.le) (by linarith) (by linarith) (by nlinarith)
    refine ⟨m', trivial, hm', ?_⟩
    obtain ⟨hxy, -⟩ := eq_of_combObs_eq hm'
    rw [ps_eq, hβ, hxy, mul_div_cancel_right₀ _ h00.ne']

/-- Sharpness of the Tian and Pearl bounds on `PNS` (Pearl 2009, equation (11.41); Section
11.9.2 attributes sharpness to Tian and Pearl 2000): at the combined observation of any
model, the identified set of `PNS` is exactly the closed interval between the bounds. -/
theorem identifiedSet_pns_comb (m : ResponseModel) :
    identifiedSet Set.univ combObs PNS m.combObs =
      Set.Icc (max (max (max 0 (m.pY1 - m.pY0)) (m.pY - m.pY0)) (m.pY1 - m.pY))
        (min (min (min m.pY1 (1 - m.pY0)) (m.pXY true true + m.pXY false false))
          (m.pY1 - m.pY0 + m.pXY true false + m.pXY false true)) := by
  ext p
  rw [mem_identifiedSet]
  constructor
  · rintro ⟨m', -, hm, rfl⟩
    obtain ⟨hxy, h1, h0, hy⟩ := eq_of_combObs_eq hm
    have := m'.pns_mem_Icc_comb
    rwa [hxy, h1, h0, hy] at this
  · rintro ⟨hl, hu⟩
    simp only [max_le_iff, le_min_iff] at hl hu
    obtain ⟨⟨⟨hl0, hl1⟩, hl2⟩, hl3⟩ := hl
    obtain ⟨⟨⟨hu0, hu1⟩, hu2⟩, hu3⟩ := hu
    have key : ∃ α, 0 ≤ α ∧ m.pY - m.pY0 ≤ α ∧ α ≤ m.pXY true true ∧
        α ≤ 1 - m.pY0 - m.pXY false false ∧ 0 ≤ p - α ∧ m.pY1 - m.pY ≤ p - α ∧
        p - α ≤ m.pY1 - m.pXY true true ∧ p - α ≤ m.pXY false false := by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
      have hs := m.sum_cells
      simp only [pY_eq, pY0_eq, pY1_eq, pXY_true_true, pXY_true_false, pXY_false_true,
        pXY_false_false] at hl1 hl2 hl3 hu0 hu1 hu2 hu3 ⊢
      -- the helped mass of the arm `X = 1` is `min U (p - L)`, where `U` is its upper limit and
      -- `L` the lower limit of the arm `X = 0`
      rcases le_total (m.w true false true + m.w true true true)
          (1 - (m.w true true false + m.w true true true + m.w false true false +
            m.w false true true) - (m.w false false false + m.w false false true)) with hU | hU
      · rcases le_total 0 (m.w false false true - m.w false true false) with hL | hL
        · rcases le_total (m.w true false true + m.w true true true)
            (p - (m.w false false true - m.w false true false)) with h | h
          · exact ⟨m.w true false true + m.w true true true, by refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_⟩ <;> linarith⟩
          · exact ⟨p - (m.w false false true - m.w false true false), by refine ⟨?_, ?_, ?_,
              ?_, ?_, ?_, ?_, ?_⟩ <;> linarith⟩
        · rcases le_total (m.w true false true + m.w true true true) p with h | h
          · exact ⟨m.w true false true + m.w true true true, by refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_⟩ <;> linarith⟩
          · exact ⟨p, by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith⟩
      · rcases le_total 0 (m.w false false true - m.w false true false) with hL | hL
        · rcases le_total (m.w true false false + m.w true false true)
            (p - (m.w false false true - m.w false true false)) with h | h
          · exact ⟨m.w true false false + m.w true false true, by refine ⟨?_, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_⟩ <;> linarith⟩
          · exact ⟨p - (m.w false false true - m.w false true false), by refine ⟨?_, ?_, ?_,
              ?_, ?_, ?_, ?_, ?_⟩ <;> linarith⟩
        · rcases le_total (m.w true false false + m.w true false true) p with h | h
          · exact ⟨m.w true false false + m.w true false true, by refine ⟨?_, ?_, ?_, ?_, ?_,
              ?_, ?_, ?_⟩ <;> linarith⟩
          · exact ⟨p, by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith⟩
    obtain ⟨α, k0, k1, k2, k3, k4, k5, k6, k7⟩ := key
    obtain ⟨m', hm', hα, hβ⟩ := m.exists_combObs_eq k0 k1 k2 k3 k4 k5 k6 k7
    refine ⟨m', trivial, hm', ?_⟩
    rw [pns_eq, hα, hβ]
    ring

/-! ### Feasibility of combined data

The sharpness theorems above start from a model. Applied to supplied numbers they require the
numbers to be the combined observation of some model; otherwise the bound formulas still
produce an interval, which is meaningless. -/

/-- Feasibility of combined data: a model with combined observation `d` exists if and only if
the four observational cells are nonnegative and sum to one and the experimental marginals lie
in the ranges `P(x, y) ≤ P(y_x) ≤ 1 - P(x, y')` and `P(x', y) ≤ P(y_x') ≤ 1 - P(x', y')`. -/
theorem exists_combObs_eq_iff (d : CombinedData) :
    (∃ m : ResponseModel, m.combObs = d) ↔
      (∀ a b, 0 ≤ d.pXY a b) ∧
        d.pXY true true + d.pXY true false + d.pXY false true + d.pXY false false = 1 ∧
        d.pXY true true ≤ d.pY1 ∧ d.pY1 ≤ 1 - d.pXY true false ∧
        d.pXY false true ≤ d.pY0 ∧ d.pY0 ≤ 1 - d.pXY false false := by
  constructor
  · rintro ⟨m, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
    have hs := m.sum_cells
    simp only [combObs, pY1_eq, pY0_eq, pXY_true_true, pXY_true_false, pXY_false_true,
      pXY_false_false]
    refine ⟨?_, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    intro a b
    cases a <;> cases b <;>
      simp only [pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false] <;> linarith
  · rintro ⟨hnn, hs, ha1, ha2, hb1, hb2⟩
    have q11 := hnn true true
    have q10 := hnn true false
    have q01 := hnn false true
    have q00 := hnn false false
    -- `s` is the mass of `Y0 = 1` in the arm `X = 1`, `t` the mass of `Y1 = 1` in the arm `X = 0`
    set s := d.pY0 - d.pXY false true with hsdef
    set t := d.pY1 - d.pXY true true with htdef
    have ms1 := min_le_left s (d.pXY true true)
    have ms2 := min_le_right s (d.pXY true true)
    have mt1 := min_le_left t (d.pXY false true)
    have mt2 := min_le_right t (d.pXY false true)
    have ms0 : 0 ≤ min s (d.pXY true true) := le_min (by linarith) q11
    have mt0 : 0 ≤ min t (d.pXY false true) := le_min (by linarith) q01
    have ms3 : 0 ≤ d.pXY true false - s + min s (d.pXY true true) := by
      rcases le_total s (d.pXY true true) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    have mt3 : 0 ≤ d.pXY false false - t + min t (d.pXY false true) := by
      rcases le_total t (d.pXY false true) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
    let cells : Bool → Bool → Bool → ℝ
      | true, true, true => min s (d.pXY true true)
      | true, true, false => s - min s (d.pXY true true)
      | true, false, true => d.pXY true true - min s (d.pXY true true)
      | true, false, false => d.pXY true false - s + min s (d.pXY true true)
      | false, true, true => min t (d.pXY false true)
      | false, false, true => t - min t (d.pXY false true)
      | false, true, false => d.pXY false true - min t (d.pXY false true)
      | false, false, false => d.pXY false false - t + min t (d.pXY false true)
    let m := ofCells cells
      (by intro x y0 y1; cases x <;> cases y0 <;> cases y1 <;> simp only [cells] <;> linarith)
      (by simp only [cells]; linarith)
    refine ⟨m, ?_⟩
    have e : ∀ x y0 y1, m.w x y0 y1 = cells x y0 y1 := fun _ _ _ => rfl
    ext a b
    · cases a <;> cases b <;>
        simp only [combObs, pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false, e,
          cells] <;> ring
    · simp only [combObs, pY1_eq, e, cells]; ring
    · simp only [combObs, pY0_eq, e, cells]; ring

/-- Feasibility of combined data under monotonicity (the exact test): a monotonic model with
combined observation `d` exists if and only if the four observational cells are nonnegative and
sum to one and `P(x', y) ≤ P(y_x') ≤ P(y) ≤ P(y_x) ≤ 1 - P(x, y')`, where
`P(y) = P(x, y) + P(x', y)`. -/
theorem exists_monotonic_combObs_eq_iff (d : CombinedData) :
    (∃ m : ResponseModel, m.Monotonic ∧ m.combObs = d) ↔
      (∀ a b, 0 ≤ d.pXY a b) ∧
        d.pXY true true + d.pXY true false + d.pXY false true + d.pXY false false = 1 ∧
        d.pXY false true ≤ d.pY0 ∧ d.pY0 ≤ d.pXY true true + d.pXY false true ∧
        d.pXY true true + d.pXY false true ≤ d.pY1 ∧ d.pY1 ≤ 1 - d.pXY true false := by
  constructor
  · rintro ⟨m, hmono, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := m.nonneg_cells
    have hs := m.sum_cells
    have m1 := hmono true
    have m0 := hmono false
    simp only [combObs, pY1_eq, pY0_eq, pXY_true_true, pXY_true_false, pXY_false_true,
      pXY_false_false]
    refine ⟨?_, by linarith, by linarith, by linarith, by linarith, by linarith⟩
    intro a b
    cases a <;> cases b <;>
      simp only [pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false] <;> linarith
  · rintro ⟨hnn, hs, hb1, hb2, ha1, ha2⟩
    have q11 := hnn true true
    have q10 := hnn true false
    have q01 := hnn false true
    have q00 := hnn false false
    let cells : Bool → Bool → Bool → ℝ
      | true, true, true => d.pY0 - d.pXY false true
      | true, true, false => 0
      | true, false, true => d.pXY true true + d.pXY false true - d.pY0
      | true, false, false => d.pXY true false
      | false, true, true => d.pXY false true
      | false, true, false => 0
      | false, false, true => d.pY1 - d.pXY true true - d.pXY false true
      | false, false, false => d.pXY false false + d.pXY true true + d.pXY false true - d.pY1
    let m := ofCells cells
      (by intro x y0 y1; cases x <;> cases y0 <;> cases y1 <;> simp only [cells] <;> linarith)
      (by simp only [cells]; linarith)
    have e : ∀ x y0 y1, m.w x y0 y1 = cells x y0 y1 := fun _ _ _ => rfl
    refine ⟨m, fun x => by cases x <;> rfl, ?_⟩
    ext a b
    · cases a <;> cases b <;>
        simp only [combObs, pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false, e,
          cells] <;> ring
    · simp only [combObs, pY1_eq, e, cells]; ring
    · simp only [combObs, pY0_eq, e, cells]; ring

/-- The nominal Tian and Pearl interval for `PN` (Pearl 2009, equation (11.42)), computed from
supplied combined data `d` by the bound formulas, with `P(y) = P(x, y) + P(x', y)`. At the
combined observation of a model with `P(x, y) > 0` it is the identified set of `PN`
(`identifiedSet_pn_comb`); at infeasible data it is meaningless. -/
noncomputable def pnBoundsComb (d : CombinedData) : Set ℝ :=
  Set.Icc (max 0 ((d.pXY true true + d.pXY false true - d.pY0) / d.pXY true true))
    (min 1 ((1 - d.pY0 - d.pXY false false) / d.pXY true true))

/-- At the combined observation of a model with `P(x, y) > 0`, the nominal interval is the
identified set of `PN`. -/
theorem pnBoundsComb_combObs (m : ResponseModel) (h11 : 0 < m.pXY true true) :
    pnBoundsComb m.combObs = identifiedSet Set.univ combObs PN m.combObs := by
  rw [identifiedSet_pn_comb m h11, pnBoundsComb, pY_eq]
  rfl

/-- Infeasible combined data: every observational cell is `1/4`, `P(y_x) = 0`, `P(y_x') = 1/2`.
The experimental `P(y_x) = 0` contradicts the observational `P(x, y) = 1/4`. -/
noncomputable def infeasibleData : CombinedData := ⟨fun _ _ => 1 / 4, 0, 1 / 2⟩

/-- No model has the combined observation `infeasibleData`, so its identified set of `PN` is
empty, yet the bound formulas give the nominal interval `[0, 1]`. -/
theorem infeasibleData_nominal :
    (¬ ∃ m : ResponseModel, m.combObs = infeasibleData) ∧
      identifiedSet Set.univ combObs PN infeasibleData = ∅ ∧
      pnBoundsComb infeasibleData = Set.Icc 0 1 := by
  have hno : ¬ ∃ m : ResponseModel, m.combObs = infeasibleData := by
    rw [exists_combObs_eq_iff]
    rintro ⟨-, -, h, -⟩
    norm_num [infeasibleData] at h
  refine ⟨hno, ?_, ?_⟩
  · ext p
    simp only [mem_identifiedSet, Set.mem_univ, true_and, Set.mem_empty_iff_false, iff_false]
    rintro ⟨m, hm, -⟩
    exact hno ⟨m, hm⟩
  · rw [pnBoundsComb]
    norm_num [infeasibleData]

/-! ### Primer equation (4.31) -/

/-- Primer equation (4.31), lower bound: the inner term `(P(y) - P(y_x')) / P(x, y)` of the
lower bound (4.30) on `PN` equals `ERR + CF`, with excess risk ratio
`ERR = (P(y | x) - P(y | x')) / P(y | x)` (4.33) and confounding factor
`CF = (P(y | x') - P(y_x')) / P(x, y)` (4.32). Assumes `P(x, y) > 0` and `P(x') > 0`. -/
theorem pn_lower_eq_err_add_cf (m : ResponseModel) (h11 : 0 < m.pXY true true)
    (hx' : 0 < m.pX false) :
    (m.pY - m.pY0) / m.pXY true true = (m.condY true - m.condY false) / m.condY true +
      (m.condY false - m.pY0) / m.pXY true true := by
  have hx := m.pX_true_pos h11
  have hsum := m.pX_add_pX
  rw [condY, condY, pY_eq]
  field_simp
  linear_combination m.pXY false true * hsum

/-- Primer equation (4.31), upper bound: the inner term `(P(y'_x') - P(x', y')) / P(x, y)` of
the upper bound (4.30) on `PN` equals `ERR + q + CF`, with `q = P(y' | x) / P(y | x)` (4.34).
Assumes `P(x, y) > 0` and `P(x') > 0`. -/
theorem pn_upper_eq_err_add_q_add_cf (m : ResponseModel) (h11 : 0 < m.pXY true true)
    (hx' : 0 < m.pX false) :
    (1 - m.pY0 - m.pXY false false) / m.pXY true true =
      (m.condY true - m.condY false) / m.condY true +
        m.pXY true false / m.pX true / m.condY true +
        (m.condY false - m.pY0) / m.pXY true true := by
  have hx := m.pX_true_pos h11
  have hsum := m.pX_add_pX
  have hpx : m.pX true = m.pXY true true + m.pXY true false := by
    rw [pX_true, pXY_true_true, pXY_true_false]; ring
  have hpx' : m.pX false = m.pXY false true + m.pXY false false := by
    rw [pX_false, pXY_false_true, pXY_false_false]; ring
  rw [condY, condY]
  field_simp
  linear_combination m.pX false * hpx + m.pX false * hpx' +
    (m.pXY false true - m.pX false) * hsum

/-! ### Non-identification without monotonicity: the coin bet and the bookie -/

/-- The coin bet model of Pearl (2009), Example 9.3.1: the bet `X` and the coin `U` are
independent fair coins and `Y = (X ∧ U) ∨ (¬X ∧ ¬U)`, so `(Y0, Y1) = (¬U, U)`. Each cell with
`Y0 ≠ Y1` has mass `1/4`. -/
noncomputable def coinBet : ResponseModel :=
  ofCells (fun _ y0 y1 => if y0 = y1 then 0 else 1 / 4)
    (by intro x y0 y1; split_ifs <;> norm_num) (by norm_num)

/-- The bookie model of Pearl (2009), Example 9.3.1: the payoff ignores the bet, `Y = U` with
`U` a fair coin independent of `X`, so `(Y0, Y1) = (U, U)`. Each cell with `Y0 = Y1` has mass
`1/4`. -/
noncomputable def bookie : ResponseModel :=
  ofCells (fun _ y0 y1 => if y0 = y1 then 1 / 4 else 0)
    (by intro x y0 y1; split_ifs <;> norm_num) (by norm_num)

/-- The coin bet and the bookie agree on the observational law of `(X, Y)` (every cell `1/4`)
and on the experimental marginals (`P(y_x) = P(y_x') = 1/2`). -/
theorem combObs_coinBet_eq_bookie : coinBet.combObs = bookie.combObs := by
  ext a b
  · cases a <;> cases b <;>
      simp [combObs, coinBet, bookie, pXY_true_true, pXY_true_false, pXY_false_true,
        pXY_false_false]
  · simp [combObs, coinBet, bookie, pY1_eq]
  · simp [combObs, coinBet, bookie, pY0_eq]

theorem coinBet_pn : coinBet.PN = 1 := by
  simp [coinBet, pn_eq, pXY_true_true]

theorem bookie_pn : bookie.PN = 0 := by
  simp [bookie, pn_eq]

theorem coinBet_ps : coinBet.PS = 1 := by
  simp [coinBet, ps_eq, pXY_false_false]

theorem bookie_ps : bookie.PS = 0 := by
  simp [bookie, ps_eq]

theorem coinBet_pns : coinBet.PNS = 1 / 2 := by
  simp [coinBet, pns_eq]; norm_num

theorem bookie_pns : bookie.PNS = 0 := by
  simp [bookie, pns_eq]

/-- The model class with both conditioning events of positive probability:
`P(x, y) > 0` and `P(x', y') > 0`, so that `PN` and `PS` are genuine conditional
probabilities. -/
def positiveModels : Set ResponseModel := {m | 0 < m.pXY true true ∧ 0 < m.pXY false false}

theorem coinBet_mem_positiveModels : coinBet ∈ positiveModels := by
  constructor <;> simp [coinBet, pXY_true_true, pXY_false_false]

theorem bookie_mem_positiveModels : bookie ∈ positiveModels := by
  constructor <;> simp [bookie, pXY_true_true, pXY_false_false]

/-- Non-identification of `PN` (Pearl 2009, Example 9.3.1): without monotonicity, `PN` is not
a function of the observational law of `(X, Y)` and the experimental marginals together, even
on models with positive conditioning events. The coin bet and the bookie agree on all of
these and have `PN = 1` and `PN = 0`. -/
theorem not_pointIdentified_pn : ¬ PointIdentified positiveModels combObs PN := fun h => by
  have := h coinBet coinBet_mem_positiveModels bookie bookie_mem_positiveModels
    combObs_coinBet_eq_bookie
  rw [coinBet_pn, bookie_pn] at this
  exact one_ne_zero this

/-- Non-identification of `PS` from combined data (Pearl 2009, Example 9.3.1). -/
theorem not_pointIdentified_ps : ¬ PointIdentified positiveModels combObs PS := fun h => by
  have := h coinBet coinBet_mem_positiveModels bookie bookie_mem_positiveModels
    combObs_coinBet_eq_bookie
  rw [coinBet_ps, bookie_ps] at this
  exact one_ne_zero this

/-- Non-identification of `PNS` from combined data (Pearl 2009, Example 9.3.1). -/
theorem not_pointIdentified_pns : ¬ PointIdentified positiveModels combObs PNS := fun h => by
  have := h coinBet coinBet_mem_positiveModels bookie bookie_mem_positiveModels
    combObs_coinBet_eq_bookie
  rw [coinBet_pns, bookie_pns] at this
  norm_num at this

/-- The coin bet model violates monotonicity: it has mass on the response type
`Y0 = 1`, `Y1 = 0`. -/
theorem not_monotonic_coinBet : ¬ coinBet.Monotonic := fun h => by
  have := h true
  simp [coinBet] at this

/-- The bookie model is exogenous (the payoff ignores the bet). -/
theorem bookie_exogenous : bookie.Exogenous := by
  intro x y0 y1
  cases x <;> cases y0 <;> cases y1 <;> simp [bookie, pX_true, pX_false, pR_eq] <;> norm_num

/-- The coin bet model is exogenous (the bet is independent of the coin). -/
theorem coinBet_exogenous : coinBet.Exogenous := by
  intro x y0 y1
  cases x <;> cases y0 <;> cases y1 <;> simp [coinBet, pX_true, pX_false, pR_eq] <;> norm_num

/-- Non-identification of `PN` on the class of positive exogenous models (Pearl 2009,
Example 9.3.1: `PN` is not identified "even in a controlled experiment"). The coin bet and the
bookie are both exogenous with positive conditioning events, agree on the observational law of
`(X, Y)` and on the experimental marginals, and have `PN = 1` and `PN = 0`. -/
theorem not_pointIdentified_pn_exogenous :
    ¬ PointIdentified (positiveModels ∩ {m | m.Exogenous}) combObs PN := fun h => by
  have := h coinBet ⟨coinBet_mem_positiveModels, coinBet_exogenous⟩ bookie
    ⟨bookie_mem_positiveModels, bookie_exogenous⟩ combObs_coinBet_eq_bookie
  rw [coinBet_pn, bookie_pn] at this
  exact one_ne_zero this

/-- Non-identification of `PS` on the class of positive exogenous models (Pearl 2009,
Example 9.3.1). -/
theorem not_pointIdentified_ps_exogenous :
    ¬ PointIdentified (positiveModels ∩ {m | m.Exogenous}) combObs PS := fun h => by
  have := h coinBet ⟨coinBet_mem_positiveModels, coinBet_exogenous⟩ bookie
    ⟨bookie_mem_positiveModels, bookie_exogenous⟩ combObs_coinBet_eq_bookie
  rw [coinBet_ps, bookie_ps] at this
  exact one_ne_zero this

/-- Non-identification of `PNS` on the class of positive exogenous models (Pearl 2009,
Example 9.3.1). -/
theorem not_pointIdentified_pns_exogenous :
    ¬ PointIdentified (positiveModels ∩ {m | m.Exogenous}) combObs PNS := fun h => by
  have := h coinBet ⟨coinBet_mem_positiveModels, coinBet_exogenous⟩ bookie
    ⟨bookie_mem_positiveModels, bookie_exogenous⟩ combObs_coinBet_eq_bookie
  rw [coinBet_pns, bookie_pns] at this
  norm_num at this

/-- In contrast, under monotonicity `PN` is point identified from combined data on the models
with `P(x, y) > 0` (Pearl 2009, Theorem 9.2.15). -/
theorem pointIdentified_pn_of_monotonic :
    PointIdentified {m | m.Monotonic ∧ 0 < m.pXY true true} combObs PN := by
  rintro m ⟨hm, h11⟩ m' ⟨hm', h11'⟩ h
  obtain ⟨hxy, -, h0, hy⟩ := eq_of_combObs_eq h
  rw [m.pn_eq_of_monotonic hm h11, m'.pn_eq_of_monotonic hm' h11', hxy, h0, hy]

end ResponseModel

end Attribution

end CausalInference
