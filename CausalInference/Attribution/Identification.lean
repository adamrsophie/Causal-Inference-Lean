/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Tactic.LinearCombination
public import CausalInference.Attribution.Definitions

/-!
# Identification of the probabilities of causation

Identification of `PN`, `PS`, `PNS` in the finite response-type model of
`CausalInference.Attribution.Definitions` under two assumptions:

* exogeneity: the pair `(Y0, Y1)` is independent of `X` (Pearl 2009, Definition 9.2.9,
  equation (9.7), strong ignorability), stated as the factorization of the eight weights;
* monotonicity: no unit has `Y0 = 1` and `Y1 = 0` (Pearl 2009, Definition 9.2.13, equation
  (9.20)), stated as the vanishing of the two weights of that response type.

## Main definitions

* `Attribution.ResponseModel.pR`: the law of the response type `(Y0, Y1)`.
* `Attribution.ResponseModel.Exogenous`: `(Y0, Y1)` is independent of `X`.
* `Attribution.ResponseModel.Monotonic`: `P(Y0 = 1, Y1 = 0) = 0`.
* `Attribution.ResponseModel.condY`: the observational conditional `P(Y = 1 | X = a)`.

## Main results

* Under exogeneity alone (Theorem 9.2.11, equations (9.11), (9.12)):
  `pn_eq_pns_div_of_exogenous`, `ps_eq_pns_div_of_exogenous`.
* Under monotonicity alone (equation (9.27); Theorem 9.2.15, equations (9.28) to (9.31);
  Primer Theorem 4.5.1, equations (4.28), (4.29)): `pns_eq_of_monotonic`,
  `pn_eq_of_monotonic`, `ps_eq_of_monotonic`, `pn_eq_err_add_of_monotonic`.
* Under exogeneity and monotonicity (Theorem 9.2.14, equations (9.21) to (9.23)):
  `pns_eq_of_exogenous_of_monotonic` (risk difference), `pn_eq_of_exogenous_of_monotonic`
  (excess risk ratio), `ps_eq_of_exogenous_of_monotonic` (relative difference).

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press,
  2009, Sections 9.2.2 to 9.2.4.
* J. Pearl, M. Glymour, N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley, 2016,
  Section 4.5.1, Theorem 4.5.1.
-/

@[expose] public section

namespace CausalInference

namespace Attribution

namespace ResponseModel

variable (m : ResponseModel)

/-- The law of the response type: `P(Y0 = a, Y1 = b)`. -/
def pR (a b : Bool) : ℝ := m.prob fun _ y0 y1 => y0 == a && y1 == b

/-- Exogeneity of `X` relative to `Y` (Pearl 2009, Definition 9.2.9): the pair of potential
outcomes `(Y0, Y1)` is independent of `X`, that is, every cell weight factors as
`P(X = x) P(Y0 = y0, Y1 = y1)`. -/
def Exogenous : Prop := ∀ x y0 y1, m.w x y0 y1 = m.pX x * m.pR y0 y1

/-- Monotonicity of `Y` relative to `X` (Pearl 2009, Definition 9.2.13): no unit would have
`Y = 1` without treatment and `Y = 0` with it. In the weight model this is the vanishing of
the weights of the response type `Y0 = 1`, `Y1 = 0`, for both values of `X`. -/
def Monotonic : Prop := ∀ x, m.w x true false = 0

/-- The observational conditional probability `P(Y = 1 | X = a) = P(X = a, Y = 1) / P(X = a)`;
meaningful only when `P(X = a) > 0`, which every theorem about it assumes. -/
noncomputable def condY (a : Bool) : ℝ := m.pXY a true / m.pX a

theorem pR_eq (a b : Bool) : m.pR a b = m.w true a b + m.w false a b := by
  cases a <;> cases b <;> simp [pR, prob]

theorem pXY_le_pX (a b : Bool) : m.pXY a b ≤ m.pX a := by
  have := m.nonneg
  cases a <;> cases b <;>
  simp only [pXY_true_true, pXY_true_false, pXY_false_true, pXY_false_false, pX_true,
    pX_false] <;> linarith [this true false false, this true false true, this true true false,
      this true true true, this false false false, this false false true, this false true false,
      this false true true]

/-! ### Monotonicity alone -/

/-- Pearl (2009), equation (9.27), and Primer equation (4.42): under monotonicity,
`PNS = P(y_x) - P(y_x')`, with no exogeneity assumption. -/
theorem pns_eq_of_monotonic (hmono : m.Monotonic) : m.PNS = m.pY1 - m.pY0 := by
  rw [pns_eq, pY1_eq, pY0_eq, hmono true, hmono false]; ring

/-- Pearl (2009), Theorem 9.2.15, equation (9.29), and Primer Theorem 4.5.1, equation (4.28):
under monotonicity, `PN = (P(y) - P(y_x')) / P(x, y)`, assuming `P(x, y) > 0`. The
experimental quantity `P(y_x')` and the observational law of `(X, Y)` identify `PN`. -/
theorem pn_eq_of_monotonic (hmono : m.Monotonic) (_h11 : 0 < m.pXY true true) :
    m.PN = (m.pY - m.pY0) / m.pXY true true := by
  rw [pn_eq, pY_eq, pY0_eq, pXY_true_true, pXY_false_true, hmono true, hmono false]
  congr 1; ring

/-- Pearl (2009), Theorem 9.2.15, equation (9.30): under monotonicity,
`PS = (P(y_x) - P(y)) / P(x', y')`, assuming `P(x', y') > 0`. -/
theorem ps_eq_of_monotonic (hmono : m.Monotonic) (_h00 : 0 < m.pXY false false) :
    m.PS = (m.pY1 - m.pY) / m.pXY false false := by
  rw [ps_eq, pY_eq, pY1_eq, pXY_true_true, pXY_false_true, hmono false]
  congr 1; ring

theorem pX_add_pX : m.pX true + m.pX false = 1 := by
  rw [pX_true, pX_false]; linarith [m.sum_cells]

theorem pX_true_pos (h11 : 0 < m.pXY true true) : 0 < m.pX true :=
  h11.trans_le (m.pXY_le_pX true true)

theorem pX_false_pos (h00 : 0 < m.pXY false false) : 0 < m.pX false :=
  h00.trans_le (m.pXY_le_pX false false)

/-- Pearl (2009), equation (9.31), and Primer Theorem 4.5.1, equation (4.29): under
monotonicity, `PN` is the excess risk ratio `(P(y | x) - P(y | x')) / P(y | x)` plus the
confounding correction `(P(y | x') - P(y_x')) / P(x, y)`. Assumes `P(x, y) > 0` and
`P(x') > 0` so that every conditional probability is genuine. -/
theorem pn_eq_err_add_of_monotonic (hmono : m.Monotonic) (h11 : 0 < m.pXY true true)
    (hx' : 0 < m.pX false) :
    m.PN = (m.condY true - m.condY false) / m.condY true +
      (m.condY false - m.pY0) / m.pXY true true := by
  have hx := m.pX_true_pos h11
  have hsum := m.pX_add_pX
  rw [m.pn_eq_of_monotonic hmono h11, condY, condY, pY_eq]
  field_simp
  linear_combination m.pXY false true * hsum

/-! ### Exogeneity -/

theorem pY1_eq_pR : m.pY1 = m.pR false true + m.pR true true := by
  rw [pY1_eq, pR_eq, pR_eq]; ring

theorem pY0_eq_pR : m.pY0 = m.pR true false + m.pR true true := by
  rw [pY0_eq, pR_eq, pR_eq]; ring

theorem one_sub_pY0_eq_pR : 1 - m.pY0 = m.pR false false + m.pR false true := by
  rw [pY0_eq, pR_eq, pR_eq]; linarith [m.sum_cells]

/-- Pearl (2009), equation (9.8): under exogeneity, `P(y_x) = P(y | x)`, assuming
`P(x) > 0`. -/
theorem condY_true_of_exogenous (hexo : m.Exogenous) (hx : 0 < m.pX true) :
    m.condY true = m.pY1 := by
  rw [condY, pXY_true_true, hexo true false true, hexo true true true, pY1_eq_pR,
    div_eq_iff hx.ne']
  ring

/-- Pearl (2009), equation (9.8) for the control arm: under exogeneity, `P(y_x') = P(y | x')`,
assuming `P(x') > 0`. -/
theorem condY_false_of_exogenous (hexo : m.Exogenous) (hx' : 0 < m.pX false) :
    m.condY false = m.pY0 := by
  rw [condY, pXY_false_true, hexo false true false, hexo false true true, pY0_eq_pR,
    div_eq_iff hx'.ne']
  ring

/-- Pearl (2009), Theorem 9.2.11, equation (9.11): under exogeneity, `PN = PNS / P(y | x)`,
assuming `P(x, y) > 0`. -/
theorem pn_eq_pns_div_of_exogenous (hexo : m.Exogenous) (h11 : 0 < m.pXY true true) :
    m.PN = m.PNS / m.condY true := by
  have hx := m.pX_true_pos h11
  rw [m.condY_true_of_exogenous hexo hx, pns_eq, ← pR_eq, pn_eq, pXY_true_true,
    hexo true false true, hexo true true true, pY1_eq_pR, ← mul_add,
    mul_div_mul_left _ _ hx.ne']

/-- Pearl (2009), Theorem 9.2.11, equation (9.12): under exogeneity,
`PS = PNS / P(y' | x') = PNS / (1 - P(y | x'))`, assuming `P(x', y') > 0`. -/
theorem ps_eq_pns_div_of_exogenous (hexo : m.Exogenous) (h00 : 0 < m.pXY false false) :
    m.PS = m.PNS / (1 - m.condY false) := by
  have hx' := m.pX_false_pos h00
  rw [m.condY_false_of_exogenous hexo hx', pns_eq, ← pR_eq, ps_eq, pXY_false_false,
    hexo false false false, hexo false false true, one_sub_pY0_eq_pR, ← mul_add,
    mul_div_mul_left _ _ hx'.ne']

/-! ### Exogeneity and monotonicity: Theorem 9.2.14 -/

/-- Pearl (2009), Theorem 9.2.14, equation (9.21): under exogeneity and monotonicity, `PNS` is
the risk difference `P(y | x) - P(y | x')`, assuming `P(x) > 0` and `P(x') > 0`. -/
theorem pns_eq_of_exogenous_of_monotonic (hexo : m.Exogenous) (hmono : m.Monotonic)
    (hx : 0 < m.pX true) (hx' : 0 < m.pX false) :
    m.PNS = m.condY true - m.condY false := by
  rw [m.condY_true_of_exogenous hexo hx, m.condY_false_of_exogenous hexo hx',
    m.pns_eq_of_monotonic hmono]

/-- Pearl (2009), Theorem 9.2.14, equation (9.22): under exogeneity and monotonicity, `PN` is
the excess risk ratio `(P(y | x) - P(y | x')) / P(y | x)`, assuming `P(x, y) > 0` and
`P(x') > 0`. -/
theorem pn_eq_of_exogenous_of_monotonic (hexo : m.Exogenous) (hmono : m.Monotonic)
    (h11 : 0 < m.pXY true true) (hx' : 0 < m.pX false) :
    m.PN = (m.condY true - m.condY false) / m.condY true := by
  rw [m.pn_eq_pns_div_of_exogenous hexo h11,
    m.pns_eq_of_exogenous_of_monotonic hexo hmono (m.pX_true_pos h11) hx']

/-- Pearl (2009), Theorem 9.2.14, equation (9.23): under exogeneity and monotonicity, `PS` is
the relative difference `(P(y | x) - P(y | x')) / (1 - P(y | x'))`, assuming `P(x', y') > 0`
and `P(x) > 0`. -/
theorem ps_eq_of_exogenous_of_monotonic (hexo : m.Exogenous) (hmono : m.Monotonic)
    (h00 : 0 < m.pXY false false) (hx : 0 < m.pX true) :
    m.PS = (m.condY true - m.condY false) / (1 - m.condY false) := by
  rw [m.ps_eq_pns_div_of_exogenous hexo h00,
    m.pns_eq_of_exogenous_of_monotonic hexo hmono hx (m.pX_false_pos h00)]

end ResponseModel

end Attribution

end CausalInference
