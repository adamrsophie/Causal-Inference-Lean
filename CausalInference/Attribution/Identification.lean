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
  equation (9.7), strong ignorability), stated as the factorization of the eight weights; and
  weak exogeneity: each potential outcome separately independent of `X` (the weaker condition
  that Pearl, after Definition 9.2.9, says suffices for every result of Chapter 9 except
  (9.11), (9.12), (9.19));
* monotonicity: no unit has `Y0 = 1` and `Y1 = 0` (Pearl 2009, Definition 9.2.13, equation
  (9.20)), stated as the vanishing of the two weights of that response type.

## Main definitions

* `Attribution.ResponseModel.pR`: the law of the response type `(Y0, Y1)`.
* `Attribution.ResponseModel.Exogenous`: `(Y0, Y1)` is independent of `X`.
* `Attribution.ResponseModel.WeakExogenous`: `Y0` and `Y1` are each independent of `X`.
* `Attribution.ResponseModel.Monotonic`: `P(Y0 = 1, Y1 = 0) = 0`.
* `Attribution.ResponseModel.condY`: the observational conditional `P(Y = 1 | X = a)`.

## Main results

* Strong implies weak exogeneity (`Exogenous.weakExogenous`); under monotonicity the two
  coincide (`exogenous_of_weakExogenous_of_monotonic`).
* Under weak exogeneity (equation (9.8)): `condY_true_of_weakExogenous`,
  `condY_false_of_weakExogenous`.
* Under strong exogeneity (Theorem 9.2.11, equations (9.11), (9.12), and equation (9.19)):
  `pn_eq_pns_div_of_exogenous`, `ps_eq_pns_div_of_exogenous`, `pd_eq_of_exogenous`,
  `pe_eq_of_exogenous`. The model `weakExoCounter` is weakly but not strongly exogenous and
  violates all four (`weakExoCounter_pn_ne`, `weakExoCounter_ps_ne`, `weakExoCounter_pd_ne`,
  `weakExoCounter_pe_ne`).
* Under monotonicity alone (equation (9.27); Theorem 9.2.15, equations (9.28) to (9.31);
  Primer Theorem 4.5.1, equations (4.28), (4.29)): `pns_eq_of_monotonic`,
  `pn_eq_of_monotonic`, `ps_eq_of_monotonic`, `pn_eq_err_add_of_monotonic`.
* Under weak exogeneity and monotonicity (Theorem 9.2.14, equations (9.21) to (9.23)):
  `pns_eq_of_weakExogenous_of_monotonic` (risk difference),
  `pn_eq_of_weakExogenous_of_monotonic` (excess risk ratio),
  `ps_eq_of_weakExogenous_of_monotonic` (relative difference), with the strong-form
  corollaries `pns_eq_of_exogenous_of_monotonic`, `pn_eq_of_exogenous_of_monotonic`,
  `ps_eq_of_exogenous_of_monotonic`.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press,
  2009, Sections 9.2.1 to 9.2.4.
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

/-- Weak exogeneity of `X` relative to `Y`: each potential outcome is separately independent of
`X`, that is, `P(X = x, Y1 = 1) = P(X = x) P(Y1 = 1)` and `P(X = x, Y0 = 1) = P(X = x) P(Y0 = 1)`
for both values of `x` (for Boolean variables these equations are independence). This is the
weaker condition of Pearl (2009), equation (5.30), discussed after Definition 9.2.9; it does not
constrain the joint law of `(Y0, Y1)` given `X`. -/
def WeakExogenous : Prop :=
  (∀ x, m.w x false true + m.w x true true = m.pX x * m.pY1) ∧
    ∀ x, m.w x true false + m.w x true true = m.pX x * m.pY0

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

/-- Strong exogeneity implies weak exogeneity. -/
theorem Exogenous.weakExogenous {m : ResponseModel} (hexo : m.Exogenous) : m.WeakExogenous := by
  constructor <;> intro x
  · rw [hexo x false true, hexo x true true, pY1_eq_pR]; ring
  · rw [hexo x true false, hexo x true true, pY0_eq_pR]; ring

theorem pX_eq_cells (x : Bool) :
    m.pX x = m.w x false false + m.w x false true + m.w x true false + m.w x true true := by
  cases x
  · rw [pX_false]
  · rw [pX_true]

/-- Under monotonicity, weak exogeneity implies strong exogeneity: with the response type
`(Y0, Y1) = (1, 0)` absent, the remaining three cells of each arm are determined by the two
marginals `P(Y1 = 1)` and `P(Y0 = 1)`. -/
theorem exogenous_of_weakExogenous_of_monotonic (hw : m.WeakExogenous) (hmono : m.Monotonic) :
    m.Exogenous := by
  obtain ⟨h1, h0⟩ := hw
  have hs := m.pX_add_pX
  have t11 : ∀ x, m.w x true true = m.pX x * m.pY0 := fun x => by
    linear_combination h0 x - hmono x
  have t01 : ∀ x, m.w x false true = m.pX x * (m.pY1 - m.pY0) := fun x => by
    linear_combination h1 x - t11 x
  have t00 : ∀ x, m.w x false false = m.pX x * (1 - m.pY1) := fun x => by
    linear_combination -(m.pX_eq_cells x) - t01 x - t11 x - hmono x
  have r11 : m.pR true true = m.pY0 := by
    rw [pR_eq, t11, t11]; linear_combination m.pY0 * hs
  have r01 : m.pR false true = m.pY1 - m.pY0 := by
    rw [pR_eq, t01, t01]; linear_combination (m.pY1 - m.pY0) * hs
  have r10 : m.pR true false = 0 := by rw [pR_eq, hmono, hmono]; ring
  have r00 : m.pR false false = 1 - m.pY1 := by
    rw [pR_eq, t00, t00]; linear_combination (1 - m.pY1) * hs
  intro x y0 y1
  cases y0 <;> cases y1
  · rw [r00, t00]
  · rw [r01, t01]
  · rw [r10, hmono, mul_zero]
  · rw [r11, t11]

/-- Pearl (2009), equation (9.8): under weak exogeneity (`Y1` independent of `X`),
`P(y_x) = P(y | x)`, assuming `P(x) > 0`. -/
theorem condY_true_of_weakExogenous (hw : m.WeakExogenous) (hx : 0 < m.pX true) :
    m.condY true = m.pY1 := by
  rw [condY, pXY_true_true, hw.1 true, mul_div_cancel_left₀ _ hx.ne']

/-- Pearl (2009), equation (9.8) for the control arm: under weak exogeneity (`Y0` independent
of `X`), `P(y_x') = P(y | x')`, assuming `P(x') > 0`. -/
theorem condY_false_of_weakExogenous (hw : m.WeakExogenous) (hx' : 0 < m.pX false) :
    m.condY false = m.pY0 := by
  rw [condY, pXY_false_true, hw.2 false, mul_div_cancel_left₀ _ hx'.ne']

/-- Pearl (2009), equation (9.8): under exogeneity, `P(y_x) = P(y | x)`, assuming `P(x) > 0`.
Weak exogeneity suffices (`condY_true_of_weakExogenous`). -/
theorem condY_true_of_exogenous (hexo : m.Exogenous) (hx : 0 < m.pX true) :
    m.condY true = m.pY1 :=
  m.condY_true_of_weakExogenous hexo.weakExogenous hx

/-- Pearl (2009), equation (9.8) for the control arm: under exogeneity, `P(y_x') = P(y | x')`,
assuming `P(x') > 0`. Weak exogeneity suffices (`condY_false_of_weakExogenous`). -/
theorem condY_false_of_exogenous (hexo : m.Exogenous) (hx' : 0 < m.pX false) :
    m.condY false = m.pY0 :=
  m.condY_false_of_weakExogenous hexo.weakExogenous hx'

/-- Pearl (2009), Theorem 9.2.11, equation (9.11): under exogeneity, `PN = PNS / P(y | x)`,
assuming `P(x, y) > 0`. This needs the strong form (9.7): the step (9.17) factors
`P(Y0 = 0, Y1 = 1, X = 1)` as `P(Y0 = 0, Y1 = 1) P(X = 1)`, which is a statement about the
joint law of `(Y0, Y1)`. Under weak exogeneity alone (9.11) fails
(`weakExoCounter_pn_ne`). -/
theorem pn_eq_pns_div_of_exogenous (hexo : m.Exogenous) (h11 : 0 < m.pXY true true) :
    m.PN = m.PNS / m.condY true := by
  have hx := m.pX_true_pos h11
  rw [m.condY_true_of_exogenous hexo hx, pns_eq, ← pR_eq, pn_eq, pXY_true_true,
    hexo true false true, hexo true true true, pY1_eq_pR, ← mul_add,
    mul_div_mul_left _ _ hx.ne']

/-- Pearl (2009), Theorem 9.2.11, equation (9.12): under exogeneity,
`PS = PNS / P(y' | x') = PNS / (1 - P(y | x'))`, assuming `P(x', y') > 0`. As for (9.11), this
needs the strong form (9.7); under weak exogeneity alone it fails (`weakExoCounter_ps_ne`). -/
theorem ps_eq_pns_div_of_exogenous (hexo : m.Exogenous) (h00 : 0 < m.pXY false false) :
    m.PS = m.PNS / (1 - m.condY false) := by
  have hx' := m.pX_false_pos h00
  rw [m.condY_false_of_exogenous hexo hx', pns_eq, ← pR_eq, ps_eq, pXY_false_false,
    hexo false false false, hexo false false true, one_sub_pY0_eq_pR, ← mul_add,
    mul_div_mul_left _ _ hx'.ne']

/-- Pearl (2009), equation (9.19), probability of disablement: under exogeneity,
`PD = P(x) PNS / P(y)`, where `P(y) > 0` makes `PD` a conditional probability. This needs the
strong form (9.7); under weak exogeneity alone it fails (`weakExoCounter_pd_ne`). -/
theorem pd_eq_of_exogenous (hexo : m.Exogenous) (_hy : 0 < m.pY) :
    m.PD = m.pX true * m.PNS / m.pY := by
  rw [pd_eq, hexo true false true, pns_eq, ← pR_eq]

/-- Pearl (2009), equation (9.19), probability of enablement: under exogeneity,
`PE = P(x') PNS / P(y')`, where `P(y') = 1 - P(y) > 0` makes `PE` a conditional probability.
This needs the strong form (9.7); under weak exogeneity alone it fails
(`weakExoCounter_pe_ne`). -/
theorem pe_eq_of_exogenous (hexo : m.Exogenous) (_hy : m.pY < 1) :
    m.PE = m.pX false * m.PNS / (1 - m.pY) := by
  rw [pe_eq, hexo false false true, pns_eq, ← pR_eq]

/-! ### Exogeneity and monotonicity: Theorem 9.2.14

Pearl states after Definition 9.2.9 that the weak form of exogeneity suffices for every result
of Chapter 9 except (9.11), (9.12) and (9.19). For Theorem 9.2.14 this is visible directly:
under monotonicity weak exogeneity implies the strong form
(`exogenous_of_weakExogenous_of_monotonic`). The three equations are stated under weak
exogeneity; the strong-form versions are corollaries. -/

/-- Pearl (2009), Theorem 9.2.14, equation (9.21): under weak exogeneity and monotonicity,
`PNS` is the risk difference `P(y | x) - P(y | x')`, assuming `P(x) > 0` and `P(x') > 0`. -/
theorem pns_eq_of_weakExogenous_of_monotonic (hw : m.WeakExogenous) (hmono : m.Monotonic)
    (hx : 0 < m.pX true) (hx' : 0 < m.pX false) :
    m.PNS = m.condY true - m.condY false := by
  rw [m.condY_true_of_weakExogenous hw hx, m.condY_false_of_weakExogenous hw hx',
    m.pns_eq_of_monotonic hmono]

/-- Pearl (2009), Theorem 9.2.14, equation (9.22): under weak exogeneity and monotonicity, `PN`
is the excess risk ratio `(P(y | x) - P(y | x')) / P(y | x)`, assuming `P(x, y) > 0` and
`P(x') > 0`. -/
theorem pn_eq_of_weakExogenous_of_monotonic (hw : m.WeakExogenous) (hmono : m.Monotonic)
    (h11 : 0 < m.pXY true true) (hx' : 0 < m.pX false) :
    m.PN = (m.condY true - m.condY false) / m.condY true := by
  rw [m.pn_eq_pns_div_of_exogenous (m.exogenous_of_weakExogenous_of_monotonic hw hmono) h11,
    m.pns_eq_of_weakExogenous_of_monotonic hw hmono (m.pX_true_pos h11) hx']

/-- Pearl (2009), Theorem 9.2.14, equation (9.23): under weak exogeneity and monotonicity, `PS`
is the relative difference `(P(y | x) - P(y | x')) / (1 - P(y | x'))`, assuming
`P(x', y') > 0` and `P(x) > 0`. -/
theorem ps_eq_of_weakExogenous_of_monotonic (hw : m.WeakExogenous) (hmono : m.Monotonic)
    (h00 : 0 < m.pXY false false) (hx : 0 < m.pX true) :
    m.PS = (m.condY true - m.condY false) / (1 - m.condY false) := by
  rw [m.ps_eq_pns_div_of_exogenous (m.exogenous_of_weakExogenous_of_monotonic hw hmono) h00,
    m.pns_eq_of_weakExogenous_of_monotonic hw hmono hx (m.pX_false_pos h00)]

/-- Pearl (2009), Theorem 9.2.14, equation (9.21), under strong exogeneity. -/
theorem pns_eq_of_exogenous_of_monotonic (hexo : m.Exogenous) (hmono : m.Monotonic)
    (hx : 0 < m.pX true) (hx' : 0 < m.pX false) :
    m.PNS = m.condY true - m.condY false :=
  m.pns_eq_of_weakExogenous_of_monotonic hexo.weakExogenous hmono hx hx'

/-- Pearl (2009), Theorem 9.2.14, equation (9.22), under strong exogeneity. -/
theorem pn_eq_of_exogenous_of_monotonic (hexo : m.Exogenous) (hmono : m.Monotonic)
    (h11 : 0 < m.pXY true true) (hx' : 0 < m.pX false) :
    m.PN = (m.condY true - m.condY false) / m.condY true :=
  m.pn_eq_of_weakExogenous_of_monotonic hexo.weakExogenous hmono h11 hx'

/-- Pearl (2009), Theorem 9.2.14, equation (9.23), under strong exogeneity. -/
theorem ps_eq_of_exogenous_of_monotonic (hexo : m.Exogenous) (hmono : m.Monotonic)
    (h00 : 0 < m.pXY false false) (hx : 0 < m.pX true) :
    m.PS = (m.condY true - m.condY false) / (1 - m.condY false) :=
  m.ps_eq_of_weakExogenous_of_monotonic hexo.weakExogenous hmono h00 hx

/-! ### Weak exogeneity does not suffice for (9.11), (9.12), (9.19) -/

/-- A weakly but not strongly exogenous model: `X` is a fair coin; given `X = 1` the response
type `(Y0, Y1)` is `(0, 0)` or `(1, 1)` with probability `1/2` each, and given `X = 0` it is
`(0, 1)` or `(1, 0)`. Each potential outcome is a fair coin independent of `X`, but the pair
determines `X`. -/
noncomputable def weakExoCounter : ResponseModel :=
  ofCells (fun x y0 y1 => if x = (y0 == y1) then 1 / 4 else 0)
    (by intro x y0 y1; split_ifs <;> norm_num) (by norm_num)

theorem weakExoCounter_weakExogenous : weakExoCounter.WeakExogenous := by
  constructor <;> intro x <;> cases x <;>
    simp [weakExoCounter, pX_true, pX_false, pY1_eq, pY0_eq] <;> norm_num

theorem not_exogenous_weakExoCounter : ¬ weakExoCounter.Exogenous := fun h => by
  have := h true false true
  simp [weakExoCounter, pX_true, pR_eq] at this
  norm_num at this

theorem weakExoCounter_pos : 0 < weakExoCounter.pXY true true ∧
    0 < weakExoCounter.pXY false false ∧ 0 < weakExoCounter.pY ∧ weakExoCounter.pY < 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [weakExoCounter, pXY_true_true, pXY_false_false, pY_eq, pXY_false_true]
  norm_num

theorem weakExoCounter_pns : weakExoCounter.PNS = 1 / 4 := by
  simp [weakExoCounter, pns_eq]

theorem weakExoCounter_condY :
    weakExoCounter.condY true = 1 / 2 ∧ weakExoCounter.condY false = 1 / 2 := by
  refine ⟨?_, ?_⟩ <;>
    simp [weakExoCounter, condY, pXY_true_true, pXY_false_true, pX_true, pX_false] <;> norm_num

/-- Equation (9.11) fails under weak exogeneity: in `weakExoCounter`, `PN = 0` while
`PNS / P(y | x) = 1/2`. -/
theorem weakExoCounter_pn_ne :
    weakExoCounter.PN ≠ weakExoCounter.PNS / weakExoCounter.condY true := by
  rw [weakExoCounter_pns, weakExoCounter_condY.1]
  simp [weakExoCounter, pn_eq]

/-- Equation (9.12) fails under weak exogeneity: in `weakExoCounter`, `PS = 1` while
`PNS / (1 - P(y | x')) = 1/2`. -/
theorem weakExoCounter_ps_ne :
    weakExoCounter.PS ≠ weakExoCounter.PNS / (1 - weakExoCounter.condY false) := by
  rw [weakExoCounter_pns, weakExoCounter_condY.2]
  simp [weakExoCounter, ps_eq, pXY_false_false]; norm_num

/-- Equation (9.19) for `PD` fails under weak exogeneity: in `weakExoCounter`, `PD = 0` while
`P(x) PNS / P(y) = 1/4`. -/
theorem weakExoCounter_pd_ne :
    weakExoCounter.PD ≠ weakExoCounter.pX true * weakExoCounter.PNS / weakExoCounter.pY := by
  rw [weakExoCounter_pns]
  simp [weakExoCounter, pd_eq, pX_true, pY_eq, pXY_true_true, pXY_false_true]; norm_num

/-- Equation (9.19) for `PE` fails under weak exogeneity: in `weakExoCounter`, `PE = 1/2` while
`P(x') PNS / P(y') = 1/4`. -/
theorem weakExoCounter_pe_ne :
    weakExoCounter.PE ≠
      weakExoCounter.pX false * weakExoCounter.PNS / (1 - weakExoCounter.pY) := by
  rw [weakExoCounter_pns]
  simp [weakExoCounter, pe_eq, pX_false, pY_eq, pXY_true_true, pXY_false_true]; norm_num

end ResponseModel

end Attribution

end CausalInference
