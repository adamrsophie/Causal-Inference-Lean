/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Probabilities of causation for a binary treatment and a binary outcome

A finite response-type model for a binary treatment `X` and a binary outcome `Y`. Each unit has
a treatment `X` and a pair of potential outcomes `(Y0, Y1)`, all Boolean. The model is a table
of eight nonnegative weights `w x y0 y1` summing to one: the joint law of `(X, Y0, Y1)`. The
observed outcome is `Y = Y1` if `X` is true and `Y = Y0` otherwise, so consistency is built in.

Experimental quantities are the marginals `P(Y1 = 1)` and `P(Y0 = 1)`, written `P(y_x)` and
`P(y_x')` in Pearl's notation. Observational quantities are the joint law of `(X, Y)`.

## Main definitions

* `Attribution.ResponseModel`: the eight weights with nonnegativity and normalization.
* `Attribution.ResponseModel.prob`: the probability of a Boolean event in `(X, Y0, Y1)`.
* `Attribution.ResponseModel.pY1`, `pY0`: the experimental quantities `P(y_x)`, `P(y_x')`.
* `Attribution.ResponseModel.pXY`, `pX`, `pY`: the observational law of `(X, Y)`.
* `Attribution.ResponseModel.PN`: probability of necessity `P(Y0 = 0 | X = 1, Y = 1)`.
* `Attribution.ResponseModel.PS`: probability of sufficiency `P(Y1 = 1 | X = 0, Y = 0)`.
* `Attribution.ResponseModel.PNS`: probability of necessity and sufficiency
  `P(Y1 = 1, Y0 = 0)`.

## Main results

* `Attribution.ResponseModel.pns_eq_add`: the division-free decomposition
  `P(Y1, ¬Y0) = P(¬Y0, X, Y) + P(Y1, ¬X, ¬Y)`.
* `Attribution.ResponseModel.pns_eq_pXY_mul_pn_add`: Lemma 9.2.6 of Pearl (2009),
  `PNS = P(x, y) PN + P(x', y') PS`, under positivity of both conditioning events.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge University Press,
  2009, Section 9.2.1 (Definitions 9.2.1 to 9.2.3, Lemma 9.2.6).
* J. Pearl, M. Glymour, N. P. Jewell, *Causal Inference in Statistics: A Primer*, Wiley, 2016,
  equations (4.23) to (4.25).
-/

@[expose] public section

namespace CausalInference

namespace Attribution

/-- A finite response-type model for binary `X` and `Y`: a joint law of the treatment `X` and
the potential outcomes `(Y0, Y1)`, given as eight nonnegative weights `w x y0 y1` summing to
one. -/
structure ResponseModel where
  /-- The weight of the cell `X = x`, `Y0 = y0`, `Y1 = y1`. -/
  w : Bool → Bool → Bool → ℝ
  /-- Every weight is nonnegative. -/
  nonneg : ∀ x y0 y1, 0 ≤ w x y0 y1
  /-- The weights sum to one. -/
  sum_eq_one : ∑ x, ∑ y0, ∑ y1, w x y0 y1 = 1

namespace ResponseModel

variable (m : ResponseModel)

/-- The observed outcome of a unit with treatment `x` and potential outcomes `(y0, y1)`:
`Y = Y1` if `x` is true and `Y = Y0` otherwise (consistency). -/
def obsY (x y0 y1 : Bool) : Bool := cond x y1 y0

/-- The probability of a Boolean event `E` of `(X, Y0, Y1)`: the total weight of the cells on
which `E` holds. -/
def prob (E : Bool → Bool → Bool → Bool) : ℝ :=
  ∑ x, ∑ y0, ∑ y1, if E x y0 y1 then m.w x y0 y1 else 0

/-- The experimental quantity `P(y_x) = P(Y1 = 1)`. -/
def pY1 : ℝ := m.prob fun _ _ y1 => y1

/-- The experimental quantity `P(y_x') = P(Y0 = 1)`. -/
def pY0 : ℝ := m.prob fun _ y0 _ => y0

/-- The observational quantity `P(X = a, Y = b)`. -/
def pXY (a b : Bool) : ℝ := m.prob fun x y0 y1 => x == a && obsY x y0 y1 == b

/-- The observational quantity `P(X = a)`. -/
def pX (a : Bool) : ℝ := m.prob fun x _ _ => x == a

/-- The observational quantity `P(Y = 1)`. -/
def pY : ℝ := m.prob fun x y0 y1 => obsY x y0 y1

/-- The probability of necessity (Pearl 2009, Definition 9.2.1):
`PN = P(Y0 = 0 | X = 1, Y = 1)`. It is meaningful only when `P(X = 1, Y = 1) > 0`, which every
theorem about it assumes. -/
noncomputable def PN : ℝ :=
  m.prob (fun x y0 y1 => !y0 && x && obsY x y0 y1) / m.pXY true true

/-- The probability of sufficiency (Pearl 2009, Definition 9.2.2):
`PS = P(Y1 = 1 | X = 0, Y = 0)`. It is meaningful only when `P(X = 0, Y = 0) > 0`, which every
theorem about it assumes. -/
noncomputable def PS : ℝ :=
  m.prob (fun x y0 y1 => y1 && !x && !obsY x y0 y1) / m.pXY false false

/-- The probability of necessity and sufficiency (Pearl 2009, Definition 9.2.3):
`PNS = P(Y1 = 1, Y0 = 0)`. -/
def PNS : ℝ := m.prob fun _ y0 y1 => y1 && !y0

/-! ### Cell expansions

Each quantity written as an explicit sum of cells. Later proofs reduce to linear arithmetic
over the eight weights. -/

theorem sum_cells : m.w true false false + m.w true false true + m.w true true false +
    m.w true true true + m.w false false false + m.w false false true +
    m.w false true false + m.w false true true = 1 := by
  have h := m.sum_eq_one
  simp only [Fintype.sum_bool] at h
  linarith

theorem pY1_eq : m.pY1 = m.w true false true + m.w true true true + m.w false false true +
    m.w false true true := by
  simp [pY1, prob]; ring

theorem pY0_eq : m.pY0 = m.w true true false + m.w true true true + m.w false true false +
    m.w false true true := by
  simp [pY0, prob]; ring

theorem pXY_true_true : m.pXY true true = m.w true false true + m.w true true true := by
  simp [pXY, prob, obsY]; ring

theorem pXY_true_false : m.pXY true false = m.w true false false + m.w true true false := by
  simp [pXY, prob, obsY]; ring

theorem pXY_false_true : m.pXY false true = m.w false true false + m.w false true true := by
  simp [pXY, prob, obsY]; ring

theorem pXY_false_false : m.pXY false false = m.w false false false + m.w false false true := by
  simp [pXY, prob, obsY]; ring

theorem pX_true : m.pX true = m.w true false false + m.w true false true +
    m.w true true false + m.w true true true := by
  simp [pX, prob]; ring

theorem pX_false : m.pX false = m.w false false false + m.w false false true +
    m.w false true false + m.w false true true := by
  simp [pX, prob]; ring

theorem pY_eq : m.pY = m.pXY true true + m.pXY false true := by
  rw [pXY_true_true, pXY_false_true]
  simp [pY, prob, obsY]; ring

theorem pns_eq : m.PNS = m.w true false true + m.w false false true := by
  simp [PNS, prob]

theorem pn_num_eq : m.prob (fun x y0 y1 => !y0 && x && obsY x y0 y1) = m.w true false true := by
  simp [prob, obsY]

theorem ps_num_eq : m.prob (fun x y0 y1 => y1 && !x && !obsY x y0 y1) =
    m.w false false true := by
  simp [prob, obsY]

theorem pn_eq : m.PN = m.w true false true / m.pXY true true := by
  rw [PN, pn_num_eq]

theorem ps_eq : m.PS = m.w false false true / m.pXY false false := by
  rw [PS, ps_num_eq]

/-! ### Lemma 9.2.6 -/

/-- Division-free form of Pearl's Lemma 9.2.6:
`P(Y1 = 1, Y0 = 0) = P(Y0 = 0, X = 1, Y = 1) + P(Y1 = 1, X = 0, Y = 0)`. It follows from
consistency alone. -/
theorem pns_eq_add : m.PNS = m.prob (fun x y0 y1 => !y0 && x && obsY x y0 y1) +
    m.prob (fun x y0 y1 => y1 && !x && !obsY x y0 y1) := by
  rw [pns_eq, pn_num_eq, ps_num_eq]

/-- Pearl (2009), Lemma 9.2.6, equation (9.5): `PNS = P(x, y) PN + P(x', y') PS`, assuming
`P(X = 1, Y = 1) > 0` and `P(X = 0, Y = 0) > 0` so that `PN` and `PS` are genuine conditional
probabilities. -/
theorem pns_eq_pXY_mul_pn_add (h11 : 0 < m.pXY true true) (h00 : 0 < m.pXY false false) :
    m.PNS = m.pXY true true * m.PN + m.pXY false false * m.PS := by
  rw [pns_eq, pn_eq, ps_eq, mul_div_cancel₀ _ h11.ne', mul_div_cancel₀ _ h00.ne']

end ResponseModel

end Attribution

end CausalInference
