/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Selection on a common effect

Finite results on selection bias for two marginally independent causes `A` and `E` of a
selection or survival indicator.

## Setting

`A` and `E` take values in finite types and are independent with marginal laws `pA` and `pE`.
The selection indicator (survival, being a firefighter, being in the study) has conditional
probability `s a e = P(S = 1 | A = a, E = e)`. The restriction of the joint law to the
selected stratum is the table `stratum pA pE s a e = pA a * pE e * s a e`, the mass of
`{A = a, E = e, S = 1}`. Independence of two variables within a stratum is stated without
division by the scale-free predicate `TableIndep`: every cell times the total mass equals the
product of its row and column totals. Dividing by the square of the stratum mass gives
`P(A = a, E = e | S = 1) = P(A = a | S = 1) P(E = e | S = 1)`.

## Main results

* `colliderExample_marginal_indep`, `colliderExample_selected_not_indep`: treatment and outcome
  independent fair coins, selected if either equals one; independent marginally, dependent among
  the selected (`1/3 ≠ 4/9` after normalization).
* `stratum_indep_of_multiplicative`: the multiplicative survival model of What If Technical
  Point 8.2. If `P(Y = 0 | E = e, A = a) = g(e) h(a)`, then `A` and `E` are independent among the
  survivors.
* `multiplicative_of_stratum_indep`: the converse. If `A ⫫ E`, the margins are positive and
  `A ⫫ E | Y = 0` with `P(Y = 0) > 0`, then the survival probability is multiplicative.
* `causeSpecific_survival`: the derivation in Technical Point 8.2. With
  `Y = Y_A ∨ Y_E ∨ Y_O`, cause-specific deaths independent given `(A, E)`, `Y_A` depending on `A`
  only and `Y_E` on `E` only, `P(Y = 0 | E = e, A = a) = P(Y_O = 0) P(Y_A = 0 | a) P(Y_E = 0 | e)`.
  `causeSpecific_survivors_indep` is the resulting "selection without bias" of section 8.6.
* `deaths_indep_iff`: for binary `A` and `E` with positive margins under a multiplicative
  survival model, `A ⫫ E | Y = 1` holds if and only if `(g 1 - g 0) (h 1 - h 0) = 0`, that is,
  if and only if `A` or `E` has no effect on survival. This makes precise the book's statement
  that `1 - g(e) h(a)` is not multiplicative and so `A` and `E` are dependent given `Y = 1`: the
  dependence holds exactly when both causes affect survival.
* `andMechanism_survivors_not_indep`: a non-multiplicative survival model (death if and only if
  both `A = 1` and `E = 1`) in which `A` and `E` are dependent among the survivors.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman and Hall/CRC (2020),
  section 8.1, section 8.6 (selection without bias) and Technical Point 8.2 (multiplicative
  survival model).
-/

@[expose] public section

namespace CausalInference

namespace Bias

open Finset

/-- Scale-free independence of a two-way table `q` of masses (a joint law, or its restriction to
a stratum): for every cell, `q a b` times the total mass equals the row total of `a` times the
column total of `b`. For a stratum with positive mass this is conditional independence of the
row and column variables given the stratum. -/
def TableIndep {α β : Type*} [Fintype α] [Fintype β] (q : α → β → ℝ) : Prop :=
  ∀ a b, q a b * ∑ a', ∑ b', q a' b' = (∑ b', q a b') * ∑ a', q a' b

/-- A product table `f a * g b` is independent, with no normalization needed. -/
theorem tableIndep_mul {α β : Type*} [Fintype α] [Fintype β] (f : α → ℝ) (g : β → ℝ) :
    TableIndep fun a b ↦ f a * g b := by
  intro a b
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- For a two-by-two table, independence is equivalent to equality of the cross products:
`q 1 1 * q 0 0 = q 1 0 * q 0 1`, that is, an odds ratio of one. -/
theorem tableIndep_bool_iff (q : Bool → Bool → ℝ) :
    TableIndep q ↔ q true true * q false false = q true false * q false true := by
  constructor
  · intro h
    have h11 := h true true
    simp only [Fintype.sum_bool] at h11
    linear_combination h11
  · intro h a b
    cases a <;> cases b <;> simp only [Fintype.sum_bool] <;>
      first | linear_combination h | linear_combination (-1 : ℝ) * h

section Stratum

variable {α β : Type*}

/-- The restriction of the joint law of `(A, E, S)` to the stratum `S = 1`, when `A` and `E` are
independent with marginal laws `pA` and `pE` and `P(S = 1 | A = a, E = e) = s a e`: the mass
`P(A = a, E = e, S = 1) = pA a * pE e * s a e`. With `s = fun _ _ ↦ 1` it is the joint law of
`(A, E)` itself. -/
def stratum (pA : α → ℝ) (pE : β → ℝ) (s : α → β → ℝ) (a : α) (e : β) : ℝ :=
  pA a * pE e * s a e

/-- Selection without bias, the multiplicative survival model (What If, Technical Point 8.2).
If `A ⫫ E` and the selection (survival) probability factorizes as
`P(S = 1 | A = a, E = e) = g(e) h(a)`, then `A` and `E` remain independent in the selected
stratum. -/
theorem stratum_indep_of_multiplicative [Fintype α] [Fintype β] (pA : α → ℝ) (pE : β → ℝ)
    (s : α → β → ℝ) (g : β → ℝ) (h : α → ℝ) (hs : ∀ a e, s a e = g e * h a) :
    TableIndep (stratum pA pE s) := by
  have hq : stratum pA pE s = fun a e ↦ (pA a * h a) * (pE e * g e) := by
    funext a e
    simp only [stratum, hs]
    ring
  rw [hq]
  exact tableIndep_mul _ _

/-- Before selection, `A` and `E` are independent: the table `pA a * pE e` is independent. -/
theorem stratum_one_indep [Fintype α] [Fintype β] (pA : α → ℝ) (pE : β → ℝ) :
    TableIndep (stratum pA pE fun _ _ ↦ 1) :=
  stratum_indep_of_multiplicative pA pE _ (fun _ ↦ 1) (fun _ ↦ 1) fun _ _ ↦ by ring

/-- Converse of the multiplicative survival model. If `A ⫫ E` with positive margins and `A` and
`E` are independent in the selected stratum, which has positive mass, then the selection
probability is multiplicative: `P(S = 1 | A = a, E = e) = g(e) h(a)` for some `g` and `h`. So
with marginally independent causes, independence within a stratum of their common effect holds
exactly under a multiplicative model for that stratum. -/
theorem multiplicative_of_stratum_indep [Fintype α] [Fintype β] (pA : α → ℝ) (pE : β → ℝ)
    (s : α → β → ℝ) (hA : ∀ a, 0 < pA a) (hE : ∀ e, 0 < pE e)
    (hT : 0 < ∑ a, ∑ e, stratum pA pE s a e) (hind : TableIndep (stratum pA pE s)) :
    ∃ g : β → ℝ, ∃ h : α → ℝ, ∀ a e, s a e = g e * h a := by
  set T := ∑ a, ∑ e, stratum pA pE s a e with hTdef
  refine ⟨fun e ↦ (∑ a', stratum pA pE s a' e) / (pE e * T),
    fun a ↦ (∑ e', stratum pA pE s a e') / pA a, fun a e ↦ ?_⟩
  have key := hind a e
  have ha := (hA a).ne'
  have he := (hE e).ne'
  have hT' := hT.ne'
  rw [div_mul_div_comm, eq_div_iff (by positivity)]
  simp only [stratum] at key hTdef ⊢
  linear_combination key + s a e * pE e * pA a * hTdef

/-- With binary `A` and `E` that are independent with positive margins, and a multiplicative
survival model `P(Y = 0 | E = e, A = a) = g(e) h(a)`, the two causes are independent among the
deaths `Y = 1` if and only if `(g 1 - g 0) (h 1 - h 0) = 0`, that is, if and only if one of them
has no effect on survival. What If (Technical Point 8.2) states that `1 - g(e) h(a)` is not
multiplicative and hence `A` and `E` are dependent given `Y = 1`; this theorem is the precise
form: dependence among the deaths holds exactly when both causes affect survival. -/
theorem deaths_indep_iff (pA pE g h : Bool → ℝ) (hA : ∀ a, 0 < pA a) (hE : ∀ e, 0 < pE e) :
    TableIndep (stratum pA pE fun a e ↦ 1 - g e * h a) ↔
      (g true - g false) * (h true - h false) = 0 := by
  rw [tableIndep_bool_iff]
  simp only [stratum]
  have hP : 0 < pA true * pA false * pE true * pE false := by
    have := hA true; have := hA false; have := hE true; have := hE false
    positivity
  constructor
  · intro H
    have key : (pA true * pA false * pE true * pE false) *
        ((g true - g false) * (h true - h false)) = 0 := by
      linear_combination (-1 : ℝ) * H
    exact (mul_eq_zero.mp key).resolve_left hP.ne'
  · intro H
    linear_combination (-(pA true * pA false * pE true * pE false)) * H

end Stratum

section CauseSpecific

variable {α β : Type*}

/-- The law of a binary variable with success probability `p`: `P(B = 1) = p`,
`P(B = 0) = 1 - p`. -/
def bern (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Survival probability in the cause-specific model of What If section 8.6 (Figure 8.13).
Death `Y` is `Y_A ∨ Y_E ∨ Y_O`, where the cause-specific deaths are conditionally independent
given `(A, E)`, `P(Y_A = 1 | A = a, E = e) = qA a` depends on `a` only, `P(Y_E = 1 | ...) = qE e`
depends on `e` only, and `P(Y_O = 1) = qO` depends on neither. The value is
`P(Y = 0 | A = a, E = e)`, the sum of the product law over the cause-specific outcomes that give
`Y = 0`. -/
def causeSpecificSurvival (qA : α → ℝ) (qE : β → ℝ) (qO : ℝ) (a : α) (e : β) : ℝ :=
  ∑ yA : Bool, ∑ yE : Bool, ∑ yO : Bool,
    bern (qA a) yA * bern (qE e) yE * bern qO yO * (if yA || yE || yO then 0 else 1)

/-- The derivation in What If, Technical Point 8.2: in the cause-specific model,
`P(Y = 0 | E = e, A = a) = P(Y_E = 0 | e) * (P(Y_O = 0) P(Y_A = 0 | a))`, a multiplicative
survival model with `g(e) = 1 - qE e` and `h(a) = (1 - qO) (1 - qA a)`. -/
theorem causeSpecific_survival (qA : α → ℝ) (qE : β → ℝ) (qO : ℝ) (a : α) (e : β) :
    causeSpecificSurvival qA qE qO a e = (1 - qE e) * ((1 - qO) * (1 - qA a)) := by
  simp only [causeSpecificSurvival, bern, Fintype.sum_bool]
  norm_num
  ring

/-- Selection without bias (What If, section 8.6): in the cause-specific model with
independent causes `A` and `E`, the two remain independent among the survivors `Y = 0`. -/
theorem causeSpecific_survivors_indep [Fintype α] [Fintype β] (pA : α → ℝ) (pE : β → ℝ)
    (qA : α → ℝ) (qE : β → ℝ) (qO : ℝ) :
    TableIndep (stratum pA pE (causeSpecificSurvival qA qE qO)) :=
  stratum_indep_of_multiplicative pA pE _ (fun e ↦ 1 - qE e) (fun a ↦ (1 - qO) * (1 - qA a))
    (causeSpecific_survival qA qE qO)

/-- In the cause-specific model with binary `A` and `E`, positive margins, and `qO ≠ 1`, the
causes are independent among the deaths `Y = 1` if and only if `qE` or `qA` is constant, that is,
if and only if `A` or `E` has no effect on death. When both have an effect, conditioning on
death creates an association although conditioning on survival does not. -/
theorem causeSpecific_deaths_indep_iff (pA pE qA qE : Bool → ℝ) (qO : ℝ)
    (hA : ∀ a, 0 < pA a) (hE : ∀ e, 0 < pE e) (hO : qO ≠ 1) :
    TableIndep (stratum pA pE fun a e ↦ 1 - causeSpecificSurvival qA qE qO a e) ↔
      (qE true - qE false) * (qA true - qA false) = 0 := by
  have hfun : (fun a e ↦ 1 - causeSpecificSurvival qA qE qO a e) =
      fun a e ↦ 1 - (fun e ↦ 1 - qE e) e * (fun a ↦ (1 - qO) * (1 - qA a)) a := by
    funext a e
    rw [causeSpecific_survival]
  rw [hfun, deaths_indep_iff pA pE _ _ hA hE]
  have hO' : 1 - qO ≠ 0 := sub_ne_zero.mpr (Ne.symm hO)
  constructor
  · intro H
    have key : (1 - qO) * ((qE true - qE false) * (qA true - qA false)) = 0 := by
      linear_combination H
    exact (mul_eq_zero.mp key).resolve_left hO'
  · intro H
    linear_combination (1 - qO) * H

end CauseSpecific

section Examples

/-- The fair coin law on `Bool`. -/
noncomputable def halfLaw (_ : Bool) : ℝ := 1 / 2

/-- Selection on a common effect: an individual with treatment `a` and outcome `y` is selected
if and only if `a = 1` or `y = 1`. -/
def colliderSelection (a y : Bool) : ℝ := if a || y then 1 else 0

/-- In the collider example, treatment and outcome are independent fair coins before selection. -/
theorem colliderExample_marginal_indep : TableIndep (stratum halfLaw halfLaw fun _ _ ↦ 1) :=
  stratum_one_indep _ _

/-- The selected stratum of the collider example has probability `3/4`. -/
theorem colliderExample_selected_mass :
    ∑ a, ∑ y, stratum halfLaw halfLaw colliderSelection a y = 3 / 4 := by
  simp only [stratum, halfLaw, colliderSelection, Fintype.sum_bool]
  norm_num

/-- The normalized numbers of the collider example: among the selected,
`P(A = 1, Y = 1 | S = 1) = 1/3` while `P(A = 1 | S = 1) P(Y = 1 | S = 1) = 2/3 * 2/3 = 4/9`. -/
theorem colliderExample_selected_values :
    stratum halfLaw halfLaw colliderSelection true true / (3 / 4) = 1 / 3 ∧
      (∑ y, stratum halfLaw halfLaw colliderSelection true y) / (3 / 4) *
          ((∑ a, stratum halfLaw halfLaw colliderSelection a true) / (3 / 4)) = 4 / 9 := by
  constructor <;> norm_num [stratum, halfLaw, colliderSelection, Fintype.sum_bool]

/-- Selection bias (What If, section 8.1): treatment and outcome, independent before selection,
are dependent among the selected. Normalized, `P(A = 1, Y = 1 | S = 1) = 1/3` while
`P(A = 1 | S = 1) P(Y = 1 | S = 1) = 4/9`. -/
theorem colliderExample_selected_not_indep :
    ¬ TableIndep (stratum halfLaw halfLaw colliderSelection) := by
  rw [tableIndep_bool_iff]
  simp only [stratum, halfLaw, colliderSelection]
  norm_num

/-- An "and" survival mechanism: death if and only if both `A = 1` and `E = 1`. The survival
probability `1 - [a = 1 ∧ e = 1]` is not multiplicative (the two causes act through a common
mechanism, as in What If Figure 8.14). -/
def andSurvival (a e : Bool) : ℝ := if a && e then 0 else 1

/-- The survivors of the "and" mechanism have probability `3/4`. -/
theorem andMechanism_survivors_mass :
    ∑ a, ∑ e, stratum halfLaw halfLaw andSurvival a e = 3 / 4 := by
  simp only [stratum, halfLaw, andSurvival, Fintype.sum_bool]
  norm_num

/-- Without a multiplicative survival model, selection on survival biases: under the "and"
mechanism, independent fair causes `A` and `E` are dependent among the survivors. -/
theorem andMechanism_survivors_not_indep :
    ¬ TableIndep (stratum halfLaw halfLaw andSurvival) := by
  rw [tableIndep_bool_iff]
  simp only [stratum, halfLaw, andSurvival]
  norm_num

end Examples

end Bias

end CausalInference
