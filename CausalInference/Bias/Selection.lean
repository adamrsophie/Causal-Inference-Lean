/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
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
* `tableIndep_bool_iff_ratio`, `tableIndep_iff_normalized`: the odds ratio reading of the
  cross-product criterion (under a positive cross product) and the probability reading of
  `TableIndep` (under positive total mass). `stratum_condIndep_of_multiplicative` and
  `deaths_condIndep_iff` restate the two stratum results for the normalized cells, assuming a
  positive selected mass.
* `multiplicative_iff_ratio_const`: the multiplicative survival model holds if and only if the
  survival ratio `s a e / s a₀ e` does not depend on `e` (Technical Point 8.2).
* `orMechanism_deaths_negative`, `andMechanism_deaths_positive`: the direction of the bias among
  the deaths (Fine Point 8.2): negative association under an "or" mechanism, positive under an
  "and" mechanism with a positive baseline death probability.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman and Hall/CRC (2020),
  section 8.1, section 8.6 (selection without bias), Technical Point 8.2 (multiplicative
  survival model) and Fine Point 8.2 (the strength and direction of selection bias).
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
`q 1 1 * q 0 0 = q 1 0 * q 0 1`. This needs no positivity. It reads as an odds ratio of one
only when the cross product `q 1 0 * q 0 1` is positive (`tableIndep_bool_iff_ratio`): a point
mass at `(0, 0)` is independent while its odds ratio is `0 / 0`. -/
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

/-- The odds ratio reading of `tableIndep_bool_iff`: when the cross product `q 1 0 * q 0 1` is
positive, a two-by-two table is independent if and only if its odds ratio
`q 1 1 q 0 0 / (q 1 0 q 0 1)` equals one. -/
theorem tableIndep_bool_iff_ratio (q : Bool → Bool → ℝ)
    (hpos : 0 < q true false * q false true) :
    TableIndep q ↔ q true true * q false false / (q true false * q false true) = 1 := by
  rw [tableIndep_bool_iff, div_eq_one_iff_eq hpos.ne']

/-- The probability reading of `TableIndep`. For a table with positive total mass `T`, the
table is independent if and only if the normalized cells `q a b / T` (the conditional law given
the stratum the table describes) factorize into the product of their margins. -/
theorem tableIndep_iff_normalized {α β : Type*} [Fintype α] [Fintype β] (q : α → β → ℝ)
    (hT : 0 < ∑ a, ∑ b, q a b) :
    TableIndep q ↔ ∀ a b, q a b / (∑ a', ∑ b', q a' b') =
      (∑ b', q a b' / (∑ a', ∑ b', q a' b')) * ∑ a', q a' b / (∑ a', ∑ b', q a' b') := by
  unfold TableIndep
  set T := ∑ a, ∑ b, q a b with hTdef
  have hT' : T ≠ 0 := hT.ne'
  refine forall_congr' fun a ↦ forall_congr' fun b ↦ ?_
  rw [← Finset.sum_div, ← Finset.sum_div, div_mul_div_comm,
    div_eq_div_iff hT' (mul_ne_zero hT' hT')]
  constructor
  · intro h
    linear_combination T * h
  · intro h
    have h2 : T * (q a b * T - (∑ b', q a b') * ∑ a', q a' b) = 0 := by linear_combination h
    linear_combination (mul_eq_zero.mp h2).resolve_left hT'

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

/-- The probability form of `stratum_indep_of_multiplicative`. Under a multiplicative survival
model and with positive selected mass `T = P(S = 1)`, the conditional law of `(A, E)` given
`S = 1`, the normalized cells `P(A = a, E = e, S = 1) / T`, is the product of its margins:
`P(A = a, E = e | S = 1) = P(A = a | S = 1) P(E = e | S = 1)`. -/
theorem stratum_condIndep_of_multiplicative [Fintype α] [Fintype β] (pA : α → ℝ) (pE : β → ℝ)
    (s : α → β → ℝ) (g : β → ℝ) (h : α → ℝ) (hs : ∀ a e, s a e = g e * h a)
    (hT : 0 < ∑ a, ∑ e, stratum pA pE s a e) (a : α) (e : β) :
    stratum pA pE s a e / (∑ a', ∑ e', stratum pA pE s a' e') =
      (∑ e', stratum pA pE s a e' / (∑ a', ∑ e', stratum pA pE s a' e')) *
        ∑ a', stratum pA pE s a' e / (∑ a', ∑ e', stratum pA pE s a' e') :=
  (tableIndep_iff_normalized _ hT).mp (stratum_indep_of_multiplicative pA pE s g h hs) a e

/-- The probability form of `deaths_indep_iff`. With binary `A` and `E`, positive margins, a
multiplicative survival model and positive death mass `P(Y = 1)`, the conditional law of
`(A, E)` given `Y = 1` factorizes into its margins if and only if
`(g 1 - g 0) (h 1 - h 0) = 0`. -/
theorem deaths_condIndep_iff (pA pE g h : Bool → ℝ) (hA : ∀ a, 0 < pA a) (hE : ∀ e, 0 < pE e)
    (hT : 0 < ∑ a, ∑ e, stratum pA pE (fun a e ↦ 1 - g e * h a) a e) :
    (∀ a e, stratum pA pE (fun a e ↦ 1 - g e * h a) a e /
        (∑ a', ∑ e', stratum pA pE (fun a e ↦ 1 - g e * h a) a' e') =
      (∑ e', stratum pA pE (fun a e ↦ 1 - g e * h a) a e' /
          (∑ a', ∑ e', stratum pA pE (fun a e ↦ 1 - g e * h a) a' e')) *
        ∑ a', stratum pA pE (fun a e ↦ 1 - g e * h a) a' e /
          (∑ a', ∑ e', stratum pA pE (fun a e ↦ 1 - g e * h a) a' e')) ↔
      (g true - g false) * (h true - h false) = 0 := by
  rw [← tableIndep_iff_normalized _ hT, deaths_indep_iff pA pE g h hA hE]

/-- The multiplicative survival model as a constant survival ratio (What If, Technical Point
8.2). Fix a reference level `a₀` with `s a₀ e ≠ 0` for every `e`. Then `s a e = g(e) h(a)` for
some `g` and `h` if and only if the survival ratio `s a e / s a₀ e` does not depend on `e`,
that is, there is no multiplicative interaction of `A` and `E` on survival. -/
theorem multiplicative_iff_ratio_const (s : α → β → ℝ) (a₀ : α) (hs : ∀ e, s a₀ e ≠ 0) :
    (∃ g : β → ℝ, ∃ h : α → ℝ, ∀ a e, s a e = g e * h a) ↔
      ∀ a e e', s a e / s a₀ e = s a e' / s a₀ e' := by
  constructor
  · rintro ⟨g, h, hgh⟩ a e e'
    have he : g e * h a₀ ≠ 0 := hgh a₀ e ▸ hs e
    have he' : g e' * h a₀ ≠ 0 := hgh a₀ e' ▸ hs e'
    rw [hgh a e, hgh a₀ e, hgh a e', hgh a₀ e', div_eq_div_iff he he']
    ring
  · intro H
    rcases isEmpty_or_nonempty β with hβ | hβ
    · exact ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ e ↦ hβ.elim e⟩
    obtain ⟨e₀⟩ := hβ
    refine ⟨fun e ↦ s a₀ e, fun a ↦ s a e₀ / s a₀ e₀, fun a e ↦ ?_⟩
    change s a e = s a₀ e * (s a e₀ / s a₀ e₀)
    rw [← H a e e₀, mul_div_cancel₀ _ (hs e)]

end Stratum

section Direction

/-! ### The direction of the bias (What If, Fine Point 8.2)

The death probability `d a e = P(Y = 1 | A = a, E = e)` has a baseline `m`, and a mechanism
adds an excess `k` on some cells. Under an "or" mechanism the excess applies when `A = 1` or
`E = 1`; under an "and" mechanism only when both hold. Fine Point 8.2 has a background factor
`U` with prevalence `u`, unassociated with `A` and `E`, that enables the mechanism. If death
outside the mechanism happens at rate `b` among those without `U`, then `d a e` is
`u [mechanism] + (1 - u) b`, which is the form below with `m = (1 - u) b` and `k = u`. The
baseline is a re-derivation: without it (`m = 0`) the "and" mechanism puts every death in the
cell `A = E = 1`, and the death stratum then shows no association at all (both cross products
are zero). -/

/-- For binary `A` and `E` with independent margins, the cross product difference of a stratum
is the cross product difference of the selection probabilities times the margins. -/
theorem stratum_cross_sub (pA pE : Bool → ℝ) (d : Bool → Bool → ℝ) :
    stratum pA pE d true true * stratum pA pE d false false -
        stratum pA pE d true false * stratum pA pE d false true =
      pA true * pA false * pE true * pE false *
        (d true true * d false false - d true false * d false true) := by
  simp only [stratum]
  ring

/-- Death probability under an "or" mechanism with baseline `m` and excess `k`. -/
def orDeath (m k : ℝ) (a e : Bool) : ℝ := if a || e then m + k else m

/-- Death probability under an "and" mechanism with baseline `m` and excess `k`. -/
def andDeath (m k : ℝ) (a e : Bool) : ℝ := if a && e then m + k else m

/-- Under an "or" mechanism (What If, Fine Point 8.2), marginally independent causes with
positive margins are negatively associated among the deaths: the cross product
`q 1 1 q 0 0` of the death stratum is smaller than `q 1 0 q 0 1`, so the odds ratio is below
one. It needs `m ≥ 0` and a positive excess `k`. -/
theorem orMechanism_deaths_negative (pA pE : Bool → ℝ) (hA : ∀ a, 0 < pA a)
    (hE : ∀ e, 0 < pE e) (m k : ℝ) (hm : 0 ≤ m) (hk : 0 < k) :
    stratum pA pE (orDeath m k) true true * stratum pA pE (orDeath m k) false false <
      stratum pA pE (orDeath m k) true false * stratum pA pE (orDeath m k) false true := by
  have h := stratum_cross_sub pA pE (orDeath m k)
  simp only [orDeath, Bool.or_self, Bool.or_true, Bool.or_false, ↓reduceIte,
    Bool.false_eq_true] at h
  have hP : 0 < pA true * pA false * pE true * pE false := by
    have := hA true; have := hA false; have := hE true; have := hE false
    positivity
  have : (m + k) * m - (m + k) * (m + k) < 0 := by nlinarith
  nlinarith

/-- Under an "and" mechanism (What If, Fine Point 8.2), marginally independent causes with
positive margins are positively associated among the deaths: the cross product `q 1 1 q 0 0`
of the death stratum exceeds `q 1 0 q 0 1`, so the odds ratio is above one. It needs a positive
baseline `m` and a positive excess `k`. -/
theorem andMechanism_deaths_positive (pA pE : Bool → ℝ) (hA : ∀ a, 0 < pA a)
    (hE : ∀ e, 0 < pE e) (m k : ℝ) (hm : 0 < m) (hk : 0 < k) :
    stratum pA pE (andDeath m k) true false * stratum pA pE (andDeath m k) false true <
      stratum pA pE (andDeath m k) true true * stratum pA pE (andDeath m k) false false := by
  have h := stratum_cross_sub pA pE (andDeath m k)
  simp only [andDeath, Bool.and_self, Bool.and_true, Bool.and_false, ↓reduceIte,
    Bool.false_eq_true] at h
  have hP : 0 < pA true * pA false * pE true * pE false := by
    have := hA true; have := hA false; have := hE true; have := hE false
    positivity
  have : 0 < (m + k) * m - m * m := by nlinarith
  nlinarith

/-- Without a baseline the "and" mechanism leaves no association among the deaths: every death
has `A = E = 1`, and the death stratum is independent (both cross products are zero). -/
theorem andMechanism_deaths_indep_of_zero (pA pE : Bool → ℝ) (k : ℝ) :
    TableIndep (stratum pA pE (andDeath 0 k)) := by
  rw [tableIndep_bool_iff]
  simp [stratum, andDeath]

end Direction

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
