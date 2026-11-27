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
# The built-in selection bias of hazard ratios

A finite two-period survival model with a binary treatment `A`, a binary unmeasured frailty `U`
independent of `A`, death at time 1 `Y1` and death at time 2 `Y2`.

## Setting

`A` has law `pA` and `U` has law `pU`, independently (randomized treatment). The time 1 risk is
`r1 a u = P(Y1 = 1 | A = a, U = u)` and the time 2 risk among the time 1 survivors is
`r2 a u = P(Y2 = 1 | A = a, U = u, Y1 = 0)`. That treatment has no effect at time 2 on anyone
who survives time 1 is the explicit hypothesis `∀ u, r2 true u = r2 false u`. The hazards are
ratios of masses of the joint law: `hazard1 a = P(Y1 = 1 | A = a)` and
`hazard2 a = P(Y2 = 1 | A = a, Y1 = 0)`.

## Main results

* `hazard2_eq_weighted`: the time 2 hazard is `∑ u, P(U = u | A = a, Y1 = 0) * r2 a u`. The
  weights `frailtyWeight a u` condition on survival, which depends on both treatment and frailty.
* `stratumHazard2_eq`: within a stratum of `U`, the time 2 hazard is `r2 a u`, so under no
  effect at time 2 the stratum-specific hazard ratio is one.
* `frailtyWeight_lt_iff`: treated survivors are less likely than untreated survivors to carry
  the frailty level `U = 1` if and only if the survival cross product satisfies
  `s 1 1 * s 0 0 < s 1 0 * s 0 1`, with `s a u = 1 - r1 a u`.
* `hazard2_sub_of_noEffect`, `hazard2_lt_of_noEffect`: under no effect at time 2, the hazard
  difference at time 2 is `(r2 1 - r2 0) (w 1 - w 0)`; if `U = 1` is protective at time 2 and
  the cross-product condition holds, the time 2 hazard is larger in the treated.
* `example_hazardRatio1`, `example_hazardRatio2`, `example_stratum_hazardRatio2`: the numerical
  version of What If Technical Point 8.1 (Figure 8.8). Treatment lowers the time 1 risk in every
  frailty stratum, `U = 1` lowers the risk at both times, and treatment has no effect at time 2.
  The time 1 hazard ratio is `1/3 < 1`, the time 2 hazard ratio is `50/49 > 1`, and the
  stratum-specific time 2 hazard ratios are `1`.

## References

* M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman and Hall/CRC (2020),
  Technical Point 8.1 (the built-in selection bias of hazard ratios).
-/

@[expose] public section

namespace CausalInference

namespace Bias

namespace HazardRatio

open Finset

section General

variable (pA pU : Bool → ℝ) (r1 r2 : Bool → Bool → ℝ)

/-- The mass `P(A = a, Y1 = 1) = ∑ u, pA a pU u r1 a u`. -/
def dead1Mass (a : Bool) : ℝ := ∑ u, pA a * pU u * r1 a u

/-- The mass `P(A = a)` of the treatment arm `a`. -/
def armMass (a : Bool) : ℝ := ∑ u, pA a * pU u

/-- The mass `P(A = a, Y1 = 0) = ∑ u, pA a pU u (1 - r1 a u)` of the time 1 survivors in arm
`a`. -/
def surv1Mass (a : Bool) : ℝ := ∑ u, pA a * pU u * (1 - r1 a u)

/-- The mass `P(A = a, Y1 = 0, Y2 = 1) = ∑ u, pA a pU u (1 - r1 a u) r2 a u`. -/
def dead2Mass (a : Bool) : ℝ := ∑ u, pA a * pU u * (1 - r1 a u) * r2 a u

/-- The time 1 hazard `P(Y1 = 1 | A = a)`, equal to the time 1 risk. -/
noncomputable def hazard1 (a : Bool) : ℝ := dead1Mass pA pU r1 a / armMass pA pU a

/-- The time 2 hazard `P(Y2 = 1 | A = a, Y1 = 0)`: the risk at time 2 among the time 1
survivors. -/
noncomputable def hazard2 (a : Bool) : ℝ := dead2Mass pA pU r1 r2 a / surv1Mass pA pU r1 a

/-- The time 2 hazard within the frailty stratum `U = u`:
`P(Y2 = 1 | A = a, U = u, Y1 = 0)`. -/
noncomputable def stratumHazard2 (a u : Bool) : ℝ :=
  pA a * pU u * (1 - r1 a u) * r2 a u / (pA a * pU u * (1 - r1 a u))

/-- The frailty distribution among the time 1 survivors of arm `a`:
`P(U = u | A = a, Y1 = 0) = pA a pU u (1 - r1 a u) / P(A = a, Y1 = 0)`. -/
noncomputable def frailtyWeight (a u : Bool) : ℝ :=
  pA a * pU u * (1 - r1 a u) / surv1Mass pA pU r1 a

/-- The time 2 hazard conditions on survival: it is the average of the stratum risks `r2 a u`
over the frailty distribution `P(U = u | A = a, Y1 = 0)` of the survivors, which depends on the
arm `a` through `r1 a u` even though `U` is independent of `A`. The weights sum to one when
the survivor mass is nonzero (`frailtyWeight_add`). -/
theorem hazard2_eq_weighted (a : Bool) :
    hazard2 pA pU r1 r2 a = ∑ u, frailtyWeight pA pU r1 a u * r2 a u := by
  simp only [hazard2, frailtyWeight, dead2Mass, div_mul_eq_mul_div, ← Finset.sum_div]

/-- Within a frailty stratum with positive survivor mass, the time 2 hazard is `r2 a u`. -/
theorem stratumHazard2_eq (a u : Bool) (h : pA a * pU u * (1 - r1 a u) ≠ 0) :
    stratumHazard2 pA pU r1 r2 a u = r2 a u := by
  rw [stratumHazard2, mul_div_cancel_left₀ _ h]

/-- Under no effect of treatment at time 2, the stratum-specific time 2 hazard ratio is one: the
conditional hazard ratio correctly shows the absence of an effect. -/
theorem stratum_hazardRatio2_eq_one (u : Bool)
    (hnull : ∀ u, r2 true u = r2 false u)
    (h1 : pA true * pU u * (1 - r1 true u) ≠ 0) (h0 : pA false * pU u * (1 - r1 false u) ≠ 0)
    (hr : r2 false u ≠ 0) :
    stratumHazard2 pA pU r1 r2 true u / stratumHazard2 pA pU r1 r2 false u = 1 := by
  rw [stratumHazard2_eq pA pU r1 r2 true u h1, stratumHazard2_eq pA pU r1 r2 false u h0,
    hnull u, div_self hr]

/-- Selection by survival. With `0 < pU u`, positive arm probabilities and positive survival
probabilities `s a u = 1 - r1 a u`, the treated survivors are less likely than the untreated
survivors to have `U = 1` if and only if `s 1 1 * s 0 0 < s 1 0 * s 0 1`, that is, if and only if
treatment improves survival relatively more in the stratum `U = 0`. -/
theorem frailtyWeight_lt_iff (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hs : ∀ a u, 0 < 1 - r1 a u) :
    frailtyWeight pA pU r1 true true < frailtyWeight pA pU r1 false true ↔
      (1 - r1 true true) * (1 - r1 false false) < (1 - r1 true false) * (1 - r1 false true) := by
  have hS : ∀ a, 0 < surv1Mass pA pU r1 a := fun a ↦ by
    simp only [surv1Mass, Fintype.sum_bool]
    have := hA a; have := hU true; have := hU false; have := hs a true; have := hs a false
    positivity
  rw [frailtyWeight, frailtyWeight, div_lt_div_iff₀ (hS true) (hS false)]
  simp only [surv1Mass, Fintype.sum_bool]
  have hP : 0 < pA true * pA false * pU true * pU false := by
    have := hA true; have := hA false; have := hU true; have := hU false
    positivity
  constructor
  · intro H
    have key : 0 < (pA true * pA false * pU true * pU false) *
        ((1 - r1 true false) * (1 - r1 false true) - (1 - r1 true true) * (1 - r1 false false)) :=
      by linarith
    have := (pos_iff_pos_of_mul_pos key).mp hP
    linarith
  · intro H
    have : 0 < (1 - r1 true false) * (1 - r1 false true) -
        (1 - r1 true true) * (1 - r1 false false) := by linarith
    nlinarith

/-- When the survivor mass of arm `a` is nonzero, the survivors' frailty distribution is a
probability distribution: `P(U = 1 | A = a, Y1 = 0) + P(U = 0 | A = a, Y1 = 0) = 1`. -/
theorem frailtyWeight_add (a : Bool) (ha : surv1Mass pA pU r1 a ≠ 0) :
    frailtyWeight pA pU r1 a true + frailtyWeight pA pU r1 a false = 1 := by
  simp only [frailtyWeight, ← add_div]
  rw [div_eq_one_iff_eq ha, surv1Mass, Fintype.sum_bool]

/-- Under no effect of treatment at time 2 (`r2 a u = r2 0 u` for both arms), the difference of
the time 2 hazards is `(r2 · 1 - r2 · 0) (w 1 1 - w 0 1)`, where `w a 1 = P(U = 1 | A = a,
Y1 = 0)`. It is nonzero as soon as the frailty affects time 2 risk and the survivors' frailty
distributions differ between the arms. -/
theorem hazard2_sub_of_noEffect (hnull : ∀ u, r2 true u = r2 false u)
    (h1 : surv1Mass pA pU r1 true ≠ 0) (h0 : surv1Mass pA pU r1 false ≠ 0) :
    hazard2 pA pU r1 r2 true - hazard2 pA pU r1 r2 false =
      (r2 false true - r2 false false) *
        (frailtyWeight pA pU r1 true true - frailtyWeight pA pU r1 false true) := by
  have hw : ∀ a, surv1Mass pA pU r1 a ≠ 0 →
      frailtyWeight pA pU r1 a false = 1 - frailtyWeight pA pU r1 a true := fun a ha ↦ by
    rw [eq_sub_iff_add_eq, add_comm, frailtyWeight_add pA pU r1 a ha]
  rw [hazard2_eq_weighted pA pU r1 r2 true, hazard2_eq_weighted pA pU r1 r2 false]
  simp only [Fintype.sum_bool, hnull, hw true h1, hw false h0]
  ring

/-- The built-in selection bias of the time 2 hazard ratio. Under no effect of treatment at
time 2, if `U = 1` is protective at time 2 (`r2 · 1 < r2 · 0`) and treatment improves time 1
survival relatively more in the stratum `U = 0`, then the time 2 hazard is larger in the treated
than in the untreated. -/
theorem hazard2_lt_of_noEffect (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hs : ∀ a u, 0 < 1 - r1 a u) (hnull : ∀ u, r2 true u = r2 false u)
    (hprot : r2 false true < r2 false false)
    (hsel : (1 - r1 true true) * (1 - r1 false false) < (1 - r1 true false) * (1 - r1 false true)) :
    hazard2 pA pU r1 r2 false < hazard2 pA pU r1 r2 true := by
  have hS : ∀ a, 0 < surv1Mass pA pU r1 a := fun a ↦ by
    simp only [surv1Mass, Fintype.sum_bool]
    have := hA a; have := hU true; have := hU false; have := hs a true; have := hs a false
    positivity
  have hd := hazard2_sub_of_noEffect pA pU r1 r2 hnull (hS true).ne' (hS false).ne'
  have hw := (frailtyWeight_lt_iff pA pU r1 hA hU hs).mpr hsel
  have : 0 < hazard2 pA pU r1 r2 true - hazard2 pA pU r1 r2 false := by
    rw [hd]
    exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

end General

section Example

/-- Fair laws for treatment and frailty. -/
noncomputable def exHalf (_ : Bool) : ℝ := 1 / 2

/-- Time 1 risks `r1 a u`: `1/2` untreated without the protective haplotype, `1/4` treated
without it or untreated with it, `0` treated with it. -/
noncomputable def exR1 (a u : Bool) : ℝ :=
  if a then (if u then 0 else 1 / 4) else (if u then 1 / 4 else 1 / 2)

/-- Time 2 risks among the survivors: `1/4` with the protective haplotype `U = 1`, `1/2` without
it, whatever the treatment (no effect of treatment at time 2). -/
noncomputable def exR2 (_ u : Bool) : ℝ := if u then 1 / 4 else 1 / 2

theorem example_noEffect : ∀ u, exR2 true u = exR2 false u := fun _ ↦ rfl

/-- In the example, treatment lowers the time 1 risk in each frailty stratum, the haplotype
`U = 1` lowers the risk at both times, and all time 1 survival probabilities are positive. -/
theorem example_structure :
    (∀ u, exR1 true u < exR1 false u) ∧ (∀ a, exR1 a true < exR1 a false) ∧
      exR2 false true < exR2 false false ∧ ∀ a u, 0 < 1 - exR1 a u := by
  refine ⟨fun u ↦ ?_, fun a ↦ ?_, ?_, fun a u ↦ ?_⟩
  · cases u <;> norm_num [exR1]
  · cases a <;> norm_num [exR1]
  · norm_num [exR2]
  · cases a <;> cases u <;> norm_num [exR1]

/-- The time 1 hazards are `1/8` (treated) and `3/8` (untreated): hazard ratio `1/3 < 1`. -/
theorem example_hazardRatio1 :
    hazard1 exHalf exHalf exR1 true = 1 / 8 ∧ hazard1 exHalf exHalf exR1 false = 3 / 8 ∧
      hazard1 exHalf exHalf exR1 true / hazard1 exHalf exHalf exR1 false = 1 / 3 := by
  have h1 : hazard1 exHalf exHalf exR1 true = 1 / 8 := by
    norm_num [hazard1, dead1Mass, armMass, exHalf, exR1, Fintype.sum_bool]
  have h0 : hazard1 exHalf exHalf exR1 false = 3 / 8 := by
    norm_num [hazard1, dead1Mass, armMass, exHalf, exR1, Fintype.sum_bool]
  refine ⟨h1, h0, ?_⟩
  rw [h1, h0]
  norm_num

/-- The time 2 hazards are `5/14` (treated) and `7/20` (untreated): hazard ratio `50/49 > 1`,
although treatment has no effect at time 2. The hazards have crossed. -/
theorem example_hazardRatio2 :
    hazard2 exHalf exHalf exR1 exR2 true = 5 / 14 ∧
      hazard2 exHalf exHalf exR1 exR2 false = 7 / 20 ∧
      hazard2 exHalf exHalf exR1 exR2 true / hazard2 exHalf exHalf exR1 exR2 false = 50 / 49 := by
  have h1 : hazard2 exHalf exHalf exR1 exR2 true = 5 / 14 := by
    norm_num [hazard2, dead2Mass, surv1Mass, exHalf, exR1, exR2, Fintype.sum_bool]
  have h0 : hazard2 exHalf exHalf exR1 exR2 false = 7 / 20 := by
    norm_num [hazard2, dead2Mass, surv1Mass, exHalf, exR1, exR2, Fintype.sum_bool]
  refine ⟨h1, h0, ?_⟩
  rw [h1, h0]
  norm_num

/-- The survivors' frailty distributions differ between the arms:
`P(U = 1 | A = 1, Y1 = 0) = 4/7 < 3/5 = P(U = 1 | A = 0, Y1 = 0)`. -/
theorem example_frailtyWeight :
    frailtyWeight exHalf exHalf exR1 true true = 4 / 7 ∧
      frailtyWeight exHalf exHalf exR1 false true = 3 / 5 := by
  constructor <;> norm_num [frailtyWeight, surv1Mass, exHalf, exR1, Fintype.sum_bool]

/-- In each frailty stratum of the example the time 2 hazard ratio is one: the stratum hazards
are `1/4` (for `U = 1`) and `1/2` (for `U = 0`) in both arms. -/
theorem example_stratum_hazardRatio2 (u : Bool) :
    stratumHazard2 exHalf exHalf exR1 exR2 true u /
        stratumHazard2 exHalf exHalf exR1 exR2 false u = 1 := by
  refine stratum_hazardRatio2_eq_one _ _ _ _ u example_noEffect ?_ ?_ ?_ <;>
    cases u <;> norm_num [exHalf, exR1, exR2]

end Example

end HazardRatio

end Bias

end CausalInference
