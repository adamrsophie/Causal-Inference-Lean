/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.DifferenceInDifferences.Staggered
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Two-way fixed effects under staggered adoption: a negative result

A concrete balanced panel with two equally sized cohorts and three periods (`0, 1, 2`): the
early cohort is first treated in period `1`, the late cohort in period `2`, and nobody is never
treated. Untreated outcomes are `0`, so parallel trends and no anticipation hold exactly, but
treatment effects are heterogeneous over time.

The static two-way fixed effects estimand is the coefficient on the treatment indicator in the
least squares regression of the outcome on cohort dummies, period dummies, and the treatment
indicator. It is defined by its closed form `twfeCoef a b c = a - b / 2 + c / 2`, and we prove
that this closed form satisfies the normal equations (`normalEquations_twfeCoef`) and is the
only treatment coefficient that does (`eq_twfeCoef_of_normalEquations`).

## Main results

* `twfeCoef_eq_sum_twfeWeight`, `twfeWeight_one_neg`: the estimand puts weight `-1/2` on the
  group-time effect of the early cohort in the last period.
* `twfe_not_convex_combination`: with group-time effects `1, 4, 1` (computed with
  `Staggered.att` in an explicit staggered adoption model) the estimand is `-1/2`: wrong sign,
  and not in the convex hull of the group-time effects.

Sources: Goodman-Bacon (2021), *Difference-in-differences with variation in treatment timing*;
Sun and Abraham (2021), *Estimating dynamic treatment effects in event studies with
heterogeneous treatment effects*.
-/

@[expose] public section

namespace CausalInference

namespace EventStudy

open Finset

/-- Adoption period of each cohort, with periods `0, 1, 2`: cohort `0` (early) is first treated
in period `1`, cohort `1` (late) in period `2`. There is no never-treated cohort. -/
def adoption : Fin 2 → ℕ := ![1, 2]

/-- The treatment indicator of cohort `i` in period `t`: `1` from the adoption period on. -/
noncomputable def treat (i : Fin 2) (t : Fin 3) : ℝ := if adoption i ≤ (t : ℕ) then 1 else 0

/-- Cohort-time treatment effects, parameterized by `a = ATT(early, 1)`, `b = ATT(early, 2)`,
`c = ATT(late, 2)`; effects are `0` before adoption. -/
def effect (a b c : ℝ) : Fin 2 → Fin 3 → ℝ := ![![0, a, b], ![0, 0, c]]

/-- The cohort-time mean outcome. Untreated potential outcomes are `0` in every cell (so
parallel trends holds exactly), and the observed outcome is the treatment effect when treated. -/
noncomputable def outcome (a b c : ℝ) (i : Fin 2) (t : Fin 3) : ℝ :=
  treat i t * effect a b c i t

/-- The residual of the two-way fixed effects fit with cohort effects `α`, period effects `δ`,
and treatment coefficient `β`. -/
noncomputable def resid (y : Fin 2 → Fin 3 → ℝ) (α : Fin 2 → ℝ) (δ : Fin 3 → ℝ) (β : ℝ)
    (i : Fin 2) (t : Fin 3) : ℝ :=
  y i t - α i - δ t - β * treat i t

/-- The **normal equations** of the least squares regression of the outcome on cohort dummies,
period dummies, and the treatment indicator, for a balanced panel with equally sized cohorts:
the residual is orthogonal to every cohort dummy, every period dummy, and the treatment
indicator. -/
def NormalEquations (y : Fin 2 → Fin 3 → ℝ) (α : Fin 2 → ℝ) (δ : Fin 3 → ℝ) (β : ℝ) : Prop :=
  (∀ i, ∑ t, resid y α δ β i t = 0) ∧ (∀ t, ∑ i, resid y α δ β i t = 0) ∧
    ∑ i, ∑ t, treat i t * resid y α δ β i t = 0

/-- The closed form of the static two-way fixed effects coefficient in this design:
`β = a - b / 2 + c / 2`. -/
noncomputable def twfeCoef (a b c : ℝ) : ℝ := a - b / 2 + c / 2

/-- Cohort effects solving the normal equations together with `twfeCoef`: the cohort means of
`outcome - β * treat`, with `β = twfeCoef a b c`. -/
noncomputable def twfeCohortEffect (a b c : ℝ) : Fin 2 → ℝ :=
  ![(a + b - 2 * twfeCoef a b c) / 3, (c - twfeCoef a b c) / 3]

/-- Period effects solving the normal equations together with `twfeCoef`: the period means of
`outcome - β * treat` minus the grand mean, with `β = twfeCoef a b c`. -/
noncomputable def twfePeriodEffect (a b c : ℝ) : Fin 3 → ℝ :=
  let m := (a + b + c - 3 * twfeCoef a b c) / 6
  ![-m, (a - twfeCoef a b c) / 2 - m, (b + c - 2 * twfeCoef a b c) / 2 - m]

/-- **The closed form solves the two-way fixed effects normal equations.** For all effects
`a, b, c`, the coefficient `twfeCoef a b c`, with the explicit cohort and period effects, makes
the residual orthogonal to all regressors. -/
theorem normalEquations_twfeCoef (a b c : ℝ) :
    NormalEquations (outcome a b c) (twfeCohortEffect a b c) (twfePeriodEffect a b c)
      (twfeCoef a b c) := by
  refine ⟨fun i => ?_, fun t => ?_, ?_⟩
  · fin_cases i <;>
      simp [resid, twfeCohortEffect, twfePeriodEffect, twfeCoef, outcome, treat, adoption,
        effect, Fin.sum_univ_succ] <;> ring
  · fin_cases t <;>
      simp [resid, twfeCohortEffect, twfePeriodEffect, twfeCoef, outcome, treat, adoption,
        effect, Fin.sum_univ_succ] <;> ring
  · simp [resid, twfeCohortEffect, twfePeriodEffect, twfeCoef, outcome, treat, adoption,
      effect, Fin.sum_univ_succ]
    ring

/-- **Uniqueness of the treatment coefficient.** Any solution of the normal equations has
treatment coefficient `twfeCoef a b c`; so `twfeCoef` is the population two-way fixed effects
coefficient, whatever cohort and period effects accompany it. -/
theorem eq_twfeCoef_of_normalEquations {a b c : ℝ} {α : Fin 2 → ℝ} {δ : Fin 3 → ℝ} {β : ℝ}
    (h : NormalEquations (outcome a b c) α δ β) : β = twfeCoef a b c := by
  obtain ⟨hrow, hcol, hD⟩ := h
  have r0 := hrow 0
  have r1 := hrow 1
  have c0 := hcol 0
  have c1 := hcol 1
  have c2 := hcol 2
  simp [resid, outcome, treat, adoption, effect, Fin.sum_univ_succ] at r0 r1 c0 c1 c2 hD
  rw [twfeCoef]
  linarith

/-- The implicit weights of the two-way fixed effects coefficient on the group-time effects
`(ATT(early, 1), ATT(early, 2), ATT(late, 2))`. -/
noncomputable def twfeWeight : Fin 3 → ℝ := ![1, -1 / 2, 1 / 2]

/-- **Weight decomposition.** The two-way fixed effects coefficient is the linear combination
`1 * ATT(early, 1) - 1/2 * ATT(early, 2) + 1/2 * ATT(late, 2)` of the group-time effects. -/
theorem twfeCoef_eq_sum_twfeWeight (a b c : ℝ) :
    twfeCoef a b c = ∑ k, twfeWeight k * ![a, b, c] k := by
  simp [twfeCoef, twfeWeight, Fin.sum_univ_succ]
  ring

/-- The weights sum to one. -/
theorem sum_twfeWeight : ∑ k, twfeWeight k = 1 := by
  simp [twfeWeight, Fin.sum_univ_succ]
  norm_num

/-- **A negative weight.** The weight on `ATT(early, 2)`, the effect of the early cohort in the
period where the late cohort, used as its comparison, is itself treated, is `-1/2 < 0`. So the
two-way fixed effects coefficient is not a convex combination of the group-time effects. -/
theorem twfeWeight_one_neg : twfeWeight 1 < 0 := by
  norm_num [twfeWeight]

/-- **Wrong sign.** With `ATT(early, 1) = 1`, `ATT(early, 2) = 4`, and `ATT(late, 2) = 1`, every
group-time effect is positive while the two-way fixed effects coefficient is `-1/2`. -/
theorem twfeCoef_wrong_sign :
    (0 < (1 : ℝ) ∧ 0 < (4 : ℝ) ∧ 0 < (1 : ℝ)) ∧ twfeCoef 1 4 1 = -1 / 2 := by
  refine ⟨by norm_num, ?_⟩
  simp [twfeCoef]
  norm_num

/-- **Not a convex combination.** In the example with effects `1, 4, 1`, the two-way fixed
effects coefficient, which is the unique treatment coefficient solving the normal equations,
lies outside the convex hull of the group-time effects. -/
theorem twfeCoef_not_mem_convexHull :
    NormalEquations (outcome 1 4 1) (twfeCohortEffect 1 4 1) (twfePeriodEffect 1 4 1)
        (twfeCoef 1 4 1) ∧
      twfeCoef 1 4 1 ∉ convexHull ℝ (Set.range ![(1 : ℝ), 4, 1]) := by
  refine ⟨normalEquations_twfeCoef 1 4 1, fun h => ?_⟩
  have hsub : convexHull ℝ (Set.range ![(1 : ℝ), 4, 1]) ⊆ Set.Ioi 0 := by
    refine convexHull_min ?_ (convex_Ioi 0)
    rintro _ ⟨k, rfl⟩
    fin_cases k <;> simp
  have := hsub h
  rw [twfeCoef_wrong_sign.2] at this
  norm_num at this

/-! ### The example as a staggered adoption model

The population consists of two equally likely units, one per cohort; within the example all
units of a cohort are identical, so cohort fixed effects coincide with unit fixed effects. -/

section Model

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

/-- The uniform probability measure on the two units. -/
noncomputable def exMeasure : Measure (Fin 2) := uniformOn Set.univ

instance : IsProbabilityMeasure exMeasure := by
  unfold exMeasure
  infer_instance

/-- The cohort (first treated period) of each unit. -/
def exCohort (i : Fin 2) : WithTop ℕ := adoption i

/-- The treatment effect of unit `i` in period `t`, extended by `0` beyond period `2`. -/
def effectNat (a b c : ℝ) (i : Fin 2) (t : ℕ) : ℝ :=
  if h : t < 3 then effect a b c i ⟨t, h⟩ else 0

/-- Potential outcomes: under its own adoption date a unit's outcome is its treatment effect
from adoption on, and every other potential outcome, in particular the never-treated one, is
`0`. -/
noncomputable def exY (a b c : ℝ) (t : ℕ) (g : WithTop ℕ) (i : Fin 2) : ℝ :=
  if g = exCohort i ∧ adoption i ≤ t then effectNat a b c i t else 0

/-- Observed outcomes, defined by consistency. -/
noncomputable def exYobs (a b c : ℝ) (t : ℕ) (i : Fin 2) : ℝ := exY a b c t (exCohort i) i

theorem ex_consistency (a b c : ℝ) : Staggered.Consistency exCohort (exY a b c) (exYobs a b c) :=
  fun _ _ => rfl

theorem ex_noAnticipation (a b c : ℝ) :
    Staggered.NoAnticipation exMeasure exCohort (exY a b c) := by
  refine ae_of_all _ fun i t ht => ?_
  have hlt : t < adoption i := by unfold exCohort at ht; exact_mod_cast ht
  have hne : (⊤ : WithTop ℕ) ≠ exCohort i := (WithTop.coe_ne_top).symm
  simp [exY, Nat.not_le.mpr hlt, hne]

/-- Never-treated potential outcomes are identically `0`. -/
theorem ex_untreated (a b c : ℝ) (t : ℕ) (i : Fin 2) : exY a b c t ⊤ i = 0 := by
  simp [exY, exCohort]

/-- Hence parallel trends against the never-treated potential outcomes holds for every cohort,
comparison event, and period. -/
theorem ex_parallel_trends (a b c : ℝ) (s c' : Set (Fin 2)) (r : ℕ) :
    ∫ ω, (exY a b c (r + 1) ⊤ ω - exY a b c r ⊤ ω) ∂exMeasure[|s]
      = ∫ ω, (exY a b c (r + 1) ⊤ ω - exY a b c r ⊤ ω) ∂exMeasure[|c'] := by
  simp [ex_untreated]

theorem ex_cohort_one : Staggered.cohort exCohort 1 = {0} := by
  ext i
  fin_cases i <;> simp [Staggered.cohort, exCohort, adoption]

theorem ex_cohort_two : Staggered.cohort exCohort 2 = {1} := by
  ext i
  fin_cases i <;> simp [Staggered.cohort, exCohort, adoption]

theorem ex_measure_ne_zero (i : Fin 2) : exMeasure {i} ≠ 0 := by
  rw [exMeasure, Ne, uniformOn_eq_zero_iff Set.finite_univ]
  simp

/-- The group-time effects of the model, in the sense of `Staggered.att`, are
`ATT(1, 1) = a`, `ATT(1, 2) = b`, and `ATT(2, 2) = c`. -/
theorem ex_att (a b c : ℝ) :
    Staggered.att exMeasure exCohort (exY a b c) 1 1 = a ∧
      Staggered.att exMeasure exCohort (exY a b c) 1 2 = b ∧
      Staggered.att exMeasure exCohort (exY a b c) 2 2 = c := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [Staggered.att, Nat.cast_one, Nat.cast_ofNat, ex_cohort_one, ex_cohort_two]
    refine DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (ex_measure_ne_zero _) ?_
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    simp [exY, exCohort, adoption, effectNat, effect]

/-- The observed cohort-time means of the model are the cells `outcome a b c` used in the two-way
fixed effects regression above. -/
theorem ex_cell_mean (a b c : ℝ) (i : Fin 2) (t : Fin 3) :
    ∫ ω, exYobs a b c t ω ∂exMeasure[|Staggered.cohort exCohort (adoption i)]
      = outcome a b c i t := by
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [show ((adoption 0 : ℕ) : WithTop ℕ) = ((1 : ℕ) : WithTop ℕ) from rfl, Nat.cast_one,
      ex_cohort_one]
    refine DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (ex_measure_ne_zero _) ?_
    intro j hj
    rw [Set.mem_singleton_iff] at hj
    subst hj
    fin_cases t <;> simp [exYobs, exY, exCohort, adoption, effectNat, effect, outcome, treat]
  · simp only [Fin.mk_one, Fin.isValue]
    rw [show ((adoption 1 : ℕ) : WithTop ℕ) = ((2 : ℕ) : WithTop ℕ) from rfl, Nat.cast_ofNat,
      ex_cohort_two]
    refine DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (ex_measure_ne_zero _) ?_
    intro j hj
    rw [Set.mem_singleton_iff] at hj
    subst hj
    fin_cases t <;> simp [exYobs, exY, exCohort, adoption, effectNat, effect, outcome, treat]

/-- **Two-way fixed effects is not a convex combination of group-time effects.** In the
staggered adoption model with `ATT(1, 1) = 1`, `ATT(1, 2) = 4`, `ATT(2, 2) = 1` (consistency and
no anticipation hold, and untreated outcomes are `0`, so parallel trends holds exactly by
`ex_parallel_trends`), the static
two-way fixed effects coefficient of the observed cohort-time means is `-1/2`: it is the unique
solution of the normal equations, has the wrong sign, and lies outside the convex hull of the
group-time effects. -/
theorem twfe_not_convex_combination :
    Staggered.Consistency exCohort (exY 1 4 1) (exYobs 1 4 1) ∧
    Staggered.NoAnticipation exMeasure exCohort (exY 1 4 1) ∧
    (∀ (i : Fin 2) (t : Fin 3), ∫ ω, exYobs 1 4 1 t ω
        ∂exMeasure[|Staggered.cohort exCohort (adoption i)] = outcome 1 4 1 i t) ∧
    (∀ (α : Fin 2 → ℝ) (δ : Fin 3 → ℝ) (β : ℝ),
        NormalEquations (outcome 1 4 1) α δ β → β = -1 / 2) ∧
    NormalEquations (outcome 1 4 1) (twfeCohortEffect 1 4 1) (twfePeriodEffect 1 4 1) (-1 / 2) ∧
    0 < Staggered.att exMeasure exCohort (exY 1 4 1) 1 1 ∧
    0 < Staggered.att exMeasure exCohort (exY 1 4 1) 1 2 ∧
    0 < Staggered.att exMeasure exCohort (exY 1 4 1) 2 2 ∧
    (-1 / 2 : ℝ) ∉ convexHull ℝ {Staggered.att exMeasure exCohort (exY 1 4 1) 1 1,
      Staggered.att exMeasure exCohort (exY 1 4 1) 1 2,
      Staggered.att exMeasure exCohort (exY 1 4 1) 2 2} := by
  obtain ⟨h11, h12, h22⟩ := ex_att 1 4 1
  have hβ : twfeCoef 1 4 1 = -1 / 2 := twfeCoef_wrong_sign.2
  refine ⟨ex_consistency 1 4 1, ex_noAnticipation 1 4 1, ex_cell_mean 1 4 1,
    fun α δ β h => (eq_twfeCoef_of_normalEquations h).trans hβ,
    hβ ▸ normalEquations_twfeCoef 1 4 1, by rw [h11]; norm_num, by rw [h12]; norm_num,
    by rw [h22]; norm_num, ?_⟩
  rw [h11, h12, h22]
  intro h
  have hsub : convexHull ℝ ({1, 4, 1} : Set ℝ) ⊆ Set.Ioi 0 := by
    refine convexHull_min ?_ (convex_Ioi 0)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num
  have := hsub h
  norm_num at this

end Model

end EventStudy

end CausalInference
