/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Interference.TwoStage
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

/-!
# A two-unit counterexample under interference

Two units, each of which responds only if both units are treated:
`Y a i = 1` if `a 0 = a 1 = true` and `Y a i = 0` otherwise.

* `twoUnitY_not_noInterference`: no interference fails.
* `twoUnitY_unit_effect_ill_defined`: the unit level effect of treatment on unit `0` is not
  well defined; switching unit `0` from control to treatment changes its outcome by `0` when
  unit `1` is a control and by `1` when unit `1` is treated.
* `twoUnitY_diffInMeans_biased`: under complete randomization of one of the two units, the
  classical difference in means (mean outcome of the treated minus mean outcome of the
  controls) is identically zero, so its expectation is `0`, while the average effect of
  treating everybody versus treating nobody, `2⁻¹ ∑_i (Y(1, 1) i - Y(0, 0) i)`, equals `1`.

The difference in means is therefore biased for the all versus none contrast
(`twoUnitY_diffInMeans_ne`). It is not biased for the Hudgens and Halloran direct effect:
`expect_diffInMeans_completeRandomization` shows that under complete randomization with
`0 < k < n` its expectation is `ȳ(1; ψ) - ȳ(0; ψ)`, the negative of the direct effect in the
sign convention used here, for arbitrary potential outcomes.

Source: the phenomenon is discussed in M. G. Hudgens and M. E. Halloran (2008), Toward causal
inference with interference; the specific example is elementary.
-/

@[expose] public section

open Finset

namespace CausalInference

namespace Interference

/-- Potential outcomes of two units that respond only when both are treated. -/
def twoUnitY (a : Fin 2 → Bool) (_i : Fin 2) : ℝ :=
  if a 0 = true ∧ a 1 = true then 1 else 0

/-- The two-unit outcomes violate no interference. -/
theorem twoUnitY_not_noInterference : ¬ NoInterference twoUnitY := by
  intro h
  have := h ![true, true] ![true, false] 0 rfl
  norm_num [twoUnitY] at this

/-- The effect on unit `0` of switching it from control to treatment depends on the treatment
of unit `1`: it is `0` when unit `1` is a control and `1` when unit `1` is treated. -/
theorem twoUnitY_unit_effect_ill_defined :
    twoUnitY ![true, false] 0 - twoUnitY ![false, false] 0 = 0 ∧
      twoUnitY ![true, true] 0 - twoUnitY ![false, true] 0 = 1 := by
  norm_num [twoUnitY]

/-- The classical difference in means: mean outcome of the treated units minus mean outcome of
the control units. -/
noncomputable def diffInMeans {ι : Type*} [Fintype ι] (Y : (ι → Bool) → ι → ℝ)
    (a : ι → Bool) : ℝ :=
  groupEstimator Y true a - groupEstimator Y false a

/-- Under complete randomization of `k` among `n` units with `0 < k < n`, the expected
difference in means is `ȳ(1; ψ) - ȳ(0; ψ)`, the negative of the Hudgens and Halloran direct
effect `DE(ψ) = ȳ(0; ψ) - ȳ(1; ψ)`, for arbitrary potential outcomes `Y` (interference
allowed). -/
theorem expect_diffInMeans_completeRandomization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : (ι → Bool) → ι → ℝ) {k : ℕ} (hk0 : 0 < k) (hk : k < Fintype.card ι) :
    expect (completeRandomization ι k hk.le) (diffInMeans Y) =
      -directEffect (fun t s ↦ groupAvg Y s t) (completeRandomization ι k hk.le) := by
  rw [show diffInMeans Y = fun a ↦ groupEstimator Y true a - groupEstimator Y false a from rfl,
    expect_sub, expect_groupEstimator_completeRandomization_true Y hk0 hk.le,
    expect_groupEstimator_completeRandomization_false Y hk, directEffect, neg_sub]

/-- Under complete randomization of one of the two units the expected difference in means is
`0`, while the average effect of treating both units versus treating neither is `1`; the
difference in means is biased for that effect. -/
theorem twoUnitY_diffInMeans_biased :
    expect (completeRandomization (Fin 2) 1 (by simp)) (diffInMeans twoUnitY) = 0 ∧
      (Fintype.card (Fin 2) : ℝ)⁻¹ * ∑ i, (y1 twoUnitY i - y0 twoUnitY i) = 1 := by
  constructor
  · refine sum_eq_zero fun a _ ↦ ?_
    by_cases ha : (completeRandomization (Fin 2) 1 (by simp)).prob a = 0
    · rw [ha, zero_mul]
    have h1 := completeRandomization_supp (by simp) a ha
    have hY : ∀ i, twoUnitY a i = 0 := by
      intro i
      have hnot : ¬ (a 0 = true ∧ a 1 = true) := by
        rintro ⟨h0, h1'⟩
        have : (univ.filter fun j : Fin 2 ↦ a j = true) = univ := by
          rw [eq_univ_iff_forall, Fin.forall_fin_two]
          simp [h0, h1']
        rw [numWith, this] at h1
        simp at h1
      simp [twoUnitY, hnot]
    simp only [diffInMeans, groupEstimator, hY, sum_const_zero, zero_div, sub_self, mul_zero]
  · norm_num [y1, y0, unitOutcome, twoUnitY, Fin.sum_univ_two]

/-- The bias itself: under complete randomization of one of the two units, the expected
difference in means differs from the average effect of treating both units versus neither. -/
theorem twoUnitY_diffInMeans_ne :
    expect (completeRandomization (Fin 2) 1 (by simp)) (diffInMeans twoUnitY) ≠
      (Fintype.card (Fin 2) : ℝ)⁻¹ * ∑ i, (y1 twoUnitY i - y0 twoUnitY i) := by
  rw [twoUnitY_diffInMeans_biased.1, twoUnitY_diffInMeans_biased.2]
  norm_num

end Interference

end CausalInference
