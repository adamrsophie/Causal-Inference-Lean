/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Weighting

/-!
# Treatment-confounder feedback: the g-formula is right, regression adjustment is wrong

A concrete finite model with two time points and causal structure `A0 → L1 ← U → Y`,
`L1 → A1`: the time-varying covariate `L1` is affected by the first treatment `A0` and by an
unmeasured cause `U` of the outcome, and it affects the second treatment `A1`. The outcome is
`Y = 1{U}`: neither treatment nor `L1` affects it. Sequential exchangeability and sequential
positivity hold, so the g-formula and inverse probability weighting recover the true mean of
every potential outcome; but the naive contrast that adjusts for `L1` by stratification and the
unadjusted contrast both give a nonzero effect, while the true effect is zero.

The two biases have different sources. `L1` is a collider on the path `A0 → L1 ← U → Y`, so
stratifying on `L1` opens that path: within a stratum of `L1` the first treatment is associated
with `U`, hence with `Y`. Not stratifying on `L1` leaves the second treatment confounded along
`A1 ← L1 ← U → Y`.

This is the phenomenon that motivated Robins (1986): when a covariate is both a confounder for
later treatment and affected by earlier treatment, conditioning on it is biased, and so is not
conditioning on it.

## The model

The sample space is `Bool × Bool × Bool × Bool`, a point being `(u, a0, n1, n2)`:
* `u` is an unmeasured cause of the outcome, `P(u) = 1/2`;
* `a0 = A0` is the first treatment, randomized, `P(A0) = 1/2`;
* `n1` is noise with `P(n1) = 1/2`, and `L1 = u` if `A0 = false`, `L1 = u || n1` if `A0 = true`;
* `n2` is noise with `P(n2) = 3/4`, and `A1 = n2` if `L1 = true`, `A1 = !n2` if `L1 = false`, so
  `P(A1 = true | L1 = true) = 3/4` and `P(A1 = true | L1 = false) = 1/4`;
* the outcome is `Y = 1{u}`, unaffected by treatment: `Y(a0, a1) = Y` for every regime.

The baseline covariate `L0` is constant. The potential covariate is
`L1(a0) = if a0 then u || n1 else u`.

## Main results

* `FeedbackExample.seqExchangeable`, `FeedbackExample.seqPositive`: the assumptions of the
  g-formula theorem hold for every static regime.
* `FeedbackExample.gFormula_eq`: the g-formula equals `1/2 = E[Y(a0, a1)]` for every regime
  (obtained from `gFormula2_static`, and `E[Y(a0, a1)] = 1/2` by direct computation); likewise
  inverse probability weighting (`FeedbackExample.ipw_eq`).
* `FeedbackExample.gFormula_eq_direct`: the same value `1/2` evaluated directly from the
  observational cells, without the identification theorem. The term `L1 = false` vanishes,
  since `L1 = false` forces `U = false` and the cell mean of `Y` is `0`; the term `L1 = true` is
  `1 · 1/2` for `a0 = false` and `2/3 · 3/4` for `a0 = true`, for either `a1`.
* `FeedbackExample.model_seqExchangeable`, `FeedbackExample.model_seqPositive` in
  `CausalInference.Longitudinal.GNull`: the example as a `Model` with two time points satisfies
  `Model.SeqExchangeable` and `Model.SeqPositive` for every static regime.
* `FeedbackExample.feedback`: `L1(true) ≠ L1(false)` at some sample point.
* `FeedbackExample.naiveAdjusted_eq`: the contrast
  `Σ_l P(L1 = l) (E[Y | A0 = 1, A1 = 1, L1 = l] - E[Y | A0 = 0, A1 = 0, L1 = l])` is `-5/24`.
* `FeedbackExample.unadjusted_eq`: `E[Y | A0 = 1, A1 = 1] - E[Y | A0 = 0, A1 = 0] = 7/20`.
* `FeedbackExample.adjustment_fails`: the true effect and the g-formula contrast are `0`, the
  two naive contrasts are not.

Every event on which these contrasts condition has positive probability
(`FeedbackExample.naive_events_pos`).

## References

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), chapter 20.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

namespace FeedbackExample

open Finset

/-- The sample space: a point is `(u, a0, n1, n2)`. -/
abbrev Ω := Bool × Bool × Bool × Bool

/-- The mass function: `u`, `a0`, `n1` fair and independent, `n2` independent with
`P(n2 = true) = 3/4`. -/
noncomputable def mass (ω : Ω) : ℝ := if ω.2.2.2 then 3 / 32 else 1 / 32

/-- The distribution of the sample point. -/
noncomputable def p : FiniteDist Ω where
  mass := mass
  nonneg ω := by unfold mass; split_ifs <;> norm_num
  sum_eq_one := by simp [mass, Fintype.sum_prod_type]; norm_num

/-- The baseline covariate, constant. -/
def L0 (_ : Ω) : Bool := false

/-- The first treatment. -/
def A0 (ω : Ω) : Bool := ω.2.1

/-- The potential covariate at time `1` under the first treatment `a0`. -/
def L1po (a0 : Bool) (ω : Ω) : Bool := if a0 then ω.1 || ω.2.2.1 else ω.1

/-- The observed covariate at time `1`: the potential covariate under the observed `A0`. -/
def L1 (ω : Ω) : Bool := L1po (A0 ω) ω

/-- The second treatment, depending on `L1` and the noise `n2`. -/
def A1 (ω : Ω) : Bool := if L1 ω then ω.2.2.2 else !ω.2.2.2

/-- The outcome, the indicator of the unmeasured `u`. -/
noncomputable def Y (ω : Ω) : ℝ := if ω.1 then 1 else 0

/-- The potential outcomes: treatment has no effect. -/
noncomputable def Ypo (_ _ : Bool) : Ω → ℝ := Y

/-- Covariate consistency at time `1`. -/
theorem covariate_consistent (ω : Ω) (a0 : Bool) (h : A0 ω = a0) : L1 ω = L1po a0 ω := by
  rw [L1, h]

/-- Treatment-confounder feedback: the first treatment changes the covariate at time `1`. -/
theorem feedback : L1po true (false, false, true, false) ≠ L1po false (false, false, true, false) :=
  by decide

/-- Sequential exchangeability holds for every static regime. -/
theorem seqExchangeable (a0 a1 : Bool) :
    SeqExchangeable2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) (Ypo a0 a1) := by
  refine ⟨fun l0 => ?_, fun l0 l1 => ?_⟩ <;>
  simp only [MeanIndepOn, wsum, wmass, ev, filter_inter, inter_filter, univ_inter, filter_filter,
    sum_filter, Fintype.sum_prod_type, Fintype.sum_bool] <;>
  cases a0 <;> cases a1 <;> cases l0 <;> (try cases l1) <;>
  norm_num [p, mass, A0, A1, L0, L1, L1po, Ypo, Y]

/-- Sequential positivity holds for every static regime. -/
theorem seqPositive (a0 a1 : Bool) :
    SeqPositive2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) := by
  refine ⟨fun l0 h => ?_, fun l0 l1 h => ?_⟩ <;>
  simp only [wmass, ev, filter_inter, inter_filter, univ_inter, filter_filter,
    sum_filter, Fintype.sum_prod_type, Fintype.sum_bool] at h ⊢ <;>
  cases a0 <;> cases a1 <;> cases l0 <;> (try cases l1) <;>
  norm_num [p, mass, A0, A1, L0, L1, L1po] at h <;>
  norm_num [p, mass, A0, A1, L0, L1, L1po]

/-- The true mean of every potential outcome is `1/2`. -/
theorem expect_Ypo (a0 a1 : Bool) : p.expect (Ypo a0 a1) = 1 / 2 := by
  simp only [FiniteDist.expect, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [p, mass, Ypo, Y]

/-- The g-formula recovers the true mean `1/2` for every static regime. -/
theorem gFormula_eq (a0 a1 : Bool) :
    gFormula2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) Y = 1 / 2 := by
  rw [← expect_Ypo a0 a1]
  exact (gFormula2_static p (fun _ _ _ => rfl) (seqExchangeable a0 a1) (seqPositive a0 a1)).symm

/-- **Direct evaluation of the g-formula from the observational cells.** For every static regime
the two time point g-formula, computed from the observed distribution alone, is `1/2`. In each
sum the term `L0 = true` has weight `P(L0 = true) = 0`, the term `L1 = false` has cell mean
`E[Y | …, L1 = false, …] = 0`, and the term `L1 = true` is `1 · 1/2` for `a0 = false` and
`2/3 · 3/4` for `a0 = true`. -/
theorem gFormula_eq_direct (a0 a1 : Bool) :
    gFormula2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) Y = 1 / 2 := by
  simp only [gFormula2, condMean, condProb, wsum, wmass, ev, filter_inter, inter_filter,
    univ_inter, filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a0 <;> cases a1 <;> norm_num [p, mass, A0, A1, L0, L1, L1po, Y]

/-- Inverse probability of treatment weighting recovers the true mean `1/2`. -/
theorem ipw_eq (a0 a1 : Bool) : ipw2 p L0 A0 L1 A1 a0 a1 Y = 1 / 2 := by
  rw [← expect_Ypo a0 a1]
  exact (ipw2_static p (fun _ _ _ => rfl) (seqExchangeable a0 a1) (seqPositive a0 a1)).symm

/-- The naive contrast adjusting for `L1` by stratification and standardization over the
marginal of `L1`:
`Σ_l P(L1 = l) (E[Y | A0 = 1, A1 = 1, L1 = l] - E[Y | A0 = 0, A1 = 0, L1 = l])`. -/
noncomputable def naiveAdjusted : ℝ :=
  ∑ l, wmass p (ev L1 l) *
    (condMean p (ev A0 true ∩ ev A1 true ∩ ev L1 l) Y -
      condMean p (ev A0 false ∩ ev A1 false ∩ ev L1 l) Y)

/-- The unadjusted contrast `E[Y | A0 = 1, A1 = 1] - E[Y | A0 = 0, A1 = 0]`. -/
noncomputable def unadjusted : ℝ :=
  condMean p (ev A0 true ∩ ev A1 true) Y - condMean p (ev A0 false ∩ ev A1 false) Y

/-- Every event on which the naive contrasts condition has positive probability. -/
theorem naive_events_pos (a l : Bool) :
    0 < wmass p (ev A0 a ∩ ev A1 a ∩ ev L1 l) ∧ 0 < wmass p (ev A0 a ∩ ev A1 a) := by
  constructor <;>
  simp only [wmass, ev, filter_inter, inter_filter, univ_inter, filter_filter,
    sum_filter, Fintype.sum_prod_type, Fintype.sum_bool] <;>
  cases a <;> cases l <;>
  norm_num [p, mass, A0, A1, L1, L1po]

/-- The naive adjusted contrast is `-5/24`. -/
theorem naiveAdjusted_eq : naiveAdjusted = -5 / 24 := by
  simp only [naiveAdjusted, condMean, wsum, wmass, ev, filter_inter, inter_filter, univ_inter,
    filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [p, mass, A0, A1, L1, L1po, Y]

/-- The unadjusted contrast is `7/20`. -/
theorem unadjusted_eq : unadjusted = 7 / 20 := by
  simp only [unadjusted, condMean, wsum, wmass, ev, filter_inter, inter_filter, univ_inter,
    filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [p, mass, A0, A1, L1, L1po, Y]

/-- **Regression adjustment fails under treatment-confounder feedback.** In this model the true
effect `E[Y(1, 1)] - E[Y(0, 0)]` is `0` and the g-formula contrast is `0`, while the naive
contrast adjusting for `L1` and the unadjusted contrast are both nonzero. -/
theorem adjustment_fails :
    p.expect (Ypo true true) - p.expect (Ypo false false) = 0 ∧
      gFormula2 p L0 A0 L1 A1 (fun _ => true) (fun _ _ => true) Y -
        gFormula2 p L0 A0 L1 A1 (fun _ => false) (fun _ _ => false) Y = 0 ∧
      naiveAdjusted ≠ 0 ∧ unadjusted ≠ 0 := by
  refine ⟨by rw [expect_Ypo, expect_Ypo]; ring, by rw [gFormula_eq, gFormula_eq]; ring,
    by rw [naiveAdjusted_eq]; norm_num, by rw [unadjusted_eq]; norm_num⟩

end FeedbackExample

end Longitudinal

end CausalInference
