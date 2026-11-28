/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.Feasibility
public import CausalInference.PopulationAdjustment.EffectiveSampleSize
public import CausalInference.PopulationAdjustment.WeightedContrast

/-!
# Population adjustment: a worked example of entropy balancing

Three trial units with one centered covariate `Δ = (-1, 1, 1)` (covariates `(0, 2, 2)` and
target mean `1`). The dual parameter `β = -(log 2) / 2` balances the covariate: with
`a = exp(β)`, `a² = 1/2`, the exponential weights are `(1/a, a, a)` and
`-1/a + a + a = (2a² - 1)/a = 0`. Hence `β` minimizes the log partition function, it is the
dual minimizer (the centered covariates span `ℝ¹`), and the entropy balancing weights are
`(1/2, 1/4, 1/4)`, with effective sample size `1 / (1/4 + 1/16 + 1/16) = 8/3` and variance
inflation `3 / (8/3) = 9/8`.

A second example checks the agreement with the outcome model under a linear model: four units,
two in each arm, with covariates `(0, 2)` in each arm, unit weights (which balance both arms at
`x̄ = 1`), and outcomes from the anchored model with `α = 0`, `β₁ = 1`, `γ_true = 1`,
`β₂,true = 1`, `γ_false = 0`, `β₂,false = 0`. The weighted contrast of `false` relative to `true`
is `η_false(1) - η_true(1) = 1 - 3 = -2`.

## Main results

* `threeUnitDelta_span`, `isMinOn_logPartition_threeUnitDelta`, `dualMinimizer_threeUnitDelta`.
* `balancingWeights_threeUnitDelta`, `ess_balancingWeights_threeUnitDelta`.
* `weightedContrast_fourUnit`: an instance of `weightedContrast_eq_predictor_sub`.
-/

@[expose] public section

namespace CausalInference

namespace PopulationAdjustment

open Finset

/-- The centered covariates `(-1, 1, 1)` of the example. -/
def threeUnitDelta : Fin 3 → Fin 1 → ℝ := ![fun _ => -1, fun _ => 1, fun _ => 1]

/-- The dual parameter `-(log 2) / 2` of the example. -/
noncomputable def threeUnitBeta : Fin 1 → ℝ := fun _ => -(Real.log 2) / 2

theorem threeUnitDelta_span : Submodule.span ℝ (Set.range threeUnitDelta) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun v => ?_
  have hv : v = v 0 • threeUnitDelta 1 := by
    funext j
    fin_cases j
    simp [threeUnitDelta]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)

private theorem exp_threeUnitBeta_sq : Real.exp (-(Real.log 2) / 2) ^ 2 = 1 / 2 := by
  rw [← Real.exp_nat_mul]
  push_cast
  rw [show (2 : ℝ) * (-Real.log 2 / 2) = -Real.log 2 by ring, Real.exp_neg,
    Real.exp_log (by norm_num)]
  norm_num

private theorem exp_dot_threeUnitDelta (i : Fin 3) :
    Real.exp (threeUnitBeta ⬝ᵥ threeUnitDelta i) =
      ![(Real.exp (-(Real.log 2) / 2))⁻¹, Real.exp (-(Real.log 2) / 2),
        Real.exp (-(Real.log 2) / 2)] i := by
  fin_cases i <;> simp [threeUnitBeta, threeUnitDelta, dotProduct, Real.exp_neg]

/-- `β = -(log 2) / 2` minimizes the log partition function of the example. -/
theorem isMinOn_logPartition_threeUnitDelta :
    IsMinOn (logPartition threeUnitDelta) Set.univ threeUnitBeta := by
  rw [isMinOn_logPartition_iff, momentBalanced_zero_iff]
  have ha2 : Real.exp (-(Real.log 2 / 2)) ^ 2 = 1 / 2 := by
    rw [← neg_div]; exact exp_threeUnitBeta_sq
  funext j
  fin_cases j
  simp only [Fin.sum_univ_three, exp_dot_threeUnitDelta]
  simp [threeUnitDelta]
  field_simp
  linarith

/-- **The dual minimizer of the example is `-(log 2) / 2`.** -/
theorem dualMinimizer_threeUnitDelta : dualMinimizer threeUnitDelta = threeUnitBeta :=
  (eq_dualMinimizer_of_span threeUnitDelta_span isMinOn_logPartition_threeUnitDelta).symm

/-- **The entropy balancing weights of the example are `(1/2, 1/4, 1/4)`**, and they balance the
centered covariates. -/
theorem balancingWeights_threeUnitDelta :
    balancingWeights threeUnitDelta = ![1 / 2, 1 / 4, 1 / 4] ∧
      balancingWeights threeUnitDelta ∈ balancingSet threeUnitDelta := by
  have hmin := isMinOn_logPartition_threeUnitDelta
  have hmem := (entropyWeights_mem_balancingSet_iff threeUnitBeta).2
    ((isMinOn_logPartition_iff _).1 hmin)
  rw [balancingWeights, dualMinimizer_threeUnitDelta]
  refine ⟨?_, hmem⟩
  have ha2 : Real.exp (-(Real.log 2 / 2)) ^ 2 = 1 / 2 := by
    rw [← neg_div]; exact exp_threeUnitBeta_sq
  funext i
  simp only [entropyWeights, partitionFunction, Fin.sum_univ_three, exp_dot_threeUnitDelta]
  fin_cases i <;> simp <;> field_simp <;> linarith

/-- **Effective sample size and variance inflation of the example**: `ESS = 8/3` and
`n / ESS = 9/8`. -/
theorem ess_balancingWeights_threeUnitDelta :
    ess (balancingWeights threeUnitDelta) = 8 / 3 ∧
      (Fintype.card (Fin 3) : ℝ) / ess (balancingWeights threeUnitDelta) = 9 / 8 := by
  have h : ess (balancingWeights threeUnitDelta) = 8 / 3 := by
    rw [balancingWeights_threeUnitDelta.1, ess]
    simp [Fin.sum_univ_three]
    norm_num
  refine ⟨h, ?_⟩
  rw [h]
  simp
  norm_num

/-- The arms of the four unit example. -/
def fourUnitArm : Fin 4 → Bool := ![true, true, false, false]

/-- The covariates of the four unit example. -/
def fourUnitZ : Fin 4 → Fin 1 → ℝ := ![fun _ => 0, fun _ => 2, fun _ => 0, fun _ => 2]

/-- The anchored model of the four unit example. -/
def fourUnitModel : IndirectComparison.AnchoredModel Bool 1 :=
  ⟨0, fun _ => 1, fun t => if t then 1 else 0, fun t _ => if t then 1 else 0⟩

/-- The outcomes of the four unit example, from the linear predictor without residuals. -/
def fourUnitY (i : Fin 4) : ℝ := fourUnitModel.predictor (fourUnitArm i) (fourUnitZ i)

private theorem fourUnit_balanced (t : Bool) :
    MomentBalanced (armWeights (fun _ => 1) fourUnitArm t) fourUnitZ (fun _ => 1) ∧
      ∑ i, armWeights (fun _ => (1 : ℝ)) fourUnitArm t i ≠ 0 := by
  constructor
  · funext j
    cases t <;> simp [armWeights, fourUnitArm, fourUnitZ, Fin.sum_univ_four] <;>
      norm_num
  · cases t <;> simp [armWeights, fourUnitArm, Fin.sum_univ_four]

/-- **An instance of `weightedContrast_eq_predictor_sub`**: in the four unit example the
weighted contrast of `false` relative to `true` is the outcome model contrast
`η_false(1) - η_true(1) = -2`. -/
theorem weightedContrast_fourUnit :
    weightedContrast id (fun _ => 1) fourUnitArm fourUnitY true false = -2 := by
  obtain ⟨-, -, h⟩ := weightedContrast_eq_predictor_sub fourUnitModel (y := fourUnitY)
    (e := fun _ => 0) (xbar := fun _ => 1) true false (fun i => (add_zero _).symm)
    (fourUnit_balanced true).1 (fourUnit_balanced true).2 (fourUnit_balanced false).1
    (fourUnit_balanced false).2
  rw [h fun _ => rfl]
  simp [fourUnitModel, IndirectComparison.AnchoredModel.predictor,
    IndirectComparison.anchoredPredictor]
  norm_num

end PopulationAdjustment

end CausalInference
