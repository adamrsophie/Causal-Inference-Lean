/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.PathCoefficients
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Star.Real

/-!
# Counterexamples for linear SEMs: the bow

The bow is the model `X → Y` together with a bidirected arc `X ↔ Y`: `Y = β X + ε_Y` with
`Cov(ε_X, ε_Y) = ω`. It is the simplest model in which the regression coefficient is not the
structural coefficient, and in which the structural coefficient is not identified.

## Main results

* `Bow.slope_eq`, `Bow.slope_ne`, `Bow.regression_ne`: the slope of `Y` on `X` is
  `β + ω / ω_X`, which differs from `β` whenever `ω ≠ 0`; so regressing on the parents does not
  return the structural coefficient once errors are correlated (contrast
  `LinearSEM.isRegCoeff_parents`).
* `Bow.not_identified`: two bows with structural coefficients `1` and `0` (each with a positive
  semidefinite error covariance, as every `LinearSEM` has) imply the same covariance matrix; so
  no function of the covariance matrix recovers `β` (non-identification of the bow).
  `Bow.not_identified_both_active`: the same with both the directed coefficient and the error
  covariance nonzero in both models, and positive definite error covariances.

The instrumental variable repair, `α = r_YZ / r_XZ` when an instrument `Z` is added, is
`LinearSEM.iv_ratio` and `LinearSEM.Fig59.iv_formula`.

Source: J. Pearl (2009), *Causality*, 2nd edition, Section 5.3.1; J. Pearl, M. Glymour and
N. P. Jewell (2016), *Causal Inference in Statistics: A Primer*, Section 3.8.3.
-/

@[expose] public section

namespace CausalInference

namespace LinearSEM

namespace Bow

open Matrix Finset

/-- The graph `X → Y` with `X = 0`, `Y = 1`. -/
def G : Digraph (Fin 2) where
  Adj i j := i = 0 ∧ j = 1

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The error covariance matrix of the bow. -/
abbrev errCov (ωx ωy ω : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![ωx, ω; ω, ωy]

/-- The bow: `Y = β X + ε_Y`, `Var(ε_X) = ω_X`, `Var(ε_Y) = ω_Y`, `Cov(ε_X, ε_Y) = ω`, for a
positive semidefinite error covariance. -/
def model (β ωx ωy ω : ℝ) (hΩ : (errCov ωx ωy ω).PosSemidef) : LinearSEM (Fin 2) where
  G := G
  acyclic := by decide
  B := !![0, 0; β, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := errCov ωx ωy ω
  Ω_posSemidef := hΩ

variable (β ωx ωy ω : ℝ) (hΩ : (errCov ωx ωy ω).PosSemidef)

theorem T_eq : (model β ωx ωy ω hΩ).T = !![1, 0; β, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_two]

/-- The implied covariance matrix of the bow. -/
theorem cov_eq : (model β ωx ωy ω hΩ).cov =
    !![ωx, β * ωx + ω; β * ωx + ω, β ^ 2 * ωx + 2 * β * ω + ωy] := by
  ext i j
  rw [cov_apply, T_eq]
  fin_cases i <;> fin_cases j <;> simp [model, Fin.sum_univ_two]
  all_goals ring

/-- The slope of `Y` on `X` in the bow is `β + ω / ω_X`. -/
theorem slope_eq (hωx : ωx ≠ 0) :
    regSlope (model β ωx ωy ω hΩ).cov 0 1 = β + ω / ωx := by
  simp [regSlope, cov_eq]
  field_simp

/-- With correlated errors the slope is not the structural coefficient. -/
theorem slope_ne (hωx : ωx ≠ 0) (hω : ω ≠ 0) :
    regSlope (model β ωx ωy ω hΩ).cov 0 1 ≠ β := by
  rw [slope_eq β ωx ωy ω hΩ hωx]
  intro h
  exact hω (by simpa [hωx] using h)

/-- Regressing `Y` on its only parent `X` does not return the structural coefficient when the
errors are correlated. -/
theorem regression_ne (hωx : ωx ≠ 0) (hω : ω ≠ 0) {r : Fin 2 → ℝ}
    (hr : IsRegCoeff (model β ωx ωy ω hΩ).cov {0} 1 r) : r 0 ≠ β := by
  have hxx : (model β ωx ωy ω hΩ).cov 0 0 ≠ 0 := by simpa [cov_eq] using hωx
  rw [(isRegCoeff_singleton_iff hxx).1 hr, Pi.single_eq_same]
  exact slope_ne β ωx ωy ω hΩ hωx hω

/-- A 2 by 2 matrix of the form `L Lᵀ` with `L = !![1, 0; a, b]` is positive semidefinite. -/
theorem errCov_posSemidef (a b : ℝ) : (errCov 1 (a ^ 2 + b ^ 2) a).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose !![(1 : ℝ), 0; a, b]
  convert h using 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sq]

/-- Uncorrelated unit errors: `Ω = 1`. -/
theorem psd₁ : (errCov 1 1 0).PosSemidef := by simpa using errCov_posSemidef 0 1

/-- `Ω = !![1, 1; 1, 2]`. -/
theorem psd₂ : (errCov 1 2 1).PosSemidef := by
  have h := errCov_posSemidef 1 1
  norm_num at h
  exact h

/-- `Ω = !![1, -1; -1, 2]`. -/
theorem psd₃ : (errCov 1 2 (-1)).PosSemidef := by
  have h := errCov_posSemidef (-1) 1
  norm_num at h
  exact h

/-- `Ω = !![1, -2; -2, 5]`. -/
theorem psd₄ : (errCov 1 5 (-2)).PosSemidef := by
  have h := errCov_posSemidef (-2) 1
  norm_num at h
  exact h

/-- Non-identification of the bow: the bow with `β = 1` and uncorrelated unit errors and the bow
with `β = 0`, `Var(ε_Y) = 2` and `Cov(ε_X, ε_Y) = 1` have the same implied covariance matrix
(both error covariances are positive semidefinite, as every `LinearSEM` requires), but different
structural coefficients. -/
theorem not_identified :
    (model 1 1 1 0 psd₁).cov = (model 0 1 2 1 psd₂).cov ∧
      (model 1 1 1 0 psd₁).B 1 0 ≠ (model 0 1 2 1 psd₂).B 1 0 := by
  refine ⟨by rw [cov_eq, cov_eq]; norm_num, by simp [model]⟩

/-- Non-identification of the bow with both arcs active in both models: the bows with
`(β, ω_X, ω_Y, ω) = (2, 1, 2, -1)` and `(3, 1, 5, -2)` have nonzero directed coefficients, nonzero
error covariances, positive definite error covariance matrices, and the same implied covariance
matrix `!![1, 1; 1, 2]`, but different structural coefficients. -/
theorem not_identified_both_active :
    (model 2 1 2 (-1) psd₃).cov = (model 3 1 5 (-2) psd₄).cov ∧
      (model 2 1 2 (-1) psd₃).B 1 0 ≠ (model 3 1 5 (-2) psd₄).B 1 0 ∧
      (model 2 1 2 (-1) psd₃).B 1 0 ≠ 0 ∧ (model 3 1 5 (-2) psd₄).B 1 0 ≠ 0 ∧
      (model 2 1 2 (-1) psd₃).Ω 0 1 ≠ 0 ∧ (model 3 1 5 (-2) psd₄).Ω 0 1 ≠ 0 ∧
      (model 2 1 2 (-1) psd₃).Ω.PosDef ∧ (model 3 1 5 (-2) psd₄).Ω.PosDef := by
  refine ⟨by rw [cov_eq, cov_eq]; norm_num, by simp [model], by simp [model], by simp [model],
    by simp [model], by simp [model], ?_, ?_⟩
  · refine (psd₃.posDef_iff_det_ne_zero).2 ?_
    simp [Matrix.det_fin_two]; norm_num
  · refine (psd₄.posDef_iff_det_ne_zero).2 ?_
    simp [Matrix.det_fin_two]; norm_num

end Bow

end LinearSEM

end CausalInference
