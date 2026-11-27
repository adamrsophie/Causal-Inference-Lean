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
* `Bow.not_identified`: two bows with structural coefficients `1` and `0`, both with positive
  semidefinite error covariance, imply the same covariance matrix; so no function of the
  covariance matrix recovers `β` (non-identification of the bow).

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

/-- The bow: `Y = β X + ε_Y`, `Var(ε_X) = ω_X`, `Var(ε_Y) = ω_Y`, `Cov(ε_X, ε_Y) = ω`. -/
def model (β ωx ωy ω : ℝ) : LinearSEM (Fin 2) where
  G := G
  acyclic := by decide
  B := !![0, 0; β, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := !![ωx, ω; ω, ωy]
  Ω_symm := by ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem T_eq (β ωx ωy ω : ℝ) : (model β ωx ωy ω).T = !![1, 0; β, 1] :=
  T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_two]

/-- The implied covariance matrix of the bow. -/
theorem cov_eq (β ωx ωy ω : ℝ) : (model β ωx ωy ω).cov =
    !![ωx, β * ωx + ω; β * ωx + ω, β ^ 2 * ωx + 2 * β * ω + ωy] := by
  ext i j
  rw [cov_apply, T_eq]
  fin_cases i <;> fin_cases j <;> simp [model, Fin.sum_univ_two]
  all_goals ring

/-- The slope of `Y` on `X` in the bow is `β + ω / ω_X`. -/
theorem slope_eq (β ωx ωy ω : ℝ) (hωx : ωx ≠ 0) :
    regSlope (model β ωx ωy ω).cov 0 1 = β + ω / ωx := by
  simp [regSlope, cov_eq]
  field_simp

/-- With correlated errors the slope is not the structural coefficient. -/
theorem slope_ne (β ωx ωy ω : ℝ) (hωx : ωx ≠ 0) (hω : ω ≠ 0) :
    regSlope (model β ωx ωy ω).cov 0 1 ≠ β := by
  rw [slope_eq β ωx ωy ω hωx]
  intro h
  exact hω (by simpa [hωx] using h)

/-- Regressing `Y` on its only parent `X` does not return the structural coefficient when the
errors are correlated. -/
theorem regression_ne (β ωx ωy ω : ℝ) (hωx : ωx ≠ 0) (hω : ω ≠ 0) {r : Fin 2 → ℝ}
    (hr : IsRegCoeff (model β ωx ωy ω).cov {0} 1 r) : r 0 ≠ β := by
  have hxx : (model β ωx ωy ω).cov 0 0 ≠ 0 := by simpa [cov_eq] using hωx
  rw [(isRegCoeff_singleton_iff hxx).1 hr, Pi.single_eq_same]
  exact slope_ne β ωx ωy ω hωx hω

/-- Non-identification of the bow: the bow with `β = 1` and independent unit errors and the bow
with `β = 0`, `Var(ε_Y) = 2` and `Cov(ε_X, ε_Y) = 1` have the same implied covariance matrix
and positive semidefinite error covariances, but different structural coefficients. -/
theorem not_identified :
    (model 1 1 1 0).cov = (model 0 1 2 1).cov ∧ (model 1 1 1 0).B 1 0 ≠ (model 0 1 2 1).B 1 0 ∧
      (model 1 1 1 0).Ω.PosSemidef ∧ (model 0 1 2 1).Ω.PosSemidef := by
  refine ⟨by rw [cov_eq, cov_eq]; norm_num, by simp [model], ?_, ?_⟩
  · have : (model 1 1 1 0).Ω = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [model]
    rw [this]
    exact Matrix.PosSemidef.one
  · have : (model 0 1 2 1).Ω = !![(1 : ℝ), 0; 1, 1] * (!![(1 : ℝ), 0; 1, 1])ᴴ := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_two]
      norm_num
    rw [this]
    exact Matrix.posSemidef_self_mul_conjTranspose _

end Bow

end LinearSEM

end CausalInference
