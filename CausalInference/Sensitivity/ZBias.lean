/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.LinearSEM.Regression
public import CausalInference.LinearSEM.Basic

/-!
# Z-bias: adjusting for an instrument amplifies confounding bias

A linear structural equation model on four variables, an instrument `Z`, an unmeasured
confounder `U`, a treatment `X` and an outcome `Y` (indices `0, 1, 2, 3`):

`Z = ε_Z`, `U = ε_U`, `X = α Z + γ U + ε_X`, `Y = κ Z + δ U + β X + ε_Y`,

with uncorrelated errors of variances `ω 0, ω 1, ω 2, ω 3` (a diagonal error covariance). The
setting is second moments only, as in `CausalInference.LinearSEM.Basic`: the covariance matrix is
`LinearSEM.cov`, and a regression is a solution of the normal equations (`IsRegCoeff`). The
causal effect of `X` on `Y` is the total effect `T Y X = β`, and the bias of a regression is its
coefficient of `X` minus `T Y X`.

`Z` is uncorrelated with `U` by construction. It is a valid instrument when, in addition, the
exclusion restriction `κ = 0` holds (it then affects `Y` only through `X`) and it is relevant,
`Cov(Z, X) = α ω₀ ≠ 0`. The coefficient `κ` is kept as a parameter so that the failure of the
exclusion restriction is a member of the same family; relevance is not assumed in the
amplification statements: by `ZBias.abs_bias_lt_iff` the amplification is strict exactly when
the instrument is relevant and there is confounding through `U` (`γ δ ω₁ ≠ 0`).

## Main results

Write `v = γ² ω₁ + ω₂`; with `ω₀ = Var(Z) > 0` it is the residual variance
`Var(X) - Cov(X, Z)² / Var(Z)` of the linear regression of `X` on `Z`
(`ZBias.residualVar_XZ`, `ZBias.partialCov_XX`). It is a second moment quantity, not the
conditional variance `Var(X | Z)`: the uncorrelated errors of the model need not be
independent, and when the conditional mean of `X` given `Z` is not linear the two differ (with
`Z` uniform on `{-1, 0, 1}`, `U = Z² - 2/3` and `X = Z + U`, the conditional variance is `0` and
the residual variance is `2/9`). The adjusted statements assume `ω₀ > 0` and `v > 0`.

* `ZBias.bias_unadjusted`: if `Var(X) = α² ω₀ + v > 0`, the regression of `Y` on `X` alone has
  bias `(γ δ ω₁ + α κ ω₀) / Var(X)`.
* `ZBias.bias_adjusted`: the regression of `Y` on `X` and `Z` has bias `γ δ ω₁ / v`, whatever
  `κ`; `ZBias.bias_adjusted_eq_cov` and `ZBias.bias_adjusted_eq_partialCov` state it in
  covariance form, `δ Cov(X, U) Var(Z) / (Var(X) Var(Z) - Cov(X, Z)²) = δ Cov(X, U) / v`.
* `ZBias.bias_adjusted_mul`: under the exclusion restriction the two biases are in the exact
  ratio `Var(X) / v`: adjusted bias times `v` equals unadjusted bias times `Var(X)`.
* `ZBias.abs_bias_le`: Z-bias. Under the exclusion restriction the absolute bias of the
  adjusted regression is at least that of the unadjusted one, with the same sign;
  `ZBias.abs_bias_lt_iff`: the inequality is strict if and only if `α ≠ 0` (relevance,
  equivalently `Cov(Z, X) ≠ 0`) and `γ δ ω₁ ≠ 0` (residual confounding through `U`);
  `ZBias.bias_eq_iff`: otherwise the two biases are equal, and they are both zero when
  `γ δ ω₁ = 0` (`ZBias.bias_eq_zero_of_no_confounding`).
* `ZBias.Example.bias_unadjusted`, `ZBias.Example.bias_adjusted`: with every coefficient and
  every error variance equal to one, the biases are `1/3` and `1/2`.
* `ZBias.Counterexample.abs_bias_adjusted_lt`: when `Z` also affects `Y` directly (`κ = 1`, so
  `Z` is a confounder and not an instrument), adjusting for `Z` reduces the absolute bias from
  `2/3` to `1/2`: amplification needs the exclusion restriction.

The existence statements `ZBias.exists_isRegCoeff_unadjusted` and
`ZBias.exists_isRegCoeff_adjusted` show that the regressions in these statements exist. The
companion claim that adjusting for an instrument with no residual confounding increases the
variance of an estimator is a statement about sampling variance and is not covered here.

Sources: NICE Decision Support Unit Technical Support Document 17 (Faria, Hernandez Alava,
Manca and Wailoo, 2015), Section 2.3 and Section 4.2.2, Question 10, which state the claim
verbally, citing J. Wooldridge (2009), *Should instrumental variables be used as matching
variables*; M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Section 18.2 and
Figure 18.7 (bias amplification, guaranteed in linear structural equation models, citing
Wooldridge 2010 and Pearl 2011).
-/

@[expose] public section

namespace CausalInference

namespace ZBias

open Matrix

/-- The graph `Z → X`, `U → X`, `Z → Y`, `U → Y`, `X → Y` with `Z = 0`, `U = 1`, `X = 2`,
`Y = 3`. -/
def G : Digraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨
    (i = 2 ∧ j = 3)

instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The linear SEM `X = α Z + γ U + ε_X`, `Y = κ Z + δ U + β X + ε_Y`, with `Z` and `U`
exogenous and uncorrelated errors of variances `ω` (nonnegative). The exclusion restriction for
the instrument `Z` is `κ = 0`. -/
def model (α γ β δ κ : ℝ) (ω : Fin 4 → ℝ) (hω : 0 ≤ ω) : LinearSEM (Fin 4) where
  G := G
  acyclic := by decide
  B := !![0, 0, 0, 0; 0, 0, 0, 0; α, γ, 0, 0; κ, δ, β, 0]
  B_support v u h := by fin_cases v <;> fin_cases u <;> simp_all [G]
  Ω := Matrix.diagonal ω
  Ω_posSemidef := PosSemidef.diagonal hω

variable (α γ β δ κ : ℝ) (ω : Fin 4 → ℝ) (hω : 0 ≤ ω)

/-- The error covariance is diagonal: the errors are uncorrelated. -/
theorem isDiag_Ω : (model α γ β δ κ ω hω).Ω.IsDiag := isDiag_diagonal ω

/-- The total effect matrix. -/
theorem T_eq : (model α γ β δ κ ω hω).T =
    !![1, 0, 0, 0; 0, 1, 0, 0; α, γ, 1, 0; κ + β * α, δ + β * γ, β, 1] :=
  LinearSEM.T_eq_of_mul_eq_one _ <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [model, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals ring

/-- The causal effect of `X` on `Y` is `β`. -/
theorem T_Y_X : (model α γ β δ κ ω hω).T 3 2 = β := by
  rw [T_eq]; rfl

/-- The implied covariances. -/
theorem cov_eq (i j : Fin 4) : (model α γ β δ κ ω hω).cov i j =
    ∑ k, (!![1, 0, 0, 0; 0, 1, 0, 0; α, γ, 1, 0; κ + β * α, δ + β * γ, β, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) i k * ω k *
      (!![1, 0, 0, 0; 0, 1, 0, 0; α, γ, 1, 0; κ + β * α, δ + β * γ, β, 1] :
        Matrix (Fin 4) (Fin 4) ℝ) j k := by
  rw [LinearSEM.cov_apply_of_isDiag _ (isDiag_Ω α γ β δ κ ω hω), T_eq]; rfl

theorem cov_ZZ : (model α γ β δ κ ω hω).cov 0 0 = ω 0 := by
  simp [cov_eq, Fin.sum_univ_four]

theorem cov_XZ : (model α γ β δ κ ω hω).cov 2 0 = α * ω 0 := by
  simp [cov_eq, Fin.sum_univ_four]

theorem cov_XU : (model α γ β δ κ ω hω).cov 2 1 = γ * ω 1 := by
  simp [cov_eq, Fin.sum_univ_four]

theorem cov_ZU : (model α γ β δ κ ω hω).cov 0 1 = 0 := by
  simp [cov_eq, Fin.sum_univ_four]

theorem cov_XX : (model α γ β δ κ ω hω).cov 2 2 = α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2) := by
  simp [cov_eq, Fin.sum_univ_four]; ring

theorem cov_XY : (model α γ β δ κ ω hω).cov 2 3 =
    β * (α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2)) + (γ * δ * ω 1 + α * κ * ω 0) := by
  simp [cov_eq, Fin.sum_univ_four]; ring

theorem cov_ZY : (model α γ β δ κ ω hω).cov 0 3 = (κ + β * α) * ω 0 := by
  simp [cov_eq, Fin.sum_univ_four]; ring

variable {α γ β δ κ ω hω}

theorem cov_XX_pos (hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2)) :
    0 < (model α γ β δ κ ω hω).cov 2 2 := by
  rwa [cov_XX]

theorem det_XZ : (model α γ β δ κ ω hω).cov 2 2 * (model α γ β δ κ ω hω).cov 0 0 -
    (model α γ β δ κ ω hω).cov 2 0 ^ 2 = (γ ^ 2 * ω 1 + ω 2) * ω 0 := by
  rw [cov_XX, cov_ZZ, cov_XZ]; ring

/-- The covariance block of `{Z}` is invertible when `Var(Z) = ω₀ > 0`. -/
theorem isUnit_subCov_Z (hz : 0 < ω 0) : IsUnit (subCov (model α γ β δ κ ω hω).cov {0}) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse
    (B := (ω 0)⁻¹ • 1) ?_)
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [Finset.mem_singleton] at hi hj
  subst hi hj
  simp only [Matrix.mul_apply, Fintype.sum_unique, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [Subsingleton.elim (default : ({0} : Finset (Fin 4))) ⟨0, hj⟩, Matrix.one_apply_eq]
  change (model α γ β δ κ ω hω).cov 0 0 * ((ω 0)⁻¹ * 1) = 1
  rw [cov_ZZ, mul_one, mul_inv_cancel₀ hz.ne']

/-- The residual variance of the linear regression of `X` on `Z`, written out:
`Var(X) - Cov(X, Z)² / Var(Z) = γ² ω₁ + ω₂`. The left side is a residual variance only when
`Var(Z) = ω₀ > 0` (for `ω₀ = 0` the identity holds through `x / 0 = 0`, since then
`Cov(X, Z) = 0`). It is not the conditional variance `Var(X | Z)`, which second moments do not
determine. -/
theorem residualVar_XZ :
    (model α γ β δ κ ω hω).cov 2 2 -
        (model α γ β δ κ ω hω).cov 2 0 ^ 2 / (model α γ β δ κ ω hω).cov 0 0 =
      γ ^ 2 * ω 1 + ω 2 := by
  rw [cov_XX, cov_XZ, cov_ZZ]
  field_simp
  ring

/-- `γ² ω₁ + ω₂` is the partial covariance of `X` with itself given `Z`, that is the residual
variance `Var(X) - Cov(X, Z)² / Var(Z)` of the linear regression of `X` on `Z`
(`IsRegCoeff.partialCov_eq_covComb`, `ZBias.residualVar_XZ`). It is not the conditional
variance `Var(X | Z)` unless the conditional mean of `X` given `Z` is linear with constant
conditional variance, which the second moment model does not assume. -/
theorem partialCov_XX (hz : 0 < ω 0) :
    partialCov (model α γ β δ κ ω hω).cov {0} 2 2 = γ ^ 2 * ω 1 + ω 2 := by
  have hreg := regCoeff_isRegCoeff 2 (isUnit_subCov_Z (α := α) (γ := γ) (β := β) (δ := δ)
    (κ := κ) (hω := hω) hz)
  rw [partialCov, (isRegCoeff_singleton_iff (by rw [cov_ZZ]; exact hz.ne')).1 hreg]
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [cov_XX, cov_ZZ, cov_XZ, (model α γ β δ κ ω hω).cov_symm 0 2, cov_XZ]
  field_simp
  ring

/-! ### The two biases -/

/-- The regression of `Y` on `X` alone exists when `Var(X) = α² ω₀ + γ² ω₁ + ω₂ > 0`. -/
theorem exists_isRegCoeff_unadjusted (hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2)) :
    ∃ r, IsRegCoeff (model α γ β δ κ ω hω).cov {2} 3 r :=
  exists_isRegCoeff_singleton 3 (cov_XX_pos hW).ne'

/-- The regression of `Y` on `X` and `Z` exists when `Var(Z) > 0` and the residual variance
`γ² ω₁ + ω₂` of `X` on `Z` is positive. -/
theorem exists_isRegCoeff_adjusted (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2) :
    ∃ r, IsRegCoeff (model α γ β δ κ ω hω).cov {2, 0} 3 r :=
  exists_isRegCoeff_pair 3 (by decide) ((model α γ β δ κ ω hω).cov_symm 0 2)
    (by rw [det_XZ]; positivity)

/-- The bias of the unadjusted regression: if `Var(X) = α² ω₀ + (γ² ω₁ + ω₂) > 0`, the
coefficient of `X` in the regression of `Y` on `X` alone exceeds the causal effect `T Y X = β`
by `(γ δ ω₁ + α κ ω₀) / Var(X)`; here `γ² ω₁ + ω₂` is the residual variance of `X` on `Z`.
The term `γ δ ω₁ =
δ Cov(X, U)` is the confounding through `U`, the term `α κ ω₀` the confounding through `Z`
(zero under the exclusion restriction). -/
theorem bias_unadjusted (hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2)) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ κ ω hω).cov {2} 3 r) :
    r 2 - (model α γ β δ κ ω hω).T 3 2 =
      (γ * δ * ω 1 + α * κ * ω 0) / (α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2)) := by
  have hXX := cov_XX_pos (β := β) (δ := δ) (κ := κ) (hω := hω) hW
  rw [(isRegCoeff_singleton_iff hXX.ne').1 hr, Pi.single_eq_same, T_Y_X]
  rw [cov_XX] at hXX ⊢
  rw [cov_XY]
  field_simp
  ring

/-- The bias of the regression adjusted for the instrument: if `Var(Z) = ω₀ > 0` and the
residual variance `v = γ² ω₁ + ω₂` of `X` on `Z` is positive, the coefficient of `X` in the
regression of `Y` on `X` and `Z` exceeds the causal effect `T Y X = β` by `γ δ ω₁ / v`,
whatever the direct effect `κ` of `Z` on `Y`. -/
theorem bias_adjusted (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ κ ω hω).cov {2, 0} 3 r) :
    r 2 - (model α γ β δ κ ω hω).T 3 2 = γ * δ * ω 1 / (γ ^ 2 * ω 1 + ω 2) := by
  have hD := det_XZ (α := α) (γ := γ) (β := β) (δ := δ) (κ := κ) (hω := hω)
  have hD0 : (γ ^ 2 * ω 1 + ω 2) * ω 0 ≠ 0 := by positivity
  rw [((isRegCoeff_pair_iff (by decide) ((model α γ β δ κ ω hω).cov_symm 0 2)
    (hD ▸ hD0)).1 hr).2.1, hD, T_Y_X, cov_ZZ, cov_XY, cov_XZ, cov_ZY]
  field_simp
  ring

/-- The adjusted bias in covariance form: under the hypotheses of `bias_adjusted`, it is
`δ Cov(X, U) Var(Z) / (Var(X) Var(Z) - Cov(X, Z)²)`, that is `δ Cov(X, U)` divided by the
residual variance of `X` on `Z`. -/
theorem bias_adjusted_eq_cov (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2) {r : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ κ ω hω).cov {2, 0} 3 r) :
    r 2 - (model α γ β δ κ ω hω).T 3 2 =
      δ * (model α γ β δ κ ω hω).cov 2 1 * (model α γ β δ κ ω hω).cov 0 0 /
        ((model α γ β δ κ ω hω).cov 2 2 * (model α γ β δ κ ω hω).cov 0 0 -
          (model α γ β δ κ ω hω).cov 2 0 ^ 2) := by
  rw [bias_adjusted hz hv hr, det_XZ, cov_XU, cov_ZZ]
  field_simp

/-- The adjusted bias with the partial variance: under the hypotheses of `bias_adjusted`, it is
`δ Cov(X, U) / partialCov Σ {Z} X X`, the partial variance being the residual variance of `X`
on `Z`, as in the Frisch, Waugh, and Lovell form `IsRegCoeff.eq_partialCov_div` of the adjusted
coefficient. -/
theorem bias_adjusted_eq_partialCov (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2)
    {r : Fin 4 → ℝ} (hr : IsRegCoeff (model α γ β δ κ ω hω).cov {2, 0} 3 r) :
    r 2 - (model α γ β δ κ ω hω).T 3 2 =
      δ * (model α γ β δ κ ω hω).cov 2 1 / partialCov (model α γ β δ κ ω hω).cov {0} 2 2 := by
  rw [bias_adjusted hz hv hr, partialCov_XX hz, cov_XU]; ring

/-! ### Amplification under the exclusion restriction -/

/-- The amplification factor: under the exclusion restriction (`κ = 0`), with `Var(Z) > 0` and
positive residual variance `v = γ² ω₁ + ω₂ = Var(X) - Cov(X, Z)² / Var(Z)` of `X` on `Z`, the
adjusted bias times `v` equals the unadjusted bias times `Var(X)`. So the adjusted bias is the
unadjusted bias multiplied by `Var(X) / v = 1 / (1 - Corr(X, Z)²)`. -/
theorem bias_adjusted_mul (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2) {r s : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ 0 ω hω).cov {2} 3 r)
    (hs : IsRegCoeff (model α γ β δ 0 ω hω).cov {2, 0} 3 s) :
    (s 2 - (model α γ β δ 0 ω hω).T 3 2) * (γ ^ 2 * ω 1 + ω 2) =
      (r 2 - (model α γ β δ 0 ω hω).T 3 2) * (α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2)) := by
  have hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2) := by
    have := mul_nonneg (sq_nonneg α) hz.le; linarith
  rw [bias_adjusted hz hv hs, bias_unadjusted hW hr]
  field_simp
  ring

/-- Z-bias (bias amplification). Under the exclusion restriction (`κ = 0`), with `Var(Z) > 0`
and positive residual variance `γ² ω₁ + ω₂` of `X` on `Z`, the biases of the unadjusted and
the `Z`-adjusted regressions have the same sign, and adjusting for the instrument does not
decrease the absolute bias. -/
theorem abs_bias_le (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2) {r s : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ 0 ω hω).cov {2} 3 r)
    (hs : IsRegCoeff (model α γ β δ 0 ω hω).cov {2, 0} 3 s) :
    0 ≤ (r 2 - (model α γ β δ 0 ω hω).T 3 2) * (s 2 - (model α γ β δ 0 ω hω).T 3 2) ∧
      |r 2 - (model α γ β δ 0 ω hω).T 3 2| ≤ |s 2 - (model α γ β δ 0 ω hω).T 3 2| := by
  have hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2) := by
    have := mul_nonneg (sq_nonneg α) hz.le; linarith
  rw [bias_adjusted hz hv hs, bias_unadjusted hW hr]
  simp only [mul_zero, zero_mul, add_zero]
  refine ⟨by rw [div_mul_div_comm]; exact div_nonneg (mul_self_nonneg _) (mul_pos hW hv).le, ?_⟩
  rw [abs_div, abs_div, abs_of_pos hW, abs_of_pos hv]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hv
    (by have := mul_nonneg (sq_nonneg α) hz.le; linarith)

/-- When Z-bias is strict. Under the hypotheses of `abs_bias_le`, adjusting for the instrument
strictly increases the absolute bias if and only if the instrument is relevant (`α ≠ 0`,
equivalently `Cov(Z, X) = α ω₀ ≠ 0`) and there is residual confounding through `U`
(`γ δ ω₁ = δ Cov(X, U) ≠ 0`). -/
theorem abs_bias_lt_iff (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2) {r s : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ 0 ω hω).cov {2} 3 r)
    (hs : IsRegCoeff (model α γ β δ 0 ω hω).cov {2, 0} 3 s) :
    |r 2 - (model α γ β δ 0 ω hω).T 3 2| < |s 2 - (model α γ β δ 0 ω hω).T 3 2| ↔
      α ≠ 0 ∧ γ * δ * ω 1 ≠ 0 := by
  have hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2) := by
    have := mul_nonneg (sq_nonneg α) hz.le; linarith
  rw [bias_adjusted hz hv hs, bias_unadjusted hW hr]
  simp only [mul_zero, zero_mul, add_zero]
  rw [abs_div, abs_div, abs_of_pos hW, abs_of_pos hv, div_lt_div_iff₀ hW hv]
  have key : |γ * δ * ω 1| * (α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2)) -
      |γ * δ * ω 1| * (γ ^ 2 * ω 1 + ω 2) = |γ * δ * ω 1| * α ^ 2 * ω 0 := by ring
  constructor
  · intro h
    have hpos : 0 < |γ * δ * ω 1| * α ^ 2 * ω 0 := by linarith
    refine ⟨fun ha => ?_, fun hk => ?_⟩
    · simp [ha] at hpos
    · simp [hk] at hpos
  · rintro ⟨ha, hk⟩
    have : 0 < |γ * δ * ω 1| * α ^ 2 * ω 0 := by positivity
    linarith

/-- When the two biases coincide. Under the hypotheses of `abs_bias_le`, the unadjusted and
the `Z`-adjusted biases are equal if and only if the instrument is irrelevant (`α = 0`) or
there is no confounding through `U` (`γ δ ω₁ = 0`). -/
theorem bias_eq_iff (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2) {r s : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ 0 ω hω).cov {2} 3 r)
    (hs : IsRegCoeff (model α γ β δ 0 ω hω).cov {2, 0} 3 s) :
    s 2 - (model α γ β δ 0 ω hω).T 3 2 = r 2 - (model α γ β δ 0 ω hω).T 3 2 ↔
      α = 0 ∨ γ * δ * ω 1 = 0 := by
  have hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2) := by
    have := mul_nonneg (sq_nonneg α) hz.le; linarith
  rw [bias_adjusted hz hv hs, bias_unadjusted hW hr]
  simp only [mul_zero, zero_mul, add_zero]
  rw [div_eq_div_iff hv.ne' hW.ne']
  constructor
  · intro h
    have : γ * δ * ω 1 * (α ^ 2 * ω 0) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with hk | h2
    · exact Or.inr hk
    · rcases mul_eq_zero.1 h2 with ha | hz0
      · exact Or.inl (pow_eq_zero_iff two_ne_zero |>.1 ha)
      · exact absurd hz0 hz.ne'
  · rintro (ha | hk)
    · rw [ha]; ring
    · rw [hk]; ring

/-- Under the exclusion restriction and with no confounding through `U` (`γ δ ω₁ = 0`), both
regressions are unbiased, whether or not the instrument is relevant: adjusting for `Z` adds no
bias. -/
theorem bias_eq_zero_of_no_confounding (hz : 0 < ω 0) (hv : 0 < γ ^ 2 * ω 1 + ω 2)
    (hk : γ * δ * ω 1 = 0) {r s : Fin 4 → ℝ}
    (hr : IsRegCoeff (model α γ β δ 0 ω hω).cov {2} 3 r)
    (hs : IsRegCoeff (model α γ β δ 0 ω hω).cov {2, 0} 3 s) :
    r 2 - (model α γ β δ 0 ω hω).T 3 2 = 0 ∧ s 2 - (model α γ β δ 0 ω hω).T 3 2 = 0 := by
  have hW : 0 < α ^ 2 * ω 0 + (γ ^ 2 * ω 1 + ω 2) := by
    have := mul_nonneg (sq_nonneg α) hz.le; linarith
  rw [bias_adjusted hz hv hs, bias_unadjusted hW hr, hk]
  simp

/-! ### A numeric model -/

/-- Unit error variances. -/
theorem unitVar_nonneg : (0 : Fin 4 → ℝ) ≤ fun _ => 1 := fun _ => zero_le_one

namespace Example

/-- A valid instrument with every coefficient and every error variance equal to one:
`X = Z + U + ε_X`, `Y = U + X + ε_Y`, so `Var(X) = 3` and the residual variance of `X` on `Z`
is `2`. -/
abbrev M : LinearSEM (Fin 4) := model 1 1 1 1 0 (fun _ => 1) unitVar_nonneg

/-- The unadjusted regression has bias `1/3`. -/
theorem bias_unadjusted {r : Fin 4 → ℝ} (hr : IsRegCoeff M.cov {2} 3 r) :
    r 2 - M.T 3 2 = 1 / 3 := by
  rw [ZBias.bias_unadjusted (by norm_num) hr]; norm_num

/-- Adjusting for the instrument raises the bias to `1/2`. -/
theorem bias_adjusted {s : Fin 4 → ℝ} (hs : IsRegCoeff M.cov {2, 0} 3 s) :
    s 2 - M.T 3 2 = 1 / 2 := by
  rw [ZBias.bias_adjusted (by norm_num) (by norm_num) hs]; norm_num

end Example

/-! ### Countermodel: an instrument that is also a confounder -/

namespace Counterexample

/-- The model of `Example` with a direct arrow `Z → Y` of coefficient `κ = 1`: the exclusion
restriction fails and `Z` is a confounder of `X` and `Y`. -/
abbrev M : LinearSEM (Fin 4) := model 1 1 1 1 1 (fun _ => 1) unitVar_nonneg

/-- The unadjusted regression has bias `2/3`: confounding through `U` and through `Z`. -/
theorem bias_unadjusted {r : Fin 4 → ℝ} (hr : IsRegCoeff M.cov {2} 3 r) :
    r 2 - M.T 3 2 = 2 / 3 := by
  rw [ZBias.bias_unadjusted (by norm_num) hr]; norm_num

/-- The `Z`-adjusted regression has bias `1/2`. -/
theorem bias_adjusted {s : Fin 4 → ℝ} (hs : IsRegCoeff M.cov {2, 0} 3 s) :
    s 2 - M.T 3 2 = 1 / 2 := by
  rw [ZBias.bias_adjusted (by norm_num) (by norm_num) hs]; norm_num

/-- Without the exclusion restriction amplification fails: adjusting for `Z` strictly reduces
the absolute bias, from `2/3` to `1/2`, so `abs_bias_le` does not extend to `κ ≠ 0`. -/
theorem abs_bias_adjusted_lt {r s : Fin 4 → ℝ} (hr : IsRegCoeff M.cov {2} 3 r)
    (hs : IsRegCoeff M.cov {2, 0} 3 s) : |s 2 - M.T 3 2| < |r 2 - M.T 3 2| := by
  rw [bias_unadjusted hr, bias_adjusted hs]; norm_num [abs_of_pos]

/-- The regressions of the countermodel exist, so `abs_bias_adjusted_lt` is not vacuous. -/
theorem exists_regressions :
    (∃ r, IsRegCoeff M.cov {2} 3 r) ∧ ∃ s, IsRegCoeff M.cov {2, 0} 3 s :=
  ⟨exists_isRegCoeff_unadjusted (by norm_num),
    exists_isRegCoeff_adjusted (by norm_num) (by norm_num)⟩

end Counterexample

end ZBias

end CausalInference
