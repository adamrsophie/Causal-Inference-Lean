/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.LinearIV
public import CausalInference.LinearSEM.Regression
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Measurement error for continuous variables

Linear measurement error models of Fox, MacLehose and Lash (2021), *Applying Quantitative Bias
Analysis to Epidemiologic Data*, second edition, Chapter 10, sections "Classical and Berkson
Measurement Error for Continuous Exposures" and "Regression Calibration" (Equations 10.7 to
10.19). Every regression is a population least squares projection, written with Mathlib's
`covariance` and `variance`; every statement read statistically assumes a probability measure
and square integrable variables (`MemLp _ 2 μ`), since Mathlib gives a variable of infinite
variance the variance `0`. The only exceptions are named as identities between totalized
expressions (`coef2_normal_equations_totalized`) or are algebra in real numbers. The results
are exact for these linear projections; the book applies them to log-linear, logistic and
proportional hazards models, where they hold only approximately.

## Main definitions

* `slope μ X Y = Cov(X, Y) / Var(X)` and `coef2 μ X W Y`, the coefficient of `X` in the
  regression of `Y` on `(X, W)`; `resVar μ X W`, the residual variance `σ²_{X|W}`.
* `reliability μ x e = Var(x) / (Var(x) + Var(e))`, the attenuation factor.
* `ClassicalError` and `TwoCovariateError`: the error models, as structures of hypotheses.

## Main results

* `ClassicalError.slope_surrogate`: `β' = λ β` (Equation 10.7);
  `ClassicalError.slope_eq_div_reliability`: `β = β' / λ` (Equation 10.8);
  `ClassicalError.reliability_eq_sq_corr`: `λ` is the squared correlation of `x` and `m`;
  `ClassicalError.abs_slope_surrogate_le`, `ClassicalError.abs_slope_surrogate_lt_iff`:
  toward the null, strictly exactly when `Var(e) > 0` and `β ≠ 0`.
* `reliability_lt_one_iff_not_ae_const`: `λ < 1` exactly when the error is not almost surely
  constant.
* `slope_surrogate_eq_mul_calibration`, `beta_eq_div_calibration`,
  `slope_true_eq_div_calibration`: regression calibration, `β = β' / γ`;
  `calibration_classical` (`γ = λ`), `calibration_berkson` (`γ = 1`),
  `slope_berkson_eq_slope_true` (Berkson error does not attenuate), `slope_classical_linear`;
  `calibration_delta_variance`: Equation 10.10 as a first-order variance, with the joint
  gradient `calibration_ratio_hasFDerivAt` and the covariance term for overlapping samples
  `calibration_delta_variance_cov`.
* `regression_calibration_covariates`, `regression_calibration_covariates_true`: regression
  calibration with error-free covariates (Equations 10.14 to 10.16), exact for the identity link.
* `coef2_normal_equations`, `isRegCoeff_slope`, `isRegCoeff_coef2`: `slope` and `coef2` are least
  squares coefficients, and agree with `IsRegCoeff` of `LinearSEM.Regression`.
* `slope_outcome_error`, `slope_outcome_error_differential`: error in a continuous outcome
  leaves the slope unchanged (Equation 10.17) or adds `δ` (Equation 10.19).
* `TwoCovariateError.coef2_surrogate`, `TwoCovariateError.coef2_eq_correction`: the
  two-covariate formula and its inversion, stated correctly. The printed Equation 10.12 uses the
  weights `(σ²_{x|v} / σ²_{m|w}) (σ²_{v|x} / σ²_{w|m})` and `1 - σ²_{v|x} / σ²_{w|m}`, and the
  printed Equation 10.13 is its exact rearrangement; both fail in a model satisfying every
  hypothesis (`Examples.printed_equations_10_12_10_13_fail`). The two printed special cases are
  `coef2_surrogate_of_var_e'_eq_zero` and `coef2_surrogate_of_var_e_eq_zero`;
  `TwoCovariateError.coef2_eq_moment_correction` computes the true coefficient from observed
  moments and the error variances.
* Counterexamples: `Examples.differential_not_attenuated` (correlated error and outcome move
  the slope away from the null), `Examples.berkson_coefficient_ne_true_slope`,
  `Examples.two_covariate_not_between` and `Examples.two_covariate_confounded_not_between`
  (with both covariates mismeasured the estimate need not lie between the crude and the adjusted
  value, also under genuine confounding).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace CausalInference.BiasAnalysis.MeasurementError

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The population least squares slope of `Y` on `X` (with intercept):
`Cov(X, Y) / Var(X)`. It is meaningful only when `Var(X) ≠ 0`, which every result below
assumes. -/
noncomputable def slope (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ := cov[X, Y; μ] / Var[X; μ]

/-- The reliability ratio (attenuation factor) of `m = x + e` as a measure of `x`:
`λ = Var(x) / (Var(x) + Var(e))`. -/
noncomputable def reliability (μ : Measure Ω) (x e : Ω → ℝ) : ℝ :=
  Var[x; μ] / (Var[x; μ] + Var[e; μ])

/-- Variance of a sum of uncorrelated square integrable variables. -/
theorem variance_add_of_cov_eq_zero [IsProbabilityMeasure μ] {x e : Ω → ℝ} (hx : MemLp x 2 μ)
    (he : MemLp e 2 μ) (hxe : cov[x, e; μ] = 0) : Var[x + e; μ] = Var[x; μ] + Var[e; μ] := by
  rw [variance_add hx he, hxe]; ring

/-- The reliability ratio is positive when `Var(x) > 0`. Both variables are square integrable,
so that `Var(e)` is the variance of the error and not Mathlib's value `0` for a variable of
infinite variance. -/
theorem reliability_pos {x e : Ω → ℝ} (_hx2 : MemLp x 2 μ) (_he2 : MemLp e 2 μ)
    (hx : 0 < Var[x; μ]) : 0 < reliability μ x e :=
  div_pos hx (by linarith [variance_nonneg e μ])

/-- The reliability ratio is at most one (square integrable `x` and `e`, `Var(x) > 0`). -/
theorem reliability_le_one {x e : Ω → ℝ} (_hx2 : MemLp x 2 μ) (_he2 : MemLp e 2 μ)
    (hx : 0 < Var[x; μ]) : reliability μ x e ≤ 1 :=
  (div_le_one (by linarith [variance_nonneg e μ])).2 (by linarith [variance_nonneg e μ])

/-- The reliability ratio is strictly below one exactly when the error has positive variance
(square integrable `x` and `e`, `Var(x) > 0`). Without `MemLp e 2 μ` an error of infinite
variance would have `Var(e) = 0` in Mathlib and reliability one. -/
theorem reliability_lt_one_iff {x e : Ω → ℝ} (_hx2 : MemLp x 2 μ) (_he2 : MemLp e 2 μ)
    (hx : 0 < Var[x; μ]) : reliability μ x e < 1 ↔ 0 < Var[e; μ] := by
  rw [reliability, div_lt_one (by linarith [variance_nonneg e μ])]
  constructor <;> intro h <;> linarith

/-- A square integrable variable has variance zero exactly when it is almost surely equal to
its mean. -/
theorem variance_eq_zero_iff_ae_eq [IsProbabilityMeasure μ] {e : Ω → ℝ} (he : MemLp e 2 μ) :
    Var[e; μ] = 0 ↔ e =ᵐ[μ] fun _ ↦ μ[e] := by
  refine ⟨ae_eq_integral_of_variance_eq_zero he, fun h ↦ ?_⟩
  rw [variance, (evariance_eq_zero_iff he.aemeasurable).2 h, ENNReal.toReal_zero]

/-- **Strict attenuation in statistical terms.** For square integrable `x` and `e` with
`Var(x) > 0`, the reliability ratio is below one exactly when the error is not almost surely
constant. -/
theorem reliability_lt_one_iff_not_ae_const [IsProbabilityMeasure μ] {x e : Ω → ℝ}
    (hx2 : MemLp x 2 μ) (he2 : MemLp e 2 μ) (hx : 0 < Var[x; μ]) :
    reliability μ x e < 1 ↔ ¬ e =ᵐ[μ] fun _ ↦ μ[e] := by
  rw [reliability_lt_one_iff hx2 he2 hx, ← variance_eq_zero_iff_ae_eq he2]
  exact ⟨fun h h0 ↦ by linarith, fun h ↦ lt_of_le_of_ne (variance_nonneg e μ) (Ne.symm h)⟩

/-! ### Classical error -/

/-- **The classical measurement error model** for the slope of an outcome `y` on a continuous
exposure `x` observed through the surrogate `m = x + e`: all three variables are square
integrable, the error is uncorrelated with the true value (`Cov(x, e) = 0`) and with the
outcome (`Cov(e, y) = 0`, the linear form of nondifferential error). -/
structure ClassicalError (μ : Measure Ω) (x e y : Ω → ℝ) : Prop where
  memLp_x : MemLp x 2 μ
  memLp_e : MemLp e 2 μ
  memLp_y : MemLp y 2 μ
  cov_x_e : cov[x, e; μ] = 0
  cov_e_y : cov[e, y; μ] = 0

namespace ClassicalError

variable [IsProbabilityMeasure μ] {x e y : Ω → ℝ}

theorem cov_surrogate (h : ClassicalError μ x e y) : cov[x + e, y; μ] = cov[x, y; μ] := by
  rw [covariance_add_left h.memLp_x h.memLp_e h.memLp_y, h.cov_e_y, add_zero]

theorem var_surrogate (h : ClassicalError μ x e y) :
    Var[x + e; μ] = Var[x; μ] + Var[e; μ] :=
  variance_add_of_cov_eq_zero h.memLp_x h.memLp_e h.cov_x_e

/-- **Classical error attenuates the slope** (Fox, MacLehose and Lash 2021, Equation 10.7).
Under the classical error model with `Var(x) > 0`, the slope of `y` on the surrogate
`m = x + e` is the reliability ratio times the slope of `y` on `x`:
`β' = λ β` with `λ = Var(x) / (Var(x) + Var(e))`. This is an exact statement about population
least squares slopes; the book states it for log-linear risk models, where it holds only
approximately. -/
theorem slope_surrogate (h : ClassicalError μ x e y) (hx : 0 < Var[x; μ]) :
    slope μ (x + e) y = reliability μ x e * slope μ x y := by
  have he := variance_nonneg e μ
  rw [slope, slope, reliability, h.cov_surrogate, h.var_surrogate]
  field_simp

/-- **Correction for classical error** (Equation 10.8): `β = β' / λ`. -/
theorem slope_eq_div_reliability (h : ClassicalError μ x e y) (hx : 0 < Var[x; μ]) :
    slope μ x y = slope μ (x + e) y / reliability μ x e := by
  rw [h.slope_surrogate hx, mul_div_cancel_left₀ _ (reliability_pos h.memLp_x h.memLp_e hx).ne']

/-- **The reliability ratio is the squared correlation** of `x` and `m = x + e`
(the text after Equation 10.7): `λ = Cov(x, m)² / (Var(x) Var(m))`. -/
theorem reliability_eq_sq_corr (h : ClassicalError μ x e y) (hx : 0 < Var[x; μ]) :
    reliability μ x e = cov[x, x + e; μ] ^ 2 / (Var[x; μ] * Var[x + e; μ]) := by
  have he := variance_nonneg e μ
  rw [covariance_add_right h.memLp_x h.memLp_x h.memLp_e, h.cov_x_e,
    covariance_self h.memLp_x.aemeasurable, h.var_surrogate, reliability]
  field_simp
  ring

/-- **Toward the null.** Under the classical error model the surrogate slope is never farther
from zero than the true slope: `|β'| ≤ |β|`. -/
theorem abs_slope_surrogate_le (h : ClassicalError μ x e y) (hx : 0 < Var[x; μ]) :
    |slope μ (x + e) y| ≤ |slope μ x y| := by
  rw [h.slope_surrogate hx, abs_mul, abs_of_pos (reliability_pos h.memLp_x h.memLp_e hx)]
  exact mul_le_of_le_one_left (abs_nonneg _) (reliability_le_one h.memLp_x h.memLp_e hx)

/-- **Strict attenuation.** Under the classical error model, `|β'| < |β|` if and only if the
error has positive variance and the true slope is nonzero. -/
theorem abs_slope_surrogate_lt_iff (h : ClassicalError μ x e y) (hx : 0 < Var[x; μ]) :
    |slope μ (x + e) y| < |slope μ x y| ↔ 0 < Var[e; μ] ∧ slope μ x y ≠ 0 := by
  rw [h.slope_surrogate hx, abs_mul, abs_of_pos (reliability_pos h.memLp_x h.memLp_e hx),
    ← reliability_lt_one_iff h.memLp_x h.memLp_e hx]
  constructor
  · intro hlt
    refine ⟨?_, fun h0 ↦ by simp [h0] at hlt⟩
    by_contra hge
    have := mul_le_mul_of_nonneg_right (not_lt.1 hge) (abs_nonneg (slope μ x y))
    linarith
  · rintro ⟨hl, hne⟩
    exact mul_lt_of_lt_one_left (abs_pos.2 hne) hl

end ClassicalError

/-- The reliability ratio written through the ratio `r = σ_e / σ_x` of standard deviations, as
in Figure 10.2: `σ_x² / (σ_x² + σ_e²) = 1 / (1 + r²)`. -/
theorem attenuation_eq_of_sd_ratio {σx σe : ℝ} (hx : 0 < σx) :
    σx ^ 2 / (σx ^ 2 + σe ^ 2) = 1 / (1 + (σe / σx) ^ 2) := by
  field_simp

/-! ### A linear outcome model, regression calibration and Berkson error -/

/-- Covariance of a square integrable `W` with a linear outcome `α + β x + u`:
`Cov(W, α + β x + u) = β Cov(W, x) + Cov(W, u)`. This is
`CausalInference.LinearIVModel.covariance_Y` with `W` in the role of the instrument. -/
theorem cov_linear [IsProbabilityMeasure μ] {W x u : Ω → ℝ} (α β : ℝ) (hW : MemLp W 2 μ)
    (hx : MemLp x 2 μ) (hu : MemLp u 2 μ) :
    cov[W, fun ω ↦ α + β * x ω + u ω; μ] = β * cov[W, x; μ] + cov[W, u; μ] :=
  LinearIVModel.covariance_Y (L := ⟨α, β, x, W, u⟩) hW hx hu

/-- In the linear outcome model `y = α + β x + u` with `Cov(x, u) = 0` and `Var(x) ≠ 0`, the
slope of `y` on the true exposure `x` is `β`. -/
theorem slope_linear [IsProbabilityMeasure μ] {x u : Ω → ℝ} (α β : ℝ) (hx : MemLp x 2 μ)
    (hu : MemLp u 2 μ) (hxu : cov[x, u; μ] = 0) (hV : Var[x; μ] ≠ 0) :
    slope μ x (fun ω ↦ α + β * x ω + u ω) = β := by
  rw [slope, cov_linear α β hx hx hu, hxu, add_zero, covariance_self hx.aemeasurable,
    mul_div_assoc, div_self hV, mul_one]

/-- **Regression calibration, exact linear form.** Let `y = α + β x + u` and let `m` be any
square integrable surrogate with `Cov(m, u) = 0` (the outcome depends on `m` only through `x`,
in the linear sense) and `Var(m) ≠ 0`. Then the slope of `y` on `m` is `β γ`, where
`γ = Cov(m, x) / Var(m)` is the calibration slope of `x` on `m` (Equation 10.11). The proof does
not use `Var(m) ≠ 0`; the hypothesis only excludes the degenerate case where both slopes are
`0` by the convention `t / 0 = 0`. -/
theorem slope_surrogate_eq_mul_calibration [IsProbabilityMeasure μ] {m x u : Ω → ℝ} (α β : ℝ)
    (hm : MemLp m 2 μ) (hx : MemLp x 2 μ) (hu : MemLp u 2 μ) (hmu : cov[m, u; μ] = 0)
    (_hVm : Var[m; μ] ≠ 0) :
    slope μ m (fun ω ↦ α + β * x ω + u ω) = β * slope μ m x := by
  rw [slope, slope, cov_linear α β hm hx hu, hmu, add_zero, mul_div_assoc]

/-- **Regression calibration estimand** (Fox, MacLehose and Lash 2021, section "Regression
Calibration", `β = β' / γ`). Under the hypotheses of `slope_surrogate_eq_mul_calibration` and
a nonzero calibration covariance `Cov(m, x) ≠ 0`, `β` is the surrogate slope divided by the
calibration slope. This is exact for the linear outcome model; for the logistic and
proportional hazards models of the book it is an approximation (rare disease, modest effect,
modest error). -/
theorem beta_eq_div_calibration [IsProbabilityMeasure μ] {m x u : Ω → ℝ} (α β : ℝ)
    (hm : MemLp m 2 μ) (hx : MemLp x 2 μ) (hu : MemLp u 2 μ) (hmu : cov[m, u; μ] = 0)
    (hVm : Var[m; μ] ≠ 0) (hmx : cov[m, x; μ] ≠ 0) :
    β = slope μ m (fun ω ↦ α + β * x ω + u ω) / slope μ m x := by
  rw [slope_surrogate_eq_mul_calibration α β hm hx hu hmu hVm, mul_div_assoc,
    div_self (show slope μ m x ≠ 0 from div_ne_zero hmx hVm), mul_one]

/-- **Regression calibration recovers the slope on the true exposure.** In
`beta_eq_div_calibration` the coefficient `β` is that of the supplied decomposition
`y = α + β x + u`. If moreover `Cov(x, u) = 0` and `Var(x) ≠ 0`, then `β` is the slope of `y` on
`x`, so the surrogate slope divided by the calibration slope is the slope on the true exposure:
`slope(y on x) = slope(y on m) / slope(x on m)`. -/
theorem slope_true_eq_div_calibration [IsProbabilityMeasure μ] {m x u : Ω → ℝ} (α β : ℝ)
    (hm : MemLp m 2 μ) (hx : MemLp x 2 μ) (hu : MemLp u 2 μ) (hmu : cov[m, u; μ] = 0)
    (hxu : cov[x, u; μ] = 0) (hVm : Var[m; μ] ≠ 0) (hVx : Var[x; μ] ≠ 0)
    (hmx : cov[m, x; μ] ≠ 0) :
    slope μ x (fun ω ↦ α + β * x ω + u ω) =
      slope μ m (fun ω ↦ α + β * x ω + u ω) / slope μ m x := by
  rw [slope_linear α β hx hu hxu hVx]
  exact beta_eq_div_calibration α β hm hx hu hmu hVm hmx

/-- Under classical error (`m = x + e`, `Cov(x, e) = 0`, `Var(x) > 0`) the calibration slope
of `x` on `m` is the reliability ratio: `γ = λ`. So Equation 10.8 is the special case of
regression calibration with classical error. (The proof does not use `Var(x) > 0`, which only
excludes the degenerate case where both sides are `0`.) -/
theorem calibration_classical [IsProbabilityMeasure μ] {x e : Ω → ℝ} (hx : MemLp x 2 μ)
    (he : MemLp e 2 μ) (hxe : cov[x, e; μ] = 0) (_hV : 0 < Var[x; μ]) :
    slope μ (x + e) x = reliability μ x e := by
  rw [slope, covariance_add_left hx he hx, covariance_comm e, hxe, add_zero,
    covariance_self hx.aemeasurable, variance_add_of_cov_eq_zero hx he hxe, reliability]

/-- Under Berkson error (`x = m + e` with `Cov(m, e) = 0` and `Var(m) ≠ 0`) the calibration
slope of `x` on `m` is one: `γ = 1`. -/
theorem calibration_berkson [IsProbabilityMeasure μ] {m e : Ω → ℝ} (hm : MemLp m 2 μ)
    (he : MemLp e 2 μ) (hme : cov[m, e; μ] = 0) (hV : Var[m; μ] ≠ 0) :
    slope μ m (m + e) = 1 := by
  rw [slope, covariance_add_right hm hm he, hme, add_zero, covariance_self hm.aemeasurable,
    div_self hV]

/-- Berkson error, coefficient form. Let `x = m + e` with `Cov(m, e) = 0`, the outcome
`y = α + β x + u` with `Cov(m, u) = 0`, and `Var(m) ≠ 0`. Then the slope of `y` on the assigned
value `m` is the coefficient `β` of the supplied decomposition. Without `Cov(e, u) = 0` this `β`
need not be the slope of `y` on the true exposure `x`
(`Examples.berkson_coefficient_ne_true_slope`); `slope_berkson_eq_slope_true` is the statement
of the book. -/
theorem slope_berkson [IsProbabilityMeasure μ] {m e u : Ω → ℝ} (α β : ℝ) (hm : MemLp m 2 μ)
    (he : MemLp e 2 μ) (hu : MemLp u 2 μ) (hme : cov[m, e; μ] = 0) (hmu : cov[m, u; μ] = 0)
    (hV : Var[m; μ] ≠ 0) :
    slope μ m (fun ω ↦ α + β * (m + e) ω + u ω) = β := by
  rw [slope_surrogate_eq_mul_calibration α β hm (hm.add he) hu hmu hV,
    calibration_berkson hm he hme hV, mul_one]

/-- **Berkson error does not attenuate** (section "Classical and Berkson Measurement Error",
`β' = β`). Let the true exposure be `x = m + e` with `Cov(m, e) = 0`, the outcome
`y = α + β x + u` with the residual `u` uncorrelated with `m` and with `e` (so with `x`), and
`Var(m) ≠ 0`. Then the slope of `y` on the assigned value `m` equals the slope of `y` on the true
exposure `x`, and both are `β`. Exact for the linear model; the book states it for log-linear
risk models. -/
theorem slope_berkson_eq_slope_true [IsProbabilityMeasure μ] {m e u : Ω → ℝ} (α β : ℝ)
    (hm : MemLp m 2 μ) (he : MemLp e 2 μ) (hu : MemLp u 2 μ) (hme : cov[m, e; μ] = 0)
    (hmu : cov[m, u; μ] = 0) (heu : cov[e, u; μ] = 0) (hV : Var[m; μ] ≠ 0) :
    slope μ m (fun ω ↦ α + β * (m + e) ω + u ω) =
        slope μ (m + e) (fun ω ↦ α + β * (m + e) ω + u ω) ∧
      slope μ (m + e) (fun ω ↦ α + β * (m + e) ω + u ω) = β := by
  have hxu : cov[m + e, u; μ] = 0 := by rw [covariance_add_left hm he hu, hmu, heu, add_zero]
  have hVx : Var[m + e; μ] ≠ 0 := by
    rw [variance_add_of_cov_eq_zero hm he hme]
    exact (lt_of_lt_of_le ((variance_nonneg m μ).lt_of_ne (Ne.symm hV))
      (le_add_of_nonneg_right (variance_nonneg e μ))).ne'
  rw [slope_berkson α β hm he hu hme hmu hV, slope_linear α β (hm.add he) hu hxu hVx]
  exact ⟨rfl, rfl⟩

/-- **Classical error in the linear outcome model.** With `y = α + β x + u`, `m = x + e`,
`Cov(x, e) = Cov(x, u) = Cov(e, u) = 0` and `Var(x) > 0`, the surrogate slope is `λ β`, where
`β` is the slope of `y` on `x` by `slope_linear`. -/
theorem slope_classical_linear [IsProbabilityMeasure μ] {x e u : Ω → ℝ} (α β : ℝ)
    (hx : MemLp x 2 μ) (he : MemLp e 2 μ) (hu : MemLp u 2 μ) (hxe : cov[x, e; μ] = 0)
    (hxu : cov[x, u; μ] = 0) (heu : cov[e, u; μ] = 0) (hV : 0 < Var[x; μ]) :
    slope μ (x + e) (fun ω ↦ α + β * x ω + u ω) = reliability μ x e * β := by
  have hmu : cov[x + e, u; μ] = 0 := by
    rw [covariance_add_left hx he hu, hxu, heu, add_zero]
  have hVm : Var[x + e; μ] ≠ 0 := by
    rw [variance_add_of_cov_eq_zero hx he hxe]; linarith [variance_nonneg e μ]
  rw [slope_surrogate_eq_mul_calibration α β (hx.add he) hx hu hmu hVm,
    calibration_classical hx he hxe hV, mul_comm]

/-- **First-order variance of the calibrated slope** (Equation 10.10). The map
`(b, g) ↦ b / g` has partial derivatives `1 / g` and `-b / g²` at a point with `g ≠ 0`, and
the first-order (delta method) variance for independent estimates `β̂'` and `γ̂`,
`(∂/∂b)² Var(β̂') + (∂/∂g)² Var(γ̂)`, equals the printed
`Var(β̂') / γ̂² + (β̂² / γ̂²) Var(γ̂)` with `β̂ = β̂' / γ̂`. This is the linearization only, not an
exact variance of a ratio. -/
theorem calibration_delta_variance {b g Vb Vg : ℝ} (hg : g ≠ 0) :
    HasDerivAt (fun t ↦ t / g) (1 / g) b ∧ HasDerivAt (fun t ↦ b / t) (-b / g ^ 2) g ∧
      (1 / g) ^ 2 * Vb + (-b / g ^ 2) ^ 2 * Vg = Vb / g ^ 2 + (b / g) ^ 2 / g ^ 2 * Vg := by
  refine ⟨?_, ?_, by field_simp⟩
  · convert (hasDerivAt_id' b).mul_const g⁻¹ using 1
    · funext t; ring
    · ring
  · convert (hasDerivAt_inv hg).const_mul b using 1
    · funext t; ring
    · ring

/-- The calibrated slope `(b, g) ↦ b / g` is differentiable as a map of both arguments at a
point with `g ≠ 0`, with derivative `(db, dg) ↦ db / g - b dg / g²`. This is the joint gradient
that a multivariate delta method uses for Equation 10.10. -/
theorem calibration_ratio_hasFDerivAt {b g : ℝ} (hg : g ≠ 0) :
    HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 / p.2)
      ((1 / g) • ContinuousLinearMap.fst ℝ ℝ ℝ + (-b / g ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (b, g) := by
  have h := (hasFDerivAt_fst (𝕜 := ℝ) (p := (b, g))).mul
    ((hasFDerivAt_inv (𝕜 := ℝ) hg).comp (b, g) (hasFDerivAt_snd (𝕜 := ℝ) (p := (b, g))))
  convert h using 1
  · funext p; simp [div_eq_mul_inv]
  · refine ContinuousLinearMap.ext fun p ↦ ?_
    simp
    field_simp
    ring

/-- **First-order variance of the calibrated slope with correlated estimates.** When `β̂'` and
`γ̂` come from overlapping samples (internal validation) with covariance `C`, the first-order
variance of `β̂ = β̂' / γ̂` along the gradient `(1 / g, -b / g²)` is
`Var(β̂') / γ̂² + (β̂² / γ̂²) Var(γ̂) - 2 b C / g³`: Equation 10.10 plus a cross term, which
vanishes for independent estimates. Linearization only. -/
theorem calibration_delta_variance_cov {b g Vb Vg C : ℝ} (hg : g ≠ 0) :
    (1 / g) ^ 2 * Vb + (-b / g ^ 2) ^ 2 * Vg + 2 * (1 / g) * (-b / g ^ 2) * C =
      Vb / g ^ 2 + (b / g) ^ 2 / g ^ 2 * Vg - 2 * b * C / g ^ 3 := by
  field_simp
  ring

/-! ### Error in a continuous outcome -/

/-- **Nondifferential error in a continuous outcome** (Equation 10.17). If the outcome `y` is
recorded as `s = y + ε` with `Cov(x, ε) = 0` and `Var(x) ≠ 0`, the slope of `s` on `x` equals
the slope of `y` on `x`: outcome error of this kind does not bias the slope. (The proof does not
use `Var(x) ≠ 0`, which only excludes the degenerate case where both slopes are `0`.) -/
theorem slope_outcome_error [IsProbabilityMeasure μ] {x y ε : Ω → ℝ} (hx : MemLp x 2 μ)
    (hy : MemLp y 2 μ) (hε : MemLp ε 2 μ) (hxε : cov[x, ε; μ] = 0) (_hV : Var[x; μ] ≠ 0) :
    slope μ x (y + ε) = slope μ x y := by
  rw [slope, slope, covariance_add_right hx hy hε, hxε, add_zero]

/-- **Differential error in a continuous outcome** (Equation 10.19). If `s = y + δ x + ε` with
`Cov(x, ε) = 0` and `Var(x) ≠ 0`, the slope of `s` on `x` is the slope of `y` on `x` plus `δ`;
the bias is removed by subtracting `δ`. -/
theorem slope_outcome_error_differential [IsProbabilityMeasure μ] {x y ε : Ω → ℝ} (δ : ℝ)
    (hx : MemLp x 2 μ) (hy : MemLp y 2 μ) (hε : MemLp ε 2 μ) (hxε : cov[x, ε; μ] = 0)
    (hV : Var[x; μ] ≠ 0) :
    slope μ x (fun ω ↦ y ω + δ * x ω + ε ω) = slope μ x y + δ := by
  have hf : (fun ω ↦ y ω + δ * x ω + ε ω) = y + ((fun ω ↦ δ * x ω) + ε) := by
    funext ω; simp only [Pi.add_apply]; ring
  rw [slope, slope, hf, covariance_add_right hx hy ((hx.const_mul δ).add hε),
    covariance_add_right hx (hx.const_mul δ) hε, covariance_const_mul_right, hxε,
    covariance_self hx.aemeasurable, add_zero]
  field_simp

/-! ### Two mismeasured covariates -/

/-- The coefficient of `X` in the population least squares regression of `Y` on `X` and `W`
(with intercept), by Cramer's rule for the normal equations:
`(Var(W) Cov(X, Y) - Cov(X, W) Cov(W, Y)) / (Var(X) Var(W) - Cov(X, W)²)`. It is meaningful only
when the determinant `Var(X) Var(W) - Cov(X, W)²` is nonzero, which the results assume. -/
noncomputable def coef2 (μ : Measure Ω) (X W Y : Ω → ℝ) : ℝ :=
  (Var[W; μ] * cov[X, Y; μ] - cov[X, W; μ] * cov[W, Y; μ]) /
    (Var[X; μ] * Var[W; μ] - cov[X, W; μ] ^ 2)

/-- The residual variance of `X` after linear regression on `W`:
`σ²_{X|W} = Var(X) - Cov(X, W)² / Var(W)`. -/
noncomputable def resVar (μ : Measure Ω) (X W : Ω → ℝ) : ℝ :=
  Var[X; μ] - cov[X, W; μ] ^ 2 / Var[W; μ]

/-- The normal equations as an identity between totalized expressions: with
`b = coef2 X W Y` and `c = coef2 W X Y`, `Cov(X, Y) = b Var(X) + c Cov(X, W)` and
`Cov(W, Y) = b Cov(X, W) + c Var(W)` hold for Mathlib's `covariance` and `variance` whenever the
determinant is nonzero, whatever the integrability. They are least squares normal equations
only for square integrable variables (`coef2_normal_equations`). -/
theorem coef2_normal_equations_totalized {X W Y : Ω → ℝ}
    (hD : Var[X; μ] * Var[W; μ] - cov[X, W; μ] ^ 2 ≠ 0) :
    cov[X, Y; μ] = coef2 μ X W Y * Var[X; μ] + coef2 μ W X Y * cov[X, W; μ] ∧
      cov[W, Y; μ] = coef2 μ X W Y * cov[X, W; μ] + coef2 μ W X Y * Var[W; μ] := by
  have hD' : Var[W; μ] * Var[X; μ] - cov[W, X; μ] ^ 2 ≠ 0 := by
    rw [covariance_comm W X, mul_comm]; exact hD
  unfold coef2
  rw [covariance_comm W X] at hD' ⊢
  constructor <;> field_simp <;> ring

/-- **`coef2` is the least squares coefficient.** For square integrable `X`, `W`, `Y` on a
probability space with `Var(X) Var(W) - Cov(X, W)² ≠ 0`, `b = coef2 X W Y` and
`c = coef2 W X Y` solve the normal equations, and the residual `Y - b X - c W` is uncorrelated
with `X` and with `W`. -/
theorem coef2_normal_equations [IsProbabilityMeasure μ] {X W Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hW : MemLp W 2 μ) (hY : MemLp Y 2 μ)
    (hD : Var[X; μ] * Var[W; μ] - cov[X, W; μ] ^ 2 ≠ 0) :
    (cov[X, Y; μ] = coef2 μ X W Y * Var[X; μ] + coef2 μ W X Y * cov[X, W; μ] ∧
      cov[W, Y; μ] = coef2 μ X W Y * cov[X, W; μ] + coef2 μ W X Y * Var[W; μ]) ∧
    cov[X, fun ω ↦ Y ω - coef2 μ X W Y * X ω - coef2 μ W X Y * W ω; μ] = 0 ∧
      cov[W, fun ω ↦ Y ω - coef2 μ X W Y * X ω - coef2 μ W X Y * W ω; μ] = 0 := by
  obtain ⟨h1, h2⟩ := coef2_normal_equations_totalized (Y := Y) hD
  have hres : ∀ Z : Ω → ℝ, MemLp Z 2 μ →
      cov[Z, fun ω ↦ Y ω - coef2 μ X W Y * X ω - coef2 μ W X Y * W ω; μ] =
        cov[Z, Y; μ] - coef2 μ X W Y * cov[Z, X; μ] - coef2 μ W X Y * cov[Z, W; μ] := by
    intro Z hZ
    rw [show (fun ω ↦ Y ω - coef2 μ X W Y * X ω - coef2 μ W X Y * W ω) =
        (Y - fun ω ↦ coef2 μ X W Y * X ω) - fun ω ↦ coef2 μ W X Y * W ω from rfl,
      covariance_sub_right hZ (hY.sub (hX.const_mul _)) (hW.const_mul _),
      covariance_sub_right hZ hY (hX.const_mul _), covariance_const_mul_right,
      covariance_const_mul_right]
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩
  · rw [hres X hX, covariance_self hX.aemeasurable, h1]; ring
  · rw [hres W hW, covariance_self hW.aemeasurable, covariance_comm W X, h2]; ring

/-- Uniqueness of the solution of the normal equations: if `b` and `c` satisfy
`Cov(X, Y) = b Var(X) + c Cov(X, W)` and `Cov(W, Y) = b Cov(X, W) + c Var(W)` and the
determinant is nonzero, then `coef2 X W Y = b`. -/
theorem coef2_eq_of_normal_equations {X W Y : Ω → ℝ} {b c : ℝ}
    (hD : Var[X; μ] * Var[W; μ] - cov[X, W; μ] ^ 2 ≠ 0)
    (h1 : cov[X, Y; μ] = b * Var[X; μ] + c * cov[X, W; μ])
    (h2 : cov[W, Y; μ] = b * cov[X, W; μ] + c * Var[W; μ]) : coef2 μ X W Y = b := by
  rw [coef2, h1, h2, div_eq_iff hD]
  ring

/-! ### Regression calibration with error-free covariates (Equations 10.14 to 10.16) -/

/-- Covariance with an affine combination of two variables:
`Cov(Z, k + p A + q B) = p Cov(Z, A) + q Cov(Z, B)`. -/
theorem cov_affine [IsProbabilityMeasure μ] {Z A B : Ω → ℝ} (k p q : ℝ) (hZ : MemLp Z 2 μ)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    cov[Z, fun ω ↦ k + p * A ω + q * B ω; μ] = p * cov[Z, A; μ] + q * cov[Z, B; μ] := by
  have hf : (fun ω ↦ k + p * A ω + q * B ω) =
      fun ω ↦ k + ((fun ω ↦ p * A ω) + fun ω ↦ q * B ω) ω := by
    funext ω; simp only [Pi.add_apply]; ring
  rw [hf, covariance_const_add_right (((hA.const_mul p).add (hB.const_mul q)).integrable
    (by norm_num)), covariance_add_right hZ (hA.const_mul p) (hB.const_mul q),
    covariance_const_mul_right, covariance_const_mul_right]

/-- Covariance with an affine combination of two variables plus a third:
`Cov(Z, k + p A + q B + C) = p Cov(Z, A) + q Cov(Z, B) + Cov(Z, C)`. -/
theorem cov_affine_add [IsProbabilityMeasure μ] {Z A B C : Ω → ℝ} (k p q : ℝ)
    (hZ : MemLp Z 2 μ) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hC : MemLp C 2 μ) :
    cov[Z, fun ω ↦ k + p * A ω + q * B ω + C ω; μ] =
      p * cov[Z, A; μ] + q * cov[Z, B; μ] + cov[Z, C; μ] := by
  have hAB : MemLp (fun ω ↦ k + p * A ω + q * B ω) 2 μ :=
    ((memLp_const k).add (hA.const_mul p)).add (hB.const_mul q)
  rw [show (fun ω ↦ k + p * A ω + q * B ω + C ω) = (fun ω ↦ k + p * A ω + q * B ω) + C from rfl,
    covariance_add_right hZ hAB hC, cov_affine k p q hZ hA hB]

/-- **Regression calibration with error-free covariates, exact linear form** (Equations 10.14
to 10.16). Let `m` be the surrogate, `v` a covariate measured without error, and let the
calibration model of Equation 10.15 hold as a population projection:
`x = a + γ m + ρ v + e` with `Cov(m, e) = Cov(v, e) = 0`. Let the outcome be
`y = α + β x + η v + u` with `Cov(m, u) = Cov(v, u) = 0` (the surrogate carries no information
on the outcome beyond `x` and `v`, in the linear sense), and let
`Var(m) Var(v) - Cov(m, v)² ≠ 0` and `γ ≠ 0`. Then
* the coefficient of `m` in the regression of `x` on `(m, v)` is `γ`;
* the coefficient of `m` in the regression of `y` on `(m, v)` (the biased `β` of Equation 10.14)
  is `β γ`;
* the coefficient of the calibrated exposure `x̃ = a + γ m + ρ v` in the regression of `y` on
  `(x̃, v)` (the `θ₁` of Equation 10.16) is `β`.
So `β = β' / γ` with the covariate-adjusted calibration coefficient `γ`. This is exact for the
identity link only; for the logistic and other links of the book it is an approximation. -/
theorem regression_calibration_covariates [IsProbabilityMeasure μ] {m v e u x : Ω → ℝ}
    (a γ ρ α β η : ℝ) (hm : MemLp m 2 μ) (hv : MemLp v 2 μ) (he : MemLp e 2 μ)
    (hu : MemLp u 2 μ) (hx : ∀ ω, x ω = a + γ * m ω + ρ * v ω + e ω)
    (hme : cov[m, e; μ] = 0) (hve : cov[v, e; μ] = 0) (hmu : cov[m, u; μ] = 0)
    (hvu : cov[v, u; μ] = 0) (hD : Var[m; μ] * Var[v; μ] - cov[m, v; μ] ^ 2 ≠ 0)
    (hγ : γ ≠ 0) :
    coef2 μ m v x = γ ∧ coef2 μ m v (fun ω ↦ α + β * x ω + η * v ω + u ω) = β * γ ∧
      coef2 μ (fun ω ↦ a + γ * m ω + ρ * v ω) v (fun ω ↦ α + β * x ω + η * v ω + u ω) =
        β := by
  have hxf : x = fun ω ↦ a + γ * m ω + ρ * v ω + e ω := funext hx
  have hxL : MemLp x 2 μ := by
    rw [hxf]; exact (((memLp_const a).add (hm.const_mul γ)).add (hv.const_mul ρ)).add he
  set xt : Ω → ℝ := fun ω ↦ a + γ * m ω + ρ * v ω with hxt
  have hxtL : MemLp xt 2 μ := ((memLp_const a).add (hm.const_mul γ)).add (hv.const_mul ρ)
  have hVm := covariance_self (μ := μ) hm.aemeasurable
  have hVv := covariance_self (μ := μ) hv.aemeasurable
  have hvm : cov[v, m; μ] = cov[m, v; μ] := covariance_comm v m
  -- covariances with the true exposure
  have hcx : ∀ Z : Ω → ℝ, MemLp Z 2 μ →
      cov[Z, x; μ] = γ * cov[Z, m; μ] + ρ * cov[Z, v; μ] + cov[Z, e; μ] := fun Z hZ ↦ by
    rw [hxf]; exact cov_affine_add a γ ρ hZ hm hv he
  have hcy : ∀ Z : Ω → ℝ, MemLp Z 2 μ →
      cov[Z, fun ω ↦ α + β * x ω + η * v ω + u ω; μ] =
        β * cov[Z, x; μ] + η * cov[Z, v; μ] + cov[Z, u; μ] := fun Z hZ ↦
    cov_affine_add α β η hZ hxL hv hu
  have hcxt : ∀ Z : Ω → ℝ, MemLp Z 2 μ →
      cov[Z, xt; μ] = γ * cov[Z, m; μ] + ρ * cov[Z, v; μ] := fun Z hZ ↦
    cov_affine a γ ρ hZ hm hv
  have hmx := hcx m hm
  have hvx := hcx v hv
  rw [hVm, hme] at hmx
  rw [hVv, hvm, hve] at hvx
  refine ⟨coef2_eq_of_normal_equations hD (c := ρ) (by rw [hmx]; ring) (by rw [hvx]; ring),
    coef2_eq_of_normal_equations hD (c := β * ρ + η)
      (by rw [hcy m hm, hmx, hmu]; ring) (by rw [hcy v hv, hvx, hVv, hvu]; ring), ?_⟩
  -- the calibrated exposure
  have hxtm : cov[xt, m; μ] = γ * Var[m; μ] + ρ * cov[m, v; μ] := by
    rw [covariance_comm, hcxt m hm, hVm]
  have hxtv : cov[xt, v; μ] = γ * cov[m, v; μ] + ρ * Var[v; μ] := by
    rw [covariance_comm, hcxt v hv, hVv, hvm]
  have hVxt : Var[xt; μ] = γ * (γ * Var[m; μ] + ρ * cov[m, v; μ]) +
      ρ * (γ * cov[m, v; μ] + ρ * Var[v; μ]) := by
    rw [← covariance_self hxtL.aemeasurable, hcxt xt hxtL, hxtm, hxtv]
  have hxte : cov[xt, e; μ] = 0 := by
    rw [covariance_comm, hcxt e he, covariance_comm e m, covariance_comm e v, hme, hve]; ring
  have hxtu : cov[xt, u; μ] = 0 := by
    rw [covariance_comm, hcxt u hu, covariance_comm u m, covariance_comm u v, hmu, hvu]; ring
  have hxtx : cov[xt, x; μ] = Var[xt; μ] := by
    rw [hcx xt hxtL, hxtm, hxtv, hxte, hVxt]; ring
  refine coef2_eq_of_normal_equations (c := η) ?_ ?_ ?_
  · rw [hVxt, hxtv]
    intro h0
    exact hD (by
      have : γ ^ 2 * (Var[m; μ] * Var[v; μ] - cov[m, v; μ] ^ 2) = 0 := by linear_combination h0
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.1 h) hγ
      · exact h)
  · rw [hcy xt hxtL, hxtx, hxtv, hxtu]; ring
  · rw [hcy v hv, hcx v hv, hVv, hvm, hve, hvu, hxtv]; ring

/-- **The calibrated coefficient is the true adjusted coefficient.** Under the hypotheses of
`regression_calibration_covariates`, if moreover the outcome residual is uncorrelated with the
calibration residual (`Cov(e, u) = 0`, so `u` is uncorrelated with `x` and `v`) and the true
covariates are nondegenerate (`Var(x) Var(v) - Cov(x, v)² ≠ 0`), then `β` is the coefficient
of `x` in the regression of `y` on `(x, v)`, and it equals the surrogate coefficient divided by
the calibration coefficient: `β_{x|v} = β'_{m|v} / γ_{m|v}`. -/
theorem regression_calibration_covariates_true [IsProbabilityMeasure μ] {m v e u x : Ω → ℝ}
    (a γ ρ α β η : ℝ) (hm : MemLp m 2 μ) (hv : MemLp v 2 μ) (he : MemLp e 2 μ)
    (hu : MemLp u 2 μ) (hx : ∀ ω, x ω = a + γ * m ω + ρ * v ω + e ω)
    (hme : cov[m, e; μ] = 0) (hve : cov[v, e; μ] = 0) (hmu : cov[m, u; μ] = 0)
    (hvu : cov[v, u; μ] = 0) (heu : cov[e, u; μ] = 0)
    (hD : Var[m; μ] * Var[v; μ] - cov[m, v; μ] ^ 2 ≠ 0)
    (hDx : Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2 ≠ 0) (hγ : γ ≠ 0) :
    coef2 μ x v (fun ω ↦ α + β * x ω + η * v ω + u ω) = β ∧
      coef2 μ x v (fun ω ↦ α + β * x ω + η * v ω + u ω) =
        coef2 μ m v (fun ω ↦ α + β * x ω + η * v ω + u ω) / coef2 μ m v x := by
  obtain ⟨h1, h2, -⟩ :=
    regression_calibration_covariates a γ ρ α β η hm hv he hu hx hme hve hmu hvu hD hγ
  have hxf : x = fun ω ↦ a + γ * m ω + ρ * v ω + e ω := funext hx
  have hxL : MemLp x 2 μ := by
    rw [hxf]; exact (((memLp_const a).add (hm.const_mul γ)).add (hv.const_mul ρ)).add he
  have hxu : cov[x, u; μ] = 0 := by
    rw [covariance_comm, hxf, cov_affine_add a γ ρ hu hm hv he, covariance_comm u m,
      covariance_comm u v, covariance_comm u e, hmu, hvu, heu]; ring
  have hβ : coef2 μ x v (fun ω ↦ α + β * x ω + η * v ω + u ω) = β := by
    refine coef2_eq_of_normal_equations (c := η) hDx ?_ ?_
    · rw [cov_affine_add α β η hxL hxL hv hu, covariance_self hxL.aemeasurable, hxu]; ring
    · rw [cov_affine_add α β η hv hxL hv hu, covariance_self hv.aemeasurable,
        covariance_comm v x, hvu]; ring
  refine ⟨hβ, ?_⟩
  rw [hβ, h1, h2, mul_div_assoc, div_self hγ, mul_one]

/-- The algebra behind the two-covariate formula: for reals with `a b - c² ≠ 0`, `a ≠ 0` and
`(a + s)(b + t) - c² ≠ 0`,
`((b + t) p - c q) / ((a + s)(b + t) - c²)
  = ((a b - c²) / ((a + s)(b + t) - c²)) ((b p - c q) / (a b - c²))
    + (a t / ((a + s)(b + t) - c²)) (p / a)`. -/
theorem two_covariate_algebra {a b c s t p q : ℝ} (h0 : a * b - c ^ 2 ≠ 0) (ha : a ≠ 0)
    (h1 : (a + s) * (b + t) - c ^ 2 ≠ 0) :
    ((b + t) * p - c * q) / ((a + s) * (b + t) - c ^ 2) =
      (a * b - c ^ 2) / ((a + s) * (b + t) - c ^ 2) * ((b * p - c * q) / (a * b - c ^ 2)) +
        a * t / ((a + s) * (b + t) - c ^ 2) * (p / a) := by
  generalize (a + s) * (b + t) - c ^ 2 = D at h1 ⊢
  generalize a * b - c ^ 2 = E at h0 ⊢
  field_simp
  ring

/-- **Two covariates measured with classical error.** The exposure `x` and the confounder `v`
are observed through `m = x + e` and `w = v + e'`; all variables are square integrable; the
errors are uncorrelated with each other, with both true values and with the outcome `y`. -/
structure TwoCovariateError (μ : Measure Ω) (x v e e' y : Ω → ℝ) : Prop where
  memLp_x : MemLp x 2 μ
  memLp_v : MemLp v 2 μ
  memLp_e : MemLp e 2 μ
  memLp_e' : MemLp e' 2 μ
  memLp_y : MemLp y 2 μ
  cov_x_e : cov[x, e; μ] = 0
  cov_v_e : cov[v, e; μ] = 0
  cov_x_e' : cov[x, e'; μ] = 0
  cov_v_e' : cov[v, e'; μ] = 0
  cov_e_e' : cov[e, e'; μ] = 0
  cov_e_y : cov[e, y; μ] = 0
  cov_e'_y : cov[e', y; μ] = 0

namespace TwoCovariateError

variable [IsProbabilityMeasure μ] {x v e e' y : Ω → ℝ}

theorem var_m (h : TwoCovariateError μ x v e e' y) : Var[x + e; μ] = Var[x; μ] + Var[e; μ] :=
  variance_add_of_cov_eq_zero h.memLp_x h.memLp_e h.cov_x_e

theorem var_w (h : TwoCovariateError μ x v e e' y) :
    Var[v + e'; μ] = Var[v; μ] + Var[e'; μ] :=
  variance_add_of_cov_eq_zero h.memLp_v h.memLp_e' h.cov_v_e'

theorem cov_m_w (h : TwoCovariateError μ x v e e' y) :
    cov[x + e, v + e'; μ] = cov[x, v; μ] := by
  rw [covariance_add_left h.memLp_x h.memLp_e (h.memLp_v.add h.memLp_e'),
    covariance_add_right h.memLp_x h.memLp_v h.memLp_e',
    covariance_add_right h.memLp_e h.memLp_v h.memLp_e', h.cov_x_e', covariance_comm e v,
    h.cov_v_e, h.cov_e_e']
  ring

theorem cov_m_y (h : TwoCovariateError μ x v e e' y) : cov[x + e, y; μ] = cov[x, y; μ] := by
  rw [covariance_add_left h.memLp_x h.memLp_e h.memLp_y, h.cov_e_y, add_zero]

theorem cov_w_y (h : TwoCovariateError μ x v e e' y) : cov[v + e', y; μ] = cov[v, y; μ] := by
  rw [covariance_add_left h.memLp_v h.memLp_e' h.memLp_y, h.cov_e'_y, add_zero]

/-- The determinant of the observed covariates is positive when that of the true covariates
is: `Var(m) Var(w) - Cov(m, w)² ≥ Var(x) Var(v) - Cov(x, v)² > 0`. -/
theorem det_pos (h : TwoCovariateError μ x v e e' y)
    (hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) :
    0 < Var[x + e; μ] * Var[v + e'; μ] - cov[x + e, v + e'; μ] ^ 2 := by
  rw [h.var_m, h.var_w, h.cov_m_w]
  have := variance_nonneg x μ
  have := variance_nonneg v μ
  have := variance_nonneg e μ
  have := variance_nonneg e' μ
  nlinarith [mul_nonneg (variance_nonneg e μ) (variance_nonneg e' μ),
    mul_nonneg (variance_nonneg x μ) (variance_nonneg e' μ),
    mul_nonneg (variance_nonneg e μ) (variance_nonneg v μ)]

/-- **Two mismeasured covariates, corrected form of Equation 10.12** (after Armstrong et al.
1989). Under `TwoCovariateError` with nondegenerate true covariates
(`Cov(x, v)² < Var(x) Var(v)`), the coefficient `β'` of `m` in the regression of `y` on
`(m, w)` is
`β' = κ β_{x|v} + τ β_x`, where `β_{x|v}` is the coefficient of `x` in the regression of `y` on
`(x, v)`, `β_x` is the crude slope of `y` on `x`, `D = Var(m) Var(w) - Cov(x, v)²`,
`κ = (Var(x) Var(v) - Cov(x, v)²) / D` and `τ = Var(x) Var(e') / D`. The printed
Equation 10.12 has the weights `(σ²_{x|v} / σ²_{m|w}) (σ²_{v|x} / σ²_{w|m})` and
`1 - σ²_{v|x} / σ²_{w|m}` instead, and it fails in a model satisfying every hypothesis
(`Examples.printed_equations_10_12_10_13_fail`). -/
theorem coef2_surrogate (h : TwoCovariateError μ x v e e' y)
    (hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) :
    coef2 μ (x + e) (v + e') y =
      (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
          (Var[x + e; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2) * coef2 μ x v y +
        Var[x; μ] * Var[e'; μ] / (Var[x + e; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2) *
          slope μ x y := by
  have hD := h.det_pos hdet
  rw [h.cov_m_w] at hD
  have ha : Var[x; μ] ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdet; linarith [sq_nonneg cov[x, v; μ]]
  rw [coef2, coef2, slope, h.cov_m_w, h.cov_m_y, h.cov_w_y]
  rw [h.var_m, h.var_w] at hD ⊢
  exact two_covariate_algebra (by linarith) ha hD.ne'

/-- **Corrected form of Equation 10.13.** Solving `coef2_surrogate` for the true adjusted
coefficient: `β_{x|v} = (β' - τ β_x) / κ`, with `κ` and `τ` as in `coef2_surrogate`. The printed
Equation 10.13 is the exact rearrangement of the printed Equation 10.12, so it inherits its
error. -/
theorem coef2_eq_correction (h : TwoCovariateError μ x v e e' y)
    (hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) :
    coef2 μ x v y =
      (coef2 μ (x + e) (v + e') y -
          Var[x; μ] * Var[e'; μ] / (Var[x + e; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2) *
            slope μ x y) /
        ((Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
          (Var[x + e; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2)) := by
  have hD := h.det_pos hdet
  rw [h.cov_m_w] at hD
  rw [h.coef2_surrogate hdet, add_sub_cancel_right, mul_div_cancel_left₀]
  exact div_ne_zero (by linarith) hD.ne'

/-- **Moment correction from observed quantities.** Under `TwoCovariateError` the true
adjusted coefficient is computed from the moments of the surrogates `m = x + e`, `w = v + e'`
and the outcome, and the two error variances `s = Var(e)`, `t = Var(e')`: it is the first
entry of `(Cov(m, w) - diag(s, t))⁻¹ Cov((m, w), y)`,
`β_{x|v} = ((Var(w) - t) Cov(m, y) - Cov(m, w) Cov(w, y))
  / ((Var(m) - s)(Var(w) - t) - Cov(m, w)²)`.
The corrected determinant is that of the true covariates, nonzero under `hdet`. -/
theorem coef2_eq_moment_correction (h : TwoCovariateError μ x v e e' y)
    (_hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) :
    coef2 μ x v y =
      ((Var[v + e'; μ] - Var[e'; μ]) * cov[x + e, y; μ] -
          cov[x + e, v + e'; μ] * cov[v + e', y; μ]) /
        ((Var[x + e; μ] - Var[e; μ]) * (Var[v + e'; μ] - Var[e'; μ]) -
          cov[x + e, v + e'; μ] ^ 2) := by
  rw [h.var_m, h.var_w, h.cov_m_w, h.cov_m_y, h.cov_w_y, add_sub_cancel_right,
    add_sub_cancel_right, coef2]

/-- **Only the exposure is mismeasured** (`Var(e') = 0`, for example `w = v`). Then
`β' = κ β_{x|v}` with `κ = (Var(x) Var(v) - Cov(x, v)²) / (Var(m) Var(v) - Cov(x, v)²)`, the
reliability of `m` conditional on `v` (`σ²_{x|v} / σ²_{m|v}`); this is Equation 10.8
conditional on the confounder, as the book says, and `0 < κ ≤ 1`. -/
theorem coef2_surrogate_of_var_e'_eq_zero (h : TwoCovariateError μ x v e e' y)
    (hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) (he' : Var[e'; μ] = 0) :
    coef2 μ (x + e) (v + e') y =
        (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
          (Var[x + e; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) * coef2 μ x v y ∧
      0 < (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
          (Var[x + e; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) ∧
      (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
          (Var[x + e; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) ≤ 1 := by
  have hD := h.det_pos hdet
  rw [h.cov_m_w, h.var_w, he', add_zero] at hD
  have hv := variance_nonneg v μ
  have hee := variance_nonneg e μ
  have hle : Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2 ≤
      Var[x + e; μ] * Var[v; μ] - cov[x, v; μ] ^ 2 := by
    rw [h.var_m]; nlinarith
  refine ⟨?_, div_pos (by linarith) hD, (div_le_one hD).2 hle⟩
  rw [h.coef2_surrogate hdet, h.var_w, he', add_zero, mul_zero, zero_div, zero_mul, add_zero]

/-- **Only the confounder is mismeasured** (`Var(e) = 0`, for example `m = x`). Then
`β' = ρ β_{x|v} + (1 - ρ) β_x` with
`ρ = (Var(x) Var(v) - Cov(x, v)²) / (Var(x) Var(w) - Cov(x, v)²)` (that is
`σ²_{v|x} / σ²_{w|x}`), and `0 < ρ ≤ 1`: the estimate is a convex combination of the adjusted
and the crude slope. This is the printed special case after Equation 10.13 (with
`σ²_{w|m} = σ²_{w|x}` since `m = x`). -/
theorem coef2_surrogate_of_var_e_eq_zero (h : TwoCovariateError μ x v e e' y)
    (hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) (he : Var[e; μ] = 0) :
    coef2 μ (x + e) (v + e') y =
        (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
            (Var[x; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2) * coef2 μ x v y +
          (1 - (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
            (Var[x; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2)) * slope μ x y ∧
      0 < (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
          (Var[x; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2) ∧
      (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
          (Var[x; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2) ≤ 1 := by
  have hD := h.det_pos hdet
  rw [h.cov_m_w, h.var_m, he, add_zero] at hD
  have hx := variance_nonneg x μ
  have hee := variance_nonneg e' μ
  have hle : Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2 ≤
      Var[x; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2 := by
    rw [h.var_w]; nlinarith
  refine ⟨?_, div_pos (by linarith) hD, (div_le_one hD).2 hle⟩
  rw [h.coef2_surrogate hdet, h.var_m, he, add_zero]
  congr 1
  rw [h.var_w] at hD ⊢
  field_simp
  ring

/-- In the case `Var(e) = 0` the estimate lies between the crude slope `β_x` and the adjusted
coefficient `β_{x|v}` (the claim of the section "Regression Calibration" for a mismeasured
confounder). -/
theorem coef2_surrogate_mem_uIcc_of_var_e_eq_zero (h : TwoCovariateError μ x v e e' y)
    (hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) (he : Var[e; μ] = 0) :
    coef2 μ (x + e) (v + e') y ∈ Set.uIcc (coef2 μ x v y) (slope μ x y) := by
  obtain ⟨heq, hpos, hle⟩ := h.coef2_surrogate_of_var_e_eq_zero hdet he
  rw [heq]
  set ρ := (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
    (Var[x; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2)
  rcases le_total (coef2 μ x v y) (slope μ x y) with hab | hab
  · rw [Set.uIcc_of_le hab]
    constructor <;> nlinarith
  · rw [Set.uIcc_of_ge hab]
    constructor <;> nlinarith

/-- The weight `κ` of `coef2_surrogate` in residual-variance notation:
`κ = (σ²_{x|v} / σ²_{m|w}) (σ²_v / σ²_w)`. The printed Equations 10.12 and 10.13 both have
`σ²_{v|x} / σ²_{w|m}` in place of the second factor `σ²_v / σ²_w`. -/
theorem kappa_eq_resVar (h : TwoCovariateError μ x v e e' y)
    (hdet : cov[x, v; μ] ^ 2 < Var[x; μ] * Var[v; μ]) :
    (Var[x; μ] * Var[v; μ] - cov[x, v; μ] ^ 2) /
        (Var[x + e; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2) =
      resVar μ x v / resVar μ (x + e) (v + e') * (Var[v; μ] / Var[v + e'; μ]) := by
  have hD := h.det_pos hdet
  rw [h.cov_m_w] at hD
  have hv : Var[v; μ] ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hdet; linarith [sq_nonneg cov[x, v; μ]]
  have hw : Var[v + e'; μ] ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hD; linarith [sq_nonneg cov[x, v; μ]]
  have hD' : Var[x + e; μ] - cov[x, v; μ] ^ 2 / Var[v + e'; μ] ≠ 0 := by
    intro h0
    have : Var[x + e; μ] * Var[v + e'; μ] - cov[x, v; μ] ^ 2 = 0 := by
      field_simp at h0; linarith
    linarith
  rw [resVar, resVar, h.cov_m_w]
  field_simp

end TwoCovariateError

/-! ### Bridge to the regression coefficients of `LinearSEM.Regression` -/

/-- The covariance matrix `(Cov(f i, f j))_{i j}` of a finite family of random variables. -/
noncomputable def covMatrix (μ : Measure Ω) {ι : Type*} (f : ι → Ω → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j ↦ cov[f i, f j; μ]

/-- `slope` is the regression coefficient of `LinearSEM.Regression`: for `X` almost everywhere
measurable with `Var(X) ≠ 0`, `slope μ X Y` is the coefficient of `X` in the population
regression of `Y` on `X` for the covariance matrix of `(X, Y)`. -/
theorem isRegCoeff_slope {X Y : Ω → ℝ} (hX : AEMeasurable X μ) (hV : Var[X; μ] ≠ 0) :
    IsRegCoeff (covMatrix μ ![X, Y]) {0} 1 (Pi.single 0 (slope μ X Y)) := by
  have h00 : covMatrix μ ![X, Y] 0 0 = Var[X; μ] := by
    simp [covMatrix, covariance_self hX]
  have h01 : covMatrix μ ![X, Y] 0 1 = cov[X, Y; μ] := by simp [covMatrix]
  rw [isRegCoeff_singleton_iff (by rw [h00]; exact hV), h01, h00]
  rfl

/-- `coef2` is the regression coefficient of `LinearSEM.Regression`: for almost everywhere
measurable `X`, `W` with `Var(X) Var(W) - Cov(X, W)² ≠ 0`, the vector
`(coef2 X W Y, coef2 W X Y, 0)` is the coefficient vector of the population regression of `Y` on
`(X, W)` for the covariance matrix of `(X, W, Y)`. -/
theorem isRegCoeff_coef2 {X W Y : Ω → ℝ} (hX : AEMeasurable X μ) (hW : AEMeasurable W μ)
    (hD : Var[X; μ] * Var[W; μ] - cov[X, W; μ] ^ 2 ≠ 0) :
    IsRegCoeff (covMatrix μ ![X, W, Y]) {0, 1} 2 ![coef2 μ X W Y, coef2 μ W X Y, 0] := by
  have h00 : covMatrix μ ![X, W, Y] 0 0 = Var[X; μ] := by simp [covMatrix, covariance_self hX]
  have h11 : covMatrix μ ![X, W, Y] 1 1 = Var[W; μ] := by simp [covMatrix, covariance_self hW]
  have h01 : covMatrix μ ![X, W, Y] 0 1 = cov[X, W; μ] := by simp [covMatrix]
  have h10 : covMatrix μ ![X, W, Y] 1 0 = cov[X, W; μ] := by
    simp [covMatrix, covariance_comm W X]
  have h02 : covMatrix μ ![X, W, Y] 0 2 = cov[X, Y; μ] := by simp [covMatrix]
  have h12 : covMatrix μ ![X, W, Y] 1 2 = cov[W, Y; μ] := by simp [covMatrix]
  rw [isRegCoeff_pair_iff (by decide) (by rw [h10, h01]) (by rw [h00, h11, h01]; exact hD),
    h00, h11, h01, h02, h12]
  refine ⟨fun v hv ↦ ?_, by simp [coef2], ?_⟩
  · fin_cases v <;> simp_all
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, coef2, covariance_comm W X]
    rw [mul_comm (Var[W; μ])]

/-! ### Examples and counterexamples -/

namespace Examples

open LinearIVExample IVModel

/-- **Attenuation values of Figure 10.2.** With `r = σ_e / σ_x`: `r = 1/10` gives
`λ = 100/101`, between `0.99` and `0.991` (printed `0.99`); `r = 1/3` gives `λ = 9/10`
(printed `0.90`; the height example with `σ_x = 3` inches and `σ_e = 1` inch); `r = 1` gives
`λ = 1/2` (printed `0.50`). -/
theorem attenuation_values :
    (1 : ℝ) / (1 + (1 / 10) ^ 2) = 100 / 101 ∧ (0.99 : ℝ) < 100 / 101 ∧
      (100 : ℝ) / 101 < 0.991 ∧ (1 : ℝ) / (1 + (1 / 3) ^ 2) = 9 / 10 ∧
      (3 : ℝ) ^ 2 / (3 ^ 2 + 1 ^ 2) = 9 / 10 ∧ (1 : ℝ) / (1 + 1 ^ 2) = 1 / 2 := by
  norm_num

/-- **Counterexample: differential error is not attenuated.** On two fair coins let `x` and
`e` be the two coins (coded `0`/`1`) and `y = e`. Then `Cov(x, e) = 0` but `Cov(e, y) ≠ 0`, so
the classical model fails only through the nondifferential condition. The true slope is `0`
and the surrogate slope is `1/2`: the error moves the slope away from the null. -/
theorem differential_not_attenuated :
    cov[fun ω ↦ boolToReal ω.1, fun ω ↦ boolToReal ω.2; coins] = 0 ∧
      cov[fun ω ↦ boolToReal ω.2, fun ω ↦ boolToReal ω.2; coins] ≠ 0 ∧
      slope coins (fun ω ↦ boolToReal ω.1) (fun ω ↦ boolToReal ω.2) = 0 ∧
      slope coins ((fun ω ↦ boolToReal ω.1) + fun ω ↦ boolToReal ω.2)
        (fun ω ↦ boolToReal ω.2) = 1 / 2 := by
  simp only [slope, ← covariance_self (measurable_of_countable _).aemeasurable, covariance,
    integral_coins, Pi.add_apply, boolToReal]
  norm_num

/-- Four independent fair coins: the uniform distribution on `Bool × Bool × Bool × Bool`. -/
noncomputable def coins4 : Measure (Bool × Bool × Bool × Bool) := uniformOn Set.univ

instance : IsProbabilityMeasure coins4 := by unfold coins4; infer_instance

theorem integral_coins4 (f : Bool × Bool × Bool × Bool → ℝ) :
    ∫ ω, f ω ∂coins4 = (∑ ω, f ω) / 16 := by
  rw [coins4, integral_fintype .of_finite]
  simp [uniformOn_univ, measureReal_def, div_eq_inv_mul, Finset.mul_sum]

theorem memLp_coins4 (g : Bool × Bool × Bool × Bool → Bool) :
    MemLp (fun ω ↦ boolToReal (g ω)) 2 coins4 :=
  MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    (ae_of_all _ fun ω ↦ by cases g ω <;> norm_num [boolToReal])

/-- True exposure of the four-coin model: the first coin. -/
noncomputable def x4 (ω : Bool × Bool × Bool × Bool) : ℝ := boolToReal ω.1

/-- True confounder of the four-coin model: the sum of the first two coins, so
`Cov(x, v) = 1/4 ≠ 0`. -/
noncomputable def v4 (ω : Bool × Bool × Bool × Bool) : ℝ := boolToReal ω.1 + boolToReal ω.2.1

/-- Exposure error of the four-coin model: the third coin. -/
noncomputable def e4 (ω : Bool × Bool × Bool × Bool) : ℝ := boolToReal ω.2.2.1

/-- Confounder error of the four-coin model: the fourth coin. -/
noncomputable def e4' (ω : Bool × Bool × Bool × Bool) : ℝ := boolToReal ω.2.2.2

/-- The four-coin model with outcome `y = x` satisfies `TwoCovariateError`. -/
theorem two_covariate_assumptions : TwoCovariateError coins4 x4 v4 e4 e4' x4 := by
  refine ⟨memLp_coins4 _, (memLp_coins4 _).add (memLp_coins4 _), memLp_coins4 _,
    memLp_coins4 _, memLp_coins4 _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [covariance, integral_coins4, x4, v4, e4, e4', boolToReal, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num

/-- **Counterexample: with both covariates mismeasured the estimate need not lie between the
crude and the adjusted value**, contrary to the text before Equation 10.12. In the four-coin
model (`x` the first coin, `v` the sum of the first two, `e` and `e'` the last two, `y = x`;
`two_covariate_assumptions` checks the hypotheses), the adjusted coefficient `β_{x|v}` and the
crude slope on the true exposure are both `1`, the crude slope on the surrogate `m` is `1/2`,
and the coefficient of `m` in the regression of `y` on `(m, w)` is `2/5`, outside the interval
between the crude and the adjusted value under either reading of the crude estimate. Here the
confounder has adjusted coefficient `0`; `two_covariate_confounded_not_between` is a version
with genuine confounding. -/
theorem two_covariate_not_between :
    coef2 coins4 x4 v4 x4 = 1 ∧ slope coins4 x4 x4 = 1 ∧ slope coins4 (x4 + e4) x4 = 1 / 2 ∧
      coef2 coins4 (x4 + e4) (v4 + e4') x4 = 2 / 5 := by
  simp only [coef2, slope, ← covariance_self (measurable_of_countable _).aemeasurable,
    covariance, integral_coins4, Pi.add_apply, x4, v4, e4, e4', boolToReal,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- **Printed error in Equations 10.12 and 10.13.** As printed (pages 347 and 348 of the
book), Equation 10.12 reads
`β' = (σ²_{x|v} / σ²_{m|w}) (σ²_{v|x} / σ²_{w|m}) β_{x|v} + (1 - σ²_{v|x} / σ²_{w|m}) β_x`
and Equation 10.13 is its exact rearrangement
`β_{x|v} = [β' - (1 - σ²_{v|x} / σ²_{w|m}) β_x] / [(σ²_{x|v} / σ²_{m|w}) (σ²_{v|x} / σ²_{w|m})]`.
In the four-coin model (every hypothesis of `TwoCovariateError` holds,
`two_covariate_assumptions`) the coefficient of `m` is `2/5` (`two_covariate_not_between`),
which `coef2_surrogate` reproduces, but the printed right side of Equation 10.12 equals `18/25`;
and the printed Equation 10.13 applied to the true `β' = 2/5` returns `-5/3`, not the true
`β_{x|v} = 1`. Here `β_x` is the crude slope on `x`. -/
theorem printed_equations_10_12_10_13_fail :
    resVar coins4 x4 v4 / resVar coins4 (x4 + e4) (v4 + e4') *
          (resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4)) * coef2 coins4 x4 v4 x4 +
        (1 - resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4)) * slope coins4 x4 x4 =
      18 / 25 ∧
    (coef2 coins4 (x4 + e4) (v4 + e4') x4 -
          (1 - resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4)) * slope coins4 x4 x4) /
        (resVar coins4 x4 v4 / resVar coins4 (x4 + e4) (v4 + e4') *
          (resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4))) = -5 / 3 := by
  simp only [coef2, slope, resVar, ← covariance_self (measurable_of_countable _).aemeasurable,
    covariance, integral_coins4, Pi.add_apply, x4, v4, e4, e4', boolToReal,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- A variant of Equation 10.12 that the printed book does not contain: the first weight with
the unconditional `σ²_v` in place of `σ²_{v|x}`,
`(σ²_{x|v} / σ²_{m|w}) (σ²_v / σ²_{w|m}) β_{x|v} + (1 - σ²_{v|x} / σ²_{w|m}) β_x`. It also fails
in the four-coin model: it equals `21/25`, not `2/5`. -/
theorem variant_equation_10_12_fails :
    resVar coins4 x4 v4 / resVar coins4 (x4 + e4) (v4 + e4') *
          (Var[v4; coins4] / resVar coins4 (v4 + e4') (x4 + e4)) * coef2 coins4 x4 v4 x4 +
        (1 - resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4)) * slope coins4 x4 x4 =
      21 / 25 := by
  simp only [coef2, slope, resVar, ← covariance_self (measurable_of_countable _).aemeasurable,
    covariance, integral_coins4, Pi.add_apply, x4, v4, e4, e4', boolToReal,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- Outcome of the confounded four-coin model: `y = x + 2 v`, so the confounder `v` has
adjusted coefficient `2`. -/
noncomputable def y4c (ω : Bool × Bool × Bool × Bool) : ℝ := x4 ω + 2 * v4 ω

/-- The confounded four-coin model satisfies `TwoCovariateError`. -/
theorem two_covariate_confounded_assumptions : TwoCovariateError coins4 x4 v4 e4 e4' y4c := by
  refine ⟨memLp_coins4 _, (memLp_coins4 _).add (memLp_coins4 _), memLp_coins4 _,
    memLp_coins4 _, (memLp_coins4 _).add (((memLp_coins4 _).add (memLp_coins4 _)).const_mul 2),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [covariance, integral_coins4, x4, v4, e4, e4', y4c, boolToReal,
      Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num

/-- **Counterexample with genuine confounding: with both covariates mismeasured the estimate
need not lie between the crude and the adjusted value**, contrary to the text before
Equation 10.12. In the four-coin model with outcome `y = x + 2 v` (hypotheses checked in
`two_covariate_confounded_assumptions`) the confounder matters: its adjusted coefficient is `2`
and the crude slope on `x` is `3`, while the adjusted coefficient of `x` is `1`. The crude slope
on the surrogate `m` is `3/2`, and the coefficient of `m` in the regression of `y` on `(m, w)`
is `4/5`, below both the adjusted value `1` and either reading of the crude value. -/
theorem two_covariate_confounded_not_between :
    coef2 coins4 x4 v4 y4c = 1 ∧ coef2 coins4 v4 x4 y4c = 2 ∧ slope coins4 x4 y4c = 3 ∧
      slope coins4 (x4 + e4) y4c = 3 / 2 ∧ coef2 coins4 (x4 + e4) (v4 + e4') y4c = 4 / 5 := by
  simp only [coef2, slope, ← covariance_self (measurable_of_countable _).aemeasurable,
    covariance, integral_coins4, Pi.add_apply, x4, v4, e4, e4', y4c, boolToReal,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- The first of two fair coins, coded `0`/`1`. -/
noncomputable def coinM (ω : Bool × Bool) : ℝ := boolToReal ω.1

/-- The second of two fair coins, coded `0`/`1`. -/
noncomputable def coinE (ω : Bool × Bool) : ℝ := boolToReal ω.2

/-- **Counterexample: the Berkson coefficient need not be the slope on the true exposure.** On
two fair coins let `m` and `e` be the coins, `x = m + e`, `u = e` and `y = x + u`. The
hypotheses of `slope_berkson` hold (`Cov(m, e) = 0` and, since `u = e`, `Cov(m, u) = 0`), and
the slope of `y` on `m` is the decomposition coefficient `1`, but the slope of `y` on the true
exposure `x` is `3/2`: the residual `u` is correlated with `x`, which
`slope_berkson_eq_slope_true` excludes. -/
theorem berkson_coefficient_ne_true_slope :
    cov[coinM, coinE; coins] = 0 ∧
      slope coins coinM (fun ω ↦ 0 + 1 * (coinM + coinE) ω + coinE ω) = 1 ∧
      slope coins (coinM + coinE) (fun ω ↦ 0 + 1 * (coinM + coinE) ω + coinE ω) = 3 / 2 := by
  simp only [slope, ← covariance_self (measurable_of_countable _).aemeasurable, covariance,
    integral_coins, Pi.add_apply, coinM, coinE, boolToReal]
  norm_num

end Examples

end CausalInference.BiasAnalysis.MeasurementError
