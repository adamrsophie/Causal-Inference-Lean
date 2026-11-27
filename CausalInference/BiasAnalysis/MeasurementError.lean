/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.InstrumentalVariables.LinearIV
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Measurement error for continuous variables

Linear measurement error models of Fox, MacLehose and Lash (2021), *Applying Quantitative Bias
Analysis to Epidemiologic Data*, second edition, Chapter 10, sections "Classical and Berkson
Measurement Error for Continuous Exposures" and "Regression Calibration" (Equations 10.7 to
10.13 and 10.17 to 10.19). All variables are square integrable real random variables on a
probability space and every regression is a population least squares projection, written with
Mathlib's `covariance` and `variance`. The results are exact for these linear projections; the
book applies them to log-linear, logistic and proportional hazards models, where they hold
only approximately.

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
* `slope_surrogate_eq_mul_calibration`, `beta_eq_div_calibration`: regression calibration,
  `β = β' / γ`; `calibration_classical` (`γ = λ`), `calibration_berkson` (`γ = 1`),
  `slope_berkson` (Berkson error does not attenuate), `slope_classical_linear`;
  `calibration_delta_variance`: Equation 10.10 as a first-order variance.
* `slope_outcome_error`, `slope_outcome_error_differential`: error in a continuous outcome
  leaves the slope unchanged (Equation 10.17) or adds `δ` (Equation 10.19).
* `TwoCovariateError.coef2_surrogate`, `TwoCovariateError.coef2_eq_correction`: the
  two-covariate formula and its inversion, stated correctly (Equations 10.12 and 10.13 as
  printed are not identities; see `Examples.printed_equations_10_12_10_13_fail`), with the
  two printed special cases `coef2_surrogate_of_var_e'_eq_zero` and
  `coef2_surrogate_of_var_e_eq_zero`.
* Counterexamples: `Examples.differential_not_attenuated` (correlated error and outcome move
  the slope away from the null) and `Examples.two_covariate_not_between` (with both covariates
  mismeasured the estimate need not lie between the crude and the adjusted value).
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

theorem reliability_pos {x e : Ω → ℝ} (hx : 0 < Var[x; μ]) : 0 < reliability μ x e :=
  div_pos hx (by linarith [variance_nonneg e μ])

theorem reliability_le_one {x e : Ω → ℝ} (hx : 0 < Var[x; μ]) : reliability μ x e ≤ 1 :=
  (div_le_one (by linarith [variance_nonneg e μ])).2 (by linarith [variance_nonneg e μ])

/-- The reliability ratio is strictly below one exactly when the error has positive variance. -/
theorem reliability_lt_one_iff {x e : Ω → ℝ} (hx : 0 < Var[x; μ]) :
    reliability μ x e < 1 ↔ 0 < Var[e; μ] := by
  rw [reliability, div_lt_one (by linarith [variance_nonneg e μ])]
  constructor <;> intro h <;> linarith

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
  rw [h.slope_surrogate hx, mul_div_cancel_left₀ _ (reliability_pos hx).ne']

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
  rw [h.slope_surrogate hx, abs_mul, abs_of_pos (reliability_pos hx)]
  exact mul_le_of_le_one_left (abs_nonneg _) (reliability_le_one hx)

/-- **Strict attenuation.** Under the classical error model, `|β'| < |β|` if and only if the
error has positive variance and the true slope is nonzero. -/
theorem abs_slope_surrogate_lt_iff (h : ClassicalError μ x e y) (hx : 0 < Var[x; μ]) :
    |slope μ (x + e) y| < |slope μ x y| ↔ 0 < Var[e; μ] ∧ slope μ x y ≠ 0 := by
  rw [h.slope_surrogate hx, abs_mul, abs_of_pos (reliability_pos hx),
    ← reliability_lt_one_iff hx]
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

/-- **Berkson error does not attenuate** (section "Classical and Berkson Measurement Error",
`β' = β`). Let the true exposure be `x = m + e` with `Cov(m, e) = 0`, the outcome
`y = α + β x + u` with `Cov(m, u) = 0`, and `Var(m) ≠ 0`. Then the slope of `y` on the assigned
value `m` is `β`. Exact for the linear model; the book states it for log-linear risk models. -/
theorem slope_berkson [IsProbabilityMeasure μ] {m e u : Ω → ℝ} (α β : ℝ) (hm : MemLp m 2 μ)
    (he : MemLp e 2 μ) (hu : MemLp u 2 μ) (hme : cov[m, e; μ] = 0) (hmu : cov[m, u; μ] = 0)
    (hV : Var[m; μ] ≠ 0) :
    slope μ m (fun ω ↦ α + β * (m + e) ω + u ω) = β := by
  rw [slope_surrogate_eq_mul_calibration α β hm (hm.add he) hu hmu hV,
    calibration_berkson hm he hme hV, mul_one]

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

/-- `coef2` solves the normal equations: with `b = coef2 X W Y` and `c = coef2 W X Y`,
`Cov(X, Y) = b Var(X) + c Cov(X, W)` and `Cov(W, Y) = b Cov(X, W) + c Var(W)`, so the residual
`Y - b X - c W` is uncorrelated with `X` and `W`. -/
theorem coef2_normal_equations {X W Y : Ω → ℝ}
    (hD : Var[X; μ] * Var[W; μ] - cov[X, W; μ] ^ 2 ≠ 0) :
    cov[X, Y; μ] = coef2 μ X W Y * Var[X; μ] + coef2 μ W X Y * cov[X, W; μ] ∧
      cov[W, Y; μ] = coef2 μ X W Y * cov[X, W; μ] + coef2 μ W X Y * Var[W; μ] := by
  have hD' : Var[W; μ] * Var[X; μ] - cov[W, X; μ] ^ 2 ≠ 0 := by
    rw [covariance_comm W X, mul_comm]; exact hD
  unfold coef2
  rw [covariance_comm W X] at hD' ⊢
  constructor <;> field_simp <;> ring

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
Equation 10.12 has different weights (see `Examples.printed_equations_10_12_10_13_fail`). -/
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
coefficient: `β_{x|v} = (β' - τ β_x) / κ`, with `κ` and `τ` as in `coef2_surrogate`. -/
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
`κ = (σ²_{x|v} / σ²_{m|w}) (σ²_v / σ²_w)`. The printed Equation 10.12 has `σ²_{w|m}` where this
has the unconditional `σ²_w`, and Equation 10.13 has `σ²_{v|x} / σ²_{w|m}`. -/
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
between the crude and the adjusted value under either reading of the crude estimate. -/
theorem two_covariate_not_between :
    coef2 coins4 x4 v4 x4 = 1 ∧ slope coins4 x4 x4 = 1 ∧ slope coins4 (x4 + e4) x4 = 1 / 2 ∧
      coef2 coins4 (x4 + e4) (v4 + e4') x4 = 2 / 5 := by
  simp only [coef2, slope, ← covariance_self (measurable_of_countable _).aemeasurable,
    covariance, integral_coins4, Pi.add_apply, x4, v4, e4, e4', boolToReal,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

/-- **Printed error in Equations 10.12 and 10.13.** In the four-coin model the coefficient of
`m` is `2/5` (`two_covariate_not_between`), which `coef2_surrogate` reproduces, but the printed
right side of Equation 10.12,
`(σ²_{x|v} / σ²_{m|w}) (σ²_v / σ²_{w|m}) β_{x|v} + (1 - σ²_{v|x} / σ²_{w|m}) β_x`, equals
`21/25`, and the variant with `σ²_{v|x}` in place of `σ²_v` (the weight of Equation 10.13)
equals `18/25`. Here `β_x` is the crude slope on `x`; with the crude slope on `m` (`1/2`) the
two values would be `27/50` and `21/50`, also not `2/5`. -/
theorem printed_equations_10_12_10_13_fail :
    resVar coins4 x4 v4 / resVar coins4 (x4 + e4) (v4 + e4') *
          (Var[v4; coins4] / resVar coins4 (v4 + e4') (x4 + e4)) * coef2 coins4 x4 v4 x4 +
        (1 - resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4)) * slope coins4 x4 x4 =
      21 / 25 ∧
    resVar coins4 x4 v4 / resVar coins4 (x4 + e4) (v4 + e4') *
          (resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4)) * coef2 coins4 x4 v4 x4 +
        (1 - resVar coins4 v4 x4 / resVar coins4 (v4 + e4') (x4 + e4)) * slope coins4 x4 x4 =
      18 / 25 := by
  simp only [coef2, slope, resVar, ← covariance_self (measurable_of_countable _).aemeasurable,
    covariance, integral_coins4, Pi.add_apply, x4, v4, e4, e4', boolToReal,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

end Examples

end CausalInference.BiasAnalysis.MeasurementError
