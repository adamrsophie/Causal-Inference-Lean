/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.CondVar
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import CausalInference.Mediation.Basic

/-!
# Trial-level surrogate endpoints: criteria, parameter relations, single mapping

Let `δ₁`, `δ₂` be the true treatment effects on a surrogate endpoint and on the final outcome,
viewed as random variables across studies. NICE DSU Technical Support Document 20 evaluates a
surrogate by the trial-level regression of `δ₂` on `δ₁`.

## Setting and hypotheses

TSD 20 assumes a bivariate normal law for `(δ₁, δ₂)` (the standard form of the bivariate
random-effects meta-analysis, Section 2.1, equation (2)) or, equivalently, the product normal
formulation `δ₂ | δ₁ ~ N(λ₀ + λ₁ δ₁, ψ₂²)` (Section 2.2, equation (5); the model of Daniels and
Hughes, Section 3.2, equation (7), has the same second line with `δ₁` a fixed effect). Mathlib
has no Gaussian conditioning, and the results below need only moments, so the product normal
formulation is replaced by its moment consequences (`PNFMoments`): the residual
`δ₂ - (λ₀ + λ₁ δ₁)` has mean zero, is uncorrelated with `δ₁`, and has variance `ψ₂²`. These are
least squares moments: `ψ₂²` is a residual variance, which TSD 20 calls the conditional variance.
The conditional moments imply the least squares ones (`pnfMoments_of_condMoments`), not
conversely (`Countermodel.residVar_ne_condVar`). Every theorem therefore holds in the Gaussian
model and in every other model with these moments.

## Main definitions

* `SurrogacyCriteria λ₀ λ₁ ψ₂²`: the criteria of Daniels and Hughes as named in TSD 20,
  Section 3.2: `λ₀ = 0`, `λ₁ ≠ 0`, `ψ₂² = 0`.
* `PNFMoments μ δ₁ δ₂ λ₀ λ₁ ψ₂²`: the moment form of the product normal formulation.
* `PrenticeCriteria P μ`: the four operational criteria of Prentice (1989), mentioned in TSD 20,
  Section 3.1.2, in mean form for a trial with binary treatment and binary surrogate described
  by a `Mediation.MediationModel`, under a probability law with integrable outcome and positive
  probability of every treatment by surrogate cell. Full capture is `MeanFullCapture`;
  `DistFullCapture` is the distributional form (the outcome is independent of the treatment
  given the surrogate). Countermodels showing that the criteria neither imply nor follow from a
  zero natural direct effect, that the mean form does not imply the distributional form, and
  that a null cell can decide the mean form are in `Surrogacy.Counterexamples`.

## Main results

* `PNFMoments.ae_eq_of_residVar_eq_zero`: perfect prediction. If `ψ₂² = 0` then
  `δ₂ = λ₀ + λ₁ δ₁` almost surely.
* `PNFMoments.null_preservation`: under the three criteria, almost surely `δ₂ = λ₁ δ₁` and
  `δ₁ = 0 ↔ δ₂ = 0`: no effect on the surrogate means no effect on the final outcome, and
  conversely. `PNFMoments.null_preservation_forward`: zero intercept and zero residual variance
  alone give `δ₂ = λ₁ δ₁` and `δ₁ = 0 → δ₂ = 0` almost surely. Countermodels in which exactly
  one criterion fails: `Countermodel.intercept_ne_zero`, `Countermodel.condVar_pos`,
  `Countermodel.slope_eq_zero`.
* `PNFMoments.slope_eq`, `PNFMoments.intercept_eq`, `PNFMoments.residVar_eq`: the parameter
  relations of equation (6) and equation (10), `λ₁ = cov(δ₁, δ₂) / var δ₁`,
  `λ₀ = d₂ - λ₁ d₁`, `ψ₂² = τ₂² - λ₁² τ₁²`. Equation (10) is printed with the justification
  `λ₁ = (d₂ - λ₀) / d₁`, which needs `d₁ ≠ 0`; the relation itself holds without it.
* `covariance_sub_slope_mul`, `variance_sub_slope_mul`: the residual of the least squares slope
  is uncorrelated with `δ₁` and has variance `var δ₂ - cov(δ₁, δ₂)² / var δ₁` (the residual
  variance identity); `pnfMoments_slope` builds the moment form from any square integrable
  pair, so these parameters always exist.
* `PNFMoments.slope_eq_corr`, `PNFMoments.residVar_eq_corr`, `PNFMoments.intercept_eq_corr`:
  equations (8), (9) and (10) in the correlation parameterization, `λ₁ = ρ τ₂ / τ₁`,
  `ψ₂² = τ₂² (1 - ρ²)` and `λ₀ = d₂ - d₁ ρ τ₂ / τ₁`.
* `PNFMoments.residVar_eq_zero_iff_corr`: `ψ₂² = 0 ↔ ρ² = 1` when `τ₂ ≠ 0` (perfect affine
  prediction is perfect correlation, Sections 3.4 and 3.5);
  `PNFMoments.surrogacyCriteria_iff_corr`: the three criteria hold if and only if `ρ² = 1` and
  `λ₀ = 0`; `PNFMoments.rSq_eq_corr`: `1 - ψ₂² / τ₂² = ρ²`, the trial-level `R²`. The printed
  claim "from (9), `ψ₂² = 0` implies `ρ = ±1`" needs `τ₂ > 0`, which TSD 20 leaves implicit:
  `Countermodel.degenerate_final` is a model with a constant final outcome effect, `ψ₂² = 0`
  and `ρ = 0`.
* `single_mapping`: the single mapping hypothesis of TSD 5, Section 3.1. If the treatment acts
  on the final outcome only through a binary short-term outcome (no direct effect) and the
  short-term outcome is independent of the effect of the short-term outcome on the final one,
  then for every treatment the mean final outcome is the same affine function of the
  probability of the short-term outcome; `single_mapping_sub` is the contrast form. Countermodels
  are in `Surrogacy.Counterexamples`.

## Sources

* NICE DSU Technical Support Document 20: S. Bujkiewicz, F. Achana, T. Papanikos, R. D. Riley
  and K. R. Abrams (2019), Multivariate meta-analysis of summary data for combining treatment
  effects on correlated outcomes and evaluating surrogate endpoints, Sections 2.2, 3.1.2, 3.2
  to 3.5, equations (5) to (10). Section 3.1.2 mentions the Prentice criteria without listing
  them.
* NICE DSU Technical Support Document 5: S. Dias, N. J. Welton, A. J. Sutton and A. E. Ades
  (2011, updated 2012), Evidence synthesis in the baseline natural history model, Section 3.1.
* M. J. Daniels and M. D. Hughes (1997), Meta-analysis for the evaluation of potential
  surrogate markers, Statistics in Medicine 16 (reference [8] of TSD 20).
* R. L. Prentice (1989), Surrogate endpoints in clinical trials: definition and operational
  criteria, Statistics in Medicine 8 (reference [65] of TSD 20). Source of the operational
  criteria in `PrenticeCriteria`.
-/

@[expose] public section

namespace CausalInference

namespace Surrogacy

open MeasureTheory ProbabilityTheory

/-- The surrogacy criteria of Daniels and Hughes as stated in TSD 20, Section 3.2, for the
trial-level regression `δ₂ | δ₁ ~ N(λ₀ + λ₁ δ₁, ψ₂²)`: zero intercept (the fitted effect on the
final outcome is zero at a zero effect on the surrogate), nonzero slope (the effects are related),
and zero conditional variance `ψ₂²` (perfect prediction). In the moment form `PNFMoments` the
parameter `ψ₂²` is the residual variance of the least squares fit; it is the conditional variance
only under the conditional moment hypotheses of `pnfMoments_of_condMoments`. -/
structure SurrogacyCriteria (lam0 lam1 psiSq : ℝ) : Prop where
  intercept_eq_zero : lam0 = 0
  slope_ne_zero : lam1 ≠ 0
  condVar_eq_zero : psiSq = 0

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The moment form of the product normal formulation (TSD 20, Section 2.2, equation (5)):
`δ₁` and `δ₂` are square integrable and the residual `δ₂ - (λ₀ + λ₁ δ₁)` has mean zero, is
uncorrelated with `δ₁`, and has variance `ψ₂²`. These are unconditional least squares moments:
`λ₀ + λ₁ δ₁` is the best affine predictor of `δ₂` and `ψ₂²` is its residual variance. They
follow from `δ₂ | δ₁ ~ N(λ₀ + λ₁ δ₁, ψ₂²)`, and more generally from conditional mean
`λ₀ + λ₁ δ₁` and conditional variance `ψ₂²` (`pnfMoments_of_condMoments`), but they are weaker:
they say nothing about the conditional mean or variance of `δ₂` given `δ₁`
(`Countermodel.residVar_ne_condVar`). -/
structure PNFMoments (μ : Measure Ω) (δ₁ δ₂ : Ω → ℝ) (lam0 lam1 psiSq : ℝ) : Prop where
  memLp_fst : MemLp δ₁ 2 μ
  memLp_snd : MemLp δ₂ 2 μ
  mean_residual : ∫ ω, (δ₂ ω - (lam0 + lam1 * δ₁ ω)) ∂μ = 0
  cov_residual : cov[δ₁, fun ω => δ₂ ω - (lam0 + lam1 * δ₁ ω); μ] = 0
  var_residual : Var[fun ω => δ₂ ω - (lam0 + lam1 * δ₁ ω); μ] = psiSq

namespace PNFMoments

variable [IsProbabilityMeasure μ] {δ₁ δ₂ : Ω → ℝ} {lam0 lam1 psiSq : ℝ}

theorem memLp_residual (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) :
    MemLp (fun ω => δ₂ ω - (lam0 + lam1 * δ₁ ω)) 2 μ :=
  h.memLp_snd.sub ((memLp_const lam0).add (h.memLp_fst.const_mul lam1))

/-- Perfect prediction (TSD 20, Section 3.2): if the residual variance `ψ₂²` is zero, then
`δ₂ = λ₀ + λ₁ δ₁` almost surely. -/
theorem ae_eq_of_residVar_eq_zero (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) (hψ : psiSq = 0) :
    ∀ᵐ ω ∂μ, δ₂ ω = lam0 + lam1 * δ₁ ω := by
  have h0 := ae_eq_integral_of_variance_eq_zero h.memLp_residual (h.var_residual.trans hψ)
  filter_upwards [h0] with ω hω
  rw [h.mean_residual] at hω
  linarith

/-- Null preservation under the surrogacy criteria of Daniels and Hughes (TSD 20, Section 3.2):
if `λ₀ = 0`, `λ₁ ≠ 0` and `ψ₂² = 0`, then almost surely `δ₂ = λ₁ δ₁`, and the treatment has no
effect on the final outcome exactly when it has no effect on the surrogate. -/
theorem null_preservation (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq)
    (hc : SurrogacyCriteria lam0 lam1 psiSq) :
    ∀ᵐ ω ∂μ, δ₂ ω = lam1 * δ₁ ω ∧ (δ₁ ω = 0 ↔ δ₂ ω = 0) := by
  filter_upwards [h.ae_eq_of_residVar_eq_zero hc.condVar_eq_zero] with ω hω
  rw [hc.intercept_eq_zero, zero_add] at hω
  refine ⟨hω, ?_⟩
  rw [hω, mul_eq_zero, or_iff_right hc.slope_ne_zero]

/-- Forward null preservation (TSD 20, Section 3.2): zero intercept and zero residual variance
alone give, almost surely, `δ₂ = λ₁ δ₁`, so no effect on the surrogate means no effect on the
final outcome. No hypothesis on the slope is needed; the nonzero slope of `null_preservation`
serves only the converse. -/
theorem null_preservation_forward (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) (h0 : lam0 = 0)
    (hψ : psiSq = 0) : ∀ᵐ ω ∂μ, δ₂ ω = lam1 * δ₁ ω ∧ (δ₁ ω = 0 → δ₂ ω = 0) := by
  filter_upwards [h.ae_eq_of_residVar_eq_zero hψ] with ω hω
  rw [h0, zero_add] at hω
  exact ⟨hω, fun h1 => by rw [hω, h1, mul_zero]⟩

end PNFMoments

/-! ### Covariance algebra of the residual -/

section Algebra

variable [IsProbabilityMeasure μ] {δ₁ δ₂ : Ω → ℝ}

omit [MeasurableSpace Ω] in
/-- The residual `δ₂ - (λ₀ + λ₁ δ₁)` is the residual `δ₂ - λ₁ δ₁` shifted by the constant
`λ₀`. -/
theorem residual_eq (δ₁ δ₂ : Ω → ℝ) (lam0 lam1 : ℝ) :
    (fun ω => δ₂ ω - (lam0 + lam1 * δ₁ ω)) = fun ω => (δ₂ ω - lam1 * δ₁ ω) - lam0 := by
  funext ω
  ring

/-- The covariance of `δ₁` with the residual: `cov(δ₁, δ₂ - (λ₀ + λ₁ δ₁)) =
cov(δ₁, δ₂) - λ₁ var δ₁`. -/
theorem covariance_residual (h₁ : MemLp δ₁ 2 μ) (h₂ : MemLp δ₂ 2 μ) (lam0 lam1 : ℝ) :
    cov[δ₁, fun ω => δ₂ ω - (lam0 + lam1 * δ₁ ω); μ] =
      cov[δ₁, δ₂; μ] - lam1 * Var[δ₁; μ] := by
  have hm : MemLp (fun ω => δ₂ ω - lam1 * δ₁ ω) 2 μ := h₂.sub (h₁.const_mul lam1)
  rw [residual_eq, covariance_sub_const_right (hm.integrable one_le_two),
    covariance_fun_sub_right h₁ h₂ (h₁.const_mul lam1),
    covariance_const_mul_right, covariance_self h₁.aemeasurable]

/-- The variance of the residual: `var(δ₂ - (λ₀ + λ₁ δ₁)) =
var δ₂ - 2 λ₁ cov(δ₁, δ₂) + λ₁² var δ₁`. -/
theorem variance_residual (h₁ : MemLp δ₁ 2 μ) (h₂ : MemLp δ₂ 2 μ) (lam0 lam1 : ℝ) :
    Var[fun ω => δ₂ ω - (lam0 + lam1 * δ₁ ω); μ] =
      Var[δ₂; μ] - 2 * lam1 * cov[δ₁, δ₂; μ] + lam1 ^ 2 * Var[δ₁; μ] := by
  have hm : MemLp (fun ω => δ₂ ω - lam1 * δ₁ ω) 2 μ := h₂.sub (h₁.const_mul lam1)
  rw [residual_eq, variance_sub_const hm.aestronglyMeasurable,
    variance_fun_sub h₂ (h₁.const_mul lam1), covariance_const_mul_right, variance_const_mul,
    covariance_comm]
  ring

/-- The mean of the residual: `E[δ₂ - (λ₀ + λ₁ δ₁)] = d₂ - λ₀ - λ₁ d₁`. -/
theorem integral_residual (h₁ : MemLp δ₁ 2 μ) (h₂ : MemLp δ₂ 2 μ) (lam0 lam1 : ℝ) :
    ∫ ω, (δ₂ ω - (lam0 + lam1 * δ₁ ω)) ∂μ = μ[δ₂] - lam0 - lam1 * μ[δ₁] := by
  have i₁ := h₁.integrable one_le_two
  have i₂ := h₂.integrable one_le_two
  have i₃ : Integrable (fun ω => lam1 * δ₁ ω) μ := i₁.const_mul lam1
  have i₄ : Integrable (fun ω => lam0 + lam1 * δ₁ ω) μ := (integrable_const lam0).add i₃
  rw [integral_sub i₂ i₄, integral_add (integrable_const lam0) i₃, integral_const,
    integral_const_mul]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The conditional reading of the moment form: if `δ₁` is measurable, both effects are square
integrable, the conditional mean of `δ₂` given `δ₁` is `λ₀ + λ₁ δ₁` and the conditional
variance of `δ₂` given `δ₁` is the constant `ψ₂²` (almost surely), then the moment form
`PNFMoments` holds with the same parameters. This is the sense in which the moment form is a
consequence of the product normal formulation `δ₂ | δ₁ ~ N(λ₀ + λ₁ δ₁, ψ₂²)`. -/
theorem pnfMoments_of_condMoments {lam0 lam1 psiSq : ℝ} (hm : Measurable δ₁)
    (h₁ : MemLp δ₁ 2 μ) (h₂ : MemLp δ₂ 2 μ)
    (hmean : μ[δ₂ | Real.measurableSpace.comap δ₁] =ᵐ[μ]
      fun ω => lam0 + lam1 * δ₁ ω)
    (hvar : Var[δ₂; μ | Real.measurableSpace.comap δ₁] =ᵐ[μ] fun _ => psiSq) :
    PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq := by
  have hle : Real.measurableSpace.comap δ₁ ≤ ‹MeasurableSpace Ω› :=
    hm.comap_le
  set f : Ω → ℝ := fun ω => lam0 + lam1 * δ₁ ω
  have hfm : StronglyMeasurable[Real.measurableSpace.comap δ₁] f :=
    (measurable_const.add (measurable_const.mul (comap_measurable δ₁))).stronglyMeasurable
  have i₁ := h₁.integrable one_le_two
  have i₂ := h₂.integrable one_le_two
  have hf2 : MemLp f 2 μ := (memLp_const lam0).add (h₁.const_mul lam1)
  have hR2 : MemLp (fun ω => δ₂ ω - f ω) 2 μ := h₂.sub hf2
  -- the mean of the residual vanishes
  have hmeanR : ∫ ω, (δ₂ ω - f ω) ∂μ = 0 := by
    rw [integral_sub i₂ (hf2.integrable one_le_two), ← integral_condExp hle,
      integral_congr_ae hmean, sub_self]
  -- the conditional mean of the residual vanishes
  have hcR : μ[fun ω => δ₂ ω - f ω | Real.measurableSpace.comap δ₁] =ᵐ[μ] 0 := by
    have e1 := condExp_sub i₂ (hf2.integrable one_le_two) (Real.measurableSpace.comap δ₁)
    have e2 : μ[f | Real.measurableSpace.comap δ₁] = f :=
      condExp_of_stronglyMeasurable hle hfm (hf2.integrable one_le_two)
    filter_upwards [e1, hmean] with ω h1 h2
    simp only [Pi.sub_apply, e2] at h1
    rw [show (fun ω => δ₂ ω - f ω) = δ₂ - f from rfl, h1, h2]
    simp [f]
  have hprod : ∫ ω, δ₁ ω * (δ₂ ω - f ω) ∂μ = 0 := by
    have hint : Integrable (δ₁ * fun ω => δ₂ ω - f ω) μ := h₁.integrable_mul hR2
    rw [show (fun ω => δ₁ ω * (δ₂ ω - f ω)) = δ₁ * fun ω => δ₂ ω - f ω from rfl,
      ← integral_condExp hle]
    have := condExp_mul_of_stronglyMeasurable_left (m := Real.measurableSpace.comap δ₁)
      (μ := μ) (comap_measurable δ₁).stronglyMeasurable hint (hR2.integrable one_le_two)
    rw [integral_congr_ae this]
    have h0 : (δ₁ * μ[fun ω => δ₂ ω - f ω | Real.measurableSpace.comap δ₁]) =ᵐ[μ] 0 := by
      filter_upwards [hcR] with ω hω
      simp [hω]
    rw [integral_congr_ae h0]
    simp
  have hcov : cov[δ₁, fun ω => δ₂ ω - f ω; μ] = 0 := by
    rw [covariance_eq_sub h₁ hR2]
    simp only [Pi.mul_apply]
    rw [hprod, hmeanR, mul_zero, sub_zero]
  refine ⟨h₁, h₂, hmeanR, hcov, ?_⟩
  -- law of total variance: `var δ₂ = ψ₂² + λ₁² var δ₁`
  have htot := integral_condVar_add_variance_condExp hle h₂ (μ := μ)
  rw [integral_congr_ae hvar, integral_const, variance_congr hmean] at htot
  simp only [probReal_univ, smul_eq_mul, one_mul] at htot
  rw [variance_const_add (h₁.const_mul lam1).aestronglyMeasurable, variance_const_mul] at htot
  have hc := hcov
  rw [covariance_residual h₁ h₂] at hc
  rw [variance_residual h₁ h₂]
  have : cov[δ₁, δ₂; μ] = lam1 * Var[δ₁; μ] := by linarith
  rw [this]
  linarith

end Algebra

/-! ### Parameter relations (TSD 20, equations (6), (8), (9), (10)) -/

namespace PNFMoments

variable [IsProbabilityMeasure μ] {δ₁ δ₂ : Ω → ℝ} {lam0 lam1 psiSq : ℝ}

/-- The slope of the product normal formulation is the least squares slope (TSD 20,
equation (6)): `λ₁ = cov(δ₁, δ₂) / var δ₁`, when `var δ₁ ≠ 0`. -/
theorem slope_eq (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) (hV : Var[δ₁; μ] ≠ 0) :
    lam1 = cov[δ₁, δ₂; μ] / Var[δ₁; μ] := by
  have := h.cov_residual
  rw [covariance_residual h.memLp_fst h.memLp_snd] at this
  field_simp
  linarith

/-- The intercept (TSD 20, equation (10) before substituting the slope): `λ₀ = d₂ - λ₁ d₁`
with `dⱼ = E δⱼ`. No condition `d₁ ≠ 0` is needed. -/
theorem intercept_eq (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) :
    lam0 = μ[δ₂] - lam1 * μ[δ₁] := by
  have := h.mean_residual
  rw [integral_residual h.memLp_fst h.memLp_snd] at this
  linarith

/-- The residual variance (TSD 20, equation (6)): `ψ₂² = τ₂² - λ₁² τ₁²` with
`τⱼ² = var δⱼ`. Here `ψ₂²` is the variance of the least squares residual; TSD 20 calls it the
conditional variance, which it is under the conditional moment hypotheses of
`pnfMoments_of_condMoments` (for instance in the bivariate normal model) and not in general
(`Countermodel.residVar_ne_condVar`). -/
theorem residVar_eq (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) :
    psiSq = Var[δ₂; μ] - lam1 ^ 2 * Var[δ₁; μ] := by
  have hc := h.cov_residual
  rw [covariance_residual h.memLp_fst h.memLp_snd] at hc
  rw [← h.var_residual, variance_residual h.memLp_fst h.memLp_snd]
  have : cov[δ₁, δ₂; μ] = lam1 * Var[δ₁; μ] := by linarith
  rw [this]
  ring

/-- Equation (8) of TSD 20: in the parameterization of the standard bivariate model,
`var δ₁ = τ₁²`, `var δ₂ = τ₂²`, `cov(δ₁, δ₂) = ρ τ₁ τ₂` with `τ₁ > 0`, the slope is
`λ₁ = ρ τ₂ / τ₁`. -/
theorem slope_eq_corr (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) {τ₁ τ₂ ρ : ℝ} (hτ₁ : 0 < τ₁)
    (hv₁ : Var[δ₁; μ] = τ₁ ^ 2) (hc : cov[δ₁, δ₂; μ] = ρ * τ₁ * τ₂) :
    lam1 = ρ * τ₂ / τ₁ := by
  rw [h.slope_eq (by rw [hv₁]; positivity), hv₁, hc]
  field_simp

/-- Equation (9) of TSD 20 for the residual variance: `ψ₂² = τ₂² (1 - ρ²)`. -/
theorem residVar_eq_corr (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) {τ₁ τ₂ ρ : ℝ} (hτ₁ : 0 < τ₁)
    (hv₁ : Var[δ₁; μ] = τ₁ ^ 2) (hv₂ : Var[δ₂; μ] = τ₂ ^ 2)
    (hc : cov[δ₁, δ₂; μ] = ρ * τ₁ * τ₂) :
    psiSq = τ₂ ^ 2 * (1 - ρ ^ 2) := by
  rw [h.residVar_eq, h.slope_eq_corr hτ₁ hv₁ hc, hv₁, hv₂]
  field_simp

/-- Equation (10) of TSD 20: `λ₀ = d₂ - d₁ ρ τ₂ / τ₁`. -/
theorem intercept_eq_corr (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) {τ₁ τ₂ ρ : ℝ}
    (hτ₁ : 0 < τ₁) (hv₁ : Var[δ₁; μ] = τ₁ ^ 2) (hc : cov[δ₁, δ₂; μ] = ρ * τ₁ * τ₂) :
    lam0 = μ[δ₂] - μ[δ₁] * ρ * τ₂ / τ₁ := by
  rw [h.intercept_eq, h.slope_eq_corr hτ₁ hv₁ hc]
  ring

end PNFMoments

/-- The least squares slope `cov(δ₁, δ₂) / var δ₁` of `δ₂` on `δ₁`. It is a slope only when
`var δ₁ ≠ 0`, which every theorem using it assumes. -/
noncomputable def lsSlope (μ : Measure Ω) (δ₁ δ₂ : Ω → ℝ) : ℝ := cov[δ₁, δ₂; μ] / Var[δ₁; μ]

section LeastSquares

variable [IsProbabilityMeasure μ] {δ₁ δ₂ : Ω → ℝ}

/-- Orthogonality: the residual `δ₂ - λ₁ δ₁` of the least squares slope is uncorrelated with
`δ₁`, when `var δ₁ ≠ 0`. -/
theorem covariance_sub_slope_mul (h₁ : MemLp δ₁ 2 μ) (h₂ : MemLp δ₂ 2 μ)
    (hV : Var[δ₁; μ] ≠ 0) (lam0 : ℝ) :
    cov[δ₁, fun ω => δ₂ ω - (lam0 + lsSlope μ δ₁ δ₂ * δ₁ ω); μ] = 0 := by
  rw [covariance_residual h₁ h₂, lsSlope, div_mul_cancel₀ _ hV, sub_self]

/-- The residual variance identity: `var(δ₂ - λ₁ δ₁) = var δ₂ - cov(δ₁, δ₂)² / var δ₁` for the
least squares slope `λ₁`, when `var δ₁ ≠ 0`. This is the equality case of population least
squares behind TSD 20, equations (6) and (9). -/
theorem variance_sub_slope_mul (h₁ : MemLp δ₁ 2 μ) (h₂ : MemLp δ₂ 2 μ)
    (hV : Var[δ₁; μ] ≠ 0) (lam0 : ℝ) :
    Var[fun ω => δ₂ ω - (lam0 + lsSlope μ δ₁ δ₂ * δ₁ ω); μ] =
      Var[δ₂; μ] - cov[δ₁, δ₂; μ] ^ 2 / Var[δ₁; μ] := by
  rw [variance_residual h₁ h₂, lsSlope]
  field_simp
  ring

/-- Every square integrable pair `(δ₁, δ₂)` with `var δ₁ ≠ 0` satisfies the moment form of the
product normal formulation with `λ₁ = cov(δ₁, δ₂) / var δ₁`, `λ₀ = d₂ - λ₁ d₁` and
`ψ₂² = var δ₂ - cov(δ₁, δ₂)² / var δ₁`; by `PNFMoments.slope_eq`, `PNFMoments.intercept_eq`
and `PNFMoments.residVar_eq` these are the only such parameters. -/
theorem pnfMoments_slope (h₁ : MemLp δ₁ 2 μ) (h₂ : MemLp δ₂ 2 μ) (hV : Var[δ₁; μ] ≠ 0) :
    PNFMoments μ δ₁ δ₂ (μ[δ₂] - lsSlope μ δ₁ δ₂ * μ[δ₁]) (lsSlope μ δ₁ δ₂)
      (Var[δ₂; μ] - cov[δ₁, δ₂; μ] ^ 2 / Var[δ₁; μ]) where
  memLp_fst := h₁
  memLp_snd := h₂
  mean_residual := by rw [integral_residual h₁ h₂]; ring
  cov_residual := covariance_sub_slope_mul h₁ h₂ hV _
  var_residual := variance_sub_slope_mul h₁ h₂ hV _

end LeastSquares

/-! ### Perfect surrogacy and the correlation (TSD 20, Sections 3.4 and 3.5) -/

/-- Perfect affine prediction in the two parameterizations (TSD 20, Section 3.5): if
`ψ₂² = τ₂² (1 - ρ²)` (equation (9)) and `τ₂ ≠ 0`, then `ψ₂² = 0` if and only if `ρ² = 1`, that
is `ρ = ±1` (Section 3.4). The surrogacy criteria also need a zero intercept
(`PNFMoments.surrogacyCriteria_iff_corr`). -/
theorem residVar_eq_zero_iff {τ₂ ρ psiSq : ℝ} (h : psiSq = τ₂ ^ 2 * (1 - ρ ^ 2)) (hτ : τ₂ ≠ 0) :
    psiSq = 0 ↔ ρ ^ 2 = 1 := by
  rw [h, mul_eq_zero, or_iff_right (pow_ne_zero 2 hτ), sub_eq_zero, eq_comm]

/-- The trial-level `R²` (TSD 20, Section 3.5): `1 - ψ₂² / τ₂² = ρ²` when
`ψ₂² = τ₂² (1 - ρ²)` and `τ₂ ≠ 0`. -/
theorem rSq_eq {τ₂ ρ psiSq : ℝ} (h : psiSq = τ₂ ^ 2 * (1 - ρ ^ 2)) (hτ : τ₂ ≠ 0) :
    1 - psiSq / τ₂ ^ 2 = ρ ^ 2 := by
  rw [h]
  field_simp
  ring

namespace PNFMoments

variable [IsProbabilityMeasure μ] {δ₁ δ₂ : Ω → ℝ} {lam0 lam1 psiSq : ℝ}

/-- Perfect affine prediction is perfect correlation (TSD 20, Section 3.5): under the moment
form of the product normal formulation, with `var δ₁ = τ₁²`, `var δ₂ = τ₂²`,
`cov(δ₁, δ₂) = ρ τ₁ τ₂`, `τ₁ > 0` and `τ₂ ≠ 0`, the residual variance `ψ₂²` is zero (so `δ₂` is
almost surely an affine function of `δ₁`) if and only if `ρ² = 1`. This is not perfect
surrogacy: `δ₂ = 1 + δ₁` has `ρ = 1` and `ψ₂² = 0` but a nonzero intercept
(`Countermodel.intercept_ne_zero`); the full criteria are `surrogacyCriteria_iff_corr`. -/
theorem residVar_eq_zero_iff_corr (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) {τ₁ τ₂ ρ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : τ₂ ≠ 0) (hv₁ : Var[δ₁; μ] = τ₁ ^ 2) (hv₂ : Var[δ₂; μ] = τ₂ ^ 2)
    (hc : cov[δ₁, δ₂; μ] = ρ * τ₁ * τ₂) : psiSq = 0 ↔ ρ ^ 2 = 1 :=
  residVar_eq_zero_iff (h.residVar_eq_corr hτ₁ hv₁ hv₂ hc) hτ₂

/-- The trial-level `R²` under the moment form of the product normal formulation:
`1 - ψ₂² / τ₂² = ρ²` when `τ₁ > 0` and `τ₂ ≠ 0`. -/
theorem rSq_eq_corr (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) {τ₁ τ₂ ρ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : τ₂ ≠ 0) (hv₁ : Var[δ₁; μ] = τ₁ ^ 2) (hv₂ : Var[δ₂; μ] = τ₂ ^ 2)
    (hc : cov[δ₁, δ₂; μ] = ρ * τ₁ * τ₂) : 1 - psiSq / τ₂ ^ 2 = ρ ^ 2 :=
  rSq_eq (h.residVar_eq_corr hτ₁ hv₁ hv₂ hc) hτ₂

/-- The surrogacy criteria of Daniels and Hughes in the correlation parameterization: under the
moment form, with `var δ₁ = τ₁²`, `var δ₂ = τ₂²`, `cov(δ₁, δ₂) = ρ τ₁ τ₂`, `τ₁ > 0` and
`τ₂ ≠ 0`, the three criteria `λ₀ = 0`, `λ₁ ≠ 0`, `ψ₂² = 0` hold if and only if `ρ² = 1` and
`λ₀ = 0`. -/
theorem surrogacyCriteria_iff_corr (h : PNFMoments μ δ₁ δ₂ lam0 lam1 psiSq) {τ₁ τ₂ ρ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : τ₂ ≠ 0) (hv₁ : Var[δ₁; μ] = τ₁ ^ 2) (hv₂ : Var[δ₂; μ] = τ₂ ^ 2)
    (hc : cov[δ₁, δ₂; μ] = ρ * τ₁ * τ₂) :
    SurrogacyCriteria lam0 lam1 psiSq ↔ ρ ^ 2 = 1 ∧ lam0 = 0 := by
  have hiff := h.residVar_eq_zero_iff_corr hτ₁ hτ₂ hv₁ hv₂ hc
  refine ⟨fun hs => ⟨hiff.1 hs.condVar_eq_zero, hs.intercept_eq_zero⟩,
    fun ⟨hρ, h0⟩ => ⟨h0, ?_, hiff.2 hρ⟩⟩
  have hρ0 : ρ ≠ 0 := by rintro rfl; norm_num at hρ
  rw [h.slope_eq_corr hτ₁ hv₁ hc]
  exact div_ne_zero (mul_ne_zero hρ0 hτ₂) hτ₁.ne'

end PNFMoments

/-! ### Countermodels: each criterion is needed, and `τ₂ > 0` is needed -/

namespace Countermodel

/-- The indicator `[b]` of a Boolean, as a real number. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The uniform law on the four points of `Bool × Bool`. -/
noncomputable abbrev unif₄ : Measure (Bool × Bool) := uniformOn Set.univ

/-- The uniform law on the two points of `Bool`. -/
noncomputable abbrev unif₂ : Measure Bool := uniformOn Set.univ

theorem integral_unif₂ (f : Bool → ℝ) : ∫ b, f b ∂unif₂ = (f true + f false) / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Fintype.sum_bool, measureReal_def, uniformOn_univ, Measure.count_singleton,
    Fintype.card_bool, smul_eq_mul]
  norm_num
  ring

theorem integral_unif₄ (f : Bool × Bool → ℝ) :
    ∫ ω, f ω ∂unif₄ =
      (f (true, true) + f (true, false) + f (false, true) + f (false, false)) / 4 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, measureReal_def, uniformOn_univ,
    Measure.count_singleton, Fintype.card_prod, Fintype.card_bool, smul_eq_mul]
  norm_num
  ring

/-- Every point of `Bool` has positive mass under `unif₂`. -/
theorem unif₂_singleton_ne_zero (b : Bool) : unif₂ {b} ≠ 0 := by
  simp [uniformOn_univ]

/-- Every point of `Bool × Bool` has positive mass under `unif₄`. -/
theorem unif₄_singleton_ne_zero (ω : Bool × Bool) : unif₄ {ω} ≠ 0 := by
  simp [uniformOn_univ]

/-- The variance of `[b]` under the uniform law on `Bool` is `(1/2)²`. -/
theorem variance_bit : Var[bit; unif₂] = (1 / 2) ^ 2 := by
  rw [variance_eq_integral (measurable_of_finite _).aemeasurable, integral_unif₂,
    integral_unif₂]
  simp only [bit]
  norm_num

/-- Without a zero intercept null preservation fails, although the other two criteria hold:
two equally likely studies with `δ₁ = [b]`, `δ₂ = 1 + [b]` satisfy the moment form of the
product normal formulation with `λ₀ = 1`, `λ₁ = 1`, `ψ₂² = 0` and `var δ₁ > 0` (so the
parameters are unique, `PNFMoments.slope_eq`), yet in the study with no effect on the
surrogate the effect on the final outcome is `1`. -/
theorem intercept_ne_zero :
    PNFMoments unif₂ bit (fun b => 1 + bit b) 1 1 0 ∧ Var[bit; unif₂] ≠ 0 ∧
      ¬ ∀ᵐ b ∂unif₂, bit b = 0 → 1 + bit b = 0 := by
  have hres : (fun b => 1 + bit b - (1 + 1 * bit b)) = fun _ => (0 : ℝ) := by
    funext b; ring
  refine ⟨⟨MemLp.of_discrete, MemLp.of_discrete, ?_, ?_, ?_⟩, by rw [variance_bit]; norm_num,
    fun h => ?_⟩
  · rw [hres, integral_zero]
  · rw [hres]; exact covariance_const_right _
  · rw [hres]; exact variance_zero _
  · have := (ae_iff_of_countable.1 h) false (unif₂_singleton_ne_zero false)
    norm_num [bit] at this

/-- Without a nonzero slope an effect on the surrogate does not imply an effect on the final
outcome, although the other two criteria hold: two equally likely studies with `δ₁ = [b]` and
`δ₂ = 0` satisfy the moment form of the product normal formulation with `λ₀ = 0`, `λ₁ = 0`,
`ψ₂² = 0` and `var δ₁ > 0`, yet in the study with an effect `1` on the surrogate there is no
effect on the final outcome. -/
theorem slope_eq_zero :
    PNFMoments unif₂ bit (fun _ => 0) 0 0 0 ∧ Var[bit; unif₂] ≠ 0 ∧
      ¬ ∀ᵐ b ∂unif₂, (0 : ℝ) = 0 → bit b = 0 := by
  have hres : (fun b => (0 : ℝ) - (0 + 0 * bit b)) = fun _ => (0 : ℝ) := by
    funext b; ring
  refine ⟨⟨MemLp.of_discrete, MemLp.of_discrete, ?_, ?_, ?_⟩, by rw [variance_bit]; norm_num,
    fun h => ?_⟩
  · rw [hres, integral_zero]
  · rw [hres]; exact covariance_const_right _
  · rw [hres]; exact variance_zero _
  · have := (ae_iff_of_countable.1 h) true (unif₂_singleton_ne_zero true)
    norm_num [bit] at this

/-- The residual `±1` of the conditional variance countermodel. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Without zero conditional variance null preservation fails, although the other two criteria
hold: four equally likely studies `(a, b)` with `δ₁ = [a]` and `δ₂ = [a] ± 1` (sign from `b`)
satisfy the moment form of the product normal formulation with `λ₀ = 0`, `λ₁ = 1`, `ψ₂² = 1`
and `var δ₁ > 0`, yet in the studies with no effect on the surrogate the effect on the final
outcome is `±1`. Here the residual `±1` is independent of `δ₁`, so `ψ₂² = 1` is also the
conditional variance. -/
theorem condVar_pos :
    PNFMoments unif₄ (fun ω => bit ω.1) (fun ω => bit ω.1 + sgn ω.2) 0 1 1 ∧
      Var[fun ω : Bool × Bool => bit ω.1; unif₄] ≠ 0 ∧
      ¬ ∀ᵐ ω ∂unif₄, bit ω.1 = 0 → bit ω.1 + sgn ω.2 = 0 := by
  have hres : (fun ω : Bool × Bool => bit ω.1 + sgn ω.2 - (0 + 1 * bit ω.1)) =
      fun ω => sgn ω.2 := by
    funext ω; ring
  have hmean : ∫ ω, sgn ω.2 ∂unif₄ = 0 := by
    rw [integral_unif₄]; norm_num [sgn]
  refine ⟨⟨MemLp.of_discrete, MemLp.of_discrete, ?_, ?_, ?_⟩, ?_, fun h => ?_⟩
  · rw [hres, hmean]
  · rw [hres, covariance, integral_unif₄, hmean, integral_unif₄]
    norm_num [bit, sgn]
  · rw [hres, variance_of_integral_eq_zero (measurable_of_finite _).aemeasurable hmean,
      integral_unif₄]
    norm_num [sgn]
  · rw [variance_eq_integral (measurable_of_finite _).aemeasurable, integral_unif₄,
      integral_unif₄]
    norm_num [bit]
  · have := (ae_iff_of_countable.1 h) (false, true)
      (unif₄_singleton_ne_zero (false, true))
    norm_num [bit, sgn] at this

/-- The condition `τ₂ ≠ 0` cannot be dropped from `PNFMoments.residVar_eq_zero_iff_corr`. With
`δ₁ = [b]` on two equally likely studies and a constant `δ₂ = 1`, the moment form of the product
normal formulation holds with `λ₀ = 1`, `λ₁ = 0`, `ψ₂² = 0`, and the second moments are
`var δ₁ = (1/2)²`, `var δ₂ = 0²`, `cov(δ₁, δ₂) = ρ τ₁ τ₂` for `ρ = 0`; so `ψ₂² = 0` although
`ρ² ≠ 1`. TSD 20, Section 3.5 derives "`ψ₂² = 0` implies `ρ = ±1`" from equation (9) without
stating `τ₂ > 0`. (With `τ₂ = 0` the correlation is undefined, and every `ρ` satisfies the
displayed moment equations.) -/
theorem degenerate_final :
    PNFMoments unif₂ bit (fun _ => 1) 1 0 0 ∧ Var[bit; unif₂] = (1 / 2) ^ 2 ∧
      Var[fun _ : Bool => (1 : ℝ); unif₂] = 0 ^ 2 ∧
      cov[bit, fun _ : Bool => (1 : ℝ); unif₂] = 0 * (1 / 2) * 0 ∧ ¬ (0 : ℝ) ^ 2 = 1 := by
  have hres : (fun b => (1 : ℝ) - (1 + 0 * bit b)) = fun _ => (0 : ℝ) := by
    funext b; ring
  refine ⟨⟨MemLp.of_discrete, MemLp.of_discrete, ?_, ?_, ?_⟩, variance_bit, ?_, ?_, by norm_num⟩
  · rw [hres, integral_zero]
  · rw [hres]; exact covariance_const_right _
  · rw [hres]; exact variance_zero _
  · rw [variance_eq_integral (measurable_of_finite _).aemeasurable, integral_unif₂,
      integral_unif₂]
    norm_num
  · rw [covariance_const_right]; ring

/-- The uniform law on the three points of `Fin 3`. -/
noncomputable abbrev unif₃ : Measure (Fin 3) := uniformOn Set.univ

theorem integral_unif₃ (f : Fin 3 → ℝ) : ∫ i, f i ∂unif₃ = (f 0 + f 1 + f 2) / 3 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Fin.sum_univ_three, measureReal_def, uniformOn_univ, Measure.count_singleton,
    Fintype.card_fin, smul_eq_mul]
  norm_num
  ring

/-- Under `unif₃` the conditional mean given a point is the value at that point. -/
theorem condMean_unif₃_singleton (i : Fin 3) (f : Fin 3 → ℝ) :
    Mediation.condMean unif₃ {i} f = f i := by
  rw [Mediation.condMean_eq, integral_singleton, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by simp [measureReal_def, uniformOn_univ]), one_mul]

/-- The surrogate effect `δ₁` of the residual variance countermodel: `-1`, `0`, `1`. -/
def tri : Fin 3 → ℝ := ![-1, 0, 1]

/-- The final outcome effect of the residual variance countermodel: `δ₂ = δ₁ + δ₁² - 2/3`. -/
noncomputable def triY (i : Fin 3) : ℝ := tri i + tri i ^ 2 - 2 / 3

/-- The moment form describes the least squares residual, not the conditional law. With `δ₁`
uniform on `{-1, 0, 1}` and `δ₂ = δ₁ + δ₁² - 2/3`, the moment form of the product normal
formulation holds with `λ₀ = 0`, `λ₁ = 1` and residual variance `ψ₂² = 2/9`, yet `δ₂` is a
function of `δ₁`: the conditional variance of `δ₂` given `δ₁` is zero in every cell, and the
conditional mean at `δ₁ = 0` is `-2/3`, not `λ₀ + λ₁ · 0 = 0`. -/
theorem residVar_ne_condVar :
    PNFMoments unif₃ tri triY 0 1 (2 / 9) ∧
      (∀ i, Mediation.condMean unif₃ (tri ⁻¹' {tri i})
        (fun j => (triY j - Mediation.condMean unif₃ (tri ⁻¹' {tri i}) triY) ^ 2) = 0) ∧
      Mediation.condMean unif₃ (tri ⁻¹' {0}) triY = -2 / 3 := by
  have hcell : ∀ i, tri ⁻¹' {tri i} = {i} := by
    intro i; ext j
    fin_cases i <;> fin_cases j <;> norm_num [tri]
  have hres : (fun i => triY i - (0 + 1 * tri i)) = fun i => tri i ^ 2 - 2 / 3 := by
    funext i; simp only [triY]; ring
  have hmean : ∫ i, (tri i ^ 2 - 2 / 3) ∂unif₃ = 0 := by
    rw [integral_unif₃]; norm_num [tri]
  refine ⟨⟨MemLp.of_discrete, MemLp.of_discrete, ?_, ?_, ?_⟩, fun i => ?_, ?_⟩
  · rw [hres, hmean]
  · rw [hres, covariance, integral_unif₃, hmean, integral_unif₃]
    norm_num [tri]
  · rw [hres, variance_of_integral_eq_zero (measurable_of_finite _).aemeasurable hmean,
      integral_unif₃]
    norm_num [tri]
  · rw [hcell, condMean_unif₃_singleton, condMean_unif₃_singleton, sub_self]
    norm_num
  · rw [show (0 : ℝ) = tri 1 by simp [tri], hcell, condMean_unif₃_singleton]
    norm_num [triY, tri]

end Countermodel

/-! ### The single mapping hypothesis (TSD 5, Section 3.1) -/

/-- The single mapping hypothesis of TSD 5, Section 3.1, for a binary short-term outcome. The
treatments `t : T` have short-term potential outcomes `S t` and final potential outcomes
`Y t s`, so the final outcome under treatment `t` is `Y t (S t)`. Assume

* no direct effect: `Y t s = Y t₀ s` for every treatment (the treatment acts on the final
  outcome only through the short-term outcome; the "no differences between treatments in the
  downstream model, conditional on the shorter term trial outcomes" of TSD 5);
* for every treatment, `S t` is independent of the unit level effect `Y t₀ 1 - Y t₀ 0` of the
  short-term outcome on the final outcome (no common cause of the two).

Then `E[Y t (S t)] = E[Y t₀ 0] + P(S t = 1) E[Y t₀ 1 - Y t₀ 0]` for every treatment: one affine
map, the same for all treatments, sends the short-term outcome to the final outcome. The
countermodels in `Surrogacy.Counterexamples` show that neither assumption can be dropped. -/
theorem single_mapping [IsProbabilityMeasure μ] {T : Type*} (S : T → Ω → Bool)
    (Y : T → Bool → Ω → ℝ) (t₀ : T) (hS : ∀ t, Measurable (S t))
    (hY : ∀ m, Integrable (Y t₀ m) μ) (hnde : ∀ t m, Y t m = Y t₀ m)
    (hind : ∀ t, IndepFun (S t) (fun ω => Y t₀ true ω - Y t₀ false ω) μ) (t : T) :
    ∫ ω, Y t (S t ω) ω ∂μ = ∫ ω, Y t₀ false ω ∂μ +
      μ.real {ω | S t ω = true} * ∫ ω, (Y t₀ true ω - Y t₀ false ω) ∂μ := by
  set D : Ω → ℝ := fun ω => Y t₀ true ω - Y t₀ false ω
  set I : Ω → ℝ := fun ω => if S t ω then 1 else 0
  have hpt : (fun ω => Y t (S t ω) ω) = fun ω => Y t₀ false ω + I ω * D ω := by
    funext ω
    simp only [hnde, I, D]
    cases S t ω <;> simp
  have hI : Measurable I := (measurable_of_finite fun b : Bool => if b then (1 : ℝ) else 0).comp
    (hS t)
  have hD : Integrable D μ := (hY true).sub (hY false)
  have hind' : IndepFun I D μ :=
    (hind t).comp (measurable_of_finite fun b : Bool => if b then (1 : ℝ) else 0) measurable_id
  have hprod : ∫ ω, I ω * D ω ∂μ = μ.real {ω | S t ω = true} * ∫ ω, D ω ∂μ := by
    rw [hind'.integral_fun_mul_eq_mul_integral hI.aestronglyMeasurable hD.aestronglyMeasurable]
    congr 1
    have hset : MeasurableSet {ω | S t ω = true} := hS t (measurableSet_singleton true)
    rw [← integral_indicator_one hset]
    congr 1
    funext ω
    by_cases h : S t ω = true <;> simp [I, h, Set.indicator]
  have hIDint : Integrable (fun ω => I ω * D ω) μ := by
    have : (fun ω => I ω * D ω) = {ω | S t ω = true}.indicator D := by
      funext ω
      by_cases h : S t ω = true <;> simp [I, h, Set.indicator]
    rw [this]
    exact hD.indicator (hS t (measurableSet_singleton true))
  rw [hpt, integral_add (hY false) hIDint, hprod]

/-- The single mapping hypothesis in contrast form (TSD 5, Section 3.1): under the assumptions of
`single_mapping`, the effect of treatment `t` against `t'` on the final outcome is the effect on
the probability of the short-term outcome times the mean effect `E[Y t₀ 1 - Y t₀ 0]` of the
short-term outcome on the final outcome; the factor is the same for every pair of treatments. -/
theorem single_mapping_sub [IsProbabilityMeasure μ] {T : Type*} (S : T → Ω → Bool)
    (Y : T → Bool → Ω → ℝ) (t₀ : T) (hS : ∀ t, Measurable (S t))
    (hY : ∀ m, Integrable (Y t₀ m) μ) (hnde : ∀ t m, Y t m = Y t₀ m)
    (hind : ∀ t, IndepFun (S t) (fun ω => Y t₀ true ω - Y t₀ false ω) μ) (t t' : T) :
    ∫ ω, Y t (S t ω) ω ∂μ - ∫ ω, Y t' (S t' ω) ω ∂μ =
      (μ.real {ω | S t ω = true} - μ.real {ω | S t' ω = true}) *
        ∫ ω, (Y t₀ true ω - Y t₀ false ω) ∂μ := by
  rw [single_mapping S Y t₀ hS hY hnde hind t, single_mapping S Y t₀ hS hY hnde hind t']
  ring

/-! ### The Prentice criteria (Prentice 1989; discussed in TSD 20, Section 3.1.2) -/

open Mediation

/-- Full capture in mean form for a trial with binary treatment `A`, observed surrogate
`S = Mobs` and observed final outcome `Y = Yobs` of a mediation model `P`:
`E[Y | A = 1, S = s] = E[Y | A = 0, S = s]` for both values `s`. Conditional means are
`Mediation.condMean`, which is `0` on a null event; the criteria that use this predicate
(`PrenticeCriteria`) require every cell `A = a, S = s` to have positive probability. -/
def MeanFullCapture {Ω : Type*} [MeasurableSpace Ω] (P : MediationModel Ω Bool)
    (μ : Measure Ω) : Prop :=
  ∀ s : Bool, condMean μ (P.A ⁻¹' {true} ∩ P.Mobs ⁻¹' {s}) P.Yobs =
    condMean μ (P.A ⁻¹' {false} ∩ P.Mobs ⁻¹' {s}) P.Yobs

/-- Distributional full capture: for both values `s` of the surrogate, the conditional law of the
final outcome `Y = Yobs` given `A = 1, S = s` equals its conditional law given `A = 0, S = s`.
When every cell `A = a, S = s` has positive probability this says that the final outcome is
independent of the binary treatment given the surrogate. It implies the mean form
(`DistFullCapture.meanFullCapture`) but is not implied by it
(`Surrogacy.Counterexample.meanOnly_not_distFullCapture`). -/
def DistFullCapture {Ω : Type*} [MeasurableSpace Ω] (P : MediationModel Ω Bool)
    (μ : Measure Ω) : Prop :=
  ∀ s : Bool, (μ[|P.A ⁻¹' {true} ∩ P.Mobs ⁻¹' {s}]).map P.Yobs =
    (μ[|P.A ⁻¹' {false} ∩ P.Mobs ⁻¹' {s}]).map P.Yobs

/-- Under distributional full capture the conditional mean of every measurable transform
`g(Y)` of the final outcome is the same in the two arms within each surrogate value. -/
theorem DistFullCapture.condMean_comp_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : MediationModel Ω Bool} {μ : Measure Ω} (h : DistFullCapture P μ)
    (hY : Measurable P.Yobs) {g : ℝ → ℝ} (hg : Measurable g) (s : Bool) :
    condMean μ (P.A ⁻¹' {true} ∩ P.Mobs ⁻¹' {s}) (fun ω => g (P.Yobs ω)) =
      condMean μ (P.A ⁻¹' {false} ∩ P.Mobs ⁻¹' {s}) (fun ω => g (P.Yobs ω)) := by
  simp only [condMean]
  rw [← integral_map hY.aemeasurable hg.aestronglyMeasurable, h s,
    integral_map hY.aemeasurable hg.aestronglyMeasurable]

/-- Distributional full capture implies full capture in mean form. -/
theorem DistFullCapture.meanFullCapture {Ω : Type*} [MeasurableSpace Ω]
    {P : MediationModel Ω Bool} {μ : Measure Ω} (h : DistFullCapture P μ)
    (hY : Measurable P.Yobs) : MeanFullCapture P μ :=
  fun s => h.condMean_comp_eq hY measurable_id s

/-- If the observed final outcome is a function `f` of the observed surrogate, and every cell
`A = a, S = s` has positive probability, then distributional full capture holds: within each
surrogate value the conditional law of the final outcome is the point mass at `f s` in both
arms. -/
theorem distFullCapture_of_comp {Ω : Type*} [MeasurableSpace Ω] {P : MediationModel Ω Bool}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hA : Measurable P.A) (hS : Measurable P.Mobs)
    (f : Bool → ℝ) (hf : ∀ ω, P.Yobs ω = f (P.Mobs ω))
    (hpos : ∀ a s : Bool, μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {s}) ≠ 0) : DistFullCapture P μ := by
  have key : ∀ a s : Bool, (μ[|P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {s}]).map P.Yobs = Measure.dirac (f s) := by
    intro a s
    have hc : MeasurableSet (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {s}) :=
      (hA (measurableSet_singleton a)).inter (hS (measurableSet_singleton s))
    have := cond_isProbabilityMeasure (μ := μ) (hpos a s)
    have hae : P.Yobs =ᵐ[μ[|P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {s}]] fun _ => f s := by
      filter_upwards [ae_cond_mem hc] with ω hω
      rw [hf, hω.2]
    rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]
  exact fun s => (key true s).trans (key false s).symm

/-- The operational criteria of Prentice (1989) for a binary surrogate, in mean form, for a trial
with binary treatment `A`, observed surrogate `S = Mobs` and observed final outcome `Y = Yobs` of
a mediation model `P` under a probability law `μ`. TSD 20, Section 3.1.2 mentions these criteria
(the surrogate is correlated with the final outcome and, in the fourth criterion, fully mediates
the treatment effect); the list is from Prentice (1989). The setting is a probability law, a
measurable treatment, surrogate and outcome, an integrable outcome, and positive probability of
each of the four cells `A = a, S = s` (so every conditional mean below is a genuine conditional
mean). The criteria are:

1. the treatment affects the surrogate: `P(S = 1 | A = 1) ≠ P(S = 1 | A = 0)`;
2. the surrogate predicts the final outcome: `E[Y | S = 1] ≠ E[Y | S = 0]`;
3. the treatment affects the final outcome: `E[Y | A = 1] ≠ E[Y | A = 0]`;
4. full capture in mean form (`MeanFullCapture`): `E[Y | A = 1, S = s] = E[Y | A = 0, S = s]`
   for both values `s`.

In a randomized trial the first and third are average causal effects. The distributional form of
the fourth criterion is `DistFullCapture`. -/
structure PrenticeCriteria {Ω : Type*} [MeasurableSpace Ω] (P : MediationModel Ω Bool)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop where
  measurable_A : Measurable P.A
  measurable_S : Measurable P.Mobs
  measurable_Y : Measurable P.Yobs
  integrable_Y : Integrable P.Yobs μ
  cell_pos : ∀ a s : Bool, μ (P.A ⁻¹' {a} ∩ P.Mobs ⁻¹' {s}) ≠ 0
  treatment_affects_surrogate :
    condMean μ (P.A ⁻¹' {true}) (fun ω => if P.Mobs ω then 1 else 0) ≠
      condMean μ (P.A ⁻¹' {false}) (fun ω => if P.Mobs ω then 1 else 0)
  surrogate_predicts_outcome :
    condMean μ (P.Mobs ⁻¹' {true}) P.Yobs ≠ condMean μ (P.Mobs ⁻¹' {false}) P.Yobs
  treatment_affects_outcome :
    condMean μ (P.A ⁻¹' {true}) P.Yobs ≠ condMean μ (P.A ⁻¹' {false}) P.Yobs
  full_capture : MeanFullCapture P μ

end Surrogacy

end CausalInference
