/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.MeasurementError

/-!
# Ecological bias, within-trial coefficients and regression to the mean

Three ways in which between-trial comparisons in a meta-regression mislead, from TSD 3
(Sections 1.1.2, 4.4 and 4.5.1), and the within-trial remedy.

## Main definitions

* `trialMean tr x i`, `dev tr x j = x j - trialMean tr x (tr j)`: trial means and deviations
  of patient-level data, `tr j` being the trial of patient `j`.
* `withinSlope tr x y`: the pooled within-trial slope `∑ (x - x̄)(y - ȳ) / ∑ (x - x̄)²`.
* `lsSlope`, `lsIntercept`: the equal-weight least squares line; `betweenSlope tr x y`: the
  least squares slope of the trial mean outcome on the trial mean covariate over the populated
  trials, with equal weights (aggregate-data meta-regression); `sizeWeightedBetweenSlope`: the
  same regression with trials weighted by their size.
* `feRSS tr x y α β`, `wbRSS tr x y a bW bB`: residual sums of squares of the model with trial
  fixed effects and of the within and between model with a common intercept.
* `armWithinSlope tr A a x y`: the pooled within-trial slope in treatment arm `a`.

## Main results

* `ecological_fallacy_example`: two trials with slope `1` inside each trial and between-trial
  slope `-3/2` (TSD 3, Section 1.1.2).
* `betweenSlope_eq_of_surjective`, `betweenSlope_unused_label`: unused trial labels do not
  enter `betweenSlope`; a regression over all labels would change with them.
  `betweenSlope_ne_sizeWeighted_example`: the equal-weight slope `1/2` and the size-weighted
  slope `6/11` of the same data.
* `withinSlope_add_trial`: the within-trial slope does not change when an additive trial-level
  term `g (trial)` is added to the outcome. It does change under trial-specific changes of the
  slope itself.
* `feRSS_le`: with a free intercept for every trial the least squares slope is the pooled
  within-trial slope, uniquely when the covariate varies within some trial.
* `wbRSS_le`, `wbRSS_min`: in the within and between model the least squares within coefficient
  is the pooled within-trial slope, whatever the intercept and the between coefficient, and the
  least squares between coefficient is `sizeWeightedBetweenSlope`.
* `armWithinSlope_add_trial`, `armWithinSlope_sub_add_trial`: the arm-specific within-trial
  slopes, and so their difference (the within-trial treatment by covariate interaction), do not
  change when `g (trial) + h (trial) * treatment` is added to the outcome.
* `slope_observed_baseline`, `slope_observed_baseline_lt_zero`, `slope_observed_baseline_neg`,
  `regression_to_mean_example`: regressing observed treatment effects on observed baseline
  risks gives the slope `(Cov(μ, δ) - Var(e_C)) / (Var(μ) + Var(e_C))`, so a spurious negative
  slope when the true effect is uncorrelated with the true baseline (TSD 3, Section 4.4,
  "regression to the mean").

Section 4.5.1 of TSD 3 concerns treatment by covariate interactions estimated from individual
patient data with two covariates, the trial mean and the individual value minus the trial mean;
it does not specify intercepts. The main-effect form used here (the slope of an outcome on a
covariate) and the common intercept of `wbRSS` are simplifications made here: a model with trial
fixed effects and a separate term `β_B x̄_i` is not identified (the term is collinear with the
trial intercepts). The interaction model itself, with the two interaction columns, is in
`BiasAnalysis/EcologicalInteraction.lean`.
Regression to the mean is stated for population least squares slopes with uncorrelated (not
necessarily independent) errors, using `slope` of `BiasAnalysis/MeasurementError.lean`; the
error `e_C` enters both the regressor and the outcome, so the classical error model of that
file does not apply.

## References

* S. Dias, A. J. Sutton, N. J. Welton, A. E. Ades, *NICE DSU Technical Support Document 3:
  Heterogeneity: Subgroups, Meta-Regression, Bias and Bias-Adjustment* (2011, updated 2012),
  Sections 1.1.2, 4.4 and 4.5.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace CausalInference.BiasAnalysis.EcologicalBias

open MeasurementError

/-! ### Regression to the mean in baseline-risk regression -/

section RegressionToMean

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Regression to the mean against the observed baseline** (TSD 3, Section 4.4: naive
approaches "which regress against the observed baseline risk fail to take into account the
correlation between the treatment effect and baseline risk, and the consequent regression to the
mean phenomenon"). A trial has true baseline `μ` (control arm, linear predictor scale) and true
treatment effect `δ`. The observed control arm is `μ + e_C` and the observed treated arm is
`μ + δ + e_T`, so the observed effect is `δ + e_T - e_C`: the control arm error enters the
observed baseline and, with the opposite sign, the observed effect. If the errors are
uncorrelated with each other and with `μ`, and `e_C` is uncorrelated with `δ`, the population
least squares slope of the observed effect on the observed baseline is
`(Cov(μ, δ) - Var(e_C)) / (Var(μ) + Var(e_C))`, not the slope `Cov(μ, δ) / Var(μ)` of the true
effect on the true baseline. The positivity hypothesis excludes the degenerate case in which
the slope is not defined. -/
theorem slope_observed_baseline {μb δ eC eT : Ω → ℝ} (hμ : MemLp μb 2 P) (hδ : MemLp δ 2 P)
    (hC : MemLp eC 2 P) (hT : MemLp eT 2 P) (h1 : cov[μb, eC; P] = 0)
    (h2 : cov[μb, eT; P] = 0) (h3 : cov[eC, δ; P] = 0) (h4 : cov[eC, eT; P] = 0)
    (_hpos : 0 < Var[μb; P] + Var[eC; P]) :
    MeasurementError.slope P (μb + eC) (δ + eT - eC) =
      (cov[μb, δ; P] - Var[eC; P]) / (Var[μb; P] + Var[eC; P]) := by
  rw [MeasurementError.slope, variance_add_of_cov_eq_zero hμ hC h1,
    covariance_add_left hμ hC ((hδ.add hT).sub hC),
    covariance_sub_right hμ (hδ.add hT) hC, covariance_sub_right hC (hδ.add hT) hC,
    covariance_add_right hμ hδ hT, covariance_add_right hC hδ hT,
    covariance_self hC.aemeasurable, h1, h2, h3, h4]
  ring

/-- **A negative slope against the observed baseline.** Under the hypotheses of
`slope_observed_baseline`, if the true effect is uncorrelated with the true baseline and the
baseline is measured with error of positive variance, the slope of the observed effect on the
observed baseline is `-Var(e_C) / (Var(μ) + Var(e_C)) < 0`. No condition on `Var(μ)` is needed;
in particular this holds even when the true baseline is constant. -/
theorem slope_observed_baseline_lt_zero {μb δ eC eT : Ω → ℝ} (hμ : MemLp μb 2 P)
    (hδ : MemLp δ 2 P) (hC : MemLp eC 2 P) (hT : MemLp eT 2 P) (h1 : cov[μb, eC; P] = 0)
    (h2 : cov[μb, eT; P] = 0) (h3 : cov[eC, δ; P] = 0) (h4 : cov[eC, eT; P] = 0)
    (h0 : cov[μb, δ; P] = 0) (hvar : 0 < Var[eC; P]) :
    MeasurementError.slope P (μb + eC) (δ + eT - eC) =
        -Var[eC; P] / (Var[μb; P] + Var[eC; P]) ∧
      MeasurementError.slope P (μb + eC) (δ + eT - eC) < 0 := by
  have hs := slope_observed_baseline hμ hδ hC hT h1 h2 h3 h4
    (by linarith [variance_nonneg μb P])
  rw [h0, zero_sub] at hs
  refine ⟨hs, ?_⟩
  rw [hs]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hvar) (by linarith [variance_nonneg μb P])

/-- **A spurious negative slope.** Under the hypotheses of `slope_observed_baseline`, if the true
baseline varies (`0 < Var(μ)`, so that the slope of `δ` on `μ` is defined) and the true effect is
uncorrelated with it (so that slope is `0`), and the baseline is measured with error of positive
variance, the slope of the observed effect on the observed baseline is
`-Var(e_C) / (Var(μ) + Var(e_C)) < 0` (`slope_observed_baseline_lt_zero`). -/
theorem slope_observed_baseline_neg {μb δ eC eT : Ω → ℝ} (hμ : MemLp μb 2 P) (hδ : MemLp δ 2 P)
    (hC : MemLp eC 2 P) (hT : MemLp eT 2 P) (h1 : cov[μb, eC; P] = 0)
    (h2 : cov[μb, eT; P] = 0) (h3 : cov[eC, δ; P] = 0) (h4 : cov[eC, eT; P] = 0)
    (h0 : cov[μb, δ; P] = 0) (_hμv : 0 < Var[μb; P]) (hvar : 0 < Var[eC; P]) :
    MeasurementError.slope P μb δ = 0 ∧
      MeasurementError.slope P (μb + eC) (δ + eT - eC) =
        -Var[eC; P] / (Var[μb; P] + Var[eC; P]) ∧
      MeasurementError.slope P (μb + eC) (δ + eT - eC) < 0 :=
  ⟨by rw [MeasurementError.slope, h0, zero_div],
    slope_observed_baseline_lt_zero hμ hδ hC hT h1 h2 h3 h4 h0 hvar⟩

end RegressionToMean

section RegressionToMeanExample

open LinearIVExample IVModel

/-- **Countermodel: naive baseline-risk regression.** On two fair coins let the true baseline
`μ` be the first coin, the baseline error `e_C` the second coin, and the true effect `δ` and the
error `e_T` be `0`. All hypotheses of `slope_observed_baseline_neg` hold (the true baseline has
variance `1/4`) and the true effect does not depend on the baseline at all, yet the slope of
the observed effect `-e_C` on the observed baseline `μ + e_C` is `-1/2`. -/
theorem regression_to_mean_example :
    let μb : Bool × Bool → ℝ := fun ω => boolToReal ω.1
    let eC : Bool × Bool → ℝ := fun ω => boolToReal ω.2
    let z : Bool × Bool → ℝ := fun _ => 0
    MemLp μb 2 coins ∧ MemLp eC 2 coins ∧ MemLp z 2 coins ∧ cov[μb, eC; coins] = 0 ∧
      cov[μb, z; coins] = 0 ∧ cov[eC, z; coins] = 0 ∧ Var[μb; coins] = 1 / 4 ∧
      Var[eC; coins] = 1 / 4 ∧ MeasurementError.slope coins μb z = 0 ∧
      MeasurementError.slope coins (μb + eC) (z + z - eC) = -1 / 2 := by
  intro μb eC z
  have hb : ∀ b : Bool, |boolToReal b| ≤ 2 := fun b => by cases b <;> norm_num [boolToReal]
  refine ⟨memLp_coins fun ω => hb _, memLp_coins fun ω => hb _, memLp_const 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [MeasurementError.slope, ← covariance_self (measurable_of_countable _).aemeasurable,
      covariance, integral_coins, Pi.add_apply, Pi.sub_apply, μb, eC, z, boolToReal]
    norm_num

end RegressionToMeanExample

/-! ### Within-trial and between-trial slopes -/

section WithinBetween

variable {ι I : Type*} [Fintype ι] [Finite I] [DecidableEq I] (tr : ι → I)

/-- The number of patients of trial `i`; `tr j` is the trial of patient `j`. -/
def trialSize (i : I) : ℕ := #{j | tr j = i}

/-- The trial mean `x̄_i` of a patient-level variable `x`. For a trial label with no patient the
value is `0` (division by zero) and has no meaning; `betweenSlope` uses populated trials only. -/
noncomputable def trialMean (x : ι → ℝ) (i : I) : ℝ := (∑ j with tr j = i, x j) / trialSize tr i

/-- The deviation `x_j - x̄_{tr j}` of a patient-level value from its trial mean. -/
noncomputable def dev (x : ι → ℝ) (j : ι) : ℝ := x j - trialMean tr x (tr j)

/-- **The pooled within-trial slope** `∑ (x - x̄)(y - ȳ) / ∑ (x - x̄)²`, deviations taken from
the trial means. It is meaningful when the covariate varies within some trial
(`0 < ∑ (x - x̄)²`). -/
noncomputable def withinSlope (x y : ι → ℝ) : ℝ :=
  (∑ j, dev tr x j * dev tr y j) / ∑ j, dev tr x j ^ 2

variable {tr}

/-- Deviations from the trial means sum to zero against any trial-level quantity. -/
theorem sum_dev_mul_trial (x : ι → ℝ) (g : I → ℝ) : ∑ j, dev tr x j * g (tr j) = 0 := by
  have := Fintype.ofFinite I
  rw [← Finset.sum_fiberwise Finset.univ tr]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : ∀ j ∈ ({j | tr j = i} : Finset ι), dev tr x j * g (tr j) =
      g i * (x j - trialMean tr x i) := by
    intro j hj
    rw [(Finset.mem_filter.1 hj).2]; unfold dev; rw [(Finset.mem_filter.1 hj).2]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
    nsmul_eq_mul]
  by_cases hn : (trialSize tr i : ℝ) = 0
  · have h0 : ({j | tr j = i} : Finset ι) = ∅ := by
      rw [← Finset.card_eq_zero]; exact_mod_cast hn
    simp [h0]
  · unfold trialMean
    change g i * (_ - (trialSize tr i : ℝ) * _) = 0
    rw [mul_div_cancel₀ _ hn, sub_self, mul_zero]

omit [Finite I] in
/-- The trial mean of a trial-level quantity is that quantity, on every nonempty trial. -/
theorem trialMean_trial (g : I → ℝ) (j : ι) :
    trialMean tr (fun k => g (tr k)) (tr j) = g (tr j) := by
  unfold trialMean
  have hpos : (trialSize tr (tr j) : ℝ) ≠ 0 := by
    have : 0 < trialSize tr (tr j) := Finset.card_pos.2 ⟨j, by simp⟩
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl (g := fun _ => g (tr j)) fun k hk => by
    simp only [(Finset.mem_filter.1 hk).2], Finset.sum_const,
    nsmul_eq_mul]
  change (trialSize tr (tr j) : ℝ) * g (tr j) / _ = _
  field_simp

omit [Finite I] in
/-- Adding a trial-level term to every patient of a trial leaves the deviations unchanged. -/
theorem dev_add_trial (y : ι → ℝ) (g : I → ℝ) :
    dev tr (fun k => y k + g (tr k)) = dev tr y := by
  funext j
  have : trialMean tr (fun k => y k + g (tr k)) (tr j) =
      trialMean tr y (tr j) + trialMean tr (fun k => g (tr k)) (tr j) := by
    unfold trialMean; rw [Finset.sum_add_distrib, add_div]
  unfold dev
  rw [this, trialMean_trial]
  ring

omit [Finite I] in
/-- **The within-trial slope is invariant to additive trial terms.** Adding a trial-level term
`g (tr j)` to the outcome, such as an additive effect of an unmeasured trial characteristic,
does not change the pooled within-trial slope. This is the linear demeaning step behind the
within-trial analysis of TSD 3, Section 4.5.1 (whose within-trial estimate "is free from
ecological/aggregation biases and other potential sources of confounding between studies");
no causal model is formalized, and a trial-specific change of the slope, a term
`g_i (x_j - x̄_i)`, is not removed. -/
theorem withinSlope_add_trial (x y : ι → ℝ) (g : I → ℝ) :
    withinSlope tr x (fun k => y k + g (tr k)) = withinSlope tr x y := by
  unfold withinSlope; rw [dev_add_trial]

omit [Finite I] in
/-- The within-trial residual sum of squares at slope `b` is its minimum, attained at the
pooled within-trial slope, plus `(b - β_W)² ∑ (x - x̄)²`. -/
theorem sum_sq_dev_sub (x y : ι → ℝ) (b : ℝ) (hD : ∑ j, dev tr x j ^ 2 ≠ 0) :
    ∑ j, (dev tr y j - b * dev tr x j) ^ 2 =
      ∑ j, (dev tr y j - withinSlope tr x y * dev tr x j) ^ 2 +
        (b - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 := by
  have e : ∀ c : ℝ, ∑ j, (dev tr y j - c * dev tr x j) ^ 2 = ∑ j, dev tr y j ^ 2 -
      2 * c * ∑ j, dev tr x j * dev tr y j + c ^ 2 * ∑ j, dev tr x j ^ 2 := by
    intro c
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · congr 1; exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, e, withinSlope]
  field_simp
  ring

/-- Splitting a residual into its within-trial and trial-level parts: for any slope `b` on the
deviations and any trial-level fitted value `c`, the residual sum of squares is the within-trial
part plus the trial-level part, with no cross term. -/
theorem sum_sq_split (x y : ι → ℝ) (b : ℝ) (c : I → ℝ) :
    ∑ j, (y j - b * dev tr x j - c (tr j)) ^ 2 =
      ∑ j, (dev tr y j - b * dev tr x j) ^ 2 + ∑ j, (trialMean tr y (tr j) - c (tr j)) ^ 2 := by
  have hcross : ∑ j, (dev tr y j - b * dev tr x j) * (trialMean tr y (tr j) - c (tr j)) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
    rw [sum_dev_mul_trial y (fun i => trialMean tr y i - c i), ← Finset.mul_sum,
      sum_dev_mul_trial x (fun i => trialMean tr y i - c i)]
    ring
  have : ∀ j, (y j - b * dev tr x j - c (tr j)) ^ 2 = (dev tr y j - b * dev tr x j) ^ 2 +
      2 * ((dev tr y j - b * dev tr x j) * (trialMean tr y (tr j) - c (tr j))) +
      (trialMean tr y (tr j) - c (tr j)) ^ 2 := fun j => by unfold dev; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
  ring

/-- The residual sum of squares of the fixed-effects model `y_j = α_{tr j} + β x_j`. -/
noncomputable def feRSS (tr : ι → I) (x y : ι → ℝ) (α : I → ℝ) (β : ℝ) : ℝ :=
  ∑ j, (y j - α (tr j) - β * x j) ^ 2

/-- **Least squares with trial fixed effects** (the main-effect analogue of the within-trial
coefficient of TSD 3, Section 4.5.1). In the model `y_j = α_{tr j} + β x_j` with a free
intercept for every trial, the least squares slope is the pooled within-trial slope `β_W`,
with intercepts `α̂_i = ȳ_i - β_W x̄_i`, and it is the unique least squares slope when the
covariate varies within some trial. -/
theorem feRSS_le (x y : ι → ℝ) (hD : 0 < ∑ j, dev tr x j ^ 2) (α : I → ℝ) (β : ℝ) :
    feRSS tr x y (fun i => trialMean tr y i - withinSlope tr x y * trialMean tr x i)
        (withinSlope tr x y) ≤ feRSS tr x y α β ∧
      (feRSS tr x y α β = feRSS tr x y
          (fun i => trialMean tr y i - withinSlope tr x y * trialMean tr x i)
          (withinSlope tr x y) → β = withinSlope tr x y) := by
  have hsplit : ∀ (α : I → ℝ) (β : ℝ), feRSS tr x y α β =
      ∑ j, (dev tr y j - withinSlope tr x y * dev tr x j) ^ 2 +
        (β - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 +
        ∑ j, (trialMean tr y (tr j) - (α (tr j) + β * trialMean tr x (tr j))) ^ 2 := by
    intro α β
    rw [← sum_sq_dev_sub x y β hD.ne', ← sum_sq_split x y β (fun i => α i + β * trialMean tr x i),
      feRSS]
    exact Finset.sum_congr rfl fun j _ => by unfold dev; ring
  rw [hsplit, hsplit]
  have h0 : ∑ j, (trialMean tr y (tr j) - ((trialMean tr y (tr j) -
      withinSlope tr x y * trialMean tr x (tr j)) + withinSlope tr x y *
        trialMean tr x (tr j))) ^ 2 = 0 := by simp
  rw [h0, sub_self]
  have hT : 0 ≤ ∑ j, (trialMean tr y (tr j) - (α (tr j) + β * trialMean tr x (tr j))) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hQ : 0 ≤ (β - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 :=
    mul_nonneg (sq_nonneg _) hD.le
  refine ⟨by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    add_zero]; linarith, fun h => ?_⟩
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero] at h
  have : (β - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
  · exact absurd h' hD.ne'

/-- The residual sum of squares of the within and between model
`y_j = a + b_W (x_j - x̄_{tr j}) + b_B x̄_{tr j}`: one covariate for the deviation from the trial
mean and one for the trial mean, the two covariates of TSD 3, Section 4.5.1. The main-effect
form and the common intercept `a` are simplifications made here; the document uses these
covariates in treatment by covariate interactions and does not specify intercepts. -/
noncomputable def wbRSS (tr : ι → I) (x y : ι → ℝ) (a bW bB : ℝ) : ℝ :=
  ∑ j, (y j - a - bW * dev tr x j - bB * trialMean tr x (tr j)) ^ 2

/-- The residual sum of squares of the within and between model splits into the minimal
within-trial part, the within-trial penalty `(b_W - β_W)² ∑ (x - x̄)²`, and the patient-level
residual sum of squares of the trial means `∑ⱼ (ȳ_{tr j} - a - b_B x̄_{tr j})²`. -/
theorem wbRSS_split (x y : ι → ℝ) (hD : ∑ j, dev tr x j ^ 2 ≠ 0) (a bW bB : ℝ) :
    wbRSS tr x y a bW bB =
      ∑ j, (dev tr y j - withinSlope tr x y * dev tr x j) ^ 2 +
        (bW - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 +
        ∑ j, (trialMean tr y (tr j) - a - bB * trialMean tr x (tr j)) ^ 2 := by
  have e : ∑ j, (trialMean tr y (tr j) - a - bB * trialMean tr x (tr j)) ^ 2 =
      ∑ j, (trialMean tr y (tr j) - (a + bB * trialMean tr x (tr j))) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by ring
  rw [e, ← sum_sq_dev_sub x y bW hD, ← sum_sq_split x y bW (fun i => a + bB * trialMean tr x i),
    wbRSS]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The within coefficient of the within and between model is the pooled within-trial slope.**
Whatever the intercept `a` and the between coefficient `b_B`, the residual sum of squares is
minimized in `b_W` exactly at the pooled within-trial slope `β_W`, which does not change when
additive trial-level terms are added to the outcome (`withinSlope_add_trial`). The two
coefficients are estimated from orthogonal parts of the data (`wbRSS_split`). -/
theorem wbRSS_le (x y : ι → ℝ) (hD : 0 < ∑ j, dev tr x j ^ 2) (a bW bB : ℝ) :
    wbRSS tr x y a (withinSlope tr x y) bB ≤ wbRSS tr x y a bW bB ∧
      (wbRSS tr x y a bW bB = wbRSS tr x y a (withinSlope tr x y) bB →
        bW = withinSlope tr x y) := by
  rw [wbRSS_split x y hD.ne', wbRSS_split x y hD.ne', sub_self]
  have hQ : 0 ≤ (bW - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 :=
    mul_nonneg (sq_nonneg _) hD.le
  refine ⟨by simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
    add_zero]; linarith, fun h => ?_⟩
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero] at h
  have : (bW - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h')
  · exact absurd h' hD.ne'

end WithinBetween

/-! ### The ecological fallacy -/

section Ecological

variable {I : Type*} [Fintype I]

/-- The least squares slope `∑ (a - ā)(b - b̄) / ∑ (a - ā)²` of `b` on `a` over a finite set
of units with equal weights; meaningful when `a` is not constant. -/
noncomputable def lsSlope (a b : I → ℝ) : ℝ :=
  (∑ i, (a i - (∑ k, a k) / Fintype.card I) * (b i - (∑ k, b k) / Fintype.card I)) /
    ∑ i, (a i - (∑ k, a k) / Fintype.card I) ^ 2

/-- The least squares slope does not depend on how the units are labeled. -/
theorem lsSlope_comp_equiv {J : Type*} [Fintype J] (e : J ≃ I) (a b : I → ℝ) :
    lsSlope (a ∘ e) (b ∘ e) = lsSlope a b := by
  have hc : Fintype.card J = Fintype.card I := Fintype.card_congr e
  simp only [lsSlope, Function.comp_apply, hc, Equiv.sum_comp e
    (fun i => (a i - (∑ k, a k) / Fintype.card I) * (b i - (∑ k, b k) / Fintype.card I)),
    Equiv.sum_comp e (fun i => (a i - (∑ k, a k) / Fintype.card I) ^ 2), Equiv.sum_comp e a,
    Equiv.sum_comp e b]

/-- The least squares intercept `b̄ - lsSlope a b * ā` of `b` on `a`, with equal weights. -/
noncomputable def lsIntercept (a b : I → ℝ) : ℝ :=
  (∑ k, b k) / Fintype.card I - lsSlope a b * ((∑ k, a k) / Fintype.card I)

/-- **The least squares decomposition.** If `u` is not constant (`Sxx ≠ 0`), the residual sum of
squares of the line `a + b u` is its value at `(lsIntercept, lsSlope)` plus
`n (â - a + (b̂ - b) ū)² + Sxx (b̂ - b)²`. -/
theorem lsRSS_eq (u v : I → ℝ) (hS : ∑ i, (u i - (∑ k, u k) / Fintype.card I) ^ 2 ≠ 0)
    (a b : ℝ) :
    ∑ i, (v i - a - b * u i) ^ 2 = ∑ i, (v i - lsIntercept u v - lsSlope u v * u i) ^ 2 +
      (Fintype.card I : ℝ) * (lsIntercept u v - a + (lsSlope u v - b) *
        ((∑ k, u k) / Fintype.card I)) ^ 2 +
      (∑ i, (u i - (∑ k, u k) / Fintype.card I) ^ 2) * (lsSlope u v - b) ^ 2 := by
  set n : ℝ := (Fintype.card I : ℝ) with hn_def
  have hn : n ≠ 0 := by
    intro h
    apply hS
    have : IsEmpty I := Fintype.card_eq_zero_iff.1 (by rw [hn_def] at h; exact_mod_cast h)
    simp
  set Su := ∑ i, u i
  set Sv := ∑ i, v i
  set Suu := ∑ i, u i ^ 2
  set Suv := ∑ i, u i * v i
  set Svv := ∑ i, v i ^ 2
  have hR : ∀ a b, ∑ i, (v i - a - b * u i) ^ 2 =
      Svv - 2 * a * Sv - 2 * b * Suv + a ^ 2 * n + 2 * a * b * Su + b ^ 2 * Suu := by
    intro a b
    have : ∀ i, (v i - a - b * u i) ^ 2 = v i ^ 2 - 2 * a * v i - 2 * b * (u i * v i) + a ^ 2 +
        2 * a * b * u i + b ^ 2 * u i ^ 2 := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Svv, Sv, Suv, Su, Suu, n]
    ring
  have hSxx : ∑ i, (u i - Su / n) ^ 2 = (n * Suu - Su ^ 2) / n := by
    have : ∀ i, (u i - Su / n) ^ 2 = u i ^ 2 - 2 * (Su / n) * u i + (Su / n) ^ 2 :=
      fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hSxy : ∑ i, (u i - Su / n) * (v i - Sv / n) = (n * Suv - Su * Sv) / n := by
    have : ∀ i, (u i - Su / n) * (v i - Sv / n) =
        u i * v i - (Su / n) * v i - (Sv / n) * u i + Su / n * (Sv / n) := fun i => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hD : n * Suu - Su ^ 2 ≠ 0 := by
    intro h; apply hS; rw [hSxx, h, zero_div]
  have hb : lsSlope u v = (n * Suv - Su * Sv) / (n * Suu - Su ^ 2) := by
    rw [lsSlope, hSxy, hSxx]; field_simp
  have ha : lsIntercept u v = Sv / n - lsSlope u v * (Su / n) := rfl
  rw [hR, hR, ha, hSxx, hb]
  field_simp
  ring

/-- **The least squares line.** If `u` is not constant, `(lsIntercept u v, lsSlope u v)` is the
unique minimizer of the residual sum of squares `∑ (v - a - b u)²`. -/
theorem lsRSS_le (u v : I → ℝ) (hS : 0 < ∑ i, (u i - (∑ k, u k) / Fintype.card I) ^ 2)
    (a b : ℝ) :
    ∑ i, (v i - lsIntercept u v - lsSlope u v * u i) ^ 2 ≤ ∑ i, (v i - a - b * u i) ^ 2 ∧
      (∑ i, (v i - a - b * u i) ^ 2 = ∑ i, (v i - lsIntercept u v - lsSlope u v * u i) ^ 2 →
        a = lsIntercept u v ∧ b = lsSlope u v) := by
  rw [lsRSS_eq u v hS.ne' a b]
  have hn : (0 : ℝ) < Fintype.card I := by
    rcases (Fintype.card I).eq_zero_or_pos with h | h
    · have : IsEmpty I := Fintype.card_eq_zero_iff.1 h
      simp at hS
    · exact_mod_cast h
  have h1 : 0 ≤ (Fintype.card I : ℝ) * (lsIntercept u v - a + (lsSlope u v - b) *
      ((∑ k, u k) / Fintype.card I)) ^ 2 := mul_nonneg hn.le (sq_nonneg _)
  have h2 : 0 ≤ (∑ i, (u i - (∑ k, u k) / Fintype.card I) ^ 2) * (lsSlope u v - b) ^ 2 :=
    mul_nonneg hS.le (sq_nonneg _)
  refine ⟨by linarith, fun h => ?_⟩
  have e2 : (∑ i, (u i - (∑ k, u k) / Fintype.card I) ^ 2) * (lsSlope u v - b) ^ 2 = 0 := by
    linarith
  have e1 : (Fintype.card I : ℝ) * (lsIntercept u v - a + (lsSlope u v - b) *
      ((∑ k, u k) / Fintype.card I)) ^ 2 = 0 := by linarith
  rw [mul_eq_zero, or_iff_right hS.ne', sq_eq_zero_iff, sub_eq_zero] at e2
  rw [mul_eq_zero, or_iff_right hn.ne', sq_eq_zero_iff, e2, sub_self, zero_mul, add_zero,
    sub_eq_zero] at e1
  exact ⟨e1.symm, e2.symm⟩

end Ecological

section Between

variable {ι I : Type*} [Fintype ι] [DecidableEq I]

/-- **The between-trial slope**: the least squares slope of the trial mean outcome on the trial
mean covariate, one point per populated trial (`Set.range tr`), with equal weights, as in a
meta-regression on aggregate data. Trial labels with no patient do not enter. It is meaningful
when the trial mean covariate is not constant over the populated trials. -/
noncomputable def betweenSlope (tr : ι → I) (x y : ι → ℝ) : ℝ :=
  lsSlope (fun i : Set.range tr => trialMean tr x i) (fun i : Set.range tr => trialMean tr y i)

/-- The between-trial slope computed from any enumeration `e` of the populated trials. -/
theorem betweenSlope_eq_of_equiv {J : Type*} [Fintype J] (tr : ι → I) (x y : ι → ℝ)
    (e : J ≃ Set.range tr) :
    betweenSlope tr x y =
      lsSlope (fun j => trialMean tr x (e j)) (fun j => trialMean tr y (e j)) :=
  (lsSlope_comp_equiv e _ _).symm

/-- When every trial label is populated, the between-trial slope is the least squares slope over
all labels. -/
theorem betweenSlope_eq_of_surjective [Fintype I] {tr : ι → I} (htr : Function.Surjective tr)
    (x y : ι → ℝ) : betweenSlope tr x y = lsSlope (trialMean tr x) (trialMean tr y) :=
  betweenSlope_eq_of_equiv tr x y
    (Equiv.ofBijective (fun i => (⟨i, htr i⟩ : Set.range tr))
      ⟨fun _ _ h => congrArg Subtype.val h, fun ⟨i, _⟩ => ⟨i, rfl⟩⟩)

/-- **Countermodel: an unused trial label.** Two patients, one per trial, with covariates `1, 2`
and outcomes `3, 4`. With the labels `Fin 2` the least squares slope of the trial means over all
labels is `1`. Adding a third, unused label (`Fin.castSucc : Fin 2 → Fin 3`) makes the trial
means of the empty trial `0` (division by zero), and the slope over all labels becomes `2`
without any change in the data. `betweenSlope`, which uses only populated trials, is `1` for
both labelings. -/
theorem betweenSlope_unused_label :
    lsSlope (trialMean (id : Fin 2 → Fin 2) ![1, 2]) (trialMean id ![3, 4]) = 1 ∧
      lsSlope (trialMean (Fin.castSucc : Fin 2 → Fin 3) ![1, 2])
        (trialMean Fin.castSucc ![3, 4]) = 2 ∧
      betweenSlope (id : Fin 2 → Fin 2) ![1, 2] ![3, 4] = 1 ∧
      betweenSlope (Fin.castSucc : Fin 2 → Fin 3) ![1, 2] ![3, 4] = 1 := by
  have h1 : ∀ (z : Fin 2 → ℝ) (i : Fin 2), trialMean (id : Fin 2 → Fin 2) z i = z i := by
    intro z i
    simp [trialMean, trialSize, Finset.filter_eq']
  have h2 : ∀ (z : Fin 2 → ℝ) (i : Fin 2),
      trialMean (Fin.castSucc : Fin 2 → Fin 3) z (Fin.castSucc i) = z i := by
    intro z i
    simp [trialMean, trialSize, Fin.castSucc_inj, Finset.filter_eq']
  have h3 : ∀ z : Fin 2 → ℝ, trialMean (Fin.castSucc : Fin 2 → Fin 3) z (Fin.last 2) = 0 := by
    intro z
    simp [trialMean, trialSize]
  have hA : lsSlope (trialMean (id : Fin 2 → Fin 2) ![1, 2]) (trialMean id ![3, 4]) = 1 := by
    simp only [lsSlope, h1, Fin.sum_univ_two, Fintype.card_fin, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have hC : betweenSlope (Fin.castSucc : Fin 2 → Fin 3) ![1, 2] ![3, 4] = 1 := by
    rw [betweenSlope_eq_of_equiv _ _ _ (Equiv.ofBijective
      (fun i => (⟨Fin.castSucc i, Set.mem_range_self i⟩ :
        Set.range (Fin.castSucc : Fin 2 → Fin 3)))
      ⟨fun _ _ h => Fin.castSucc_inj.1 (congrArg Subtype.val h),
        fun ⟨_, i, hi⟩ => ⟨i, Subtype.ext hi⟩⟩)]
    change lsSlope (fun j => trialMean Fin.castSucc ![1, 2] (Fin.castSucc j))
      (fun j => trialMean Fin.castSucc ![3, 4] (Fin.castSucc j)) = 1
    simp only [h2]
    have h1' : ∀ z, trialMean (id : Fin 2 → Fin 2) z = z := fun z => funext (h1 z)
    rw [h1', h1'] at hA
    exact hA
  refine ⟨hA, ?_, ?_, hC⟩
  · simp only [lsSlope, Fin.sum_univ_castSucc, Fintype.card_fin, h2, h3]
    norm_num
  · rw [betweenSlope_eq_of_surjective Function.surjective_id, hA]

end Between

/-! ### The between coefficient of the within and between model -/

section WithinBetweenFit

variable {ι I : Type*} [Fintype ι] [Fintype I] [DecidableEq I] {tr : ι → I}

/-- **The trial-size weighted between-trial slope**: the least squares slope of `ȳ_{tr j}` on
`x̄_{tr j}` over patients, that is, the regression of the trial means in which each trial is
weighted by its number of patients (`sizeWeightedBetweenSlope_eq`). Empty trials get weight
`0`. It differs from the equal-weight `betweenSlope` unless the trials have equal sizes. -/
noncomputable def sizeWeightedBetweenSlope (tr : ι → I) (x y : ι → ℝ) : ℝ :=
  lsSlope (fun j => trialMean tr x (tr j)) (fun j => trialMean tr y (tr j))

/-- A sum over patients of a trial-level quantity is the sum over trials weighted by trial
size. -/
theorem sum_comp_trial (f : I → ℝ) :
    ∑ j, f (tr j) = ∑ i, (trialSize tr i : ℝ) * f i := by
  rw [← Finset.sum_fiberwise Finset.univ tr]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.1 hj).2], Finset.sum_const,
    nsmul_eq_mul]
  rfl

/-- **The between slope weighted by trial size.** With `n_i` the size of trial `i` and
`m_x = ∑ n_i x̄_i / ∑ n_i`, `m_y = ∑ n_i ȳ_i / ∑ n_i` the size-weighted means of the trial means,
`sizeWeightedBetweenSlope = ∑ n_i (x̄_i - m_x)(ȳ_i - m_y) / ∑ n_i (x̄_i - m_x)²`. -/
theorem sizeWeightedBetweenSlope_eq (x y : ι → ℝ) :
    sizeWeightedBetweenSlope tr x y =
      (∑ i, (trialSize tr i : ℝ) *
          ((trialMean tr x i - (∑ k, (trialSize tr k : ℝ) * trialMean tr x k) /
              ∑ k, (trialSize tr k : ℝ)) *
            (trialMean tr y i - (∑ k, (trialSize tr k : ℝ) * trialMean tr y k) /
              ∑ k, (trialSize tr k : ℝ)))) /
        ∑ i, (trialSize tr i : ℝ) *
          (trialMean tr x i - (∑ k, (trialSize tr k : ℝ) * trialMean tr x k) /
            ∑ k, (trialSize tr k : ℝ)) ^ 2 := by
  have hc : (Fintype.card ι : ℝ) = ∑ k, (trialSize tr k : ℝ) := by
    have := sum_comp_trial (tr := tr) (fun _ => (1 : ℝ))
    simpa using this
  simp only [sizeWeightedBetweenSlope, lsSlope, hc]
  rw [sum_comp_trial (trialMean tr x), sum_comp_trial (trialMean tr y),
    sum_comp_trial (fun i => (trialMean tr x i - (∑ k, (trialSize tr k : ℝ) * trialMean tr x k) /
      ∑ k, (trialSize tr k : ℝ)) * (trialMean tr y i - (∑ k, (trialSize tr k : ℝ) *
        trialMean tr y k) / ∑ k, (trialSize tr k : ℝ))),
    sum_comp_trial (fun i => (trialMean tr x i - (∑ k, (trialSize tr k : ℝ) * trialMean tr x k) /
      ∑ k, (trialSize tr k : ℝ)) ^ 2)]

omit [Fintype I] in
/-- **Least squares in the within and between model.** In the patient-level model
`y_j = a + b_W (x_j - x̄_{tr j}) + b_B x̄_{tr j}`, if the covariate varies within some trial and
the trial means of the covariate vary across patients, the residual sum of squares has the
unique minimizer `b_W = withinSlope`, `b_B = sizeWeightedBetweenSlope` (the regression of the
trial means weighted by trial size, not the equal-weight `betweenSlope`), and `a` the
corresponding least squares intercept. -/
theorem wbRSS_min [Finite I] (x y : ι → ℝ) (hD : 0 < ∑ j, dev tr x j ^ 2)
    (hB : 0 < ∑ j, (trialMean tr x (tr j) -
      (∑ k, trialMean tr x (tr k)) / Fintype.card ι) ^ 2) (a bW bB : ℝ) :
    wbRSS tr x y (lsIntercept (fun j => trialMean tr x (tr j)) (fun j => trialMean tr y (tr j)))
        (withinSlope tr x y) (sizeWeightedBetweenSlope tr x y) ≤ wbRSS tr x y a bW bB ∧
      (wbRSS tr x y a bW bB = wbRSS tr x y
          (lsIntercept (fun j => trialMean tr x (tr j)) (fun j => trialMean tr y (tr j)))
          (withinSlope tr x y) (sizeWeightedBetweenSlope tr x y) →
        a = lsIntercept (fun j => trialMean tr x (tr j)) (fun j => trialMean tr y (tr j)) ∧
          bW = withinSlope tr x y ∧ bB = sizeWeightedBetweenSlope tr x y) := by
  obtain ⟨hle, huniq⟩ := lsRSS_le (fun j => trialMean tr x (tr j))
    (fun j => trialMean tr y (tr j)) hB a bB
  rw [wbRSS_split x y hD.ne', wbRSS_split x y hD.ne', sub_self]
  have hQ : 0 ≤ (bW - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 :=
    mul_nonneg (sq_nonneg _) hD.le
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero]
  refine ⟨by unfold sizeWeightedBetweenSlope; linarith, fun h => ?_⟩
  unfold sizeWeightedBetweenSlope at h ⊢
  have hT := hle
  have e1 : (bW - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 = 0 := by linarith
  have e2 := huniq (by linarith)
  rcases mul_eq_zero.1 e1 with h' | h'
  · exact ⟨e2.1, sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h'), e2.2⟩
  · exact absurd h' hD.ne'

/-- The pooled within-trial slope among the patients of arm `a` (those with treatment
`A j = a`), deviations taken from the arm-specific trial means. -/
noncomputable def armWithinSlope (tr : ι → I) (A : ι → ℝ) (a : ℝ) (x y : ι → ℝ) : ℝ :=
  withinSlope (fun j : {j // A j = a} => tr j) (fun j => x j) (fun j => y j)

omit [Fintype I] in
/-- **Arm-specific within-trial slopes ignore trial main effects and trial-specific treatment
effects.** Adding `g (trial) + h (trial) * A` to the outcome, a trial-specific intercept and a
trial-specific treatment effect, does not change the within-trial slope in any arm. -/
theorem armWithinSlope_add_trial (A : ι → ℝ) (a : ℝ) (x y : ι → ℝ) (g h : I → ℝ) :
    armWithinSlope tr A a x (fun k => y k + g (tr k) + h (tr k) * A k) =
      armWithinSlope tr A a x y := by
  unfold armWithinSlope
  have e : (fun j : {j // A j = a} => y j + g (tr j) + h (tr j) * A j) =
      fun j : {j // A j = a} => y j + (fun i => g i + h i * a) (tr j) := by
    funext j; rw [j.2]; beta_reduce; ring
  rw [e]
  exact withinSlope_add_trial (tr := fun j : {j // A j = a} => tr j) (fun j => x j)
    (fun j => y j) (fun i => g i + h i * a)

omit [Fintype I] in
/-- **The within-trial treatment by covariate interaction.** The difference
`armWithinSlope 1 - armWithinSlope 0` of the within-trial covariate slopes of the treated and the
control arm, the within-trial estimate of the interaction of treatment with the covariate, is
unchanged by trial-specific intercepts and trial-specific treatment effects
`g (trial) + h (trial) * A`. This is the additive part of the within-trial argument of TSD 3,
Section 4.5.1; a randomized design or a model for the interaction itself is not formalized. -/
theorem armWithinSlope_sub_add_trial (A : ι → ℝ) (x y : ι → ℝ) (g h : I → ℝ) :
    armWithinSlope tr A 1 x (fun k => y k + g (tr k) + h (tr k) * A k) -
        armWithinSlope tr A 0 x (fun k => y k + g (tr k) + h (tr k) * A k) =
      armWithinSlope tr A 1 x y - armWithinSlope tr A 0 x y := by
  rw [armWithinSlope_add_trial, armWithinSlope_add_trial]

/-- **Equal and size weights give different between slopes.** Four patients in three trials of
sizes `1, 1, 2` (`tr = (0, 1, 2, 2)`), with covariates `(0, 1, 2, 2)` and outcomes
`(0, 0, 1, 1)`, so that the trial means are `(0, 0)`, `(1, 0)` and `(2, 1)`. The equal-weight
between slope is `1/2`, while the between coefficient of the patient-level within and between
model (`wbRSS_min`), the size-weighted slope, is `6/11`. -/
theorem betweenSlope_ne_sizeWeighted_example :
    betweenSlope (![0, 1, 2, 2] : Fin 4 → Fin 3) ![0, 1, 2, 2] ![0, 0, 1, 1] = 1 / 2 ∧
      sizeWeightedBetweenSlope (![0, 1, 2, 2] : Fin 4 → Fin 3) ![0, 1, 2, 2] ![0, 0, 1, 1] =
        6 / 11 := by
  set tr : Fin 4 → Fin 3 := ![0, 1, 2, 2] with htr
  have hsurj : Function.Surjective tr := by
    intro i; fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have hn : ∀ i, (trialSize tr i : ℝ) = ![1, 1, 2] i := by
    have h0 : trialSize tr 0 = 1 := by decide
    have h1 : trialSize tr 1 = 1 := by decide
    have h2 : trialSize tr 2 = 2 := by decide
    intro i; fin_cases i <;> simp [h0, h1, h2]
  have hm : ∀ (z : Fin 4 → ℝ) (i : Fin 3), trialMean tr z i =
      (∑ j, if tr j = i then z j else 0) / ![1, 1, 2] i := by
    intro z i; rw [trialMean, hn, Finset.sum_filter]
  have hx : ∀ i, trialMean tr ![0, 1, 2, 2] i = ![0, 1, 2] i := by
    intro i; rw [hm]; fin_cases i <;> simp [htr, Fin.sum_univ_four]
  have hy : ∀ i, trialMean tr ![0, 0, 1, 1] i = ![0, 0, 1] i := by
    intro i; rw [hm]; fin_cases i <;> simp [htr, Fin.sum_univ_four]
  refine ⟨?_, ?_⟩
  · rw [betweenSlope_eq_of_surjective hsurj]
    simp only [lsSlope, hx, hy, Fin.sum_univ_three, Fintype.card_fin]
    simp
    norm_num
  · simp only [sizeWeightedBetweenSlope, lsSlope, hx, hy, Fin.sum_univ_four, Fintype.card_fin]
    simp [htr]
    norm_num

end WithinBetweenFit

/-- Covariate values of the ecological countermodel: two trials (`false`, `true`) of two patients
each; covariate `0, 1` in trial `false` and `2, 3` in trial `true`. -/
noncomputable def ecoX (ω : Bool × Bool) : ℝ := (if ω.1 then 2 else 0) + if ω.2 then 1 else 0

/-- A trial-level term of the ecological countermodel (for example the effect of a trial
characteristic associated with the trial mean covariate): `1` in trial `false`, `-4` in trial
`true`. -/
noncomputable def ecoTrial (i : Bool) : ℝ := if i then -4 else 1

/-- Outcomes of the ecological countermodel: `y = x + ecoTrial (trial)`, so `1, 2` in trial
`false` and `-2, -1` in trial `true`. -/
noncomputable def ecoY (ω : Bool × Bool) : ℝ := ecoX ω + ecoTrial ω.1

/-- **Ecological fallacy** (TSD 3, Section 1.1.2: the between-trial coefficient "can be entirely
different to the coefficient for the within-trial data"). In the countermodel the outcome rises
by one unit per unit of covariate within each trial (slope `1` in each trial, and pooled
within-trial slope `1`), but the
trial means `(1/2, 3/2)` and `(5/2, -3/2)` give a between-trial slope of `-3/2`: opposite sign.
The difference is produced by the trial-level term alone, which the within-trial slope ignores
(`withinSlope_add_trial`). -/
theorem ecological_fallacy_example :
    (∀ i, lsSlope (fun k => ecoX (i, k)) (fun k => ecoY (i, k)) = 1) ∧
      withinSlope Prod.fst ecoX ecoY = 1 ∧ betweenSlope Prod.fst ecoX ecoY = -3 / 2 := by
  have hn : ∀ i : Bool, (trialSize (Prod.fst : Bool × Bool → Bool) i : ℝ) = 2 := by
    intro i; cases i <;> rfl
  have hm : ∀ (x : Bool × Bool → ℝ) (i : Bool),
      trialMean Prod.fst x i = (x (i, false) + x (i, true)) / 2 := by
    intro x i
    rw [trialMean, hn, Finset.sum_filter, Fintype.sum_prod_type]
    cases i <;> simp [add_comm]
  refine ⟨fun i => ?_, ?_, ?_⟩
  · cases i <;> simp only [lsSlope, Fintype.sum_bool, Fintype.card_bool, ecoY, ecoX, ecoTrial] <;>
      norm_num
  · rw [show ecoY = fun ω => ecoX ω + ecoTrial ω.1 from rfl, withinSlope_add_trial, withinSlope]
    simp only [← sq]
    refine div_self ?_
    simp only [dev, hm, Fintype.sum_prod_type, Fintype.sum_bool, ecoX]
    norm_num
  · rw [betweenSlope_eq_of_surjective Prod.fst_surjective]
    simp only [lsSlope, hm, Fintype.sum_bool, Fintype.card_bool, ecoY, ecoX,
      ecoTrial]
    norm_num

end CausalInference.BiasAnalysis.EcologicalBias
