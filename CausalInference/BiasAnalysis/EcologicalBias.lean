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
* `lsSlope`, `betweenSlope tr x y`: the least squares slope of the trial mean outcome on the
  trial mean covariate (aggregate-data meta-regression).
* `feRSS tr x y α β`, `wbRSS tr x y a bW bB`: residual sums of squares of the model with trial
  fixed effects and of the within and between model with a common intercept.

## Main results

* `ecological_fallacy_example`: two trials with slope `1` inside each trial and between-trial
  slope `-3/2` (TSD 3, Section 1.1.2).
* `withinSlope_add_trial`: the within-trial slope does not change when an arbitrary trial-level
  term is added to the outcome; so it is free of confounding by trial characteristics.
* `feRSS_le`: with a free intercept for every trial the least squares slope is the pooled
  within-trial slope, uniquely when the covariate varies within some trial.
* `wbRSS_le`: in the within and between model of Section 4.5.1 the least squares within
  coefficient is the pooled within-trial slope, whatever the intercept and the between
  coefficient.
* `slope_observed_baseline`, `slope_observed_baseline_neg`, `regression_to_mean_example`:
  regressing observed treatment effects on observed baseline risks gives the slope
  `(Cov(μ, δ) - Var(e_C)) / (Var(μ) + Var(e_C))`, so a spurious negative slope when the true
  effect is unrelated to the true baseline (TSD 3, Section 4.4, "regression to the mean").

A model with trial fixed effects and a separate term `β_B x̄_i` is not identified (the term is
collinear with the trial intercepts), so the within and between model is stated with a common
intercept, as Section 4.5.1 describes it. Regression to the mean is stated for population least
squares slopes with uncorrelated (not necessarily independent) errors, using `slope` of
`BiasAnalysis/MeasurementError.lean`; the error `e_C` enters both the regressor and the outcome,
so the classical error model of that file does not apply.

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

/-- **A spurious negative slope.** Under the hypotheses of `slope_observed_baseline`, if the true
effect is uncorrelated with the true baseline (so the slope of `δ` on `μ` is `0`) and the
baseline is measured with error of positive variance, the slope of the observed effect on the
observed baseline is `-Var(e_C) / (Var(μ) + Var(e_C)) < 0`. -/
theorem slope_observed_baseline_neg {μb δ eC eT : Ω → ℝ} (hμ : MemLp μb 2 P) (hδ : MemLp δ 2 P)
    (hC : MemLp eC 2 P) (hT : MemLp eT 2 P) (h1 : cov[μb, eC; P] = 0)
    (h2 : cov[μb, eT; P] = 0) (h3 : cov[eC, δ; P] = 0) (h4 : cov[eC, eT; P] = 0)
    (h0 : cov[μb, δ; P] = 0) (hvar : 0 < Var[eC; P]) :
    MeasurementError.slope P μb δ = 0 ∧
      MeasurementError.slope P (μb + eC) (δ + eT - eC) =
        -Var[eC; P] / (Var[μb; P] + Var[eC; P]) ∧
      MeasurementError.slope P (μb + eC) (δ + eT - eC) < 0 := by
  have hs := slope_observed_baseline hμ hδ hC hT h1 h2 h3 h4
    (by linarith [variance_nonneg μb P])
  rw [h0, zero_sub] at hs
  refine ⟨by rw [MeasurementError.slope, h0, zero_div], hs, ?_⟩
  rw [hs]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hvar) (by linarith [variance_nonneg μb P])

end RegressionToMean

section RegressionToMeanExample

open LinearIVExample IVModel

/-- **Countermodel: naive baseline-risk regression.** On two fair coins let the true baseline
`μ` be the first coin, the baseline error `e_C` the second coin, and the true effect `δ` and the
error `e_T` be `0`. All hypotheses of `slope_observed_baseline` hold and the true effect does not
depend on the baseline at all, yet the slope of the observed effect `-e_C` on the observed
baseline `μ + e_C` is `-1/2`. -/
theorem regression_to_mean_example :
    let μb : Bool × Bool → ℝ := fun ω => boolToReal ω.1
    let eC : Bool × Bool → ℝ := fun ω => boolToReal ω.2
    let z : Bool × Bool → ℝ := fun _ => 0
    MemLp μb 2 coins ∧ MemLp eC 2 coins ∧ MemLp z 2 coins ∧ cov[μb, eC; coins] = 0 ∧
      cov[μb, z; coins] = 0 ∧ cov[eC, z; coins] = 0 ∧
      MeasurementError.slope coins μb z = 0 ∧
      MeasurementError.slope coins (μb + eC) (z + z - eC) = -1 / 2 := by
  intro μb eC z
  have hb : ∀ b : Bool, |boolToReal b| ≤ 2 := fun b => by cases b <;> norm_num [boolToReal]
  refine ⟨memLp_coins fun ω => hb _, memLp_coins fun ω => hb _, memLp_const 0,
    ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [MeasurementError.slope, ← covariance_self (measurable_of_countable _).aemeasurable,
      covariance, integral_coins, Pi.add_apply, Pi.sub_apply, μb, eC, z, boolToReal]
    norm_num

end RegressionToMeanExample

/-! ### Within-trial and between-trial slopes -/

section WithinBetween

variable {ι I : Type*} [Fintype ι] [Finite I] [DecidableEq I] (tr : ι → I)

/-- The number of patients of trial `i`; `tr j` is the trial of patient `j`. -/
def trialSize (i : I) : ℕ := #{j | tr j = i}

/-- The trial mean `x̄_i` of a patient-level variable `x`. -/
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
/-- **The within-trial slope is free of trial-level confounding** (TSD 3, Section 4.5.1: the
within-trial estimate "is free from ecological/aggregation biases and other potential sources of
confounding between studies"). Adding any trial-level term `g (tr j)` to the outcome, such as
the effect of an unmeasured trial characteristic, does not change the pooled within-trial
slope. -/
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

/-- **Least squares with trial fixed effects** (TSD 3, Section 4.5.1, the within-trial
coefficient). In the model `y_j = α_{tr j} + β x_j` with a free intercept for every trial, the
least squares slope is the pooled within-trial slope `β_W`, with intercepts
`α̂_i = ȳ_i - β_W x̄_i`, and it is the unique least squares slope when the covariate varies
within some trial. -/
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
`y_j = a + b_W (x_j - x̄_{tr j}) + b_B x̄_{tr j}` of TSD 3, Section 4.5.1 (one covariate for the
deviation from the trial mean, one for the trial mean, a common intercept). -/
noncomputable def wbRSS (tr : ι → I) (x y : ι → ℝ) (a bW bB : ℝ) : ℝ :=
  ∑ j, (y j - a - bW * dev tr x j - bB * trialMean tr x (tr j)) ^ 2

/-- **The within coefficient of the within and between model is the pooled within-trial slope**
(TSD 3, Section 4.5.1). Whatever the intercept `a` and the between coefficient `b_B`, the
residual sum of squares is minimized in `b_W` exactly at the pooled within-trial slope `β_W`,
which does not change when trial-level terms are added to the outcome
(`withinSlope_add_trial`). The two coefficients are estimated from orthogonal parts of the
data. -/
theorem wbRSS_le (x y : ι → ℝ) (hD : 0 < ∑ j, dev tr x j ^ 2) (a bW bB : ℝ) :
    wbRSS tr x y a (withinSlope tr x y) bB ≤ wbRSS tr x y a bW bB ∧
      (wbRSS tr x y a bW bB = wbRSS tr x y a (withinSlope tr x y) bB →
        bW = withinSlope tr x y) := by
  have hsplit : ∀ b, wbRSS tr x y a b bB =
      ∑ j, (dev tr y j - withinSlope tr x y * dev tr x j) ^ 2 +
        (b - withinSlope tr x y) ^ 2 * ∑ j, dev tr x j ^ 2 +
        ∑ j, (trialMean tr y (tr j) - (a + bB * trialMean tr x (tr j))) ^ 2 := by
    intro b
    rw [← sum_sq_dev_sub x y b hD.ne', ← sum_sq_split x y b (fun i => a + bB * trialMean tr x i),
      wbRSS]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, hsplit, sub_self]
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

/-- **The between-trial slope**: the least squares slope of the trial mean outcome on the trial
mean covariate, one point per trial, as in a meta-regression on aggregate data. -/
noncomputable def betweenSlope {ι : Type*} [Fintype ι] [DecidableEq I] (tr : ι → I)
    (x y : ι → ℝ) : ℝ :=
  lsSlope (trialMean tr x) (trialMean tr y)

end Ecological

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
  · simp only [betweenSlope, lsSlope, hm, Fintype.sum_bool, Fintype.card_bool, ecoY, ecoX,
      ecoTrial]
    norm_num

end CausalInference.BiasAnalysis.EcologicalBias
