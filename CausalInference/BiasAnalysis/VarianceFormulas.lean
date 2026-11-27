/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.DeltaMethod
public import CausalInference.Estimation.ConfidenceInterval

/-!
# Variance formulas and pooling for bias analysis

First-order (delta method) variances of bias-adjusted log odds ratios, and the pooling rules used
with them, from M. P. Fox, R. F. MacLehose and T. L. Lash (2021), *Applying Quantitative Bias
Analysis to Epidemiologic Data*, second edition, Chapter 2 (the 2 by 2 table of Table 2.1 and the
standard error of the log odds ratio in the text after it) and Chapter 10 ("Standard Errors for
Misclassification When Sensitivity and Specificity Are Used", "... When Predictive Values Are
Used", "Predictive Value Weighting", Equations 10.1 to 10.6, 10.20 and 10.21, and the pooling
display of the "Misclassification Example").

Each variance formula is stated as a gradient identity: the partial derivatives of the adjusted
log odds ratio are given by `HasDerivAt` in each argument, and the formula of the book is the
first-order variance `∑ᵢ gᵢ² Var Xᵢ` (`firstOrderVariance`) of independent inputs.
`variance_linearization` shows that this is the exact variance of the linearization
`∑ᵢ gᵢ Xᵢ` for pairwise independent square integrable `Xᵢ`.

Main results:

* `firstOrderVariance_logOddsRatio_eq_woolf`: the Woolf variance `1/a + 1/b + 1/c + 1/d`.
  `logit_sampleMean_isAsymptoticallyLinear` and `integral_sq_logit_influence` derive the per-group
  asymptotic variance `1 / (p (1 - p))` from the delta method of `Estimation/DeltaMethod.lean`.
* `greenland_differential`, `greenland_nondifferential`: Greenland's variances for the
  correction with sensitivity and specificity, with `trueProportion_of_forward` (the correction
  recovers the true proportion) and `logORSeSp_eq_log_direct` (the direct odds ratio formula).
* `marshall_variance`: Marshall's variance for the correction with predictive values
  (Equations 10.4 to 10.6), with `trueProportionPV_eq_true` (Equation 10.4 recovers the truth).
* `pvw_recovers_true`: predictive value weighting reproduces the true row.
* `jackknifeVariance_leaveOneOutMean`: the jackknife variance of the sample mean is `s² / n`.
* `rubinVariance_eq`: Equation 10.21 is Rubin's `W + (1 + 1/M) B`.
* `ivPooledVariance_le`, `firstOrderVariance_ivWeights`: inverse-variance weights minimize the
  variance of a weighted average, with minimum `1 / ∑ (1/Vᵢ)`.
* `forward_eq_se_of_sum_eq_one`, `trueProportion_neg_example`: the correction is undefined at
  `se + sp = 1` and can leave the unit interval.
* `Examples`: the worked numbers of Chapter 2 and Chapter 10, recomputed.

The joint asymptotic normality of several independent estimates (two binomial samples, or a
validation study and a main study) is not formalized: the delta method of the library is
univariate, so the multivariate step is represented by the gradient identities and
`variance_linearization`. The methods are attributed in the chapter to Greenland (1988),
Marshall (1990), Lyles and colleagues (2010) for predictive value weighting, and Rubin for the
combination rules of multiple imputation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace CausalInference

namespace BiasAnalysis.VarianceFormulas

/-! ### First-order (delta method) variance for independent inputs -/

/-- The first-order variance `∑ᵢ gᵢ² vᵢ` of a smooth function of `k` independent estimates with
variances `vᵢ`, where `gᵢ` is the partial derivative of the function in its `i`th argument. -/
def firstOrderVariance {k : ℕ} (grad var : Fin k → ℝ) : ℝ :=
  ∑ i, grad i ^ 2 * var i

/-- **The first-order variance is the variance of the linearization.** If `X₀, …, X_{k-1}` are
square integrable and pairwise independent under a probability measure, then the variance of the
linear combination `∑ᵢ gᵢ Xᵢ` is `∑ᵢ gᵢ² Var Xᵢ`. This is the step of the delta method that turns
a gradient into a variance. -/
theorem variance_linearization {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {k : ℕ} (X : Fin k → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) μ) (g : Fin k → ℝ) :
    Var[fun ω ↦ ∑ i, g i * X i ω; μ] = firstOrderVariance g (fun i ↦ Var[X i; μ]) := by
  have hfn : (fun ω ↦ ∑ i, g i * X i ω) = ∑ i, fun ω ↦ g i * X i ω := by
    ext ω
    simp only [Finset.sum_apply]
  rw [hfn, IndepFun.variance_sum (fun i _ ↦ (hX i).const_mul (g i))]
  · simp only [firstOrderVariance]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact variance_const_mul (g i) (X i) μ
  · intro i _ j _ hij
    exact (hind hij).comp (measurable_const_mul (g i)) (measurable_const_mul (g j))

/-! ### Woolf variance of the log odds ratio -/

/-- The log odds `logit p = log p - log (1 - p)`. For `0 < p < 1` it is `log (p / (1 - p))`
(`logit_eq_log_div`). -/
noncomputable def logit (p : ℝ) : ℝ := Real.log p - Real.log (1 - p)

/-- For `0 < p < 1`, `logit p = log (p / (1 - p))`. -/
theorem logit_eq_log_div {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    logit p = Real.log (p / (1 - p)) := by
  rw [logit, Real.log_div h0.ne' (by linarith)]

/-- The derivative of the log odds at `p ∈ (0, 1)` is `1 / (p (1 - p))`. -/
theorem hasDerivAt_logit {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    HasDerivAt logit (1 / (p * (1 - p))) p := by
  have h1' : (1 : ℝ) - p ≠ 0 := by linarith
  have h := (Real.hasDerivAt_log h0.ne').sub (((hasDerivAt_id' p).const_sub 1).log h1')
  have he : logit = (Real.log - fun y ↦ Real.log (1 - y)) := rfl
  rw [he]
  convert h using 1
  field_simp
  ring

/-- The log odds ratio `logit p₁ - logit p₀` of two exposure proportions (cases and controls, or
exposed and unexposed). -/
noncomputable def logOddsRatio (p₁ p₀ : ℝ) : ℝ := logit p₁ - logit p₀

/-- The Woolf variance `1/a + 1/b + 1/c + 1/d` of the log odds ratio of a 2 by 2 table with
cells `a, b` (first row) and `c, d` (second row). -/
noncomputable def woolfVariance (a b c d : ℝ) : ℝ := 1 / a + 1 / b + 1 / c + 1 / d

/-- With expected cells `a = n₁ p₁`, `b = n₁ (1 - p₁)`, `c = n₀ p₀`, `d = n₀ (1 - p₀)`, the log
odds ratio of the proportions is the logarithm of the cross-product ratio `a d / (b c)`. -/
theorem logOddsRatio_eq_log_crossProduct {n₁ n₀ p₁ p₀ : ℝ} (hn₁ : 0 < n₁) (hn₀ : 0 < n₀)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1) (h₀ : 0 < p₀) (h₀' : p₀ < 1) :
    logOddsRatio p₁ p₀ =
      Real.log ((n₁ * p₁) * (n₀ * (1 - p₀)) / ((n₁ * (1 - p₁)) * (n₀ * p₀))) := by
  have e₁ : 0 < 1 - p₁ := by linarith
  have e₀ : 0 < 1 - p₀ := by linarith
  rw [logOddsRatio, logit_eq_log_div h₁ h₁', logit_eq_log_div h₀ h₀',
    ← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **Gradient of the log odds ratio.** The partial derivatives of `logOddsRatio p₁ p₀` are
`1 / (p₁ (1 - p₁))` in `p₁` and `-1 / (p₀ (1 - p₀))` in `p₀`. -/
theorem hasDerivAt_logOddsRatio {p₁ p₀ : ℝ} (h₁ : 0 < p₁) (h₁' : p₁ < 1) (h₀ : 0 < p₀)
    (h₀' : p₀ < 1) :
    HasDerivAt (fun x ↦ logOddsRatio x p₀) (1 / (p₁ * (1 - p₁))) p₁ ∧
      HasDerivAt (fun x ↦ logOddsRatio p₁ x) (-(1 / (p₀ * (1 - p₀)))) p₀ := by
  refine ⟨(hasDerivAt_logit h₁ h₁').sub_const _, ?_⟩
  exact (hasDerivAt_logit h₀ h₀').const_sub (logit p₁)

/-- **Woolf variance as a delta-method variance** (Fox, MacLehose and Lash, Chapter 2, Table 2.1).
If the two proportions are estimated independently from binomial samples of sizes `n₁` and `n₀`,
with variances `p₁ (1 - p₁) / n₁` and `p₀ (1 - p₀) / n₀`, the first-order variance of the log
odds ratio built from the gradient of `hasDerivAt_logOddsRatio` is `1/a + 1/b + 1/c + 1/d` for the
expected cells `a = n₁ p₁`, `b = n₁ (1 - p₁)`, `c = n₀ p₀`, `d = n₀ (1 - p₀)`. -/
theorem firstOrderVariance_logOddsRatio_eq_woolf {n₁ n₀ p₁ p₀ : ℝ} (hn₁ : 0 < n₁)
    (hn₀ : 0 < n₀) (h₁ : 0 < p₁) (h₁' : p₁ < 1) (h₀ : 0 < p₀) (h₀' : p₀ < 1) :
    firstOrderVariance ![1 / (p₁ * (1 - p₁)), -(1 / (p₀ * (1 - p₀)))]
        ![p₁ * (1 - p₁) / n₁, p₀ * (1 - p₀) / n₀] =
      woolfVariance (n₁ * p₁) (n₁ * (1 - p₁)) (n₀ * p₀) (n₀ * (1 - p₀)) := by
  have e₁ : 0 < 1 - p₁ := by linarith
  have e₀ : 0 < 1 - p₀ := by linarith
  simp only [firstOrderVariance, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    woolfVariance]
  field_simp
  ring

/-- **The log odds of a sample proportion is asymptotically linear.** Let `O` be an i.i.d. sample
under a probability measure, `f` a measurable indicator (values `0` or `1`) and
`p = E f (O 0) ∈ (0, 1)`. Then the log odds of the sample proportion is asymptotically linear at
`logit p` with influence function `(f - p) / (p (1 - p))`. This is the delta method
(`IsAsymptoticallyLinear.comp_hasDerivAt`) applied to the sample mean. -/
theorem logit_sampleMean_isAsymptoticallyLinear {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace 𝒪] {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1)
    {p : ℝ} (hp : μ[fun ω ↦ f (O 0 ω)] = p) (h0 : 0 < p) (h1 : p < 1) :
    IsAsymptoticallyLinear (fun n ω ↦ logit (sampleMean f O n ω)) (logit p)
      (fun x ↦ 1 / (p * (1 - p)) * (f x - p)) O μ := by
  have h2 : MemLp (fun ω ↦ f (O 0 ω)) 2 μ := by
    refine MemLp.of_bound (hf.comp_aemeasurable (hO.aemeasurable 0)).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ ?_)
    rcases h01 (O 0 ω) with h | h <;> simp [h]
  have h := (sampleMean_isAsymptoticallyLinear hf h2).comp_hasDerivAt hO
    (g := logit) (by rw [hp]; exact hasDerivAt_logit h0 h1)
  subst hp
  exact h

/-- **Asymptotic variance of the log odds of a sample proportion.** Under the hypotheses of
`logit_sampleMean_isAsymptoticallyLinear`, the influence function has second moment
`1 / (p (1 - p))`. Divided by the group size and summed over two independent groups, this is
the Woolf variance (`firstOrderVariance_logOddsRatio_eq_woolf`). -/
theorem integral_sq_logit_influence {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace 𝒪] {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f) (h01 : ∀ x, f x = 0 ∨ f x = 1)
    {p : ℝ} (hp : μ[fun ω ↦ f (O 0 ω)] = p) (h0 : 0 < p) (h1 : p < 1) :
    μ[fun ω ↦ (1 / (p * (1 - p)) * (f (O 0 ω) - p)) ^ 2] = 1 / (p * (1 - p)) := by
  have hint : Integrable (fun ω ↦ f (O 0 ω)) μ := by
    refine Integrable.of_bound (hf.comp_aemeasurable (hO.aemeasurable 0)).aestronglyMeasurable 1
      (ae_of_all _ fun ω ↦ ?_)
    rcases h01 (O 0 ω) with h | h <;> simp [h]
  set c : ℝ := 1 / (p * (1 - p)) with hc
  have hpt : ∀ ω, (c * (f (O 0 ω) - p)) ^ 2 = c ^ 2 * (1 - 2 * p) * f (O 0 ω) + c ^ 2 * p ^ 2 := by
    intro ω
    rcases h01 (O 0 ω) with h | h <;> rw [h] <;> ring
  simp_rw [hpt]
  rw [integral_add (hint.const_mul _) (integrable_const _), integral_const_mul, integral_const,
    hp]
  have e : 0 < 1 - p := by linarith
  simp only [probReal_univ, smul_eq_mul, one_mul, hc]
  field_simp
  ring

/-! ### Greenland variance: correction with sensitivity and specificity -/

/-- The true exposure proportion recovered from sensitivity `se`, specificity `sp` and the
observed exposure proportion `pe`: `(pe + sp - 1) / (se + sp - 1)` (Chapter 6, Table 6.8, in
proportion form; the corrected count `A` divided by the row total `D`). -/
noncomputable def trueProportion (se sp pe : ℝ) : ℝ := (pe + sp - 1) / (se + sp - 1)

/-- **The correction recovers the truth.** If the observed proportion is the image
`pe = se P + (1 - sp)(1 - P)` of a true proportion `P` under misclassification with sensitivity
`se` and specificity `sp`, and `se + sp ≠ 1`, then `trueProportion se sp pe = P`. -/
theorem trueProportion_of_forward {se sp P : ℝ} (hk : se + sp - 1 ≠ 0) :
    trueProportion se sp (se * P + (1 - sp) * (1 - P)) = P := by
  rw [trueProportion, div_eq_iff hk]
  ring

/-- The complement of the corrected proportion: `1 - P = (se - pe) / (se + sp - 1)`. -/
theorem one_sub_trueProportion {se sp pe : ℝ} (hk : se + sp - 1 ≠ 0) :
    1 - trueProportion se sp pe = (se - pe) / (se + sp - 1) := by
  rw [trueProportion]
  field_simp
  ring

/-- The log odds of the corrected exposure proportion, written so that the common denominator
`se + sp - 1` cancels: `log (pe + sp - 1) - log (se - pe)` (`logOddsSeSp_eq_logit`). -/
noncomputable def logOddsSeSp (se sp pe : ℝ) : ℝ := Real.log (pe + sp - 1) - Real.log (se - pe)

/-- If `pe + sp - 1 > 0` and `se - pe > 0` (so that the corrected proportion lies strictly
inside `(0, 1)`), `logOddsSeSp se sp pe` is the log odds of `trueProportion se sp pe`. -/
theorem logOddsSeSp_eq_logit {se sp pe : ℝ} (hA : 0 < pe + sp - 1) (hB : 0 < se - pe) :
    logOddsSeSp se sp pe = logit (trueProportion se sp pe) := by
  have hk : 0 < se + sp - 1 := by linarith
  rw [logit, one_sub_trueProportion hk.ne', trueProportion, Real.log_div hA.ne' hk.ne',
    Real.log_div hB.ne' hk.ne', logOddsSeSp]
  ring

/-- **Partial derivatives of the corrected log odds.** At an admissible point
(`pe + sp - 1 > 0`, `se - pe > 0`), `logOddsSeSp se sp pe` has partial derivatives
`-1 / (se - pe)` in `se`, `1 / (pe + sp - 1)` in `sp`, and `1 / (pe + sp - 1) + 1 / (se - pe)`
in `pe`. -/
theorem hasDerivAt_logOddsSeSp {se sp pe : ℝ} (hA : 0 < pe + sp - 1) (hB : 0 < se - pe) :
    HasDerivAt (fun x ↦ logOddsSeSp x sp pe) (-(1 / (se - pe))) se ∧
      HasDerivAt (fun x ↦ logOddsSeSp se x pe) (1 / (pe + sp - 1)) sp ∧
      HasDerivAt (fun x ↦ logOddsSeSp se sp x) (1 / (pe + sp - 1) + 1 / (se - pe)) pe := by
  refine ⟨?_, ?_, ?_⟩
  · have h := (hasDerivAt_const se (Real.log (pe + sp - 1))).sub
      (((hasDerivAt_id' se).sub_const pe).log hB.ne')
    exact h.congr_deriv (by ring)
  · have h := ((((hasDerivAt_id' sp).const_add pe).sub_const 1).log
      (by simpa [add_comm, add_assoc] using hA.ne')).sub_const (Real.log (se - pe))
    convert h using 1
    ext x
    simp only [logOddsSeSp]
  · have h := ((((hasDerivAt_id' pe).add_const sp).sub_const 1).log hA.ne').sub
      (((hasDerivAt_id' pe).const_sub se).log hB.ne')
    exact h.congr_deriv (by ring)

/-- The bias-adjusted log odds ratio from sensitivities and specificities that may differ
between cases (`₁`) and controls (`₀`): `logit P(E₁) - logit P(E₀)`. -/
noncomputable def logORSeSp (se₁ sp₁ pe₁ se₀ sp₀ pe₀ : ℝ) : ℝ :=
  logOddsSeSp se₁ sp₁ pe₁ - logOddsSeSp se₀ sp₀ pe₀

/-- The bias-adjusted log odds ratio is the logarithm of the direct odds ratio formula of
Chapter 6, `(P₁ + SP₁ - 1)(SE₀ - P₀) / ((P₀ + SP₀ - 1)(SE₁ - P₁))`, with `Pᵢ` the observed exposure
proportions. -/
theorem logORSeSp_eq_log_direct {se₁ sp₁ pe₁ se₀ sp₀ pe₀ : ℝ} (hA₁ : 0 < pe₁ + sp₁ - 1)
    (hB₁ : 0 < se₁ - pe₁) (hA₀ : 0 < pe₀ + sp₀ - 1) (hB₀ : 0 < se₀ - pe₀) :
    logORSeSp se₁ sp₁ pe₁ se₀ sp₀ pe₀ =
      Real.log ((pe₁ + sp₁ - 1) * (se₀ - pe₀) / ((pe₀ + sp₀ - 1) * (se₁ - pe₁))) := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul hA₁.ne' hB₀.ne',
    Real.log_mul hA₀.ne' hB₁.ne', logORSeSp, logOddsSeSp, logOddsSeSp]
  ring

/-- One group's term of the Greenland variance (differential form):
`(Var SE / (1 - P)² + Var SP / P² + pe (1 - pe) / (D P² (1 - P)²)) / (SE + SP - 1)²`, where
`P = trueProportion se sp pe` is the corrected exposure proportion and `D` the group size. -/
noncomputable def greenlandTerm (vse vsp se sp pe D : ℝ) : ℝ :=
  (vse / (1 - trueProportion se sp pe) ^ 2 + vsp / trueProportion se sp pe ^ 2 +
    pe * (1 - pe) / (D * trueProportion se sp pe ^ 2 * (1 - trueProportion se sp pe) ^ 2)) /
      (se + sp - 1) ^ 2

/-- One group's contribution to the first-order variance equals `greenlandTerm`: the squared
partial derivatives of `hasDerivAt_logOddsSeSp`, weighted by `Var SE`, `Var SP` and the binomial
variance `pe (1 - pe) / D` of the observed proportion. -/
theorem firstOrderVariance_logOddsSeSp {vse vsp se sp pe D : ℝ} (hA : 0 < pe + sp - 1)
    (hB : 0 < se - pe) (hD : 0 < D) :
    firstOrderVariance ![-(1 / (se - pe)), 1 / (pe + sp - 1), 1 / (pe + sp - 1) + 1 / (se - pe)]
        ![vse, vsp, pe * (1 - pe) / D] = greenlandTerm vse vsp se sp pe D := by
  have hk : 0 < se + sp - 1 := by linarith
  have h1 := hA.ne'
  have h2 := hB.ne'
  have h3 := hk.ne'
  have h4 := hD.ne'
  rw [greenlandTerm, one_sub_trueProportion h3, trueProportion]
  simp only [firstOrderVariance, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

/-- **Greenland variance, differential misclassification** (Fox, MacLehose and Lash, Chapter 10,
"Standard Errors for Misclassification When Sensitivity and Specificity Are Used"; Greenland
1988). With independent estimates of `SEᵢ`, `SPᵢ` and of the observed proportions `pe_i` (binomial
variance `pe_i (1 - pe_i) / Dᵢ`), the first-order variance of the adjusted log odds ratio
`logORSeSp`, from its six partial derivatives, is the sum over cases and controls of
`greenlandTerm`. The admissibility hypotheses force `seᵢ + spᵢ > 1`; the mirrored region
`seᵢ + spᵢ < 1` is not treated. -/
theorem greenland_differential {vse₁ vsp₁ se₁ sp₁ pe₁ D₁ vse₀ vsp₀ se₀ sp₀ pe₀ D₀ : ℝ}
    (hA₁ : 0 < pe₁ + sp₁ - 1) (hB₁ : 0 < se₁ - pe₁) (hD₁ : 0 < D₁)
    (hA₀ : 0 < pe₀ + sp₀ - 1) (hB₀ : 0 < se₀ - pe₀) (hD₀ : 0 < D₀) :
    HasDerivAt (fun x ↦ logORSeSp x sp₁ pe₁ se₀ sp₀ pe₀) (-(1 / (se₁ - pe₁))) se₁ ∧
    HasDerivAt (fun x ↦ logORSeSp se₁ x pe₁ se₀ sp₀ pe₀) (1 / (pe₁ + sp₁ - 1)) sp₁ ∧
    HasDerivAt (fun x ↦ logORSeSp se₁ sp₁ x se₀ sp₀ pe₀)
      (1 / (pe₁ + sp₁ - 1) + 1 / (se₁ - pe₁)) pe₁ ∧
    HasDerivAt (fun x ↦ logORSeSp se₁ sp₁ pe₁ x sp₀ pe₀) (1 / (se₀ - pe₀)) se₀ ∧
    HasDerivAt (fun x ↦ logORSeSp se₁ sp₁ pe₁ se₀ x pe₀) (-(1 / (pe₀ + sp₀ - 1))) sp₀ ∧
    HasDerivAt (fun x ↦ logORSeSp se₁ sp₁ pe₁ se₀ sp₀ x)
      (-(1 / (pe₀ + sp₀ - 1) + 1 / (se₀ - pe₀))) pe₀ ∧
    firstOrderVariance
        ![-(1 / (se₁ - pe₁)), 1 / (pe₁ + sp₁ - 1), 1 / (pe₁ + sp₁ - 1) + 1 / (se₁ - pe₁),
          1 / (se₀ - pe₀), -(1 / (pe₀ + sp₀ - 1)), -(1 / (pe₀ + sp₀ - 1) + 1 / (se₀ - pe₀))]
        ![vse₁, vsp₁, pe₁ * (1 - pe₁) / D₁, vse₀, vsp₀, pe₀ * (1 - pe₀) / D₀] =
      greenlandTerm vse₁ vsp₁ se₁ sp₁ pe₁ D₁ + greenlandTerm vse₀ vsp₀ se₀ sp₀ pe₀ D₀ := by
  obtain ⟨d1, d2, d3⟩ := hasDerivAt_logOddsSeSp hA₁ hB₁
  obtain ⟨e1, e2, e3⟩ := hasDerivAt_logOddsSeSp hA₀ hB₀
  refine ⟨d1.sub_const _, d2.sub_const _, d3.sub_const _, ?_, ?_, ?_, ?_⟩
  · exact (e1.const_sub (logOddsSeSp se₁ sp₁ pe₁)).congr_deriv (by ring)
  · exact e2.const_sub (logOddsSeSp se₁ sp₁ pe₁)
  · exact e3.const_sub (logOddsSeSp se₁ sp₁ pe₁)
  · rw [← firstOrderVariance_logOddsSeSp hA₁ hB₁ hD₁, ← firstOrderVariance_logOddsSeSp hA₀ hB₀ hD₀]
    simp only [firstOrderVariance, Fin.sum_univ_six, Fin.sum_univ_three]
    simp
    ring

/-- The Greenland variance for nondifferential misclassification (shared `SE`, `SP`):
`[Var SE (1/(1 - P₁) - 1/(1 - P₀))² + Var SP (1/P₁ - 1/P₀)²] / (SE + SP - 1)²` plus
`∑ᵢ pe_i (1 - pe_i) / (Dᵢ Pᵢ² (1 - Pᵢ)²) / (SE + SP - 1)²`, with
`Pᵢ = trueProportion se sp pe_i`. -/
noncomputable def greenlandNondiff (vse vsp se sp pe₁ D₁ pe₀ D₀ : ℝ) : ℝ :=
  (vse * (1 / (1 - trueProportion se sp pe₁) - 1 / (1 - trueProportion se sp pe₀)) ^ 2 +
      vsp * (1 / trueProportion se sp pe₁ - 1 / trueProportion se sp pe₀) ^ 2) /
      (se + sp - 1) ^ 2 +
    (pe₁ * (1 - pe₁) /
        (D₁ * trueProportion se sp pe₁ ^ 2 * (1 - trueProportion se sp pe₁) ^ 2) +
      pe₀ * (1 - pe₀) /
        (D₀ * trueProportion se sp pe₀ ^ 2 * (1 - trueProportion se sp pe₀) ^ 2)) /
      (se + sp - 1) ^ 2

/-- **Greenland variance, nondifferential misclassification** (Fox, MacLehose and Lash,
Chapter 10, second display of "Standard Errors for Misclassification When Sensitivity and
Specificity Are Used", evaluated in Equation 10.1). With one sensitivity and one specificity for
cases and controls, the adjusted log odds ratio is a function of the four inputs
`(SE, SP, pe₁, pe₀)`; its partial derivatives are as stated, and with independent inputs of
variances `Var SE`, `Var SP`, `pe_i (1 - pe_i) / Dᵢ` its first-order variance is
`greenlandNondiff`. The hypotheses `pe_i + sp - 1 > 0` and `se - pe_i > 0` (corrected proportions
strictly inside `(0, 1)`) force `se + sp > 1`; the mirrored region `se + sp < 1` is not treated. -/
theorem greenland_nondifferential {vse vsp se sp pe₁ D₁ pe₀ D₀ : ℝ}
    (hA₁ : 0 < pe₁ + sp - 1) (hB₁ : 0 < se - pe₁) (hD₁ : 0 < D₁)
    (hA₀ : 0 < pe₀ + sp - 1) (hB₀ : 0 < se - pe₀) (hD₀ : 0 < D₀) :
    HasDerivAt (fun x ↦ logORSeSp x sp pe₁ x sp pe₀)
      (-(1 / (se - pe₁)) + 1 / (se - pe₀)) se ∧
    HasDerivAt (fun x ↦ logORSeSp se x pe₁ se x pe₀)
      (1 / (pe₁ + sp - 1) - 1 / (pe₀ + sp - 1)) sp ∧
    HasDerivAt (fun x ↦ logORSeSp se sp x se sp pe₀)
      (1 / (pe₁ + sp - 1) + 1 / (se - pe₁)) pe₁ ∧
    HasDerivAt (fun x ↦ logORSeSp se sp pe₁ se sp x)
      (-(1 / (pe₀ + sp - 1) + 1 / (se - pe₀))) pe₀ ∧
    firstOrderVariance
        ![-(1 / (se - pe₁)) + 1 / (se - pe₀), 1 / (pe₁ + sp - 1) - 1 / (pe₀ + sp - 1),
          1 / (pe₁ + sp - 1) + 1 / (se - pe₁), -(1 / (pe₀ + sp - 1) + 1 / (se - pe₀))]
        ![vse, vsp, pe₁ * (1 - pe₁) / D₁, pe₀ * (1 - pe₀) / D₀] =
      greenlandNondiff vse vsp se sp pe₁ D₁ pe₀ D₀ := by
  obtain ⟨d1, d2, d3⟩ := hasDerivAt_logOddsSeSp hA₁ hB₁
  obtain ⟨e1, e2, e3⟩ := hasDerivAt_logOddsSeSp hA₀ hB₀
  refine ⟨(d1.sub e1).congr_deriv (by ring), d2.sub e2, d3.sub_const _, e3.const_sub _, ?_⟩
  have hk : 0 < se + sp - 1 := by linarith
  have h1 := hA₁.ne'
  have h2 := hB₁.ne'
  have h3 := hk.ne'
  have h4 := hD₁.ne'
  have h5 := hA₀.ne'
  have h6 := hB₀.ne'
  have h7 := hD₀.ne'
  rw [greenlandNondiff, one_sub_trueProportion h3, one_sub_trueProportion h3, trueProportion,
    trueProportion]
  simp only [firstOrderVariance, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring

/-! ### Marshall variance: correction with predictive values -/

/-- The true exposure proportion from predictive values (Chapter 10, Equation 10.4):
`P(E) = PPV P(e) + (1 - NPV)(1 - P(e))`. -/
def trueProportionPV (ppv npv pe : ℝ) : ℝ := ppv * pe + (1 - npv) * (1 - pe)

/-- **Equation 10.4 recovers the truth.** Let `q₁₁, q₀₁, q₁₀, q₀₀ ≥ 0` be the joint probabilities
of (true exposure, observed exposure) = `(1,1), (0,1), (1,0), (0,0)`, summing to one, with observed
prevalence `pe = q₁₁ + q₀₁` strictly between `0` and `1`. With `PPV = q₁₁ / pe` and
`NPV = q₀₀ / (1 - pe)`, `trueProportionPV PPV NPV pe` is the true prevalence `q₁₁ + q₁₀`. -/
theorem trueProportionPV_eq_true {q₁₁ q₀₁ q₁₀ q₀₀ : ℝ} (hsum : q₁₁ + q₀₁ + q₁₀ + q₀₀ = 1)
    (hpe : 0 < q₁₁ + q₀₁) (hpe' : q₁₁ + q₀₁ < 1) :
    trueProportionPV (q₁₁ / (q₁₁ + q₀₁)) (q₀₀ / (1 - (q₁₁ + q₀₁))) (q₁₁ + q₀₁) = q₁₁ + q₁₀ := by
  have h1 : 1 - (q₁₁ + q₀₁) ≠ 0 := by linarith
  rw [trueProportionPV]
  field_simp
  linear_combination -hsum

/-- The log odds of the predictive-value corrected proportion. -/
noncomputable def logOddsPV (ppv npv pe : ℝ) : ℝ := logit (trueProportionPV ppv npv pe)

/-- **Partial derivatives of the predictive-value corrected log odds.** With
`P = trueProportionPV ppv npv pe ∈ (0, 1)`, the partial derivatives are `pe / (P (1 - P))` in
`PPV`, `-(1 - pe) / (P (1 - P))` in `NPV` and `(PPV - (1 - NPV)) / (P (1 - P))` in `pe`. -/
theorem hasDerivAt_logOddsPV {ppv npv pe : ℝ} (hP₀ : 0 < trueProportionPV ppv npv pe)
    (hP₁ : trueProportionPV ppv npv pe < 1) :
    HasDerivAt (fun x ↦ logOddsPV x npv pe)
      (pe / (trueProportionPV ppv npv pe * (1 - trueProportionPV ppv npv pe))) ppv ∧
    HasDerivAt (fun x ↦ logOddsPV ppv x pe)
      (-(1 - pe) / (trueProportionPV ppv npv pe * (1 - trueProportionPV ppv npv pe))) npv ∧
    HasDerivAt (fun x ↦ logOddsPV ppv npv x)
      ((ppv - (1 - npv)) /
        (trueProportionPV ppv npv pe * (1 - trueProportionPV ppv npv pe))) pe := by
  have hl := hasDerivAt_logit hP₀ hP₁
  refine ⟨?_, ?_, ?_⟩
  · exact (hl.comp ppv (((hasDerivAt_id' ppv).mul_const pe).add_const
      ((1 - npv) * (1 - pe)))).congr_deriv (by ring)
  · exact (hl.comp npv ((((hasDerivAt_id' npv).const_sub 1).mul_const (1 - pe)).const_add
      (ppv * pe))).congr_deriv (by ring)
  · exact (hl.comp pe (((hasDerivAt_id' pe).const_mul ppv).add
      (((hasDerivAt_id' pe).const_sub 1).const_mul (1 - npv)))).congr_deriv (by ring)

/-- Marshall's `aᵢ` (Chapter 10, Equation 10.6):
`(PPV - (1 - NPV))² Var P(e) + Var PPV · P(e)² + Var NPV · (1 - P(e))²`. -/
def marshallA (vppv vnpv vpe ppv npv pe : ℝ) : ℝ :=
  (ppv - (1 - npv)) ^ 2 * vpe + vppv * pe ^ 2 + vnpv * (1 - pe) ^ 2

/-- One group's first-order variance of the predictive-value corrected log odds is
`aᵢ / (P (1 - P))²` (one summand of Equation 10.5). -/
theorem firstOrderVariance_logOddsPV {vppv vnpv vpe ppv npv pe : ℝ}
    (hP₀ : 0 < trueProportionPV ppv npv pe) (hP₁ : trueProportionPV ppv npv pe < 1) :
    firstOrderVariance
        ![pe / (trueProportionPV ppv npv pe * (1 - trueProportionPV ppv npv pe)),
          -(1 - pe) / (trueProportionPV ppv npv pe * (1 - trueProportionPV ppv npv pe)),
          (ppv - (1 - npv)) /
            (trueProportionPV ppv npv pe * (1 - trueProportionPV ppv npv pe))]
        ![vppv, vnpv, vpe] =
      marshallA vppv vnpv vpe ppv npv pe /
        (trueProportionPV ppv npv pe * (1 - trueProportionPV ppv npv pe)) ^ 2 := by
  have h1 : trueProportionPV ppv npv pe ≠ 0 := hP₀.ne'
  have h2 : 1 - trueProportionPV ppv npv pe ≠ 0 := by linarith
  simp only [firstOrderVariance, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, marshallA]
  field_simp
  ring

/-- The adjusted log odds ratio from predictive values: `logit P(E₁) - logit P(E₀)`. -/
noncomputable def logORPV (ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀ : ℝ) : ℝ :=
  logOddsPV ppv₁ npv₁ pe₁ - logOddsPV ppv₀ npv₀ pe₀

/-- The six partial derivatives of `logORPV` used in `marshall_variance`: those of the case
group as in `hasDerivAt_logOddsPV`, and those of the control group with reversed sign. -/
theorem hasDerivAt_logORPV {ppv₁ npv₁ pe₁ ppv₀ npv₀ pe₀ : ℝ}
    (hP₁₀ : 0 < trueProportionPV ppv₁ npv₁ pe₁) (hP₁₁ : trueProportionPV ppv₁ npv₁ pe₁ < 1)
    (hP₀₀ : 0 < trueProportionPV ppv₀ npv₀ pe₀) (hP₀₁ : trueProportionPV ppv₀ npv₀ pe₀ < 1) :
    HasDerivAt (fun x ↦ logORPV x npv₁ pe₁ ppv₀ npv₀ pe₀)
      (pe₁ / (trueProportionPV ppv₁ npv₁ pe₁ * (1 - trueProportionPV ppv₁ npv₁ pe₁))) ppv₁ ∧
    HasDerivAt (fun x ↦ logORPV ppv₁ x pe₁ ppv₀ npv₀ pe₀)
      (-(1 - pe₁) / (trueProportionPV ppv₁ npv₁ pe₁ * (1 - trueProportionPV ppv₁ npv₁ pe₁)))
      npv₁ ∧
    HasDerivAt (fun x ↦ logORPV ppv₁ npv₁ x ppv₀ npv₀ pe₀)
      ((ppv₁ - (1 - npv₁)) /
        (trueProportionPV ppv₁ npv₁ pe₁ * (1 - trueProportionPV ppv₁ npv₁ pe₁))) pe₁ ∧
    HasDerivAt (fun x ↦ logORPV ppv₁ npv₁ pe₁ x npv₀ pe₀)
      (-(pe₀ / (trueProportionPV ppv₀ npv₀ pe₀ * (1 - trueProportionPV ppv₀ npv₀ pe₀)))) ppv₀ ∧
    HasDerivAt (fun x ↦ logORPV ppv₁ npv₁ pe₁ ppv₀ x pe₀)
      (-(-(1 - pe₀) / (trueProportionPV ppv₀ npv₀ pe₀ * (1 - trueProportionPV ppv₀ npv₀ pe₀))))
      npv₀ ∧
    HasDerivAt (fun x ↦ logORPV ppv₁ npv₁ pe₁ ppv₀ npv₀ x)
      (-((ppv₀ - (1 - npv₀)) /
        (trueProportionPV ppv₀ npv₀ pe₀ * (1 - trueProportionPV ppv₀ npv₀ pe₀)))) pe₀ := by
  obtain ⟨d1, d2, d3⟩ := hasDerivAt_logOddsPV hP₁₀ hP₁₁
  obtain ⟨e1, e2, e3⟩ := hasDerivAt_logOddsPV hP₀₀ hP₀₁
  exact ⟨d1.sub_const _, d2.sub_const _, d3.sub_const _, e1.const_sub _, e2.const_sub _,
    e3.const_sub _⟩

/-- **Marshall variance** (Fox, MacLehose and Lash, Chapter 10, Equations 10.4 to 10.6; Marshall
1990). With independent estimates of `PPVᵢ`, `NPVᵢ` and `P(eᵢ)`, the first-order variance of the
adjusted log odds ratio `logORPV`, from its six partial derivatives (`hasDerivAt_logORPV`), is
`a₀ / (P(E₀)(1 - P(E₀)))² + a₁ / (P(E₁)(1 - P(E₁)))²` with `aᵢ = marshallA …`. -/
theorem marshall_variance {vppv₁ vnpv₁ vpe₁ ppv₁ npv₁ pe₁ vppv₀ vnpv₀ vpe₀ ppv₀ npv₀ pe₀ : ℝ}
    (hP₁₀ : 0 < trueProportionPV ppv₁ npv₁ pe₁) (hP₁₁ : trueProportionPV ppv₁ npv₁ pe₁ < 1)
    (hP₀₀ : 0 < trueProportionPV ppv₀ npv₀ pe₀) (hP₀₁ : trueProportionPV ppv₀ npv₀ pe₀ < 1) :
    firstOrderVariance
        ![pe₁ / (trueProportionPV ppv₁ npv₁ pe₁ * (1 - trueProportionPV ppv₁ npv₁ pe₁)),
          -(1 - pe₁) / (trueProportionPV ppv₁ npv₁ pe₁ * (1 - trueProportionPV ppv₁ npv₁ pe₁)),
          (ppv₁ - (1 - npv₁)) /
            (trueProportionPV ppv₁ npv₁ pe₁ * (1 - trueProportionPV ppv₁ npv₁ pe₁)),
          -(pe₀ / (trueProportionPV ppv₀ npv₀ pe₀ * (1 - trueProportionPV ppv₀ npv₀ pe₀))),
          -(-(1 - pe₀) /
            (trueProportionPV ppv₀ npv₀ pe₀ * (1 - trueProportionPV ppv₀ npv₀ pe₀))),
          -((ppv₀ - (1 - npv₀)) /
            (trueProportionPV ppv₀ npv₀ pe₀ * (1 - trueProportionPV ppv₀ npv₀ pe₀)))]
        ![vppv₁, vnpv₁, vpe₁, vppv₀, vnpv₀, vpe₀] =
      marshallA vppv₀ vnpv₀ vpe₀ ppv₀ npv₀ pe₀ /
          (trueProportionPV ppv₀ npv₀ pe₀ * (1 - trueProportionPV ppv₀ npv₀ pe₀)) ^ 2 +
        marshallA vppv₁ vnpv₁ vpe₁ ppv₁ npv₁ pe₁ /
          (trueProportionPV ppv₁ npv₁ pe₁ * (1 - trueProportionPV ppv₁ npv₁ pe₁)) ^ 2 := by
  rw [← firstOrderVariance_logOddsPV hP₁₀ hP₁₁, ← firstOrderVariance_logOddsPV hP₀₀ hP₀₁]
  simp only [firstOrderVariance, Fin.sum_univ_six, Fin.sum_univ_three]
  simp
  ring


/-! ### Predictive value weighting -/

/-- Weighted count of truly exposed records in the duplicated dataset of predictive value
weighting (Chapter 10, "Predictive Value Weighting", Table 10.3): each of the `a` records observed
exposed contributes weight `PPV` to the exposed copy and each of the `b` records observed
unexposed contributes weight `1 - NPV`. -/
def pvwExposed (a b ppv npv : ℝ) : ℝ := a * ppv + b * (1 - npv)

/-- Weighted count of truly unexposed records in the duplicated dataset: weights `1 - PPV` and
`NPV`. -/
def pvwUnexposed (a b ppv npv : ℝ) : ℝ := a * (1 - ppv) + b * npv

/-- Each record carries total weight one, so the weighted dataset has the original size. -/
theorem pvwExposed_add_pvwUnexposed (a b ppv npv : ℝ) :
    pvwExposed a b ppv npv + pvwUnexposed a b ppv npv = a + b := by
  rw [pvwExposed, pvwUnexposed]
  ring

/-- The weighted exposed proportion is the predictive-value corrected proportion of
Equation 10.4 at the observed proportion `a / (a + b)`. -/
theorem pvwExposed_div {a b ppv npv : ℝ} (hab : 0 < a + b) :
    pvwExposed a b ppv npv / (a + b) = trueProportionPV ppv npv (a / (a + b)) := by
  rw [pvwExposed, trueProportionPV]
  field_simp
  ring

/-- **Predictive value weighting recovers the true row.** Let `n₁₁, n₀₁` be the numbers of records
observed exposed that are truly exposed and truly unexposed, and `n₁₀, n₀₀` those observed
unexposed that are truly exposed and truly unexposed, with `a = n₁₁ + n₀₁ > 0` and
`b = n₁₀ + n₀₀ > 0`. With `PPV = n₁₁ / a` and `NPV = n₀₀ / b`, the weighted counts are the true
counts `n₁₁ + n₁₀` (exposed) and `n₀₁ + n₀₀` (unexposed). This is the cell correction of
Chapter 6, Tables 6.10 to 6.12, `A = a PPV + b (1 - NPV)`. -/
theorem pvw_recovers_true {n₁₁ n₀₁ n₁₀ n₀₀ : ℝ} (ha : 0 < n₁₁ + n₀₁) (hb : 0 < n₁₀ + n₀₀) :
    pvwExposed (n₁₁ + n₀₁) (n₁₀ + n₀₀) (n₁₁ / (n₁₁ + n₀₁)) (n₀₀ / (n₁₀ + n₀₀)) = n₁₁ + n₁₀ ∧
      pvwUnexposed (n₁₁ + n₀₁) (n₁₀ + n₀₀) (n₁₁ / (n₁₁ + n₀₁)) (n₀₀ / (n₁₀ + n₀₀)) =
        n₀₁ + n₀₀ := by
  constructor
  · rw [pvwExposed]
    field_simp
    ring
  · rw [pvwUnexposed]
    field_simp
    ring

/-! ### Jackknife variance -/

/-- The jackknife variance `((n - 1) / n) ∑ᵢ (θᵢ - θ̄)²` of leave-one-out estimates
`θ₀, …, θ_{n-1}`, centered at their average `θ̄` (Chapter 10, "Predictive Value Weighting",
display for `SE_jack`, squared). The book applies it to `θᵢ = ln ORⁱ`; its display centers at the
mean of the `ln ORⁱ`, as here, while the sentence after it says "the average of the `ORⁱ`",
which is a misprint for the average of the `ln ORⁱ`. -/
noncomputable def jackknifeVariance {n : ℕ} (θ : Fin n → ℝ) : ℝ :=
  ((n - 1) / n) * ∑ i, (θ i - (∑ j, θ j) / n) ^ 2

/-- The leave-one-out mean `(∑ⱼ xⱼ - xᵢ) / (n - 1)`. -/
noncomputable def leaveOneOutMean {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ((∑ j, x j) - x i) / (n - 1)

/-- **The jackknife is exact for the sample mean.** For `n ≥ 2` observations, the jackknife
variance of the leave-one-out means is `∑ᵢ (xᵢ - x̄)² / (n (n - 1))`, the usual unbiased estimate
`s² / n` of the variance of the sample mean. -/
theorem jackknifeVariance_leaveOneOutMean {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) :
    jackknifeVariance (leaveOneOutMean x) =
      (∑ i, (x i - (∑ j, x j) / n) ^ 2) / (n * (n - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmean : (∑ j, leaveOneOutMean x j) / n = (∑ j, x j) / n := by
    simp only [leaveOneOutMean, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hterm : ∀ i, leaveOneOutMean x i - (∑ j, leaveOneOutMean x j) / n =
      (-(1 / ((n : ℝ) - 1))) * (x i - (∑ j, x j) / n) := by
    intro i
    rw [hmean, leaveOneOutMean]
    field_simp
    ring
  rw [jackknifeVariance]
  simp_rw [hterm, mul_pow, ← Finset.mul_sum]
  field_simp

/-! ### Rubin's rules -/

/-- The multiple imputation estimate (Chapter 10, Equation 10.20): the average of the `M`
imputation-specific estimates. -/
noncomputable def miEstimate {M : ℕ} (θ : Fin M → ℝ) : ℝ := (∑ i, θ i) / M

/-- The within-imputation variance: the average of the imputation-specific variances. -/
noncomputable def withinVariance {M : ℕ} (V : Fin M → ℝ) : ℝ := (∑ i, V i) / M

/-- The between-imputation variance `∑ᵢ (θᵢ - θ̄)² / (M - 1)`. -/
noncomputable def betweenVariance {M : ℕ} (θ : Fin M → ℝ) : ℝ :=
  (∑ i, (θ i - miEstimate θ) ^ 2) / (M - 1)

/-- The multiple imputation variance as printed in Chapter 10, Equation 10.21:
`(1/M) ∑ᵢ Vᵢ + ((M + 1) / (M (M - 1))) ∑ᵢ (θᵢ - θ̄)²`. -/
noncomputable def rubinVariance {M : ℕ} (θ V : Fin M → ℝ) : ℝ :=
  (∑ i, V i) / M + ((M + 1) / (M * (M - 1))) * ∑ i, (θ i - miEstimate θ) ^ 2

/-- **Rubin's rules.** For `M ≥ 2` imputations, Equation 10.21 is Rubin's total variance
`W + (1 + 1/M) B`, with `W` the within- and `B` the between-imputation variance. -/
theorem rubinVariance_eq {M : ℕ} (hM : 2 ≤ M) (θ V : Fin M → ℝ) :
    rubinVariance θ V = withinVariance V + (1 + 1 / M) * betweenVariance θ := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hM1 : (M : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  rw [rubinVariance, withinVariance, betweenVariance]
  field_simp

/-- The total multiple imputation variance is at least the within-imputation variance; the
excess `(1 + 1/M) B` is the uncertainty due to the missing data. -/
theorem withinVariance_le_rubinVariance {M : ℕ} (hM : 2 ≤ M) (θ V : Fin M → ℝ) :
    withinVariance V ≤ rubinVariance θ V := by
  have hM1 : (1 : ℝ) < M := by exact_mod_cast hM
  rw [rubinVariance_eq hM, le_add_iff_nonneg_right, betweenVariance]
  have : 0 ≤ ∑ i, (θ i - miEstimate θ) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have : 0 < (M : ℝ) - 1 := by linarith
  positivity

/-! ### Inverse-variance pooling -/

/-- The total inverse-variance weight `∑ᵢ 1 / Vᵢ`. -/
noncomputable def ivTotalWeight {k : ℕ} (V : Fin k → ℝ) : ℝ := ∑ i, 1 / V i

/-- The inverse-variance pooled estimate `∑ᵢ (θᵢ / Vᵢ) / ∑ᵢ (1 / Vᵢ)` (Chapter 10,
"Misclassification Example"). -/
noncomputable def ivPooled {k : ℕ} (θ V : Fin k → ℝ) : ℝ := (∑ i, θ i / V i) / ivTotalWeight V

/-- The variance `1 / ∑ᵢ (1 / Vᵢ)` attributed to the pooled estimate. -/
noncomputable def ivPooledVariance {k : ℕ} (V : Fin k → ℝ) : ℝ := 1 / ivTotalWeight V

/-- The pooled estimate is the weighted average with normalized weights `(1/Vᵢ) / ∑ⱼ (1/Vⱼ)`. -/
theorem ivPooled_eq_sum_weights {k : ℕ} (θ V : Fin k → ℝ) :
    ivPooled θ V = ∑ i, (1 / V i) / ivTotalWeight V * θ i := by
  rw [ivPooled, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **Variance of a weighted average, decomposed.** For positive variances `Vᵢ` and weights `cᵢ`
summing to one, the variance `∑ᵢ cᵢ² Vᵢ` of `∑ᵢ cᵢ θᵢ` for independent `θᵢ` equals
`1 / ∑ⱼ (1/Vⱼ)` plus `∑ᵢ Vᵢ (cᵢ - (1/Vᵢ) / ∑ⱼ (1/Vⱼ))²`. -/
theorem firstOrderVariance_weights_eq {k : ℕ} {V : Fin k → ℝ} (hV : ∀ i, 0 < V i)
    (hk : 0 < k) {c : Fin k → ℝ} (hc : ∑ i, c i = 1) :
    firstOrderVariance c V = ivPooledVariance V +
      ∑ i, V i * (c i - (1 / V i) / ivTotalWeight V) ^ 2 := by
  have hW : 0 < ivTotalWeight V := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact Finset.sum_pos (fun i _ ↦ one_div_pos.2 (hV i)) Finset.univ_nonempty
  have hterm : ∀ i, V i * (c i - (1 / V i) / ivTotalWeight V) ^ 2 =
      c i ^ 2 * V i - 2 * (c i / ivTotalWeight V) + (1 / V i) / ivTotalWeight V ^ 2 := by
    intro i
    have := (hV i).ne'
    field_simp
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_div,
    ← Finset.sum_div, hc, ivPooledVariance, firstOrderVariance]
  change _ = _ + (_ - _ + ivTotalWeight V / _)
  field_simp
  ring

/-- **Inverse-variance weights are optimal.** Among weighted averages `∑ᵢ cᵢ θᵢ` of independent
estimates with positive variances `Vᵢ` and weights summing to one, the first-order variance is at
least `1 / ∑ⱼ (1/Vⱼ)`, with equality for the inverse-variance weights. -/
theorem ivPooledVariance_le {k : ℕ} {V : Fin k → ℝ} (hV : ∀ i, 0 < V i) (hk : 0 < k)
    {c : Fin k → ℝ} (hc : ∑ i, c i = 1) :
    ivPooledVariance V ≤ firstOrderVariance c V := by
  rw [firstOrderVariance_weights_eq hV hk hc, le_add_iff_nonneg_right]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hV i).le (sq_nonneg _)

/-- The inverse-variance weights sum to one and attain the bound of `ivPooledVariance_le`: the
first-order variance of the pooled estimate is `1 / ∑ⱼ (1/Vⱼ)`. -/
theorem firstOrderVariance_ivWeights {k : ℕ} {V : Fin k → ℝ} (hV : ∀ i, 0 < V i) (hk : 0 < k) :
    ∑ i, (1 / V i) / ivTotalWeight V = 1 ∧
      firstOrderVariance (fun i ↦ (1 / V i) / ivTotalWeight V) V = ivPooledVariance V := by
  have hW : 0 < ivTotalWeight V := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact Finset.sum_pos (fun i _ ↦ one_div_pos.2 (hV i)) Finset.univ_nonempty
  have hsum : ∑ i, (1 / V i) / ivTotalWeight V = 1 := by
    rw [← Finset.sum_div]
    exact div_self hW.ne'
  refine ⟨hsum, ?_⟩
  rw [firstOrderVariance_weights_eq hV hk hsum]
  simp

/-- **Standard error from a Wald interval.** If the Wald interval with standard error `se ≥ 0`
and critical value `z > 0` is `[L, U]`, then `se = (U - L) / (2 z)` and the estimate is the
midpoint `(L + U) / 2`. This is how Chapter 10 recovers the standard error `0.225` from the
interval `(0.75, 1.81)` on the log scale before pooling. -/
theorem se_eq_of_waldIntervalSE_eq {est se z L U : ℝ} (hz : 0 < z) (hse : 0 ≤ se)
    (h : waldIntervalSE est se z = Set.Icc L U) :
    se = (U - L) / (2 * z) ∧ est = (L + U) / 2 := by
  rw [waldIntervalSE, Set.Icc_eq_Icc_iff (by nlinarith)] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [eq_div_iff (by positivity)]
    linarith
  · linarith

/-! ### Admissibility of the sensitivity and specificity correction -/

/-- **The correction is undefined when `se + sp = 1`.** Then the observed proportion
`se P + (1 - sp)(1 - P)` equals `se` whatever the true proportion `P` is, so no correction can
recover `P`; the formula `trueProportion` divides by `se + sp - 1 = 0` and its Lean value `0` has
no meaning. The theorems above therefore assume `se + sp - 1 ≠ 0` or the stronger admissibility
conditions `pe + sp - 1 > 0`, `se - pe > 0`. -/
theorem forward_eq_se_of_sum_eq_one {se sp : ℝ} (h : se + sp = 1) (P : ℝ) :
    se * P + (1 - sp) * (1 - P) = se := by
  have : 1 - sp = se := by linarith
  rw [this]
  ring

/-- **A corrected proportion outside the unit interval.** With `se = sp = 9/10` and an observed
proportion `pe = 1/20 < 1 - sp`, the corrected proportion is `-1/16 < 0`: the observed proportion
is incompatible with these bias parameters. -/
theorem trueProportion_neg_example : trueProportion (9 / 10) (9 / 10) (1 / 20) = -1 / 16 := by
  norm_num [trueProportion]

namespace Examples

/-- **Chapter 2, Table 2.1 and text, first design.** All four cells equal to `25`: the standard
error of the log odds ratio is `√(4/25) = 0.4`. -/
theorem woolf_balanced : √(woolfVariance 25 25 25 25) = 2 / 5 := by
  rw [show woolfVariance 25 25 25 25 = (2 / 5) ^ 2 by norm_num [woolfVariance],
    Real.sqrt_sq (by norm_num)]

/-- **Chapter 2, second design.** Cells `10, 10, 40, 40`: the standard error is `√(1/4) = 0.5`,
`25%` larger than in the balanced design at the same total size `100`. -/
theorem woolf_unbalanced :
    √(woolfVariance 10 10 40 40) = 1 / 2 ∧ (1 / 2 : ℝ) / (2 / 5) = 1.25 := by
  refine ⟨?_, by norm_num⟩
  rw [show woolfVariance 10 10 40 40 = (1 / 2) ^ 2 by norm_num [woolfVariance],
    Real.sqrt_sq (by norm_num)]

/-- **Chapter 2, interval of the balanced design.** On the log scale the Wald interval around
`ln OR = 0` with standard error `0.4` is `[-0.784, 0.784]`; on the odds ratio scale its endpoints
`exp (∓0.784)` lie in `(0.455, 0.465)` and `(2.185, 2.195)`, the printed `0.46` and `2.19`. -/
theorem woolf_balanced_interval :
    waldIntervalSE 0 (2 / 5) 1.96 = Set.Icc (-0.784) 0.784 ∧
      0.455 < Real.exp (-0.784) ∧ Real.exp (-0.784) < 0.465 ∧
      2.185 < Real.exp 0.784 ∧ Real.exp 0.784 < 2.195 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 0.784) (by norm_num) 6
  have h2 := Real.exp_bound' (x := 0.784) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
  norm_num at h1 h2
  have hlo : 2.185 < Real.exp 0.784 := by linarith
  have hhi : Real.exp 0.784 < 2.195 := by linarith
  refine ⟨by norm_num [waldIntervalSE], ?_, ?_, hlo, hhi⟩
  · rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith
  · rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith

/-- **Chapter 2, interval of the unbalanced design.** With standard error `0.5` the log-scale
interval is `[-0.98, 0.98]`, `25%` wider; its odds ratio endpoints `exp (∓0.98)` lie in
`(0.375, 0.385)` and `(2.655, 2.665)`, the printed `0.38` and `2.66`. -/
theorem woolf_unbalanced_interval :
    waldIntervalSE 0 (1 / 2) 1.96 = Set.Icc (-0.98) 0.98 ∧
      0.375 < Real.exp (-0.98) ∧ Real.exp (-0.98) < 0.385 ∧
      2.655 < Real.exp 0.98 ∧ Real.exp 0.98 < 2.665 := by
  have h1 := Real.sum_le_exp_of_nonneg (x := 0.98) (by norm_num) 7
  have h2 := Real.exp_bound' (x := 0.98) (by norm_num) (by norm_num) (n := 7) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1 h2
  norm_num at h1 h2
  have hlo : 2.655 < Real.exp 0.98 := by linarith
  have hhi : Real.exp 0.98 < 2.665 := by linarith
  refine ⟨by norm_num [waldIntervalSE], ?_, ?_, hlo, hhi⟩
  · rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    linarith
  · rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    linarith

/-- **Equation 10.1, recomputed.** The smoking and breast cancer example (Chapter 6, Tables 6.2 and
6.9): `SE = 128/164`, `SP = 465/470` with binomial variances `SE (1 - SE)/164` and
`SP (1 - SP)/470`, observed exposure proportions `215/1664` (cases) and `668/4964` (controls).
The nondifferential Greenland variance lies in `(0.00889, 0.00890)`, the printed `0.0089`. The
book's own display rounds the inputs (`Var SE = 0.001`, `P(E₁) = 0.154`, …); with
`SE = 0.78`, `SP = 0.99` and unrounded observed proportions one gets `0.0088`, so the exact
validation fractions are the inputs that reproduce the printed value. -/
theorem greenland_example :
    0.00889 < greenlandNondiff ((128 / 164) * (1 - 128 / 164) / 164)
        ((465 / 470) * (1 - 465 / 470) / 470) (128 / 164) (465 / 470)
        (215 / 1664) 1664 (668 / 4964) 4964 ∧
      greenlandNondiff ((128 / 164) * (1 - 128 / 164) / 164)
        ((465 / 470) * (1 - 465 / 470) / 470) (128 / 164) (465 / 470)
        (215 / 1664) 1664 (668 / 4964) 4964 < 0.00890 := by
  constructor <;> norm_num [greenlandNondiff, trueProportion]

/-- **Equation 10.2 and the variance share.** With the same inputs the adjusted odds ratio
(direct formula of Chapter 6) lies in `(0.9485, 0.9495)`, the printed `0.949`. The conventional
Woolf variance `1/215 + 1/1449 + 1/668 + 1/4296 ≈ 0.00707` is between `79.5%` and `79.6%` of the
Greenland variance. The book prints `79%`; rounding gives `80%`, so the printed share is
truncated rather than rounded. -/
theorem greenland_example_or_share :
    (0.9485 : ℝ) < (215 / 1664 + 465 / 470 - 1) * (128 / 164 - 668 / 4964) /
        ((668 / 4964 + 465 / 470 - 1) * (128 / 164 - 215 / 1664)) ∧
      (215 / 1664 + 465 / 470 - 1) * (128 / 164 - 668 / 4964) /
        ((668 / 4964 + 465 / 470 - 1) * (128 / 164 - 215 / 1664)) < (0.9495 : ℝ) ∧
      0.795 * greenlandNondiff ((128 / 164) * (1 - 128 / 164) / 164)
        ((465 / 470) * (1 - 465 / 470) / 470) (128 / 164) (465 / 470)
        (215 / 1664) 1664 (668 / 4964) 4964 < woolfVariance 215 1449 668 4296 ∧
      woolfVariance 215 1449 668 4296 < 0.796 * greenlandNondiff
        ((128 / 164) * (1 - 128 / 164) / 164)
        ((465 / 470) * (1 - 465 / 470) / 470) (128 / 164) (465 / 470)
        (215 / 1664) 1664 (668 / 4964) 4964 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;>
    norm_num [greenlandNondiff, trueProportion, woolfVariance]

/-- **Marshall's example (Chapter 10, Tables 10.1 and 10.2).** Observed `122/442` exposed and
unexposed cases and `101/479` controls; `PPV₁ = 29/51`, `NPV₁ = 143/160`, `PPV₀ = 21/33`,
`NPV₀ = 168/184`, each with binomial variance `p (1 - p)/n`, and `Var P(eᵢ)` binomial in the
row total. Then `a₁ ∈ (0.000650, 0.000660)`, `a₀ ∈ (0.000580, 0.000590)` and the variance of
Equation 10.5 lies in `(0.0500, 0.0510)` (printed `0.051`; the unrounded value is `0.0505`). The
printed rounded inputs give `0.0503` instead. -/
theorem marshall_example :
    let a₁ := marshallA ((29 / 51) * (1 - 29 / 51) / 51) ((143 / 160) * (1 - 143 / 160) / 160)
      ((122 / 564) * (1 - 122 / 564) / 564) (29 / 51) (143 / 160) (122 / 564)
    let a₀ := marshallA ((21 / 33) * (1 - 21 / 33) / 33) ((168 / 184) * (1 - 168 / 184) / 184)
      ((101 / 580) * (1 - 101 / 580) / 580) (21 / 33) (168 / 184) (101 / 580)
    let P₁ := trueProportionPV (29 / 51) (143 / 160) (122 / 564)
    let P₀ := trueProportionPV (21 / 33) (168 / 184) (101 / 580)
    (0.000650 < a₁ ∧ a₁ < 0.000660) ∧ (0.000580 < a₀ ∧ a₀ < 0.000590) ∧
      (0.0500 < a₀ / (P₀ * (1 - P₀)) ^ 2 + a₁ / (P₁ * (1 - P₁)) ^ 2 ∧
        a₀ / (P₀ * (1 - P₀)) ^ 2 + a₁ / (P₁ * (1 - P₁)) ^ 2 < 0.0510) := by
  norm_num [marshallA, trueProportionPV]

/-- **Table 10.3, predictive value weighting.** The weighted cells are
`122 · 29/51 + 442 · (1 - 143/160) ≈ 116.335`, `122 · (1 - 29/51) + 442 · 143/160 ≈ 447.665`,
`101 · 21/33 + 479 · (1 - 168/184) ≈ 105.925`, `101 · (1 - 21/33) + 479 · 168/184 ≈ 474.075`.
The book prints `116.34, 447.67, 105.92, 474.08`; the second cell rounds to `447.66`. -/
theorem pvw_example :
    (116.33 < pvwExposed 122 442 (29 / 51) (143 / 160) ∧
        pvwExposed 122 442 (29 / 51) (143 / 160) < 116.34) ∧
      (447.66 < pvwUnexposed 122 442 (29 / 51) (143 / 160) ∧
        pvwUnexposed 122 442 (29 / 51) (143 / 160) < 447.67) ∧
      (105.92 < pvwExposed 101 479 (21 / 33) (168 / 184) ∧
        pvwExposed 101 479 (21 / 33) (168 / 184) < 105.93) ∧
      (474.07 < pvwUnexposed 101 479 (21 / 33) (168 / 184) ∧
        pvwUnexposed 101 479 (21 / 33) (168 / 184) < 474.08) := by
  norm_num [pvwExposed, pvwUnexposed]

/-- **Inverse-variance pooling (Chapter 10, "Misclassification Example").** With standard errors
`0.225` and `0.25` the pooled variance is `81/2896 ≈ 0.0280` (printed `0.028`). The pooled
estimate in the book uses `0.226` in place of `0.225`; that variance is `≈ 0.0281`, also `0.028`
to the printed precision. -/
theorem ivPooled_example :
    ivPooledVariance ![0.225 ^ 2, 0.25 ^ 2] = 81 / 2896 ∧
      0.0280 < ivPooledVariance ![0.226 ^ 2, (0.25 : ℝ) ^ 2] ∧
      ivPooledVariance ![0.226 ^ 2, (0.25 : ℝ) ^ 2] < 0.0282 := by
  norm_num [ivPooledVariance, ivTotalWeight, Fin.sum_univ_two]

/-- Lower bound for `exp x`, `x ≥ 0`, from a partial sum of its Taylor series. -/
theorem lt_exp_of_taylor {x a : ℝ} (hx : 0 ≤ x) (n : ℕ)
    (h : a < ∑ i ∈ Finset.range n, x ^ i / i.factorial) : a < Real.exp x :=
  h.trans_le (Real.sum_le_exp_of_nonneg hx n)

/-- Upper bound for `exp x`, `0 ≤ x ≤ 1`, from a partial sum of its Taylor series and the
remainder bound of Mathlib (`Real.exp_bound'`). -/
theorem exp_lt_of_taylor {x a : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : ∑ i ∈ Finset.range n, x ^ i / i.factorial + x ^ n * (n + 1) / (n.factorial * n) < a) :
    Real.exp x < a :=
  (Real.exp_bound' hx₀ hx₁ hn).trans_lt h

/-- The Greenland variance of the smoking and breast cancer example (inputs of
`greenland_example`). -/
noncomputable def exampleGreenlandVar : ℝ :=
  greenlandNondiff ((128 / 164) * (1 - 128 / 164) / 164) ((465 / 470) * (1 - 465 / 470) / 470)
    (128 / 164) (465 / 470) (215 / 1664) 1664 (668 / 4964) 4964

/-- The adjusted odds ratio of the smoking and breast cancer example (direct formula). -/
noncomputable def exampleGreenlandOR : ℝ :=
  (215 / 1664 + 465 / 470 - 1) * (128 / 164 - 668 / 4964) /
    ((668 / 4964 + 465 / 470 - 1) * (128 / 164 - 215 / 1664))

/-- **Equation 10.3, recomputed.** The interval `OR_b exp (∓1.96 √Var)` of the smoking and breast
cancer example has endpoints in `(0.785, 0.795)` and `(1.135, 1.145)`, the printed
`(0.79, 1.14)`. -/
theorem greenland_example_interval :
    (0.785 < exampleGreenlandOR * Real.exp (-(1.96 * √exampleGreenlandVar)) ∧
        exampleGreenlandOR * Real.exp (-(1.96 * √exampleGreenlandVar)) < 0.795) ∧
      (1.135 < exampleGreenlandOR * Real.exp (1.96 * √exampleGreenlandVar) ∧
        exampleGreenlandOR * Real.exp (1.96 * √exampleGreenlandVar) < 1.145) := by
  have hV₁ : (0.00889 : ℝ) < exampleGreenlandVar := by
    norm_num [exampleGreenlandVar, greenlandNondiff, trueProportion]
  have hV₂ : exampleGreenlandVar < 0.00890 := by
    norm_num [exampleGreenlandVar, greenlandNondiff, trueProportion]
  have hO₁ : (0.94885 : ℝ) < exampleGreenlandOR := by norm_num [exampleGreenlandOR]
  have hO₂ : exampleGreenlandOR < 0.94886 := by norm_num [exampleGreenlandOR]
  have hs₁ : (0.0942 : ℝ) < √exampleGreenlandVar := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hs₂ : √exampleGreenlandVar < 0.0944 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
  have he₁ : (1.2027 : ℝ) < Real.exp (1.96 * √exampleGreenlandVar) :=
    (lt_exp_of_taylor (x := 0.1846) (by norm_num) 5
      (by norm_num [Finset.sum_range_succ, Nat.factorial])).trans
      (Real.exp_lt_exp.2 (by linarith))
  have he₂ : Real.exp (1.96 * √exampleGreenlandVar) < 1.2034 :=
    (Real.exp_lt_exp.2 (by linarith : 1.96 * √exampleGreenlandVar < 0.1851)).trans
      (exp_lt_of_taylor (by norm_num) (by norm_num) (n := 5) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hpos := Real.exp_pos (1.96 * √exampleGreenlandVar)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  refine ⟨⟨?_, ?_⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rw [lt_div_iff₀ hpos]
    nlinarith
  · rw [div_lt_iff₀ hpos]
    nlinarith

/-- The Marshall variance of the antibiotics and sudden infant death example (inputs of
`marshall_example`). -/
noncomputable def exampleMarshallVar : ℝ :=
  marshallA ((21 / 33) * (1 - 21 / 33) / 33) ((168 / 184) * (1 - 168 / 184) / 184)
      ((101 / 580) * (1 - 101 / 580) / 580) (21 / 33) (168 / 184) (101 / 580) /
      (trueProportionPV (21 / 33) (168 / 184) (101 / 580) *
        (1 - trueProportionPV (21 / 33) (168 / 184) (101 / 580))) ^ 2 +
    marshallA ((29 / 51) * (1 - 29 / 51) / 51) ((143 / 160) * (1 - 143 / 160) / 160)
      ((122 / 564) * (1 - 122 / 564) / 564) (29 / 51) (143 / 160) (122 / 564) /
      (trueProportionPV (29 / 51) (143 / 160) (122 / 564) *
        (1 - trueProportionPV (29 / 51) (143 / 160) (122 / 564))) ^ 2

/-- The adjusted odds ratio `(P₁ / (1 - P₁)) / (P₀ / (1 - P₀))` of the same example. -/
noncomputable def exampleMarshallOR : ℝ :=
  (trueProportionPV (29 / 51) (143 / 160) (122 / 564) /
      (1 - trueProportionPV (29 / 51) (143 / 160) (122 / 564))) /
    (trueProportionPV (21 / 33) (168 / 184) (101 / 580) /
      (1 - trueProportionPV (21 / 33) (168 / 184) (101 / 580)))

/-- **Marshall's example, odds ratio and interval.** The adjusted odds ratio lies in
`(1.16307, 1.16308)` (printed `1.16`), the variance in `(0.05050, 0.05051)`, and the interval
`OR_b exp (∓1.96 √Var)` has endpoints in `(0.745, 0.755)` and `(1.805, 1.815)`, the printed
`(0.75, 1.81)`. -/
theorem marshall_example_interval :
    (1.16307 < exampleMarshallOR ∧ exampleMarshallOR < 1.16308) ∧
      (0.05050 < exampleMarshallVar ∧ exampleMarshallVar < 0.05051) ∧
      (0.745 < exampleMarshallOR * Real.exp (-(1.96 * √exampleMarshallVar)) ∧
        exampleMarshallOR * Real.exp (-(1.96 * √exampleMarshallVar)) < 0.755) ∧
      (1.805 < exampleMarshallOR * Real.exp (1.96 * √exampleMarshallVar) ∧
        exampleMarshallOR * Real.exp (1.96 * √exampleMarshallVar) < 1.815) := by
  have hV₁ : (0.05050 : ℝ) < exampleMarshallVar := by
    norm_num [exampleMarshallVar, marshallA, trueProportionPV]
  have hV₂ : exampleMarshallVar < 0.05051 := by
    norm_num [exampleMarshallVar, marshallA, trueProportionPV]
  have hO₁ : (1.16307 : ℝ) < exampleMarshallOR := by
    norm_num [exampleMarshallOR, trueProportionPV]
  have hO₂ : exampleMarshallOR < 1.16308 := by norm_num [exampleMarshallOR, trueProportionPV]
  have hs₁ : (0.22472 : ℝ) < √exampleMarshallVar := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hs₂ : √exampleMarshallVar < 0.22475 := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
  have he₁ : (1.5534 : ℝ) < Real.exp (1.96 * √exampleMarshallVar) :=
    (lt_exp_of_taylor (x := 0.44045) (by norm_num) 9
      (by norm_num [Finset.sum_range_succ, Nat.factorial])).trans
      (Real.exp_lt_exp.2 (by linarith))
  have he₂ : Real.exp (1.96 * √exampleMarshallVar) < 1.5536 :=
    (Real.exp_lt_exp.2 (by linarith : 1.96 * √exampleMarshallVar < 0.44051)).trans
      (exp_lt_of_taylor (by norm_num) (by norm_num) (n := 9) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hpos := Real.exp_pos (1.96 * √exampleMarshallVar)
  rw [Real.exp_neg, ← div_eq_mul_inv]
  refine ⟨⟨hO₁, hO₂⟩, ⟨hV₁, hV₂⟩, ⟨?_, ?_⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rw [lt_div_iff₀ hpos]
    nlinarith
  · rw [div_lt_iff₀ hpos]
    nlinarith

/-- The pooled log odds ratio of Chapter 10, "Misclassification Example", as printed: estimates
`ln 1.16` and `ln 1.36` with standard errors `0.226` and `0.25`. -/
noncomputable def examplePooled : ℝ :=
  ivPooled ![Real.log 1.16, Real.log 1.36] ![0.226 ^ 2, 0.25 ^ 2]

/-- **Pooled estimate and interval, recomputed.** The pooled log odds ratio lies in
`(0.21994, 0.21997)` (printed `0.22`), the pooled odds ratio in `(1.245, 1.255)` (printed `1.25`),
and with the variance `81/2896` of `ivPooled_example` (computed in the book from `0.225`) the
interval `exp (pooled ∓ 1.96 √Var)` has endpoints in `(0.895, 0.905)` and `(1.725, 1.735)`, the
printed `(0.90, 1.73)`. -/
theorem ivPooled_example_interval :
    (0.21994 < examplePooled ∧ examplePooled < 0.21997) ∧
      (1.245 < Real.exp examplePooled ∧ Real.exp examplePooled < 1.255) ∧
      (0.895 < Real.exp (examplePooled - 1.96 * √(81 / 2896)) ∧
        Real.exp (examplePooled - 1.96 * √(81 / 2896)) < 0.905) ∧
      (1.725 < Real.exp (examplePooled + 1.96 * √(81 / 2896)) ∧
        Real.exp (examplePooled + 1.96 * √(81 / 2896)) < 1.735) := by
  have hl₁ : (0.14841 : ℝ) < Real.log 1.16 := (Real.lt_log_iff_exp_lt (by norm_num)).2
    (exp_lt_of_taylor (by norm_num) (by norm_num) (n := 6) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hl₂ : Real.log 1.16 < 0.14843 := (Real.log_lt_iff_lt_exp (by norm_num)).2
    (lt_exp_of_taylor (by norm_num) 7 (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hm₁ : (0.30748 : ℝ) < Real.log 1.36 := (Real.lt_log_iff_exp_lt (by norm_num)).2
    (exp_lt_of_taylor (by norm_num) (by norm_num) (n := 7) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hm₂ : Real.log 1.36 < 0.30749 := (Real.log_lt_iff_lt_exp (by norm_num)).2
    (lt_exp_of_taylor (by norm_num) 8 (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  have hP : examplePooled = (Real.log 1.16 * (1 / 0.226 ^ 2) + Real.log 1.36 * (1 / 0.25 ^ 2)) /
      (1 / 0.226 ^ 2 + 1 / 0.25 ^ 2) := by
    simp only [examplePooled, ivPooled, ivTotalWeight, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hp₁ : (0.21994 : ℝ) < examplePooled := by
    rw [hP, lt_div_iff₀ (by norm_num)]
    norm_num
    linarith
  have hp₂ : examplePooled < 0.21997 := by
    rw [hP, div_lt_iff₀ (by norm_num)]
    norm_num
    linarith
  have hs₁ : (0.16724 : ℝ) < √(81 / 2896) := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hs₂ : √(81 / 2896 : ℝ) < 0.16725 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  refine ⟨⟨hp₁, hp₂⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (lt_exp_of_taylor (x := 0.21994) (by norm_num) 6
      (by norm_num [Finset.sum_range_succ, Nat.factorial])).trans (Real.exp_lt_exp.2 hp₁)
  · exact (Real.exp_lt_exp.2 hp₂).trans (exp_lt_of_taylor (by norm_num) (by norm_num)
      (n := 6) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  · have h : Real.exp (examplePooled - 1.96 * √(81 / 2896)) =
        (Real.exp (1.96 * √(81 / 2896) - examplePooled))⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    rw [h, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    exact (Real.exp_lt_exp.2
      (by linarith : 1.96 * √(81 / 2896 : ℝ) - examplePooled < 0.10787)).trans
      (exp_lt_of_taylor (by norm_num) (by norm_num) (n := 6) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
  · have h : Real.exp (examplePooled - 1.96 * √(81 / 2896)) =
        (Real.exp (1.96 * √(81 / 2896) - examplePooled))⁻¹ := by
      rw [← Real.exp_neg]
      ring_nf
    rw [h, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    exact (lt_exp_of_taylor (x := 0.10782) (by norm_num) 6
      (by norm_num [Finset.sum_range_succ, Nat.factorial])).trans
      (Real.exp_lt_exp.2 (by linarith))
  · exact (lt_exp_of_taylor (x := 0.54773) (by norm_num) 9
      (by norm_num [Finset.sum_range_succ, Nat.factorial])).trans
      (Real.exp_lt_exp.2 (by linarith))
  · exact (Real.exp_lt_exp.2
      (by linarith : examplePooled + 1.96 * √(81 / 2896 : ℝ) < 0.54778)).trans
      (exp_lt_of_taylor (by norm_num) (by norm_num) (n := 9) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))

/-- **Table 10.3, odds ratio.** The odds ratio of the weighted table,
`(116.335 · 474.075) / (447.665 · 105.925)`, lies in `(1.1630, 1.1632)` (printed `1.16`); it is the
odds ratio `exampleMarshallOR` of the Marshall example, as Chapter 10 states. -/
theorem pvw_example_or :
    pvwExposed 122 442 (29 / 51) (143 / 160) * pvwUnexposed 101 479 (21 / 33) (168 / 184) /
        (pvwUnexposed 122 442 (29 / 51) (143 / 160) * pvwExposed 101 479 (21 / 33) (168 / 184)) =
      exampleMarshallOR ∧
      1.1630 < exampleMarshallOR ∧ exampleMarshallOR < (1.1632 : ℝ) := by
  refine ⟨?_, by norm_num [exampleMarshallOR, trueProportionPV],
    by norm_num [exampleMarshallOR, trueProportionPV]⟩
  norm_num [pvwExposed, pvwUnexposed, exampleMarshallOR, trueProportionPV]

/-- **Differential and nondifferential formulas differ.** On the inputs of `greenland_example`,
adding the two differential terms with shared `SE` and `SP` does not give the nondifferential
variance: the shared parameters enter both groups, so their contributions add before squaring. -/
theorem greenland_differential_ne_nondifferential :
    greenlandTerm ((128 / 164) * (1 - 128 / 164) / 164) ((465 / 470) * (1 - 465 / 470) / 470)
        (128 / 164) (465 / 470) (215 / 1664) 1664 +
      greenlandTerm ((128 / 164) * (1 - 128 / 164) / 164) ((465 / 470) * (1 - 465 / 470) / 470)
        (128 / 164) (465 / 470) (668 / 4964) 4964 ≠ exampleGreenlandVar := by
  norm_num [greenlandTerm, exampleGreenlandVar, greenlandNondiff, trueProportion]

end Examples

end BiasAnalysis.VarianceFormulas

end CausalInference
