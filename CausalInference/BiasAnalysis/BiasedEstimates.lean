/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.BiasAnalysis.VarianceFormulas
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Bias adjustment of a single contrast

The bias adjustment of TSD 3, Sections 5.2 to 5.4, for one study estimate and for a pairwise
synthesis, without the network layer. A lower-quality study estimates not the effect `d` but
`d + β`, where the study-specific bias `β` has a distribution with mean `b` and variance `κ²`
(from meta-epidemiological data, Section 5.2, or from experts, Section 5.4), and the mean `b`
is itself estimated by `b̂` with variance `s²`. The study effect `d` is a fixed real number
(the trial-specific effect in a random effects synthesis, conditionally on its value).

## Main results

* `adjusted_mean_variance_of_cov` (moment form): if `y = d + β + ε` with `E β = b`, `E ε = 0`,
  `E b̂ = b`, `β` uncorrelated with `ε` and `b̂` uncorrelated with `β + ε`, the adjusted estimate
  `y - b̂` is unbiased for `d` with variance `Var β + Var ε + Var b̂ = κ² + V + s²`;
  `adjusted_mean_variance` is the special case of pairwise uncorrelated terms, and
  `cov_sum_eq_zero_example` separates the two conditions. `adjusted_mean`: in general the mean
  is `d + E β - E b̂`; `adjusted_not_transported`: an external mean bias that differs from the
  mean bias of the adjusted study leaves bias.
* `adjusted_hasLaw_of_indepFun` (Gaussian form): for `β ~ N(b, κ²)` independent of
  `ε ~ N(0, V)`, and `b̂ ~ N(b, s²)` independent of `β + ε`, the adjusted estimate has law
  `N(d, κ² + V + s²)`; `adjusted_hasLaw` is the case of three mutually independent terms.
* `adjusted_weight_lt`: the adjusted estimate is down-weighted, `1/(V + κ² + s²) < 1/V`.
* `ivPooled_mean_variance`: pooling independent unbiased (adjusted or high-quality) estimates
  by inverse variance gives an unbiased estimate with variance `1 / ∑ 1/Wᵢ`, the least
  variance of any weighted average (`ivPooledVariance_le` of
  `BiasAnalysis/VarianceFormulas.lean`).
* `variance_shared_adjustment`, `ivPooledVariance_lt_shared`: with one bias estimate `b̂`
  shared by several trials the adjusted estimates are correlated and the nominal pooled variance
  understates the true one. `ivWeights_minimize_shared`: the weights proportional to
  `1 / Var(yᵢ)` minimize the actual variance, which is then `1 / ∑ 1/Var(yᵢ) + Var(b̂)`.
* `biasModelCriterion_min` (TSD 3, Section 5.3): with two treatments and a free mean bias, the
  estimate of the effect is the pooled high-quality estimate; the lower-quality trials inform
  only the bias. `biasModelCriterion_fixed_bias_example`: fixing the bias at `0` lets them move
  the estimate. `biasModelCriterion_shift_of_no_high`, `lowQualityLaw_shift`,
  `lowQuality_not_identified`: without high-quality trials the effect is not identified, both
  for the criterion and for the product normal law of the estimates (`hasLaw_lowQualityLaw`).
* `wlsIntercept_unbiased` (TSD 3, Section 5.3, small-study bias): if `E yᵢ = d + γ Vᵢ`, the
  intercept formula of the regression of the estimates on the study variances is unbiased for
  `d`; `wlsRSS_le`: under `0 < Sxx` the formula is the unique weighted least squares minimizer,
  and `wlsRSS_signed_example` shows that signed weights can leave the objective unbounded below;
  `wMean_biased`: the weighted mean is biased by `γ V̄_w`;
  `smallStudy_not_identified_of_const`: with equal variances `d` is not identified.

The pairwise model of Section 5.3 is stated for weighted least squares with known variances;
for independent normal estimates this is maximum likelihood, but the likelihood is not
formalized. The pooling of several assessors' bias distributions in Section 5.4 is not stated
in the document and is not formalized.

## References

* S. Dias, A. J. Sutton, N. J. Welton, A. E. Ades, *NICE DSU Technical Support Document 3:
  Heterogeneity: Subgroups, Meta-Regression, Bias and Bias-Adjustment* (2011, updated 2012),
  Sections 5.2, 5.3 and 5.4, equations (8) and (9).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

open scoped NNReal

namespace CausalInference.BiasAnalysis.BiasedEstimates

open VarianceFormulas

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The mean of the adjusted estimate.** For integrable `β`, `ε`, `b̂` with `E ε = 0`, the
adjusted estimate `d + β + ε - b̂` has mean `d + E β - E b̂`: it is unbiased for `d` exactly when
the external estimate `b̂` has the mean of the bias of the study being adjusted. -/
theorem adjusted_mean {β ε bh : Ω → ℝ} (d : ℝ) (hβi : Integrable β P) (hεi : Integrable ε P)
    (hbi : Integrable bh P) (hεm : P[ε] = 0) :
    P[fun ω => d + β ω + ε ω - bh ω] = d + P[β] - P[bh] := by
  rw [integral_sub (f := fun ω => d + β ω + ε ω) ((integrable_const d).add hβi |>.add hεi) hbi,
    integral_add (f := fun ω => d + β ω) ((integrable_const d).add hβi) hεi,
    integral_add (f := fun _ => d) (integrable_const d) hβi]
  simp [hεm]

/-- **Bias adjustment of one estimate: moments, under the reported-estimate condition** (TSD 3,
Sections 5.2 and 5.4, equation (9)). A lower-quality study reports `y = d + β + ε`: the effect
`d`, a study-specific bias `β` with mean `b` (and variance `κ² = Var β`), and sampling error `ε`
with mean `0` (and variance `V = Var ε`). The external estimate `b̂` of the mean bias has mean
`b` (and variance `s² = Var b̂`). If `β`, `ε` and `b̂` are square integrable, the bias is
uncorrelated with the sampling error, and `b̂` is uncorrelated with the random part `β + ε` of
the reported estimate (no condition on its covariance with `β` and `ε` separately), the adjusted
estimate `y - b̂` has mean `d` and variance `κ² + V + s²`. -/
theorem adjusted_mean_variance_of_cov {β ε bh : Ω → ℝ} (d b : ℝ) (hβ : MemLp β 2 P)
    (hε : MemLp ε 2 P) (hb : MemLp bh 2 P) (hβm : P[β] = b) (hεm : P[ε] = 0) (hbm : P[bh] = b)
    (h1 : cov[β, ε; P] = 0) (h23 : cov[β + ε, bh; P] = 0) :
    P[fun ω => d + β ω + ε ω - bh ω] = d ∧
      Var[fun ω => d + β ω + ε ω - bh ω; P] = Var[β; P] + Var[ε; P] + Var[bh; P] := by
  constructor
  · rw [adjusted_mean d (hβ.integrable one_le_two) (hε.integrable one_le_two)
      (hb.integrable one_le_two) hεm, hβm, hbm]
    ring
  · have e : (fun ω => d + β ω + ε ω - bh ω) = fun ω => d + (β + ε - bh) ω := by
      funext ω; simp only [Pi.sub_apply, Pi.add_apply]; ring
    rw [e, variance_const_add ((hβ.add hε).sub hb).aestronglyMeasurable,
      variance_sub (hβ.add hε) hb, variance_add hβ hε, h1, h23]
    ring

/-- **Bias adjustment of one estimate: moments** (TSD 3, Sections 5.2 and 5.4, equation (9)).
The special case of `adjusted_mean_variance_of_cov` in which `β`, `ε` and `b̂` are pairwise
uncorrelated: the adjusted estimate `y - b̂` has mean `d` and variance `κ² + V + s²`. -/
theorem adjusted_mean_variance {β ε bh : Ω → ℝ} (d b : ℝ) (hβ : MemLp β 2 P)
    (hε : MemLp ε 2 P) (hb : MemLp bh 2 P) (hβm : P[β] = b) (hεm : P[ε] = 0) (hbm : P[bh] = b)
    (h1 : cov[β, ε; P] = 0) (h2 : cov[β, bh; P] = 0) (h3 : cov[ε, bh; P] = 0) :
    P[fun ω => d + β ω + ε ω - bh ω] = d ∧
      Var[fun ω => d + β ω + ε ω - bh ω; P] = Var[β; P] + Var[ε; P] + Var[bh; P] :=
  adjusted_mean_variance_of_cov d b hβ hε hb hβm hεm hbm h1
    (by rw [covariance_add_left hβ hε hb, h2, h3, add_zero])

/-- **The reported-estimate condition is weaker.** For independent standard normal `β` and `ε`,
the external estimate `b̂ = β - ε` is uncorrelated with `β + ε` (so
`adjusted_mean_variance_of_cov` applies), while its covariances with `β` and with `ε` are `1`
and `-1` (so `adjusted_mean_variance` does not). -/
theorem cov_sum_eq_zero_example {β ε : Ω → ℝ} (hβ : MemLp β 2 P) (hε : MemLp ε 2 P)
    (hind : cov[β, ε; P] = 0) (hvβ : Var[β; P] = 1) (hvε : Var[ε; P] = 1) :
    cov[β + ε, β - ε; P] = 0 ∧ cov[β, β - ε; P] = 1 ∧ cov[ε, β - ε; P] = -1 := by
  have hεβ : cov[ε, β; P] = 0 := by rw [covariance_comm, hind]
  refine ⟨?_, ?_, ?_⟩
  · rw [covariance_add_left hβ hε (hβ.sub hε), covariance_sub_right hβ hβ hε,
      covariance_sub_right hε hβ hε, covariance_self hβ.aemeasurable,
      covariance_self hε.aemeasurable, hind, hεβ, hvβ, hvε]
    ring
  · rw [covariance_sub_right hβ hβ hε, covariance_self hβ.aemeasurable, hind, hvβ]
    ring
  · rw [covariance_sub_right hε hβ hε, covariance_self hε.aemeasurable, hεβ, hvε]
    ring

/-- **Countermodel: the external mean bias does not transport.** Let the study being adjusted
have bias `β = 1` and the external estimate be `b̂ = 0` (estimating the mean bias of a different
population of studies), with any square integrable centered sampling error `ε`. Every
hypothesis of `adjusted_mean_variance_of_cov` holds with `b = 1` except `E b̂ = b`, and the
adjusted estimate has mean `d + 1`, not `d`: one unit of bias is left. -/
theorem adjusted_not_transported {ε : Ω → ℝ} (d : ℝ) (hε : MemLp ε 2 P) (hεm : P[ε] = 0) :
    let β : Ω → ℝ := fun _ => 1
    let bh : Ω → ℝ := fun _ => 0
    MemLp β 2 P ∧ MemLp bh 2 P ∧ P[β] = 1 ∧ cov[β, ε; P] = 0 ∧ cov[β + ε, bh; P] = 0 ∧
      P[bh] ≠ 1 ∧ P[fun ω => d + β ω + ε ω - bh ω] = d + 1 := by
  intro β bh
  refine ⟨memLp_const 1, memLp_const 0, by simp [β], by simp [β, covariance_const_left],
    by simp [bh, covariance_const_right], by simp [bh], ?_⟩
  rw [adjusted_mean d (integrable_const 1) (hε.integrable one_le_two) (integrable_const 0) hεm]
  simp

omit [IsProbabilityMeasure P] in
/-- **Bias adjustment of one estimate: Gaussian law, under the reported-estimate condition**
(TSD 3, Section 5.2, equation (9) with `β ~ N(b₀, κ²)`). If the bias `β ~ N(b, κ²)` and the
sampling error `ε ~ N(0, V)` are independent, and the estimate `b̂ ~ N(b, s²)` of the mean bias
is independent of the random part `β + ε` of the reported estimate (no condition on its joint
law with `β` and `ε` separately), the adjusted estimate `d + β + ε - b̂` has law
`N(d, κ² + V + s²)`. -/
theorem adjusted_hasLaw_of_indepFun {β ε bh : Ω → ℝ} (d b : ℝ) (κ2 V s2 : ℝ≥0)
    (hmβ : Measurable β) (hmε : Measurable ε) (hmb : Measurable bh) (h01 : IndepFun β ε P)
    (hind : IndepFun (β + ε) bh P)
    (hβ : HasLaw β (gaussianReal b κ2) P) (hε : HasLaw ε (gaussianReal 0 V) P)
    (hb : HasLaw bh (gaussianReal b s2) P) :
    HasLaw (fun ω => d + β ω + ε ω - bh ω) (gaussianReal d (κ2 + V + s2)) P := by
  have hsum : HasLaw (β + ε) (gaussianReal (b + 0) (κ2 + V)) P :=
    ⟨(hmβ.add hmε).aemeasurable, gaussianReal_add_gaussianReal_of_indepFun h01 hβ hε⟩
  have h2 : IndepFun (β + ε) (-bh) P := hind.comp measurable_id measurable_neg
  have hsum2 := gaussianReal_add_gaussianReal_of_indepFun h2 hsum (gaussianReal_neg hb)
  have hlaw : HasLaw (β + ε + -bh) (gaussianReal (b + 0 + -b) (κ2 + V + s2)) P :=
    ⟨((hmβ.add hmε).add hmb.neg).aemeasurable, hsum2⟩
  have := gaussianReal_const_add hlaw d
  convert this using 2
  · simp only [Pi.add_apply, Pi.neg_apply]; ring
  · ring

omit [IsProbabilityMeasure P] in
/-- **Bias adjustment of one estimate: Gaussian law** (TSD 3, Section 5.2, equation (9)). The
special case of `adjusted_hasLaw_of_indepFun` in which `β ~ N(b, κ²)`, `ε ~ N(0, V)` and
`b̂ ~ N(b, s²)` are mutually independent: the adjusted estimate has law `N(d, κ² + V + s²)`. -/
theorem adjusted_hasLaw {β ε bh : Ω → ℝ} (d b : ℝ) (κ2 V s2 : ℝ≥0) (hmβ : Measurable β)
    (hmε : Measurable ε) (hmb : Measurable bh) (hind : iIndepFun ![β, ε, bh] P)
    (hβ : HasLaw β (gaussianReal b κ2) P) (hε : HasLaw ε (gaussianReal 0 V) P)
    (hb : HasLaw bh (gaussianReal b s2) P) :
    HasLaw (fun ω => d + β ω + ε ω - bh ω) (gaussianReal d (κ2 + V + s2)) P := by
  have hmeas : ∀ i, Measurable (![β, ε, bh] i) := fun i => by
    fin_cases i <;> simpa
  have h01 : IndepFun β ε P := by simpa using hind.indepFun (i := 0) (j := 1) (by decide)
  have h2 : IndepFun (β + ε) bh P :=
    (hind.indepFun_prodMk hmeas 0 1 2 (by decide) (by decide)).comp
      (measurable_fst.add measurable_snd) measurable_id
  exact adjusted_hasLaw_of_indepFun d b κ2 V s2 hmβ hmε hmb h01 h2 hβ hε hb

/-- **Down-weighting.** The inverse-variance weight `1 / (V + κ² + s²)` of an adjusted estimate
is below the weight `1 / V` of the unadjusted one whenever the bias distribution has positive
variance or its mean is uncertain (`κ² + s² > 0`). -/
theorem adjusted_weight_lt {V κ2 s2 : ℝ} (hV : 0 < V) (h : 0 < κ2 + s2) :
    1 / (V + κ2 + s2) < 1 / V :=
  one_div_lt_one_div_of_lt hV (by linarith)

/-- **Pooling adjusted estimates.** Let `θ₀, …, θ_{k-1}` be pairwise independent square
integrable estimates of a common effect `d`, unbiased (`E θᵢ = d`), with variances `Wᵢ > 0`
(for an adjusted estimate `Wᵢ = Vᵢ + κ² + s²`, `adjusted_mean_variance`). The inverse-variance
pooled estimate is unbiased for `d` and its variance is `1 / ∑ᵢ (1 / Wᵢ)`, the least variance
of any weighted average with weights summing to one (`ivPooledVariance_le`). -/
theorem ivPooled_mean_variance {k : ℕ} (hk : 0 < k) {θ : Fin k → Ω → ℝ} {W : Fin k → ℝ}
    {d : ℝ} (hW : ∀ i, 0 < W i) (hθ : ∀ i, MemLp (θ i) 2 P) (hmean : ∀ i, P[θ i] = d)
    (hvar : ∀ i, Var[θ i; P] = W i) (hind : Pairwise fun i j => IndepFun (θ i) (θ j) P) :
    P[fun ω => ivPooled (fun i => θ i ω) W] = d ∧
      Var[fun ω => ivPooled (fun i => θ i ω) W; P] = ivPooledVariance W := by
  obtain ⟨hsum, hfov⟩ := firstOrderVariance_ivWeights hW hk
  have e : (fun ω => ivPooled (fun i => θ i ω) W) =
      fun ω => ∑ i, (1 / W i) / ivTotalWeight W * θ i ω :=
    funext fun ω => (ivPooled_eq_sum_weights _ _ hW hk).2
  rw [e]
  refine ⟨?_, ?_⟩
  · rw [integral_finsetSum _ fun i _ => ((hθ i).integrable one_le_two).const_mul _]
    simp only [integral_const_mul, hmean, ← Finset.sum_mul, hsum, one_mul]
  · rw [variance_linearization θ hθ hind]
    simp only [hvar]
    exact hfov

/-! ### A shared bias estimate correlates the adjusted estimates -/

/-- **Adjusting several trials with one bias estimate.** Let `y₀, …, y_{k-1}` be pairwise
independent square integrable estimates, uncorrelated with a common bias estimate `b̂`, and let
`c` be weights summing to one. The weighted average of the adjusted estimates `yᵢ - b̂` has
variance `∑ᵢ cᵢ² Var(yᵢ) + Var(b̂)`: the variance of `b̂` enters with weight `1`, not with
weight `∑ᵢ cᵢ²` as it would for independent adjustments. -/
theorem variance_shared_adjustment {k : ℕ} {y : Fin k → Ω → ℝ} {bh : Ω → ℝ} {c : Fin k → ℝ}
    (hy : ∀ i, MemLp (y i) 2 P) (hb : MemLp bh 2 P)
    (hind : Pairwise fun i j => IndepFun (y i) (y j) P) (hcov : ∀ i, cov[y i, bh; P] = 0)
    (hc : ∑ i, c i = 1) :
    Var[fun ω => ∑ i, c i * (y i ω - bh ω); P] =
      firstOrderVariance c (fun i => Var[y i; P]) + Var[bh; P] := by
  have e : (fun ω => ∑ i, c i * (y i ω - bh ω)) =
      (fun ω => ∑ i, c i * y i ω) - bh := by
    funext ω
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc, one_mul, Pi.sub_apply]
  have hS : MemLp (fun ω => ∑ i, c i * y i ω) 2 P :=
    memLp_finsetSum _ fun i _ => (hy i).const_mul (c i)
  rw [e, variance_sub hS hb, variance_linearization y hy hind,
    covariance_fun_sum_left (fun i => (hy i).const_mul (c i)) hb]
  simp only [covariance_const_mul_left, hcov, mul_zero, Finset.sum_const_zero]
  ring

/-- **Shared adjustment: the nominal pooled variance is too small.** With `k ≥ 2` trials, a
common bias estimate of variance `s² > 0`, and the inverse-variance weights computed from the
nominal variances `Wᵢ = Var(yᵢ) + s²`, the actual variance of the pooled adjusted estimate
exceeds the nominal value `ivPooledVariance W` (it equals it plus `s² (1 - ∑ cᵢ²)`). The
statement is about the reported variance: the variance formula of `ivPooled_mean_variance`
needs independent adjustments. The choice of weights is a separate matter; by
`ivWeights_minimize_shared` the weights proportional to `1 / Var(yᵢ)` (not to `1 / Wᵢ`) are
optimal under a shared adjustment, and when the `Var(yᵢ)` are equal the nominal weights are the
optimal ones. -/
theorem ivPooledVariance_lt_shared {k : ℕ} (hk : 2 ≤ k) {y : Fin k → Ω → ℝ} {bh : Ω → ℝ}
    (hy : ∀ i, MemLp (y i) 2 P) (hb : MemLp bh 2 P)
    (hind : Pairwise fun i j => IndepFun (y i) (y j) P) (hcov : ∀ i, cov[y i, bh; P] = 0)
    (hs : 0 < Var[bh; P]) :
    ivPooledVariance (fun i => Var[y i; P] + Var[bh; P]) <
      Var[fun ω => ∑ i, (1 / (Var[y i; P] + Var[bh; P])) /
        ivTotalWeight (fun i => Var[y i; P] + Var[bh; P]) * (y i ω - bh ω); P] := by
  set W : Fin k → ℝ := fun i => Var[y i; P] + Var[bh; P] with hWdef
  have hW : ∀ i, 0 < W i := fun i => by
    simp only [hWdef]; linarith [variance_nonneg (y i) P]
  obtain ⟨hsum, hfov⟩ := firstOrderVariance_ivWeights hW (by omega)
  set c : Fin k → ℝ := fun i => (1 / W i) / ivTotalWeight W with hcdef
  have hc0 : ∀ i, 0 < c i := fun i => by
    have : 0 < ivTotalWeight W := by
      have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
      exact Finset.sum_pos (fun i _ => one_div_pos.2 (hW i)) Finset.univ_nonempty
    exact div_pos (one_div_pos.2 (hW i)) this
  rw [variance_shared_adjustment hy hb hind hcov hsum]
  -- actual minus nominal is `s² (1 - ∑ cᵢ²)`
  have hfov' : firstOrderVariance c W =
      firstOrderVariance c (fun i => Var[y i; P]) + Var[bh; P] * ∑ i, c i ^ 2 := by
    simp only [firstOrderVariance, hWdef, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : ∑ i, c i ^ 2 < 1 := by
    have h01 : c ⟨0, by omega⟩ + c ⟨1, by omega⟩ ≤ ∑ i, c i := by
      have := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin k)))
        (fun i _ _ => (hc0 i).le)
      rwa [Finset.sum_pair (by simp [Fin.ext_iff])] at this
    have hle : ∀ i, c i ≤ 1 := fun i => by
      rw [← hsum]
      exact Finset.single_le_sum (fun j _ => (hc0 j).le) (Finset.mem_univ i)
    have hlt0 : c ⟨0, by omega⟩ < 1 := by linarith [hc0 ⟨1, by omega⟩]
    rw [← hsum]
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    · nlinarith [hc0 i, hle i]
    · nlinarith [hc0 ⟨0, by omega⟩]
  have := hfov
  rw [hfov'] at this
  nlinarith

/-- **Optimal weights under a shared adjustment.** Under the hypotheses of
`variance_shared_adjustment`, with `k ≥ 1` trials of positive variances `Var(yᵢ) > 0`, every
weighted average `∑ᵢ cᵢ (yᵢ - b̂)` with `∑ᵢ cᵢ = 1` has variance at least
`ivPooledVariance (Var y) + Var(b̂)`, and the inverse-variance weights
`cᵢ ∝ 1 / Var(yᵢ)` of the unadjusted estimates attain it. The shared term `Var(b̂)` does not
depend on the weights, so it does not change which weights are optimal. -/
theorem ivWeights_minimize_shared {k : ℕ} (hk : 0 < k) {y : Fin k → Ω → ℝ} {bh : Ω → ℝ}
    (hy : ∀ i, MemLp (y i) 2 P) (hb : MemLp bh 2 P)
    (hind : Pairwise fun i j => IndepFun (y i) (y j) P) (hcov : ∀ i, cov[y i, bh; P] = 0)
    (hV : ∀ i, 0 < Var[y i; P]) {c : Fin k → ℝ} (hc : ∑ i, c i = 1) :
    ivPooledVariance (fun i => Var[y i; P]) + Var[bh; P] ≤
        Var[fun ω => ∑ i, c i * (y i ω - bh ω); P] ∧
      Var[fun ω => ∑ i, (1 / Var[y i; P]) / ivTotalWeight (fun i => Var[y i; P]) *
          (y i ω - bh ω); P] = ivPooledVariance (fun i => Var[y i; P]) + Var[bh; P] := by
  obtain ⟨hsum, hfov⟩ := firstOrderVariance_ivWeights hV hk
  refine ⟨?_, ?_⟩
  · rw [variance_shared_adjustment hy hb hind hcov hc]
    linarith [ivPooledVariance_le hV hk hc]
  · rw [variance_shared_adjustment hy hb hind hcov hsum, hfov]

/-! ### Lower-quality trials with a free mean bias -/

/-- **Weighted sum of squares about a point.** For positive variances,
`∑ᵢ (yᵢ - c)² / Vᵢ = ∑ᵢ (yᵢ - ŷ)² / Vᵢ + (∑ᵢ 1 / Vᵢ) (ŷ - c)²`, where `ŷ = ivPooled y V`. -/
theorem sum_sq_div_eq {k : ℕ} (y V : Fin k → ℝ) (hV : ∀ i, 0 < V i) (hk : 0 < k) (c : ℝ) :
    ∑ i, (y i - c) ^ 2 / V i =
      ∑ i, (y i - ivPooled y V) ^ 2 / V i + ivTotalWeight V * (ivPooled y V - c) ^ 2 := by
  have hT : 0 < ivTotalWeight V := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact Finset.sum_pos (fun i _ => one_div_pos.2 (hV i)) Finset.univ_nonempty
  have e : ∀ a : ℝ, ∑ i, (y i - a) ^ 2 / V i =
      ∑ i, y i ^ 2 / V i - 2 * a * ∑ i, y i / V i + a ^ 2 * ivTotalWeight V := by
    intro a
    rw [ivTotalWeight, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by have := (hV i).ne'; field_simp; ring
  have hS : ∑ i, y i / V i = ivPooled y V * ivTotalWeight V := by
    rw [ivPooled, div_mul_cancel₀ _ hT.ne']
  rw [e, e, hS]
  ring

/-- The weighted least squares criterion of the bias model with a free mean bias: high-quality
estimates `yh` estimate `d` with variances `Vh`, lower-quality estimates `yl` estimate `d + b₀`
with variances `Vl`. -/
noncomputable def biasModelCriterion {m n : ℕ} (yh Vh : Fin m → ℝ) (yl Vl : Fin n → ℝ)
    (d b₀ : ℝ) : ℝ :=
  ∑ i, (yh i - d) ^ 2 / Vh i + ∑ i, (yl i - d - b₀) ^ 2 / Vl i

/-- **With two treatments, lower-quality trials say nothing about the effect** (TSD 3,
Section 5.3: "if there are only two treatments, the analysis would tell us about the bias
distribution, but it would add nothing to our knowledge of the true treatment effect"). In the
fixed effect model with known variances, high-quality estimates `yh i` of `d` and lower-quality
estimates `yl i` of `d + b₀` with an unrestricted mean bias `b₀`, the weighted least squares
estimate of `(d, b₀)` is unique and equals `d̂ = ivPooled yh Vh`, the pooled high-quality
estimate, which does not involve the lower-quality data, and `b̂₀ = ivPooled yl Vl - d̂`. When
the estimates are independent normal with the stated variances (a product likelihood with
diagonal covariance), the log-likelihood is `-1/2` times this criterion plus a constant, so
this is also the maximum likelihood estimate; with correlated estimates the likelihood involves
the full inverse covariance matrix and this diagonal criterion is not it. The likelihood itself
is not formalized here. At least one high-quality trial is needed: without one the effect is
not identified (`biasModelCriterion_shift_of_no_high`). -/
theorem biasModelCriterion_min {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {yh Vh : Fin m → ℝ}
    {yl Vl : Fin n → ℝ} (hVh : ∀ i, 0 < Vh i) (hVl : ∀ i, 0 < Vl i) (d b₀ : ℝ) :
    biasModelCriterion yh Vh yl Vl (ivPooled yh Vh) (ivPooled yl Vl - ivPooled yh Vh) ≤
        biasModelCriterion yh Vh yl Vl d b₀ ∧
      (biasModelCriterion yh Vh yl Vl d b₀ =
          biasModelCriterion yh Vh yl Vl (ivPooled yh Vh) (ivPooled yl Vl - ivPooled yh Vh) →
        d = ivPooled yh Vh ∧ b₀ = ivPooled yl Vl - ivPooled yh Vh) := by
  have hTh : 0 < ivTotalWeight Vh := by
    have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact Finset.sum_pos (fun i _ => one_div_pos.2 (hVh i)) Finset.univ_nonempty
  have hTl : 0 < ivTotalWeight Vl := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact Finset.sum_pos (fun i _ => one_div_pos.2 (hVl i)) Finset.univ_nonempty
  have hQ : ∀ d b₀, biasModelCriterion yh Vh yl Vl d b₀ =
      ∑ i, (yh i - ivPooled yh Vh) ^ 2 / Vh i + ivTotalWeight Vh * (ivPooled yh Vh - d) ^ 2 +
      (∑ i, (yl i - ivPooled yl Vl) ^ 2 / Vl i +
        ivTotalWeight Vl * (ivPooled yl Vl - (d + b₀)) ^ 2) := by
    intro d b₀
    rw [biasModelCriterion, sum_sq_div_eq yh Vh hVh hm d, ← sum_sq_div_eq yl Vl hVl hn (d + b₀)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  rw [hQ, hQ]
  have h1 : 0 ≤ ivTotalWeight Vh * (ivPooled yh Vh - d) ^ 2 := by positivity
  have h2 : 0 ≤ ivTotalWeight Vl * (ivPooled yl Vl - (d + b₀)) ^ 2 := by positivity
  simp only [sub_self, add_sub_cancel, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero]
  refine ⟨by linarith, fun h => ?_⟩
  have e1 : ivTotalWeight Vh * (ivPooled yh Vh - d) ^ 2 = 0 := by linarith
  have e2 : ivTotalWeight Vl * (ivPooled yl Vl - (d + b₀)) ^ 2 = 0 := by linarith
  rw [mul_eq_zero, or_iff_right hTh.ne', sq_eq_zero_iff, sub_eq_zero] at e1
  rw [mul_eq_zero, or_iff_right hTl.ne', sq_eq_zero_iff, sub_eq_zero] at e2
  exact ⟨e1.symm, by linarith⟩

/-- **Lower-quality trials alone do not identify the effect.** With no high-quality trial
(`m = 0`) the criterion depends on `(d, b₀)` only through `d + b₀`: it is invariant under
`(d, b₀) ↦ (d + t, b₀ - t)` for every `t`, so every effect `d` attains the minimum value
together with a suitable mean bias. The same invariance for the joint normal law of the
estimates is `lowQualityLaw_shift`. -/
theorem biasModelCriterion_shift_of_no_high {n : ℕ} (yh Vh : Fin 0 → ℝ) (yl Vl : Fin n → ℝ)
    (d b₀ t : ℝ) :
    biasModelCriterion yh Vh yl Vl (d + t) (b₀ - t) = biasModelCriterion yh Vh yl Vl d b₀ := by
  simp only [biasModelCriterion, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  exact Finset.sum_congr rfl fun i _ => by ring_nf

/-- The joint law of `n` independent lower-quality estimates in the bias model with a free mean
bias: `yᵢ ~ N(d + b₀, Vᵢ)`, the product of the normal laws. Here `Vᵢ` is the total variance of
the `i`-th estimate (its sampling variance, plus the between-study bias variance `κ²` when the
study-specific bias is random as in `adjusted_hasLaw`). -/
noncomputable def lowQualityLaw {n : ℕ} (d b₀ : ℝ) (V : Fin n → ℝ≥0) : Measure (Fin n → ℝ) :=
  Measure.pi fun i => gaussianReal (d + b₀) (V i)

omit [IsProbabilityMeasure P] in
/-- Independent estimates `Yᵢ ~ N(d + b₀, Vᵢ)` have joint law `lowQualityLaw d b₀ V`. -/
theorem hasLaw_lowQualityLaw {n : ℕ} {Y : Fin n → Ω → ℝ} {d b₀ : ℝ} {V : Fin n → ℝ≥0}
    (hind : iIndepFun Y P) (hY : ∀ i, HasLaw (Y i) (gaussianReal (d + b₀) (V i)) P) :
    HasLaw (fun ω i => Y i ω) (lowQualityLaw d b₀ V) P where
  aemeasurable := AEMeasurable.of_eval fun i => (hY i).aemeasurable
  map_eq := by
    rw [hind.map_fun_eq_pi_map fun i => (hY i).aemeasurable, lowQualityLaw]
    congr 1
    funext i
    exact (hY i).map_eq

/-- **Lower-quality estimates alone do not identify the effect: the observed law.** The joint law
of independent lower-quality estimates is the same under `(d, b₀)` and `(d + t, b₀ - t)` for
every `t`: it depends on the parameters only through `d + b₀`. -/
theorem lowQualityLaw_shift {n : ℕ} (d b₀ t : ℝ) (V : Fin n → ℝ≥0) :
    lowQualityLaw (d + t) (b₀ - t) V = lowQualityLaw d b₀ V := by
  unfold lowQualityLaw
  congr 1
  funext i
  congr 1
  ring

omit [IsProbabilityMeasure P] in
/-- **Non-identification, stated for a data vector.** If the observed estimates `Y` have the
law of the model with parameters `(d, b₀)`, they also have the law of the model with
`(d + t, b₀ - t)`; for `t ≠ 0` the two effects differ. So no functional of the law of `Y`
recovers `d`. -/
theorem lowQuality_not_identified {n : ℕ} {Y : Ω → Fin n → ℝ} {d b₀ : ℝ} {V : Fin n → ℝ≥0}
    (hY : HasLaw Y (lowQualityLaw d b₀ V) P) {t : ℝ} (ht : t ≠ 0) :
    HasLaw Y (lowQualityLaw (d + t) (b₀ - t) V) P ∧ d + t ≠ d := by
  refine ⟨by rwa [lowQualityLaw_shift], fun h => ht (by linarith)⟩

/-- **Countermodel: ignoring the bias.** With one high-quality estimate `0` and one
lower-quality estimate `1`, both of variance `1`, the free-bias model estimates `d̂ = 0`
(`biasModelCriterion_min`), while setting the bias to `0` makes the least squares estimate
`1/2`: then the lower-quality trial moves the estimate of the effect. -/
theorem biasModelCriterion_fixed_bias_example (d : ℝ) :
    biasModelCriterion ![0] ![1] ![1] ![1] (1 / 2) 0 ≤ biasModelCriterion ![0] ![1] ![1] ![1] d 0 ∧
      biasModelCriterion ![0] ![1] ![1] ![1] (1 / 2) 0 <
        biasModelCriterion ![0] ![1] ![1] ![1] 0 0 ∧
      ivPooled ![(0 : ℝ)] ![1] = 0 := by
  simp only [biasModelCriterion, ivPooled, ivTotalWeight, Fin.sum_univ_one, Matrix.cons_val_zero]
  refine ⟨by nlinarith [sq_nonneg (d - 1 / 2)], by norm_num, by norm_num⟩

/-! ### Small-study bias: the intercept of a regression on the variance -/

/-- The weighted mean `∑ wᵢ zᵢ / ∑ wᵢ`. -/
noncomputable def wMean {k : ℕ} (w z : Fin k → ℝ) : ℝ := (∑ i, w i * z i) / ∑ i, w i

/-- The weighted sum of squares `∑ wᵢ (xᵢ - x̄_w)²` of the regressor. -/
noncomputable def wSxx {k : ℕ} (w x : Fin k → ℝ) : ℝ := ∑ i, w i * (x i - wMean w x) ^ 2

/-- The weighted least squares slope of `y` on `x`. -/
noncomputable def wlsSlope {k : ℕ} (w x y : Fin k → ℝ) : ℝ :=
  (∑ i, w i * (x i - wMean w x) * (y i - wMean w y)) / wSxx w x

/-- The weighted least squares intercept `ȳ_w - slope x̄_w`. -/
noncomputable def wlsIntercept {k : ℕ} (w x y : Fin k → ℝ) : ℝ :=
  wMean w y - wlsSlope w x y * wMean w x

/-- The intercept is the linear combination `∑ᵢ aᵢ yᵢ` of the outcomes with coefficients
`aᵢ = wᵢ / ∑ w - x̄_w wᵢ (xᵢ - x̄_w) / Sxx`. -/
theorem wlsIntercept_eq_sum {k : ℕ} (w x y : Fin k → ℝ) (h : ∑ j, w j ≠ 0) :
    wlsIntercept w x y = ∑ i, (w i / ∑ j, w j -
      wMean w x * (w i * (x i - wMean w x)) / wSxx w x) * y i := by
  have h1 : ∑ i, w i * (x i - wMean w x) * (y i - wMean w y) =
      ∑ i, w i * (x i - wMean w x) * y i := by
    have h0 : ∑ i, w i * (x i - wMean w x) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, wMean]
      field_simp; ring
    have : ∑ i, w i * (x i - wMean w x) * (y i - wMean w y) =
        ∑ i, w i * (x i - wMean w x) * y i -
          (∑ i, w i * (x i - wMean w x)) * wMean w y := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h0, zero_mul, sub_zero]
  have h2 : ∑ i, (w i / ∑ j, w j) * y i = (∑ i, w i * y i) / ∑ j, w j := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ i, wMean w x * (w i * (x i - wMean w x)) / wSxx w x * y i =
      (∑ i, w i * (x i - wMean w x) * y i) / wSxx w x * wMean w x := by
    rw [Finset.sum_div, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [h2, h3, wlsIntercept, wlsSlope, h1, wMean]

/-- **The intercept reproduces lines.** If `yᵢ = d + γ xᵢ` exactly, with positive total weight
and `Sxx ≠ 0` (for nonnegative weights: the regressor is not constant on their support), the
intercept formula is `d` and the slope is `γ`. -/
theorem wlsIntercept_line {k : ℕ} {w x : Fin k → ℝ} (hw : 0 < ∑ i, w i) (hS : wSxx w x ≠ 0)
    (d γ : ℝ) : wlsSlope w x (fun i => d + γ * x i) = γ ∧
      wlsIntercept w x (fun i => d + γ * x i) = d := by
  have hm : wMean w (fun i => d + γ * x i) = d + γ * wMean w x := by
    simp only [wMean, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    field_simp
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hs : wlsSlope w x (fun i => d + γ * x i) = γ := by
    rw [wlsSlope, hm, div_eq_iff hS, wSxx, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  exact ⟨hs, by rw [wlsIntercept, hs, hm]; ring⟩

/-- The weighted least squares objective `∑ᵢ wᵢ (yᵢ - a - b xᵢ)²` of a line `a + b x`. -/
noncomputable def wlsRSS {k : ℕ} (w x y : Fin k → ℝ) (a b : ℝ) : ℝ :=
  ∑ i, w i * (y i - a - b * x i) ^ 2

/-- **The weighted least squares decomposition.** With positive total weight and `Sxx ≠ 0`, the
objective at `(a, b)` is its value at the formula `(wlsIntercept, wlsSlope)` plus
`(∑ w) (ŷ_w(a, b))² + Sxx (b - b̂)²`, where `ŷ_w(a, b) = â - a + (b̂ - b) x̄_w` is the gap
between the two lines at the weighted mean regressor. -/
theorem wlsRSS_eq {k : ℕ} (w x y : Fin k → ℝ) (hw : ∑ i, w i ≠ 0) (hS : wSxx w x ≠ 0)
    (a b : ℝ) :
    wlsRSS w x y a b = wlsRSS w x y (wlsIntercept w x y) (wlsSlope w x y) +
      (∑ i, w i) * (wlsIntercept w x y - a + (wlsSlope w x y - b) * wMean w x) ^ 2 +
      wSxx w x * (wlsSlope w x y - b) ^ 2 := by
  set S0 := ∑ i, w i
  set Sx := ∑ i, w i * x i
  set Sy := ∑ i, w i * y i
  set Sxx := ∑ i, w i * x i ^ 2
  set Sxy := ∑ i, w i * x i * y i
  set Syy := ∑ i, w i * y i ^ 2
  have hR : ∀ a b, wlsRSS w x y a b =
      Syy - 2 * a * Sy - 2 * b * Sxy + a ^ 2 * S0 + 2 * a * b * Sx + b ^ 2 * Sxx := by
    intro a b
    simp only [wlsRSS, Syy, Sy, Sxy, S0, Sx, Sxx, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hmx : wMean w x = Sx / S0 := rfl
  have hmy : wMean w y = Sy / S0 := rfl
  have hSxx : wSxx w x = Sxx - Sx ^ 2 / S0 := by
    have : wSxx w x = Sxx - 2 * wMean w x * Sx + wMean w x ^ 2 * S0 := by
      simp only [wSxx, Sxx, Sx, S0, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hmx]; field_simp; ring
  have hSxy : ∑ i, w i * (x i - wMean w x) * (y i - wMean w y) = Sxy - Sx * Sy / S0 := by
    have : ∑ i, w i * (x i - wMean w x) * (y i - wMean w y) =
        Sxy - wMean w x * Sy - wMean w y * Sx + wMean w x * wMean w y * S0 := by
      simp only [Sxy, Sy, Sx, S0, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hmx, hmy]; field_simp; ring
  have hb : wlsSlope w x y = (Sxy - Sx * Sy / S0) / wSxx w x := by rw [wlsSlope, hSxy]
  have ha : wlsIntercept w x y = Sy / S0 - wlsSlope w x y * (Sx / S0) := by
    rw [wlsIntercept, hmx, hmy]
  have hD : S0 * Sxx - Sx ^ 2 ≠ 0 := by
    intro h; apply hS; rw [hSxx]; field_simp; linarith
  have hb' : wlsSlope w x y = (S0 * Sxy - Sx * Sy) / (S0 * Sxx - Sx ^ 2) := by
    rw [hb, hSxx]; field_simp
  have hSxx' : wSxx w x = (S0 * Sxx - Sx ^ 2) / S0 := by rw [hSxx]; field_simp
  rw [hR, hR, ha, hmx, hb', hSxx']
  field_simp
  ring

/-- **The formula minimizes the weighted least squares objective.** For weights with positive
total and positive weighted spread of the regressor (`0 < Sxx`), `(wlsIntercept, wlsSlope)`
minimizes `wlsRSS` and is its unique minimizer. For nonnegative weights `0 < Sxx` says that the
regressor is not constant on the support of the weights; the sign of the individual weights is
not used. With `Sxx < 0` (possible only for signed weights) the objective is unbounded below
(`wlsRSS_signed_example`), and the formula then has no least squares reading. -/
theorem wlsRSS_le {k : ℕ} {w x : Fin k → ℝ} (y : Fin k → ℝ)
    (hw : 0 < ∑ i, w i) (hS : 0 < wSxx w x) (a b : ℝ) :
    wlsRSS w x y (wlsIntercept w x y) (wlsSlope w x y) ≤ wlsRSS w x y a b ∧
      (wlsRSS w x y a b = wlsRSS w x y (wlsIntercept w x y) (wlsSlope w x y) →
        a = wlsIntercept w x y ∧ b = wlsSlope w x y) := by
  rw [wlsRSS_eq w x y hw.ne' hS.ne' a b]
  have h1 : 0 ≤ (∑ i, w i) * (wlsIntercept w x y - a + (wlsSlope w x y - b) * wMean w x) ^ 2 :=
    mul_nonneg hw.le (sq_nonneg _)
  have h2 : 0 ≤ wSxx w x * (wlsSlope w x y - b) ^ 2 := mul_nonneg hS.le (sq_nonneg _)
  refine ⟨by linarith, fun h => ?_⟩
  have e2 : wSxx w x * (wlsSlope w x y - b) ^ 2 = 0 := by linarith
  have e1 : (∑ i, w i) * (wlsIntercept w x y - a + (wlsSlope w x y - b) * wMean w x) ^ 2 = 0 := by
    linarith
  rw [mul_eq_zero, or_iff_right hS.ne', sq_eq_zero_iff, sub_eq_zero] at e2
  rw [mul_eq_zero, or_iff_right hw.ne', sq_eq_zero_iff, e2, sub_self, zero_mul, add_zero,
    sub_eq_zero] at e1
  exact ⟨e1.symm, e2.symm⟩

/-- **Countermodel: signed weights.** With weights `(2, -1)`, study variances `(1, 2)` as the
regressor and outcomes `0`, the total weight is `1` and `wSxx = -2`, and the objective at
intercept `0` and slope `b` is `-2 b²`: it has no minimum, although `wlsIntercept_unbiased`
applies. -/
theorem wlsRSS_signed_example (b : ℝ) :
    ∑ i, ![(2 : ℝ), -1] i = 1 ∧ wSxx ![2, -1] ![1, 2] = -2 ∧
      wlsRSS ![2, -1] ![1, 2] ![0, 0] 0 b = -2 * b ^ 2 := by
  simp only [wSxx, wMean, wlsRSS, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  refine ⟨by norm_num, by norm_num, by ring⟩

omit [IsProbabilityMeasure P] in
/-- **The small-study intercept is unbiased** (TSD 3, Section 5.3: the true treatment effect
"is taken to be the intercept in a regression of the treatment effect against the study
variance", following Moreno and colleagues). Let the study estimates `Yᵢ` be integrable with
`E Yᵢ = d + γ Vᵢ` (a bias linear in the known study variance `Vᵢ`, the effect of a study of
infinite size being `d`), and take weights `w` with positive total and `Sxx ≠ 0`. Then the
intercept formula `wlsIntercept` applied to `Y` and `V` is unbiased for `d`. This is a statement
about the formula, valid for signed weights. It is the weighted least squares intercept, the
unique minimizer of `wlsRSS`, when moreover `0 < Sxx` (`wlsRSS_le`), for instance for
nonnegative weights and study variances not all equal on the support of the weights; with
`Sxx < 0` the objective has no minimum (`wlsRSS_signed_example`). -/
theorem wlsIntercept_unbiased {k : ℕ} {w Vs : Fin k → ℝ} (hw : 0 < ∑ i, w i)
    (hS : wSxx w Vs ≠ 0) {Y : Fin k → Ω → ℝ} (hY : ∀ i, Integrable (Y i) P) (d γ : ℝ)
    (hmean : ∀ i, P[Y i] = d + γ * Vs i) :
    P[fun ω => wlsIntercept w Vs (fun i => Y i ω)] = d := by
  simp_rw [wlsIntercept_eq_sum _ _ _ hw.ne']
  rw [integral_finsetSum _ fun i _ => (hY i).const_mul _]
  simp only [integral_const_mul, hmean]
  rw [← wlsIntercept_eq_sum _ _ _ hw.ne', (wlsIntercept_line hw hS d γ).2]

omit [IsProbabilityMeasure P] in
/-- **The naive pooled estimate carries the small-study bias.** Under the hypotheses of
`wlsIntercept_unbiased` without the condition on `Sxx`, the weighted mean of the estimates has
expectation `d + γ V̄_w`: biased by `γ` times the weighted mean variance, which is positive
for positive variances and weights. -/
theorem wMean_biased {k : ℕ} {w Vs : Fin k → ℝ} (hw : 0 < ∑ i, w i) {Y : Fin k → Ω → ℝ}
    (hY : ∀ i, Integrable (Y i) P) (d γ : ℝ) (hmean : ∀ i, P[Y i] = d + γ * Vs i) :
    P[fun ω => wMean w (fun i => Y i ω)] = d + γ * wMean w Vs := by
  simp only [wMean]
  rw [integral_div, integral_finsetSum _ fun i _ => (hY i).const_mul _]
  simp only [integral_const_mul, hmean, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  field_simp
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Countermodel: equal study variances.** If every study has the same variance `v` (and the
weights have positive total), the hypothesis `Sxx ≠ 0` of `wlsIntercept_unbiased` fails, and the
effect is not identified: the effect `d` with bias slope `γ` and the effect `d + γ v` without
small-study bias give the same mean `d + γ v` in every study, yet for `γ ≠ 0` and `v ≠ 0` the
two effects differ. -/
theorem smallStudy_not_identified_of_const {k : ℕ} {w Vs : Fin k → ℝ} {v : ℝ}
    (hw : 0 < ∑ i, w i) (hv : ∀ i, Vs i = v) (d γ : ℝ) (hγ : γ ≠ 0) (hv0 : v ≠ 0) :
    wSxx w Vs = 0 ∧ (∀ i, d + γ * Vs i = (d + γ * v) + 0 * Vs i) ∧ d ≠ d + γ * v := by
  have hm : wMean w Vs = v := by
    simp only [wMean, hv, ← Finset.sum_mul]
    field_simp
  refine ⟨?_, fun i => by rw [hv]; ring, fun h => ?_⟩
  · simp [wSxx, hm, hv]
  · have : γ * v = 0 := by linarith
    rcases mul_eq_zero.1 this with h' | h'
    · exact hγ h'
    · exact hv0 h'

end CausalInference.BiasAnalysis.BiasedEstimates
