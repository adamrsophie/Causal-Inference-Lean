/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.PopulationAdjustment.EffectiveSampleSize
public import CausalInference.BiasAnalysis.VarianceCovariance
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Meta-analysis: the common effect model and inverse variance pooling

Studies indexed by a finite type `ι` report estimates `Yᵢ` of one effect `θ`, with known
within-study variances `vᵢ > 0`. Under the **common effect** (fixed effect) model the estimates
are independent with `E[Yᵢ] = θ` and `Var(Yᵢ) = vᵢ` (`IsCommonEffectModel`); in the Gaussian
model `Yᵢ ~ N(θ, vᵢ)` independently (`IsGaussianCommonEffectModel`).

The **inverse variance weights** are `wᵢ = 1 / vᵢ` (`ivWeight`) and the **pooled estimate** is
the weighted mean `θ̂ = ∑ wᵢ Yᵢ / ∑ wᵢ` (`ivwEstimate`, the library's `weightedMean` with these
weights). For the random effects model the same definition with the variances `vᵢ + τ²` gives
the random effects pooled estimate.

* **Unbiasedness** needs only the means: a linear estimator `∑ cᵢ Yᵢ` is unbiased for every `θ`
  exactly when `∑ cᵢ = 1` (`integral_sum_mul_eq_iff`), and `θ̂` is unbiased
  (`integral_ivwEstimate`).
* **Variance** needs pairwise uncorrelated square integrable estimates:
  `Var(∑ cᵢ Yᵢ) = ∑ cᵢ² vᵢ` (`variance_sum_mul_of_uncorrelated`) and `Var θ̂ = 1 / ∑ wᵢ`
  (`variance_ivwEstimate`).
* **Optimality** (best linear unbiased estimation): among weights summing to one,
  `∑ cᵢ² vᵢ = 1 / ∑ wᵢ + ∑ vᵢ (cᵢ - wᵢ / ∑ wⱼ)²` (`sum_sq_mul_eq_add`), so every linear unbiased
  estimator has variance at least `1 / ∑ wᵢ`, with equality exactly for the inverse variance
  weights (`variance_sum_mul_ge`, `variance_sum_mul_eq_iff`).

The identities agree with the deterministic pooling formulas `ivPooled`, `ivTotalWeight` and
`ivPooledVariance` of `BiasAnalysis.VarianceFormulas` on `Fin k` (`ivPooled_eq_ivwEstimate`,
`ivTotalWeight_eq_sum_ivWeight`, `ivPooledVariance_eq`); `sum_sq_mul_eq_add` is proved from
`firstOrderVariance_weights_eq` by reindexing.

## Main definitions

* `ivWeight`, `ivwEstimate`, `IsCommonEffectModel`, `IsGaussianCommonEffectModel`.

## Main results

* `integral_sum_mul`, `integral_sum_mul_eq_iff`, `integral_ivwEstimate`.
* `variance_sum_mul_of_uncorrelated`, `variance_ivwEstimate`.
* `sum_sq_mul_eq_add`, `variance_sum_mul_ge`, `variance_sum_mul_eq_iff`.
* `IsCommonEffectModel.memLp_ivwEstimate`, `IsCommonEffectModel.integral_variance_ivwEstimate`,
  `IsCommonEffectModel.variance_sum_mul`, `IsGaussianCommonEffectModel.isCommonEffectModel`.
* `isGaussianCommonEffectModel_pi`: the coordinates of `⊗ᵢ N(θ, vᵢ)` form a Gaussian common effect
  model, so every hypothesis of this file is met; `isGaussianCommonEffectModel_of_hasLaw` for any
  random vector with that law.

## References

* L. V. Hedges and I. Olkin, *Statistical Methods for Meta-Analysis*, Academic Press, 1985.
* M. Borenstein, L. V. Hedges, J. P. T. Higgins and H. R. Rothstein, *Introduction to
  Meta-Analysis*, Wiley, 2009.
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset PopulationAdjustment

/-! ### Inverse variance weights and the pooled estimate -/

section Weights

variable {ι : Type*} {v : ι → ℝ}

/-- The **inverse variance weight** `wᵢ = 1 / vᵢ` of a study with variance `vᵢ`. The results
assume `vᵢ > 0`. -/
noncomputable def ivWeight (v : ι → ℝ) (i : ι) : ℝ := 1 / v i

/-- The **inverse variance weighted pooled estimate** `θ̂ = ∑ wᵢ yᵢ / ∑ wᵢ` of the study
estimates `y` with variances `v`: the weighted mean with the weights `wᵢ = 1 / vᵢ`. -/
noncomputable def ivwEstimate [Fintype ι] (v y : ι → ℝ) : ℝ := weightedMean (ivWeight v) y

theorem ivWeight_pos (hv : ∀ i, 0 < v i) (i : ι) : 0 < ivWeight v i :=
  one_div_pos.2 (hv i)

/-- `vᵢ wᵢ = 1`. -/
theorem mul_ivWeight (hv : ∀ i, 0 < v i) (i : ι) : v i * ivWeight v i = 1 := by
  rw [ivWeight, mul_one_div_cancel (hv i).ne']

variable [Fintype ι]

/-- With at least one study, the total weight `∑ wᵢ` is positive. -/
theorem sum_ivWeight_pos [Nonempty ι] (hv : ∀ i, 0 < v i) : 0 < ∑ i, ivWeight v i :=
  Finset.sum_pos (fun i _ => ivWeight_pos hv i) Finset.univ_nonempty

/-- The pooled estimate is the linear combination with coefficients `wᵢ / ∑ⱼ wⱼ`. -/
theorem ivwEstimate_eq_sum (v y : ι → ℝ) :
    ivwEstimate v y = ∑ i, ivWeight v i / (∑ j, ivWeight v j) * y i := by
  rw [ivwEstimate, weightedMean_eq_sum_normalizedWeights]
  rfl

/-- The coefficients `wᵢ / ∑ⱼ wⱼ` of the pooled estimate sum to one. -/
theorem sum_ivWeight_div [Nonempty ι] (hv : ∀ i, 0 < v i) :
    ∑ i, ivWeight v i / (∑ j, ivWeight v j) = 1 := by
  rw [← Finset.sum_div, div_self (sum_ivWeight_pos hv).ne']

/-- `∑ wᵢ (yᵢ - θ) = (∑ wᵢ) (θ̂ - θ)` for every `θ`. -/
theorem sum_ivWeight_mul_sub [Nonempty ι] (hv : ∀ i, 0 < v i) (y : ι → ℝ) (θ : ℝ) :
    ∑ i, ivWeight v i * (y i - θ) = (∑ i, ivWeight v i) * (ivwEstimate v y - θ) := by
  rw [ivwEstimate, weightedMean, mul_sub, mul_div_cancel₀ _ (sum_ivWeight_pos hv).ne']
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]

/-- The pooled estimate of a shifted data vector is the shifted pooled estimate. -/
theorem ivwEstimate_add_const [Nonempty ι] (hv : ∀ i, 0 < v i) (y : ι → ℝ) (a : ℝ) :
    ivwEstimate v (fun i => y i + a) = ivwEstimate v y + a := by
  simp only [ivwEstimate_eq_sum, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_ivWeight_div hv, one_mul]

/-- The pooled estimate of a constant data vector is that constant. -/
theorem ivwEstimate_const [Nonempty ι] (hv : ∀ i, 0 < v i) (a : ℝ) :
    ivwEstimate v (fun _ => a) = a := by
  rw [ivwEstimate_eq_sum, ← Finset.sum_mul, sum_ivWeight_div hv, one_mul]

/-- The pooled estimate is a measurable function of the data vector. -/
@[fun_prop]
theorem measurable_ivwEstimate (v : ι → ℝ) : Measurable fun y : ι → ℝ => ivwEstimate v y := by
  simp only [ivwEstimate_eq_sum]
  fun_prop

end Weights

/-! ### The deterministic pooling formulas on `Fin k` -/

section Bridge

open BiasAnalysis.VarianceFormulas

variable {k : ℕ}

/-- The total inverse variance weight of `BiasAnalysis.VarianceFormulas` is `∑ wᵢ`. -/
theorem ivTotalWeight_eq_sum_ivWeight (V : Fin k → ℝ) : ivTotalWeight V = ∑ i, ivWeight V i :=
  rfl

/-- The pooled estimate `ivPooled` of `BiasAnalysis.VarianceFormulas` is `ivwEstimate`. -/
theorem ivPooled_eq_ivwEstimate (θ V : Fin k → ℝ) : ivPooled θ V = ivwEstimate V θ := by
  rw [ivPooled, ivwEstimate, weightedMean, ivTotalWeight_eq_sum_ivWeight]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [ivWeight]; ring

/-- The pooled variance `ivPooledVariance` of `BiasAnalysis.VarianceFormulas` is `1 / ∑ wᵢ`. -/
theorem ivPooledVariance_eq (V : Fin k → ℝ) : ivPooledVariance V = 1 / ∑ i, ivWeight V i :=
  rfl

end Bridge

/-! ### Optimality of the inverse variance weights: the algebra -/

section Algebra

variable {ι : Type*} [Fintype ι] {v : ι → ℝ}

/-- **The variance gap of a weighted average.** For positive variances and weights `cᵢ` summing
to one, `∑ cᵢ² vᵢ = 1 / ∑ wᵢ + ∑ vᵢ (cᵢ - wᵢ / ∑ wⱼ)²`. This is
`BiasAnalysis.VarianceFormulas.firstOrderVariance_weights_eq` transported along an enumeration
of `ι`. -/
theorem sum_sq_mul_eq_add (hv : ∀ i, 0 < v i) {c : ι → ℝ} (hc : ∑ i, c i = 1) :
    ∑ i, c i ^ 2 * v i = 1 / (∑ i, ivWeight v i) +
      ∑ i, v i * (c i - ivWeight v i / ∑ j, ivWeight v j) ^ 2 := by
  classical
  set e := Fintype.equivFin ι
  have hk : 0 < Fintype.card ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · simp at hc
    · exact Fintype.card_pos
  have hW : ∑ j : Fin (Fintype.card ι), 1 / v (e.symm j) = ∑ i, ivWeight v i :=
    e.symm.sum_comp (fun i => 1 / v i)
  have hc' : ∑ j : Fin (Fintype.card ι), c (e.symm j) = 1 := by
    rw [e.symm.sum_comp c, hc]
  have h := BiasAnalysis.VarianceFormulas.firstOrderVariance_weights_eq
    (V := fun j => v (e.symm j)) (fun j => hv _) hk hc'
  simp only [BiasAnalysis.VarianceFormulas.firstOrderVariance,
    BiasAnalysis.VarianceFormulas.ivPooledVariance,
    BiasAnalysis.VarianceFormulas.ivTotalWeight, hW] at h
  rw [e.symm.sum_comp (fun i => c i ^ 2 * v i)] at h
  rw [h, e.symm.sum_comp (fun i => v i * (c i - 1 / v i / ∑ j, ivWeight v j) ^ 2)]
  rfl

end Algebra

/-! ### Means and variances of linear estimators -/

section Moments

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ι → Ω → ℝ}
  {v : ι → ℝ} {θ : ℝ}

/-- **The mean of a linear estimator.** For integrable estimates with common mean `θ`,
`E[∑ cᵢ Yᵢ] = θ ∑ cᵢ`. -/
theorem integral_sum_mul (hY : ∀ i, Integrable (Y i) P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ)
    (c : ι → ℝ) : ∫ ω, ∑ i, c i * Y i ω ∂P = θ * ∑ i, c i := by
  rw [integral_finsetSum _ fun i _ => (hY i).const_mul _]
  simp only [integral_const_mul, hmean, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- **Unbiased linear estimators.** Let `P θ` be a law of the estimates under which they are
integrable with common mean `θ`, for every `θ`. A linear estimator `∑ cᵢ Yᵢ` is unbiased for
every `θ` exactly when `∑ cᵢ = 1`. -/
theorem integral_sum_mul_eq_iff {P : ℝ → Measure Ω} (hY : ∀ θ i, Integrable (Y i) (P θ))
    (hmean : ∀ θ i, ∫ ω, Y i ω ∂P θ = θ) (c : ι → ℝ) :
    (∀ θ, ∫ ω, ∑ i, c i * Y i ω ∂P θ = θ) ↔ ∑ i, c i = 1 := by
  simp only [integral_sum_mul (hY _) (hmean _)]
  exact ⟨fun h => by simpa using h 1, fun h θ => by rw [h, mul_one]⟩

/-- **The pooled estimate is unbiased**: for integrable estimates with common mean `θ` and
positive variances, `E[θ̂] = θ`. Only the means enter. -/
theorem integral_ivwEstimate [Nonempty ι] (hv : ∀ i, 0 < v i) (hY : ∀ i, Integrable (Y i) P)
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ) : ∫ ω, ivwEstimate v (fun i => Y i ω) ∂P = θ :=
  integral_weightedMean (sum_ivWeight_pos hv).ne' hY hmean

/-- **The variance of a linear combination of uncorrelated estimates**:
`Var(∑ cᵢ Yᵢ) = ∑ cᵢ² Var(Yᵢ)` for square integrable, pairwise uncorrelated `Yᵢ`. -/
theorem variance_sum_mul_of_uncorrelated [IsFiniteMeasure P] (hY : ∀ i, MemLp (Y i) 2 P)
    (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) (c : ι → ℝ) :
    Var[fun ω => ∑ i, c i * Y i ω; P] = ∑ i, c i ^ 2 * Var[Y i; P] := by
  classical
  rw [BiasAnalysis.VarianceCovariance.variance_linearization_cov Y hY c]
  simp only [BiasAnalysis.VarianceCovariance.quadraticVariance,
    BiasAnalysis.MeasurementError.covMatrix, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hji => by rw [hunc i j (Ne.symm hji), mul_zero])
    (by simp), covariance_self (hY i).aemeasurable]
  ring

/-- **The variance of the pooled estimate** (Hedges and Olkin 1985): for square integrable,
pairwise uncorrelated estimates with variances `vᵢ > 0`, `Var θ̂ = 1 / ∑ wᵢ`. -/
theorem variance_ivwEstimate [Nonempty ι] [IsFiniteMeasure P] (hv : ∀ i, 0 < v i)
    (hY : ∀ i, MemLp (Y i) 2 P) (hvar : ∀ i, Var[Y i; P] = v i)
    (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    Var[fun ω => ivwEstimate v (fun i => Y i ω); P] = 1 / ∑ i, ivWeight v i := by
  simp only [ivwEstimate_eq_sum]
  rw [variance_sum_mul_of_uncorrelated hY hunc]
  simp only [hvar]
  rw [sum_sq_mul_eq_add hv (sum_ivWeight_div hv)]
  simp

/-- **Inverse variance weighting is best linear unbiased** (Hedges and Olkin 1985). For square
integrable, pairwise uncorrelated estimates with variances `vᵢ > 0` and weights `cᵢ` summing to
one, `Var(∑ cᵢ Yᵢ) ≥ 1 / ∑ wᵢ = Var θ̂`. -/
theorem variance_sum_mul_ge [IsFiniteMeasure P] (hv : ∀ i, 0 < v i)
    (hY : ∀ i, MemLp (Y i) 2 P) (hvar : ∀ i, Var[Y i; P] = v i)
    (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) {c : ι → ℝ} (hc : ∑ i, c i = 1) :
    1 / ∑ i, ivWeight v i ≤ Var[fun ω => ∑ i, c i * Y i ω; P] := by
  rw [variance_sum_mul_of_uncorrelated hY hunc]
  simp only [hvar]
  rw [sum_sq_mul_eq_add hv hc, le_add_iff_nonneg_right]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hv i).le (sq_nonneg _)

/-- **The equality case**: under the hypotheses of `variance_sum_mul_ge`, a linear unbiased
estimator attains the variance `1 / ∑ wᵢ` exactly when its weights are the inverse variance
weights `wᵢ / ∑ⱼ wⱼ`. -/
theorem variance_sum_mul_eq_iff [IsFiniteMeasure P] (hv : ∀ i, 0 < v i)
    (hY : ∀ i, MemLp (Y i) 2 P) (hvar : ∀ i, Var[Y i; P] = v i)
    (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) {c : ι → ℝ} (hc : ∑ i, c i = 1) :
    Var[fun ω => ∑ i, c i * Y i ω; P] = 1 / ∑ i, ivWeight v i ↔
      c = fun i => ivWeight v i / ∑ j, ivWeight v j := by
  rw [variance_sum_mul_of_uncorrelated hY hunc]
  simp only [hvar]
  rw [sum_sq_mul_eq_add hv hc, add_eq_left,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hv i).le (sq_nonneg _)]
  constructor
  · intro h
    funext i
    have := h i (Finset.mem_univ i)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 (hv i).ne'
    · exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0)
  · rintro rfl i _
    simp

end Moments

/-! ### The common effect model -/

section Model

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ι → Ω → ℝ}
  {θ : ℝ} {v : ι → ℝ}

variable (P Y θ v) in
/-- The **common effect model**: the study estimates `Yᵢ` are independent and square integrable,
with common mean `θ` and known variances `vᵢ > 0`. -/
structure IsCommonEffectModel : Prop where
  /-- The estimates of different studies are independent. -/
  indep : iIndepFun Y P
  /-- Finite second moments. -/
  memLp : ∀ i, MemLp (Y i) 2 P
  /-- `E[Yᵢ] = θ`. -/
  integral_eq : ∀ i, ∫ ω, Y i ω ∂P = θ
  /-- `Var(Yᵢ) = vᵢ`. -/
  variance_eq : ∀ i, Var[Y i; P] = v i
  /-- The variances are positive. -/
  pos : ∀ i, 0 < v i

variable (P Y θ v) in
/-- The **Gaussian common effect model**: the study estimates are independent with
`Yᵢ ~ N(θ, vᵢ)` and `vᵢ > 0`. -/
structure IsGaussianCommonEffectModel : Prop where
  /-- The estimates of different studies are independent. -/
  indep : iIndepFun Y P
  /-- `Yᵢ ~ N(θ, vᵢ)`. -/
  hasLaw : ∀ i, HasLaw (Y i) (gaussianReal θ (v i).toNNReal) P
  /-- The variances are positive. -/
  pos : ∀ i, 0 < v i

namespace IsCommonEffectModel

theorem isProbabilityMeasure (h : IsCommonEffectModel P Y θ v) : IsProbabilityMeasure P :=
  h.indep.isProbabilityMeasure

/-- In the common effect model the estimates of different studies are uncorrelated. -/
theorem covariance_eq_zero (h : IsCommonEffectModel P Y θ v) {i j : ι} (hij : i ≠ j) :
    cov[Y i, Y j; P] = 0 :=
  have := h.isProbabilityMeasure
  (h.indep.indepFun hij).covariance_eq_zero (h.memLp i) (h.memLp j)

variable [Fintype ι]

/-- In the common effect model the pooled estimate is square integrable. -/
theorem memLp_ivwEstimate (h : IsCommonEffectModel P Y θ v) :
    MemLp (fun ω => ivwEstimate v fun i => Y i ω) 2 P := by
  simp only [ivwEstimate_eq_sum]
  exact memLp_finsetSum _ fun i _ => (h.memLp i).const_mul _

/-- In the common effect model with at least one study, `θ̂` is unbiased with variance
`1 / ∑ wᵢ`. -/
theorem integral_variance_ivwEstimate [Nonempty ι] (h : IsCommonEffectModel P Y θ v) :
    ∫ ω, ivwEstimate v (fun i => Y i ω) ∂P = θ ∧
      Var[fun ω => ivwEstimate v (fun i => Y i ω); P] = 1 / ∑ i, ivWeight v i :=
  have := h.isProbabilityMeasure
  ⟨integral_ivwEstimate h.pos (fun i => (h.memLp i).integrable one_le_two) h.integral_eq,
    variance_ivwEstimate h.pos h.memLp h.variance_eq fun _ _ => h.covariance_eq_zero⟩

/-- In the common effect model, every linear estimator with weights summing to one has variance
at least `1 / ∑ wᵢ`, with equality exactly for the inverse variance weights. -/
theorem variance_sum_mul (h : IsCommonEffectModel P Y θ v) {c : ι → ℝ} (hc : ∑ i, c i = 1) :
    1 / ∑ i, ivWeight v i ≤ Var[fun ω => ∑ i, c i * Y i ω; P] ∧
      (Var[fun ω => ∑ i, c i * Y i ω; P] = 1 / ∑ i, ivWeight v i ↔
        c = fun i => ivWeight v i / ∑ j, ivWeight v j) :=
  have := h.isProbabilityMeasure
  ⟨variance_sum_mul_ge h.pos h.memLp h.variance_eq (fun _ _ => h.covariance_eq_zero) hc,
    variance_sum_mul_eq_iff h.pos h.memLp h.variance_eq (fun _ _ => h.covariance_eq_zero) hc⟩

end IsCommonEffectModel

namespace IsGaussianCommonEffectModel

/-- The Gaussian common effect model is a common effect model. -/
theorem isCommonEffectModel (h : IsGaussianCommonEffectModel P Y θ v) :
    IsCommonEffectModel P Y θ v where
  indep := h.indep
  memLp i := (h.hasLaw i).memLp (memLp_id_gaussianReal 2)
  integral_eq i := by rw [(h.hasLaw i).integral_eq, integral_id_gaussianReal]
  variance_eq i := by
    rw [(h.hasLaw i).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ (h.pos i).le]
  pos := h.pos

variable [Fintype ι]

/-- In the Gaussian common effect model the data vector has law `⊗ᵢ N(θ, vᵢ)`. -/
theorem hasLaw_pi (h : IsGaussianCommonEffectModel P Y θ v) :
    HasLaw (fun ω i => Y i ω) (Measure.pi fun i => gaussianReal θ (v i).toNNReal) P :=
  h.indep.hasLaw_pi h.hasLaw

end IsGaussianCommonEffectModel

/-- A random vector with law `⊗ᵢ N(θ, vᵢ)`, `vᵢ > 0`, has coordinates forming a Gaussian common
effect model. -/
theorem isGaussianCommonEffectModel_of_hasLaw [Fintype ι] {X : Ω → ι → ℝ} (hv : ∀ i, 0 < v i)
    (hX : HasLaw X (Measure.pi fun i => gaussianReal θ (v i).toNNReal) P) :
    IsGaussianCommonEffectModel P (fun i ω => X ω i) θ v := by
  have := hX.isProbabilityMeasure
  have hi : ∀ i, HasLaw (fun ω => X ω i) (gaussianReal θ (v i).toNNReal) P := fun i =>
    (measurePreserving_eval (fun i => gaussianReal θ (v i).toNNReal) i).hasLaw.comp hX
  refine ⟨?_, hi, hv⟩
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (hi i).aemeasurable]
  simp only [(hi _).map_eq]
  exact hX.map_eq

/-- **A concrete Gaussian common effect model**: under `⊗ᵢ N(θ, vᵢ)` with `vᵢ > 0`, the
coordinates form a Gaussian common effect model, hence a common effect model. -/
theorem isGaussianCommonEffectModel_pi [Fintype ι] (hv : ∀ i, 0 < v i) (θ : ℝ) :
    IsGaussianCommonEffectModel (Measure.pi fun i => gaussianReal θ (v i).toNNReal)
      (fun i x => x i) θ v where
  indep := iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  hasLaw i := (measurePreserving_eval (fun i => gaussianReal θ (v i).toNNReal) i).hasLaw
  pos := hv

end Model

end MetaAnalysis

end CausalInference
