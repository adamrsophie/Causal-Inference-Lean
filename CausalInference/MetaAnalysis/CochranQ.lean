/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.CommonEffect

/-!
# Meta-analysis: Cochran's `Q` and its expectation

**Cochran's `Q`** is the weighted sum of squared deviations of the study estimates from the pooled
estimate, `Q = ∑ wᵢ (Yᵢ - θ̂)²` with `wᵢ = 1 / vᵢ` (`cochranQ`). It is the minimum over `θ` of
`∑ wᵢ (Yᵢ - θ)²` (`cochranQ_le`), with the decomposition
`∑ wᵢ (Yᵢ - θ)² = Q + (∑ wᵢ) (θ̂ - θ)²` (`cochranQ_eq_sub`); it is nonnegative and vanishes
exactly when all the estimates agree (`cochranQ_nonneg`, `cochranQ_eq_zero_iff`), and it is
invariant under a common shift of the estimates (`cochranQ_add_const`).

**Expectation.** Only means, variances and uncorrelatedness enter. If the estimates are square
integrable, pairwise uncorrelated, with common mean `θ` and variances `σᵢ`, then `Q` is
integrable and `E[Q] = ∑ wᵢ σᵢ - ∑ wᵢ² σᵢ / ∑ wᵢ` (`integral_cochranQ`). Two cases:

* under the common effect model, `σᵢ = vᵢ` and `E[Q] = k - 1` (`integral_cochranQ_of_variance`);
* with a between study variance `τ²`, `σᵢ = vᵢ + τ²` and `E[Q] = (k - 1) + τ² c` with
  `c = ∑ wᵢ - ∑ wᵢ² / ∑ wᵢ` (`cochranQSlope`, `integral_cochranQ_of_variance_add`; in the
  components form `Yᵢ = θ + bᵢ + εᵢ`, `integral_cochranQ_of_components`), and `c > 0`
  for two or more studies (`cochranQSlope_pos`). This is the identity that the moment estimator
  of `τ²` inverts.

## Main definitions

* `cochranQ`, `cochranQSlope`.

## Main results

* `cochranQ_eq_sub`, `cochranQ_le`, `cochranQ_nonneg`, `cochranQ_eq_zero_iff`,
  `cochranQ_add_const`, `cochranQSlope_pos`.
* `integral_cochranQ`, `integral_cochranQ_of_variance`, `integral_cochranQ_of_variance_add`,
  `integral_cochranQ_of_components`,
  `IsCommonEffectModel.integral_cochranQ`.

## References

* W. G. Cochran, *The combination of estimates from different experiments*, Biometrics 10
  (1954).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset

/-! ### Definition and algebra -/

section Algebra

variable {ι : Type*} [Fintype ι] {v : ι → ℝ}

/-- **Cochran's `Q`**: `Q = ∑ wᵢ (yᵢ - θ̂)²`, with the inverse variance weights `wᵢ = 1 / vᵢ` and
the pooled estimate `θ̂` (Cochran 1954). -/
noncomputable def cochranQ (v y : ι → ℝ) : ℝ :=
  ∑ i, ivWeight v i * (y i - ivwEstimate v y) ^ 2

/-- The **slope** `c = ∑ wᵢ - ∑ wᵢ² / ∑ wᵢ` of the expectation of `Q` in the between study
variance: `E[Q] = (k - 1) + τ² c` (`integral_cochranQ_of_variance_add`). -/
noncomputable def cochranQSlope (v : ι → ℝ) : ℝ :=
  ∑ i, ivWeight v i - (∑ i, ivWeight v i ^ 2) / ∑ i, ivWeight v i

/-- **The weighted sum of squares decomposition**: for every `θ`,
`Q = ∑ wᵢ (yᵢ - θ)² - (∑ wᵢ) (θ̂ - θ)²`. -/
theorem cochranQ_eq_sub [Nonempty ι] (hv : ∀ i, 0 < v i) (y : ι → ℝ) (θ : ℝ) :
    cochranQ v y = ∑ i, ivWeight v i * (y i - θ) ^ 2 -
      (∑ i, ivWeight v i) * (ivwEstimate v y - θ) ^ 2 := by
  have hsum := sum_ivWeight_mul_sub hv y θ
  have hexp : ∀ i, ivWeight v i * (y i - ivwEstimate v y) ^ 2 = ivWeight v i * (y i - θ) ^ 2 -
      2 * (ivwEstimate v y - θ) * (ivWeight v i * (y i - θ)) +
        (ivwEstimate v y - θ) ^ 2 * ivWeight v i := fun i => by ring
  rw [cochranQ]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
  ring

/-- **`Q` is the minimal weighted sum of squares**: `Q ≤ ∑ wᵢ (yᵢ - θ)²` for every `θ`, so the
pooled estimate is the weighted least squares estimate. -/
theorem cochranQ_le [Nonempty ι] (hv : ∀ i, 0 < v i) (y : ι → ℝ) (θ : ℝ) :
    cochranQ v y ≤ ∑ i, ivWeight v i * (y i - θ) ^ 2 := by
  rw [cochranQ_eq_sub hv y θ, sub_le_self_iff]
  exact mul_nonneg (sum_ivWeight_pos hv).le (sq_nonneg _)

/-- `Q ≥ 0` for positive variances. -/
theorem cochranQ_nonneg (hv : ∀ i, 0 < v i) (y : ι → ℝ) : 0 ≤ cochranQ v y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ivWeight_pos hv i).le (sq_nonneg _)

/-- **`Q` vanishes exactly when all the estimates agree** (positive variances). -/
theorem cochranQ_eq_zero_iff (hv : ∀ i, 0 < v i) (y : ι → ℝ) :
    cochranQ v y = 0 ↔ ∀ i j, y i = y j := by
  rw [cochranQ, Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    mul_nonneg (ivWeight_pos hv i).le (sq_nonneg _)]
  have hterm : ∀ i, ivWeight v i * (y i - ivwEstimate v y) ^ 2 = 0 ↔
      y i = ivwEstimate v y := fun i => by
    rw [mul_eq_zero, or_iff_right (ivWeight_pos hv i).ne', pow_eq_zero_iff two_ne_zero,
      sub_eq_zero]
  simp only [Finset.mem_univ, forall_true_left, hterm]
  constructor
  · intro h i j
    rw [h i, h j]
  · intro h i
    have : Nonempty ι := ⟨i⟩
    have hc : (fun j => y j) = fun _ => y i := funext fun j => (h i j).symm
    rw [show ivwEstimate v y = ivwEstimate v (fun _ => y i) from congrArg _ hc,
      ivwEstimate_const hv]

/-- **`Q` is invariant under a common shift** of the estimates. -/
theorem cochranQ_add_const [Nonempty ι] (hv : ∀ i, 0 < v i) (y : ι → ℝ) (a : ℝ) :
    cochranQ v (fun i => y i + a) = cochranQ v y := by
  simp only [cochranQ, ivwEstimate_add_const hv]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `Q` is a measurable function of the data vector. -/
@[fun_prop]
theorem measurable_cochranQ (v : ι → ℝ) : Measurable fun y : ι → ℝ => cochranQ v y := by
  unfold cochranQ
  fun_prop

/-- **The slope is positive for two or more studies**: `∑ wᵢ - ∑ wᵢ² / ∑ wᵢ > 0`, since
`(∑ wᵢ)² - ∑ wᵢ² = ∑ᵢ wᵢ ∑_{j ≠ i} wⱼ`. -/
theorem cochranQSlope_pos (hv : ∀ i, 0 < v i) (hk : 1 < Fintype.card ι) :
    0 < cochranQSlope v := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hW := sum_ivWeight_pos hv
  have hrest : ∀ i, 0 < ∑ i, ivWeight v i - ivWeight v i := fun i => by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
    refine Finset.sum_pos (fun j _ => ivWeight_pos hv j) ?_
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
    omega
  have hkey : (∑ i, ivWeight v i) ^ 2 - ∑ i, ivWeight v i ^ 2 =
      ∑ i, ivWeight v i * (∑ j, ivWeight v j - ivWeight v i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sq]
  have hpos : 0 < (∑ i, ivWeight v i) ^ 2 - ∑ i, ivWeight v i ^ 2 := by
    rw [hkey]
    exact Finset.sum_pos (fun i _ => mul_pos (ivWeight_pos hv i) (hrest i))
      Finset.univ_nonempty
  rw [cochranQSlope, sub_pos, div_lt_iff₀ hW, ← sq]
  linarith

end Algebra

/-! ### The expectation of `Q` -/

section Expectation

variable {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {Y : ι → Ω → ℝ}
  {v : ι → ℝ} {θ : ℝ}

/-- **The expectation of Cochran's `Q`.** Let the estimates be square integrable and pairwise
uncorrelated, with common mean `θ` and variances `σᵢ`, and let the weights come from variances
`vᵢ > 0`. Then `Q` is integrable and `E[Q] = ∑ wᵢ σᵢ - ∑ wᵢ² σᵢ / ∑ wᵢ`. Proof: the weighted sum
of squares decomposition, `E[(Yᵢ - θ)²] = σᵢ` and `E[(θ̂ - θ)²] = Var θ̂ = ∑ (wᵢ / ∑ wⱼ)² σᵢ`. -/
theorem integral_cochranQ [Nonempty ι] [IsFiniteMeasure P] (hv : ∀ i, 0 < v i)
    (hY : ∀ i, MemLp (Y i) 2 P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ) {σ : ι → ℝ}
    (hvar : ∀ i, Var[Y i; P] = σ i) (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    Integrable (fun ω => cochranQ v fun i => Y i ω) P ∧
      ∫ ω, cochranQ v (fun i => Y i ω) ∂P =
        ∑ i, ivWeight v i * σ i - (∑ i, ivWeight v i ^ 2 * σ i) / ∑ i, ivWeight v i := by
  set W := ∑ i, ivWeight v i with hWdef
  have hW := sum_ivWeight_pos hv
  have hQ : ∀ ω, cochranQ v (fun i => Y i ω) = ∑ i, ivWeight v i * (Y i ω - θ) ^ 2 -
      W * (ivwEstimate v (fun i => Y i ω) - θ) ^ 2 := fun ω => cochranQ_eq_sub hv _ θ
  have hest : MemLp (fun ω => ivwEstimate v fun i => Y i ω) 2 P := by
    simp only [ivwEstimate_eq_sum]
    exact memLp_finsetSum _ fun i _ => (hY i).const_mul _
  have hint1 : ∀ i, Integrable (fun ω => ivWeight v i * (Y i ω - θ) ^ 2) P := fun i =>
    ((hY i).sub (memLp_const θ)).integrable_sq.const_mul _
  have hint2 : Integrable (fun ω => W * (ivwEstimate v (fun i => Y i ω) - θ) ^ 2) P :=
    (hest.sub (memLp_const θ)).integrable_sq.const_mul _
  have hE1 : ∀ i, ∫ ω, ivWeight v i * (Y i ω - θ) ^ 2 ∂P = ivWeight v i * σ i := fun i => by
    rw [integral_const_mul, ← hvar i, variance_eq_integral (hY i).aemeasurable, hmean i]
  have hmeanest : ∫ ω, ivwEstimate v (fun i => Y i ω) ∂P = θ :=
    integral_ivwEstimate hv (fun i => (hY i).integrable one_le_two) hmean
  have hE2 : ∫ ω, W * (ivwEstimate v (fun i => Y i ω) - θ) ^ 2 ∂P =
      (∑ i, ivWeight v i ^ 2 * σ i) / W := by
    rw [integral_const_mul, ← hmeanest, ← variance_eq_integral hest.aemeasurable]
    simp only [ivwEstimate_eq_sum]
    rw [variance_sum_mul_of_uncorrelated hY hunc]
    simp only [hvar, div_pow, ← hWdef]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  simp only [hQ]
  refine ⟨(integrable_finsetSum _ fun i _ => hint1 i).sub hint2, ?_⟩
  rw [integral_sub (integrable_finsetSum _ fun i _ => hint1 i) hint2,
    integral_finsetSum _ fun i _ => hint1 i, hE2]
  simp only [hE1]

/-- **`E[Q] = k - 1` under the common effect model** (Cochran 1954): for square integrable,
pairwise uncorrelated estimates with common mean `θ` and variances `vᵢ > 0`,
`E[Q] = k - 1`, `k` the number of studies. -/
theorem integral_cochranQ_of_variance [Nonempty ι] [IsFiniteMeasure P] (hv : ∀ i, 0 < v i)
    (hY : ∀ i, MemLp (Y i) 2 P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ)
    (hvar : ∀ i, Var[Y i; P] = v i) (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    ∫ ω, cochranQ v (fun i => Y i ω) ∂P = Fintype.card ι - 1 := by
  rw [(integral_cochranQ hv hY hmean hvar hunc).2]
  have h1 : ∀ i, ivWeight v i * v i = 1 := fun i => by rw [mul_comm, mul_ivWeight hv]
  have h2 : ∀ i, ivWeight v i ^ 2 * v i = ivWeight v i := fun i => by
    rw [sq, mul_assoc, h1, mul_one]
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [div_self (sum_ivWeight_pos hv).ne']

/-- **`E[Q]` under a between study variance.** For square integrable, pairwise uncorrelated
estimates with common mean `θ` and variances `vᵢ + τ²`, where the weights use the within-study
variances `vᵢ > 0`, `E[Q] = (k - 1) + τ² c` with `c = ∑ wᵢ - ∑ wᵢ² / ∑ wᵢ`. -/
theorem integral_cochranQ_of_variance_add [Nonempty ι] [IsFiniteMeasure P] (hv : ∀ i, 0 < v i)
    (hY : ∀ i, MemLp (Y i) 2 P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ) {τ2 : ℝ}
    (hvar : ∀ i, Var[Y i; P] = v i + τ2) (hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) :
    ∫ ω, cochranQ v (fun i => Y i ω) ∂P = (Fintype.card ι - 1) + τ2 * cochranQSlope v := by
  rw [(integral_cochranQ hv hY hmean hvar hunc).2, cochranQSlope]
  have hW := (sum_ivWeight_pos hv).ne'
  have h1 : ∀ i, ivWeight v i * (v i + τ2) = 1 + τ2 * ivWeight v i := fun i => by
    rw [mul_add, mul_comm (ivWeight v i) (v i), mul_ivWeight hv, mul_comm]
  have h2 : ∀ i, ivWeight v i ^ 2 * (v i + τ2) = ivWeight v i + τ2 * ivWeight v i ^ 2 :=
    fun i => by rw [sq, mul_assoc, h1]; ring
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum]
  field_simp
  ring

/-- **`E[Q]` in the components form** `Yᵢ = θ + bᵢ + εᵢ`: study effects `bᵢ` with mean `0` and
variance `τ²`, errors `εᵢ` with mean `0` and variance `vᵢ > 0`, all square integrable, the `bᵢ`
pairwise uncorrelated, the `εᵢ` pairwise uncorrelated, and every `bᵢ` uncorrelated with every
`εⱼ`. Then `Q` is integrable and `E[Q] = (k - 1) + τ² c`. -/
theorem integral_cochranQ_of_components [Nonempty ι] [IsProbabilityMeasure P]
    (hv : ∀ i, 0 < v i) {b ε : ι → Ω → ℝ} {τ2 : ℝ}
    (hb : ∀ i, MemLp (b i) 2 P) (hε : ∀ i, MemLp (ε i) 2 P)
    (hb0 : ∀ i, ∫ ω, b i ω ∂P = 0) (hε0 : ∀ i, ∫ ω, ε i ω ∂P = 0)
    (hbv : ∀ i, Var[b i; P] = τ2) (hεv : ∀ i, Var[ε i; P] = v i)
    (hbb : ∀ i j, i ≠ j → cov[b i, b j; P] = 0) (hεε : ∀ i j, i ≠ j → cov[ε i, ε j; P] = 0)
    (hbε : ∀ i j, cov[b i, ε j; P] = 0) :
    Integrable (fun ω => cochranQ v fun i => θ + b i ω + ε i ω) P ∧
      ∫ ω, cochranQ v (fun i => θ + b i ω + ε i ω) ∂P =
        (Fintype.card ι - 1) + τ2 * cochranQSlope v := by
  set Y : ι → Ω → ℝ := fun i ω => θ + b i ω + ε i ω with hYdef
  have hδ : ∀ i, MemLp (b i + ε i) 2 P := fun i => (hb i).add (hε i)
  have hYe : ∀ i, Y i = fun ω => θ + (b i + ε i) ω := fun i => by
    funext ω; simp only [hYdef, Pi.add_apply]; ring
  have hY : ∀ i, MemLp (Y i) 2 P := fun i => by
    rw [hYe i]; exact (memLp_const θ).add (hδ i)
  have hmean : ∀ i, ∫ ω, Y i ω ∂P = θ := fun i => by
    rw [hYe i, integral_add (integrable_const θ) ((hδ i).integrable one_le_two), Pi.add_def,
      integral_add ((hb i).integrable one_le_two) ((hε i).integrable one_le_two), hb0, hε0,
      integral_const, probReal_univ, one_smul, add_zero, add_zero]
  have hcovY : ∀ i j, cov[Y i, Y j; P] = cov[b i + ε i, b j + ε j; P] := fun i j => by
    rw [hYe i, hYe j, covariance_const_add_left ((hδ i).integrable one_le_two),
      covariance_const_add_right ((hδ j).integrable one_le_two)]
  have hcov : ∀ i j, cov[b i + ε i, b j + ε j; P] =
      cov[b i, b j; P] + cov[b i, ε j; P] + (cov[b j, ε i; P] + cov[ε i, ε j; P]) := by
    intro i j
    rw [covariance_add_left (hb i) (hε i) (hδ j), covariance_add_right (hb i) (hb j) (hε j),
      covariance_add_right (hε i) (hb j) (hε j), covariance_comm (ε i) (b j)]
  have hvar : ∀ i, Var[Y i; P] = v i + τ2 := fun i => by
    rw [← covariance_self (hY i).aemeasurable, hcovY, hcov, covariance_self (hb i).aemeasurable,
      covariance_self (hε i).aemeasurable, hbε, hbv, hεv]
    ring
  have hunc : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0 := fun i j hij => by
    rw [hcovY, hcov, hbb i j hij, hεε i j hij]
    simp only [hbε, add_zero]
  exact ⟨(integral_cochranQ hv hY hmean hvar hunc).1,
    integral_cochranQ_of_variance_add hv hY hmean hvar hunc⟩

/-- In the common effect model with at least one study, `Q` is integrable with `E[Q] = k - 1`. -/
theorem IsCommonEffectModel.integral_cochranQ [Nonempty ι]
    (h : IsCommonEffectModel P Y θ v) :
    Integrable (fun ω => cochranQ v fun i => Y i ω) P ∧
      ∫ ω, cochranQ v (fun i => Y i ω) ∂P = Fintype.card ι - 1 :=
  have := h.isProbabilityMeasure
  ⟨(MetaAnalysis.integral_cochranQ h.pos h.memLp h.integral_eq h.variance_eq
      fun _ _ => h.covariance_eq_zero).1,
    integral_cochranQ_of_variance h.pos h.memLp h.integral_eq h.variance_eq
      fun _ _ => h.covariance_eq_zero⟩

end Expectation

end MetaAnalysis

end CausalInference
