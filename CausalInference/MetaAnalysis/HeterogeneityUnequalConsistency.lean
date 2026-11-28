/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HeterogeneityUnequalLLN
public import CausalInference.MetaAnalysis.HeterogeneityUnequalBounds
public import CausalInference.Estimation.ConvergenceInProbability

/-!
# Meta-analysis: consistency of heterogeneity estimators with unequal within study variances

A sequence of independent studies reports estimates `Y₀, Y₁, …` with `E Yᵢ = θ` and
`Var(Yᵢ) = vᵢ + τ²`, where the known within study variances satisfy `a ≤ vᵢ ≤ A` for constants
`0 < a` (`IsUnequalVarianceStudies`). The estimators are computed from the first `k` studies,
indexed by `Fin k`, and `k → ∞`. This file proves, without any assumption of equal variances or
identical distributions:

* **The pooled common effect estimate is consistent** for `θ` under second moments only
  (`isConsistent_ivwEstimate_of_uncorrelated`): the studies need only be square integrable,
  pairwise uncorrelated, with mean `θ` and bounded variances, and the weights may come from any
  variances in `[a, A]`.
* **The DerSimonian and Laird moment estimators are consistent** for `τ²` when the fourth moments
  `E (Yᵢ - θ)⁴` are bounded uniformly in `i`: the untruncated estimator
  (`IsUnequalVarianceStudies.isConsistent_dlTau2Untruncated`, for every real `τ²`) and the
  truncated estimator (`IsUnequalVarianceStudies.isConsistent_dlTau2`, for `τ² ≥ 0`).
* **The DerSimonian and Laird pooled estimate is consistent** for `θ`
  (`IsUnequalVarianceStudies.isConsistent_dlEstimate`), although its weights `1 / (vᵢ + τ̂²)`
  depend on the data.

**Proof.** The weak law of large numbers for uncorrelated variables with bounded variances
(`tendstoInMeasure_avg_sub_integral`) applies to `wᵢ (Yᵢ - θ)` and to
`wᵢ ((Yᵢ - θ)² - (vᵢ + τ²))` for bounded deterministic weights
(`tendstoInMeasure_avg_mul_sub`, `tendstoInMeasure_avg_mul_sq_sub`). The deterministic bounds of
`MetaAnalysis.HeterogeneityUnequalBounds` then dominate each estimation error by a continuous
function of these averages and of `1 / k`, vanishing at `0`: the slope of `E[Q]` is at least
`k / A - 1 / a`, which is at least `k / (2A)` once `k ≥ 2A / a`; the truncation `max 0` is
`1`-Lipschitz; and the pooled estimate with the random weights `1 / (vᵢ + τ̂²)` is controlled
uniformly in the weight parameter through `|τ̂² - τ²|` (`abs_ivwEstimate_add_sub_le`).

The averages `k⁻¹ ∑ wᵢ` need not converge (for instance when the `vᵢ` alternate between two
values in blocks of growing length), so the proofs use bounds instead of limits of the pieces.

## Main definitions

* `IsUnequalVarianceStudies`.

## Main results

* `isConsistent_of_abs_sub_le`, `tendstoInMeasure_avg_mul_sub`,
  `tendstoInMeasure_avg_mul_sq_sub`, `isConsistent_ivwEstimate_of_uncorrelated`.
* `IsUnequalVarianceStudies.isConsistent_dlTau2Untruncated`,
  `IsUnequalVarianceStudies.isConsistent_dlTau2`,
  `IsUnequalVarianceStudies.isConsistent_dlEstimate`,
  `IsUnequalVarianceStudies.isConsistent_ivwEstimate`
* `isUnequalVarianceStudies_of_components`: the random effects form `Yᵢ = θ + bᵢ + εᵢ`.

## References

* R. DerSimonian and N. Laird, *Meta-analysis in clinical trials*, Controlled Clinical Trials 7
  (1986).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ### Tools -/

/-- **Consistency by domination**: if `G k → 0` in probability and eventually
`|f k ω - θ| ≤ G k ω` for every `ω`, then `f` is consistent for `θ`. -/
theorem isConsistent_of_abs_sub_le {f G : ℕ → Ω → ℝ} {θ : ℝ}
    (hG : TendstoInMeasure P G atTop (fun _ => 0))
    (hle : ∀ᶠ k in atTop, ∀ ω, |f k ω - θ| ≤ G k ω) : IsConsistent f θ P := by
  have h0 : TendstoInMeasure P (fun k ω => f k ω - θ) atTop 0 :=
    TendstoInMeasure.of_norm_le (f := G) hG (hle.mono fun k hk ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact (hk ω).trans (le_abs_self _))
  have h1 := h0.comp_continuousAt (c := (0 : ℝ)) (g := fun x => x + θ)
    (continuous_id.add continuous_const).continuousAt
  simpa [IsConsistent] using h1

/-- A consistent sequence has errors tending to `0` in probability. -/
theorem _root_.CausalInference.IsConsistent.tendstoInMeasure_sub {f : ℕ → Ω → ℝ} {θ : ℝ}
    (h : IsConsistent f θ P) :
    TendstoInMeasure P (fun k ω => f k ω - θ) atTop (fun _ => 0) := by
  have h1 := TendstoInMeasure.comp_continuousAt (μ := P) (X := f) (c := θ) h
    (g := fun x => x - θ) (continuous_id.sub continuous_const).continuousAt
  simpa using h1

/-- `(Y - θ)²` is square integrable and `(Y - θ)⁴` integrable when `Y` has a fourth moment. -/
theorem memLp_sq_sub_of_memLp_four [IsFiniteMeasure P] {X : Ω → ℝ} (hX : MemLp X 4 P)
    (θ : ℝ) : MemLp (fun ω => (X ω - θ) ^ 2) 2 P ∧ Integrable (fun ω => (X ω - θ) ^ 4) P := by
  have h1 : MemLp (fun ω => X ω - θ) ((4 : ℕ) : ℝ≥0∞) P := by
    rw [Nat.cast_ofNat]
    exact hX.sub (memLp_const θ)
  have h2 : Integrable (fun ω => (X ω - θ) ^ 4) P := by
    refine (h1.integrable_norm_pow (by norm_num)).congr (ae_of_all _ fun ω => ?_)
    simp only [Real.norm_eq_abs]
    exact Even.pow_abs ⟨2, rfl⟩ _
  have hm : AEStronglyMeasurable (fun ω => (X ω - θ) ^ 2) P := h1.aestronglyMeasurable.pow 2
  refine ⟨(memLp_two_iff_integrable_sq hm).2 ?_, h2⟩
  exact h2.congr (ae_of_all _ fun ω => by simp only; ring)

/-! ### Laws of large numbers for weighted deviations -/

/-- **Weighted law of large numbers for the deviations**: for square integrable, pairwise
uncorrelated `Yᵢ` with mean `θ` and `Var(Yᵢ) ≤ B`, and deterministic weights `|cᵢ| ≤ K`,
`k⁻¹ ∑_{i<k} cᵢ (Yᵢ - θ) → 0` in probability. -/
theorem tendstoInMeasure_avg_mul_sub [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    {θ B K : ℝ} (hY : ∀ i, MemLp (Y i) 2 P) (hcov : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0)
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ) (hvar : ∀ i, Var[Y i; P] ≤ B) (hc : ∀ i, |c i| ≤ K) :
    TendstoInMeasure P (fun (k : ℕ) ω => (k : ℝ)⁻¹ * ∑ i ∈ range k, c i * (Y i ω - θ))
      atTop (fun _ => 0) := by
  have hB : 0 ≤ B := (variance_nonneg _ _).trans (hvar 0)
  have hZ : ∀ i, MemLp (fun ω => c i * Y i ω) 2 P := fun i => (hY i).const_mul (c i)
  have hcovZ : ∀ i j, i ≠ j → cov[fun ω => c i * Y i ω, fun ω => c j * Y j ω; P] = 0 :=
    fun i j hij => by
      rw [covariance_const_mul_left, covariance_const_mul_right, hcov i j hij, mul_zero,
        mul_zero]
  have hvarZ : ∀ i, Var[fun ω => c i * Y i ω; P] ≤ K ^ 2 * B := fun i => by
    rw [variance_const_mul]
    have hc2 : c i ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
    exact mul_le_mul hc2 (hvar i) (variance_nonneg _ _) (sq_nonneg _)
  refine TendstoInMeasure.congr_left (fun k => ae_of_all _ fun ω => ?_)
    (tendstoInMeasure_avg_sub_integral hZ hcovZ hvarZ)
  simp only [integral_const_mul, hmean, mul_sub]

/-- **Weighted law of large numbers for the squared deviations**: for pairwise independent `Yᵢ`
with a fourth moment, mean `θ`, `Var(Yᵢ) = vᵢ + τ²` and `E (Yᵢ - θ)⁴ ≤ M`, and deterministic
weights `|cᵢ| ≤ K`, `k⁻¹ ∑_{i<k} cᵢ ((Yᵢ - θ)² - (vᵢ + τ²)) → 0` in probability. -/
theorem tendstoInMeasure_avg_mul_sq_sub [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    {c v : ℕ → ℝ} {θ τ2 K M : ℝ} (hind : Pairwise fun i j => IndepFun (Y i) (Y j) P)
    (hY : ∀ i, MemLp (Y i) 4 P) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ)
    (hvar : ∀ i, Var[Y i; P] = v i + τ2) (h4 : ∀ i, ∫ ω, (Y i ω - θ) ^ 4 ∂P ≤ M)
    (hc : ∀ i, |c i| ≤ K) :
    TendstoInMeasure P (fun (k : ℕ) ω => (k : ℝ)⁻¹ *
      ∑ i ∈ range k, c i * ((Y i ω - θ) ^ 2 - (v i + τ2))) atTop (fun _ => 0) := by
  have hZ : ∀ i, MemLp (fun ω => c i * (Y i ω - θ) ^ 2) 2 P := fun i =>
    (memLp_sq_sub_of_memLp_four (hY i) θ).1.const_mul (c i)
  have hcovZ : ∀ i j, i ≠ j →
      cov[fun ω => c i * (Y i ω - θ) ^ 2, fun ω => c j * (Y j ω - θ) ^ 2; P] = 0 :=
    fun i j hij => ((hind hij).comp (φ := fun x => c i * (x - θ) ^ 2)
      (ψ := fun x => c j * (x - θ) ^ 2) (by fun_prop) (by fun_prop)).covariance_eq_zero
        (hZ i) (hZ j)
  have hsq : ∀ i, ∫ ω, (c i * (Y i ω - θ) ^ 2) ^ 2 ∂P ≤ K ^ 2 * M := fun i => by
    have he : (fun ω => (c i * (Y i ω - θ) ^ 2) ^ 2) = fun ω => c i ^ 2 * (Y i ω - θ) ^ 4 :=
      funext fun ω => by ring
    rw [he, integral_const_mul]
    have hc2 : c i ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
    exact mul_le_mul hc2 (h4 i) (integral_nonneg fun ω => by positivity) (sq_nonneg _)
  refine TendstoInMeasure.congr_left (fun k => ae_of_all _ fun ω => ?_)
    (tendstoInMeasure_avg_sub_integral_of_integral_sq_le hZ hcovZ hsq)
  have hE : ∀ i, ∫ ω, c i * (Y i ω - θ) ^ 2 ∂P = c i * (v i + τ2) := fun i => by
    rw [integral_const_mul, ← hvar i, variance_eq_integral (hY i).aemeasurable, hmean i]
  simp only [hE, mul_sub]

/-! ### The pooled common effect estimate: second moments suffice -/

/-- `|θ̂ - θ| ≤ A |∑ wᵢ (yᵢ - θ)| / k` for weights from variances `0 < sᵢ ≤ A`. -/
theorem abs_ivwEstimate_sub_le {ι : Type*} [Fintype ι] [Nonempty ι] {s : ι → ℝ} {a A : ℝ}
    (ha : 0 < a) (hsa : ∀ i, a ≤ s i) (hsA : ∀ i, s i ≤ A) (y : ι → ℝ) (θ : ℝ) :
    |ivwEstimate s y - θ| ≤ A * |(Fintype.card ι : ℝ)⁻¹ * ∑ i, ivWeight s i * (y i - θ)| := by
  have hs : ∀ i, 0 < s i := fun i => ha.trans_le (hsa i)
  have hA : 0 < A := ha.trans_le ((hsa (Classical.arbitrary ι)).trans (hsA _))
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hW := sum_ivWeight_pos hs
  have hWk := card_div_le_sum_ivWeight ha hsa hsA
  rw [sum_ivWeight_mul_sub hs y θ, abs_mul, abs_mul, abs_of_pos hW,
    abs_of_pos (inv_pos.2 hk)]
  have e : A * ((Fintype.card ι : ℝ)⁻¹ * ((∑ i, ivWeight s i) * |ivwEstimate s y - θ|)) =
      (∑ i, ivWeight s i) / ((Fintype.card ι : ℝ) / A) * |ivwEstimate s y - θ| := by
    field_simp
  rw [e]
  have h1 : 1 ≤ (∑ i, ivWeight s i) / ((Fintype.card ι : ℝ) / A) :=
    (one_le_div (by positivity)).2 hWk
  nlinarith [abs_nonneg (ivwEstimate s y - θ)]

/-- **Consistency of the pooled common effect estimate with unequal variances, under second
moments**: let the estimates be square integrable and pairwise uncorrelated with mean `θ` and
`Var(Yᵢ) ≤ B`, and let the weights `1 / sᵢ` come from deterministic variances `a ≤ sᵢ ≤ A`,
`0 < a`. Then the pooled estimate from the first `k` studies is consistent for `θ`. With
`sᵢ = vᵢ` this is the common effect estimate; with `sᵢ = vᵢ + τ²` the random effects estimate
with the true `τ²`. No fourth moment and no independence beyond uncorrelatedness is needed. -/
theorem isConsistent_ivwEstimate_of_uncorrelated [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ}
    {s : ℕ → ℝ} {θ B a A : ℝ} (hY : ∀ i, MemLp (Y i) 2 P)
    (hcov : ∀ i j, i ≠ j → cov[Y i, Y j; P] = 0) (hmean : ∀ i, ∫ ω, Y i ω ∂P = θ)
    (hvar : ∀ i, Var[Y i; P] ≤ B) (ha : 0 < a) (hsa : ∀ i, a ≤ s i) (hsA : ∀ i, s i ≤ A) :
    IsConsistent (fun k ω => ivwEstimate (fun i : Fin k => s i) fun i => Y i ω) θ P := by
  have hw : ∀ i, |ivWeight s i| ≤ 1 / a := fun i => by
    rw [abs_of_pos (ivWeight_pos (fun j => ha.trans_le (hsa j)) i)]
    exact one_div_le_one_div_of_le ha (hsa i)
  have hL := tendstoInMeasure_avg_mul_sub hY hcov hmean hvar hw
  have hG := hL.comp_continuousAt (g := fun x => A * |x|) (by fun_prop)
  simp only [abs_zero, mul_zero] at hG
  refine isConsistent_of_abs_sub_le hG ?_
  filter_upwards [eventually_ge_atTop 1] with k hk ω
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := abs_ivwEstimate_sub_le (s := fun i : Fin k => s i) ha (fun i => hsa i)
    (fun i => hsA i) (fun i => Y i ω) θ
  rw [Fintype.card_fin] at h
  refine h.trans_eq ?_
  congr 3
  exact Fin.sum_univ_eq_sum_range (fun i => ivWeight s i * (Y i ω - θ)) k

/-! ### The model and the DerSimonian and Laird estimators -/

theorem dlTau2_errorBound_split_eq {k : ℝ} (hk : 0 < k) (A S N c : ℝ) :
    2 * A * (|S| / k + A * (N / k) ^ 2 + c / k) =
      2 * A * (|k⁻¹ * S| + A * (k⁻¹ * N) ^ 2) + 2 * A * (c / k) := by
  rw [abs_mul, abs_of_pos (inv_pos.2 hk)]
  ring

variable (P) in
/-- **Independent studies with unequal within study variances**: the estimates `Yᵢ` are pairwise
independent with a fourth moment, `E Yᵢ = θ`, `Var(Yᵢ) = vᵢ + τ²`, the known within study
variances satisfy `a ≤ vᵢ ≤ A` with `0 < a`, and the fourth central moments are bounded,
`E (Yᵢ - θ)⁴ ≤ M`. -/
structure IsUnequalVarianceStudies (Y : ℕ → Ω → ℝ) (θ τ2 : ℝ) (v : ℕ → ℝ) (a A M : ℝ) :
    Prop where
  /-- `P` is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure P
  /-- The studies are pairwise independent. -/
  indep : Pairwise fun i j => IndepFun (Y i) (Y j) P
  /-- Every estimate has a fourth moment. -/
  memLp_four : ∀ i, MemLp (Y i) 4 P
  /-- `E Yᵢ = θ`. -/
  integral_eq : ∀ i, ∫ ω, Y i ω ∂P = θ
  /-- `Var(Yᵢ) = vᵢ + τ²`. -/
  variance_eq : ∀ i, Var[Y i; P] = v i + τ2
  /-- The lower bound of the within study variances is positive. -/
  lower_pos : 0 < a
  /-- `a ≤ vᵢ`. -/
  lower_le : ∀ i, a ≤ v i
  /-- `vᵢ ≤ A`. -/
  le_upper : ∀ i, v i ≤ A
  /-- `E (Yᵢ - θ)⁴ ≤ M`. -/
  fourth_le : ∀ i, ∫ ω, (Y i ω - θ) ^ 4 ∂P ≤ M

namespace IsUnequalVarianceStudies

variable {Y : ℕ → Ω → ℝ} {θ τ2 : ℝ} {v : ℕ → ℝ} {a A M : ℝ}
  (h : IsUnequalVarianceStudies P Y θ τ2 v a A M)
include h

theorem memLp_two (i : ℕ) : MemLp (Y i) 2 P :=
  have := h.isProbabilityMeasure
  (h.memLp_four i).mono_exponent (by norm_num)

theorem covariance_eq_zero (i j : ℕ) (hij : i ≠ j) : cov[Y i, Y j; P] = 0 :=
  have := h.isProbabilityMeasure
  (h.indep hij).covariance_eq_zero (h.memLp_two i) (h.memLp_two j)

theorem upper_pos : 0 < A := h.lower_pos.trans_le ((h.lower_le 0).trans (h.le_upper 0))

/-- The law of large numbers for `k⁻¹ ∑ cᵢ (Yᵢ - θ)` with `|cᵢ| ≤ K`. -/
theorem tendstoInMeasure_avg_mul_sub' {c : ℕ → ℝ} {K : ℝ} (hc : ∀ i, |c i| ≤ K) :
    TendstoInMeasure P (fun (k : ℕ) ω => (k : ℝ)⁻¹ * ∑ i ∈ range k, c i * (Y i ω - θ))
      atTop (fun _ => 0) :=
  have := h.isProbabilityMeasure
  tendstoInMeasure_avg_mul_sub h.memLp_two h.covariance_eq_zero h.integral_eq
    (B := A + τ2) (fun i => (h.variance_eq i).le.trans (by linarith [h.le_upper i])) hc

/-- The law of large numbers for `k⁻¹ ∑ wᵢ ((Yᵢ - θ)² - (vᵢ + τ²))`. -/
theorem tendstoInMeasure_avg_sq :
    TendstoInMeasure P (fun (k : ℕ) ω => (k : ℝ)⁻¹ *
      ∑ i ∈ range k, ivWeight v i * ((Y i ω - θ) ^ 2 - (v i + τ2))) atTop (fun _ => 0) :=
  have := h.isProbabilityMeasure
  tendstoInMeasure_avg_mul_sq_sub h.indep h.memLp_four h.integral_eq h.variance_eq h.fourth_le
    (K := 1 / a) fun i => by
      rw [abs_of_pos (ivWeight_pos (fun j => h.lower_pos.trans_le (h.lower_le j)) i)]
      exact one_div_le_one_div_of_le h.lower_pos (h.lower_le i)

/-- **Consistency of the untruncated DerSimonian and Laird estimator with unequal variances**:
computed from the first `k` studies, `(Q - (k - 1)) / c` is consistent for `τ²`. -/
theorem isConsistent_dlTau2Untruncated :
    IsConsistent (fun k ω => dlTau2Untruncated (fun i : Fin k => v i) fun i => Y i ω) τ2 P := by
  have ha := h.lower_pos
  have hA := h.upper_pos
  have hw : ∀ i, |ivWeight v i| ≤ 1 / a := fun i => by
    rw [abs_of_pos (ivWeight_pos (fun j => ha.trans_le (h.lower_le j)) i)]
    exact one_div_le_one_div_of_le ha (h.lower_le i)
  have h1 := h.tendstoInMeasure_avg_sq
  have h2 := h.tendstoInMeasure_avg_mul_sub' hw
  have hF := (h1.prodMk h2).comp_continuousAt
    (g := fun p : ℝ × ℝ => 2 * A * (|p.1| + A * p.2 ^ 2)) (by fun_prop)
  have hd : TendstoInMeasure P (fun (k : ℕ) (_ : Ω) => 2 * A * ((1 + |τ2| / a) / k)) atTop
      (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_const ?_
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (1 + |τ2| / a)).const_mul (2 * A)
  have hG : TendstoInMeasure P (fun (k : ℕ) ω => 2 * A * (|(k : ℝ)⁻¹ *
      ∑ i ∈ range k, ivWeight v i * ((Y i ω - θ) ^ 2 - (v i + τ2))| +
        A * ((k : ℝ)⁻¹ * ∑ i ∈ range k, ivWeight v i * (Y i ω - θ)) ^ 2) +
          2 * A * ((1 + |τ2| / a) / k)) atTop (fun _ => 0) := by
    convert hF.add hd using 1
    funext ω
    simp
  refine isConsistent_of_abs_sub_le hG ?_
  obtain ⟨K0, hK0⟩ := exists_nat_ge (2 * A / a)
  filter_upwards [eventually_ge_atTop (max 1 K0)] with k hk ω
  have hk1 : 1 ≤ k := le_of_max_le_left hk
  have : Nonempty (Fin k) := ⟨⟨0, hk1⟩⟩
  have hkK : 2 * A / a ≤ (Fintype.card (Fin k) : ℝ) := by
    rw [Fintype.card_fin]
    exact hK0.trans (by exact_mod_cast le_of_max_le_right hk)
  have hb := abs_dlTau2Untruncated_sub_le (v := fun i : Fin k => v i) ha (fun i => h.lower_le i)
    (fun i => h.le_upper i) hkK (fun i => Y i ω) θ τ2
  rw [Fintype.card_fin] at hb
  have e1 : ∑ i : Fin k, ivWeight (fun i : Fin k => v i) i * ((Y i ω - θ) ^ 2 - (v i + τ2)) =
      ∑ i ∈ range k, ivWeight v i * ((Y i ω - θ) ^ 2 - (v i + τ2)) :=
    Fin.sum_univ_eq_sum_range (fun i => ivWeight v i * ((Y i ω - θ) ^ 2 - (v i + τ2))) k
  have e2 : ∑ i : Fin k, ivWeight (fun i : Fin k => v i) i * (Y i ω - θ) =
      ∑ i ∈ range k, ivWeight v i * (Y i ω - θ) :=
    Fin.sum_univ_eq_sum_range (fun i => ivWeight v i * (Y i ω - θ)) k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  rw [e1, e2] at hb
  exact hb.trans_eq (dlTau2_errorBound_split_eq hkpos _ _ _ _)

/-- **Consistency of the DerSimonian and Laird estimator with unequal variances**: for
`τ² ≥ 0`, the truncated estimator `max 0 ((Q - (k - 1)) / c)` from the first `k` studies is
consistent for `τ²`. -/
theorem isConsistent_dlTau2 (hτ : 0 ≤ τ2) :
    IsConsistent (fun k ω => dlTau2 (fun i : Fin k => v i) fun i => Y i ω) τ2 P := by
  refine isConsistent_of_abs_sub_le (G := fun k ω =>
    |dlTau2Untruncated (fun i : Fin k => v i) (fun i => Y i ω) - τ2|) ?_
    (Eventually.of_forall fun k ω => ?_)
  · have h0 := h.isConsistent_dlTau2Untruncated.tendstoInMeasure_sub.comp_continuousAt
      (g := fun x => |x|) continuous_abs.continuousAt
    simpa using h0
  · have := abs_max_sub_max_le_abs
      (dlTau2Untruncated (fun i : Fin k => v i) fun i => Y i ω) τ2 0
    rw [max_eq_left hτ, max_comm] at this
    exact this

/-- **Consistency of the DerSimonian and Laird pooled estimate with unequal variances**: for
`τ² ≥ 0`, the pooled estimate with the estimated weights `1 / (vᵢ + τ̂²_DL)` from the first `k`
studies is consistent for `θ`. The dependence of the weights on the data is handled by a bound
uniform in the weight parameter (`abs_ivwEstimate_add_sub_le`). -/
theorem isConsistent_dlEstimate (hτ : 0 ≤ τ2) :
    IsConsistent (fun k ω => dlEstimate (fun i : Fin k => v i) fun i => Y i ω) θ P := by
  have ha := h.lower_pos
  have hu : ∀ i, |ivWeight (fun i => v i + τ2) i| ≤ 1 / a := fun i => by
    rw [abs_of_pos (ivWeight_pos (v := fun i => v i + τ2)
      (fun j => by linarith [ha.trans_le (h.lower_le j)]) i)]
    exact one_div_le_one_div_of_le ha (by linarith [h.lower_le i])
  have hX := (h.isConsistent_dlTau2 hτ).tendstoInMeasure_sub
  have h1 := h.tendstoInMeasure_avg_sq
  have h3 := h.tendstoInMeasure_avg_mul_sub' hu
  have hF := ((hX.prodMk h1).prodMk h3).comp_continuousAt
    (g := fun p : (ℝ × ℝ) × ℝ => (A + τ2 + |p.1.1|) *
      (|p.2| + |p.1.1| / a ^ 2 * (1 + A * (|p.1.2| + 1 + τ2 / a)))) (by fun_prop)
  simp only [abs_zero, zero_div, zero_mul, add_zero, mul_zero] at hF
  refine isConsistent_of_abs_sub_le hF ?_
  filter_upwards [eventually_ge_atTop 1] with k hk ω
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hb := abs_ivwEstimate_add_sub_le (v := fun i : Fin k => v i) ha (fun i => h.lower_le i)
    (fun i => h.le_upper i) hτ
    (dlTau2_nonneg (fun i : Fin k => v i) (fun i => Y i ω)) (fun i => Y i ω) θ
  rw [Fintype.card_fin] at hb
  refine (show |dlEstimate (fun i : Fin k => v i) (fun i => Y i ω) - θ| ≤ _ from hb).trans_eq ?_
  have e1 : ∑ i : Fin k, ivWeight (fun i : Fin k => v i) i * ((Y i ω - θ) ^ 2 - (v i + τ2)) =
      ∑ i ∈ range k, ivWeight v i * ((Y i ω - θ) ^ 2 - (v i + τ2)) :=
    Fin.sum_univ_eq_sum_range (fun i => ivWeight v i * ((Y i ω - θ) ^ 2 - (v i + τ2))) k
  have e3 : ∑ i : Fin k, ivWeight (fun i : Fin k => v i + τ2) i * (Y i ω - θ) =
      ∑ i ∈ range k, ivWeight (fun i => v i + τ2) i * (Y i ω - θ) :=
    Fin.sum_univ_eq_sum_range (fun i => ivWeight (fun i => v i + τ2) i * (Y i ω - θ)) k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [e1, e3, abs_mul (k : ℝ)⁻¹, abs_mul (k : ℝ)⁻¹, abs_of_pos (inv_pos.2 hkpos)]
  simp only [div_eq_inv_mul]

/-- The pooled common effect estimate `ivwEstimate v` is consistent for `θ` in the model; only
the second moments are used (`isConsistent_ivwEstimate_of_uncorrelated`). -/
theorem isConsistent_ivwEstimate :
    IsConsistent (fun k ω => ivwEstimate (fun i : Fin k => v i) fun i => Y i ω) θ P :=
  have := h.isProbabilityMeasure
  isConsistent_ivwEstimate_of_uncorrelated h.memLp_two h.covariance_eq_zero h.integral_eq
    (B := A + τ2) (fun i => (h.variance_eq i).le.trans (by linarith [h.le_upper i]))
    h.lower_pos h.lower_le h.le_upper

end IsUnequalVarianceStudies


/-! ### The random effects form -/

/-- **The random effects model with unequal variances satisfies the hypotheses**: let the pairs
`(bᵢ, εᵢ)` of study effects and errors be pairwise independent across studies, with fourth
moments, `E bᵢ = E εᵢ = 0`, `Var(bᵢ) = τ²`, `Var(εᵢ) = vᵢ`, `cov(bᵢ, εᵢ) = 0`,
`a ≤ vᵢ ≤ A` with `0 < a`, and `E (bᵢ + εᵢ)⁴ ≤ M`. Then the estimates `Yᵢ = θ + bᵢ + εᵢ` form
a sequence of independent studies with unequal variances. The condition `cov(bᵢ, εᵢ) = 0`
within each study is what makes `Var(Yᵢ) = vᵢ + τ²`. -/
theorem isUnequalVarianceStudies_of_components [IsProbabilityMeasure P] {b ε : ℕ → Ω → ℝ}
    {v : ℕ → ℝ} {θ τ2 a A M : ℝ}
    (hind : Pairwise fun i j =>
      IndepFun (fun ω => (b i ω, ε i ω)) (fun ω => (b j ω, ε j ω)) P)
    (hb : ∀ i, MemLp (b i) 4 P) (hε : ∀ i, MemLp (ε i) 4 P)
    (hbm : ∀ i, ∫ ω, b i ω ∂P = 0) (hεm : ∀ i, ∫ ω, ε i ω ∂P = 0)
    (hbv : ∀ i, Var[b i; P] = τ2) (hεv : ∀ i, Var[ε i; P] = v i)
    (hbε : ∀ i, cov[b i, ε i; P] = 0) (ha : 0 < a) (hva : ∀ i, a ≤ v i) (hvA : ∀ i, v i ≤ A)
    (h4 : ∀ i, ∫ ω, (b i ω + ε i ω) ^ 4 ∂P ≤ M) :
    IsUnequalVarianceStudies P (fun i ω => θ + b i ω + ε i ω) θ τ2 v a A M where
  isProbabilityMeasure := inferInstance
  indep := fun i j hij => (hind hij).comp (φ := fun p : ℝ × ℝ => θ + p.1 + p.2)
    (ψ := fun p : ℝ × ℝ => θ + p.1 + p.2) (by fun_prop) (by fun_prop)
  memLp_four := fun i => ((memLp_const θ).add (hb i)).add (hε i)
  integral_eq := fun i => by
    have hb1 : Integrable (b i) P := (hb i).integrable (by norm_num)
    have hε1 : Integrable (ε i) P := (hε i).integrable (by norm_num)
    rw [integral_add (f := fun ω => θ + b i ω) ((integrable_const θ).add hb1) hε1,
      integral_add (integrable_const θ) hb1, hbm, hεm, integral_const, probReal_univ,
      smul_eq_mul, one_mul, add_zero, add_zero]
  variance_eq := fun i => by
    have hb2 : MemLp (b i) 2 P := (hb i).mono_exponent (by norm_num)
    have hε2 : MemLp (ε i) 2 P := (hε i).mono_exponent (by norm_num)
    have he : (fun ω => θ + b i ω + ε i ω) = fun ω => θ + (b i ω + ε i ω) :=
      funext fun ω => add_assoc _ _ _
    rw [he, variance_const_add (X := fun ω => b i ω + ε i ω)
      (hb2.aestronglyMeasurable.add hε2.aestronglyMeasurable),
      variance_fun_add hb2 hε2, hbε, hbv, hεv]
    ring
  lower_pos := ha
  lower_le := hva
  le_upper := hvA
  fourth_le := fun i => by
    simpa only [add_assoc, add_sub_cancel_left] using h4 i

end MetaAnalysis

end CausalInference
