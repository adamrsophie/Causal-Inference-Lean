/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Consistency
public import Mathlib.Probability.Moments.Variance

/-!
# A weak law of large numbers for uncorrelated variables with bounded variances

The laws of large numbers of `CausalInference.Estimation` are stated for i.i.d. samples. In a
meta-analysis with unequal within study variances the studies are independent but not
identically distributed. This file proves the weak law of large numbers by Chebyshev's
inequality: if `Z₀, Z₁, …` are square integrable, pairwise uncorrelated, with
`Var(Zᵢ) ≤ C` for all `i`, then

`k⁻¹ ∑_{i < k} (Zᵢ - E Zᵢ) → 0` in probability as `k → ∞`

(`tendstoInMeasure_avg_sub_integral`). Proof: `Var(∑_{i<k} Zᵢ) = ∑_{i<k} Var(Zᵢ) ≤ k C`, and
Chebyshev's inequality bounds `P(|k⁻¹ ∑ (Zᵢ - E Zᵢ)| ≥ ε)` by `C / (k ε²)`. Pairwise independent
square integrable variables are pairwise uncorrelated
(`tendstoInMeasure_avg_sub_integral_of_indepFun`).

The second moment form `E[Zᵢ²] ≤ C` implies the variance bound
(`tendstoInMeasure_avg_sub_integral_of_integral_sq_le`), and a deterministic sequence tending to
`0` tends to `0` in probability (`tendstoInMeasure_of_tendsto_const`).

## Main results

* `variance_sum_range_le`, `tendstoInMeasure_avg_sub_integral`,
  `tendstoInMeasure_avg_sub_integral_of_indepFun`,
  `tendstoInMeasure_avg_sub_integral_of_integral_sq_le`, `tendstoInMeasure_of_tendsto_const`.

## References

* The classical Chebyshev argument; the inequality is Mathlib's `meas_ge_le_variance_div_sq`.
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The variance of a sum of uncorrelated variables**: if `Z₀, …, Z_{k-1}` are square integrable
and pairwise uncorrelated with `Var(Zᵢ) ≤ C`, then `Var(∑_{i<k} Zᵢ) ≤ k C`. -/
theorem variance_sum_range_le [IsFiniteMeasure P] {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P)
    (hcov : ∀ i j, i ≠ j → cov[Z i, Z j; P] = 0) {C : ℝ} (hvar : ∀ i, Var[Z i; P] ≤ C)
    (k : ℕ) : Var[∑ i ∈ range k, Z i; P] ≤ k * C := by
  rw [variance_sum' fun i _ => hZ i]
  have hdiag : ∀ i ∈ range k, ∑ j ∈ range k, cov[Z i, Z j; P] = Var[Z i; P] := by
    intro i hi
    rw [Finset.sum_eq_single_of_mem i hi fun j _ hji => hcov i j (Ne.symm hji),
      covariance_self (hZ i).aemeasurable]
  rw [Finset.sum_congr rfl hdiag]
  calc ∑ i ∈ range k, Var[Z i; P] ≤ ∑ _i ∈ range k, C := Finset.sum_le_sum fun i _ => hvar i
    _ = k * C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Weak law of large numbers for uncorrelated variables with bounded variances** (Chebyshev):
if `Z₀, Z₁, …` are square integrable and pairwise uncorrelated under a probability measure, with
`Var(Zᵢ) ≤ C` for every `i`, then `k⁻¹ ∑_{i<k} (Zᵢ - E Zᵢ) → 0` in probability. -/
theorem tendstoInMeasure_avg_sub_integral [IsProbabilityMeasure P] {Z : ℕ → Ω → ℝ}
    (hZ : ∀ i, MemLp (Z i) 2 P) (hcov : ∀ i j, i ≠ j → cov[Z i, Z j; P] = 0) {C : ℝ}
    (hvar : ∀ i, Var[Z i; P] ≤ C) :
    TendstoInMeasure P (fun (k : ℕ) ω => (k : ℝ)⁻¹ * ∑ i ∈ range k, (Z i ω - ∫ ω', Z i ω' ∂P))
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hC : 0 ≤ C := (variance_nonneg _ _).trans (hvar 0)
  set T : ℕ → Ω → ℝ := fun k => ∑ i ∈ range k, Z i with hT
  have hTm : ∀ k, MemLp (T k) 2 P := fun k => memLp_finsetSum' _ fun i _ => hZ i
  have hET : ∀ k, ∫ ω, T k ω ∂P = ∑ i ∈ range k, ∫ ω, Z i ω ∂P := fun k => by
    simp only [hT, Finset.sum_apply]
    exact integral_finsetSum _ fun i _ => (hZ i).integrable one_le_two
  have hbound : ∀ k : ℕ, 0 < k → P {ω | ε ≤ dist ((k : ℝ)⁻¹ *
      ∑ i ∈ range k, (Z i ω - ∫ ω', Z i ω' ∂P)) 0} ≤ ENNReal.ofReal (C / (k * ε ^ 2)) := by
    intro k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hsub : {ω | ε ≤ dist ((k : ℝ)⁻¹ * ∑ i ∈ range k, (Z i ω - ∫ ω', Z i ω' ∂P)) 0} ⊆
        {ω | k * ε ≤ |T k ω - ∫ ω', T k ω' ∂P|} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] at hω ⊢
      rw [hET, hT]
      simp only [Finset.sum_apply]
      rw [← Finset.sum_sub_distrib]
      rw [abs_mul, abs_inv, abs_of_pos hk', inv_mul_eq_div, le_div_iff₀ hk'] at hω
      linarith
    refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq (hTm k)
      (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_))
    have hv := variance_sum_range_le hZ hcov hvar k
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc Var[T k; P] * (k * ε ^ 2) ≤ (k * C) * (k * ε ^ 2) :=
          mul_le_mul_of_nonneg_right hv (by positivity)
      _ = C * (k * ε) ^ 2 := by ring
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal (C / (k * ε ^ 2))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    have h1 : Tendsto (fun k : ℕ => (k : ℝ) * ε ^ 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    exact h1.const_div_atTop C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact hbound k hk

/-- **Weak law of large numbers for independent variables with bounded variances**: pairwise
independent, square integrable `Zᵢ` with `Var(Zᵢ) ≤ C` satisfy
`k⁻¹ ∑_{i<k} (Zᵢ - E Zᵢ) → 0` in probability. -/
theorem tendstoInMeasure_avg_sub_integral_of_indepFun [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) (hind : Pairwise fun i j => IndepFun (Z i) (Z j) P)
    {C : ℝ} (hvar : ∀ i, Var[Z i; P] ≤ C) :
    TendstoInMeasure P (fun (k : ℕ) ω => (k : ℝ)⁻¹ * ∑ i ∈ range k, (Z i ω - ∫ ω', Z i ω' ∂P))
      atTop (fun _ => 0) :=
  tendstoInMeasure_avg_sub_integral hZ
    (fun i j hij => (hind hij).covariance_eq_zero (hZ i) (hZ j)) hvar

/-- The weak law of large numbers with a bound on the second moments: square integrable,
pairwise uncorrelated `Zᵢ` with `E[Zᵢ²] ≤ C` satisfy `k⁻¹ ∑_{i<k} (Zᵢ - E Zᵢ) → 0` in
probability. -/
theorem tendstoInMeasure_avg_sub_integral_of_integral_sq_le [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) (hcov : ∀ i j, i ≠ j → cov[Z i, Z j; P] = 0)
    {C : ℝ} (hsq : ∀ i, ∫ ω, Z i ω ^ 2 ∂P ≤ C) :
    TendstoInMeasure P (fun (k : ℕ) ω => (k : ℝ)⁻¹ * ∑ i ∈ range k, (Z i ω - ∫ ω', Z i ω' ∂P))
      atTop (fun _ => 0) :=
  tendstoInMeasure_avg_sub_integral hZ hcov fun i =>
    (variance_le_expectation_sq (hZ i).aestronglyMeasurable).trans (hsq i)

/-- A deterministic sequence tending to `0` tends to `0` in probability. -/
theorem tendstoInMeasure_of_tendsto_const {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0)) :
    TendstoInMeasure P (fun k (_ : Ω) => u k) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  refine tendsto_const_nhds.congr' ?_
  have hev : ∀ᶠ k in atTop, dist (u k) 0 < ε := (Metric.tendsto_nhds.1 hu) ε hε
  filter_upwards [hev] with k hk
  have : {x : Ω | ε ≤ dist (u k) 0} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
    exact hk
  rw [this, measure_empty]

end MetaAnalysis

end CausalInference
