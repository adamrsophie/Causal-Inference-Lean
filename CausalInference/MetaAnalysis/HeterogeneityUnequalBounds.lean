/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.DerSimonianLaird

/-!
# Meta-analysis: deterministic bounds for heterogeneity estimators with unequal variances

Let `k` studies have within study variances `a ≤ vᵢ ≤ A`, `0 < a`, with the inverse variance
weights `wᵢ = 1 / vᵢ` and `W = ∑ wᵢ`. This file proves the deterministic inequalities that the
consistency proofs of `MetaAnalysis.HeterogeneityUnequalConsistency` rest on. For every data
vector `y` and all `θ`, `τ²`:

* **The slope is of order `k`**: `c = ∑ wᵢ - ∑ wᵢ² / ∑ wᵢ ≥ k / A - 1 / a`
  (`cochranQSlope_ge_of_bounds`). Since `wᵢ ≤ 1 / a`, no study carries more than a bounded
  share of the weight: `∑ wᵢ² / ∑ wᵢ ≤ 1 / a`.
* **The error identity** (`dlTau2Untruncated_sub_mul_cochranQSlope`):
  `(τ̂²_DL - τ²) c = ∑ wᵢ ((yᵢ - θ)² - (vᵢ + τ²)) - (∑ wᵢ (yᵢ - θ))² / W + 1 + τ² ∑ wᵢ² / W`,
  where `τ̂²_DL` is the untruncated moment estimator.
* **The error bound** (`abs_dlTau2Untruncated_sub_le`): for `k ≥ 2A / a`,
  `|τ̂²_DL - τ²| ≤ 2A (|∑ wᵢ ((yᵢ - θ)² - (vᵢ + τ²))| / k + A (∑ wᵢ (yᵢ - θ) / k)²
  + (1 + |τ²| / a) / k)`.
* **The pooled estimate with an arbitrary between study variance** (`abs_ivwEstimate_add_sub_le`):
  for `t ≥ 0` and `τ² ≥ 0`, with `uᵢ = 1 / (vᵢ + τ²)`,
  `|θ̂(t) - θ| ≤ (A + τ² + |t - τ²|) (|∑ uᵢ (yᵢ - θ)| / k
  + |t - τ²| / a² (1 + A (|∑ wᵢ ((yᵢ - θ)² - (vᵢ + τ²))| / k + 1 + τ² / a)))`,
  where `θ̂(t)` is the pooled estimate with the weights `1 / (vᵢ + t)`.

The last bound is uniform in `t`: it controls the pooled estimate with random weights
`1 / (vᵢ + τ̂²)` through `|τ̂² - τ²|` and two weighted sums with fixed weights.

## Main results

* `cochranQSlope_ge_of_bounds`, `dlTau2Untruncated_sub_mul_cochranQSlope`,
  `abs_dlTau2Untruncated_sub_le`, `abs_ivwEstimate_add_sub_le`.

## References

* R. DerSimonian and N. Laird, *Meta-analysis in clinical trials*, Controlled Clinical Trials 7
  (1986).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι] {v : ι → ℝ} {a A : ℝ}

/-- With variances `vᵢ ≤ A`, the total weight is at least `k / A`. -/
theorem card_div_le_sum_ivWeight (ha : 0 < a) (hva : ∀ i, a ≤ v i) (hvA : ∀ i, v i ≤ A) :
    (Fintype.card ι : ℝ) / A ≤ ∑ i, ivWeight v i := by
  have hA : 0 < A := ha.trans_le ((hva (Classical.arbitrary ι)).trans (hvA _))
  have h : ∀ i, 1 / A ≤ ivWeight v i := fun i =>
    one_div_le_one_div_of_le (ha.trans_le (hva i)) (hvA i)
  calc (Fintype.card ι : ℝ) / A = ∑ _i : ι, 1 / A := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ∑ i, ivWeight v i := Finset.sum_le_sum fun i _ => h i

/-- With variances `vᵢ ≥ a > 0`, `∑ wᵢ² / ∑ wᵢ ≤ 1 / a`: no study dominates the weights. -/
theorem sum_ivWeight_sq_div_le (ha : 0 < a) (hva : ∀ i, a ≤ v i) :
    (∑ i, ivWeight v i ^ 2) / ∑ i, ivWeight v i ≤ 1 / a := by
  have hv : ∀ i, 0 < v i := fun i => ha.trans_le (hva i)
  have hW := sum_ivWeight_pos hv
  have h : ∀ i, ivWeight v i ^ 2 ≤ ivWeight v i * (1 / a) := fun i => by
    rw [sq]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le ha (hva i))
      (ivWeight_pos hv i).le
  rw [div_le_iff₀ hW]
  calc ∑ i, ivWeight v i ^ 2 ≤ ∑ i, ivWeight v i * (1 / a) := Finset.sum_le_sum fun i _ => h i
    _ = 1 / a * ∑ i, ivWeight v i := by rw [← Finset.sum_mul, mul_comm]

/-- **The slope of `E[Q]` is of order `k`**: with variances `a ≤ vᵢ ≤ A`, `0 < a`,
`cochranQSlope v ≥ k / A - 1 / a`. -/
theorem cochranQSlope_ge_of_bounds (ha : 0 < a) (hva : ∀ i, a ≤ v i) (hvA : ∀ i, v i ≤ A) :
    (Fintype.card ι : ℝ) / A - 1 / a ≤ cochranQSlope v := by
  rw [cochranQSlope]
  linarith [card_div_le_sum_ivWeight ha hva hvA, sum_ivWeight_sq_div_le ha hva]

omit [Nonempty ι] in
/-- `∑ wᵢ vᵢ = k`. -/
theorem sum_ivWeight_mul_self (hv : ∀ i, 0 < v i) :
    ∑ i, ivWeight v i * v i = Fintype.card ι := by
  simp only [mul_comm (ivWeight v _), mul_ivWeight hv, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

/-- **The error identity of the moment estimator**: for positive variances with a nonzero
slope `c`,
`(τ̂²_DL - τ²) c = ∑ wᵢ ((yᵢ - θ)² - (vᵢ + τ²)) - (∑ wᵢ (yᵢ - θ))² / W + 1 + τ² ∑ wᵢ² / W`. -/
theorem dlTau2Untruncated_sub_mul_cochranQSlope (hv : ∀ i, 0 < v i)
    (hc : cochranQSlope v ≠ 0) (y : ι → ℝ) (θ τ2 : ℝ) :
    (dlTau2Untruncated v y - τ2) * cochranQSlope v =
      ∑ i, ivWeight v i * ((y i - θ) ^ 2 - (v i + τ2)) -
        (∑ i, ivWeight v i * (y i - θ)) ^ 2 / ∑ i, ivWeight v i + 1 +
          τ2 * (∑ i, ivWeight v i ^ 2) / ∑ i, ivWeight v i := by
  have hW := (sum_ivWeight_pos hv).ne'
  have hQ := cochranQ_eq_sub hv y θ
  have hS := sum_ivWeight_mul_sub hv y θ
  have hk := sum_ivWeight_mul_self hv
  have hsplit : ∑ i, ivWeight v i * ((y i - θ) ^ 2 - (v i + τ2)) =
      ∑ i, ivWeight v i * (y i - θ) ^ 2 - ∑ i, ivWeight v i * v i -
        τ2 * ∑ i, ivWeight v i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hk, hS, dlTau2Untruncated, hQ, sub_mul, div_mul_cancel₀ _ hc, cochranQSlope]
  field_simp
  ring

/-- The real inequality behind `abs_dlTau2Untruncated_sub_le`: if
`x c = S - N² / W + 1 + τ² r` with `c ≥ k / (2A) > 0`, `W ≥ k / A > 0` and `0 ≤ r ≤ 1 / a`, then
`|x| ≤ 2A (|S| / k + A (N / k)² + (1 + |τ²| / a) / k)`. -/
theorem abs_le_of_mul_slope_eq {x c S N W r k A a τ2 : ℝ} (hk : 0 < k) (hA : 0 < A)
    (ha : 0 < a) (hW : k / A ≤ W) (hc : k / (2 * A) ≤ c) (hr0 : 0 ≤ r) (hr : r ≤ 1 / a)
    (hx : x * c = S - N ^ 2 / W + 1 + τ2 * r) :
    |x| ≤ 2 * A * (|S| / k + A * (N / k) ^ 2 + (1 + |τ2| / a) / k) := by
  have hkA : 0 < k / A := div_pos hk hA
  have hWpos : 0 < W := hkA.trans_le hW
  have hcpos : 0 < c := lt_of_lt_of_le (div_pos hk (by positivity)) hc
  have hN : N ^ 2 / W ≤ A * k * (N / k) ^ 2 := by
    have h1 : A * k * (N / k) ^ 2 = N ^ 2 / (k / A) := by
      field_simp
    rw [h1]
    exact div_le_div_of_nonneg_left (sq_nonneg N) hkA hW
  have hNW : 0 ≤ N ^ 2 / W := div_nonneg (sq_nonneg _) hWpos.le
  have h3 : |τ2 * r| ≤ |τ2| / a := by
    rw [abs_mul, abs_of_nonneg hr0, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)
  set B := |S| + A * k * (N / k) ^ 2 + (1 + |τ2| / a) with hB
  have hR : |x| * c ≤ B := by
    rw [← abs_of_pos hcpos, ← abs_mul, hx]
    have e1 := abs_add_le (S - N ^ 2 / W + 1) (τ2 * r)
    have e2 := abs_add_le (S - N ^ 2 / W) 1
    have e3 := abs_sub S (N ^ 2 / W)
    rw [abs_of_nonneg hNW] at e3
    rw [abs_one] at e2
    linarith
  have hB0 : 0 ≤ B := by positivity
  have hfin : 2 * A * (|S| / k + A * (N / k) ^ 2 + (1 + |τ2| / a) / k) = B * (2 * A / k) := by
    rw [hB]
    field_simp
  rw [hfin]
  have h4 : |x| ≤ B / c := by rw [le_div_iff₀ hcpos]; exact hR
  refine h4.trans ?_
  rw [div_le_iff₀ hcpos]
  calc B = B * (2 * A / k) * (k / (2 * A)) := by field_simp
    _ ≤ B * (2 * A / k) * c := mul_le_mul_of_nonneg_left hc (by positivity)

/-- **The error bound of the moment estimator**: with variances `a ≤ vᵢ ≤ A`, `0 < a`, and
`k ≥ 2A / a` studies,
`|τ̂²_DL - τ²| ≤ 2A (|∑ wᵢ ((yᵢ - θ)² - (vᵢ + τ²))| / k + A (∑ wᵢ (yᵢ - θ) / k)²
+ (1 + |τ²| / a) / k)`. -/
theorem abs_dlTau2Untruncated_sub_le (ha : 0 < a) (hva : ∀ i, a ≤ v i) (hvA : ∀ i, v i ≤ A)
    (hk : 2 * A / a ≤ Fintype.card ι) (y : ι → ℝ) (θ τ2 : ℝ) :
    |dlTau2Untruncated v y - τ2| ≤ 2 * A *
      (|∑ i, ivWeight v i * ((y i - θ) ^ 2 - (v i + τ2))| / Fintype.card ι +
        A * ((∑ i, ivWeight v i * (y i - θ)) / Fintype.card ι) ^ 2 +
          (1 + |τ2| / a) / Fintype.card ι) := by
  have hv : ∀ i, 0 < v i := fun i => ha.trans_le (hva i)
  have hA : 0 < A := ha.trans_le ((hva (Classical.arbitrary ι)).trans (hvA _))
  have hkpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc0 := cochranQSlope_ge_of_bounds ha hva hvA
  have hca : 1 / a ≤ (Fintype.card ι : ℝ) / (2 * A) := by
    rw [div_le_div_iff₀ ha (by positivity)]
    rw [div_le_iff₀ ha] at hk
    linarith
  have hc : (Fintype.card ι : ℝ) / (2 * A) ≤ cochranQSlope v := by
    have : (Fintype.card ι : ℝ) / A = 2 * ((Fintype.card ι : ℝ) / (2 * A)) := by
      field_simp
    linarith
  have hcpos : 0 < cochranQSlope v := lt_of_lt_of_le (by positivity) hc
  have hid := dlTau2Untruncated_sub_mul_cochranQSlope hv hcpos.ne' y θ τ2
  rw [mul_div_assoc] at hid
  exact abs_le_of_mul_slope_eq hkpos hA ha (card_div_le_sum_ivWeight ha hva hvA) hc
    (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (sum_ivWeight_pos hv).le)
    (sum_ivWeight_sq_div_le ha hva) hid

/-- **The pooled estimate with an arbitrary between study variance**: with variances
`a ≤ vᵢ ≤ A`, `0 < a`, `τ² ≥ 0` and `t ≥ 0`, the pooled estimate with the weights `1 / (vᵢ + t)`
satisfies `|θ̂(t) - θ| ≤ (A + τ² + |t - τ²|) (|∑ uᵢ (yᵢ - θ)| / k
+ |t - τ²| / a² (1 + A (|∑ wᵢ ((yᵢ - θ)² - (vᵢ + τ²))| / k + 1 + τ² / a)))`, with
`uᵢ = 1 / (vᵢ + τ²)` and `wᵢ = 1 / vᵢ`. The bound holds for every `t ≥ 0` at once. -/
theorem abs_ivwEstimate_add_sub_le (ha : 0 < a) (hva : ∀ i, a ≤ v i) (hvA : ∀ i, v i ≤ A)
    {τ2 t : ℝ} (hτ : 0 ≤ τ2) (ht : 0 ≤ t) (y : ι → ℝ) (θ : ℝ) :
    |ivwEstimate (fun i => v i + t) y - θ| ≤ (A + τ2 + |t - τ2|) *
      (|∑ i, ivWeight (fun i => v i + τ2) i * (y i - θ)| / Fintype.card ι +
        |t - τ2| / a ^ 2 * (1 + A * (|∑ i, ivWeight v i * ((y i - θ) ^ 2 - (v i + τ2))| /
          Fintype.card ι + 1 + τ2 / a))) := by
  have hv : ∀ i, 0 < v i := fun i => ha.trans_le (hva i)
  have hA : 0 < A := ha.trans_le ((hva (Classical.arbitrary ι)).trans (hvA _))
  have hkpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : ∀ i, 0 < v i + t := fun i => by linarith [hv i]
  have hsτ : ∀ i, 0 < v i + τ2 := fun i => by linarith [hv i]
  have hU : (Fintype.card ι : ℝ) / (A + t) ≤ ∑ i, ivWeight (fun i => v i + t) i :=
    card_div_le_sum_ivWeight (a := a + t) (by linarith) (fun i => by linarith [hva i])
      (fun i => by linarith [hvA i])
  have hUpos := sum_ivWeight_pos hs
  have hNt := sum_ivWeight_mul_sub hs y θ
  set Nt := ∑ i, ivWeight (fun i => v i + t) i * (y i - θ) with hNt_def
  set Nτ := ∑ i, ivWeight (fun i => v i + τ2) i * (y i - θ) with hNτ_def
  set S := ∑ i, ivWeight v i * ((y i - θ) ^ 2 - (v i + τ2)) with hS_def
  -- the pooled estimate through the weighted sum
  have habs : |ivwEstimate (fun i => v i + t) y - θ| ≤ (A + t) / Fintype.card ι * |Nt| := by
    have h1 : |ivwEstimate (fun i => v i + t) y - θ| =
        |Nt| / ∑ i, ivWeight (fun i => v i + t) i := by
      rw [hNt, abs_mul, abs_of_pos hUpos, mul_div_cancel_left₀ _ hUpos.ne']
    rw [h1, div_le_iff₀ hUpos]
    calc |Nt| = (A + t) / Fintype.card ι * |Nt| * ((Fintype.card ι : ℝ) / (A + t)) := by
          field_simp
      _ ≤ (A + t) / Fintype.card ι * |Nt| * ∑ i, ivWeight (fun i => v i + t) i :=
          mul_le_mul_of_nonneg_left hU (by positivity)
  -- the change of the weights
  have hdiff : ∀ i, |ivWeight (fun i => v i + t) i - ivWeight (fun i => v i + τ2) i| ≤
      |t - τ2| / a ^ 2 := by
    intro i
    have he : ivWeight (fun i => v i + t) i - ivWeight (fun i => v i + τ2) i =
        (τ2 - t) / ((v i + t) * (v i + τ2)) := by
      simp only [ivWeight]
      rw [div_sub_div _ _ (hs i).ne' (hsτ i).ne']
      ring
    have hprod : a ^ 2 ≤ (v i + t) * (v i + τ2) := by
      rw [sq]
      exact mul_le_mul (by linarith [hva i]) (by linarith [hva i]) ha.le (hs i).le
    rw [he, abs_div, abs_of_pos (mul_pos (hs i) (hsτ i)), abs_sub_comm]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hprod
  have hNbound : |Nt| ≤ |Nτ| + |t - τ2| / a ^ 2 * ∑ i, |y i - θ| := by
    have hsplit : Nt = Nτ + ∑ i, (ivWeight (fun i => v i + t) i -
        ivWeight (fun i => v i + τ2) i) * (y i - θ) := by
      rw [hNt_def, hNτ_def, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hdiff i) (abs_nonneg _)
  -- the absolute deviations through the weighted squares
  have habsy : ∀ i, |y i - θ| ≤ 1 + A * (ivWeight v i * (y i - θ) ^ 2) := by
    intro i
    have h1 : |y i - θ| ≤ 1 + (y i - θ) ^ 2 := by
      nlinarith [abs_nonneg (y i - θ), sq_abs (y i - θ)]
    have h2 : 1 ≤ A * ivWeight v i := by
      rw [ivWeight, mul_one_div, le_div_iff₀ (hv i), one_mul]
      exact hvA i
    nlinarith [sq_nonneg (y i - θ)]
  have hWa : ∑ i, ivWeight v i ≤ Fintype.card ι / a := by
    calc ∑ i, ivWeight v i ≤ ∑ _i : ι, 1 / a :=
          Finset.sum_le_sum fun i _ => one_div_le_one_div_of_le ha (hva i)
      _ = Fintype.card ι / a := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hsq : ∑ i, ivWeight v i * (y i - θ) ^ 2 =
      S + Fintype.card ι + τ2 * ∑ i, ivWeight v i := by
    rw [hS_def, ← sum_ivWeight_mul_self hv, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsumy : ∑ i, |y i - θ| ≤ Fintype.card ι * (1 + A * (|S| / Fintype.card ι + 1 +
      τ2 / a)) := by
    have h1 : ∑ i, |y i - θ| ≤ Fintype.card ι + A * ∑ i, ivWeight v i * (y i - θ) ^ 2 := by
      calc ∑ i, |y i - θ| ≤ ∑ i, (1 + A * (ivWeight v i * (y i - θ) ^ 2)) :=
            Finset.sum_le_sum fun i _ => habsy i
        _ = Fintype.card ι + A * ∑ i, ivWeight v i * (y i - θ) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul, mul_one]
    have h2 : τ2 * ∑ i, ivWeight v i ≤ τ2 * (Fintype.card ι / a) :=
      mul_le_mul_of_nonneg_left hWa hτ
    have h3 : Fintype.card ι * (1 + A * (|S| / Fintype.card ι + 1 + τ2 / a)) =
        Fintype.card ι + A * (|S| + Fintype.card ι + τ2 * (Fintype.card ι / a)) := by
      field_simp
    rw [h3, hsq] at *
    rw [hsq] at h1
    have h4 := le_abs_self S
    nlinarith
  -- combine
  set R := |Nτ| / Fintype.card ι + |t - τ2| / a ^ 2 * (1 + A * (|S| / Fintype.card ι + 1 +
    τ2 / a)) with hR
  have hR0 : 0 ≤ R := by positivity
  have hkey : (A + t) / Fintype.card ι * |Nt| ≤ (A + t) * R := by
    have h1 : |Nt| / Fintype.card ι ≤ R := by
      rw [div_le_iff₀ hkpos]
      calc |Nt| ≤ |Nτ| + |t - τ2| / a ^ 2 * ∑ i, |y i - θ| := hNbound
        _ ≤ |Nτ| + |t - τ2| / a ^ 2 * (Fintype.card ι * (1 + A * (|S| / Fintype.card ι + 1 +
            τ2 / a))) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsumy (by positivity))
        _ = R * Fintype.card ι := by rw [hR]; field_simp
    calc (A + t) / Fintype.card ι * |Nt| = (A + t) * (|Nt| / Fintype.card ι) := by ring
      _ ≤ (A + t) * R := mul_le_mul_of_nonneg_left h1 (by linarith)
  have hAt : A + t ≤ A + τ2 + |t - τ2| := by linarith [le_abs_self (t - τ2)]
  exact habs.trans (hkey.trans (mul_le_mul_of_nonneg_right hAt hR0))

end MetaAnalysis

end CausalInference
