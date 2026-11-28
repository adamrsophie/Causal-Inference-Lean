/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Distance.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Metric properties of the distances between covariate summaries

With positive scales, the Euclidean, standardized Euclidean, Manhattan, Chebyshev, mean
absolute standardized difference and Gower distances, and the Minkowski distances of order
`q ≥ 1`, are metrics on `ℝ^p`. For `0 < q < 1` the Minkowski formula is not a metric: the
triangle inequality fails as soon as `p ≥ 2`. As the order grows, the Minkowski distance tends
to the Chebyshev distance.

## Main results

* `isMetric_euclidean`, `isMetric_stdEuclidean`, `isMetric_chebyshev`, `isMetric_minkowski`,
  `isMetric_manhattan`, `isMetric_meanAbsStdDiff`, `isMetric_gower`.
* `minkowski_eq_zero_iff`, `self_distances`: every distance vanishes exactly on the diagonal.
* `not_triangle_minkowski`, `not_triangle_minkowski_half`: the failure of the triangle
  inequality for `0 < q < 1`, in general and with computed numbers.
* `minkowski_dim_one`: in dimension one all Minkowski distances agree.
* `tendsto_minkowski_atTop`: `d_q → d_∞` as `q → ∞`.

## References

None beyond those of `Basic` and `Mahalanobis`.
-/

@[expose] public section

namespace CausalInference

namespace Transport

namespace Distance

variable {p : ℕ}

/-! ### The standardized gap -/

/-- With positive scales the standardized gap vanishes exactly when the summaries agree. -/
theorem stdGap_eq_zero_iff {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) (a b : Fin p → ℝ) :
    (∀ l, stdGap s a b l = 0) ↔ a = b := by
  simp only [stdGap, div_eq_zero_iff, sub_eq_zero]
  constructor
  · intro h; funext l; exact ((h l).resolve_right (hs l).ne').symm
  · intro h l; exact Or.inl (by rw [h])

/-- `|z(b, a) ℓ| = |z(a, b) ℓ|`. -/
theorem abs_stdGap_comm (s a b : Fin p → ℝ) (l : Fin p) :
    |stdGap s b a l| = |stdGap s a b l| := by
  simp only [stdGap]
  rw [← neg_sub, neg_div, abs_neg]

/-- `z(a, c) = z(a, b) + z(b, c)`. -/
theorem stdGap_add (s a b c : Fin p → ℝ) (l : Fin p) :
    stdGap s a c l = stdGap s a b l + stdGap s b c l := by
  simp only [stdGap]; ring

/-- The scaling map `v ↦ (v ℓ / s ℓ)` is injective for positive scales. -/
theorem scale_injective {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) :
    Function.Injective fun v : Fin p → ℝ ↦ fun l ↦ v l / s l := fun u v h ↦ by
  funext l
  have := congrFun h l
  exact (div_left_inj₀ (hs l).ne').1 this

/-! ### Metrics -/

/-- The Euclidean distance is a metric. -/
theorem isMetric_euclidean : IsMetric (euclidean (p := p)) :=
  isMetric_of_dist (WithLp.toLp_injective 2) fun _ _ ↦ rfl

/-- With positive scales the standardized Euclidean distance is a metric: it is the Euclidean
distance after the injective scaling `v ↦ (v ℓ / s ℓ)`. -/
theorem isMetric_stdEuclidean {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) :
    IsMetric (stdEuclidean s) := by
  refine isMetric_of_dist ((WithLp.toLp_injective 2).comp (scale_injective hs)) fun a b ↦ ?_
  rw [stdEuclidean, dist_comm, dist_eq_norm, ← WithLp.toLp_sub]
  congr 2
  funext l
  simp [stdGap, sub_div]

/-- With positive scales the Chebyshev distance is a metric: it is the sup distance after the
injective scaling. -/
theorem isMetric_chebyshev {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) : IsMetric (chebyshev s) := by
  refine isMetric_of_dist (scale_injective hs) fun a b ↦ ?_
  rw [chebyshev, dist_comm, dist_eq_norm]
  congr 1
  funext l
  simp [stdGap, sub_div]

/-- **The Minkowski distance vanishes exactly on the diagonal** for positive scales and a
positive order. -/
theorem minkowski_eq_zero_iff {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) {q : ℝ} (hq : 0 < q)
    (a b : Fin p → ℝ) : minkowski q s a b = 0 ↔ a = b := by
  have hS : 0 ≤ ∑ l, |stdGap s a b l| ^ q :=
    Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  rw [minkowski, Real.rpow_eq_zero hS (one_div_ne_zero hq.ne'),
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _,
    ← stdGap_eq_zero_iff hs]
  simp only [Finset.mem_univ, true_implies, Real.rpow_eq_zero (abs_nonneg _) hq.ne',
    abs_eq_zero]

/-- **Minkowski distances of order `q ≥ 1` are metrics** (positive scales). The triangle
inequality is Minkowski's inequality `Real.Lp_add_le` applied to
`z(a, c) = z(a, b) + z(b, c)`. -/
theorem isMetric_minkowski {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) {q : ℝ} (hq : 1 ≤ q) :
    IsMetric (minkowski q s) := by
  have hS : ∀ a b, 0 ≤ ∑ l, |stdGap s a b l| ^ q := fun a b ↦
    Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨fun a b ↦ Real.rpow_nonneg (hS a b) _, minkowski_eq_zero_iff hs (by linarith),
    fun a b ↦ ?_, fun a b c ↦ ?_⟩
  · simp only [minkowski, abs_stdGap_comm]
  · simp only [minkowski]
    have := Real.Lp_add_le Finset.univ (fun l ↦ stdGap s a b l) (fun l ↦ stdGap s b c l) hq
    simpa only [← stdGap_add] using this

/-- The Manhattan distance is a metric (positive scales): the Minkowski distance of order
one. -/
theorem isMetric_manhattan {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) : IsMetric (manhattan s) := by
  have e : minkowski 1 s = manhattan s := funext₂ fun a b ↦ minkowski_one s a b
  exact e ▸ isMetric_minkowski hs le_rfl

/-- The mean absolute standardized difference is a metric (positive scales, `p > 0`): the
Manhattan distance divided by `p`. -/
theorem isMetric_meanAbsStdDiff [NeZero p] {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) :
    IsMetric (meanAbsStdDiff s) :=
  (isMetric_manhattan hs).div_card

/-- Each Gower term with a positive range is nonnegative, vanishes exactly when the
coordinates agree, is symmetric and satisfies the triangle inequality; on a continuous
coordinate, `min (ρ, 1)` of a metric `ρ` is a metric. -/
theorem gowerTerm_props {r : Fin p → ℝ} (hr : ∀ l, 0 < r l) (bin : Fin p → Bool) (l : Fin p) :
    (∀ a b, 0 ≤ gowerTerm r bin a b l) ∧ (∀ a b, gowerTerm r bin a b l = 0 ↔ a l = b l) ∧
      (∀ a b, gowerTerm r bin a b l = gowerTerm r bin b a l) ∧
      ∀ a b c, gowerTerm r bin a c l ≤ gowerTerm r bin a b l + gowerTerm r bin b c l := by
  have hrl := hr l
  have hx : ∀ a b : Fin p → ℝ, 0 ≤ |b l - a l| / r l := fun a b ↦ div_nonneg (abs_nonneg _) hrl.le
  refine ⟨fun a b ↦ ?_, fun a b ↦ ?_, fun a b ↦ ?_, fun a b c ↦ ?_⟩
  · unfold gowerTerm; split_ifs
    · exact abs_nonneg _
    · exact le_min (hx a b) zero_le_one
  · unfold gowerTerm; split_ifs
    · rw [abs_eq_zero, sub_eq_zero, eq_comm]
    · constructor
      · intro h
        rcases min_choice (|b l - a l| / r l) 1 with h1 | h1
        · rw [h1, div_eq_zero_iff, abs_eq_zero, sub_eq_zero] at h
          exact (h.resolve_right hrl.ne').symm
        · rw [h1] at h; exact absurd h one_ne_zero
      · intro h; rw [h, sub_self, abs_zero, zero_div]; exact min_eq_left zero_le_one
  · unfold gowerTerm; rw [abs_sub_comm]
  · unfold gowerTerm; split_ifs
    · exact abs_sub_le _ _ _ |>.trans (le_of_eq (add_comm _ _))
    · have hy0 := hx a b
      have hz0 := hx b c
      rcases le_total 1 (|b l - a l| / r l) with hy | hy
      · rw [min_eq_right hy]
        linarith [min_le_right (|c l - a l| / r l) 1, le_min hz0 zero_le_one]
      rcases le_total 1 (|c l - b l| / r l) with hz | hz
      · rw [min_eq_right hz]
        linarith [min_le_right (|c l - a l| / r l) 1, le_min hy0 zero_le_one]
      have hxac : |c l - a l| / r l ≤ |b l - a l| / r l + |c l - b l| / r l := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right
          ((abs_sub_le _ _ _).trans (le_of_eq (add_comm _ _))) hrl.le
      rw [min_eq_left hy, min_eq_left hz]
      linarith [min_le_left (|c l - a l| / r l) 1]

/-- **The Gower distance is a metric** on `ℝ^p`, `p > 0`, for positive ranges: an average of
coordinate metrics that together separate points. -/
theorem isMetric_gower [NeZero p] {r : Fin p → ℝ} (hr : ∀ l, 0 < r l) (bin : Fin p → Bool) :
    IsMetric (gower r bin) := by
  have H := fun l ↦ gowerTerm_props hr bin l
  have hsum : IsMetric fun a b ↦ ∑ l, gowerTerm r bin a b l := by
    refine ⟨fun a b ↦ Finset.sum_nonneg fun l _ ↦ (H l).1 a b, fun a b ↦ ?_,
      fun a b ↦ Finset.sum_congr rfl fun l _ ↦ (H l).2.2.1 a b, fun a b c ↦ ?_⟩
    · rw [Finset.sum_eq_zero_iff_of_nonneg fun l _ ↦ (H l).1 a b, funext_iff]
      simp only [Finset.mem_univ, true_implies, (H _).2.1]
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun l _ ↦ (H l).2.2.2 a b c
  exact hsum.div_card

/-- **Every distance vanishes on the diagonal** (positive scales and ranges, positive Minkowski
order, `p > 0`). The Mahalanobis distance does too, by `isMetric_mahalanobis`. -/
theorem self_distances [NeZero p] {s r : Fin p → ℝ} (hs : ∀ l, 0 < s l) (hr : ∀ l, 0 < r l)
    (bin : Fin p → Bool) {q : ℝ} (hq : 0 < q) (x : Fin p → ℝ) :
    euclidean x x = 0 ∧ stdEuclidean s x x = 0 ∧ manhattan s x x = 0 ∧
      minkowski q s x x = 0 ∧ chebyshev s x x = 0 ∧ meanAbsStdDiff s x x = 0 ∧
      gower r bin x x = 0 :=
  ⟨(isMetric_euclidean.eq_zero_iff x x).2 rfl, ((isMetric_stdEuclidean hs).eq_zero_iff x x).2 rfl,
    ((isMetric_manhattan hs).eq_zero_iff x x).2 rfl, (minkowski_eq_zero_iff hs hq x x).2 rfl,
    ((isMetric_chebyshev hs).eq_zero_iff x x).2 rfl,
    ((isMetric_meanAbsStdDiff hs).eq_zero_iff x x).2 rfl,
    ((isMetric_gower hr bin).eq_zero_iff x x).2 rfl⟩

/-- With unit scales and ranges every distance is a metric (Minkowski of order `3/2`). -/
example : IsMetric (stdEuclidean (1 : Fin 3 → ℝ)) ∧ IsMetric (chebyshev (1 : Fin 3 → ℝ)) ∧
    IsMetric (minkowski (3 / 2) (1 : Fin 3 → ℝ)) ∧ IsMetric (manhattan (1 : Fin 3 → ℝ)) ∧
    IsMetric (meanAbsStdDiff (1 : Fin 3 → ℝ)) ∧
    IsMetric (gower (1 : Fin 3 → ℝ) ![true, false, false]) := by
  have h1 : ∀ l : Fin 3, (0 : ℝ) < (1 : Fin 3 → ℝ) l := fun _ ↦ one_pos
  exact ⟨isMetric_stdEuclidean h1, isMetric_chebyshev h1, isMetric_minkowski h1 (by norm_num),
    isMetric_manhattan h1, isMetric_meanAbsStdDiff h1, isMetric_gower h1 _⟩

example (x : Fin 2 → ℝ) : minkowski (1 / 2) (1 : Fin 2 → ℝ) x x = 0 ∧
    gower (1 : Fin 2 → ℝ) ![true, false] x x = 0 :=
  have h1 : ∀ l : Fin 2, (0 : ℝ) < (1 : Fin 2 → ℝ) l := fun _ ↦ one_pos
  ⟨(self_distances h1 h1 ![true, false] (by norm_num : (0 : ℝ) < 1 / 2) x).2.2.2.1,
    (self_distances h1 h1 ![true, false] (by norm_num : (0 : ℝ) < 1 / 2) x).2.2.2.2.2.2⟩

/-! ### Minkowski distances of order below one -/

/-- **For `0 < q < 1` the Minkowski formula violates the triangle inequality when `p ≥ 2`**,
for any positive scales. With `a = 0`, `b = s₀ e₀`, `c = s₀ e₀ + s₁ e₁`, one has
`d(a, b) = d(b, c) = 1` while `d(a, c) = 2^{1/q} > 2`. -/
theorem not_triangle_minkowski {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hp : 2 ≤ p) :
    ∃ a b c : Fin p → ℝ, minkowski q s a b + minkowski q s b c < minkowski q s a c := by
  set i0 : Fin p := ⟨0, by omega⟩
  set i1 : Fin p := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  refine ⟨0, fun l ↦ if l = i0 then s l else 0, fun l ↦ if l = i0 ∨ l = i1 then s l else 0, ?_⟩
  have hsne : ∀ l, s l ≠ 0 := fun l ↦ (hs l).ne'
  have e1 : ∀ l, |stdGap s 0 (fun l ↦ if l = i0 then s l else 0) l| ^ q =
      if l = i0 then 1 else 0 := fun l ↦ by
    by_cases h : l = i0
    · simp [stdGap, h, hsne]
    · simp [stdGap, h, Real.zero_rpow hq0.ne']
  have e2 : ∀ l, |stdGap s (fun l ↦ if l = i0 then s l else 0)
      (fun l ↦ if l = i0 ∨ l = i1 then s l else 0) l| ^ q = if l = i1 then 1 else 0 := fun l ↦ by
    by_cases h1 : l = i1
    · simp [stdGap, h1, h01.symm, hsne]
    · by_cases h0 : l = i0
      · simp [stdGap, h0, h01, Real.zero_rpow hq0.ne']
      · simp [stdGap, h0, h1, Real.zero_rpow hq0.ne']
  have e3 : ∀ l, |stdGap s 0 (fun l ↦ if l = i0 ∨ l = i1 then s l else 0) l| ^ q =
      (if l = i0 then 1 else 0) + if l = i1 then 1 else 0 := fun l ↦ by
    by_cases h0 : l = i0
    · simp [stdGap, h0, h01, hsne]
    · by_cases h1 : l = i1
      · simp [stdGap, h1, h01.symm, hsne]
      · simp [stdGap, h0, h1, Real.zero_rpow hq0.ne']
  simp only [minkowski, e1, e2, e3, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Real.one_rpow]
  have hlt : (1 : ℝ) < 1 / q := by rw [lt_one_div one_pos hq0]; simpa using hq1
  have := Real.rpow_lt_rpow_of_exponent_lt (x := 2) one_lt_two hlt
  rw [Real.rpow_one] at this
  norm_num at this ⊢
  linarith

example : ∃ a b c : Fin 2 → ℝ, minkowski (1 / 2) 1 a b + minkowski (1 / 2) 1 b c <
    minkowski (1 / 2) 1 a c :=
  not_triangle_minkowski (fun _ ↦ one_pos) (by norm_num) (by norm_num) le_rfl

/-- **The failure with computed numbers.** For `q = 1/2`, unit scales and
`a = (0, 0)`, `b = (1, 0)`, `c = (1, 1)`: `d(a, b) = d(b, c) = 1` and `d(a, c) = 4`. -/
theorem not_triangle_minkowski_half :
    minkowski (1 / 2) (1 : Fin 2 → ℝ) 0 ![1, 0] = 1 ∧
      minkowski (1 / 2) (1 : Fin 2 → ℝ) ![1, 0] ![1, 1] = 1 ∧
      minkowski (1 / 2) (1 : Fin 2 → ℝ) 0 ![1, 1] = 4 := by
  have h0 : (0 : ℝ) ^ (1 / 2 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have h4 : (2 : ℝ) ^ (1 / (1 / 2) : ℝ) = 4 := by norm_num
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [minkowski, stdGap, Fin.sum_univ_two, Pi.one_apply, div_one, Pi.zero_apply] <;>
    norm_num [h0, h4]

/-- **In dimension one every Minkowski distance of positive order is the standardized absolute
distance**: `d_q(a, b) = |b - a| / s`. -/
theorem minkowski_dim_one {q : ℝ} (hq : 0 < q) {s : Fin 1 → ℝ} (hs : 0 < s 0)
    (a b : Fin 1 → ℝ) : minkowski q s a b = |b 0 - a 0| / s 0 := by
  rw [minkowski, Fin.sum_univ_one, one_div, Real.rpow_rpow_inv (abs_nonneg _) hq.ne', stdGap,
    abs_div, abs_of_pos hs]

example (a b : Fin 1 → ℝ) : minkowski (1 / 2) ![2] a b = |b 0 - a 0| / 2 :=
  minkowski_dim_one (by norm_num) (by norm_num) a b

/-! ### The limit of large orders -/

/-- **The Chebyshev distance is the limit of the Minkowski distances as the order grows**:
`d_∞ ≤ d_q ≤ p^{1/q} d_∞` for `q > 0`, and `p^{1/q} → 1`. -/
theorem tendsto_minkowski_atTop (s x y : Fin p → ℝ) :
    Filter.Tendsto (fun q ↦ minkowski q s x y) Filter.atTop (nhds (chebyshev s x y)) := by
  set z := stdGap s x y
  set M := chebyshev s x y
  have hM0 : 0 ≤ M := norm_nonneg _
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have hM : M = 0 := by
      change ‖z‖ = 0
      rw [norm_eq_zero]; exact Subsingleton.elim _ _
    rw [hM]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with q hq
    simp only [minkowski, Finset.univ_eq_empty, Finset.sum_empty]
    rw [Real.zero_rpow (one_div_ne_zero hq.ne')]
  have hlow : ∀ q : ℝ, 0 < q → M ≤ minkowski q s x y := fun q hq ↦ by
    refine (chebyshev_le_iff (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦
      Real.rpow_nonneg (abs_nonneg _) _) _)).2 fun l ↦ ?_
    have h1 : |z l| ^ q ≤ ∑ k, |z k| ^ q :=
      Finset.single_le_sum (f := fun k ↦ |z k| ^ q)
        (fun k _ ↦ Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ l)
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h1
      (one_div_nonneg.2 hq.le)
    rwa [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hq.ne', Real.rpow_one] at h2
  have hup : ∀ q : ℝ, 0 < q → minkowski q s x y ≤ (p : ℝ) ^ (1 / q) * M := fun q hq ↦ by
    have h1 : ∑ k, |z k| ^ q ≤ (p : ℝ) * M ^ q := by
      calc ∑ k, |z k| ^ q ≤ ∑ _k : Fin p, M ^ q :=
            Finset.sum_le_sum fun k _ ↦ Real.rpow_le_rpow (abs_nonneg _)
              (abs_stdGap_le_chebyshev s x y k) hq.le
        _ = (p : ℝ) * M ^ q := by simp
    have h2 := Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ ↦
      Real.rpow_nonneg (abs_nonneg _) _) h1 (one_div_nonneg.2 hq.le)
    rwa [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM0 _), ← Real.rpow_mul hM0,
      mul_one_div_cancel hq.ne', Real.rpow_one] at h2
  have hlim : Filter.Tendsto (fun q : ℝ ↦ (p : ℝ) ^ (1 / q) * M) Filter.atTop (nhds M) := by
    have h0 : Filter.Tendsto (fun q : ℝ ↦ 1 / q) Filter.atTop (nhds 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero
    have hc : ContinuousAt (fun t : ℝ ↦ (p : ℝ) ^ t) 0 :=
      Real.continuousAt_const_rpow (Nat.cast_ne_zero.2 hp.ne')
    have := (hc.tendsto.comp h0).mul_const M
    simpa only [Function.comp_def, Real.rpow_zero, one_mul] using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with q hq using hlow q hq
  · filter_upwards [Filter.eventually_gt_atTop 0] with q hq using hup q hq

end Distance

end Transport

end CausalInference
