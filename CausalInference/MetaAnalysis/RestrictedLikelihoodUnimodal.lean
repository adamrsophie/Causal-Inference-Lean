/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedLikelihoodMaximizer

/-!
# A unique maximizer of the restricted likelihood

The restricted log likelihood `ℓ_R(τ²)` of the random effects model can have several local
maxima (`exists_two_isMaxOn_restrictedLogLik`). This file gives conditions for a unique
maximizer on `[0, ∞)`.

* **One sign change of the derivative** (`lt_of_hasDerivAt_sign_change`): if `f` is continuous
  on `[0, ∞)`, differentiable on `(0, ∞)` with derivative positive on `(0, c)` and negative on
  `(c, ∞)`, then `c` is the unique maximizer of `f` on `[0, ∞)`. For the restricted likelihood
  (`restrictedLogLik_lt_of_score_sign`) the derivative is the restricted score; in particular a
  score negative on `(0, ∞)` makes `τ² = 0` the unique maximizer
  (`restrictedLogLik_lt_zero_of_score_neg`).
* **A checkable sufficient condition for `τ̂² = 0`** (`restrictedScore_neg_of_spread`,
  `restrictedLogLik_lt_zero_of_spread`): let `k` studies have variances in `[v₋, v₊]` and let
  every squared difference of two estimates be at most `D`. If `D < v₋ - v₊ / k`, the restricted
  score is negative on `[0, ∞)`, so `τ² = 0` is the unique maximizer. This covers unequal
  variances and any number of studies. Proof: `(yᵢ - θ̂)² ≤ D` since `θ̂` is a weighted mean,
  `∑ wᵢ² ≤ ∑ wᵢ / (v₋ + τ²)` and `∑ wᵢ ≥ k / (v₊ + τ²)`.

No checkable condition for a unique interior maximizer (a score positive then negative) was
found; only the general lemma above is proved for that case.

## Main results

* `lt_of_hasDerivAt_sign_change`, `restrictedLogLik_lt_of_score_sign`, `pos_of_spread`,
  `restrictedLogLik_lt_zero_of_score_neg`, `sq_sub_ivwEstimate_le`,
  `restrictedScore_neg_of_spread`, `restrictedLogLik_lt_zero_of_spread`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
* D. A. Harville, *Bayesian inference for variance components using only error contrasts*,
  Biometrika 61 (1974).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Set

/-- **One sign change of the derivative gives a unique maximizer**: let `f` be continuous on
`[0, ∞)` with derivative `f'` on `(0, ∞)`, `f' > 0` on `(0, c)` and `f' < 0` on `(c, ∞)`, where
`c ≥ 0`. Then `f t < f c` for every `t ≥ 0`, `t ≠ c`. -/
theorem lt_of_hasDerivAt_sign_change {f f' : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hcont : ContinuousOn f (Ici 0)) (hd : ∀ t, 0 < t → HasDerivAt f (f' t) t)
    (hpos : ∀ t, 0 < t → t < c → 0 < f' t) (hneg : ∀ t, c < t → f' t < 0) {t : ℝ}
    (ht : 0 ≤ t) (htc : t ≠ c) : f t < f c := by
  rcases lt_or_gt_of_ne htc with hlt | hgt
  · have hmono : StrictMonoOn f (Icc 0 c) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 c) (hcont.mono Icc_subset_Ici_self)
        fun x hx => ?_
      rw [interior_Icc] at hx
      rw [(hd x hx.1).deriv]
      exact hpos x hx.1 hx.2
    exact hmono ⟨ht, hlt.le⟩ ⟨hc, le_rfl⟩ hlt
  · have hanti : StrictAntiOn f (Ici c) := by
      refine strictAntiOn_of_deriv_neg (convex_Ici c) (hcont.mono (Ici_subset_Ici.2 hc))
        fun x hx => ?_
      rw [interior_Ici] at hx
      rw [(hd x (lt_of_le_of_lt hc hx)).deriv]
      exact hneg x hx
    exact hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hgt.le) hgt

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The restricted log likelihood is continuous on `[0, ∞)` for positive variances. -/
theorem continuousOn_restrictedLogLik {v : ι → ℝ} (hv : ∀ i, 0 < v i) (y : ι → ℝ) :
    ContinuousOn (restrictedLogLik v y) (Ici 0) := fun _t ht =>
  (hasDerivAt_restrictedLogLik y fun i => add_pos_of_pos_of_nonneg (hv i) ht).continuousAt
    |>.continuousWithinAt

/-- **A restricted score with one sign change**: for positive variances, if the restricted score
is positive on `(0, c)` and negative on `(c, ∞)`, `c ≥ 0`, then `c` is the unique maximizer of
the restricted log likelihood on `[0, ∞)`. -/
theorem restrictedLogLik_lt_of_score_sign {v : ι → ℝ} (hv : ∀ i, 0 < v i) (y : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hpos : ∀ t, 0 < t → t < c → 0 < restrictedScore v y t)
    (hneg : ∀ t, c < t → restrictedScore v y t < 0) {t : ℝ} (ht : 0 ≤ t) (htc : t ≠ c) :
    restrictedLogLik v y t < restrictedLogLik v y c :=
  lt_of_hasDerivAt_sign_change hc (continuousOn_restrictedLogLik hv y)
    (fun _t ht => hasDerivAt_restrictedLogLik y fun i => add_pos (hv i) ht) hpos hneg ht htc

/-- **A negative restricted score makes `τ² = 0` the unique maximizer**: for positive variances,
if the restricted score is negative on `(0, ∞)`, then `ℓ_R(t) < ℓ_R(0)` for every `t > 0`. -/
theorem restrictedLogLik_lt_zero_of_score_neg {v : ι → ℝ} (hv : ∀ i, 0 < v i) (y : ι → ℝ)
    (hneg : ∀ t, 0 < t → restrictedScore v y t < 0) {t : ℝ} (ht : 0 < t) :
    restrictedLogLik v y t < restrictedLogLik v y 0 :=
  restrictedLogLik_lt_of_score_sign hv y le_rfl (fun _t h h' => absurd h' (not_lt.2 h.le)) hneg
    ht.le ht.ne'

omit [Nonempty ι] in
/-- **Residuals from a weighted mean are bounded by the spread**: for positive weights
`wᵢ = 1/vᵢ`, if `(yᵢ - yⱼ)² ≤ D` for all `i, j`, then `(yᵢ - θ̂)² ≤ D` for every `i`. -/
theorem sq_sub_ivwEstimate_le [Nonempty ι] {v : ι → ℝ} (hv : ∀ i, 0 < v i) {y : ι → ℝ} {D : ℝ}
    (hD : ∀ i j, (y i - y j) ^ 2 ≤ D) (i : ι) : (y i - ivwEstimate v y) ^ 2 ≤ D := by
  have hW := sum_ivWeight_pos hv
  have hD0 : 0 ≤ D := le_trans (sq_nonneg _) (hD i i)
  have hrep : y i - ivwEstimate v y =
      (∑ j, ivWeight v j * (y i - y j)) / ∑ j, ivWeight v j := by
    rw [ivwEstimate, PopulationAdjustment.weightedMean, eq_div_iff hW.ne']
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    field_simp
  have habs : |y i - ivwEstimate v y| ≤ √D := by
    rw [hrep, abs_div, abs_of_pos hW, div_le_iff₀ hW]
    calc |∑ j, ivWeight v j * (y i - y j)| ≤ ∑ j, |ivWeight v j * (y i - y j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, ivWeight v j * √D := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_of_pos (ivWeight_pos hv j)]
          exact mul_le_mul_of_nonneg_left (Real.abs_le_sqrt (hD i j)) (ivWeight_pos hv j).le
      _ = √D * ∑ j, ivWeight v j := by rw [← Finset.sum_mul, mul_comm]
  calc (y i - ivwEstimate v y) ^ 2 = |y i - ivwEstimate v y| ^ 2 := (sq_abs _).symm
    _ ≤ √D ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = D := Real.sq_sqrt hD0

/-- The spread condition forces positive variances: `D ≥ 0` gives `v₋ > v₊ / k`, which with
`v₋ ≤ v₊` and `k ≥ 1` gives `v₋ > 0`. -/
theorem pos_of_spread {v : ι → ℝ} {y : ι → ℝ} {vmin vmax D : ℝ} (hmin : ∀ i, vmin ≤ v i)
    (hmax : ∀ i, v i ≤ vmax) (hD : ∀ i j, (y i - y j) ^ 2 ≤ D)
    (hcond : D < vmin - vmax / Fintype.card ι) (i : ι) : 0 < v i := by
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hD0 : 0 ≤ D := le_trans (sq_nonneg _) (hD i i)
  set q := vmax / Fintype.card ι
  have hq : vmax = q * (Fintype.card ι - 1) + q := by
    simp only [q]; field_simp; ring
  refine lt_of_lt_of_le ?_ (hmin i)
  by_contra hle0
  have hle : vmin ≤ 0 := not_lt.1 hle0
  have hq0 : q * (Fintype.card ι - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith [hmin i, hmax i]

/-- **A spread condition gives a negative restricted score**: let the `k` variances lie in
`[v₋, v₊]`, let `(yᵢ - yⱼ)² ≤ D` for all `i, j`, and let `D < v₋ - v₊ / k`. Then the restricted
score is negative at every `t ≥ 0`. -/
theorem restrictedScore_neg_of_spread {v : ι → ℝ} {y : ι → ℝ}
    {vmin vmax D : ℝ} (hmin : ∀ i, vmin ≤ v i) (hmax : ∀ i, v i ≤ vmax)
    (hD : ∀ i j, (y i - y j) ^ 2 ≤ D) (hcond : D < vmin - vmax / Fintype.card ι) {t : ℝ}
    (ht : 0 ≤ t) : restrictedScore v y t < 0 := by
  have hv := pos_of_spread hmin hmax hD hcond
  set u : ι → ℝ := fun i => v i + t
  have hu : ∀ i, 0 < u i := fun i => add_pos_of_pos_of_nonneg (hv i) ht
  set w := ivWeight u
  set W := ∑ i, w i
  set W2 := ∑ i, w i ^ 2
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hwpos : ∀ i, 0 < w i := ivWeight_pos hu
  have hW : 0 < W := sum_ivWeight_pos hu
  have hW2 : 0 < W2 := Finset.sum_pos (fun i _ => pow_pos (hwpos i) 2) Finset.univ_nonempty
  have hvmin : 0 < vmin + t := by
    have hD0 : 0 ≤ D := le_trans (sq_nonneg _) (hD (Classical.arbitrary ι) (Classical.arbitrary ι))
    have : 0 ≤ vmax / Fintype.card ι := div_nonneg
      ((hv (Classical.arbitrary ι)).le.trans (hmax _)) (by positivity)
    linarith
  have h1 : W2 * (vmin + t) ≤ W := by
    simp only [W2, W, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hwi : w i * (v i + t) = 1 := by
      simp only [w, ivWeight, u]; field_simp [(hu i).ne']; exact div_self (hu i).ne'
    have : w i * (vmin + t) ≤ 1 := by
      rw [← hwi]; exact mul_le_mul_of_nonneg_left (by linarith [hmin i]) (hwpos i).le
    nlinarith [hwpos i]
  have h2 : (Fintype.card ι : ℝ) ≤ (vmax + t) * W := by
    simp only [W, Finset.mul_sum]
    have : ∀ i, (1 : ℝ) ≤ (vmax + t) * w i := fun i => by
      have hwi : w i * (v i + t) = 1 := by
        simp only [w, ivWeight, u]; field_simp [(hu i).ne']; exact div_self (hu i).ne'
      nlinarith [hmax i, hwpos i]
    calc (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => this i
  have h3 : ∑ i, w i ^ 2 * (y i - ivwEstimate u y) ^ 2 ≤ D * W2 := by
    simp only [W2, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_comm D]
    exact mul_le_mul_of_nonneg_left (sq_sub_ivwEstimate_le hu hD i) (sq_nonneg _)
  have hkpos : (0 : ℝ) < Fintype.card ι := by linarith
  have h4 : W2 / W ≤ W2 * (vmax + t) / Fintype.card ι := by
    rw [div_le_div_iff₀ hW hkpos]
    nlinarith
  have h5 : W2 * (vmax + t) / Fintype.card ι ≤ W2 * (vmax / Fintype.card ι + t) := by
    have e : W2 * (vmax / Fintype.card ι + t) * Fintype.card ι =
        W2 * vmax + W2 * t * Fintype.card ι := by
      field_simp
    rw [div_le_iff₀ hkpos, e]
    nlinarith [mul_nonneg (mul_nonneg hW2.le ht) (sub_nonneg.2 hk)]
  have hslope : D * W2 < W - W2 / W := by
    have : D * W2 < W2 * (vmin + t) - W2 * (vmax / Fintype.card ι + t) := by
      nlinarith
    linarith
  have hscore : restrictedScore v y t =
      1 / 2 * (∑ i, w i ^ 2 * (y i - ivwEstimate u y) ^ 2 - (W - W2 / W)) := rfl
  rw [hscore]
  linarith

/-- **The spread condition makes `τ² = 0` the unique maximizer** of the restricted likelihood
on `[0, ∞)`: under the hypotheses of `restrictedScore_neg_of_spread`, `ℓ_R(t) < ℓ_R(0)` for every
`t > 0`. -/
theorem restrictedLogLik_lt_zero_of_spread {v : ι → ℝ} {y : ι → ℝ}
    {vmin vmax D : ℝ} (hmin : ∀ i, vmin ≤ v i) (hmax : ∀ i, v i ≤ vmax)
    (hD : ∀ i j, (y i - y j) ^ 2 ≤ D) (hcond : D < vmin - vmax / Fintype.card ι) {t : ℝ}
    (ht : 0 < t) : restrictedLogLik v y t < restrictedLogLik v y 0 :=
  restrictedLogLik_lt_zero_of_score_neg (pos_of_spread hmin hmax hD hcond) y
    (fun _t hs => restrictedScore_neg_of_spread hmin hmax hD hcond hs.le) ht

end MetaAnalysis

end CausalInference
