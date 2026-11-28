/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.HeterogeneityUnequalLikelihood
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Meta-analysis: locating the restricted maximum likelihood estimate with unequal variances

**Structure in the data.** The restricted log likelihood splits into a part free of the data
and Cochran's `Q` of the shifted variances (`restrictedLogLik_eq_zero_sub_cochranQ`):

`ℓ_R(t; y) = ℓ_R(t; 0) - ½ Q(t; y)`,  `ℓ_R(t; 0) = -½ log(∏ᵢ (vᵢ + t) ∑ᵢ 1 / (vᵢ + t))`

(`restrictedLogLik_zero_eq`). `Q` is quadratic in the data, `Q(t; s y) = s² Q(t; y)`
(`cochranQ_smul`), and nonincreasing in `t` (`cochranQ_le_of_le`): the weights `1 / (vᵢ + t)`
decrease and `Q` is the minimal weighted sum of squares. The restricted score is affine in `s²`
(`restrictedScore_smul`). On `[a, ∞)` the restricted log likelihood attains its maximum
(`exists_isMaxOn_Ici_restrictedLogLik`).

**The two peak instance of `restrictedLogLik_twoPeak`.** For `v = (1/10, 1/10, 10)` the data
free part is `-½ log P(t)` with `P(t) = (1/10 + t)² + 2 (1/10 + t)(10 + t)`
(`restrictedLogLik_twoPeakVar_zero`), increasing in `t ≥ 0`. So on `[a, b] ⊆ [0, ∞)`

`ℓ_R(t; y) ≤ -½ log P(a) - ½ Q(b; y)`  (`restrictedLogLik_twoPeakVar_le`).

With `y = (0, 1/2, 10)` six such bounds, on `[0, 1/5]`, `[1/5, 1]`, `[1, 2]`, `[50, 65]`,
`[65, 90]` and `[90, ∞)`, are all below `ℓ_R(20)`; the logarithms are bounded through
`log x = n log 2 + log(x / 2ⁿ)` and `1 - 1/u ≤ log u ≤ u - 1`. Hence
(`restrictedLogLik_twoPeak_lt_twenty`, `isMaxOn_restrictedLogLik_twoPeak_mem_Ioo`) **every
maximizer of the restricted likelihood of the two peak instance on `[0, ∞)` lies in `(2, 50)`**: the
global maximum is the far local maximum, and the local maximizer in `(1/100, 1/10)` of
`restrictedLogLik_twoPeak` is not a maximizer on `[0, ∞)`.

**A negative score at `0` does not make `0` the estimate.** A maximizer at `0` has restricted
score `≤ 0` at `0` (`restrictedLogLik_firstOrder`). The converse fails: for `v = (1/10, 1/10, 10)`
and `y = (0, 0, 10)` the restricted score at `0` is `-58340/13467 < 0`, yet `ℓ_R(0) < ℓ_R(20)`, so
`0` is not a maximizer and every maximizer is positive (`restrictedScore_flatPeakEst_zero_neg`,
`not_forall_isMaxOn_zero_of_restrictedScore_nonpos`). The first order condition at the boundary
is necessary, not sufficient.

## Main definitions

* `twoPeakDet`, `flatPeakEst`.

## Main results

* `cochranQ_smul`, `restrictedLogLik_eq_zero_sub_cochranQ`, `restrictedScore_smul`,
  `cochranQ_le_of_le`, `restrictedLogLik_zero_eq`, `exists_isMaxOn_Ici_restrictedLogLik`.
* `restrictedLogLik_twoPeakVar_le`, `restrictedLogLik_twoPeak_lt_twenty`,
  `isMaxOn_restrictedLogLik_twoPeak_mem_Ioo`.
* `restrictedScore_flatPeakEst_zero_neg`, `not_forall_isMaxOn_zero_of_restrictedScore_nonpos`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Filter Topology Set PopulationAdjustment

/-! ### Structure of the restricted log likelihood in the data -/

section General

variable {ι : Type*} [Fintype ι]

/-- The pooled estimate is linear in the data: `θ̂(s y) = s θ̂(y)`. -/
theorem ivwEstimate_smul (v y : ι → ℝ) (s : ℝ) : ivwEstimate v (s • y) = s * ivwEstimate v y := by
  simp only [ivwEstimate, weightedMean, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Cochran's `Q` is quadratic in the data**: `Q(s y) = s² Q(y)`. -/
theorem cochranQ_smul (v y : ι → ℝ) (s : ℝ) : cochranQ v (s • y) = s ^ 2 * cochranQ v y := by
  simp only [cochranQ, ivwEstimate_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `Q` of the zero data vector is `0`. -/
theorem cochranQ_zero (v : ι → ℝ) : cochranQ v 0 = 0 := by
  simpa using cochranQ_smul v 0 0

/-- **The data free part of the restricted log likelihood**:
`ℓ_R(t; y) = ℓ_R(t; 0) - ½ Q(t; y)`, with `Q(t; y)` Cochran's `Q` with the weights
`1 / (vᵢ + t)`. -/
theorem restrictedLogLik_eq_zero_sub_cochranQ (v y : ι → ℝ) (t : ℝ) :
    restrictedLogLik v y t = restrictedLogLik v 0 t - 1 / 2 * cochranQ (fun i => v i + t) y := by
  simp only [restrictedLogLik, cochranQ_zero]
  ring

/-- **The restricted score is affine in the square of a data scale**:
`ℓ_R'(t; s y) = s² ℓ_R'(t; y) + (1 - s²) ℓ_R'(t; 0)`. -/
theorem restrictedScore_smul (v y : ι → ℝ) (s t : ℝ) :
    restrictedScore v (s • y) t =
      s ^ 2 * restrictedScore v y t + (1 - s ^ 2) * restrictedScore v 0 t := by
  have h0 : ivwEstimate (fun i => v i + t) (0 : ι → ℝ) = 0 := by
    simpa using ivwEstimate_smul (fun i => v i + t) 0 0
  simp only [restrictedScore, ivwEstimate_smul, h0, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    sub_zero]
  have key : ∑ i, ivWeight (fun i => v i + t) i ^ 2 *
      (s * y i - s * ivwEstimate (fun i => v i + t) y) ^ 2 = s ^ 2 *
        ∑ i, ivWeight (fun i => v i + t) i ^ 2 * (y i - ivwEstimate (fun i => v i + t) y) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Finset.sum_const_zero]
  ring

/-- **`Q` is nonincreasing in the between study variance**: for `a ≤ b` with all `vᵢ + a > 0`,
`Q(b) ≤ Q(a)`. Proof: `Q(b) ≤ ∑ wᵢ(b) (yᵢ - θ̂(a))² ≤ ∑ wᵢ(a) (yᵢ - θ̂(a))² = Q(a)`. -/
theorem cochranQ_le_of_le [Nonempty ι] {v : ι → ℝ} {a b : ℝ} (ha : ∀ i, 0 < v i + a)
    (hab : a ≤ b) (y : ι → ℝ) :
    cochranQ (fun i => v i + b) y ≤ cochranQ (fun i => v i + a) y := by
  have hb : ∀ i, 0 < v i + b := fun i => by linarith [ha i]
  calc cochranQ (fun i => v i + b) y
      ≤ ∑ i, ivWeight (fun i => v i + b) i * (y i - ivwEstimate (fun i => v i + a) y) ^ 2 :=
        cochranQ_le hb y _
    _ ≤ ∑ i, ivWeight (fun i => v i + a) i * (y i - ivwEstimate (fun i => v i + a) y) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          (one_div_le_one_div_of_le (ha i) (by linarith)) (sq_nonneg _)
    _ = cochranQ (fun i => v i + a) y := rfl

/-- **The data free part as one logarithm**: for all `vᵢ + t > 0`,
`ℓ_R(t; 0) = -½ log(∏ᵢ (vᵢ + t) ∑ᵢ 1 / (vᵢ + t))`. -/
theorem restrictedLogLik_zero_eq [Nonempty ι] {v : ι → ℝ} {t : ℝ} (ht : ∀ i, 0 < v i + t) :
    restrictedLogLik v 0 t =
      -(1 / 2) * Real.log ((∏ i, (v i + t)) * ∑ i, ivWeight (fun i => v i + t) i) := by
  have hW := sum_ivWeight_pos ht
  have hP : (∏ i, (v i + t)) ≠ 0 := (Finset.prod_pos fun i _ => ht i).ne'
  rw [Real.log_mul hP hW.ne', Real.log_prod fun i _ => (ht i).ne', restrictedLogLik,
    cochranQ_zero]
  ring

/-- **The maximum on a half line**: for `vᵢ > 0`, at least two studies and `a ≥ 0`, the
restricted log likelihood attains its maximum on `[a, ∞)`. -/
theorem exists_isMaxOn_Ici_restrictedLogLik {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hk : 2 ≤ Fintype.card ι) (y : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∃ t, a ≤ t ∧ IsMaxOn (restrictedLogLik v y) (Ici a) t := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hcont : ContinuousOn (restrictedLogLik v y) (Ici a) := fun t ht =>
    (hasDerivAt_restrictedLogLik y fun i => by
      linarith [hv i, ha.trans (mem_Ici.1 ht)]).continuousAt.continuousWithinAt
  have htend := tendsto_restrictedLogLik_atTop hv hk y
  have hc : ∀ᶠ x in Filter.cocompact ℝ ⊓ 𝓟 (Ici a),
      restrictedLogLik v y x ≤ restrictedLogLik v y a := by
    rw [cocompact_eq_atBot_atTop, inf_sup_right, eventually_sup]
    refine ⟨?_, ?_⟩
    · refine eventually_inf_principal.2 ?_
      filter_upwards [eventually_lt_atBot a] with x hx hx'
      exact absurd (mem_Ici.1 hx') (not_le.2 hx)
    · refine eventually_inf_principal.2 ?_
      filter_upwards [htend.eventually (eventually_le_atBot (restrictedLogLik v y a))] with x hx _
      exact hx
  obtain ⟨t, ht, hmax⟩ := hcont.exists_isMaxOn' isClosed_Ici (mem_Ici.2 le_rfl) hc
  exact ⟨t, ht, hmax⟩

end General

/-! ### Rational bounds for logarithms -/

/-- `log x ≤ n log 2 + (x / 2ⁿ - 1)` for `x > 0`. -/
theorem log_le_nat_mul_log_two_add {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.log x ≤ n * Real.log 2 + (x / 2 ^ n - 1) := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx' : x = 2 ^ n * (x / 2 ^ n) := by field_simp
  have hl := Real.log_le_sub_one_of_pos (div_pos hx h2)
  rw [hx', Real.log_mul h2.ne' (div_pos hx h2).ne', Real.log_pow]
  rw [← hx']
  linarith

/-- `n log 2 + (1 - 2ⁿ / x) ≤ log x` for `x > 0`. -/
theorem nat_mul_log_two_add_le_log {x : ℝ} (hx : 0 < x) (n : ℕ) :
    n * Real.log 2 + (1 - 2 ^ n / x) ≤ Real.log x := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hl := Real.log_le_sub_one_of_pos (div_pos h2 hx)
  rw [Real.log_div h2.ne' hx.ne', Real.log_pow] at hl
  linarith

/-! ### The two peak instance -/

/-- The polynomial `P(t) = (1/10 + t)² + 2 (1/10 + t)(10 + t)`, equal to
`∏ᵢ (vᵢ + t) ∑ᵢ 1 / (vᵢ + t)` for the variances `(1/10, 1/10, 10)`. -/
noncomputable def twoPeakDet (t : ℝ) : ℝ := (1 / 10 + t) ^ 2 + 2 * (1 / 10 + t) * (10 + t)

/-- `P(t) > 0` for `t ≥ 0`. -/
theorem twoPeakDet_pos {t : ℝ} (ht : 0 ≤ t) : 0 < twoPeakDet t := by
  unfold twoPeakDet; positivity

/-- `P` is nondecreasing on `[0, ∞)`. -/
theorem twoPeakDet_le {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) : twoPeakDet a ≤ twoPeakDet t := by
  unfold twoPeakDet; nlinarith

/-- For the variances `(1/10, 1/10, 10)` the data free part of the restricted log likelihood is
`-½ log P(t)`. -/
theorem restrictedLogLik_twoPeakVar_zero {t : ℝ} (ht : 0 ≤ t) :
    restrictedLogLik twoPeakVar 0 t = -(1 / 2) * Real.log (twoPeakDet t) := by
  rw [restrictedLogLik_zero_eq (twoPeakVar_add_pos ht)]
  congr 2
  have h1 : (0 : ℝ) < 1 / 10 + t := by linarith
  have h2 : (0 : ℝ) < 10 + t := by linarith
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, ivWeight, twoPeakVar, twoPeakDet,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  field_simp
  ring

/-- **A bound on an interval**: for the variances `(1/10, 1/10, 10)`, any data and
`0 ≤ a ≤ t ≤ b`, `ℓ_R(t) ≤ -½ log P(a) - ½ Q(b)`. -/
theorem restrictedLogLik_twoPeakVar_le (y : Fin 3 → ℝ) {a b t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t)
    (htb : t ≤ b) : restrictedLogLik twoPeakVar y t ≤
      -(1 / 2) * Real.log (twoPeakDet a) - 1 / 2 * cochranQ (fun i => twoPeakVar i + b) y := by
  have ht : 0 ≤ t := ha.trans hat
  rw [restrictedLogLik_eq_zero_sub_cochranQ, restrictedLogLik_twoPeakVar_zero ht]
  have hlog := Real.log_le_log (twoPeakDet_pos ha) (twoPeakDet_le ha hat)
  have hQ := cochranQ_le_of_le (twoPeakVar_add_pos ht) htb y
  linarith

/-- The value at `t ≥ 0`: `ℓ_R(t) = -½ log P(t) - ½ Q(t)`. -/
theorem restrictedLogLik_twoPeakVar_eq (y : Fin 3 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    restrictedLogLik twoPeakVar y t =
      -(1 / 2) * Real.log (twoPeakDet t) - 1 / 2 * cochranQ (fun i => twoPeakVar i + t) y := by
  rw [restrictedLogLik_eq_zero_sub_cochranQ, restrictedLogLik_twoPeakVar_zero ht]

/-- **Comparison of an interval with a point, left of the point**: for the variances
`(1/10, 1/10, 10)`, if `n log 2 + (P(r) / P(a) / 2ⁿ - 1) < Q(b) - Q(r)` (with the upper bound
`0.6931471808` of `log 2`), then `ℓ_R(t) < ℓ_R(r)` on `[a, b]`. -/
theorem restrictedLogLik_twoPeakVar_lt_left (y : Fin 3 → ℝ) {a b r : ℝ} (ha : 0 ≤ a)
    (hr : 0 ≤ r) (n : ℕ)
    (h : n * 0.6931471808 + (twoPeakDet r / twoPeakDet a / 2 ^ n - 1) <
      cochranQ (fun i => twoPeakVar i + b) y - cochranQ (fun i => twoPeakVar i + r) y) :
    ∀ t ∈ Icc a b, restrictedLogLik twoPeakVar y t < restrictedLogLik twoPeakVar y r := by
  intro t ht
  have hle := restrictedLogLik_twoPeakVar_le y ha ht.1 ht.2
  rw [restrictedLogLik_twoPeakVar_eq y hr]
  have hPa := twoPeakDet_pos ha
  have hPr := twoPeakDet_pos hr
  have hl := log_le_nat_mul_log_two_add (div_pos hPr hPa) n
  rw [Real.log_div hPr.ne' hPa.ne'] at hl
  have h2 : (n : ℝ) * Real.log 2 ≤ n * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (Nat.cast_nonneg n)
  linarith

/-- **Comparison of an interval with a point, right of the point**: for the variances
`(1/10, 1/10, 10)`, if `Q(r) - Q(b) < n log 2 + (1 - 2ⁿ / (P(a) / P(r)))` (with the lower bound
`0.6931471803` of `log 2`), then `ℓ_R(t) < ℓ_R(r)` on `[a, b]`. -/
theorem restrictedLogLik_twoPeakVar_lt_right (y : Fin 3 → ℝ) {a b r : ℝ} (ha : 0 ≤ a)
    (hr : 0 ≤ r) (n : ℕ)
    (h : cochranQ (fun i => twoPeakVar i + r) y - cochranQ (fun i => twoPeakVar i + b) y <
      n * 0.6931471803 + (1 - 2 ^ n / (twoPeakDet a / twoPeakDet r))) :
    ∀ t ∈ Icc a b, restrictedLogLik twoPeakVar y t < restrictedLogLik twoPeakVar y r := by
  intro t ht
  have hle := restrictedLogLik_twoPeakVar_le y ha ht.1 ht.2
  rw [restrictedLogLik_twoPeakVar_eq y hr]
  have hPa := twoPeakDet_pos ha
  have hPr := twoPeakDet_pos hr
  have hl := nat_mul_log_two_add_le_log (div_pos hPa hPr) n
  rw [Real.log_div hPa.ne' hPr.ne'] at hl
  have h2 : (n : ℝ) * 0.6931471803 ≤ n * Real.log 2 :=
    mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg n)
  linarith

/-- **Comparison of a half line with a point**: for the variances `(1/10, 1/10, 10)`, if
`Q(r) < n log 2 + (1 - 2ⁿ / (P(a) / P(r)))`, then `ℓ_R(t) < ℓ_R(r)` for every `t ≥ a`. -/
theorem restrictedLogLik_twoPeakVar_lt_tail (y : Fin 3 → ℝ) {a r : ℝ} (ha : 0 ≤ a)
    (hr : 0 ≤ r) (n : ℕ)
    (h : cochranQ (fun i => twoPeakVar i + r) y <
      n * 0.6931471803 + (1 - 2 ^ n / (twoPeakDet a / twoPeakDet r))) :
    ∀ t, a ≤ t → restrictedLogLik twoPeakVar y t < restrictedLogLik twoPeakVar y r := by
  intro t ht
  have hQ := cochranQ_nonneg (twoPeakVar_add_pos (ha.trans ht)) y
  exact restrictedLogLik_twoPeakVar_lt_right y ha hr n (by linarith) t ⟨ht, le_rfl⟩

/-- The values of Cochran's `Q` of the two peak instance used in the comparisons:
`Q(1/5) = 1325/138`, `Q(1) = 1285/154`, `Q(2) = 8945/1218`, `Q(20) = 85145/35778`,
`Q(65) = 275645/311178`, `Q(90) = 1144435/1742534`. -/
theorem cochranQ_twoPeak_values :
    cochranQ (fun i => twoPeakVar i + 1 / 5) twoPeakEst = 1325 / 138 ∧
      cochranQ (fun i => twoPeakVar i + 1) twoPeakEst = 1285 / 154 ∧
      cochranQ (fun i => twoPeakVar i + 2) twoPeakEst = 8945 / 1218 ∧
      cochranQ (fun i => twoPeakVar i + 20) twoPeakEst = 85145 / 35778 ∧
      cochranQ (fun i => twoPeakVar i + 65) twoPeakEst = 275645 / 311178 ∧
      cochranQ (fun i => twoPeakVar i + 90) twoPeakEst = 1144435 / 1742534 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [cochranQ, ivwEstimate, weightedMean, ivWeight, Fin.sum_univ_three, twoPeakVar,
      twoPeakEst, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    norm_num

/-- **The far local maximum is the global one**: for `v = (1/10, 1/10, 10)` and
`y = (0, 1/2, 10)`, `ℓ_R(t) < ℓ_R(20)` for every `t ∈ [0, 2] ∪ [50, ∞)`. -/
theorem restrictedLogLik_twoPeak_lt_twenty {t : ℝ} (ht : 0 ≤ t) (h : t ≤ 2 ∨ 50 ≤ t) :
    restrictedLogLik twoPeakVar twoPeakEst t < restrictedLogLik twoPeakVar twoPeakEst 20 := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := cochranQ_twoPeak_values
  have h20 : (0 : ℝ) ≤ 20 := by norm_num
  rcases h with h | h
  · rcases le_or_gt t (1 / 5) with h1 | h1
    · refine restrictedLogLik_twoPeakVar_lt_left twoPeakEst le_rfl h20 10 ?_ t ⟨ht, h1⟩
      rw [q1, q4]; norm_num [twoPeakDet]
    rcases le_or_gt t 1 with h2 | h2
    · refine restrictedLogLik_twoPeakVar_lt_left twoPeakEst (by norm_num) h20 8 ?_ t
        ⟨h1.le, h2⟩
      rw [q2, q4]; norm_num [twoPeakDet]
    · refine restrictedLogLik_twoPeakVar_lt_left twoPeakEst (by norm_num) h20 6 ?_ t ⟨h2.le, h⟩
      rw [q3, q4]; norm_num [twoPeakDet]
  · rcases le_or_gt t 65 with h1 | h1
    · refine restrictedLogLik_twoPeakVar_lt_right twoPeakEst (by norm_num) h20 2 ?_ t ⟨h, h1⟩
      rw [q4, q5]; norm_num [twoPeakDet]
    rcases le_or_gt t 90 with h2 | h2
    · refine restrictedLogLik_twoPeakVar_lt_right twoPeakEst (by norm_num) h20 3 ?_ t
        ⟨h1.le, h2⟩
      rw [q4, q6]; norm_num [twoPeakDet]
    · refine restrictedLogLik_twoPeakVar_lt_tail twoPeakEst (by norm_num) h20 4 ?_ t h2.le
      rw [q4]; norm_num [twoPeakDet]

/-- **Where the restricted maximum likelihood estimate of the two peak instance lies**: for
`v = (1/10, 1/10, 10)` and `y = (0, 1/2, 10)` a maximizer of `ℓ_R` on `[0, ∞)` exists, and every
maximizer lies in `(2, 50)` and is a zero of the restricted score. In particular the local
maximizer in `(1/100, 1/10)` of `restrictedLogLik_twoPeak` is not a maximizer on `[0, ∞)`. -/
theorem isMaxOn_restrictedLogLik_twoPeak_mem_Ioo :
    (∃ t, 0 ≤ t ∧ IsMaxOn (restrictedLogLik twoPeakVar twoPeakEst) (Ici 0) t) ∧
      ∀ t, 0 ≤ t → IsMaxOn (restrictedLogLik twoPeakVar twoPeakEst) (Ici 0) t →
        t ∈ Ioo 2 50 ∧ restrictedScore twoPeakVar twoPeakEst t = 0 := by
  have hv : ∀ i, 0 < twoPeakVar i := fun i => by simpa using twoPeakVar_add_pos le_rfl i
  obtain ⟨t0, ht0, hmax0, -, -⟩ := exists_isMaxOn_restrictedLogLik hv (by simp) twoPeakEst
  refine ⟨⟨t0, ht0, hmax0⟩, fun t ht hmax => ?_⟩
  have hle := isMaxOn_iff.1 hmax 20 (by norm_num)
  have hmem : t ∈ Ioo 2 50 := by
    by_contra hn
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hn
    exact absurd hle (not_le.2 (restrictedLogLik_twoPeak_lt_twenty ht hn))
  refine ⟨hmem, ?_⟩
  exact (hmax.isLocalMax (Ici_mem_nhds (by linarith [hmem.1]))).hasDerivAt_eq_zero
    (hasDerivAt_restrictedLogLik twoPeakEst (twoPeakVar_add_pos ht))

/-! ### A negative score at the boundary does not make `0` the estimate -/

/-- The estimates `(0, 0, 10)`: two precise studies that agree and one imprecise study far
away. -/
noncomputable def flatPeakEst : Fin 3 → ℝ := ![0, 0, 10]

/-- **A negative restricted score at `0` with a positive estimate**: for `v = (1/10, 1/10, 10)`
and `y = (0, 0, 10)`, the restricted score at `0` is `-58340/13467 < 0`, yet `ℓ_R(0) < ℓ_R(20)`,
so `0` is not a maximizer of `ℓ_R` on `[0, ∞)`; a maximizer exists, and every maximizer is
positive and a zero of the restricted score. -/
theorem restrictedScore_flatPeakEst_zero_neg :
    restrictedScore twoPeakVar flatPeakEst 0 = -58340 / 13467 ∧
      restrictedLogLik twoPeakVar flatPeakEst 0 < restrictedLogLik twoPeakVar flatPeakEst 20 ∧
      ¬ IsMaxOn (restrictedLogLik twoPeakVar flatPeakEst) (Ici 0) 0 ∧
      (∃ t, 0 ≤ t ∧ IsMaxOn (restrictedLogLik twoPeakVar flatPeakEst) (Ici 0) t) ∧
      ∀ t, 0 ≤ t → IsMaxOn (restrictedLogLik twoPeakVar flatPeakEst) (Ici 0) t →
        0 < t ∧ restrictedScore twoPeakVar flatPeakEst t = 0 := by
  have hv : ∀ i, 0 < twoPeakVar i := fun i => by simpa using twoPeakVar_add_pos le_rfl i
  have hs : restrictedScore twoPeakVar flatPeakEst 0 = -58340 / 13467 := by
    simp only [restrictedScore, cochranQSlope, ivwEstimate, weightedMean, ivWeight,
      Fin.sum_univ_three, twoPeakVar, flatPeakEst, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    norm_num
  have hQ : cochranQ (fun i => twoPeakVar i + 0) flatPeakEst = 2000 / 201 ∧
      cochranQ (fun i => twoPeakVar i + 20) flatPeakEst = 2000 / 801 := by
    refine ⟨?_, ?_⟩ <;>
    · simp only [cochranQ, ivwEstimate, weightedMean, ivWeight, Fin.sum_univ_three, twoPeakVar,
        flatPeakEst, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      norm_num
  have hlt : restrictedLogLik twoPeakVar flatPeakEst 0 <
      restrictedLogLik twoPeakVar flatPeakEst 20 := by
    refine restrictedLogLik_twoPeakVar_lt_left flatPeakEst le_rfl (by norm_num) 10 ?_ 0
      ⟨le_rfl, le_rfl⟩
    rw [hQ.1, hQ.2]; norm_num [twoPeakDet]
  have hnot : ¬ IsMaxOn (restrictedLogLik twoPeakVar flatPeakEst) (Ici 0) 0 := fun hmax =>
    absurd (isMaxOn_iff.1 hmax 20 (by norm_num)) (not_le.2 hlt)
  obtain ⟨t0, ht0, hmax0, -, -⟩ := exists_isMaxOn_restrictedLogLik hv (by simp) flatPeakEst
  refine ⟨hs, hlt, hnot, ⟨t0, ht0, hmax0⟩, fun t ht hmax => ?_⟩
  have htpos : 0 < t := lt_of_le_of_ne ht fun h => hnot (h ▸ hmax)
  exact ⟨htpos, (hmax.isLocalMax (Ici_mem_nhds htpos)).hasDerivAt_eq_zero
    (hasDerivAt_restrictedLogLik flatPeakEst (twoPeakVar_add_pos ht))⟩

/-- **The boundary first order condition is not sufficient**: it is false that, for all positive
within study variances and all data of three studies, a restricted score `≤ 0` at `0` makes `0` a
maximizer of the restricted likelihood on `[0, ∞)`. Counterexample:
`restrictedScore_flatPeakEst_zero_neg`. -/
theorem not_forall_isMaxOn_zero_of_restrictedScore_nonpos :
    ¬ ∀ v y : Fin 3 → ℝ, (∀ i, 0 < v i) → restrictedScore v y 0 ≤ 0 →
      IsMaxOn (restrictedLogLik v y) (Ici 0) 0 := by
  intro h
  obtain ⟨hs, -, hnot, -⟩ := restrictedScore_flatPeakEst_zero_neg
  exact hnot (h twoPeakVar flatPeakEst (fun i => by simpa using twoPeakVar_add_pos le_rfl i)
    (by rw [hs]; norm_num))

end MetaAnalysis

end CausalInference
