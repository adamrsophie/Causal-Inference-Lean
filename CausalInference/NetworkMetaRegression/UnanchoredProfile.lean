/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredIdentification
public import CausalInference.NetworkMetaAnalysis.Deviance

/-!
# Profile likelihood of the aggregate intercept

For a fixed slope `β`, the aggregate data of the comparator arm enter the likelihood only
through the arm mean `θ(s) = ∫ g⁻¹(s + xᵀβ) dF_B` as a function of the intercept `s`. If `ℓ` is
the log likelihood of the reported summary as a function of the mean, the profile over `s` is
`s ↦ ℓ(θ(s))`. This file shows that the profile is maximized exactly at the calibrated shift
`c(β, θ̂)` of the maximizer `θ̂` of `ℓ`: maximizing over the intercept is calibration of the
mean to `θ̂`.

* **The general statement** (`isMaxOn_shiftMean_calibratedShift`): if `g⁻¹` is continuous and
  strictly increasing, the integrands are integrable under the probability law `F_B`, and `θ̂` in
  the range of `g⁻¹` is the unique maximizer of `ℓ` on that range, then `c(β, θ̂)` is the unique
  maximizer of `s ↦ ℓ(θ(s))` on `ℝ`. Continuity enters only through the range of `θ`
  (`range_shiftMean`); strict monotonicity gives uniqueness. No concavity of `ℓ` is used.
* **Binomial summary** (`isMaxOn_binomialLogLik_shiftMean`): for `y` events out of `n` with
  `0 < y < n` and an inverse link with range `(0, 1)`, the maximizer is `c(β, y / n)`; the
  binomial maximizer `y / n` is `binomialLogLik_le_saturated`.
* **Normal summary** (`isMaxOn_normalLogLik_shiftMean`): for a reported mean `ȳ` in the range of
  `g⁻¹` with sampling variance `v > 0`, the log likelihood `-(ȳ - θ)² / (2v)` gives the
  maximizer `c(β, ȳ)`.

## Main definitions

None: the file proves facts about the profile likelihood of the calibrated shift.

## Main results

* `isMaxOn_shiftMean_calibratedShift`, `isMaxOn_binomialLogLik_shiftMean`,
  `isMaxOn_normalLogLik_shiftMean`.
* `profile_binomial_instance`, `profile_normal_instance`.

## References

* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory NetworkMetaAnalysis

variable {p : ℕ} {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F] {ginv : ℝ → ℝ}

/-- **The profile over the intercept is maximized at the calibrated shift.** Let `g⁻¹` be
continuous and strictly increasing and `g⁻¹(s + xᵀβ)` integrable under the probability law `F`
for every `s`. If `θ̂` lies in the range of `g⁻¹`, maximizes `ℓ` on that range, and is the only
point of the range where `ℓ` takes the value `ℓ(θ̂)`, then the calibrated shift `c(β, θ̂)`
maximizes `s ↦ ℓ(∫ g⁻¹(s + xᵀβ) dF)` on `ℝ`, and it is the only maximizer. -/
theorem isMaxOn_shiftMean_calibratedShift (hmono : StrictMono ginv) (hcont : Continuous ginv)
    {β : Fin p → ℝ} (hint : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ β)) F) {ℓ : ℝ → ℝ}
    {θhat : ℝ} (hθ : θhat ∈ Set.range ginv) (hmax : IsMaxOn ℓ (Set.range ginv) θhat)
    (huniq : ∀ θ ∈ Set.range ginv, ℓ θ = ℓ θhat → θ = θhat) :
    IsMaxOn (fun s => ℓ (shiftMean F ginv (fun x => x ⬝ᵥ β) s)) Set.univ
        (calibratedShift F ginv β θhat) ∧
      ∀ s, ℓ (shiftMean F ginv (fun x => x ⬝ᵥ β) s) =
          ℓ (shiftMean F ginv (fun x => x ⬝ᵥ β) (calibratedShift F ginv β θhat)) →
        s = calibratedShift F ginv β θhat := by
  have hdot : Measurable fun x : Fin p → ℝ => x ⬝ᵥ β :=
    (by unfold dotProduct; fun_prop : Continuous fun x : Fin p → ℝ => x ⬝ᵥ β).measurable
  have hrange := range_shiftMean hmono hcont hdot hint
  have hex : ∃ c, shiftMean F ginv (fun x => x ⬝ᵥ β) c = θhat := by
    rw [← hrange] at hθ; exact hθ
  have hcal := shiftMean_calibratedShift hex
  have hmem : ∀ s, shiftMean F ginv (fun x => x ⬝ᵥ β) s ∈ Set.range ginv := fun s => by
    rw [← hrange]; exact ⟨s, rfl⟩
  refine ⟨fun s _ => ?_, fun s hs => ?_⟩
  · simp only [Set.mem_ofPred_eq, hcal]
    exact hmax (hmem s)
  · rw [hcal] at hs
    have := huniq _ (hmem s) hs
    exact (shiftMean_strictMono hmono hint).injective (this.trans hcal.symm)

/-- **Binomial summary.** Let `g⁻¹` be continuous and strictly increasing with range `(0, 1)`,
and let the aggregate study report `y` events out of `n` with `0 < y < n`. For every slope `β`
with integrable integrands, the intercept `c(β, y / n)` is the unique maximizer of the binomial
log likelihood `s ↦ y log θ(s) + (n - y) log (1 - θ(s))` of the arm mean
`θ(s) = ∫ g⁻¹(s + xᵀβ) dF`. -/
theorem isMaxOn_binomialLogLik_shiftMean (hmono : StrictMono ginv) (hcont : Continuous ginv)
    (hrange : Set.range ginv = Set.Ioo 0 1) {β : Fin p → ℝ}
    (hint : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ β)) F) {n y : ℝ} (hy0 : 0 < y)
    (hyn : y < n) :
    IsMaxOn (fun s => binomialLogLik n y (shiftMean F ginv (fun x => x ⬝ᵥ β) s)) Set.univ
        (calibratedShift F ginv β (y / n)) ∧
      ∀ s, binomialLogLik n y (shiftMean F ginv (fun x => x ⬝ᵥ β) s) =
          binomialLogLik n y
            (shiftMean F ginv (fun x => x ⬝ᵥ β) (calibratedShift F ginv β (y / n))) →
        s = calibratedShift F ginv β (y / n) := by
  have hn : 0 < n := hy0.trans hyn
  refine isMaxOn_shiftMean_calibratedShift hmono hcont hint ?_ ?_ ?_
  · rw [hrange]
    exact ⟨div_pos hy0 hn, (div_lt_one hn).2 hyn⟩
  · intro q hq
    rw [hrange] at hq
    exact (binomialLogLik_le_saturated hn hy0.le hyn.le hq.1 hq.2).1
  · intro q hq h
    rw [hrange] at hq
    exact (binomialLogLik_le_saturated hn hy0.le hyn.le hq.1 hq.2).2.1 h

/-- **Normal summary.** Let `g⁻¹` be continuous and strictly increasing, and let the aggregate
study report a mean `ȳ` in the range of `g⁻¹` with sampling variance `v > 0`. For every slope
`β` with integrable integrands, the intercept `c(β, ȳ)` is the unique maximizer of the normal log
likelihood `s ↦ -(ȳ - θ(s))² / (2v)` of the arm mean `θ(s) = ∫ g⁻¹(s + xᵀβ) dF`. -/
theorem isMaxOn_normalLogLik_shiftMean (hmono : StrictMono ginv) (hcont : Continuous ginv)
    {β : Fin p → ℝ} (hint : ∀ s, Integrable (fun x => ginv (s + x ⬝ᵥ β)) F) {ybar v : ℝ}
    (hy : ybar ∈ Set.range ginv) (hv : 0 < v) :
    IsMaxOn (fun s => -(ybar - shiftMean F ginv (fun x => x ⬝ᵥ β) s) ^ 2 / (2 * v)) Set.univ
        (calibratedShift F ginv β ybar) ∧
      ∀ s, -(ybar - shiftMean F ginv (fun x => x ⬝ᵥ β) s) ^ 2 / (2 * v) =
          -(ybar - shiftMean F ginv (fun x => x ⬝ᵥ β) (calibratedShift F ginv β ybar)) ^ 2 /
            (2 * v) →
        s = calibratedShift F ginv β ybar := by
  refine isMaxOn_shiftMean_calibratedShift (ℓ := fun θ => -(ybar - θ) ^ 2 / (2 * v)) hmono hcont
    hint hy (fun θ _ => ?_) (fun θ _ h => ?_)
  · simp only [Set.mem_ofPred_eq, sub_self]
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [sq_nonneg (ybar - θ)]
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero,
      zero_div] at h
    have h2 : (ybar - θ) ^ 2 = 0 := by
      rcases div_eq_zero_iff.1 h with h3 | h3
      · linarith
      · exact absurd h3 (by positivity)
    linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h2]

/-! ### Instances -/

omit [IsProbabilityMeasure F] in
/-- With slope `0` the shift mean of a probability law is `g⁻¹(s)`. -/
theorem shiftMean_zero_slope (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F] (ginv : ℝ → ℝ)
    (s : ℝ) : shiftMean F ginv (fun x => x ⬝ᵥ (0 : Fin p → ℝ)) s = ginv s := by
  simp [shiftMean]

/-- `σ(-log 3) = 1/4`. -/
theorem sigmoid_neg_log_three : Real.sigmoid (-Real.log 3) = 1 / 4 := by
  rw [Real.sigmoid_def, neg_neg, Real.exp_log (by norm_num)]
  norm_num

/-- **Instance of the binomial profile.** The logistic link, `F_B = binaryLaw (1/2)`, slope `0`,
`y = 1` event out of `n = 4`: the profile over the intercept is maximized exactly at
`c(0, 1/4) = -log 3`, where the arm mean is `σ(-log 3) = 1/4`. -/
theorem profile_binomial_instance :
    calibratedShift (binaryLaw (1 / 2)) Real.sigmoid 0 (1 / 4) = -Real.log 3 ∧
      IsMaxOn (fun s => binomialLogLik 4 1
          (shiftMean (binaryLaw (1 / 2)) Real.sigmoid (fun x => x ⬝ᵥ (0 : Fin 1 → ℝ)) s))
        Set.univ (-Real.log 3) ∧
      ∀ s, binomialLogLik 4 1
          (shiftMean (binaryLaw (1 / 2)) Real.sigmoid (fun x => x ⬝ᵥ (0 : Fin 1 → ℝ)) s) =
          binomialLogLik 4 1 (shiftMean (binaryLaw (1 / 2)) Real.sigmoid
            (fun x => x ⬝ᵥ (0 : Fin 1 → ℝ)) (-Real.log 3)) → s = -Real.log 3 := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have hc : calibratedShift (binaryLaw (1 / 2)) Real.sigmoid 0 (1 / 4) = -Real.log 3 := by
    have := calibratedShift_eq (F := binaryLaw (1 / 2)) Real.sigmoid_strictMono (β := 0)
      (fun c => integrable_binaryLaw _ _) (c := -Real.log 3)
    rwa [shiftMean_zero_slope, sigmoid_neg_log_three] at this
  have h := isMaxOn_binomialLogLik_shiftMean (F := binaryLaw (1 / 2)) (β := 0) (n := 4) (y := 1)
    Real.sigmoid_strictMono continuous_sigmoid Real.range_sigmoid
    (fun s => integrable_binaryLaw _ _) one_pos (by norm_num)
  rw [show (1 : ℝ) / 4 = 1 / 4 from rfl, hc] at h
  exact ⟨hc, h⟩

/-- **Instance of the normal profile.** The identity link, `F_B = binaryLaw (1/2)`, slope `1`,
reported mean `ȳ = 2` with variance `v = 1`: the arm mean is `θ(s) = s + 1/2`, and the profile
over the intercept is maximized exactly at `c(1, 2) = 3/2`. -/
theorem profile_normal_instance :
    calibratedShift (binaryLaw (1 / 2)) id (fun _ => 1) 2 = 3 / 2 ∧
      IsMaxOn (fun s => -(2 - shiftMean (binaryLaw (1 / 2)) id
          (fun x => x ⬝ᵥ (fun _ => (1 : ℝ))) s) ^ 2 / (2 * 1)) Set.univ (3 / 2) ∧
      ∀ s, -(2 - shiftMean (binaryLaw (1 / 2)) id (fun x => x ⬝ᵥ (fun _ => (1 : ℝ))) s) ^ 2 /
          (2 * 1) = -(2 - shiftMean (binaryLaw (1 / 2)) id
            (fun x => x ⬝ᵥ (fun _ => (1 : ℝ))) (3 / 2)) ^ 2 / (2 * 1) → s = 3 / 2 := by
  have : IsProbabilityMeasure (binaryLaw (1 / 2)) := isProbabilityMeasure_binaryLaw_half
  have hsm : ∀ s, shiftMean (binaryLaw (1 / 2)) id (fun x => x ⬝ᵥ (fun _ => (1 : ℝ))) s =
      s + 1 / 2 := fun s => by
    rw [shiftMean, integral_binaryLaw ⟨by norm_num, by norm_num⟩]
    simp [dotProduct]
    ring
  have hc : calibratedShift (binaryLaw (1 / 2)) id (fun _ => 1) 2 = 3 / 2 := by
    have := calibratedShift_eq (F := binaryLaw (1 / 2)) strictMono_id (β := fun _ => 1)
      (fun c => integrable_binaryLaw _ _) (c := 3 / 2)
    rw [hsm] at this
    norm_num at this
    exact this
  have h := isMaxOn_normalLogLik_shiftMean (F := binaryLaw (1 / 2)) (β := fun _ => 1)
    (ybar := 2) (v := 1) strictMono_id continuous_id (fun s => integrable_binaryLaw _ _)
    ⟨2, rfl⟩ one_pos
  rw [hc] at h
  exact ⟨hc, h⟩

end NetworkMetaRegression

end CausalInference
