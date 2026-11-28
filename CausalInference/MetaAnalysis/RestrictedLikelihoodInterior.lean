/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedLikelihoodTieTwoStudy
public import CausalInference.MetaAnalysis.RestrictedLikelihoodUnimodal

/-!
# Interior maximizers of the restricted likelihood

The restricted maximum likelihood estimate `τ̂²` of the between study variance is a maximizer of
the restricted log likelihood `ℓ_R` on `[0, ∞)`. This file gives checkable conditions for the
estimate to be **interior**, `τ̂² > 0`.

* **Any number of studies, any variances** (`pos_of_isMaxOn_restrictedLogLik_of_score_pos`,
  `exists_pos_isMaxOn_restrictedLogLik_of_score_pos`): for `k ≥ 2` studies with variances
  `vᵢ > 0`, if the restricted score at `0`,
  `½ (∑ wᵢ² (yᵢ - θ̂)² - (∑ wᵢ - ∑ wᵢ² / ∑ wᵢ))` with `wᵢ = 1/vᵢ` and `θ̂` the fixed effect
  estimate, is positive, then a maximizer exists and every maximizer is interior and solves the
  score equation. Uniqueness is not claimed here: three studies can give two interior local
  maxima (`restrictedLogLik_twoPeak`).
* **Equal variances** (`exists_pos_isMaxOn_restrictedLogLik_const_iff`): for `vᵢ = v > 0` and
  `k ≥ 2` there is an interior maximizer if and only if `v < s²`, with `s²` the sample variance
  of the estimates, and then it is unique, `τ̂² = s² - v`.
* **Two studies with unequal variances** (`exists_pos_isMaxOn_restrictedLogLik_fin_two_iff`):
  there is an interior maximizer if and only if `v₁ + v₂ < (y₁ - y₂)²`, and then it is unique,
  `τ̂² = ((y₁ - y₂)² - v₁ - v₂) / 2`.
* **Instance** (`example_restrictedScore_pos`): for the variances `(1, 2)` and estimates `(0, 3)`
  the restricted score at `0` is `2/3`, and the unique maximizer is the interior point `3`.

## Main results

* `pos_of_isMaxOn_restrictedLogLik_of_score_pos`,
  `exists_pos_isMaxOn_restrictedLogLik_of_score_pos`,
  `exists_pos_isMaxOn_restrictedLogLik_const_iff`,
  `exists_pos_isMaxOn_restrictedLogLik_fin_two_iff`, `example_restrictedScore_pos`.

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

variable {ι : Type*} [Fintype ι]

/-- **A positive score at `0` makes every maximizer interior**: for variances `vᵢ > 0`, if the
restricted score at `0` is positive, every maximizer `t ≥ 0` of the restricted log likelihood on
`[0, ∞)` has `t > 0` and restricted score `0`. -/
theorem pos_of_isMaxOn_restrictedLogLik_of_score_pos [Nonempty ι] {v : ι → ℝ}
    (hv : ∀ i, 0 < v i) (y : ι → ℝ) (h0 : 0 < restrictedScore v y 0) {t : ℝ} (ht : 0 ≤ t)
    (hmax : IsMaxOn (restrictedLogLik v y) (Ici 0) t) :
    0 < t ∧ restrictedScore v y t = 0 := by
  obtain ⟨_, hint, _, hbd⟩ := restrictedLogLik_firstOrder hv y
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · subst h
      exact absurd (hbd hmax) (not_le.2 h0)
  refine ⟨htpos, ?_⟩
  simp only [restrictedScore, hint t htpos hmax, sub_self, mul_zero]

/-- **Existence of an interior maximizer from a positive score at `0`**: for `k ≥ 2` studies
with variances `vᵢ > 0` and positive restricted score at `0`, the restricted log likelihood has a
maximizer on `[0, ∞)`, and every maximizer is interior with restricted score `0`. -/
theorem exists_pos_isMaxOn_restrictedLogLik_of_score_pos {v : ι → ℝ} (hv : ∀ i, 0 < v i)
    (hk : 2 ≤ Fintype.card ι) (y : ι → ℝ) (h0 : 0 < restrictedScore v y 0) :
    (∃ t, 0 < t ∧ IsMaxOn (restrictedLogLik v y) (Ici 0) t) ∧
      ∀ t, 0 ≤ t → IsMaxOn (restrictedLogLik v y) (Ici 0) t →
        0 < t ∧ restrictedScore v y t = 0 := by
  have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨t, ht, hmax, _, _⟩ := exists_isMaxOn_restrictedLogLik hv hk y
  exact ⟨⟨t, (pos_of_isMaxOn_restrictedLogLik_of_score_pos hv y h0 ht hmax).1, hmax⟩,
    fun s hs hsmax => pos_of_isMaxOn_restrictedLogLik_of_score_pos hv y h0 hs hsmax⟩

/-- **Equal variances: an interior maximizer exists exactly when `v < s²`, and is unique**: for
`vᵢ = v > 0` and `k ≥ 2` studies, with `s² = ∑ (yᵢ - ȳ)² / (k - 1)`, the restricted log
likelihood has a maximizer `t > 0` on `[0, ∞)` if and only if `v < s²`; in that case `s² - v` is
its only maximizer on `[0, ∞)`. -/
theorem exists_pos_isMaxOn_restrictedLogLik_const_iff {v : ℝ} (hv : 0 < v)
    (hk : 2 ≤ Fintype.card ι) (y : ι → ℝ) :
    ((∃ t, 0 < t ∧ IsMaxOn (restrictedLogLik (fun _ : ι => v) y) (Ici 0) t) ↔
        v < regSxx y / ((Fintype.card ι : ℝ) - 1)) ∧
      (v < regSxx y / ((Fintype.card ι : ℝ) - 1) →
        ∀ t, 0 ≤ t → (IsMaxOn (restrictedLogLik (fun _ : ι => v) y) (Ici 0) t ↔
          t = regSxx y / ((Fintype.card ι : ℝ) - 1) - v)) := by
  set s2 := regSxx y / ((Fintype.card ι : ℝ) - 1)
  refine ⟨⟨fun ⟨t, ht, hmax⟩ => ?_, fun hlt => ?_⟩, fun hlt t ht => ?_⟩
  · have h := (isMaxOn_restrictedLogLik_const_iff hv hk y ht.le).1 hmax
    by_contra hle
    have : max 0 (s2 - v) = 0 := max_eq_left (by linarith [not_lt.1 hle])
    linarith
  · refine ⟨s2 - v, by linarith, (isMaxOn_restrictedLogLik_const_iff hv hk y
      (by linarith)).2 (max_eq_right (by linarith)).symm⟩
  · rw [isMaxOn_restrictedLogLik_const_iff hv hk y ht, max_eq_right (by linarith)]

/-- **Two studies: an interior maximizer exists exactly when `v₁ + v₂ < (y₁ - y₂)²`, and is
unique**: for variances `v₁, v₂ > 0`, equal or not, the restricted log likelihood has a maximizer
`t > 0` on `[0, ∞)` if and only if `v₁ + v₂ < (y₁ - y₂)²`; in that case
`((y₁ - y₂)² - v₁ - v₂) / 2` is its only maximizer on `[0, ∞)`. -/
theorem exists_pos_isMaxOn_restrictedLogLik_fin_two_iff {v : Fin 2 → ℝ} (hv : ∀ i, 0 < v i)
    (y : Fin 2 → ℝ) :
    ((∃ t, 0 < t ∧ IsMaxOn (restrictedLogLik v y) (Ici 0) t) ↔ v 0 + v 1 < (y 0 - y 1) ^ 2) ∧
      (v 0 + v 1 < (y 0 - y 1) ^ 2 →
        ∀ t, 0 ≤ t → (IsMaxOn (restrictedLogLik v y) (Ici 0) t ↔
          t = ((y 0 - y 1) ^ 2 - v 0 - v 1) / 2)) := by
  have he : (y 0 - y 1) ^ 2 / 2 - (v 0 + v 1) / 2 = ((y 0 - y 1) ^ 2 - v 0 - v 1) / 2 := by ring
  refine ⟨⟨fun ⟨t, ht, hmax⟩ => ?_, fun hlt => ?_⟩, fun hlt t ht => ?_⟩
  · have h := (isMaxOn_restrictedLogLik_fin_two_iff hv y ht.le).1 hmax
    by_contra hle
    have : max 0 ((y 0 - y 1) ^ 2 / 2 - (v 0 + v 1) / 2) = 0 :=
      max_eq_left (by linarith [not_lt.1 hle])
    linarith
  · refine ⟨((y 0 - y 1) ^ 2 - v 0 - v 1) / 2, by linarith,
      (isMaxOn_restrictedLogLik_fin_two_iff hv y (by linarith)).2 ?_⟩
    rw [max_eq_right (by linarith), he]
  · rw [isMaxOn_restrictedLogLik_fin_two_iff hv y ht, max_eq_right (by linarith), he]

/-- **Instance**: for the variances `(1, 2)` and the estimates `(0, 3)` the restricted score at
`0` is `2/3 > 0`, so every maximizer is interior; by the two study criterion the only maximizer
on `[0, ∞)` is `3`. -/
theorem example_restrictedScore_pos :
    restrictedScore ![1, 2] ![0, 3] 0 = 2 / 3 ∧
      ∀ t, 0 ≤ t → (IsMaxOn (restrictedLogLik ![(1 : ℝ), 2] ![0, 3]) (Ici 0) t ↔ t = 3) := by
  have hv : ∀ i, 0 < (![(1 : ℝ), 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  refine ⟨?_, fun t ht => ?_⟩
  · simp only [restrictedScore, cochranQSlope, ivwEstimate, PopulationAdjustment.weightedMean,
      ivWeight, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]
    norm_num
  · rw [((exists_pos_isMaxOn_restrictedLogLik_fin_two_iff hv _).2 (by norm_num)) t ht]
    norm_num

end MetaAnalysis

end CausalInference
