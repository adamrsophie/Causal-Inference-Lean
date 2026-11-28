/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedLikelihoodMaximizer

/-!
# Meta-analysis: the restricted maximum likelihood estimate from two studies

With equal within study variances the restricted likelihood of the between study variance has a
unique maximizer on `[0, ∞)` (`isMaxOn_restrictedLogLik_const_iff`). With unequal variances it
can have two local maxima (`restrictedLogLik_twoPeak`), already for three studies. This file
shows that for **two** studies uniqueness holds for all within study variances, equal or not.

**The two study likelihood.** With variances `v₁, v₂ > 0`, estimates `y₁, y₂` and `S(t) = v₁ + v₂ +
2t`, the restricted log likelihood is (`restrictedLogLik_fin_two`)

`ℓ_R(t) = -½ log S(t) - (y₁ - y₂)² / (2 S(t))`.

Proof: with `aᵢ = vᵢ + t`, `log a₁ + log a₂ + log(1/a₁ + 1/a₂) = log(a₁ + a₂)` and Cochran's `Q`
of two studies is `(y₁ - y₂)² / (a₁ + a₂)`. So `ℓ_R` depends on `t` only through `v₁ + v₂ + 2t`.

**Uniqueness and closed form.** The function `u ↦ log u + d² / u` has the unique minimizer
`max V d²` on `[V, ∞)` (`log_add_div_lt`). Hence the restricted likelihood of two studies has
exactly one maximizer on `[0, ∞)` (`isMaxOn_restrictedLogLik_fin_two_iff`):

`τ̂²_REML = max 0 ((y₁ - y₂)² / 2 - (v₁ + v₂) / 2)`.

With `v₁ = v₂ = v` it is `max 0 (s² - v)` with `s² = (y₁ - y₂)² / 2` the sample variance of the
two estimates, the equal variance closed form.

**Instances.** The variances `(1, 2)` with estimates `(0, 3)` give the unique estimate `3`; the
variances `(1, 3)` with estimates `(0, 2)` give the unique estimate `0`
(`example_reml_fin_two`).

## Main results

* `restrictedLogLik_fin_two`, `isMaxOn_restrictedLogLik_fin_two_iff`,
  `existsUnique_isMaxOn_restrictedLogLik_fin_two`.
* `example_reml_fin_two`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open PopulationAdjustment

/-- **The restricted log likelihood of two studies**: for `v₁ + t > 0` and `v₂ + t > 0`,
`ℓ_R(t) = -½ log(v₁ + v₂ + 2t) - (y₁ - y₂)² / (2 (v₁ + v₂ + 2t))`. -/
theorem restrictedLogLik_fin_two {v : Fin 2 → ℝ} {t : ℝ} (h0 : 0 < v 0 + t) (h1 : 0 < v 1 + t)
    (y : Fin 2 → ℝ) :
    restrictedLogLik v y t = -(1 / 2) * Real.log (v 0 + v 1 + 2 * t) -
      (y 0 - y 1) ^ 2 / (2 * (v 0 + v 1 + 2 * t)) := by
  have hS : 0 < v 0 + v 1 + 2 * t := by linarith
  have hW : 1 / (v 0 + t) + 1 / (v 1 + t) = (v 0 + v 1 + 2 * t) / ((v 0 + t) * (v 1 + t)) := by
    field_simp
    ring
  have hlog : Real.log (1 / (v 0 + t) + 1 / (v 1 + t)) = Real.log (v 0 + v 1 + 2 * t) -
      Real.log (v 0 + t) - Real.log (v 1 + t) := by
    rw [hW, Real.log_div hS.ne' (mul_pos h0 h1).ne', Real.log_mul h0.ne' h1.ne']
    ring
  simp only [restrictedLogLik, cochranQ, ivwEstimate, weightedMean, ivWeight, Fin.sum_univ_two]
  rw [hlog]
  field_simp
  ring

/-- **Uniqueness and closed form for two studies**: for `v₁, v₂ > 0` and any estimates, `t ≥ 0`
maximizes the restricted log likelihood on `[0, ∞)` exactly when
`t = max 0 ((y₁ - y₂)² / 2 - (v₁ + v₂) / 2)`. The variances need not be equal. -/
theorem isMaxOn_restrictedLogLik_fin_two_iff {v : Fin 2 → ℝ} (hv : ∀ i, 0 < v i)
    (y : Fin 2 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsMaxOn (restrictedLogLik v y) (Set.Ici 0) t ↔
      t = max 0 ((y 0 - y 1) ^ 2 / 2 - (v 0 + v 1) / 2) := by
  set V := v 0 + v 1
  set d2 := (y 0 - y 1) ^ 2
  have hV : 0 < V := add_pos (hv 0) (hv 1)
  set tstar := max 0 (d2 / 2 - V / 2)
  have htstar : 0 ≤ tstar := le_max_left _ _
  have hSstar : V + 2 * tstar = max V d2 := by
    simp only [tstar]
    rcases le_total V d2 with h | h
    · rw [max_eq_right (by linarith), max_eq_right h]; ring
    · rw [max_eq_left (by linarith), max_eq_left h]; ring
  have hform : ∀ u, 0 ≤ u → restrictedLogLik v y u =
      -(1 / 2) * (Real.log (V + 2 * u) + d2 / (V + 2 * u)) := by
    intro u hu
    rw [restrictedLogLik_fin_two (by linarith [hv 0]) (by linarith [hv 1])]
    have : 0 < V + 2 * u := by linarith
    simp only [V, d2]
    field_simp
    ring
  have hstrict : ∀ u, 0 ≤ u → u ≠ tstar → restrictedLogLik v y u < restrictedLogLik v y tstar := by
    intro u hu hne
    rw [hform u hu, hform tstar htstar, hSstar]
    have hlt := log_add_div_lt (a := d2) hV (show V ≤ V + 2 * u by linarith)
      (fun h => hne (by rw [← hSstar] at h; linarith))
    linarith
  constructor
  · intro hmax
    by_contra hne
    exact absurd (isMaxOn_iff.1 hmax tstar htstar) (not_le.2 (hstrict t ht hne))
  · rintro rfl
    refine isMaxOn_iff.2 fun u hu => ?_
    rcases eq_or_ne u tstar with h | h
    · rw [h]
    · exact (hstrict u hu h).le

/-- **The restricted maximum likelihood estimate of two studies exists and is unique**, for any
positive within study variances. -/
theorem existsUnique_isMaxOn_restrictedLogLik_fin_two {v : Fin 2 → ℝ} (hv : ∀ i, 0 < v i)
    (y : Fin 2 → ℝ) : ∃! t, 0 ≤ t ∧ IsMaxOn (restrictedLogLik v y) (Set.Ici 0) t := by
  refine ⟨max 0 ((y 0 - y 1) ^ 2 / 2 - (v 0 + v 1) / 2), ⟨le_max_left _ _,
    (isMaxOn_restrictedLogLik_fin_two_iff hv y (le_max_left _ _)).2 rfl⟩, ?_⟩
  rintro t ⟨ht, hmax⟩
  exact (isMaxOn_restrictedLogLik_fin_two_iff hv y ht).1 hmax

/-- **The two study closed form on data**: with the variances `(1, 2)` and the estimates `(0, 3)`,
`(y₁ - y₂)² / 2 - (v₁ + v₂) / 2 = 9/2 - 3/2 = 3` and the unique restricted maximum likelihood
estimate is `3`; with the variances `(1, 3)` and the estimates `(0, 2)`, `2 - 2 = 0` and the unique
estimate is `0`. -/
theorem example_reml_fin_two :
    IsMaxOn (restrictedLogLik ![1, 2] ![0, 3]) (Set.Ici 0) 3 ∧
      (∀ t, 0 ≤ t → IsMaxOn (restrictedLogLik ![1, 2] ![0, 3]) (Set.Ici 0) t → t = 3) ∧
      IsMaxOn (restrictedLogLik ![1, 3] ![0, 2]) (Set.Ici 0) 0 ∧
      (∀ t, 0 ≤ t → IsMaxOn (restrictedLogLik ![1, 3] ![0, 2]) (Set.Ici 0) t → t = 0) := by
  have hv1 : ∀ i, 0 < (![1, 2] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have hv2 : ∀ i, 0 < (![1, 3] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have h1 := fun t (ht : (0 : ℝ) ≤ t) => isMaxOn_restrictedLogLik_fin_two_iff hv1 ![0, 3] ht
  have h2 := fun t (ht : (0 : ℝ) ≤ t) => isMaxOn_restrictedLogLik_fin_two_iff hv2 ![0, 2] ht
  have e1 : max (0 : ℝ) (((![0, 3] : Fin 2 → ℝ) 0 - (![0, 3] : Fin 2 → ℝ) 1) ^ 2 / 2 -
      ((![1, 2] : Fin 2 → ℝ) 0 + (![1, 2] : Fin 2 → ℝ) 1) / 2) = 3 := by norm_num
  have e2 : max (0 : ℝ) (((![0, 2] : Fin 2 → ℝ) 0 - (![0, 2] : Fin 2 → ℝ) 1) ^ 2 / 2 -
      ((![1, 3] : Fin 2 → ℝ) 0 + (![1, 3] : Fin 2 → ℝ) 1) / 2) = 0 := by norm_num
  simp only [e1, e2] at h1 h2
  exact ⟨(h1 3 (by norm_num)).2 rfl, fun t ht hmax => (h1 t ht).1 hmax,
    (h2 0 le_rfl).2 rfl, fun t ht hmax => (h2 t ht).1 hmax⟩

end MetaAnalysis

end CausalInference
