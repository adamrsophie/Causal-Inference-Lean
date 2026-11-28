/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.RestrictedLikelihoodMaximizer

/-!
# Meta-analysis: the restricted likelihood can have two local maxima

With equal within study variances the restricted log likelihood of the between study variance
has exactly one maximizer on `[0, ∞)` (`isMaxOn_restrictedLogLik_const_iff`). This file shows that
with unequal variances the restricted likelihood need not be unimodal, already with three studies
and only two distinct variances.

**The instance.** Take the variances `v = (1/10, 1/10, 10)` and the estimates `y = (0, 1/2, 10)`.
Exact rational arithmetic gives the signs of the restricted score (which is a rational function
of `t`, the logarithms cancelling in the derivative):

`ℓ_R'(1/100) > 0`, `ℓ_R'(1/10) < 0`, `ℓ_R'(2) > 0`, `ℓ_R'(50) < 0`

(`restrictedScore_twoPeak_signs`). Hence (`restrictedLogLik_twoPeak`):

* `ℓ_R` has a local maximizer in `(1/100, 1/10)` and another in `(2, 50)`; both are zeros of the
  score;
* between them, `ℓ_R` has a zero of the score in `(1/10, 2)` that is a local minimizer and not a
  maximizer of `ℓ_R` on `[0, ∞)`.

So the score equation does not characterize the restricted maximum likelihood estimate: it has
at least three roots in `(0, ∞)`, and an iteration that stops at a root may stop at a local
minimizer. Two distinct variances, one of them with multiplicity two, suffice. Which of the two
local maxima is the global one is not determined here.

**The calculus.** For a function differentiable on `[p, q]` with derivative positive at `p` and
negative at `q`, a maximizer on `[p, q]` lies in the open interval and is a local maximizer
(`exists_isLocalMax_Ioo_of_hasDerivAt`); the endpoints are not maximizers
(`not_isMaxOn_Icc_left_of_hasDerivAt`, `not_isMaxOn_Icc_right_of_hasDerivAt`).

Whether the global maximizer can be non unique is not settled here.

## Main results

* `not_isMaxOn_Icc_left_of_hasDerivAt`, `not_isMaxOn_Icc_right_of_hasDerivAt`,
  `exists_isLocalMax_Ioo_of_hasDerivAt`, `exists_isLocalMin_Ioo_of_hasDerivAt`.
* `restrictedScore_twoPeak_signs`, `restrictedLogLik_twoPeak`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open Filter Topology Set

/-! ### Interior extrema from the signs of the derivative -/

section Calculus

variable {f : ℝ → ℝ} {p q : ℝ}

/-- If `f'(p) > 0` then `p` is not a maximizer of `f` on `[p, q]`, `p < q`. -/
theorem not_isMaxOn_Icc_left_of_hasDerivAt {d : ℝ} (hd : HasDerivAt f d p) (hpos : 0 < d)
    (hpq : p < q) : ¬ IsMaxOn f (Icc p q) p := by
  intro hmax
  have hs := hd.tendsto_slope_zero_right
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (f (p + t) - f p) := hs.eventually (lt_mem_nhds hpos)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < q - p :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨t, ht1, ht2, ht3⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
  have ht3' : 0 < t := ht3
  have hle := isMaxOn_iff.1 hmax (p + t) ⟨by linarith, by linarith⟩
  rw [smul_eq_mul] at ht1
  have : 0 < f (p + t) - f p := by
    have := mul_pos ht3' ht1
    rwa [← mul_assoc, mul_inv_cancel₀ ht3'.ne', one_mul] at this
  linarith

/-- If `f'(q) < 0` then `q` is not a maximizer of `f` on `[p, q]`, `p < q`. -/
theorem not_isMaxOn_Icc_right_of_hasDerivAt {d : ℝ} (hd : HasDerivAt f d q) (hneg : d < 0)
    (hpq : p < q) : ¬ IsMaxOn f (Icc p q) q := by
  intro hmax
  have hs := hd.tendsto_slope_zero_left
  have h1 : ∀ᶠ t in 𝓝[<] (0 : ℝ), t⁻¹ • (f (q + t) - f q) < 0 :=
    hs.eventually (gt_mem_nhds hneg)
  have h2 : ∀ᶠ t in 𝓝[<] (0 : ℝ), p - q < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
  obtain ⟨t, ht1, ht2, ht3⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
  have ht3' : t < 0 := ht3
  have hle := isMaxOn_iff.1 hmax (q + t) ⟨by linarith, by linarith⟩
  rw [smul_eq_mul] at ht1
  have : 0 < f (q + t) - f q := by
    have := mul_pos_of_neg_of_neg ht3' ht1
    rwa [← mul_assoc, mul_inv_cancel₀ ht3'.ne, one_mul] at this
  linarith

/-- **An interior local maximizer from the signs of the derivative**: if `f` has a derivative
`f' x` at every `x ∈ [p, q]`, `p < q`, with `f' p > 0` and `f' q < 0`, then `f` has a maximizer
on `[p, q]` in `(p, q)`, and it is a local maximizer of `f`. -/
theorem exists_isLocalMax_Ioo_of_hasDerivAt {f' : ℝ → ℝ}
    (hd : ∀ x ∈ Icc p q, HasDerivAt f (f' x) x) (hp : 0 < f' p) (hq : f' q < 0)
    (hpq : p < q) : ∃ m ∈ Ioo p q, IsMaxOn f (Icc p q) m ∧ IsLocalMax f m := by
  have hcont : ContinuousOn f (Icc p q) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hpq.le) hcont
  have hmp : m ≠ p := by
    rintro rfl
    exact not_isMaxOn_Icc_left_of_hasDerivAt (hd m ⟨le_rfl, hpq.le⟩) hp hpq hmax
  have hmq : m ≠ q := by
    rintro rfl
    exact not_isMaxOn_Icc_right_of_hasDerivAt (hd m ⟨hpq.le, le_rfl⟩) hq hpq hmax
  have hm' : m ∈ Ioo p q := ⟨lt_of_le_of_ne hm.1 (Ne.symm hmp), lt_of_le_of_ne hm.2 hmq⟩
  exact ⟨m, hm', hmax, hmax.isLocalMax (Icc_mem_nhds hm'.1 hm'.2)⟩

/-- **An interior local minimizer from the signs of the derivative**: if `f' p < 0` and
`f' q > 0`, then `f` has a minimizer on `[p, q]` in `(p, q)`, it is a local minimizer, and neither
endpoint is a minimizer of `f` on `[p, q]`. -/
theorem exists_isLocalMin_Ioo_of_hasDerivAt {f' : ℝ → ℝ}
    (hd : ∀ x ∈ Icc p q, HasDerivAt f (f' x) x) (hp : f' p < 0) (hq : 0 < f' q)
    (hpq : p < q) : (∃ m ∈ Ioo p q, IsMinOn f (Icc p q) m ∧ IsLocalMin f m) ∧
      ¬ IsMinOn f (Icc p q) p ∧ ¬ IsMinOn f (Icc p q) q := by
  have hd' : ∀ x ∈ Icc p q, HasDerivAt (fun x => -f x) (-f' x) x := fun x hx => (hd x hx).neg
  obtain ⟨m, hm, hmax, hloc⟩ :=
    exists_isLocalMax_Ioo_of_hasDerivAt hd' (by linarith) (by linarith) hpq
  refine ⟨⟨m, hm, fun x hx => ?_, ?_⟩, fun h => ?_, fun h => ?_⟩
  · have := hmax hx
    simp only [mem_ofPred_eq, neg_le_neg_iff] at this
    exact this
  · filter_upwards [hloc] with x hx
    simpa using hx
  · exact not_isMaxOn_Icc_left_of_hasDerivAt (hd p ⟨le_rfl, hpq.le⟩).neg (by linarith) hpq
      fun x hx => by simpa using h hx
  · exact not_isMaxOn_Icc_right_of_hasDerivAt (hd q ⟨hpq.le, le_rfl⟩).neg (by linarith) hpq
      fun x hx => by simpa using h hx

end Calculus

/-! ### The instance with two local maxima -/

/-- The within study variances `(1/10, 1/10, 10)` of the two peak instance. -/
noncomputable def twoPeakVar : Fin 3 → ℝ := ![1 / 10, 1 / 10, 10]

/-- The estimates `(0, 1/2, 10)` of the two peak instance. -/
noncomputable def twoPeakEst : Fin 3 → ℝ := ![0, 1 / 2, 10]

theorem twoPeakVar_add_pos {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) : 0 < twoPeakVar i + t := by
  fin_cases i <;> simp [twoPeakVar] <;> linarith

/-- **The signs of the restricted score** for `v = (1/10, 1/10, 10)`, `y = (0, 1/2, 10)`:
positive at `1/100`, negative at `1/10`, positive at `2`, negative at `50`. -/
theorem restrictedScore_twoPeak_signs :
    0 < restrictedScore twoPeakVar twoPeakEst (1 / 100) ∧
      restrictedScore twoPeakVar twoPeakEst (1 / 10) < 0 ∧
      0 < restrictedScore twoPeakVar twoPeakEst 2 ∧
      restrictedScore twoPeakVar twoPeakEst 50 < 0 := by
  simp only [restrictedScore, cochranQSlope, ivwEstimate, PopulationAdjustment.weightedMean,
    ivWeight, Fin.sum_univ_three, twoPeakVar, twoPeakEst, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- **The restricted likelihood with unequal variances can have two local maxima** (data
`v = (1/10, 1/10, 10)`, `y = (0, 1/2, 10)`): `ℓ_R` has a local maximizer `m₁ ∈ (1/100, 1/10)` and
a local maximizer `m₂ ∈ (2, 50)`, both zeros of the restricted score, and a zero `m₀ ∈ (1/10, 2)`
of the restricted score that is a local minimizer of `ℓ_R` and not a maximizer of `ℓ_R` on
`[0, ∞)`. -/
theorem restrictedLogLik_twoPeak :
    ∃ m₁ m₀ m₂ : ℝ, m₁ ∈ Ioo (1 / 100) (1 / 10) ∧ m₀ ∈ Ioo (1 / 10) 2 ∧ m₂ ∈ Ioo 2 50 ∧
      IsLocalMax (restrictedLogLik twoPeakVar twoPeakEst) m₁ ∧
      IsLocalMax (restrictedLogLik twoPeakVar twoPeakEst) m₂ ∧
      IsLocalMin (restrictedLogLik twoPeakVar twoPeakEst) m₀ ∧
      restrictedScore twoPeakVar twoPeakEst m₁ = 0 ∧
      restrictedScore twoPeakVar twoPeakEst m₀ = 0 ∧
      restrictedScore twoPeakVar twoPeakEst m₂ = 0 ∧
      ¬ IsMaxOn (restrictedLogLik twoPeakVar twoPeakEst) (Ici 0) m₀ := by
  obtain ⟨s1, s2, s3, s4⟩ := restrictedScore_twoPeak_signs
  have hd : ∀ t, 0 ≤ t → HasDerivAt (restrictedLogLik twoPeakVar twoPeakEst)
      (restrictedScore twoPeakVar twoPeakEst t) t := fun t ht =>
    hasDerivAt_restrictedLogLik twoPeakEst (twoPeakVar_add_pos ht)
  have hd' : ∀ p q : ℝ, 0 ≤ p → ∀ x ∈ Icc p q, HasDerivAt
      (restrictedLogLik twoPeakVar twoPeakEst) (restrictedScore twoPeakVar twoPeakEst x) x :=
    fun p q hp x hx => hd x (hp.trans hx.1)
  obtain ⟨m₁, hm₁, -, hl₁⟩ := exists_isLocalMax_Ioo_of_hasDerivAt
    (hd' (1 / 100) (1 / 10) (by norm_num)) s1 s2 (by norm_num)
  obtain ⟨m₂, hm₂, -, hl₂⟩ := exists_isLocalMax_Ioo_of_hasDerivAt
    (hd' 2 50 (by norm_num)) s3 s4 (by norm_num)
  obtain ⟨⟨m₀, hm₀, hmin, hl₀⟩, hleft, -⟩ := exists_isLocalMin_Ioo_of_hasDerivAt
    (hd' (1 / 10) 2 (by norm_num)) s2 s3 (by norm_num)
  have hpos : ∀ {m : ℝ}, 0 < m → HasDerivAt (restrictedLogLik twoPeakVar twoPeakEst)
      (restrictedScore twoPeakVar twoPeakEst m) m := fun hm => hd _ hm.le
  refine ⟨m₁, m₀, m₂, hm₁, hm₀, hm₂, hl₁, hl₂, hl₀,
    hl₁.hasDerivAt_eq_zero (hpos (by linarith [hm₁.1])),
    hl₀.hasDerivAt_eq_zero (hpos (by linarith [hm₀.1])),
    hl₂.hasDerivAt_eq_zero (hpos (by linarith [hm₂.1])), fun hmax => hleft fun x hx => ?_⟩
  have h1 : restrictedLogLik twoPeakVar twoPeakEst (1 / 10) ≤
      restrictedLogLik twoPeakVar twoPeakEst m₀ :=
    hmax (show (1 / 10 : ℝ) ∈ Ici 0 by norm_num)
  have h2 := hmin hx
  simp only [mem_ofPred_eq] at h2 ⊢
  linarith

end MetaAnalysis

end CausalInference
