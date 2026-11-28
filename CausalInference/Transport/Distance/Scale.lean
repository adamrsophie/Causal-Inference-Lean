/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Distance.Mahalanobis

/-!
# Scale invariance and scale dependence of the distances

A change of units multiplies coordinate `ℓ` of every summary by `a ℓ > 0`. If the scales,
ranges and covariance matrix are expressed in the new units as well (`s ↦ a s`, `r ↦ a r`,
`Σ ↦ diag(a) Σ diag(a)`), the standardized distances, the Gower distance and the Mahalanobis
distance do not change. The raw Euclidean distance does: it reweights the squared gaps by
`a ℓ²`, and a change of units in one covariate can reverse which of two candidates is the
matched comparator.

## Main results

* `stdGap_rescale`: the standardized gap is unchanged by a coherent change of units.
* `scale_invariance`: invariance of the standardized Euclidean, Minkowski, Manhattan,
  Chebyshev, mean absolute standardized difference, Gower and Mahalanobis distances.
* `euclidean_rescale_sq`: the raw Euclidean distance after a change of units.
* `euclidean_ranking_reversal`: a change of units reverses the matched comparator for the
  Euclidean distance, while the standardized Euclidean distance keeps it.
-/

@[expose] public section

namespace CausalInference

namespace Transport

namespace Distance

open Matrix

variable {p : ℕ}

/-- Under a coherent change of units `x ↦ a x`, `s ↦ a s` with positive `a` and `s`, the
standardized gap is unchanged. -/
theorem stdGap_rescale {a s : Fin p → ℝ} (ha : ∀ l, 0 < a l) (hs : ∀ l, 0 < s l)
    (x y : Fin p → ℝ) : stdGap (a * s) (a * x) (a * y) = stdGap s x y := by
  funext l
  simp only [stdGap, Pi.mul_apply]
  rw [← mul_sub, div_eq_div_iff (mul_ne_zero (ha l).ne' (hs l).ne') (hs l).ne']
  ring

/-- **Scale invariance.** Under the coherent change of units `x ↦ a x`, `s ↦ a s`, `r ↦ a r`,
`Σ ↦ diag(a) Σ diag(a)` with every `a ℓ > 0` (and `a ℓ = 1` on the binary Gower coordinates,
whose summaries are proportions), with positive scales and ranges and a positive definite `Σ`,
the standardized Euclidean distance, every Minkowski distance, the Manhattan, Chebyshev, mean
absolute standardized difference, Gower and Mahalanobis distances are unchanged. -/
theorem scale_invariance {a s r : Fin p → ℝ} (ha : ∀ l, 0 < a l) (hs : ∀ l, 0 < s l)
    (hr : ∀ l, 0 < r l) (bin : Fin p → Bool) (hbin : ∀ l, bin l = true → a l = 1)
    {Sig : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef) (x y : Fin p → ℝ) :
    stdEuclidean (a * s) (a * x) (a * y) = stdEuclidean s x y ∧
      (∀ q, minkowski q (a * s) (a * x) (a * y) = minkowski q s x y) ∧
      manhattan (a * s) (a * x) (a * y) = manhattan s x y ∧
      chebyshev (a * s) (a * x) (a * y) = chebyshev s x y ∧
      meanAbsStdDiff (a * s) (a * x) (a * y) = meanAbsStdDiff s x y ∧
      gower (a * r) bin (a * x) (a * y) = gower r bin x y ∧
      mahalanobis (diagonal a * Sig * diagonal a) (a * x) (a * y) = mahalanobis Sig x y := by
  have hz := stdGap_rescale ha hs x y
  refine ⟨by rw [stdEuclidean, hz]; rfl, fun q ↦ by rw [minkowski, hz]; rfl,
    by rw [manhattan, hz]; rfl, by rw [chebyshev, hz]; rfl,
    by rw [meanAbsStdDiff, manhattan, hz]; rfl, ?_, ?_⟩
  · unfold gower
    congr 1
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    unfold gowerTerm
    simp only [Pi.mul_apply]
    split_ifs with hb
    · rw [hbin l hb, one_mul, one_mul]
    · rw [← mul_sub, abs_mul, abs_of_pos (ha l)]
      congr 1
      rw [div_eq_div_iff (mul_ne_zero (ha l).ne' (hr l).ne') (hr l).ne']
      ring
  · have hdet : IsUnit (diagonal a).det := by
      rw [det_diagonal]
      exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun l _ ↦ (ha l).ne')
    have hv : ∀ v : Fin p → ℝ, a * v = diagonal a *ᵥ v + 0 := fun v ↦ by
      funext l; simp [mulVec_diagonal]
    have := mahalanobis_affine hSig hdet 0 x y
    rwa [diagonal_transpose, ← hv, ← hv] at this

/-- **The raw Euclidean distance reweights the squared gaps by `a ℓ²`** under a change of
units. -/
theorem euclidean_rescale_sq (a x y : Fin p → ℝ) :
    euclidean (a * x) (a * y) ^ 2 = ∑ l, a l ^ 2 * (y l - x l) ^ 2 := by
  rw [euclidean_eq_sqrt, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Pi.mul_apply]; ring

/-- The two candidate summaries of the ranking reversal: gaps `(1, 2.1)` and `(2, 1)` from the
target summary `0`. -/
noncomputable def reversalCandidates : Fin 2 → Fin 2 → ℝ := ![![1, 21 / 10], ![2, 1]]

/-- The change of units of the ranking reversal: the first covariate is multiplied by `10`. -/
def reversalUnits : Fin 2 → ℝ := ![10, 1]

/-- **A change of units reverses the Euclidean matched comparator.** With target summary `0`
and candidates with gaps `(1, 2.1)` and `(2, 1)`, the second candidate is the unique matched
comparator for the Euclidean distance (`5 < 5.41`). After multiplying the first covariate by
`10`, the first candidate is (`104.41 < 401`). The standardized Euclidean distance with scales
`s = (1, 1)`, expressed in the new units as `a s`, selects the second candidate in both unit
systems. -/
theorem euclidean_ranking_reversal :
    euclidean 0 (reversalCandidates 1) < euclidean 0 (reversalCandidates 0) ∧
      IsMatchedComparator euclidean 0 reversalCandidates 1 ∧
      euclidean 0 (reversalUnits * reversalCandidates 0) <
        euclidean 0 (reversalUnits * reversalCandidates 1) ∧
      IsMatchedComparator euclidean 0 (fun j ↦ reversalUnits * reversalCandidates j) 0 ∧
      IsMatchedComparator (stdEuclidean 1) 0 reversalCandidates 1 ∧
      IsMatchedComparator (stdEuclidean (reversalUnits * 1)) 0
        (fun j ↦ reversalUnits * reversalCandidates j) 1 := by
  have ha : ∀ l, 0 < reversalUnits l := fun l ↦ by fin_cases l <;> norm_num [reversalUnits]
  have h1 : ∀ l : Fin 2, (0 : ℝ) < (1 : Fin 2 → ℝ) l := fun _ ↦ one_pos
  have e1 : euclidean 0 (reversalCandidates 1) < euclidean 0 (reversalCandidates 0) := by
    rw [euclidean_eq_sqrt, euclidean_eq_sqrt]
    refine Real.sqrt_lt_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) ?_
    simp only [Fin.sum_univ_two, reversalCandidates]
    norm_num
  have e2 : euclidean 0 (reversalUnits * reversalCandidates 0) <
      euclidean 0 (reversalUnits * reversalCandidates 1) := by
    rw [euclidean_eq_sqrt, euclidean_eq_sqrt]
    refine Real.sqrt_lt_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) ?_
    simp only [Fin.sum_univ_two, Pi.mul_apply, reversalCandidates, reversalUnits]
    norm_num
  have e3 : stdEuclidean 1 0 (reversalCandidates 1) < stdEuclidean 1 0 (reversalCandidates 0) :=
    by rwa [stdEuclidean_one, stdEuclidean_one]
  have hinv : ∀ j, stdEuclidean (reversalUnits * 1) 0 (reversalUnits * reversalCandidates j) =
      stdEuclidean 1 0 (reversalCandidates j) := fun j ↦ by
    have := stdGap_rescale ha h1 0 (reversalCandidates j)
    rw [mul_zero] at this
    rw [stdEuclidean, this]; rfl
  refine ⟨e1, fun k ↦ ?_, e2, fun k ↦ ?_, fun k ↦ ?_, fun k ↦ ?_⟩
  · fin_cases k
    · exact e1.le
    · exact le_rfl
  · fin_cases k
    · exact le_rfl
    · exact e2.le
  · fin_cases k
    · exact e3.le
    · exact le_rfl
  · rw [hinv, hinv]
    fin_cases k
    · exact e3.le
    · exact le_rfl

/-- A matched comparator exists among the two candidates, for any distance. -/
example (d : (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ) : ∃ j, IsMatchedComparator d 0 reversalCandidates j :=
  exists_isMatchedComparator d 0 reversalCandidates

/-- Scale invariance with `a = (10, 1)`, unit scales and ranges, a binary second coordinate
and `Σ = I`. -/
example (x y : Fin 2 → ℝ) :
    mahalanobis (diagonal reversalUnits * 1 * diagonal reversalUnits) (reversalUnits * x)
      (reversalUnits * y) = mahalanobis 1 x y ∧
    gower (reversalUnits * 1) ![false, true] (reversalUnits * x) (reversalUnits * y) =
      gower 1 ![false, true] x y := by
  have ha : ∀ l, 0 < reversalUnits l := fun l ↦ by fin_cases l <;> norm_num [reversalUnits]
  have h1 : ∀ l : Fin 2, (0 : ℝ) < (1 : Fin 2 → ℝ) l := fun _ ↦ one_pos
  have hb : ∀ l, (![false, true] : Fin 2 → Bool) l = true → reversalUnits l = 1 := fun l ↦ by
    fin_cases l <;> simp [reversalUnits]
  have := scale_invariance ha h1 h1 ![false, true] hb PosDef.one x y
  exact ⟨this.2.2.2.2.2.2, this.2.2.2.2.2.1⟩

end Distance

end Transport

end CausalInference
