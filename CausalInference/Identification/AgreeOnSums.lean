/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Graphical.Factorization
public import Mathlib.Logic.Function.DependsOn

/-!
# Sums over cylinder sets of configurations

Finite configurations `w : ∀ v, α v` and the cylinder sets `FiniteDist.agreeOn Rᶜ w` of the
configurations that agree with `w` outside a finite set `R` of coordinates. A sum over
`agreeOn Rᶜ w` is a sum over the values of the coordinates in `R`, with the other coordinates
held at those of `w`. The identification results for c-factors are computations with such sums.

## Main results

* `FiniteDist.sum_agreeOn_union`: Fubini for cylinder sums. Summing over the coordinates of
  `A ∪ B` (disjoint) is summing over `B` and then over `A`.
* `FiniteDist.sum_agreeOn_eq_of_dependsOn`: a sum over the coordinates of `A` of a function that
  does not depend on the coordinates of `B` (disjoint from `A`) does not depend on the base
  configuration on `B`.
* `FiniteDist.sum_agreeOn_mul_of_dependsOn`: if `F` does not depend on the coordinates of `A`,
  it can be taken out of a sum over these coordinates.
* `FiniteDist.sum_agreeOn_union_mul`: a sum over `A ∪ B` (disjoint) of `F * G`, where `F` does
  not depend on `B` and `G` does not depend on `A`, is the product of the sum of `F` over `A`
  and the sum of `G` over `B`.
* `FiniteDist.sum_agreeOn_margAt`: summing the marginal mass on `T` over the coordinates of
  `R ⊆ T` gives the marginal mass on `T \ R`.
-/

@[expose] public section

namespace CausalInference

open Finset

namespace FiniteDist

variable {V : Type*} [Fintype V] [DecidableEq V] {α : V → Type*} [∀ v, Fintype (α v)]
  [∀ v, DecidableEq (α v)]

/-- Summing over the configurations that agree with `w` outside the empty set: only `w`. -/
theorem agreeOn_compl_empty' (w : ∀ v, α v) :
    agreeOn (∅ : Finset V)ᶜ w = {w} := by
  ext c
  simp [funext_iff]

/-- A sum over the coordinates of no vertex is the value at the base configuration. -/
theorem sum_agreeOn_compl_empty {M : Type*} [AddCommMonoid M] (F : (∀ v, α v) → M)
    (w : ∀ v, α v) : ∑ c ∈ agreeOn (∅ : Finset V)ᶜ w, F c = F w := by
  rw [agreeOn_compl_empty', sum_singleton]

/-- **Fubini for cylinder sums.** For disjoint `A` and `B`, summing over the coordinates of
`A ∪ B` is summing first over the coordinates of `B` and then over those of `A`. -/
theorem sum_agreeOn_union {M : Type*} [AddCommMonoid M] {A B : Finset V} (hAB : Disjoint A B)
    (F : (∀ v, α v) → M) (w : ∀ v, α v) :
    ∑ d ∈ agreeOn (A ∪ B)ᶜ w, F d = ∑ d' ∈ agreeOn Bᶜ w, ∑ d ∈ agreeOn Aᶜ d', F d := by
  rw [← sum_fiberwise_of_maps_to (s := agreeOn (A ∪ B)ᶜ w) (t := agreeOn Bᶜ w)
    (g := fun d v => if v ∈ A then w v else d v) ?_]
  · refine sum_congr rfl fun d' hd' => sum_congr ?_ fun _ _ => rfl
    simp only [mem_agreeOn, mem_compl] at hd'
    ext d
    simp only [mem_filter, mem_agreeOn, mem_compl, mem_union, not_or]
    constructor
    · rintro ⟨-, hg⟩ v hv
      rw [← hg]
      simp [hv]
    · intro hd
      refine ⟨fun v hv => (hd v hv.1).trans (hd' v hv.2), funext fun v => ?_⟩
      by_cases hv : v ∈ A
      · simp only [hv, ite_true]
        exact (hd' v fun hB => disjoint_left.1 hAB hv hB).symm
      · simp [hv, hd v hv]
  · intro d hd
    simp only [mem_agreeOn, mem_compl, mem_union, not_or] at hd ⊢
    intro v hv
    by_cases hvA : v ∈ A
    · simp [hvA]
    · simp [hvA, hd v ⟨hvA, hv⟩]

/-- A sum over the coordinates of `A` of a function that does not depend on the coordinates of
`B`, disjoint from `A`, is the same at two base configurations that agree outside `B`. -/
theorem sum_agreeOn_eq_of_dependsOn {M : Type*} [AddCommMonoid M] {A B : Finset V}
    (hAB : Disjoint A B) {F : (∀ v, α v) → M} (hF : DependsOn F (↑B)ᶜ) {x y : ∀ v, α v}
    (hxy : ∀ v ∉ B, x v = y v) :
    ∑ d ∈ agreeOn Aᶜ x, F d = ∑ d ∈ agreeOn Aᶜ y, F d := by
  refine sum_nbij' (fun d v => if v ∈ B then y v else d v) (fun d v => if v ∈ B then x v else d v)
    ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [mem_agreeOn, mem_compl] at hd ⊢
    intro v hv
    by_cases hvB : v ∈ B
    · simp [hvB]
    · simp [hvB, hd v hv, hxy v hvB]
  · intro d hd
    simp only [mem_agreeOn, mem_compl] at hd ⊢
    intro v hv
    by_cases hvB : v ∈ B
    · simp [hvB]
    · simp [hvB, hd v hv, hxy v hvB]
  · intro d hd
    simp only [mem_agreeOn, mem_compl] at hd
    funext v
    by_cases hvB : v ∈ B
    · simp only [hvB, ite_true]
      exact (hd v fun hA => disjoint_left.1 hAB hA hvB).symm
    · simp [hvB]
  · intro d hd
    simp only [mem_agreeOn, mem_compl] at hd
    funext v
    by_cases hvB : v ∈ B
    · simp only [hvB, ite_true]
      exact (hd v fun hA => disjoint_left.1 hAB hA hvB).symm
    · simp [hvB]
  · intro d _
    refine hF fun v hv => ?_
    simp only [Set.mem_compl_iff, mem_coe] at hv
    simp [hv]

/-- A function that does not depend on the coordinates of `A` can be taken out of a sum over
these coordinates. -/
theorem sum_agreeOn_mul_of_dependsOn {A : Finset V} {F : (∀ v, α v) → ℝ}
    (hF : DependsOn F (↑A)ᶜ) (G : (∀ v, α v) → ℝ) (w : ∀ v, α v) :
    ∑ d ∈ agreeOn Aᶜ w, F d * G d = F w * ∑ d ∈ agreeOn Aᶜ w, G d := by
  rw [mul_sum]
  refine sum_congr rfl fun d hd => ?_
  rw [hF fun v hv => ?_]
  simp only [Set.mem_compl_iff, mem_coe] at hv
  exact (mem_agreeOn.1 hd) v (mem_compl.2 hv)

/-- **Product of independent cylinder sums.** For disjoint `A` and `B`, if `F` does not depend on
the coordinates of `B` and `G` does not depend on those of `A`, then the sum of `F * G` over the
coordinates of `A ∪ B` is the sum of `F` over `A` times the sum of `G` over `B`. -/
theorem sum_agreeOn_union_mul {A B : Finset V} (hAB : Disjoint A B) {F G : (∀ v, α v) → ℝ}
    (hF : DependsOn F (↑B)ᶜ) (hG : DependsOn G (↑A)ᶜ) (w : ∀ v, α v) :
    ∑ d ∈ agreeOn (A ∪ B)ᶜ w, F d * G d =
      (∑ d ∈ agreeOn Aᶜ w, F d) * ∑ d ∈ agreeOn Bᶜ w, G d := by
  rw [sum_agreeOn_union hAB, mul_sum]
  refine sum_congr rfl fun d' hd' => ?_
  simp_rw [mul_comm (F _) (G _)]
  rw [sum_agreeOn_mul_of_dependsOn hG, mul_comm]
  congr 1
  refine sum_agreeOn_eq_of_dependsOn hAB hF fun v hv => ?_
  exact (mem_agreeOn.1 hd') v (mem_compl.2 hv)

/-- Summing the marginal mass on `T` over the coordinates of `R ⊆ T` gives the marginal mass on
`T \ R`. -/
theorem sum_agreeOn_margAt (p : FiniteDist (∀ v, α v)) {R T : Finset V} (hRT : R ⊆ T)
    (w : ∀ v, α v) :
    ∑ c ∈ agreeOn Rᶜ w, p.margAt T c = p.margAt (T \ R) w := by
  rw [p.margAt_eq_sum_margAt (sdiff_subset (s := T) (t := R)) w, sdiff_sdiff_right_self,
    inter_eq_right.2 hRT]

end FiniteDist

end CausalInference
