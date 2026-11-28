/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.Constancy

/-!
# Constancy of a triangle of contrasts: any two give the third

For three treatments `a, b, c` the contrasts of one population satisfy
`d_ab = d_ac - d_bc` (`Population.marginalEffect_eq_sub`). Hence, between two populations, any
two of the three contrasts being equal forces the third to be equal. The direction from
`(a, c)` and `(b, c)` to `(a, b)` is `marginalEffect_eq_of_two`; this file adds the other two
directions and the corresponding statements for `ConstantRelativeEffects` across a family of
populations: constancy of any two of the pairs `(a, b)`, `(a, c)`, `(b, c)` is constancy of all
three.

## Main results

* `marginalEffect_ac_eq_of_two`: equal `d_ab` and `d_bc` give equal `d_ac`.
* `marginalEffect_bc_eq_of_two`: equal `d_ab` and `d_ac` give equal `d_bc`.
* `constantRelativeEffects_triangle_of_ac_bc`, `constantRelativeEffects_triangle_of_ab_bc`,
  `constantRelativeEffects_triangle_of_ab_ac`: constancy of two pairs is constancy of the
  triangle.

## References

* H. C. Bucher, G. H. Guyatt, L. E. Griffith and S. D. Walter, *The results of direct and
  indirect treatment comparisons in meta-analysis of randomized controlled trials*, Journal of
  Clinical Epidemiology 50 (1997).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

variable {J ι 𝒳 : Type*} {Ω : J → Type*} [∀ j, MeasurableSpace (Ω j)] {g : ℝ → ℝ}
  {P : ∀ j, Population (Ω j) 𝒳 ι} {a b c : ι}

/-- **Equal `d_ab` and `d_bc` give equal `d_ac`**: `d_ac = d_ab + d_bc` in each population. -/
theorem marginalEffect_ac_eq_of_two (j j' : J)
    (hab : (P j).marginalEffect g a b = (P j').marginalEffect g a b)
    (hbc : (P j).marginalEffect g b c = (P j').marginalEffect g b c) :
    (P j).marginalEffect g a c = (P j').marginalEffect g a c := by
  have e := (P j).marginalEffect_eq_sub (g := g) a b c
  have e' := (P j').marginalEffect_eq_sub (g := g) a b c
  linarith

/-- **Equal `d_ab` and `d_ac` give equal `d_bc`**: `d_bc = d_ac - d_ab` in each population. -/
theorem marginalEffect_bc_eq_of_two (j j' : J)
    (hab : (P j).marginalEffect g a b = (P j').marginalEffect g a b)
    (hac : (P j).marginalEffect g a c = (P j').marginalEffect g a c) :
    (P j).marginalEffect g b c = (P j').marginalEffect g b c := by
  have e := (P j).marginalEffect_eq_sub (g := g) a b c
  have e' := (P j').marginalEffect_eq_sub (g := g) a b c
  linarith

/-- Constancy on a set of pairs, read off at one pair. -/
private theorem constantRelativeEffects_pair {S : Set (ι × ι)}
    (h : ConstantRelativeEffects g P S) {p : ι × ι} (hp : p ∈ S) (j j' : J) :
    (P j).marginalEffect g p.1 p.2 = (P j').marginalEffect g p.1 p.2 :=
  h p hp j j'

/-- Constancy of the three pairs of a triangle from the three pairwise equalities. -/
private theorem constantRelativeEffects_triangle_of_forall
    (hab : ∀ j j', (P j).marginalEffect g a b = (P j').marginalEffect g a b)
    (hac : ∀ j j', (P j).marginalEffect g a c = (P j').marginalEffect g a c)
    (hbc : ∀ j j', (P j).marginalEffect g b c = (P j').marginalEffect g b c) :
    ConstantRelativeEffects g P {(a, b), (a, c), (b, c)} := by
  intro p hp j j'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact hab j j'
  · exact hac j j'
  · exact hbc j j'

/-- **Constancy of `d_ac` and `d_bc` is constancy of the triangle.** -/
theorem constantRelativeEffects_triangle_of_ac_bc
    (h : ConstantRelativeEffects g P {(a, c), (b, c)}) :
    ConstantRelativeEffects g P {(a, b), (a, c), (b, c)} := by
  have hac := constantRelativeEffects_pair h (p := (a, c)) (by simp)
  have hbc := constantRelativeEffects_pair h (p := (b, c)) (by simp)
  exact constantRelativeEffects_triangle_of_forall
    (fun j j' => marginalEffect_eq_of_two j j' (hac j j') (hbc j j')) hac hbc

/-- **Constancy of `d_ab` and `d_bc` is constancy of the triangle.** -/
theorem constantRelativeEffects_triangle_of_ab_bc
    (h : ConstantRelativeEffects g P {(a, b), (b, c)}) :
    ConstantRelativeEffects g P {(a, b), (a, c), (b, c)} := by
  have hab := constantRelativeEffects_pair h (p := (a, b)) (by simp)
  have hbc := constantRelativeEffects_pair h (p := (b, c)) (by simp)
  exact constantRelativeEffects_triangle_of_forall hab
    (fun j j' => marginalEffect_ac_eq_of_two j j' (hab j j') (hbc j j')) hbc

/-- **Constancy of `d_ab` and `d_ac` is constancy of the triangle.** -/
theorem constantRelativeEffects_triangle_of_ab_ac
    (h : ConstantRelativeEffects g P {(a, b), (a, c)}) :
    ConstantRelativeEffects g P {(a, b), (a, c), (b, c)} := by
  have hab := constantRelativeEffects_pair h (p := (a, b)) (by simp)
  have hac := constantRelativeEffects_pair h (p := (a, c)) (by simp)
  exact constantRelativeEffects_triangle_of_forall hab hac
    (fun j j' => marginalEffect_bc_eq_of_two j j' (hab j j') (hac j j'))

end IndirectComparison

end CausalInference
