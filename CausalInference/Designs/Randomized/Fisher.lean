/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.Randomized.FinitePopulation

/-!
# Fisher randomization tests under the sharp null

Fisher's sharp null hypothesis states that treatment has no effect on any unit: `y1 i = y0 i`
for all `i`. Under it the observed outcome vector is the same for every assignment, so the
value a test statistic would take under any other assignment can be computed from the observed
data, and the randomization distribution of the statistic is known exactly. The randomization
p-value `p(a) = P_{a'}(T(a') ≥ T(a))` is then valid: `P(p ≤ α) ≤ α` for every `α ≥ 0`.
Sources: Fisher (1935), *The Design of Experiments*; Imbens and Rubin (2015), *Causal Inference
for Statistics, Social, and Biomedical Sciences*.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `PotentialOutcomes.SharpNull`: Fisher's sharp null of no effect for any unit.
* `Design.pValue`: the upper-tail randomization p-value of a function of the
  assignment.
* `Design.fisherPValue`: the randomization p-value of a test statistic
  computed from an observed outcome vector, imputing that vector for every assignment.

## Main results

* `PotentialOutcomes.observed_eq_of_sharpNull`: under the sharp null the
  observed outcomes do not depend on the assignment.
* `PotentialOutcomes.statistic_eq_imputed_of_sharpNull`: under the sharp null the
  statistic under any assignment equals its value imputed from the observed data.
* `Design.prob_pValue_le`: the upper-tail p-value of any function of the
  assignment is valid under any design.
* `fisher_pValue_valid`: validity of the Fisher randomization test under the
  sharp null, for any design.
* `fisher_pValue_valid_uniform`: the same for the uniform design on a finite
  nonempty set of assignments, with the p-value written as a proportion.
-/

@[expose] public section

namespace CausalInference.Randomized

open Finset

variable {ι : Type*}

namespace PotentialOutcomes

/-- Fisher's sharp null hypothesis: treatment has no effect on any unit, `y1 i = y0 i`. -/
def SharpNull (po : PotentialOutcomes ι) : Prop := ∀ i, po.y1 i = po.y0 i

/-- Under the sharp null the observed outcome vector equals `y0` for every assignment. -/
theorem observed_eq_of_sharpNull {po : PotentialOutcomes ι} (h : po.SharpNull)
    (a : ι → Bool) : po.observed a = po.y0 := by
  funext i
  unfold observed
  split_ifs
  · exact h i
  · rfl

/-- Under the sharp null the observed outcome vector does not depend on the assignment. -/
theorem observed_indep_of_sharpNull {po : PotentialOutcomes ι} (h : po.SharpNull)
    (a a' : ι → Bool) : po.observed a = po.observed a' := by
  rw [observed_eq_of_sharpNull h, observed_eq_of_sharpNull h]

/-- Under the sharp null the value of a test statistic `T` under any assignment `a'`, which
depends on the outcomes observed under `a'`, equals the value imputed from the outcomes
observed under the realized assignment `a`. Hence the randomization distribution of `T` is
known from the observed data. -/
theorem statistic_eq_imputed_of_sharpNull {po : PotentialOutcomes ι} (h : po.SharpNull)
    (T : (ι → Bool) → (ι → ℝ) → ℝ) (a a' : ι → Bool) :
    T a' (po.observed a') = T a' (po.observed a) := by
  rw [observed_indep_of_sharpNull h a' a]

end PotentialOutcomes

namespace Design

/-- The upper-tail randomization p-value of a function `t` of the assignment at the realized
assignment `a`: the probability over the design that `t (a') ≥ t (a)`. -/
noncomputable def pValue (d : Design ι) (t : (ι → Bool) → ℝ) (a : ι → Bool) : ℝ :=
  d.prob fun a' => t a ≤ t a'

/-- The Fisher randomization p-value of a test statistic `T`, computed from the realized
assignment `a` and the observed outcome vector `y` by imputing `y` under every assignment:
the probability over the design that `T a' y ≥ T a y`. -/
noncomputable def fisherPValue (d : Design ι) (T : (ι → Bool) → (ι → ℝ) → ℝ) (y : ι → ℝ)
    (a : ι → Bool) : ℝ :=
  d.prob fun a' => T a y ≤ T a' y

/-- **Validity of the upper-tail p-value.** For any design and any real function `t` of the
assignment, the p-value `p(a) = P_{a'}(t a' ≥ t a)` satisfies `P(p ≤ α) ≤ α` for every
`α ≥ 0`. -/
theorem prob_pValue_le (d : Design ι) (t : (ι → Bool) → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    d.prob (fun a => d.pValue t a ≤ α) ≤ α := by
  set A := d.support.filter fun a => d.pValue t a ≤ α
  rcases A.eq_empty_or_nonempty with hA | hA
  · have h0 : d.prob (fun a => d.pValue t a ≤ α) = 0 := by
      unfold prob
      rw [d.expect_congr (g := fun _ => 0) fun a ha => ?_, d.expect_const]
      have : a ∉ A := by simp [hA]
      simp only [A, mem_filter, not_and] at this
      simp [this ha]
    rw [h0]
    exact hα
  · obtain ⟨b, hbA, hmin⟩ := A.exists_min_image t hA
    have hb : d.pValue t b ≤ α := (mem_filter.mp hbA).2
    calc d.prob (fun a => d.pValue t a ≤ α)
        ≤ d.prob (fun a => t b ≤ t a) :=
          d.prob_mono fun a ha hpa => hmin a (mem_filter.mpr ⟨ha, hpa⟩)
      _ = d.pValue t b := rfl
      _ ≤ α := hb

/-- Under the uniform design on `S`, the probability of an event is the proportion of
assignments in `S` satisfying it. -/
theorem uniform_prob (S : Finset (ι → Bool)) (hS : S.Nonempty) (P : (ι → Bool) → Prop)
    [DecidablePred P] : (uniform S hS).prob P = (#{a ∈ S | P a} : ℝ) / #S := by
  rw [prob, uniform_expect, natCast_card_filter, div_eq_inv_mul]

end Design

/-- **Validity of the Fisher randomization test.** Under Fisher's sharp null, for any design
and any test statistic `T`, the randomization p-value computed from the observed data,
`p(a) = P_{a'}(T a' Y(a) ≥ T a Y(a))` with `Y(a)` the outcomes observed under `a`, satisfies
`P(p ≤ α) ≤ α` for every `α ≥ 0`. -/
theorem fisher_pValue_valid (po : PotentialOutcomes ι) (hnull : po.SharpNull) (d : Design ι)
    (T : (ι → Bool) → (ι → ℝ) → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    d.prob (fun a => d.fisherPValue T (po.observed a) a ≤ α) ≤ α := by
  simp only [PotentialOutcomes.observed_eq_of_sharpNull hnull]
  exact d.prob_pValue_le (fun a => T a po.y0) hα

/-- **Validity of the Fisher randomization test, uniform design.** Under Fisher's sharp null,
for the uniform design on a finite nonempty set `S` of assignments and any test statistic `T`,
the p-value `p(a) = #{a' ∈ S | T a' Y(a) ≥ T a Y(a)} / #S` satisfies
`#{a ∈ S | p(a) ≤ α} / #S ≤ α` for every `α ≥ 0`. -/
theorem fisher_pValue_valid_uniform (po : PotentialOutcomes ι) (hnull : po.SharpNull)
    (S : Finset (ι → Bool)) (hS : S.Nonempty) (T : (ι → Bool) → (ι → ℝ) → ℝ) {α : ℝ}
    (hα : 0 ≤ α) :
    (#{a ∈ S | (#{a' ∈ S | T a (po.observed a) ≤ T a' (po.observed a)} : ℝ) / #S ≤ α} : ℝ) /
      #S ≤ α := by
  have := fisher_pValue_valid po hnull (Design.uniform S hS) T hα
  simp only [Design.fisherPValue, Design.uniform_prob] at this
  exact this

end CausalInference.Randomized
