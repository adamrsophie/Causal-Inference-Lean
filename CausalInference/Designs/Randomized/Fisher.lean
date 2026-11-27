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
p-value `p(a) = P_{a'}(T(a') ≥ T(a))` is then valid: `P(p ≤ α) ≤ α` for every `α ≥ 0`. The
same holds for the general sharp null `y1 i = y0 i + τ i` after imputing the missing outcomes,
and inverting the tests of constant additive effects gives a confidence set with coverage at
least `1 - α`.
Sources: Fisher (1935), *The Design of Experiments*; Imbens and Rubin (2015), *Causal Inference
for Statistics, Social, and Biomedical Sciences*.

## Main definitions

All declarations live in the namespace `CausalInference.Randomized`.

* `PotentialOutcomes.SharpNull`: Fisher's sharp null of no effect for any unit.
* `Design.pValue`: the upper-tail randomization p-value of a function of the
  assignment.
* `Design.fisherPValue`: the randomization p-value of a test statistic
  computed from an observed outcome vector, imputing that vector for every assignment.
* `PotentialOutcomes.SharpNullAt`: the general sharp null `y1 i = y0 i + τ i`.
* `impute`: the outcomes imputed under hypothesized unit effects.
* `Design.fisherPValueAt`: the randomization p-value of a general sharp null.
* `Design.constEffectConfSet`: the confidence set for a constant additive effect obtained by
  inverting Fisher tests.

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
* `PotentialOutcomes.impute_observed`: under a general sharp null, imputation recovers the
  outcomes observed under every assignment.
* `fisher_pValueAt_valid`: validity of the Fisher test of a general sharp null.
* `constEffectConfSet_coverage`: under a constant additive effect `c`, the test-inversion
  confidence set contains `c` with probability at least `1 - α`.
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

/-! ### General sharp nulls and test inversion -/

namespace PotentialOutcomes

/-- The general sharp null hypothesis with unit effects `τ`: `y1 i = y0 i + τ i` for every unit.
It fixes both potential outcomes of every unit given the observed one. -/
def SharpNullAt (po : PotentialOutcomes ι) (τ : ι → ℝ) : Prop := ∀ i, po.y1 i = po.y0 i + τ i

/-- Fisher's sharp null of no effect is the general sharp null with `τ = 0`. -/
theorem sharpNull_iff_sharpNullAt_zero (po : PotentialOutcomes ι) :
    po.SharpNull ↔ po.SharpNullAt 0 := by
  simp [SharpNull, SharpNullAt]

end PotentialOutcomes

/-- The outcomes imputed under the hypothesized unit effects `τ`: from the outcomes `y`
observed under the realized assignment `a`, the outcome of unit `i` under the assignment `a'`
is `y i + (A'_i - A_i) τ i`. -/
def impute (τ : ι → ℝ) (a : ι → Bool) (y : ι → ℝ) (a' : ι → Bool) (i : ι) : ℝ :=
  y i + (treatInd a' i - treatInd a i) * τ i

/-- Under the sharp null with unit effects `τ`, imputation from the outcomes observed under
`a` recovers the outcomes that would be observed under any other assignment `a'`. -/
theorem PotentialOutcomes.impute_observed {po : PotentialOutcomes ι} {τ : ι → ℝ}
    (h : po.SharpNullAt τ) (a a' : ι → Bool) :
    impute τ a (po.observed a) a' = po.observed a' := by
  funext i
  unfold impute PotentialOutcomes.observed treatInd
  cases ha : a i <;> cases ha' : a' i <;> simp [h i]

/-- The randomization p-value of a test statistic `T` for the sharp null with unit effects
`τ`, computed from the realized assignment `a` and the observed outcome vector `y`: the
probability over the design that `T a' (imputed outcomes under a') ≥ T a y`. -/
noncomputable def Design.fisherPValueAt (d : Design ι) (T : (ι → Bool) → (ι → ℝ) → ℝ)
    (τ : ι → ℝ) (y : ι → ℝ) (a : ι → Bool) : ℝ :=
  d.prob fun a' => T a y ≤ T a' (impute τ a y a')

/-- **Validity of the Fisher test of a general sharp null.** Under the sharp null with unit
effects `τ`, for any design and any test statistic `T`, the randomization p-value computed
from the observed data by imputation satisfies `P(p ≤ α) ≤ α` for every `α ≥ 0`. -/
theorem fisher_pValueAt_valid (po : PotentialOutcomes ι) {τ : ι → ℝ} (hnull : po.SharpNullAt τ)
    (d : Design ι) (T : (ι → Bool) → (ι → ℝ) → ℝ) {α : ℝ} (hα : 0 ≤ α) :
    d.prob (fun a => d.fisherPValueAt T τ (po.observed a) a ≤ α) ≤ α := by
  simp only [Design.fisherPValueAt, PotentialOutcomes.impute_observed hnull]
  exact d.prob_pValue_le (fun a => T a (po.observed a)) hα

/-- The confidence set for a constant additive effect obtained by inverting Fisher tests: the
values `c` for which the sharp null `y1 = y0 + c` is not rejected at level `α`, that is,
whose randomization p-value exceeds `α`. -/
noncomputable def Design.constEffectConfSet (d : Design ι) (T : (ι → Bool) → (ι → ℝ) → ℝ)
    (α : ℝ) (y : ι → ℝ) (a : ι → Bool) : Set ℝ :=
  {c | α < d.fisherPValueAt T (fun _ => c) y a}

open scoped Classical in
/-- **Coverage of the test-inversion confidence set.** If the treatment effect is constant,
`y1 i = y0 i + c` for every unit, then for any design, any test statistic, and any `α ≥ 0`, the
confidence set obtained by inverting Fisher tests contains `c` with probability at least
`1 - α`. Membership in the set is decided classically. -/
theorem constEffectConfSet_coverage (po : PotentialOutcomes ι) {c : ℝ}
    (hc : po.SharpNullAt fun _ => c) (d : Design ι) (T : (ι → Bool) → (ι → ℝ) → ℝ) {α : ℝ}
    (hα : 0 ≤ α) :
    1 - α ≤ d.prob (fun a => c ∈ d.constEffectConfSet T α (po.observed a) a) := by
  have hv := fisher_pValueAt_valid po hc d T hα
  have hcompl :=
    d.prob_compl (fun a => d.fisherPValueAt T (fun _ => c) (po.observed a) a ≤ α)
  have heq : d.prob (fun a => c ∈ d.constEffectConfSet T α (po.observed a) a) =
      d.prob (fun a => ¬ d.fisherPValueAt T (fun _ => c) (po.observed a) a ≤ α) :=
    d.expect_congr fun a _ => by
      simp only [Design.constEffectConfSet, Set.mem_ofPred_eq, not_le]
      congr
  linarith

end CausalInference.Randomized
