/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.IncrementAffine

/-!
# The range of the predictor in the misaligned anchored comparison

`exists_anchoredEstimand_ne_of_not_affine` shows that, on a reporting scale `h` with
`ψ = h ∘ g⁻¹` not affine on an order connected set `I` of predictor values, some anchored
comparison of the shift model differs from the target conditional effect on the scale `h`. This
file shows that the order connected hypothesis cannot be dropped, and records that the identity,
log and logit links reach every predictor value.

* **The three point set** `I = {0, 1, 3}` is not order connected, and `ψ(η) = η²` is not affine
  on `I` (`sq_not_affine_on_zeroOneThree`).
* **Every increment on `I` is determined by its shift** (`sq_sub_eq_of_mem_zeroOneThree`): if
  `η₁, η₁ + γ, η₂, η₂ + γ ∈ I`, then `(η₁ + γ)² - η₁² = (η₂ + γ)² - η₂²`, because each nonzero
  difference of two elements of `I` is attained by one ordered pair only.
* **So the anchored comparison on the squared scale is correct** whenever the predictors of the
  shift model lie in `I` (`anchoredEstimand_sq_eq_of_mem_zeroOneThree`), with the identity link:
  the conclusion of `exists_anchoredEstimand_ne_of_not_affine` fails although `ψ` is not affine
  on `I` (`orderConnected_needed`).
* **The links reach every predictor value**: `Real.log '' (0, ∞) = ℝ` (`log_image_Ioi`); the
  logit case is `logit_image_Ioo` and the identity case is `Set.image_univ` with
  `Set.image_id`.

## Main definitions

* `zeroOneThree`.

## Main results

* `sq_not_affine_on_zeroOneThree`, `not_ordConnected_zeroOneThree`,
  `sq_sub_eq_of_mem_zeroOneThree`, `anchoredEstimand_sq_eq_of_mem_zeroOneThree`,
  `orderConnected_needed`, `log_image_Ioi`.
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory Set EffectMeasure

/-- The set `{0, 1, 3}` of predictor values. -/
def zeroOneThree : Set ℝ := {0, 1, 3}

/-- **`η ↦ η²` is not affine on `{0, 1, 3}`**: an affine function through `(0, 0)` and `(1, 1)`
takes the value `3` at `3`, not `9`. -/
theorem sq_not_affine_on_zeroOneThree :
    ¬ ∃ k l : ℝ, ∀ η ∈ zeroOneThree, η ^ 2 = k * η + l := by
  rintro ⟨k, l, h⟩
  have h0 := h 0 (by simp [zeroOneThree])
  have h1 := h 1 (by simp [zeroOneThree])
  have h3 := h 3 (by simp [zeroOneThree])
  norm_num at h0 h1 h3
  linarith

/-- `{0, 1, 3}` is not order connected: it contains `1` and `3` but not `2`. -/
theorem not_ordConnected_zeroOneThree : ¬ zeroOneThree.OrdConnected := fun h => by
  have h2 := h.out (show (1 : ℝ) ∈ zeroOneThree by simp [zeroOneThree])
    (show (3 : ℝ) ∈ zeroOneThree by simp [zeroOneThree]) (show (2 : ℝ) ∈ Icc 1 3 by norm_num)
  norm_num [zeroOneThree] at h2

/-- **On `{0, 1, 3}` the increments of `η ↦ η²` depend only on the shift**: if
`η₁, η₁ + γ, η₂, η₂ + γ ∈ {0, 1, 3}`, then `(η₁ + γ)² - η₁² = (η₂ + γ)² - η₂²`. -/
theorem sq_sub_eq_of_mem_zeroOneThree {η₁ η₂ γ : ℝ} (h1 : η₁ ∈ zeroOneThree)
    (h1' : η₁ + γ ∈ zeroOneThree) (h2 : η₂ ∈ zeroOneThree) (h2' : η₂ + γ ∈ zeroOneThree) :
    (η₁ + γ) ^ 2 - η₁ ^ 2 = (η₂ + γ) ^ 2 - η₂ ^ 2 := by
  obtain ⟨u, hu, rfl⟩ : ∃ u ∈ zeroOneThree, γ = u - η₁ := ⟨η₁ + γ, h1', by ring⟩
  simp only [zeroOneThree, mem_insert_iff, mem_singleton_iff] at h1 hu h2 h2'
  rcases h1 with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl <;> norm_num at h2' <;> norm_num

/-- **The anchored comparison on the squared scale is correct on `{0, 1, 3}`.** For the shift
model with the identity link, if its predictors at `x₁` and at `x₂` lie in `{0, 1, 3}`, the
anchored comparison on the scale `h(m) = m²`, with both trials at `x₁`, equals the target average
conditional effect at `x₂` on that scale. -/
theorem anchoredEstimand_sq_eq_of_mem_zeroOneThree (γ : ℝ) (x₁ x₂ : Fin 1 → ℝ)
    (hI : ∀ t, (shiftModel γ).predictor t x₁ ∈ zeroOneThree ∧
      (shiftModel γ).predictor t x₂ ∈ zeroOneThree) :
    anchoredEstimand (Measure.dirac x₁)
        (linkContrast (· ^ 2) ((shiftModel γ).condMean id 1) ((shiftModel γ).condMean id 0))
        (linkContrast (· ^ 2) ((shiftModel γ).condMean id 2) ((shiftModel γ).condMean id 0)) =
      linkConditional (· ^ 2) (Measure.dirac x₂) ((shiftModel γ).condMean id 1)
        ((shiftModel γ).condMean id 2) := by
  have h1 := (hI 1).1
  have h1' := (hI 2).1
  have h2 := (hI 1).2
  have h2' := (hI 2).2
  simp only [shiftModel_predictor] at h1 h1' h2 h2'
  simp only [anchoredEstimand, linkConditional, linkContrast, integral_dirac,
    AnchoredModel.condMean, shiftModel_predictor, id]
  norm_num at h1 h1' h2 h2' ⊢
  linarith [sq_sub_eq_of_mem_zeroOneThree h1 h1' h2 h2']

/-- **The order connected hypothesis of `exists_anchoredEstimand_ne_of_not_affine` is needed.**
For `I = {0, 1, 3}`, the identity link and the reporting scale `h(m) = m²`, the function
`ψ = h ∘ id` is not affine on `I`, but no shift `γ` and covariate values `x₁, x₂` with all
predictors of the shift model in `I` give an anchored comparison on the scale `h` that differs from
the target average conditional effect. The hypothesis that fails is that `I` is order
connected. -/
theorem orderConnected_needed :
    ¬ zeroOneThree.OrdConnected ∧
      (¬ ∃ k l : ℝ, ∀ η ∈ zeroOneThree, id η ^ 2 = k * η + l) ∧
      ¬ ∃ (γ : ℝ) (x₁ x₂ : Fin 1 → ℝ),
        (∀ t, (shiftModel γ).predictor t x₁ ∈ zeroOneThree ∧
          (shiftModel γ).predictor t x₂ ∈ zeroOneThree) ∧
        anchoredEstimand (Measure.dirac x₁)
            (linkContrast (· ^ 2) ((shiftModel γ).condMean id 1) ((shiftModel γ).condMean id 0))
            (linkContrast (· ^ 2) ((shiftModel γ).condMean id 2)
              ((shiftModel γ).condMean id 0)) ≠
          linkConditional (· ^ 2) (Measure.dirac x₂) ((shiftModel γ).condMean id 1)
            ((shiftModel γ).condMean id 2) :=
  ⟨not_ordConnected_zeroOneThree, sq_not_affine_on_zeroOneThree,
    fun ⟨γ, x₁, x₂, hI, hne⟩ => hne (anchoredEstimand_sq_eq_of_mem_zeroOneThree γ x₁ x₂ hI)⟩

/-- **The log link reaches every predictor value**: `Real.log '' (0, ∞) = ℝ`. -/
theorem log_image_Ioi : Real.log '' Ioi 0 = univ :=
  eq_univ_of_forall fun t => ⟨Real.exp t, Real.exp_pos t, Real.log_exp t⟩

end IndirectComparison

end CausalInference
