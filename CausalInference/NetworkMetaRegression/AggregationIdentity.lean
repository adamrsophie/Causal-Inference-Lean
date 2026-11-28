/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.Model

/-!
# Aggregation bias on the identity link

The **aggregation bias** of arm `k` under a covariate law `F` is the difference between the
aggregate mean `∫ g⁻¹(η_k(x)) F(dx)` and the plug in value `g⁻¹(η_k(x̄))` at the covariate mean
(`MultilevelModel.aggBias`). It is the error of fitting an aggregate study with the individual
level model evaluated at the mean covariate, the ecological bias of Zeger, Liang and Albert.

## Main results

* `MultilevelModel.armMean_id`, `MultilevelModel.aggBias_id`: on the identity link the aggregate
  mean is `η_k(x̄)` and the aggregation bias is zero, for every law with integrable coordinates.
* `exists_affine_of_combination`: a function that commutes with every two point convex
  combination of a set of reals is affine there.
* `MultilevelModel.affine_of_aggBias_eq_zero`: conversely, if the bias of arm `k` vanishes for
  every probability law supported on a set `S` of covariates, then `g⁻¹` is affine on the image
  `η_k(S)`. No continuity of `g⁻¹` and no convexity of `S` are needed: the laws with two atoms of
  masses `1 - t` and `t` reach every convex combination.

## References

* S. L. Zeger, K.-Y. Liang and P. S. Albert, *Models for longitudinal data: a generalized
  estimating equation approach*, Biometrics 44 (1988).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory IndirectComparison NetworkMetaAnalysis

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-- The **aggregation bias** of arm `k`: aggregate mean minus the plug in value at the covariate
mean. -/
noncomputable def aggBias (ginv : ℝ → ℝ) (M : MultilevelModel J K p) (α : ℝ)
    (F : Measure (Fin p → ℝ)) (k : K) : ℝ :=
  M.armMean ginv α F k - ginv (M.eta α k (covMean F))

/-- The integral of the linear predictor is the linear predictor at the covariate mean. -/
theorem integral_eta (M : MultilevelModel J K p) (α : ℝ) {F : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure F] (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (k : K) :
    ∫ x, M.eta α k x ∂F = M.eta α k (covMean F) := by
  simp only [eta_eq_predictor]
  exact AnchoredModel.integral_anchoredPredictor hF _ _ _ _ |>.trans
    (by rw [AnchoredModel.predictor, anchoredPredictor]; simp only [atBaseline]
        simp only [covMean, dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring)

/-- **Identity link: the aggregate mean is the predictor at the covariate mean.** -/
theorem armMean_id (M : MultilevelModel J K p) (α : ℝ) {F : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure F] (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (k : K) :
    M.armMean id α F k = M.eta α k (covMean F) :=
  M.integral_eta α hF k

/-- **Identity link: no aggregation bias**, for every probability law with integrable
coordinates. -/
theorem aggBias_id (M : MultilevelModel J K p) (α : ℝ) {F : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure F] (hF : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F) (k : K) :
    M.aggBias id α F k = 0 := by
  rw [aggBias, armMean_id M α hF, id, sub_self]

end MultilevelModel

/-- **Commuting with two point combinations forces affinity.** If
`ψ((1 - t)w₁ + t w₂) = (1 - t)ψ(w₁) + tψ(w₂)` for all `w₁, w₂ ∈ T` and `t ∈ [0, 1]`, then `ψ` is
affine on `T`. -/
theorem exists_affine_of_combination {T : Set ℝ} {ψ : ℝ → ℝ}
    (h : ∀ w₁ ∈ T, ∀ w₂ ∈ T, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ψ ((1 - t) * w₁ + t * w₂) = (1 - t) * ψ w₁ + t * ψ w₂) :
    ∃ u v : ℝ, ∀ w ∈ T, ψ w = u + v * w := by
  by_cases hT : ∃ w₁ ∈ T, ∃ w₂ ∈ T, w₁ ≠ w₂
  · obtain ⟨w₁, h₁, w₂, h₂, hne⟩ := hT
    have hd : w₂ - w₁ ≠ 0 := sub_ne_zero.mpr hne.symm
    refine ⟨ψ w₁ - (ψ w₂ - ψ w₁) / (w₂ - w₁) * w₁, (ψ w₂ - ψ w₁) / (w₂ - w₁), fun w hw => ?_⟩
    set t := (w - w₁) / (w₂ - w₁) with ht
    have hw_eq : w = (1 - t) * w₁ + t * w₂ := by
      rw [ht]; field_simp; ring
    suffices hgoal : ψ w = (1 - t) * ψ w₁ + t * ψ w₂ by
      rw [hgoal, ht]; field_simp; ring
    rcases le_or_gt 0 t with h0 | h0
    · rcases le_or_gt t 1 with h1 | h1
      · have := h w₁ h₁ w₂ h₂ t h0 h1
        rwa [← hw_eq] at this
      · have hs0 : 0 ≤ 1 / t := by positivity
        have hs1 : 1 / t ≤ 1 := by rw [div_le_one (by linarith)]; linarith
        have := h w₁ h₁ w hw (1 / t) hs0 hs1
        have hw2 : (1 - 1 / t) * w₁ + 1 / t * w = w₂ := by
          rw [hw_eq]; field_simp; ring
        rw [hw2] at this
        have htne : t ≠ 0 := by linarith
        field_simp at this
        linarith
    · have h1t : 0 < 1 - t := by linarith
      have hne1 : 1 - t ≠ 0 := h1t.ne'
      set s := -t / (1 - t) with hs
      have hs0 : 0 ≤ s := by rw [hs]; apply div_nonneg <;> linarith
      have hs1 : s ≤ 1 := by rw [hs, div_le_one h1t]; linarith
      have := h w hw w₂ h₂ s hs0 hs1
      have hw1 : (1 - s) * w + s * w₂ = w₁ := by
        rw [hw_eq, hs]; field_simp; ring
      rw [hw1, hs] at this
      field_simp at this
      linarith
  · push Not at hT
    by_cases hne : T.Nonempty
    · obtain ⟨w₀, h₀⟩ := hne
      exact ⟨ψ w₀, 0, fun w hw => by rw [hT w hw w₀ h₀]; ring⟩
    · exact ⟨0, 0, fun w hw => absurd ⟨w, hw⟩ hne⟩

/-- The law with atoms `x₁` and `x₂` of masses `1 - t` and `t`. -/
noncomputable def twoAtomLaw {p : ℕ} (x₁ x₂ : Fin p → ℝ) (t : ℝ) : Measure (Fin p → ℝ) :=
  ENNReal.ofReal (1 - t) • Measure.dirac x₁ + ENNReal.ofReal t • Measure.dirac x₂

section TwoAtom

variable {p : ℕ} {x₁ x₂ : Fin p → ℝ} {t : ℝ}

theorem isProbabilityMeasure_twoAtomLaw (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (twoAtomLaw x₁ x₂ t) := by
  constructor
  simp only [twoAtomLaw, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) ht0]
  simp

theorem integrable_twoAtomLaw (g : (Fin p → ℝ) → ℝ) : Integrable g (twoAtomLaw x₁ x₂ t) :=
  ((integrable_dirac (by simp)).smul_measure (by simp)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by simp))

theorem integral_twoAtomLaw (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (g : (Fin p → ℝ) → ℝ) :
    ∫ x, g x ∂twoAtomLaw x₁ x₂ t = (1 - t) * g x₁ + t * g x₂ := by
  rw [twoAtomLaw, integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
    ((integrable_dirac (by simp)).smul_measure (by simp)), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - t), ENNReal.toReal_ofReal ht0]

theorem ae_twoAtomLaw {S : Set (Fin p → ℝ)} (h₁ : x₁ ∈ S) (h₂ : x₂ ∈ S) :
    ∀ᵐ x ∂twoAtomLaw x₁ x₂ t, x ∈ S := by
  rw [twoAtomLaw, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact h₁) _,
    Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact h₂) _⟩

end TwoAtom

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-- **Only an affine inverse link has no aggregation bias.** If the aggregation bias of arm `k`
is zero under every probability law supported on `S` with integrable coordinates and integrable
`g⁻¹(η_k)`, then `g⁻¹` is affine on `η_k(S)`. -/
theorem affine_of_aggBias_eq_zero {ginv : ℝ → ℝ} (M : MultilevelModel J K p) (α : ℝ) (k : K)
    {S : Set (Fin p → ℝ)}
    (h : ∀ F : Measure (Fin p → ℝ), IsProbabilityMeasure F → (∀ᵐ x ∂F, x ∈ S) →
      (∀ i, Integrable (fun x : Fin p → ℝ => x i) F) →
      Integrable (M.surface ginv α k) F → M.aggBias ginv α F k = 0) :
    ∃ u v : ℝ, ∀ x ∈ S, ginv (M.eta α k x) = u + v * M.eta α k x := by
  have key : ∀ w₁ ∈ M.eta α k '' S, ∀ w₂ ∈ M.eta α k '' S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ginv ((1 - t) * w₁ + t * w₂) = (1 - t) * ginv w₁ + t * ginv w₂ := by
    rintro _ ⟨x₁, hx₁, rfl⟩ _ ⟨x₂, hx₂, rfl⟩ t ht0 ht1
    have hprob := isProbabilityMeasure_twoAtomLaw (x₁ := x₁) (x₂ := x₂) ht0 ht1
    have := h _ hprob (ae_twoAtomLaw hx₁ hx₂) (fun _ => integrable_twoAtomLaw _)
      (integrable_twoAtomLaw _)
    rw [aggBias, sub_eq_zero, armMean, integral_twoAtomLaw ht0 ht1] at this
    have hmean : covMean (twoAtomLaw x₁ x₂ t) = fun j => (1 - t) * x₁ j + t * x₂ j :=
      funext fun j => integral_twoAtomLaw ht0 ht1 (fun x => x j)
    have hη : M.eta α k (fun j => (1 - t) * x₁ j + t * x₂ j) =
        (1 - t) * M.eta α k x₁ + t * M.eta α k x₂ := by
      simp only [eta_eq_affine, dotProduct, add_mul, Finset.sum_add_distrib, mul_assoc,
        ← Finset.mul_sum]
      ring
    rw [hmean, hη] at this
    exact this.symm
  obtain ⟨u, v, huv⟩ := exists_affine_of_combination key
  exact ⟨u, v, fun x hx => huv _ ⟨x, hx, rfl⟩⟩

end MultilevelModel

end NetworkMetaRegression

end CausalInference
