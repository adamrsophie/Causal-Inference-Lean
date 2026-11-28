/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Distance.Mahalanobis
public import CausalInference.IndirectComparison.SmallestNetwork

/-!
# The transport bias of a linear outcome surface

When the common regression of the outcome on the covariates `x : ℝ^p` is affine,
`g(x) = α + βᵀ x`, the transport bias of the source mean for the target mean depends on the two
covariate laws only through their means: it is `βᵀ (x̄₁ - x̄₂)`, with `x̄ᵢ = covMean Pᵢ`. By
the Cauchy and Schwarz inequality it is then bounded by a distance between the covariate
means, the standardized Euclidean distance

`|bias| ≤ ‖S β‖₂ · d_SE(x̄₂, x̄₁; s)`,   `S = diag(s)`,

and the Mahalanobis distance

`|bias| ≤ √(βᵀ Σ β) · d_M(x̄₂, x̄₁; Σ)`,

with equality exactly when the standardized gap is parallel to `S β` (respectively the gap is
parallel to `Σ β`). Each bound is stated for bare integrals over two covariate laws and then for
the transport bias of populations with a common regression, and of a transport model.

## Main results

* `integral_affine`, `integral_affine_sub`: the mean of an affine function.
* `transportBias_affine`, `TransportModel.transportBias_affine`: the linear transport bias.
* `abs_dotProduct_le_and_eq_iff`: the Cauchy and Schwarz inequality in `ℝ^p` with its
  equality case.
* `abs_integral_affine_sub_le_stdEuclidean`, `abs_transportBias_le_stdEuclidean`: the
  standardized bound.
* `abs_integral_affine_sub_le_mahalanobis`, `abs_transportBias_le_mahalanobis`: the
  Mahalanobis bound.
-/

@[expose] public section

namespace CausalInference

namespace Transport

namespace Distance

open MeasureTheory ProbabilityTheory Matrix IndirectComparison

variable {p : ℕ}

/-! ### The mean of an affine function -/

/-- The mean of an affine function is its value at the mean:
`∫ (α + βᵀ x) dP = α + βᵀ x̄` for a probability law with integrable coordinates. -/
theorem integral_affine {P : Measure (Fin p → ℝ)} [IsProbabilityMeasure P]
    (hP : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P) (α : ℝ) (β : Fin p → ℝ) :
    ∫ x, (α + β ⬝ᵥ x) ∂P = α + β ⬝ᵥ covMean P := by
  have hs : Integrable (fun x : Fin p → ℝ ↦ β ⬝ᵥ x) P := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun l _ ↦ (hP l).const_mul (β l)
  rw [integral_add (integrable_const α) hs, integral_const, probReal_univ, one_smul]
  congr 1
  simp only [dotProduct, covMean]
  rw [integral_finsetSum _ fun l _ ↦ (hP l).const_mul (β l)]
  simp only [integral_const_mul]

/-- **The difference of the means of an affine function** under two probability laws with
integrable coordinates is `βᵀ (x̄₁ - x̄₂)`: the intercept cancels. -/
theorem integral_affine_sub {P₁ P₂ : Measure (Fin p → ℝ)} [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₁)
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₂) (α : ℝ) (β : Fin p → ℝ) :
    ∫ x, (α + β ⬝ᵥ x) ∂P₁ - ∫ x, (α + β ⬝ᵥ x) ∂P₂ = β ⬝ᵥ (covMean P₁ - covMean P₂) := by
  rw [integral_affine h₁, integral_affine h₂, dotProduct_sub]
  ring

section Transport

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  {X₁ : Ω₁ → Fin p → ℝ} {X₂ : Ω₂ → Fin p → ℝ} {Y₁ : Ω₁ → ℝ} {Y₂ : Ω₂ → ℝ}

/-- **The linear transport bias.** If `x ↦ α + βᵀ x` is a common regression of the outcome on
covariates in `ℝ^p`, the outcomes are integrable and the covariate laws `Pᵢ = μᵢ ∘ Xᵢ⁻¹` have
integrable coordinates, then the transport bias of the source mean for the target mean is
`βᵀ (x̄₁ - x̄₂)`. -/
theorem transportBias_affine (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hY₁ : Integrable Y₁ μ₁) (hY₂ : Integrable Y₂ μ₂)
    (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) (μ₁.map X₁))
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) (μ₂.map X₂)) {α : ℝ} {β : Fin p → ℝ}
    (hcom : IsCommonRegression μ₁ X₁ Y₁ μ₂ X₂ Y₂ fun x ↦ α + β ⬝ᵥ x) :
    transportBias μ₁ Y₁ μ₂ Y₂ = β ⬝ᵥ (covMean (μ₁.map X₁) - covMean (μ₂.map X₂)) := by
  have : IsProbabilityMeasure (μ₁.map X₁) :=
    (Measure.isProbabilityMeasure_map_iff hX₁.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (μ₂.map X₂) :=
    (Measure.isProbabilityMeasure_map_iff hX₂.aemeasurable).2 inferInstance
  rw [(transportBias_eq_integral_sub hX₁ hX₂ hY₁ hY₂ hcom).2.2, integral_affine_sub h₁ h₂]

end Transport

/-! ### The Cauchy and Schwarz bounds -/

/-- **The Cauchy and Schwarz inequality in `ℝ^p` with its equality case**:
`|uᵀ v| ≤ ‖u‖₂ ‖v‖₂`, with equality exactly when `u = 0` or `v` is a multiple of `u`. -/
theorem abs_dotProduct_le_and_eq_iff (u v : Fin p → ℝ) :
    |u ⬝ᵥ v| ≤ √(∑ l, u l ^ 2) * √(∑ l, v l ^ 2) ∧
      (|u ⬝ᵥ v| = √(∑ l, u l ^ 2) * √(∑ l, v l ^ 2) ↔ u = 0 ∨ ∃ r : ℝ, v = r • u) := by
  have hi : inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin p)) (WithLp.toLp 2 v) = u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]
  rw [← norm_toLp_two u, ← norm_toLp_two v, ← hi]
  refine ⟨abs_real_inner_le_norm _ _, ?_⟩
  have h := (norm_inner_eq_norm_tfae ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin p))
    (WithLp.toLp 2 v)).out 1 3
  rw [Real.norm_eq_abs] at h
  rw [h]
  simp only [WithLp.toLp_eq_zero]
  simp only [← WithLp.toLp_smul, (WithLp.toLp_injective 2).eq_iff]

/-- **The standardized bound, bare form.** For positive scales `s`, the linear functional
`βᵀ (y - x)` of a gap satisfies `|βᵀ (y - x)| ≤ ‖S β‖₂ d_SE(x, y; s)`, with equality exactly
when `S β = 0` or the standardized gap is a multiple of `S β`. -/
theorem abs_dotProduct_sub_le_stdEuclidean {s : Fin p → ℝ} (hs : ∀ l, 0 < s l)
    (β x y : Fin p → ℝ) :
    |β ⬝ᵥ (y - x)| ≤ √(∑ l, (s l * β l) ^ 2) * stdEuclidean s x y ∧
      (|β ⬝ᵥ (y - x)| = √(∑ l, (s l * β l) ^ 2) * stdEuclidean s x y ↔
        (fun l ↦ s l * β l) = 0 ∨ ∃ r : ℝ, stdGap s x y = r • fun l ↦ s l * β l) := by
  have key : β ⬝ᵥ (y - x) = (fun l ↦ s l * β l) ⬝ᵥ stdGap s x y := by
    simp only [dotProduct, stdGap, Pi.sub_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    field_simp [(hs l).ne']
  rw [key, stdEuclidean, norm_toLp_two]
  exact abs_dotProduct_le_and_eq_iff _ _

/-- **The standardized bound for two covariate laws.** For an affine function
`g(x) = α + βᵀ x`, probability laws with integrable coordinates and positive scales,
`|∫ g dP₁ - ∫ g dP₂| ≤ ‖S β‖₂ d_SE(x̄₂, x̄₁; s)`, with the equality case of
`abs_dotProduct_sub_le_stdEuclidean`. -/
theorem abs_integral_affine_sub_le_stdEuclidean {P₁ P₂ : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₁)
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₂) {s : Fin p → ℝ} (hs : ∀ l, 0 < s l)
    (α : ℝ) (β : Fin p → ℝ) :
    |∫ x, (α + β ⬝ᵥ x) ∂P₁ - ∫ x, (α + β ⬝ᵥ x) ∂P₂| ≤
      √(∑ l, (s l * β l) ^ 2) * stdEuclidean s (covMean P₂) (covMean P₁) := by
  rw [integral_affine_sub h₁ h₂]
  exact (abs_dotProduct_sub_le_stdEuclidean hs _ _ _).1

/-- **The standardized bound on the transport bias.** Under an affine common regression
`x ↦ α + βᵀ x`, with integrable outcomes, covariate laws with integrable coordinates and
positive scales, `|E₁[Y₁] - E₂[Y₂]| ≤ ‖S β‖₂ d_SE(x̄₂, x̄₁; s)`, with equality exactly when
`S β = 0` or the standardized gap of the covariate means is a multiple of `S β`. -/
theorem abs_transportBias_le_stdEuclidean {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁}
    {mΩ₂ : MeasurableSpace Ω₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {X₁ : Ω₁ → Fin p → ℝ} {X₂ : Ω₂ → Fin p → ℝ} {Y₁ : Ω₁ → ℝ}
    {Y₂ : Ω₂ → ℝ} (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hY₁ : Integrable Y₁ μ₁) (hY₂ : Integrable Y₂ μ₂)
    (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) (μ₁.map X₁))
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) (μ₂.map X₂)) {α : ℝ} {β : Fin p → ℝ}
    (hcom : IsCommonRegression μ₁ X₁ Y₁ μ₂ X₂ Y₂ fun x ↦ α + β ⬝ᵥ x)
    {s : Fin p → ℝ} (hs : ∀ l, 0 < s l) :
    |transportBias μ₁ Y₁ μ₂ Y₂| ≤
        √(∑ l, (s l * β l) ^ 2) * stdEuclidean s (covMean (μ₂.map X₂)) (covMean (μ₁.map X₁)) ∧
      (|transportBias μ₁ Y₁ μ₂ Y₂| =
          √(∑ l, (s l * β l) ^ 2) * stdEuclidean s (covMean (μ₂.map X₂)) (covMean (μ₁.map X₁))
        ↔ (fun l ↦ s l * β l) = 0 ∨
          ∃ r : ℝ, stdGap s (covMean (μ₂.map X₂)) (covMean (μ₁.map X₁)) =
            r • fun l ↦ s l * β l) := by
  rw [transportBias_affine hX₁ hX₂ hY₁ hY₂ h₁ h₂ hcom]
  exact abs_dotProduct_sub_le_stdEuclidean hs _ _ _

/-- **The Mahalanobis bound, bare form.** For a positive definite `Σ`,
`|βᵀ (y - x)| ≤ √(βᵀ Σ β) d_M(x, y; Σ)`, with equality exactly when `Σ β = 0` or the gap is a
multiple of `Σ β`. Proof: `βᵀ δ = (Σ^{1/2} β)ᵀ (Σ^{-1/2} δ)`, the Cauchy and Schwarz
inequality and whitening; the equality condition is carried by the invertible `Σ^{1/2}`. -/
theorem abs_dotProduct_sub_le_mahalanobis {Sig : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef)
    (β x y : Fin p → ℝ) :
    |β ⬝ᵥ (y - x)| ≤ √(β ⬝ᵥ (Sig *ᵥ β)) * mahalanobis Sig x y ∧
      (|β ⬝ᵥ (y - x)| = √(β ⬝ᵥ (Sig *ᵥ β)) * mahalanobis Sig x y ↔
        Sig *ᵥ β = 0 ∨ ∃ r : ℝ, y - x = r • (Sig *ᵥ β)) := by
  obtain ⟨M, -, hMt, hMM, hfac⟩ := exists_sqrt_factor hSig
  have hdet := isUnit_det_of_eq_mul_transpose hSig hfac
  have hinj : Function.Injective M.mulVec :=
    mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det M).2 hdet)
  set δ := y - x with hδ
  rw [mahalanobis_eq_norm_whitened hSig hfac, norm_toLp_two]
  have h1 : β ⬝ᵥ δ = (M *ᵥ β) ⬝ᵥ (M⁻¹ *ᵥ δ) := by
    rw [mulVec_dotProduct_eq, hMt, mulVec_mulVec δ M M⁻¹, mul_nonsing_inv _ hdet, one_mulVec]
  have hSb : Sig *ᵥ β = M *ᵥ (M *ᵥ β) := by rw [mulVec_mulVec, hMM]
  have h2 : β ⬝ᵥ (Sig *ᵥ β) = ∑ l, (M *ᵥ β) l ^ 2 := by
    rw [sum_sq_eq_dotProduct, mulVec_dotProduct_eq, hMt, hSb]
  rw [h1, h2]
  refine ⟨(abs_dotProduct_le_and_eq_iff _ _).1, (abs_dotProduct_le_and_eq_iff _ _).2.trans ?_⟩
  constructor
  · rintro (h | ⟨r, hr⟩)
    · left; rw [hSb, h, mulVec_zero]
    · right
      refine ⟨r, ?_⟩
      have := congrArg (M *ᵥ ·) hr
      simp only [mulVec_mulVec δ M M⁻¹, mul_nonsing_inv _ hdet, one_mulVec, mulVec_smul] at this
      rw [hSb, this]
  · rintro (h | ⟨r, hr⟩)
    · left
      refine hinj ?_
      rw [← hSb, h, mulVec_zero]
    · right
      refine ⟨r, ?_⟩
      rw [hr, mulVec_smul, hSb, mulVec_mulVec (M *ᵥ β) M⁻¹ M, nonsing_inv_mul _ hdet, one_mulVec]

/-- **The Mahalanobis bound for two covariate laws.** For an affine `g(x) = α + βᵀ x`,
probability laws with integrable coordinates and a positive definite `Σ`,
`|∫ g dP₁ - ∫ g dP₂| ≤ √(βᵀ Σ β) d_M(x̄₂, x̄₁; Σ)`. -/
theorem abs_integral_affine_sub_le_mahalanobis {P₁ P₂ : Measure (Fin p → ℝ)}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₁)
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) P₂) {Sig : Matrix (Fin p) (Fin p) ℝ}
    (hSig : Sig.PosDef) (α : ℝ) (β : Fin p → ℝ) :
    |∫ x, (α + β ⬝ᵥ x) ∂P₁ - ∫ x, (α + β ⬝ᵥ x) ∂P₂| ≤
      √(β ⬝ᵥ (Sig *ᵥ β)) * mahalanobis Sig (covMean P₂) (covMean P₁) := by
  rw [integral_affine_sub h₁ h₂]
  exact (abs_dotProduct_sub_le_mahalanobis hSig _ _ _).1

/-- **The Mahalanobis bound on the transport bias.** Under an affine common regression
`x ↦ α + βᵀ x`, with integrable outcomes, covariate laws with integrable coordinates and a
positive definite `Σ`, `|E₁[Y₁] - E₂[Y₂]| ≤ √(βᵀ Σ β) d_M(x̄₂, x̄₁; Σ)`, with equality exactly
when `Σ β = 0` or the gap of the covariate means is a multiple of `Σ β`. -/
theorem abs_transportBias_le_mahalanobis {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁}
    {mΩ₂ : MeasurableSpace Ω₂} {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {X₁ : Ω₁ → Fin p → ℝ} {X₂ : Ω₂ → Fin p → ℝ} {Y₁ : Ω₁ → ℝ}
    {Y₂ : Ω₂ → ℝ} (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hY₁ : Integrable Y₁ μ₁) (hY₂ : Integrable Y₂ μ₂)
    (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) (μ₁.map X₁))
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) (μ₂.map X₂)) {α : ℝ} {β : Fin p → ℝ}
    (hcom : IsCommonRegression μ₁ X₁ Y₁ μ₂ X₂ Y₂ fun x ↦ α + β ⬝ᵥ x)
    {Sig : Matrix (Fin p) (Fin p) ℝ} (hSig : Sig.PosDef) :
    |transportBias μ₁ Y₁ μ₂ Y₂| ≤
        √(β ⬝ᵥ (Sig *ᵥ β)) * mahalanobis Sig (covMean (μ₂.map X₂)) (covMean (μ₁.map X₁)) ∧
      (|transportBias μ₁ Y₁ μ₂ Y₂| =
          √(β ⬝ᵥ (Sig *ᵥ β)) * mahalanobis Sig (covMean (μ₂.map X₂)) (covMean (μ₁.map X₁))
        ↔ Sig *ᵥ β = 0 ∨
          ∃ r : ℝ, covMean (μ₁.map X₁) - covMean (μ₂.map X₂) = r • (Sig *ᵥ β)) := by
  rw [transportBias_affine hX₁ hX₂ hY₁ hY₂ h₁ h₂ hcom]
  exact abs_dotProduct_sub_le_mahalanobis hSig _ _ _

end Distance

namespace TransportModel

open MeasureTheory Matrix IndirectComparison

variable {p : ℕ} {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- **The linear transport bias of a transport model.** For arm `a` of a transport model with
covariates in `ℝ^p` and the affine common regression `x ↦ α + βᵀ x` of `Y(a)`, the bias of the
source mean for the target mean is `βᵀ (x̄₁ - x̄*)`, with `x̄*` the mean of the target
covariate law. -/
theorem transportBias_affine (M : TransportModel Ω₁ Ω₂ (Fin p → ℝ)) (a : Bool)
    [IsProbabilityMeasure M.μ₁] [IsProbabilityMeasure M.μ₂] (hX₁ : Measurable M.X₁)
    (hX₂ : Measurable M.X₂)
    (hY₁ : Integrable (M.Y₁ a) M.μ₁) (hY₂ : Integrable (M.Y₂ a) M.μ₂)
    (h₁ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) (M.μ₁.map M.X₁))
    (h₂ : ∀ l, Integrable (fun x : Fin p → ℝ ↦ x l) M.targetCovLaw) {α : ℝ} {β : Fin p → ℝ}
    (hcom : IsCommonRegression M.μ₁ M.X₁ (M.Y₁ a) M.μ₂ M.X₂ (M.Y₂ a) fun x ↦ α + β ⬝ᵥ x) :
    ∫ ω, M.Y₁ a ω ∂M.μ₁ - M.targetMean a =
      β ⬝ᵥ (covMean (M.μ₁.map M.X₁) - covMean M.targetCovLaw) :=
  Distance.transportBias_affine hX₁ hX₂ hY₁ hY₂ h₁ h₂ hcom

end TransportModel

namespace Distance

open MeasureTheory ProbabilityTheory Matrix IndirectComparison

variable {p : ℕ}

/-! ### An instance -/

section Example

/-- The affine surface `g(x) = 1 + x₀ + x₁` on `ℝ²`. -/
def exampleSurface (x : Fin 2 → ℝ) : ℝ := 1 + ![1, 1] ⬝ᵥ x

theorem measurable_exampleSurface : Measurable exampleSurface := by
  unfold exampleSurface
  fun_prop

/-- The mean of the Dirac law at `v` is `v`. -/
theorem covMean_dirac (v : Fin p → ℝ) : covMean (Measure.dirac v) = v := by
  funext l; simp [covMean]

/-- **The linear bias with all hypotheses verified.** Source covariates fixed at `(1, 1)`,
target covariates fixed at `(0, 0)`, outcome `g(X)` with `g(x) = 1 + x₀ + x₁`: the transport
bias is `2`, and both Cauchy and Schwarz bounds hold with equality (unit scales; `Σ = I`), since
the gap `(1, 1)` is parallel to `β = (1, 1)`. -/
theorem transportBias_affine_example :
    transportBias (Measure.dirac (![1, 1] : Fin 2 → ℝ)) exampleSurface
        (Measure.dirac (0 : Fin 2 → ℝ)) exampleSurface = 2 ∧
      |transportBias (Measure.dirac (![1, 1] : Fin 2 → ℝ)) exampleSurface
        (Measure.dirac (0 : Fin 2 → ℝ)) exampleSurface| =
        √(∑ l, ((1 : Fin 2 → ℝ) l * (![1, 1] : Fin 2 → ℝ) l) ^ 2) *
          stdEuclidean 1 (covMean ((Measure.dirac (0 : Fin 2 → ℝ)).map id))
            (covMean ((Measure.dirac (![1, 1] : Fin 2 → ℝ)).map id)) ∧
      |transportBias (Measure.dirac (![1, 1] : Fin 2 → ℝ)) exampleSurface
        (Measure.dirac (0 : Fin 2 → ℝ)) exampleSurface| =
        √((![1, 1] : Fin 2 → ℝ) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 1])) *
          mahalanobis 1 (covMean ((Measure.dirac (0 : Fin 2 → ℝ)).map id))
            (covMean ((Measure.dirac (![1, 1] : Fin 2 → ℝ)).map id)) := by
  have hi : ∀ v : Fin 2 → ℝ, ∀ l, Integrable (fun x : Fin 2 → ℝ ↦ x l)
      ((Measure.dirac v).map id) := fun v l ↦ by
    rw [Measure.map_id]; exact integrable_dirac eNorm_lt_top
  have hcom : IsCommonRegression (Measure.dirac (![1, 1] : Fin 2 → ℝ)) id exampleSurface
      (Measure.dirac (0 : Fin 2 → ℝ)) id exampleSurface fun x ↦ 1 + ![1, 1] ⬝ᵥ x :=
    isCommonRegression_id measurable_exampleSurface (integrable_dirac eNorm_lt_top)
      (integrable_dirac eNorm_lt_top)
  have hY : ∀ v : Fin 2 → ℝ, Integrable exampleSurface (Measure.dirac v) :=
    fun _ ↦ integrable_dirac eNorm_lt_top
  have hb := transportBias_affine measurable_id measurable_id (hY _) (hY _) (hi _) (hi _) hcom
  have h2 : transportBias (Measure.dirac (![1, 1] : Fin 2 → ℝ)) exampleSurface
      (Measure.dirac (0 : Fin 2 → ℝ)) exampleSurface = 2 := by
    rw [hb, Measure.map_id, Measure.map_id, covMean_dirac, covMean_dirac]
    simp [dotProduct, Fin.sum_univ_two]
    norm_num
  have h1 : ∀ l : Fin 2, (0 : ℝ) < (1 : Fin 2 → ℝ) l := fun _ ↦ one_pos
  refine ⟨h2, ?_, ?_⟩
  · refine ((abs_transportBias_le_stdEuclidean measurable_id measurable_id (hY _) (hY _) (hi _)
      (hi _) hcom h1).2).2 (Or.inr ⟨1, ?_⟩)
    rw [Measure.map_id, Measure.map_id, covMean_dirac, covMean_dirac]
    funext l; fin_cases l <;> simp [stdGap]
  · refine ((abs_transportBias_le_mahalanobis measurable_id measurable_id (hY _) (hY _) (hi _)
      (hi _) hcom PosDef.one).2).2 (Or.inr ⟨1, ?_⟩)
    rw [Measure.map_id, Measure.map_id, covMean_dirac, covMean_dirac]
    funext l; fin_cases l <;> simp


/-- The bare bounds for two Dirac laws (all hypotheses verified). -/
example (v w : Fin 2 → ℝ) :
    |∫ x, exampleSurface x ∂Measure.dirac v - ∫ x, exampleSurface x ∂Measure.dirac w| ≤
        √(∑ l, ((![2, 1] : Fin 2 → ℝ) l * (![1, 1] : Fin 2 → ℝ) l) ^ 2) *
          stdEuclidean ![2, 1] (covMean (Measure.dirac w)) (covMean (Measure.dirac v)) ∧
      |∫ x, exampleSurface x ∂Measure.dirac v - ∫ x, exampleSurface x ∂Measure.dirac w| ≤
        √((![1, 1] : Fin 2 → ℝ) ⬝ᵥ (exampleCov *ᵥ ![1, 1])) *
          mahalanobis exampleCov (covMean (Measure.dirac w))
            (covMean (Measure.dirac v)) :=
  ⟨abs_integral_affine_sub_le_stdEuclidean (fun _ ↦ integrable_dirac eNorm_lt_top)
      (fun _ ↦ integrable_dirac eNorm_lt_top) (fun l ↦ by fin_cases l <;> norm_num) 1 ![1, 1],
    abs_integral_affine_sub_le_mahalanobis (fun _ ↦ integrable_dirac eNorm_lt_top)
      (fun _ ↦ integrable_dirac eNorm_lt_top) posDef_exampleCov 1 ![1, 1]⟩

/-- The transport model of `transportBias_affine_example`: source and target units are their
covariate vectors, fixed at `(1, 1)` and `(0, 0)`, every unit is treated, and both potential
outcomes are `g(X)`. -/
noncomputable def exampleModel : TransportModel (Fin 2 → ℝ) (Fin 2 → ℝ) (Fin 2 → ℝ) where
  μ₁ := Measure.dirac ![1, 1]
  X₁ := id
  A := fun _ ↦ true
  Y₁ := fun _ ↦ exampleSurface
  μ₂ := Measure.dirac 0
  X₂ := id
  Y₂ := fun _ ↦ exampleSurface

/-- The linear transport bias of `exampleModel` is `βᵀ (x̄₁ - x̄*) = 2`. -/
theorem exampleModel_transportBias :
    ∫ ω, exampleModel.Y₁ true ω ∂exampleModel.μ₁ - exampleModel.targetMean true = 2 := by
  have : IsProbabilityMeasure exampleModel.μ₁ := by unfold exampleModel; infer_instance
  have : IsProbabilityMeasure exampleModel.μ₂ := by unfold exampleModel; infer_instance
  have hi : ∀ v : Fin 2 → ℝ, ∀ l, Integrable (fun x : Fin 2 → ℝ ↦ x l)
      ((Measure.dirac v).map id) := fun v l ↦ by
    rw [Measure.map_id]; exact integrable_dirac eNorm_lt_top
  have hY : ∀ v : Fin 2 → ℝ, Integrable exampleSurface (Measure.dirac v) :=
    fun _ ↦ integrable_dirac eNorm_lt_top
  rw [TransportModel.transportBias_affine exampleModel true (α := 1) (β := ![1, 1])
    measurable_id measurable_id (hY _) (hY _) (hi _) (hi _)
    (isCommonRegression_id measurable_exampleSurface (hY _) (hY _))]
  simp only [exampleModel, TransportModel.targetCovLaw, Measure.map_id, covMean_dirac]
  simp [dotProduct, Fin.sum_univ_two]
  norm_num

end Example

end Distance

end Transport

end CausalInference
