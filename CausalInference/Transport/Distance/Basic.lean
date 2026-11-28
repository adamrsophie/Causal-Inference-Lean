/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Direct
public import CausalInference.Transport.Identification
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Distances between covariate summaries and the transport bias

To choose a comparator population from aggregate data, one compares a summary vector
`x₀ : Fin p → ℝ` of the target (for instance its covariate means, `covMean`) with the summary
vectors `x_j` of candidate source populations and selects a candidate closest to the target for
some distance. This file defines the distances in use, the selection rule, and the quantity the
distances are meant to control: the **transport bias** of the mean of a source population for
the mean of a target population.

**Sign convention.** The transport bias of the source mean for the target mean is
`E₁[Y₁] - E₂[Y₂]` (source minus target). When `g` is a common regression of the outcome on the
covariates (`IsCommonRegression`), it is `∫ g dP₁ - ∫ g dP₂`, the difference of the integrals
of `g` under the source and target covariate laws (`transportBias_eq_integral_sub`). The gap of
a candidate source with summary `x₁` relative to the target summary `x₂` is `x₁ - x₂`; every
distance below is written `d x₂ x₁`, target first.

**Scales.** The standardized distances divide the gap coordinatewise by scales `s ℓ` (for
instance pooled standard deviations); every result that uses the division assumes `0 < s ℓ`.

## Main definitions

* `IsMetric d`: a real valued function of two points is a metric.
* `IsMatchedComparator d x₀ xs j`: candidate `j` minimizes `d x₀ (xs k)` over the candidates.
* `transportBias μ₁ Y₁ μ₂ Y₂`: the transport bias `E₁[Y₁] - E₂[Y₂]`.
* `euclidean`, `stdGap`, `stdEuclidean`, `manhattan`, `minkowski`, `chebyshev`,
  `meanAbsStdDiff`, `gowerTerm`, `gower`: the distances between summary vectors.

## Main results

* `isMetric_of_dist`: a distance pulled back from a metric space along an injective map is a
  metric.
* `exists_isMatchedComparator`: among finitely many candidates a matched comparator exists.
* `transportBias_eq_integral_sub`, `TransportModel.transportBias_eq`,
  `TransportModel.transportBias_eq_integral_sub`: under a
  common regression the transport bias is a difference of integrals over the covariate laws.
* `isCommonRegression_comp`, `isCommonRegression_id`: an outcome that is a function of the
  covariates has that function as common regression.
* `euclidean_eq_sqrt`, `stdEuclidean_eq_sqrt`, `minkowski_one`, `minkowski_two`,
  `chebyshev_le_iff`.

## References

* J. C. Gower, *A general coefficient of similarity and some of its properties*, Biometrics 27
  (1971): the similarity coefficient from which `gower`, a dissimilarity between summary vectors,
  is adapted.
-/

@[expose] public section

namespace CausalInference

namespace Transport

namespace Distance

open MeasureTheory ProbabilityTheory

/-! ### Metrics and the selection rule -/

/-- A real valued function `d` of two points is a **metric**: it is nonnegative, vanishes
exactly on the diagonal, is symmetric and satisfies the triangle inequality. -/
structure IsMetric {V : Type*} (d : V → V → ℝ) : Prop where
  /-- Nonnegativity. -/
  nonneg : ∀ a b, 0 ≤ d a b
  /-- The distance vanishes exactly on the diagonal. -/
  eq_zero_iff : ∀ a b, d a b = 0 ↔ a = b
  /-- Symmetry. -/
  symm : ∀ a b, d a b = d b a
  /-- The triangle inequality. -/
  triangle : ∀ a b c, d a c ≤ d a b + d b c

/-- **A pulled back metric.** If `d a b = dist (f a) (f b)` for an injective map `f` into a
metric space, then `d` is a metric. -/
theorem isMetric_of_dist {V E : Type*} [MetricSpace E] {f : V → E} (hf : Function.Injective f)
    {d : V → V → ℝ} (hd : ∀ a b, d a b = dist (f a) (f b)) : IsMetric d where
  nonneg a b := by rw [hd]; exact dist_nonneg
  eq_zero_iff a b := by rw [hd, dist_eq_zero, hf.eq_iff]
  symm a b := by rw [hd, hd, dist_comm]
  triangle a b c := by rw [hd, hd, hd]; exact dist_triangle _ _ _

/-- Dividing a metric on `ℝ^p` by the dimension `p > 0` gives a metric. -/
theorem IsMetric.div_card {p : ℕ} [NeZero p] {d : (Fin p → ℝ) → (Fin p → ℝ) → ℝ}
    (h : IsMetric d) : IsMetric fun a b ↦ d a b / p := by
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  refine ⟨fun a b ↦ div_nonneg (h.nonneg a b) (Nat.cast_nonneg p), fun a b ↦ ?_,
    fun a b ↦ by rw [h.symm], fun a b c ↦ ?_⟩
  · rw [div_eq_zero_iff, h.eq_zero_iff]
    simp only [hp, or_false]
  · rw [← add_div]
    exact div_le_div_of_nonneg_right (h.triangle a b c) (Nat.cast_nonneg p)

/-- **The selection rule.** Candidate `j` is a **matched comparator** for the distance `d`, the
target summary `x₀` and the candidate summaries `xs` when it minimizes `d x₀ (xs k)` over all
candidates `k`. -/
def IsMatchedComparator {V J : Type*} (d : V → V → ℝ) (x₀ : V) (xs : J → V) (j : J) : Prop :=
  ∀ k, d x₀ (xs j) ≤ d x₀ (xs k)

/-- Among finitely many candidates, at least one, a matched comparator exists: a real function
on a finite nonempty set attains its minimum. -/
theorem exists_isMatchedComparator {V J : Type*} [Finite J] [Nonempty J] (d : V → V → ℝ)
    (x₀ : V) (xs : J → V) : ∃ j, IsMatchedComparator d x₀ xs j := by
  have := Fintype.ofFinite J
  obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ (fun k ↦ d x₀ (xs k))
    Finset.univ_nonempty
  exact ⟨j, fun k ↦ hj k (Finset.mem_univ k)⟩

/-! ### The transport bias -/

section Bias

variable {Ω₁ Ω₂ 𝒳 : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂}
  [MeasurableSpace 𝒳] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {X₁ : Ω₁ → 𝒳} {X₂ : Ω₂ → 𝒳}
  {Y₁ : Ω₁ → ℝ} {Y₂ : Ω₂ → ℝ} {g : 𝒳 → ℝ}

/-- The **transport bias** of the mean of the source population `(μ₁, Y₁)` for the mean of
the target population `(μ₂, Y₂)`: `E₁[Y₁] - E₂[Y₂]`. -/
noncomputable def transportBias (μ₁ : Measure Ω₁) (Y₁ : Ω₁ → ℝ) (μ₂ : Measure Ω₂)
    (Y₂ : Ω₂ → ℝ) : ℝ :=
  ∫ ω, Y₁ ω ∂μ₁ - ∫ ω, Y₂ ω ∂μ₂

variable [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]

/-- **The transport bias under a common regression.** If `g` is a common regression of the
outcome on the covariates and the outcomes are integrable, then `g` is integrable under both
covariate laws and the transport bias is `∫ g dP₁ - ∫ g dP₂`, with `Pᵢ = μᵢ ∘ Xᵢ⁻¹`. -/
theorem transportBias_eq_integral_sub (hX₁ : Measurable X₁) (hX₂ : Measurable X₂)
    (hY₁ : Integrable Y₁ μ₁) (hY₂ : Integrable Y₂ μ₂)
    (hcom : IsCommonRegression μ₁ X₁ Y₁ μ₂ X₂ Y₂ g) :
    Integrable g (μ₁.map X₁) ∧ Integrable g (μ₂.map X₂) ∧
      transportBias μ₁ Y₁ μ₂ Y₂ = ∫ x, g x ∂(μ₁.map X₁) - ∫ x, g x ∂(μ₂.map X₂) := by
  obtain ⟨hg, H₁, H₂⟩ := hcom
  obtain ⟨i₁, e₁⟩ := integral_target_eq_integral_common (μ₂ := μ₁) hX₁ hY₁ hg H₁
  obtain ⟨i₂, e₂⟩ := integral_target_eq_integral_common hX₂ hY₂ hg H₂
  exact ⟨i₁, i₂, by rw [transportBias, e₁, e₂]⟩

/-- **An outcome that is a function of the covariates has that function as common
regression.** If `Y₁ = g ∘ X₁` and `Y₂ = g ∘ X₂` with `g` measurable and integrable under both
covariate laws, then `g` is a common regression. -/
theorem isCommonRegression_comp (hX₁ : Measurable X₁) (hX₂ : Measurable X₂) (hg : Measurable g)
    (hg₁ : Integrable g (μ₁.map X₁)) (hg₂ : Integrable g (μ₂.map X₂)) :
    IsCommonRegression μ₁ X₁ (g ∘ X₁) μ₂ X₂ (g ∘ X₂) g := by
  refine ⟨hg, ?_, ?_⟩
  · rw [condExp_of_stronglyMeasurable hX₁.comap_le
      (hg.comp (comap_measurable X₁)).stronglyMeasurable
      ((integrable_map_measure hg.aestronglyMeasurable hX₁.aemeasurable).1 hg₁)]
    rfl
  · rw [condExp_of_stronglyMeasurable hX₂.comap_le
      (hg.comp (comap_measurable X₂)).stronglyMeasurable
      ((integrable_map_measure hg.aestronglyMeasurable hX₂.aemeasurable).1 hg₂)]
    rfl

omit [MeasurableSpace 𝒳] in
/-- **A function of the covariates is its own common regression.** On `Ω = 𝒳` with the
covariate `X = id`, an outcome `Y = g(X)` with `g` measurable and integrable under both laws has
the common regression `g`. -/
theorem isCommonRegression_id {m𝒳 : MeasurableSpace 𝒳} {P₁ P₂ : Measure 𝒳} [IsFiniteMeasure P₁]
    [IsFiniteMeasure P₂] (hg : Measurable g) (hg₁ : Integrable g P₁) (hg₂ : Integrable g P₂) :
    IsCommonRegression P₁ id g P₂ id g g :=
  isCommonRegression_comp (g := g) measurable_id measurable_id hg (by rwa [Measure.map_id])
    (by rwa [Measure.map_id])

end Bias

/-! ### A two point law -/

/-- The two point law `½ δ₋₁ + ½ δ₁` on `ℝ`, with mean `0` and variance `1`; it serves the
examples and counterexamples of this folder. -/
noncomputable def spreadLaw : Measure ℝ :=
  (2⁻¹ : ENNReal) • Measure.dirac (-1) + (2⁻¹ : ENNReal) • Measure.dirac 1

instance isProbabilityMeasure_spreadLaw : IsProbabilityMeasure spreadLaw :=
  ⟨by simp [spreadLaw, ENNReal.inv_two_add_inv_two]⟩

/-- Every function is integrable for the two point law. -/
theorem integrable_spreadLaw (f : ℝ → ℝ) : Integrable f spreadLaw :=
  ((integrable_dirac eNorm_lt_top).smul_measure (by simp)).add_measure
    ((integrable_dirac eNorm_lt_top).smul_measure (by simp))

/-- `E f = (f(-1) + f(1)) / 2` under the two point law. -/
theorem integral_spreadLaw (f : ℝ → ℝ) : ∫ x, f x ∂spreadLaw = (f (-1) + f 1) / 2 := by
  rw [spreadLaw, integral_add_measure
    ((integrable_dirac eNorm_lt_top).smul_measure (by simp))
    ((integrable_dirac eNorm_lt_top).smul_measure (by simp)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- `∫⁻ f = f(-1)/2 + f(1)/2` under the two point law. -/
theorem lintegral_spreadLaw (f : ℝ → ENNReal) :
    ∫⁻ x, f x ∂spreadLaw = 2⁻¹ * f (-1) + 2⁻¹ * f 1 := by
  simp only [spreadLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]

/-! ### Euclidean distances and the standardized gap -/

variable {p : ℕ}

/-- The **Euclidean distance** between summary vectors, the distance of `EuclideanSpace`:
`d_E(x, y) = ‖y - x‖₂`. -/
noncomputable def euclidean (x y : Fin p → ℝ) : ℝ :=
  dist (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin p)) (WithLp.toLp 2 y)

/-- The **standardized gap** of `y` relative to `x` for the scales `s`:
`z ℓ = (y ℓ - x ℓ) / s ℓ`. -/
noncomputable def stdGap (s x y : Fin p → ℝ) : Fin p → ℝ :=
  fun l ↦ (y l - x l) / s l

/-- The **standardized Euclidean distance**, the Euclidean norm of the standardized gap:
`d_SE(x, y; s) = ‖z‖₂`. -/
noncomputable def stdEuclidean (s x y : Fin p → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 (stdGap s x y) : EuclideanSpace ℝ (Fin p))‖

/-- The Euclidean norm of `v` is `√(∑ v ℓ²)`. -/
theorem norm_toLp_two (v : Fin p → ℝ) :
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin p))‖ = √(∑ l, v l ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs]

/-- `d_E(x, y) = ‖toLp (y - x)‖`. -/
theorem euclidean_eq_norm (x y : Fin p → ℝ) :
    euclidean x y = ‖(WithLp.toLp 2 (y - x) : EuclideanSpace ℝ (Fin p))‖ := by
  rw [euclidean, dist_comm, dist_eq_norm, ← WithLp.toLp_sub]

/-- `d_E(x, y) = √(∑ (y ℓ - x ℓ)²)`. -/
theorem euclidean_eq_sqrt (x y : Fin p → ℝ) : euclidean x y = √(∑ l, (y l - x l) ^ 2) := by
  rw [euclidean_eq_norm, norm_toLp_two]; rfl

/-- `d_SE(x, y; s) = √(∑ ((y ℓ - x ℓ) / s ℓ)²)`. -/
theorem stdEuclidean_eq_sqrt (s x y : Fin p → ℝ) :
    stdEuclidean s x y = √(∑ l, ((y l - x l) / s l) ^ 2) := by
  rw [stdEuclidean, norm_toLp_two]; rfl

/-- With unit scales the standardized gap is the gap. -/
theorem stdGap_one (x y : Fin p → ℝ) : stdGap 1 x y = y - x := by
  funext l; simp [stdGap]

/-- With unit scales the standardized Euclidean distance is the Euclidean distance. -/
theorem stdEuclidean_one (x y : Fin p → ℝ) : stdEuclidean 1 x y = euclidean x y := by
  rw [stdEuclidean, stdGap_one, euclidean_eq_norm]

/-! ### Manhattan, Minkowski, Chebyshev, mean standardized difference and Gower -/

/-- The **Manhattan distance** of the standardized gap, `d₁ = ∑ |z ℓ|`. -/
noncomputable def manhattan (s x y : Fin p → ℝ) : ℝ :=
  ∑ l, |stdGap s x y l|

/-- The **Minkowski distance** of order `q` of the standardized gap,
`d_q = (∑ |z ℓ|^q)^(1/q)`, with real powers. It is a metric for `1 ≤ q`
(`isMetric_minkowski`), not for `0 < q < 1` (`not_triangle_minkowski`). -/
noncomputable def minkowski (q : ℝ) (s x y : Fin p → ℝ) : ℝ :=
  (∑ l, |stdGap s x y l| ^ q) ^ (1 / q)

/-- The **Chebyshev distance** of the standardized gap, `d_∞ = max |z ℓ|`: the sup norm of
`Fin p → ℝ`. -/
noncomputable def chebyshev (s x y : Fin p → ℝ) : ℝ :=
  ‖stdGap s x y‖

/-- The **mean absolute standardized difference** `d₁ / p`, the average over the `p` summary
coordinates of the absolute standardized differences. -/
noncomputable def meanAbsStdDiff (s x y : Fin p → ℝ) : ℝ :=
  manhattan s x y / p

/-- The **Gower term** of coordinate `ℓ`: `|y ℓ - x ℓ|` on a binary coordinate
(`bin ℓ = true`, the summaries being proportions) and `min (|y ℓ - x ℓ| / r ℓ, 1)` on a
continuous coordinate of range `r ℓ`. -/
noncomputable def gowerTerm (r : Fin p → ℝ) (bin : Fin p → Bool) (x y : Fin p → ℝ)
    (l : Fin p) : ℝ :=
  if bin l then |y l - x l| else min (|y l - x l| / r l) 1

/-- The **Gower distance**, the average of the Gower terms: `d_G = (1/p) ∑ g ℓ`. -/
noncomputable def gower (r : Fin p → ℝ) (bin : Fin p → Bool) (x y : Fin p → ℝ) : ℝ :=
  (∑ l, gowerTerm r bin x y l) / p

/-- The Chebyshev distance is at most `c ≥ 0` exactly when every absolute standardized gap is. -/
theorem chebyshev_le_iff {s x y : Fin p → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    chebyshev s x y ≤ c ↔ ∀ l, |stdGap s x y l| ≤ c := by
  simp only [chebyshev, pi_norm_le_iff_of_nonneg hc, Real.norm_eq_abs]

/-- Every absolute standardized gap is at most the Chebyshev distance. -/
theorem abs_stdGap_le_chebyshev (s x y : Fin p → ℝ) (l : Fin p) :
    |stdGap s x y l| ≤ chebyshev s x y := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ l

/-- The Minkowski distance of order one is the Manhattan distance. -/
theorem minkowski_one (s x y : Fin p → ℝ) : minkowski 1 s x y = manhattan s x y := by
  simp only [minkowski, manhattan, Real.rpow_one, div_one]

/-- The Minkowski distance of order two is the standardized Euclidean distance. -/
theorem minkowski_two (s x y : Fin p → ℝ) : minkowski 2 s x y = stdEuclidean s x y := by
  rw [minkowski, stdEuclidean, norm_toLp_two, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Real.rpow_two, sq_abs]

end Distance

namespace TransportModel

open MeasureTheory

variable {Ω₁ Ω₂ 𝒳 : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace 𝒳]
  {g : 𝒳 → ℝ}

omit [MeasurableSpace 𝒳] in
/-- The transport bias of arm `a` of a transport model is `E₁[Y₁(a)] - E₂[Y₂(a)]`, the source
mean minus the target mean. -/
theorem transportBias_eq (M : TransportModel Ω₁ Ω₂ 𝒳) (a : Bool) :
    Distance.transportBias M.μ₁ (M.Y₁ a) M.μ₂ (M.Y₂ a) =
      ∫ ω, M.Y₁ a ω ∂M.μ₁ - M.targetMean a :=
  rfl

/-- **The transport bias of a transport model.** For arm `a` of a transport model with a common
regression `g` of `Y(a)` and integrable potential outcomes, the bias of the source mean
`E₁[Y₁(a)]` for the target mean `E₂[Y₂(a)]` is `∫ g dP₁ - ∫ g dP*`, where `P*` is the target
covariate law. -/
theorem transportBias_eq_integral_sub (M : TransportModel Ω₁ Ω₂ 𝒳) (a : Bool)
    [IsFiniteMeasure M.μ₁] [IsFiniteMeasure M.μ₂]
    (hX₁ : Measurable M.X₁) (hX₂ : Measurable M.X₂) (hY₁ : Integrable (M.Y₁ a) M.μ₁)
    (hY₂ : Integrable (M.Y₂ a) M.μ₂)
    (hcom : IsCommonRegression M.μ₁ M.X₁ (M.Y₁ a) M.μ₂ M.X₂ (M.Y₂ a) g) :
    ∫ ω, M.Y₁ a ω ∂M.μ₁ - M.targetMean a =
      ∫ x, g x ∂(M.μ₁.map M.X₁) - ∫ x, g x ∂M.targetCovLaw :=
  (Distance.transportBias_eq_integral_sub hX₁ hX₂ hY₁ hY₂ hcom).2.2

end TransportModel

end Transport

end CausalInference
