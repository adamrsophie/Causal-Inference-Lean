/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Transport.Distance.Metric
public import CausalInference.Transport.Distance.BiasLinear
public import CausalInference.Transport.Distance.Wasserstein
public import CausalInference.IndirectComparison.Balance

/-!
# A zero summary distance does not bound the transport bias

**A distance between covariate summaries is a diagnostic, not a validity guarantee.** The
bounds of `BiasLinear` and `Wasserstein` control the transport bias only under assumptions on
the outcome surface (affine, Lipschitz) and on the covariates (all the covariates that the
common regression depends on are summarized). Without them a zero distance between the
summaries says nothing about the bias:

* **A nonlinear surface.** Covariate laws `½ δ₋₁ + ½ δ₁` (source) and `δ₀` (target) have the
  same mean, so every distance between the mean summaries is zero, while for the common
  regression `x ↦ x²` the transport bias is `1`. No bound `|bias| ≤ C d(x̄₂, x̄₁)` holds, for
  any distance `d` vanishing on the diagonal and any constant `C`.
* **An unmeasured covariate.** Two populations with the same law of the measured covariates
  `X`, and so equal summaries of `X` of every kind, but with an unmeasured covariate `W` equal
  to `1` in the source and `0` in the target and the outcome `Y = W`: the transport bias is
  `1`. There is then no common regression of `Y` on `X` alone.

## Main results

* `nonlinearModel`, `nonlinear_transportBias`, `not_abs_transportBias_le_of_self_eq_zero`,
  `nonlinear_bias_le_two_wasserstein1`.
* `unmeasured_transportBias`, `not_structurallyInvariant_unmeasured`,
  `covMean_eq_unmeasured`.
-/

@[expose] public section

namespace CausalInference

namespace Transport

namespace Distance

open MeasureTheory ProbabilityTheory IndirectComparison

/-! ### A nonlinear outcome surface -/

/-- The covariate of the nonlinear model, a real number seen as a vector of dimension one. -/
def oneVec (x : ℝ) : Fin 1 → ℝ := fun _ ↦ x

theorem measurable_oneVec : Measurable oneVec := Measurable.of_eval fun _ ↦ measurable_id

/-- The nonlinear outcome surface `v ↦ v₀²`. -/
def sqSurface (v : Fin 1 → ℝ) : ℝ := v 0 ^ 2

theorem measurable_sqSurface : Measurable sqSurface := (measurable_pi_apply 0).pow_const 2

/-- The covariate laws `½ δ₋₁ + ½ δ₁` and `δ₀`, seen on `ℝ¹`, have the same mean `0`. -/
theorem covMean_map_oneVec :
    covMean (spreadLaw.map oneVec) = 0 ∧ covMean ((Measure.dirac (0 : ℝ)).map oneVec) = 0 := by
  constructor <;> funext l <;>
    simp only [covMean, Pi.zero_apply, integral_map measurable_oneVec.aemeasurable
      (measurable_pi_apply l).aestronglyMeasurable, oneVec, integral_spreadLaw, integral_dirac]
  norm_num

/-- **The nonlinear model.** Source units and target units are real numbers with laws
`½ δ₋₁ + ½ δ₁` and `δ₀`; the covariate is the unit, as a vector of dimension one; every source
unit is treated, and both potential outcomes are the square of the covariate. -/
noncomputable def nonlinearModel : TransportModel ℝ ℝ (Fin 1 → ℝ) where
  μ₁ := spreadLaw
  X₁ := oneVec
  A := fun _ ↦ true
  Y₁ := fun _ ↦ sqSurface ∘ oneVec
  μ₂ := Measure.dirac 0
  X₂ := oneVec
  Y₂ := fun _ ↦ sqSurface ∘ oneVec

/-- In the nonlinear model `v ↦ v₀²` is a common regression of the outcome of either arm. -/
theorem isCommonRegression_nonlinearModel (a : Bool) :
    IsCommonRegression nonlinearModel.μ₁ nonlinearModel.X₁ (nonlinearModel.Y₁ a)
      nonlinearModel.μ₂ nonlinearModel.X₂ (nonlinearModel.Y₂ a) sqSurface :=
  isCommonRegression_comp (μ₁ := spreadLaw) (μ₂ := Measure.dirac 0) measurable_oneVec
    measurable_oneVec measurable_sqSurface
    ((integrable_map_measure measurable_sqSurface.aestronglyMeasurable
      measurable_oneVec.aemeasurable).2 (integrable_spreadLaw _))
    ((integrable_map_measure measurable_sqSurface.aestronglyMeasurable
      measurable_oneVec.aemeasurable).2 (integrable_dirac eNorm_lt_top))

/-- **Equal means, transport bias one.** In the nonlinear model the source and target
covariate laws have the same mean (`covMean`), while the bias of the source mean for the target
mean is `E₁[X²] - E₂[X²] = 1 - 0 = 1`, also as a difference of integrals of the common
regression under the covariate laws. -/
theorem nonlinear_transportBias (a : Bool) :
    covMean (nonlinearModel.μ₁.map nonlinearModel.X₁) = covMean nonlinearModel.targetCovLaw ∧
      ∫ ω, nonlinearModel.Y₁ a ω ∂nonlinearModel.μ₁ - nonlinearModel.targetMean a = 1 ∧
      ∫ v, sqSurface v ∂(nonlinearModel.μ₁.map nonlinearModel.X₁) -
        ∫ v, sqSurface v ∂nonlinearModel.targetCovLaw = 1 := by
  have hb : ∫ ω, nonlinearModel.Y₁ a ω ∂nonlinearModel.μ₁ - nonlinearModel.targetMean a = 1 := by
    simp only [nonlinearModel, TransportModel.targetMean, Function.comp_apply, sqSurface, oneVec,
      integral_spreadLaw, integral_dirac]
    norm_num
  have : IsProbabilityMeasure nonlinearModel.μ₁ := by unfold nonlinearModel; infer_instance
  have : IsProbabilityMeasure nonlinearModel.μ₂ := by unfold nonlinearModel; infer_instance
  refine ⟨?_, hb, ?_⟩
  · simp only [nonlinearModel, TransportModel.targetCovLaw]
    rw [covMean_map_oneVec.1, covMean_map_oneVec.2]
  · rw [← TransportModel.transportBias_eq_integral_sub nonlinearModel a measurable_oneVec
      measurable_oneVec ((integrable_spreadLaw _))
      (integrable_dirac eNorm_lt_top) (isCommonRegression_nonlinearModel a), hb]

/-- **No distance between the mean summaries bounds the transport bias.** In the nonlinear
model, for every distance `d` on summary vectors that vanishes on the diagonal (every distance
of this folder does, `self_distances`, `isMetric_mahalanobis`) and every constant `C`,
`|bias| ≤ C d(x̄*, x̄₁)` fails, `x̄₁` and `x̄*` being the source and target covariate means. -/
theorem not_abs_transportBias_le_of_self_eq_zero (a : Bool)
    (d : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ) (hd : ∀ x, d x x = 0) (C : ℝ) :
    ¬ |∫ ω, nonlinearModel.Y₁ a ω ∂nonlinearModel.μ₁ - nonlinearModel.targetMean a| ≤
      C * d (covMean nonlinearModel.targetCovLaw)
        (covMean (nonlinearModel.μ₁.map nonlinearModel.X₁)) := by
  obtain ⟨hm, hb, -⟩ := nonlinear_transportBias a
  rw [hb, hm, hd]
  norm_num

/-- The hypothesis of `not_abs_transportBias_le_of_self_eq_zero` holds for the standardized
Euclidean distance with unit scale, and the distance of the covariate means is zero. -/
example : (∀ x : Fin 1 → ℝ, stdEuclidean 1 x x = 0) ∧
    stdEuclidean 1 (covMean nonlinearModel.targetCovLaw)
      (covMean (nonlinearModel.μ₁.map nonlinearModel.X₁)) = 0 := by
  have h1 : ∀ l : Fin 1, (0 : ℝ) < (1 : Fin 1 → ℝ) l := fun _ ↦ one_pos
  have hs : ∀ x : Fin 1 → ℝ, stdEuclidean 1 x x = 0 := fun x ↦
    (self_distances h1 h1 ![true] one_pos x).2.1
  exact ⟨hs, by rw [(nonlinear_transportBias true).1]; exact hs _⟩

/-- **The Lipschitz bound is not contradicted.** The square is `2`-Lipschitz on `[-1, 1]`,
which contains both covariate supports, and the bias `1` is within `2 W₁ = 2`. The square is
not Lipschitz on `ℝ`, so `abs_transportBias_le_wasserstein1` applies to this model only after
restricting the covariate space to the supports; what fails is a bound by the mean summaries. -/
theorem nonlinear_bias_le_two_wasserstein1 :
    (∀ x y : ℝ, |x| ≤ 1 → |y| ≤ 1 → |x ^ 2 - y ^ 2| ≤ 2 * |x - y|) ∧
      |∫ x, x ^ 2 ∂spreadLaw - ∫ x, x ^ 2 ∂(Measure.dirac (0 : ℝ))| ≤
        2 * (wasserstein1 spreadLaw (Measure.dirac 0)).toReal := by
  refine ⟨fun x y hx hy ↦ ?_, ?_⟩
  · have hxy : |x + y| ≤ 2 := (abs_add_le x y).trans (by linarith)
    calc |x ^ 2 - y ^ 2| = |x + y| * |x - y| := by rw [← abs_mul]; ring_nf
      _ ≤ 2 * |x - y| := mul_le_mul_of_nonneg_right hxy (abs_nonneg _)
  · rw [integral_spreadLaw, integral_dirac, wasserstein1_spreadLaw_dirac]
    norm_num

/-! ### An unmeasured covariate -/

section Unmeasured

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The law of `(X, W)` with `X ∼ ν` and `W = w` fixed. -/
noncomputable def unmeasuredLaw (ν : Measure 𝒳) (w : ℝ) : Measure (𝒳 × ℝ) :=
  ν.prod (Measure.dirac w)

instance (ν : Measure 𝒳) [IsProbabilityMeasure ν] (w : ℝ) :
    IsProbabilityMeasure (unmeasuredLaw ν w) := by
  unfold unmeasuredLaw; infer_instance

theorem unmeasuredLaw_eq (ν : Measure 𝒳) [SFinite ν] (w : ℝ) :
    unmeasuredLaw ν w = ν.map fun x ↦ (x, w) := by
  rw [unmeasuredLaw, Measure.prod_dirac]

/-- The unmeasured covariate `W` is integrable and has mean `w`. -/
theorem integrable_snd_unmeasuredLaw (ν : Measure 𝒳) [IsProbabilityMeasure ν] (w : ℝ) :
    Integrable Prod.snd (unmeasuredLaw ν w) ∧ ∫ z, z.2 ∂(unmeasuredLaw ν w) = w := by
  rw [unmeasuredLaw_eq]
  refine ⟨(integrable_map_measure measurable_snd.aestronglyMeasurable
    measurable_prodMk_right.aemeasurable).2 (integrable_const w), ?_⟩
  rw [integral_map measurable_prodMk_right.aemeasurable measurable_snd.aestronglyMeasurable]
  simp

/-- The measured covariate has law `ν` whatever the value of `W`. -/
theorem map_fst_unmeasuredLaw (ν : Measure 𝒳) [IsProbabilityMeasure ν] (w : ℝ) :
    (unmeasuredLaw ν w).map Prod.fst = ν := by
  simp [unmeasuredLaw]

/-- **Balanced measured covariates, transport bias one.** Let the source and target
populations of `(X, W)` have `X ∼ ν` in both, `W = 1` in the source and `W = 0` in the
target, and the outcome `Y = W`. Then the measured covariate is balanced (`CovBalanced`: its
two laws are equal, so every summary of it agrees), `(x, w) ↦ w` is a common regression of `Y`
on the full covariates `(X, W)`, and the transport bias is `1`. -/
theorem unmeasured_transportBias (ν : Measure 𝒳) [IsProbabilityMeasure ν] :
    CovBalanced (unmeasuredLaw ν 1) Prod.fst (unmeasuredLaw ν 0) Prod.fst ∧
      IsCommonRegression (unmeasuredLaw ν 1) id Prod.snd (unmeasuredLaw ν 0) id Prod.snd
        Prod.snd ∧
      transportBias (unmeasuredLaw ν 1) Prod.snd (unmeasuredLaw ν 0) Prod.snd = 1 := by
  refine ⟨by rw [CovBalanced, map_fst_unmeasuredLaw, map_fst_unmeasuredLaw],
    isCommonRegression_id measurable_snd (integrable_snd_unmeasuredLaw ν 1).1
      (integrable_snd_unmeasuredLaw ν 0).1, ?_⟩
  rw [transportBias, (integrable_snd_unmeasuredLaw ν 1).2, (integrable_snd_unmeasuredLaw ν 0).2]
  norm_num

/-- **No common regression on the measured covariate.** In the populations of
`unmeasured_transportBias`, the outcome has no common regression on `X` alone: a common
regression `g` would give the bias `∫ g dν - ∫ g dν = 0`. -/
theorem not_structurallyInvariant_unmeasured (ν : Measure 𝒳) [IsProbabilityMeasure ν] :
    ¬ StructurallyInvariant (unmeasuredLaw ν 1) Prod.fst Prod.snd (unmeasuredLaw ν 0) Prod.fst
      Prod.snd := by
  rintro ⟨g, hg⟩
  have h := (transportBias_eq_integral_sub measurable_fst measurable_fst
    (integrable_snd_unmeasuredLaw ν 1).1 (integrable_snd_unmeasuredLaw ν 0).1 hg).2.2
  rw [map_fst_unmeasuredLaw, map_fst_unmeasuredLaw, sub_self,
    (unmeasured_transportBias ν).2.2] at h
  exact one_ne_zero h

/-- With measured covariates in `ℝ^p`, the covariate means of the measured covariates agree
(the two laws are both `ν`), so every distance between the mean summaries is zero. -/
theorem covMean_eq_unmeasured {p : ℕ} (ν : Measure (Fin p → ℝ)) [IsProbabilityMeasure ν] :
    covMean ((unmeasuredLaw ν 1).map Prod.fst) = covMean ((unmeasuredLaw ν 0).map Prod.fst) := by
  rw [map_fst_unmeasuredLaw, map_fst_unmeasuredLaw]

end Unmeasured

/-- The unmeasured covariate example with measured covariate law `½ δ₋₁ + ½ δ₁`. -/
example : transportBias (unmeasuredLaw spreadLaw 1) Prod.snd (unmeasuredLaw spreadLaw 0)
      Prod.snd = 1 ∧
    ¬ StructurallyInvariant (unmeasuredLaw spreadLaw 1) Prod.fst Prod.snd
      (unmeasuredLaw spreadLaw 0) Prod.fst Prod.snd :=
  ⟨(unmeasured_transportBias spreadLaw).2.2, not_structurallyInvariant_unmeasured spreadLaw⟩

example : covMean ((unmeasuredLaw (Measure.dirac (0 : Fin 1 → ℝ)) 1).map Prod.fst) =
    covMean ((unmeasuredLaw (Measure.dirac (0 : Fin 1 → ℝ)) 0).map Prod.fst) :=
  covMean_eq_unmeasured _

end Distance

end Transport

end CausalInference
