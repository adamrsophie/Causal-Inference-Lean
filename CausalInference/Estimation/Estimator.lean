/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Estimators built from an i.i.d. sample

This file sets up the generic statistical layer used by the estimation files.

* `CausalInference.IsIIDSample O μ`: the observations `O : ℕ → Ω → 𝒪` are mutually independent
  (`ProbabilityTheory.iIndepFun`) and identically distributed (`ProbabilityTheory.IdentDistrib`)
  under the probability measure `μ`.
* `CausalInference.IsSampleMeasurable θhat O`: the estimator sequence `θhat : ℕ → Ω → ℝ` has
  `θhat n` equal to a measurable function of the first `n` observations.
* `CausalInference.sampleMean f O n`: the sample mean `n⁻¹ ∑_{i < n} f (O i)`.
* `CausalInference.empiricalMeasure O n ω`: the empirical measure `n⁻¹ ∑_{i < n} δ_{O i ω}`, with
  `integral_empiricalMeasure`: integrating `f` against it gives the sample mean, and the instance
  `isProbabilityMeasure_empiricalMeasure`: it is a probability measure for `n ≠ 0`.
* `CausalInference.exists_isIIDSample`: for every probability measure `ν` there is an i.i.d.
  sample with marginal law `ν`, so the i.i.d. hypothesis is never vacuous.

Source: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 2, 3 and 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace CausalInference

universe u

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-- The observations `O i` form an i.i.d. sequence under `μ`: they are mutually independent and
each `O i` has the same law as `O 0`. -/
structure IsIIDSample (O : ℕ → Ω → 𝒪) (μ : Measure Ω) : Prop where
  /-- The observations are mutually independent. -/
  indep : iIndepFun O μ
  /-- Every observation has the law of the first one. -/
  ident : ∀ i, IdentDistrib (O i) (O 0) μ μ

namespace IsIIDSample

variable {O : ℕ → Ω → 𝒪} {μ : Measure Ω}

/-- Each observation of an i.i.d. sample is almost everywhere measurable. -/
theorem aemeasurable (h : IsIIDSample O μ) (i : ℕ) : AEMeasurable (O i) μ :=
  (h.ident i).aemeasurable_fst

/-- A measurable transformation `f (O i)` of an i.i.d. sample is again i.i.d. -/
theorem comp {𝒳 : Type*} [MeasurableSpace 𝒳] (h : IsIIDSample O μ) {f : 𝒪 → 𝒳}
    (hf : Measurable f) : IsIIDSample (fun i ω ↦ f (O i ω)) μ where
  indep := h.indep.comp (fun _ ↦ f) (fun _ ↦ hf)
  ident i := (h.ident i).comp hf

/-- The real-valued variables `f (O i)` of an i.i.d. sample are pairwise independent; this is the
form of independence used by the strong law of large numbers. -/
theorem pairwise_indepFun {f : 𝒪 → ℝ} (h : IsIIDSample O μ) (hf : Measurable f) :
    Pairwise fun i j ↦ IndepFun (fun ω ↦ f (O i ω)) (fun ω ↦ f (O j ω)) μ :=
  fun _ _ hij ↦ (h.comp hf).indep.indepFun hij

end IsIIDSample

/-- For every probability measure `ν` on the observation space there is a probability space
carrying an i.i.d. sample with marginal law `ν`. This shows that the i.i.d. hypothesis of the
estimation theorems can always be met. -/
theorem exists_isIIDSample {𝒳 : Type u} [MeasurableSpace 𝒳] (ν : Measure 𝒳)
    [IsProbabilityMeasure ν] :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ O : ℕ → Ω → 𝒳,
      IsProbabilityMeasure P ∧ (∀ i, Measurable (O i)) ∧ IsIIDSample O P ∧
        ∀ i, HasLaw (O i) ν P := by
  obtain ⟨Ω, _, P, O, hmeas, hlaw, hind, hP⟩ := exists_iid ℕ ν
  refine ⟨Ω, _, P, O, hP, hmeas, ⟨hind, fun i ↦ ?_⟩, hlaw⟩
  exact ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable,
    (hlaw i).map_eq.trans (hlaw 0).map_eq.symm⟩

/-- The estimator sequence `θhat` is built from the sample `O`: for every `n`, `θhat n` is a
measurable function of the first `n` observations `(O 0, …, O (n - 1))`. -/
def IsSampleMeasurable (θhat : ℕ → Ω → ℝ) (O : ℕ → Ω → 𝒪) : Prop :=
  ∀ n, ∃ g : (Fin n → 𝒪) → ℝ, Measurable g ∧ θhat n = fun ω ↦ g (fun i ↦ O i ω)

/-- An estimator built measurably from an i.i.d. sample is almost everywhere measurable. -/
theorem IsSampleMeasurable.aemeasurable {θhat : ℕ → Ω → ℝ} {O : ℕ → Ω → 𝒪} {μ : Measure Ω}
    (hθ : IsSampleMeasurable θhat O) (hO : IsIIDSample O μ) (n : ℕ) : AEMeasurable (θhat n) μ := by
  obtain ⟨g, hg, h⟩ := hθ n
  rw [h]
  exact hg.comp_aemeasurable (AEMeasurable.of_eval fun i ↦ hO.aemeasurable i)

/-- The sample mean `n⁻¹ ∑_{i < n} f (O i)` of the transformed observations `f (O i)`. At `n = 0`
it takes the value `0`. -/
noncomputable def sampleMean (f : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ range n, f (O i ω)

/-- The sample mean of a measurable transformation is a measurable function of the first `n`
observations. -/
theorem isSampleMeasurable_sampleMean {f : 𝒪 → ℝ} (hf : Measurable f) (O : ℕ → Ω → 𝒪) :
    IsSampleMeasurable (sampleMean f O) O := by
  intro n
  refine ⟨fun x ↦ (n : ℝ)⁻¹ * ∑ i : Fin n, f (x i), by fun_prop, ?_⟩
  funext ω
  simp [sampleMean, Finset.sum_range]

/-- The empirical measure `n⁻¹ ∑_{i < n} δ_{O i ω}` of the first `n` observations. At `n = 0` it is
the zero measure. -/
noncomputable def empiricalMeasure (O : ℕ → Ω → 𝒪) (n : ℕ) (ω : Ω) : Measure 𝒪 :=
  (n : ENNReal)⁻¹ • ∑ i ∈ range n, Measure.dirac (O i ω)

/-- For a positive sample size `n`, the empirical measure is a probability measure: each of the `n`
Dirac masses has weight `n⁻¹`. -/
instance isProbabilityMeasure_empiricalMeasure (O : ℕ → Ω → 𝒪) (n : ℕ) [NeZero n] (ω : Ω) :
    IsProbabilityMeasure (empiricalMeasure O n ω) where
  measure_univ := by
    simpa [empiricalMeasure] using
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 (NeZero.ne n)) (ENNReal.natCast_ne_top n)

/-- On an observation space with measurable singletons, integrating any real function against the
empirical measure gives the sample mean. -/
theorem integral_empiricalMeasure [MeasurableSingletonClass 𝒪] (f : 𝒪 → ℝ) (O : ℕ → Ω → 𝒪)
    (n : ℕ) (ω : Ω) : ∫ x, f x ∂(empiricalMeasure O n ω) = sampleMean f O n ω := by
  rw [empiricalMeasure, integral_smul_measure, integral_finsetSum_measure]
  · simp [sampleMean, integral_dirac]
  · intro i _
    exact integrable_dirac (by simp)

end CausalInference
