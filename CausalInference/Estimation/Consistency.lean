/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Estimator
public import Mathlib.Probability.StrongLaw

/-!
# Consistency of estimators

An estimator sequence `θhat : ℕ → Ω → ℝ` is consistent for `θ` when `θhat n` converges to `θ` in
probability, that is `MeasureTheory.TendstoInMeasure μ θhat atTop (fun _ ↦ θ)`.

Main results:

* `CausalInference.TendstoInMeasure.add`, `CausalInference.TendstoInMeasure.neg`,
  `CausalInference.TendstoInMeasure.sub`,
  `CausalInference.TendstoInMeasure.of_norm_le`: closure properties of convergence in
  probability, which the pinned Mathlib does not provide.
* `CausalInference.sampleMean_isConsistent`: the sample mean of an integrable `f (O i)` from an
  i.i.d. sample is consistent for `E f (O 0)` (strong law of large numbers, then almost sure
  convergence implies convergence in probability).

Source: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 2 and 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

section TendstoInMeasure

variable {ι E : Type*} [SeminormedAddCommGroup E] {μ : Measure Ω} {l : Filter ι}
  {f f' : ι → Ω → E} {g g' : Ω → E}

/-- Convergence in measure is preserved by sums: if `f i → g` and `f' i → g'` in measure, then
`f i + f' i → g + g'` in measure. -/
theorem TendstoInMeasure.add (hf : TendstoInMeasure μ f l g) (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (fun i ↦ f i + f' i) l (g + g') := by
  rw [tendstoInMeasure_iff_norm] at hf hf' ⊢
  intro ε hε
  have h := (hf (ε / 2) (by positivity)).add (hf' (ε / 2) (by positivity))
  rw [add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ zero_le) ?_
  intro i
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.add_apply] at hx ⊢
  by_contra! hcon
  have : ‖f i x + f' i x - (g x + g' x)‖ ≤ ‖f i x - g x‖ + ‖f' i x - g' x‖ := by
    rw [add_sub_add_comm]
    exact norm_add_le _ _
  linarith

/-- Convergence in measure is preserved by negation. -/
theorem TendstoInMeasure.neg (hf : TendstoInMeasure μ f l g) :
    TendstoInMeasure μ (fun i ↦ -f i) l (-g) := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  simpa only [Pi.neg_apply, neg_sub_neg, norm_sub_rev] using hf ε hε

/-- Convergence in measure is preserved by differences. -/
theorem TendstoInMeasure.sub (hf : TendstoInMeasure μ f l g) (hf' : TendstoInMeasure μ f' l g') :
    TendstoInMeasure μ (fun i ↦ f i - f' i) l (g - g') := by
  simpa [sub_eq_add_neg] using TendstoInMeasure.add hf (TendstoInMeasure.neg hf')

/-- Domination: if `f i → 0` in measure and eventually `‖h i ω‖ ≤ ‖f i ω‖` for every `ω`, then
`h i → 0` in measure. -/
theorem TendstoInMeasure.of_norm_le {h : ι → Ω → E} (hf : TendstoInMeasure μ f l 0)
    (hle : ∀ᶠ i in l, ∀ ω, ‖h i ω‖ ≤ ‖f i ω‖) : TendstoInMeasure μ h l 0 := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf ε hε)
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hle] with i hi
  refine measure_mono fun x hx ↦ ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero] at hx ⊢
  exact hx.trans (hi x)

end TendstoInMeasure

/-- The estimator sequence `θhat` is consistent for `θ` under `μ`: `θhat n` converges to `θ` in
probability. -/
def IsConsistent (θhat : ℕ → Ω → ℝ) (θ : ℝ) (μ : Measure Ω) : Prop :=
  TendstoInMeasure μ θhat atTop (fun _ ↦ θ)

/-- **Weak law of large numbers for the sample mean.** If `O` is an i.i.d. sample under a
probability measure `μ`, `f` is measurable and `f (O 0)` is integrable, then the sample mean
`n⁻¹ ∑_{i < n} f (O i)` is consistent for `E f (O 0)`. The proof goes through the strong law of
large numbers (`ProbabilityTheory.strong_law_ae_real`) and the fact that almost sure convergence
implies convergence in probability on a finite measure space. -/
theorem sampleMean_isConsistent {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪}
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω ↦ f (O 0 ω)) μ) :
    IsConsistent (sampleMean f O) (μ[fun ω ↦ f (O 0 ω)]) μ := by
  have hslln := strong_law_ae_real (fun i ω ↦ f (O i ω)) hint (hO.pairwise_indepFun hf)
    (hO.comp hf).ident
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) ?_
  · exact ((isSampleMeasurable_sampleMean hf O).aemeasurable hO n).aestronglyMeasurable
  · filter_upwards [hslln] with ω hω
    simpa [sampleMean, div_eq_inv_mul] using hω

end CausalInference
