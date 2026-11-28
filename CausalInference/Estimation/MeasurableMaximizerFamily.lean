/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.MeasurableMaximizer
public import CausalInference.Estimation.MaximumLikelihood
public import CausalInference.PopulationAdjustment.OutcomeModelFitLikelihood

/-!
# A measurable maximum likelihood estimator of a parametric family

Let `F` be a parametric family on `S` with parameters in `κ → ℝ`, `κ` finite, and `K` a compact
nonempty set of parameters on which every density `θ ↦ f(s;θ)` is continuous. The likelihood
`∏ᵢ f(xᵢ;θ)` of a data vector `x : Fin n → S` is measurable in `x` (each `f(·;θ)` is measurable)
and continuous in `θ` on `K`, so a maximizer over `K` can be chosen measurably in the data
(`ParametricFamily.exists_measurable_isMaxOn_likelihood`).

Applied to the first `n` observations of a sample with almost everywhere measurable
observations, this gives a maximum likelihood estimator `θ̂` that maximizes the likelihood over
`K` for every `n` and every outcome and is almost everywhere measurable
(`ParametricFamily.exists_isMLE_aemeasurable`).

## Main results

* `ParametricFamily.exists_measurable_isMaxOn_likelihood`.
* `ParametricFamily.exists_isMLE_aemeasurable`.
* `ParametricFamily.exists_isMLE_aemeasurable_logisticFamily`: the hypotheses hold for the
  logistic family of records on every closed ball of coefficients.

## References

* A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalInference

namespace ParametricFamily

variable {κ S : Type*} [Finite κ] [MeasurableSpace S]

/-- **A measurable maximizer of the likelihood of a data vector.** For a parametric family with
parameters in `κ → ℝ`, a compact nonempty `K` and densities continuous in the parameter on
`K`, there is a measurable `g : (Fin n → S) → κ → ℝ` with `g x ∈ K` maximizing
`θ ↦ ∏ᵢ f(xᵢ;θ)` over `K` for every data vector `x`. -/
theorem exists_measurable_isMaxOn_likelihood (F : ParametricFamily (κ → ℝ) S)
    {K : Set (κ → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (hc : ∀ s, ContinuousOn (fun θ ↦ F.density θ s) K) (n : ℕ) :
    ∃ g : (Fin n → S) → κ → ℝ, Measurable g ∧
      ∀ x, g x ∈ K ∧ IsMaxOn (fun θ ↦ ∏ i, F.density θ (x i)) K (g x) :=
  exists_measurable_forall_isMaxOn
    (fun θ _ ↦ Finset.measurable_prod _ fun i _ ↦
      (F.measurable_density θ).comp (measurable_pi_apply i))
    hK hne fun x ↦ continuousOn_finsetProd _ fun i _ ↦ hc (x i)

/-- **An almost everywhere measurable maximum likelihood estimator.** Under the hypotheses of
`exists_measurable_isMaxOn_likelihood`, for a sample `O` with almost everywhere measurable
observations there is a sequence `θ̂` of almost everywhere measurable maps such that for every
`n` and every `ω`, `θ̂_n ω ∈ K` maximizes the likelihood of the first `n` observations over `K`;
in particular `θ̂` is a maximum likelihood estimator over `K`. -/
theorem exists_isMLE_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : ParametricFamily (κ → ℝ) S) {K : Set (κ → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (hc : ∀ s, ContinuousOn (fun θ ↦ F.density θ s) K) {O : ℕ → Ω → S}
    (hO : ∀ i, AEMeasurable (O i) μ) :
    ∃ θh : ℕ → Ω → κ → ℝ, (∀ n, AEMeasurable (θh n) μ) ∧
      (∀ n ω, θh n ω ∈ K ∧ IsMaxOn (F.likelihood O n ω) K (θh n ω)) ∧ F.IsMLE μ K O θh := by
  choose g hgm hg using fun n ↦ F.exists_measurable_isMaxOn_likelihood hK hne hc n
  have hl : ∀ n ω θ, F.likelihood O n ω θ = ∏ i : Fin n, F.density θ (O i ω) := fun n ω θ ↦
    (Finset.prod_range fun i ↦ F.density θ (O i ω))
  have hmax : ∀ n ω, g n (fun i : Fin n ↦ O i ω) ∈ K ∧
      IsMaxOn (F.likelihood O n ω) K (g n fun i : Fin n ↦ O i ω) := fun n ω ↦ by
    refine ⟨(hg n _).1, fun θ hθ ↦ ?_⟩
    have h := (hg n fun i : Fin n ↦ O i ω).2 hθ
    simp only [mem_ofPred_eq] at h ⊢
    rwa [hl, hl]
  refine ⟨fun n ω ↦ g n fun i : Fin n ↦ O i ω, fun n ↦ (hgm n).comp_aemeasurable
    (AEMeasurable.of_eval fun i ↦ hO i), hmax, fun n ↦ ae_of_all _ fun ω ↦
    ⟨(hmax n ω).1, fun θ hθ ↦ (hmax n ω).2 hθ⟩⟩

omit [Finite κ] in
open PopulationAdjustment in
/-- **The logistic family has an almost everywhere measurable maximum likelihood estimator** on
every closed ball of coefficients, for every sample with almost everywhere measurable records. -/
theorem exists_isMLE_aemeasurable_logisticFamily [Fintype κ] {C Ω : Type*} [MeasurableSpace C]
    [MeasurableSpace Ω] {μ : Measure Ω} {R : Measure C} [IsProbabilityMeasure R]
    {z : C → κ → ℝ} (hz : ∀ j, Measurable fun c ↦ z c j) (ξ : κ → ℝ) {r : ℝ} (hr : 0 ≤ r)
    {O : ℕ → Ω → C × ℝ} (hO : ∀ i, AEMeasurable (O i) μ) :
    ∃ θh : ℕ → Ω → κ → ℝ, (∀ n, AEMeasurable (θh n) μ) ∧
      (glmFamily logisticKernel R z hz).IsMLE μ (Metric.closedBall ξ r) O θh :=
  have ⟨θh, hm, _, h⟩ := (glmFamily logisticKernel R z hz).exists_isMLE_aemeasurable
    (isCompact_closedBall ξ r) ⟨ξ, Metric.mem_closedBall_self hr⟩
    (fun q ↦ ((continuous_logisticDens q.2).comp
      (continuous_const.dotProduct continuous_id)).continuousOn) hO
  ⟨θh, hm, h⟩

end ParametricFamily

end CausalInference
