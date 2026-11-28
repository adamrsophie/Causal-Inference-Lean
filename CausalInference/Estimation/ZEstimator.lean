/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.LawOfLargeNumbers

/-!
# Consistency of Z-estimators

A Z-estimator `θh n` is an approximate root of a random estimating function `Mn n` whose limit
`M` has a unique root `θ₀`. On a compact parameter set, uniform convergence of `Mn` to `M` in
probability makes `θh n` consistent for `θ₀`.

## Main results

* `CausalInference.tendstoInMeasure_of_isZEstimator`: the abstract consistency theorem on a
  compact set (no sample appears).
* `CausalInference.zEstimator_tendstoInMeasure`: the form for an i.i.d. sample, with the
  estimating function `n⁻¹ ∑_{i < n} ψ (O i) θ`; the uniform convergence comes from
  `uniform_law_of_large_numbers`.
* `CausalInference.sampleMean_tendstoInMeasure_of_mem_Icc`: an instance in which every hypothesis
  is checked: the sample mean of a variable with values in `[0, 1]`, as the root of
  `θ ↦ n⁻¹ ∑_{i < n} (f (O i) - θ)` on `K = [0, 1]`.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5 (Theorem 5.9 is the
version with a well separated root on a general parameter set).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}

/-- **Consistency of a Z-estimator on a compact set.** Let `K` be compact, `M` continuous on `K`
with `θ₀` its only possible root in `K`, `Mn → M` uniformly on `K` in probability, `θh n ∈ K` with
probability tending to one, and `Mn n (θh n) → 0` in probability (an approximate root). Then
`θh n → θ₀` in probability. Neither `θ₀ ∈ K` nor `M θ₀ = 0` is assumed, and no measurability of
`θh n` is needed. The proof: `‖M‖` has a positive minimum `m` on the compact set
`K \ ball θ₀ ε`, while on the good events `‖M (θh n)‖ < m`. -/
theorem tendstoInMeasure_of_isZEstimator {Θ F : Type*} [PseudoMetricSpace Θ]
    [NormedAddCommGroup F] {K : Set Θ} (hK : IsCompact K) {θ₀ : Θ} {M : Θ → F}
    (hM : ContinuousOn M K) (huniq : ∀ θ ∈ K, M θ = 0 → θ = θ₀) {Mn : ℕ → Ω → Θ → F}
    {θh : ℕ → Ω → Θ} (hunif : TendstoUniformlyOnInProbability μ Mn M K)
    (hin : WithProbTendingToOne μ (fun n ↦ {ω | θh n ω ∈ K}))
    (hroot : TendstoInMeasure μ (fun n ω ↦ Mn n ω (θh n ω)) atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ θh atTop (fun _ ↦ θ₀) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set C := K \ Metric.ball θ₀ ε with hCdef
  have hC : IsCompact C := hK.diff Metric.isOpen_ball
  have hmemC : ∀ θ, θ ∈ K → ε ≤ dist θ θ₀ → θ ∈ C := fun θ hθ hd ↦
    ⟨hθ, fun hb ↦ absurd (Metric.mem_ball.1 hb) (not_lt.2 hd)⟩
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hin (fun _ ↦ bot_le)
      fun n ↦ measure_mono fun ω hω hK' ↦ ?_
    have h := hmemC _ hK' hω
    rw [hCe] at h
    exact h
  · obtain ⟨θ₁, hθ₁C, hmin⟩ := hC.exists_isMinOn hCne (hM.mono Set.sdiff_subset).norm
    have hm : 0 < ‖M θ₁‖ := by
      rw [norm_pos_iff]
      intro h0
      apply hθ₁C.2
      rw [huniq θ₁ hθ₁C.1 h0]
      exact Metric.mem_ball_self hε
    have hev := (hin.inter (hunif _ (half_pos hm))).inter
      (hroot.withProbTendingToOne_dist_lt (half_pos hm))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hev (fun _ ↦ bot_le)
      fun n ↦ measure_mono fun ω hω hgood ↦ ?_
    obtain ⟨⟨hK', hu⟩, hr⟩ := hgood
    simp only [Set.mem_ofPred_eq] at hω hK' hu hr
    have h1 : ‖M θ₁‖ ≤ ‖M (θh n ω)‖ := hmin (hmemC _ hK' hω)
    have h2 := hu _ hK'
    rw [dist_eq_norm] at h2
    rw [dist_zero_right] at hr
    have h3 := norm_sub_le (Mn n ω (θh n ω)) (Mn n ω (θh n ω) - M (θh n ω))
    rw [sub_sub_cancel] at h3
    linarith

variable {O : ℕ → Ω → 𝒪}

/-- **Consistency of a Z-estimator from an i.i.d. sample.** Let `O` be an i.i.d. sample under a
probability measure, `K` a compact subset of a second countable metric space, and
`ψ : 𝒪 → Θ → F` (values in a separable Banach space) measurable in the observation for each
`θ ∈ K`, continuous on `K` for almost every observation value, and dominated on `K` by an
integrable envelope `H`. If `θ₀` is the only root in `K` of `θ ↦ E ψ (O 0) θ`, `θh n ∈ K` with
probability tending to one, and `n⁻¹ ∑_{i < n} ψ (O i) (θh n) → 0` in probability, then
`θh n → θ₀` in probability. -/
theorem zEstimator_tendstoInMeasure [IsProbabilityMeasure μ] {Θ F : Type*} [MetricSpace Θ]
    [SecondCountableTopology Θ] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (hO : IsIIDSample O μ)
    {K : Set Θ} (hK : IsCompact K) {ψ : 𝒪 → Θ → F} (hmeas : ∀ θ ∈ K, Measurable fun z ↦ ψ z θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ z) K) {H : 𝒪 → ℝ}
    (hH : Integrable H (μ.map (O 0))) (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ K, ‖ψ z θ‖ ≤ H z)
    {θ₀ : Θ} (huniq : ∀ θ ∈ K, ∫ z, ψ z θ ∂(μ.map (O 0)) = 0 → θ = θ₀) {θh : ℕ → Ω → Θ}
    (hin : WithProbTendingToOne μ (fun n ↦ {ω | θh n ω ∈ K}))
    (hroot : TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) (θh n ω))
      atTop (fun _ ↦ 0)) :
    TendstoInMeasure μ θh atTop (fun _ ↦ θ₀) := by
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers hO hK hmeas hcont hH hdom
  exact tendstoInMeasure_of_isZEstimator hK hMc huniq hunif hin hroot

/-- **Instance: the sample mean of a bounded variable as a Z-estimator.** For an i.i.d. sample
under a probability measure and a measurable `f` with values in `[0, 1]`, take `K = [0, 1]` and
`ψ z θ = f z - θ`. Every hypothesis of `zEstimator_tendstoInMeasure` holds: the envelope is the
constant `2`, the population estimating function `θ ↦ E f (O 0) - θ` has the single root
`E f (O 0)`, the sample mean lies in `K`, and it is an exact root. Hence the sample mean is
consistent for `E f (O 0)`. -/
theorem sampleMean_tendstoInMeasure_of_mem_Icc [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    {f : 𝒪 → ℝ} (hf : Measurable f) (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1) :
    TendstoInMeasure μ (sampleMean f O) atTop (fun _ ↦ μ[fun ω ↦ f (O 0 ω)]) := by
  have hfi : Integrable f (μ.map (O 0)) :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf01 z).1]; exact (hf01 z).2)
  have hmean : ∫ z, f z ∂(μ.map (O 0)) = μ[fun ω ↦ f (O 0 ω)] :=
    integral_map (hO.aemeasurable 0) hf.aestronglyMeasurable
  have hM : ∀ θ : ℝ, ∫ z, (f z - θ) ∂(μ.map (O 0)) = μ[fun ω ↦ f (O 0 ω)] - θ := fun θ ↦ by
    rw [integral_sub hfi (integrable_const θ), hmean]
    simp
  have hmem : ∀ n ω, sampleMean f O n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleMean]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨mul_nonneg (inv_nonneg.2 hn'.le) (sum_nonneg fun i _ ↦ (hf01 _).1), ?_⟩
    rw [sampleMean, inv_mul_le_iff₀ hn', mul_one]
    calc ∑ i ∈ range n, f (O i ω) ≤ ∑ _i ∈ range n, (1 : ℝ) := sum_le_sum fun i _ ↦ (hf01 _).2
      _ = n := by simp
  refine zEstimator_tendstoInMeasure (ψ := fun z θ ↦ f z - θ) (H := fun _ ↦ 2)
    (K := Set.Icc (0 : ℝ) 1) hO isCompact_Icc (fun θ _ ↦ hf.sub_const θ)
    (ae_of_all _ fun z ↦ (continuous_const.sub continuous_id).continuousOn)
    (integrable_const _) (ae_of_all _ fun z θ hθ ↦ ?_) (fun θ _ h ↦ ?_) ?_ ?_
  · rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(hf01 z).1, (hf01 z).2, hθ.1, hθ.2]
  · rw [hM] at h
    linarith
  · exact (withProbTendingToOne_univ).mono fun n ω _ ↦ hmem n ω
  · refine (tendstoInMeasure_const (μ := μ) (0 : ℝ)).congr_withProbTendingToOne
      withProbTendingToOne_univ fun n ω _ ↦ ?_
    simp only [smul_eq_mul, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sampleMean]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
      ring

end CausalInference
