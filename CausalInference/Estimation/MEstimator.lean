/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ZEstimator

/-!
# Consistency of M-estimators

An M-estimator `θh n` approximately maximizes a random criterion `Mn n` whose limit `M` has a
unique maximizer `θ₀`. On a compact parameter set, uniform convergence of `Mn` to `M` in
probability makes `θh n` consistent for `θ₀`.

## Main results

* `CausalInference.tendstoInMeasure_of_isMEstimator`: the abstract consistency theorem on a
  compact set (no sample appears).
* `CausalInference.mEstimator_tendstoInMeasure`: the form for an i.i.d. sample, with the
  criterion `n⁻¹ ∑_{i < n} m (O i) θ`; the uniform convergence comes from
  `uniform_law_of_large_numbers_real`.
* `CausalInference.sampleMean_tendstoInMeasure_of_isMEstimator`: an instance in which every
  hypothesis is checked: the sample mean of a variable with values in `[0, 1]` maximizes the
  least squares criterion `θ ↦ -n⁻¹ ∑_{i < n} (f (O i) - θ)²`.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 5 (Theorem 5.7 is the
version with a well separated maximizer on a general parameter set).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}

/-- **Consistency of an M-estimator on a compact set.** Let `K` be compact, `M` continuous on `K`
with the unique maximizer `θ₀ ∈ K`, `Mn → M` uniformly on `K` in probability, `θh n ∈ K` with
probability tending to one, and `θh n` an approximate maximizer: for every `δ > 0`, with
probability tending to one, `Mn n θ₀ ≤ Mn n (θh n) + δ` (an exact maximizer on `K` satisfies
this). Then `θh n → θ₀` in probability. The gap `M θ₀ - max_{K \ ball θ₀ ε} M` is positive by
compactness, and on the good events `M (θh n)` exceeds that maximum. -/
theorem tendstoInMeasure_of_isMEstimator {Θ : Type*} [PseudoMetricSpace Θ] {K : Set Θ}
    (hK : IsCompact K) {θ₀ : Θ} (hθ₀ : θ₀ ∈ K) {M : Θ → ℝ} (hM : ContinuousOn M K)
    (hmax : ∀ θ ∈ K, θ ≠ θ₀ → M θ < M θ₀) {Mn : ℕ → Ω → Θ → ℝ} {θh : ℕ → Ω → Θ}
    (hunif : TendstoUniformlyOnInProbability μ Mn M K)
    (hin : WithProbTendingToOne μ (fun n ↦ {ω | θh n ω ∈ K}))
    (happrox : ∀ δ, 0 < δ →
      WithProbTendingToOne μ (fun n ↦ {ω | Mn n ω θ₀ ≤ Mn n ω (θh n ω) + δ})) :
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
  · obtain ⟨θ₁, hθ₁C, hmaxOn⟩ := hC.exists_isMaxOn hCne (hM.mono Set.sdiff_subset)
    have hne : θ₁ ≠ θ₀ := fun h ↦ hθ₁C.2 (h ▸ Metric.mem_ball_self hε)
    have hg : 0 < (M θ₀ - M θ₁) / 3 := by linarith [hmax θ₁ hθ₁C.1 hne]
    have hev := (hin.inter (hunif _ hg)).inter (happrox _ hg)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hev (fun _ ↦ bot_le)
      fun n ↦ measure_mono fun ω hω hgood ↦ ?_
    obtain ⟨⟨hK', hu⟩, ha⟩ := hgood
    simp only [Set.mem_ofPred_eq] at hω hK' hu ha
    have h1 : M (θh n ω) ≤ M θ₁ := hmaxOn (hmemC _ hK' hω)
    have h2 := hu _ hK'
    have h3 := hu θ₀ hθ₀
    rw [Real.dist_eq] at h2 h3
    have h2' := abs_lt.1 h2
    have h3' := abs_lt.1 h3
    linarith

variable {O : ℕ → Ω → 𝒪}

/-- **Consistency of an M-estimator from an i.i.d. sample.** Let `O` be an i.i.d. sample under a
probability measure, `K` a compact subset of a second countable metric space, and
`m : 𝒪 → Θ → ℝ` measurable in the observation for each `θ ∈ K`, continuous on `K` for almost
every observation value, and dominated on `K` by an integrable envelope `H`. If `θ₀ ∈ K` is the
unique maximizer on `K` of `θ ↦ E m (O 0) θ`, `θh n ∈ K` with probability tending to one, and
`θh n` is an approximate maximizer of the sample criterion `θ ↦ n⁻¹ ∑_{i < n} m (O i) θ`, then
`θh n → θ₀` in probability. -/
theorem mEstimator_tendstoInMeasure [IsProbabilityMeasure μ] {Θ : Type*} [MetricSpace Θ]
    [SecondCountableTopology Θ] (hO : IsIIDSample O μ) {K : Set Θ} (hK : IsCompact K)
    {m : 𝒪 → Θ → ℝ} (hmeas : ∀ θ ∈ K, Measurable fun z ↦ m z θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (m z) K) {H : 𝒪 → ℝ}
    (hH : Integrable H (μ.map (O 0))) (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ K, |m z θ| ≤ H z)
    {θ₀ : Θ} (hθ₀ : θ₀ ∈ K)
    (hmax : ∀ θ ∈ K, θ ≠ θ₀ → ∫ z, m z θ ∂(μ.map (O 0)) < ∫ z, m z θ₀ ∂(μ.map (O 0)))
    {θh : ℕ → Ω → Θ} (hin : WithProbTendingToOne μ (fun n ↦ {ω | θh n ω ∈ K}))
    (happrox : ∀ δ, 0 < δ → WithProbTendingToOne μ (fun n ↦
      {ω | sampleMean (fun z ↦ m z θ₀) O n ω ≤ sampleMean (fun z ↦ m z (θh n ω)) O n ω + δ})) :
    TendstoInMeasure μ θh atTop (fun _ ↦ θ₀) := by
  obtain ⟨hMc, hunif⟩ := uniform_law_of_large_numbers_real hO hK hmeas hcont hH hdom
  exact tendstoInMeasure_of_isMEstimator hK hθ₀ hMc hmax hunif hin happrox

omit [MeasurableSpace 𝒪] in
/-- The least squares identity for the sample mean: the sample mean of `(f (O i) - θ)²` exceeds
its value at `θ = sampleMean f O n` by `(θ - sampleMean f O n)²`, for `n ≥ 1`. -/
theorem sampleMean_sq_sub_eq {f : 𝒪 → ℝ} {n : ℕ} (hn : n ≠ 0) (ω : Ω) (θ : ℝ) :
    sampleMean (fun z ↦ (f z - θ) ^ 2) O n ω =
      sampleMean (fun z ↦ (f z - sampleMean f O n ω) ^ 2) O n ω +
        (θ - sampleMean f O n ω) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h : ∀ t : ℝ, ∑ i ∈ range n, (f (O i ω) - t) ^ 2 =
      ∑ i ∈ range n, f (O i ω) ^ 2 - 2 * t * ∑ i ∈ range n, f (O i ω) + n * t ^ 2 := by
    intro t
    rw [show ∑ i ∈ range n, (f (O i ω) - t) ^ 2 =
        ∑ i ∈ range n, (f (O i ω) ^ 2 - 2 * t * f (O i ω) + t ^ 2) from
        sum_congr rfl fun i _ ↦ by ring, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
      card_range, nsmul_eq_mul]
  simp only [sampleMean]
  rw [h θ, h]
  field_simp
  ring

/-- **Instance: the sample mean of a bounded variable as an M-estimator.** For an i.i.d. sample
under a probability measure and a measurable `f` with values in `[0, 1]`, take `K = [0, 1]` and
the least squares criterion `m z θ = -(f z - θ)²`. Every hypothesis of
`mEstimator_tendstoInMeasure` holds: the envelope is the constant `1`, the population criterion
`-E (f (O 0) - θ)²` has the unique maximizer `E f (O 0)` (it equals the maximum minus
`(θ - E f (O 0))²`), the sample mean lies in `K`, and it maximizes the sample criterion exactly
(`sampleMean_sq_sub_eq`). Hence the sample mean is consistent for `E f (O 0)`. -/
theorem sampleMean_tendstoInMeasure_of_isMEstimator [IsProbabilityMeasure μ]
    (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hf01 : ∀ z, f z ∈ Set.Icc (0 : ℝ) 1) :
    TendstoInMeasure μ (sampleMean f O) atTop (fun _ ↦ μ[fun ω ↦ f (O 0 ω)]) := by
  set ν := μ.map (O 0) with hν
  have hbdd : ∀ z, |f z| ≤ 1 := fun z ↦ by
    rw [abs_of_nonneg (hf01 z).1]; exact (hf01 z).2
  have hfi : Integrable f ν :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ fun z ↦ hbdd z)
  have hf2i : Integrable (fun z ↦ f z ^ 2) ν :=
    (integrable_const (1 : ℝ)).mono' (hf.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z ↦ by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (hbdd z))
  set a := ∫ z, f z ∂ν with ha
  have hmean : a = μ[fun ω ↦ f (O 0 ω)] :=
    integral_map (hO.aemeasurable 0) hf.aestronglyMeasurable
  have hcrit : ∀ θ : ℝ, ∫ z, -(f z - θ) ^ 2 ∂ν = -(∫ z, f z ^ 2 ∂ν) + a ^ 2 - (θ - a) ^ 2 := by
    intro θ
    have hexp : (fun z ↦ -(f z - θ) ^ 2) =
        fun z ↦ -(f z ^ 2) + 2 * θ * f z - θ ^ 2 := by
      funext z; ring
    have h1 : Integrable (fun z ↦ -(f z ^ 2) + 2 * θ * f z) ν :=
      hf2i.neg.add (hfi.const_mul (2 * θ))
    have h2 : Integrable (fun z ↦ -(f z ^ 2)) ν := hf2i.neg
    have h3 : Integrable (fun z ↦ 2 * θ * f z) ν := hfi.const_mul (2 * θ)
    rw [hexp, integral_sub h1 (integrable_const _), integral_add h2 h3, integral_neg,
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hmem : ∀ n ω, sampleMean f O n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleMean]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine ⟨mul_nonneg (inv_nonneg.2 hn'.le) (sum_nonneg fun i _ ↦ (hf01 _).1), ?_⟩
    rw [sampleMean, inv_mul_le_iff₀ hn', mul_one]
    calc ∑ i ∈ range n, f (O i ω) ≤ ∑ _i ∈ range n, (1 : ℝ) := sum_le_sum fun i _ ↦ (hf01 _).2
      _ = n := by simp
  have haK : a ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact integral_nonneg fun z ↦ (hf01 z).1
    · calc a ≤ ∫ _z, (1 : ℝ) ∂ν := integral_mono hfi (integrable_const _) fun z ↦ (hf01 z).2
        _ = 1 := by simp
  rw [← hmean]
  refine mEstimator_tendstoInMeasure (m := fun z θ ↦ -(f z - θ) ^ 2) (H := fun _ ↦ 1)
    (K := Set.Icc (0 : ℝ) 1) hO isCompact_Icc (fun θ _ ↦ ((hf.sub_const θ).pow_const 2).neg)
    (ae_of_all _ fun z ↦ (by fun_prop : Continuous fun θ : ℝ ↦ -(f z - θ) ^ 2).continuousOn)
    (integrable_const _) (ae_of_all _ fun z θ hθ ↦ ?_) haK (fun θ _ hθ ↦ ?_) ?_ fun δ hδ ↦ ?_
  · rw [abs_neg, abs_pow]
    have h1 : |f z - θ| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [(hf01 z).1, (hf01 z).2, hθ.1, hθ.2]
    exact pow_le_one₀ (abs_nonneg _) h1
  · rw [hcrit, hcrit, sub_self]
    have : 0 < (θ - a) ^ 2 := by
      have : θ - a ≠ 0 := sub_ne_zero.2 hθ
      positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]
    linarith
  · exact withProbTendingToOne_univ.mono fun n ω _ ↦ hmem n ω
  · refine withProbTendingToOne_univ.mono fun n ω _ ↦ ?_
    simp only [Set.mem_ofPred_eq]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [sampleMean] using hδ.le
    have hneg : ∀ g : 𝒪 → ℝ, sampleMean (fun z ↦ -g z) O n ω = -sampleMean g O n ω := by
      intro g
      simp [sampleMean, sum_neg_distrib]
    rw [hneg, hneg, sampleMean_sq_sub_eq hn.ne' ω a]
    nlinarith [sq_nonneg (a - sampleMean f O n ω)]

end CausalInference
