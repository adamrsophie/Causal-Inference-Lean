/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.ConvergenceInProbability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Laws of large numbers for an i.i.d. sample

The sample is `CausalInference.IsIIDSample O μ`; the law of an observation is `μ.map (O 0)`.
Pointwise conditions on an observation (continuity or differentiability in a parameter, envelope
bounds) are stated almost everywhere for that law.

## Main definitions

* `CausalInference.TendstoUniformlyOnInProbability μ Mn M K`: uniform convergence on `K` in
  probability: for every `δ > 0`, with probability tending to one, `dist (Mn n ω θ) (M θ) < δ`
  for all `θ ∈ K`. It is stated with events, so no measurability of a supremum is needed.

## Main results

* `CausalInference.IsIIDSample.hasLaw_map`, `CausalInference.IsIIDSample.ae_forall`: every
  observation has the law of the first, and a property of almost every observation value holds
  almost surely for all observations at once.
* `CausalInference.IsIIDSample.tendsto_ae_smul_sum` and
  `CausalInference.IsIIDSample.tendstoInMeasure_smul_sum`: the strong and weak laws of large
  numbers for an integrable function with values in a Banach space.
* `CausalInference.uniform_law_of_large_numbers`: **uniform law of large numbers** on a compact
  parameter set, for functions continuous in the parameter and dominated by an integrable
  envelope; `CausalInference.uniform_law_of_large_numbers_real` is its form for the real sample
  mean `CausalInference.sampleMean`.
* `CausalInference.TendstoUniformlyOnInProbability.comp_tendstoInMeasure`: plug-in of a
  consistent parameter estimate into a uniformly convergent random function.

References: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 2 and 5 (the uniform
law in the Glivenko-Cantelli form for a compact parameter set and continuous functions with an
integrable envelope, which goes back to R. I. Jennrich (1969), *Asymptotic properties of
non-linear least squares estimators*, Annals of Mathematical Statistics).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪] {μ : Measure Ω}
  {O : ℕ → Ω → 𝒪}

namespace IsIIDSample

/-- Every observation of an i.i.d. sample has the law `μ.map (O 0)` of the first one. -/
theorem hasLaw_map (hO : IsIIDSample O μ) (i : ℕ) : HasLaw (O i) (μ.map (O 0)) μ :=
  ⟨hO.aemeasurable i, (hO.ident i).map_eq⟩

/-- A property of almost every value of an observation holds almost surely for all observations
of an i.i.d. sample at once. -/
theorem ae_forall (hO : IsIIDSample O μ) {p : 𝒪 → Prop} (hp : ∀ᵐ x ∂(μ.map (O 0)), p x) :
    ∀ᵐ ω ∂μ, ∀ i, p (O i ω) :=
  ae_all_iff.2 fun i ↦ ae_of_ae_map (hO.aemeasurable i) (by rw [(hO.ident i).map_eq]; exact hp)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Strong law of large numbers in a Banach space.** For an i.i.d. sample under a probability
measure and a measurable `f` with `f (O 0)` integrable, `n⁻¹ ∑_{i < n} f (O i)` converges almost
surely to `E f (O 0)`. -/
theorem tendsto_ae_smul_sum [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {f : 𝒪 → E}
    (hf : Measurable f) (hint : Integrable (fun ω ↦ f (O 0 ω)) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) atTop
      (𝓝 (μ[fun ω ↦ f (O 0 ω)])) :=
  strong_law_ae (fun i ω ↦ f (O i ω)) hint (fun _ _ hij ↦ (hO.comp hf).indep.indepFun hij)
    (hO.comp hf).ident

/-- **Weak law of large numbers in a Banach space.** For an i.i.d. sample under a probability
measure and a measurable `f` into a separable Banach space with `f (O 0)` integrable,
`n⁻¹ ∑_{i < n} f (O i)` converges in probability to `E f (O 0)`. -/
theorem tendstoInMeasure_smul_sum [IsProbabilityMeasure μ] [SecondCountableTopology E]
    (hO : IsIIDSample O μ) {f : 𝒪 → E}
    (hf : Measurable f) (hint : Integrable (fun ω ↦ f (O 0 ω)) μ) :
    TendstoInMeasure μ (fun (n : ℕ) ω ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, f (O i ω)) atTop
      (fun _ ↦ μ[fun ω ↦ f (O 0 ω)]) :=
  tendstoInMeasure_of_tendsto_ae (fun _ ↦ ((Finset.aemeasurable_fun_sum _ fun i _ ↦
    hf.comp_aemeasurable (hO.aemeasurable i)).const_smul _).aestronglyMeasurable)
    (hO.tendsto_ae_smul_sum hf hint)

end IsIIDSample

/-- The real weak law of large numbers `sampleMean_isConsistent` is the case `E = ℝ` of
`IsIIDSample.tendstoInMeasure_smul_sum`. -/
example [IsProbabilityMeasure μ] (hO : IsIIDSample O μ) {f : 𝒪 → ℝ} (hf : Measurable f)
    (hint : Integrable (fun ω ↦ f (O 0 ω)) μ) :
    IsConsistent (sampleMean f O) (μ[fun ω ↦ f (O 0 ω)]) μ :=
  hO.tendstoInMeasure_smul_sum hf hint

/-! ### Uniform convergence in probability and the uniform law of large numbers -/

/-- Uniform convergence on `K` in probability: for every `δ > 0`, with probability tending to one,
`dist (Mn n ω θ) (M θ) < δ` for all `θ ∈ K`. -/
def TendstoUniformlyOnInProbability {Θ F : Type*} [PseudoMetricSpace F] (μ : Measure Ω)
    (Mn : ℕ → Ω → Θ → F) (M : Θ → F) (K : Set Θ) : Prop :=
  ∀ δ, 0 < δ → WithProbTendingToOne μ (fun n ↦ {ω | ∀ θ ∈ K, dist (Mn n ω θ) (M θ) < δ})

/-- **Plug-in under a uniform law.** If `Mn → M` uniformly in probability on a neighborhood `K` of
`θ₀`, `M` is continuous at `θ₀` and `θh n → θ₀` in probability, then `Mn n (θh n) → M θ₀` in
probability. -/
theorem TendstoUniformlyOnInProbability.comp_tendstoInMeasure {Θ F : Type*} [PseudoMetricSpace Θ]
    [PseudoMetricSpace F] {Mn : ℕ → Ω → Θ → F} {M : Θ → F} {K : Set Θ} {θ₀ : Θ}
    (hunif : TendstoUniformlyOnInProbability μ Mn M K) (hK : K ∈ 𝓝 θ₀) (hM : ContinuousAt M θ₀)
    {θh : ℕ → Ω → Θ} (hθ : TendstoInMeasure μ θh atTop (fun _ ↦ θ₀)) :
    TendstoInMeasure μ (fun n ω ↦ Mn n ω (θh n ω)) atTop (fun _ ↦ M θ₀) := by
  refine tendstoInMeasure_of_good_events fun ε hε κ hκ ↦ ?_
  obtain ⟨δ, hδ, hMδ⟩ := Metric.continuousAt_iff.1 hM (ε / 2) (by positivity)
  obtain ⟨δ', hδ', hball⟩ := Metric.mem_nhds_iff.1 hK
  have hev := ((hθ.withProbTendingToOne_dist_lt (lt_min hδ hδ')).inter
    (hunif (ε / 2) (by positivity))).eventually_le hκ
  refine ⟨_, hev, Eventually.of_forall fun n ω hω ↦ ?_⟩
  obtain ⟨h1, h2⟩ := hω
  simp only [Set.mem_ofPred_eq] at h1 h2
  have hin : θh n ω ∈ K := hball (lt_of_lt_of_le h1 (min_le_right _ _))
  calc dist (Mn n ω (θh n ω)) (M θ₀)
      ≤ dist (Mn n ω (θh n ω)) (M (θh n ω)) + dist (M (θh n ω)) (M θ₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h2 _ hin) (hMδ (lt_of_lt_of_le h1 (min_le_left _ _)))
    _ = ε := add_halves ε

/-- **Uniform law of large numbers on a compact parameter set.** Let `O` be an i.i.d. sample under
a probability measure, `K` a compact subset of a second countable metric space, and
`ψ : 𝒪 → Θ → F` with values in a separable Banach space such that `z ↦ ψ z θ` is measurable for
each `θ ∈ K`, `ψ z` is continuous on `K` for almost every observation value `z`, and
`‖ψ z θ‖ ≤ H z` on `K` for an integrable envelope `H`. Then `θ ↦ E ψ (O 0) θ` is continuous on
`K`, and `n⁻¹ ∑_{i < n} ψ (O i) θ` converges to it uniformly on `K` in probability.

The proof regards each observation as the element `z ↦ ψ z |_K` of the separable Banach space
`C(K, F)`, set to `0` on a measurable null set, applies the Banach-valued law of large numbers
there, and evaluates at `θ`. -/
theorem uniform_law_of_large_numbers [IsProbabilityMeasure μ] {Θ F : Type*} [MetricSpace Θ]
    [SecondCountableTopology Θ] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (hO : IsIIDSample O μ)
    {K : Set Θ} (hK : IsCompact K) {ψ : 𝒪 → Θ → F} (hmeas : ∀ θ ∈ K, Measurable fun z ↦ ψ z θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ z) K) {H : 𝒪 → ℝ}
    (hH : Integrable H (μ.map (O 0))) (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ K, ‖ψ z θ‖ ≤ H z) :
    ContinuousOn (fun θ ↦ ∫ z, ψ z θ ∂(μ.map (O 0))) K ∧
      TendstoUniformlyOnInProbability μ
        (fun n ω θ ↦ (n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) θ)
        (fun θ ↦ ∫ z, ψ z θ ∂(μ.map (O 0))) K := by
  classical
  set ν := μ.map (O 0) with hν
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hcont.and hdom))
  have hgoodN : ∀ z, z ∉ N → ContinuousOn (ψ z) K ∧ ∀ θ ∈ K, ‖ψ z θ‖ ≤ H z := fun z hz ↦ by
    by_contra h
    exact hz (hNsub h)
  let Ψ : 𝒪 → C(K, F) := fun z ↦
    if hz : z ∈ N then 0 else ⟨K.domRestrict (ψ z), (hgoodN z hz).1.domRestrict⟩
  have hΨapp : ∀ z, z ∉ N → ∀ θ : K, Ψ z θ = ψ z θ := fun z hz θ ↦ by
    simp [Ψ, hz, Set.domRestrict]
  have hΨmeas : Measurable Ψ := by
    rw [ContinuousMap.measurable_iff_eval]
    intro θ
    have h : (fun z ↦ Ψ z θ) = N.piecewise (fun _ ↦ 0) (fun z ↦ ψ z θ) := by
      funext z
      by_cases hz : z ∈ N
      · simp [Ψ, hz]
      · rw [hΨapp z hz θ, Set.piecewise_eq_of_notMem _ _ _ hz]
    rw [h]
    exact Measurable.piecewise hNm measurable_const (hmeas θ θ.2)
  have hΨint : Integrable Ψ ν := by
    refine hH.abs.mono' hΨmeas.aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
    by_cases hz : z ∈ N
    · simp [Ψ, hz]
    · refine (ContinuousMap.norm_le _ (abs_nonneg _)).2 fun θ ↦ ?_
      rw [hΨapp z hz θ]
      exact ((hgoodN z hz).2 θ θ.2).trans (le_abs_self _)
  have hint : ∀ θ : K, ∫ z, ψ z θ ∂ν = (∫ z, Ψ z ∂ν) θ := fun θ ↦ by
    rw [ContinuousMap.integral_apply hΨint]
    refine integral_congr_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with z hz
    exact (hΨapp z hz θ).symm
  refine ⟨?_, fun δ hδ ↦ ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have h : K.domRestrict (fun θ ↦ ∫ z, ψ z θ ∂ν) = ⇑(∫ z, Ψ z ∂ν) := funext hint
    rw [h]
    exact (∫ z, Ψ z ∂ν).continuous
  · have hΨint' : Integrable (fun ω ↦ Ψ (O 0 ω)) μ :=
      (integrable_map_measure hΨmeas.aestronglyMeasurable (hO.aemeasurable 0)).1 hΨint
    have hL := hO.tendstoInMeasure_smul_sum hΨmeas hΨint'
    have hmean : μ[fun ω ↦ Ψ (O 0 ω)] = ∫ z, Ψ z ∂ν :=
      (integral_map (hO.aemeasurable 0) hΨmeas.aestronglyMeasurable).symm
    rw [hmean] at hL
    have hnull : WithProbTendingToOne μ (fun _ ↦ {ω | ∀ i, O i ω ∉ N}) :=
      WithProbTendingToOne.of_ae (hO.ae_forall (measure_eq_zero_iff_ae_notMem.1 hN0))
    refine ((hL.withProbTendingToOne_dist_lt hδ).inter hnull).mono fun n ω hω θ hθ ↦ ?_
    obtain ⟨h1, h2⟩ := hω
    simp only [Set.mem_ofPred_eq] at h1 h2
    have h2' : ∀ i, Ψ (O i ω) ⟨θ, hθ⟩ = ψ (O i ω) θ := fun i ↦ hΨapp _ (h2 i) ⟨θ, hθ⟩
    have heq : (n : ℝ)⁻¹ • ∑ i ∈ range n, ψ (O i ω) θ =
        ((n : ℝ)⁻¹ • ∑ i ∈ range n, Ψ (O i ω)) ⟨θ, hθ⟩ := by
      simp [h2']
    dsimp only
    rw [heq, hint ⟨θ, hθ⟩]
    exact (ContinuousMap.dist_apply_le_dist _).trans_lt h1

/-- **Uniform law of large numbers for real sample means.** The case `F = ℝ` of
`uniform_law_of_large_numbers`, written with `sampleMean`. -/
theorem uniform_law_of_large_numbers_real [IsProbabilityMeasure μ] {Θ : Type*} [MetricSpace Θ]
    [SecondCountableTopology Θ] (hO : IsIIDSample O μ) {K : Set Θ} (hK : IsCompact K)
    {ψ : 𝒪 → Θ → ℝ} (hmeas : ∀ θ ∈ K, Measurable fun z ↦ ψ z θ)
    (hcont : ∀ᵐ z ∂(μ.map (O 0)), ContinuousOn (ψ z) K) {H : 𝒪 → ℝ}
    (hH : Integrable H (μ.map (O 0))) (hdom : ∀ᵐ z ∂(μ.map (O 0)), ∀ θ ∈ K, |ψ z θ| ≤ H z) :
    ContinuousOn (fun θ ↦ ∫ z, ψ z θ ∂(μ.map (O 0))) K ∧
      TendstoUniformlyOnInProbability μ (fun n ω θ ↦ sampleMean (fun z ↦ ψ z θ) O n ω)
        (fun θ ↦ ∫ z, ψ z θ ∂(μ.map (O 0))) K :=
  uniform_law_of_large_numbers hO hK hmeas hcont hH
    (hdom.mono fun z hz θ hθ ↦ by simpa [Real.norm_eq_abs] using hz θ hθ)

end CausalInference
