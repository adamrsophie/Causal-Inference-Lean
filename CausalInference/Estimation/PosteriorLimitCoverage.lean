/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitQuantile
public import CausalInference.Estimation.LimitLaws
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Frequentist coverage of the equal tailed credible interval

**For a real target.** Let the random posterior laws `Q_n` of a real target satisfy the weak
Bernstein and von Mises conclusion with centering `a_n` and limit `N(0, v)`, `v > 0`, and let the
centering have the matching sampling law: `√n (a_n - ψ₀) → N(0, v)` in distribution. For
`α ∈ (0, 1)` and `Φ(z) = 1 - α/2`:

* `√n (q_n(1 - α/2) - a_n) → √v z` and `√n (q_n(α/2) - a_n) → -√v z` in probability
  (`IsBernsteinVonMisesWeak.tendstoInMeasure_credibleInterval_endpoints`);
* the credible interval `[q_n(α/2), q_n(1 - α/2)]` covers `ψ₀` with probability tending to
  `1 - α` (`IsBernsteinVonMisesWeak.tendsto_credibleInterval_coverage`).

The second hypothesis is not a consequence of the first: the Bernstein and von Mises conclusion
is a statement about the posterior given the data, the normality of the centering a statement
about the sampling law, and coverage needs both with the same variance `v`. No measurability of
the quantiles in the data is assumed; the coverage event is squeezed between two events
`{|√n (a_n - ψ₀)| ≤ √v z ± δ}` up to an event of probability tending to zero.

**For a smooth functional of a parameter**
(`IsBernsteinVonMisesWeak.tendsto_credibleInterval_coverage_map`). The posteriors `Π_n` of a
parameter satisfy the weak conclusion with a centered Gaussian limit `N`, the centering satisfies
`√n (θ̂_n - θ₀) → N` in distribution, `Ψ` is strictly differentiable at `θ₀` with derivative `D`,
and the limiting variance `Var(D Z)`, `Z ∼ N`, is positive. Then the equal tailed credible interval
of `Ψ_# Π_n` covers `Ψ(θ₀)` with probability tending to `1 - α`. Consistency of `θ̂_n` follows from
its `√n` normality (`tendstoInMeasure_of_tendstoInDistribution_sqrt_smul`).

**A vanishing derivative.** For `Ψ(θ) = θ²` at `θ₀ = 0` the derivative is `0` and the limit law
`D_# N` is the point mass at `0`. The rescaled posterior quantiles still converge (to `0`), but
for every posterior law without an atom at `0`, for instance every normal posterior, the lower
endpoint `q(α/2)` of the credible interval of `θ²` is positive, so the interval never contains
`Ψ(0) = 0`: the coverage is `0` at every sample size (`sq_credibleInterval_coverage`).

## Main results

* `IsBernsteinVonMisesWeak.tendstoInMeasure_credibleInterval_endpoints`,
  `IsBernsteinVonMisesWeak.tendsto_credibleInterval_coverage`,
  `IsBernsteinVonMisesWeak.tendsto_credibleInterval_coverage_map`.
* `tendstoInMeasure_of_tendstoInDistribution_sqrt_smul`, `zero_notMem_credibleInterval_sq`,
  `sq_credibleInterval_coverage`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open BiasAnalysis.Distributions

/-- The standard normal distribution function is odd about `1/2`: `Φ(-x) = 1 - Φ(x)`. -/
lemma cdf_gaussianReal_zero_one_neg (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  have := nullSingletonClass_gaussianReal (μ := 0) (one_ne_zero (α := ℝ≥0))
  have hsymm : (gaussianReal 0 1).map (fun x ↦ -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := 0) (v := 1)
  rw [cdf_eq_real, cdf_eq_real]
  conv_lhs => rw [← hsymm]
  rw [map_measureReal_apply measurable_neg measurableSet_Iic]
  have hpre : (fun y : ℝ ↦ -y) ⁻¹' Iic (-x) = Ici x := by
    ext y
    simp
  rw [hpre, measureReal_congr (Ioi_ae_eq_Ici (μ := gaussianReal 0 1) (a := x)).symm,
    ← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]

/-- The distribution function of `N(0, v)` is continuous for `v > 0`. -/
lemma continuous_cdf_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) : Continuous (cdf (gaussianReal 0 v)) := by
  have : NullSingletonClass (gaussianReal 0 v) := nullSingletonClass_gaussianReal hv
  exact continuous_cdf_of_measure_singleton _ fun x ↦ measure_singleton x

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The endpoints of the credible interval.** Under the weak Bernstein and von Mises conclusion
with limit `N(0, v)`, `v > 0`, and `Φ(z) = 1 - α/2` with `α ∈ (0, 1)`,
`√n (q_n(1 - α/2) - a_n) → √v z` and `√n (q_n(α/2) - a_n) → -√v z` in probability. -/
theorem IsBernsteinVonMisesWeak.tendstoInMeasure_credibleInterval_endpoints
    {Q : ℕ → Ω → Measure ℝ} {a : ℕ → Ω → ℝ} {v : ℝ} (hv : 0 < v)
    (h : IsBernsteinVonMisesWeak P Q a (gaussianReal 0 v.toNNReal)) {α z : ℝ}
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ √(n : ℝ) * (quantile (Q n ω) (1 - α / 2) - a n ω))
        atTop (fun _ ↦ √v * z) ∧
      TendstoInMeasure P (fun (n : ℕ) ω ↦ √(n : ℝ) * (quantile (Q n ω) (α / 2) - a n ω))
        atTop (fun _ ↦ -(√v * z)) := by
  constructor
  · obtain ⟨h1, h2⟩ := gaussianReal_cdf_strict_crossing hv z
    rw [hz] at h1 h2
    exact h.tendstoInMeasure_quantile h1 h2
  · obtain ⟨h1, h2⟩ := gaussianReal_cdf_strict_crossing hv (-z)
    have hzn : cdf (gaussianReal 0 1) (-z) = α / 2 := by
      rw [cdf_gaussianReal_zero_one_neg, hz]; ring
    rw [hzn, mul_neg] at h1 h2
    exact h.tendstoInMeasure_quantile h1 h2

/-- **Frequentist coverage of the equal tailed credible interval for a real target.** Let the
posterior laws `Q_n` of a real target satisfy the weak Bernstein and von Mises conclusion with
centering `a_n` and limit `N(0, v)`, `v > 0`, and let `√n (a_n - ψ₀)` converge in distribution
to a variable with law `N(0, v)`. For `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the probability that
the credible interval `[q_n(α/2), q_n(1 - α/2)]` contains `ψ₀` tends to `1 - α`. -/
theorem IsBernsteinVonMisesWeak.tendsto_credibleInterval_coverage [IsProbabilityMeasure P]
    {Q : ℕ → Ω → Measure ℝ} {a : ℕ → Ω → ℝ} {v : ℝ} (hv : 0 < v)
    (h : IsBernsteinVonMisesWeak P Q a (gaussianReal 0 v.toNNReal)) {ψ₀ : ℝ}
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 v.toNNReal) P')
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) * (a n ω - ψ₀)) atTop Y
      (fun _ ↦ P) P')
    {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | ψ₀ ∈ credibleInterval (Q n ω) α}) atTop (𝓝 (1 - α)) := by
  obtain ⟨hhi, hlo⟩ := h.tendstoInMeasure_credibleInterval_endpoints hv hz
  set σ := √v with hσ
  have hs : 0 < σ := Real.sqrt_pos.2 hv
  have hv0 : v.toNNReal ≠ 0 := by simpa using hv
  -- the critical value is positive
  have hzpos : 0 < z := by
    have hzn : cdf (gaussianReal 0 1) (-z) = α / 2 := by
      rw [cdf_gaussianReal_zero_one_neg, hz]; ring
    have hlt : cdf (gaussianReal 0 1) (-z) < cdf (gaussianReal 0 1) z := by
      rw [hzn, hz]; linarith [hα.2]
    have := (cdf_gaussianReal_strictMono 0 (v := 1) one_ne_zero).lt_iff_lt.1 hlt
    linarith
  -- the limit probabilities `G c = N(0, v)([-c, c])`
  set F := cdf (gaussianReal 0 v.toNNReal) with hF
  set G : ℝ → ℝ := fun c ↦ F c - F (-c) with hG
  have hFc : Continuous F := continuous_cdf_gaussianReal hv0
  have hGc : Continuous G := hFc.sub (hFc.comp continuous_neg)
  have hvv : ((v.toNNReal : ℝ≥0) : ℝ) = σ ^ 2 := by
    rw [Real.coe_toNNReal _ hv.le, hσ, Real.sq_sqrt hv.le]
  have hGz : G (σ * z) = 1 - α := by
    have h1 : F (σ * z) = 1 - α / 2 := by
      rw [hF, show σ * z = 0 + σ * z by ring, cdf_gaussianReal_affine 0 hs hvv z, hz]
    have h2 : F (-(σ * z)) = α / 2 := by
      rw [hF, show -(σ * z) = 0 + σ * (-z) by ring, cdf_gaussianReal_affine 0 hs hvv (-z),
        cdf_gaussianReal_zero_one_neg, hz]
      ring
    simp only [hG, h1, h2]
    ring
  -- the sampling probabilities converge to `G c`
  set T : ℕ → Ω → ℝ := fun n ω ↦ √(n : ℝ) * (a n ω - ψ₀) with hTdef
  have hYm : AEMeasurable Y P' := hT.aemeasurable_limit
  have hlawY : P'.map Y = gaussianReal 0 v.toNNReal := hY.map_eq
  have hTlim : ∀ c, 0 ≤ c → Tendsto (fun n ↦ P.real {ω | |T n ω| ≤ c}) atTop (𝓝 (G c)) := by
    intro c hc
    have : NullSingletonClass (gaussianReal 0 v.toNNReal) := nullSingletonClass_gaussianReal hv0
    have hnull : P'.map Y (frontier (Icc (-c) c)) = 0 := by
      rw [hlawY]
      rw [frontier_Icc (by linarith)]
      exact (Set.toFinite _).measure_zero _
    have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hT.tendsto
      (E := Icc (-c) c) hnull
    simp only [ProbabilityMeasure.coe_mk] at hport
    have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
    have hval : (P'.map Y (Icc (-c) c)).toReal = G c := by
      rw [hlawY, ← measureReal_def]
      have hIcc : Icc (-c) c = Iic c \ Iio (-c) := by ext x; simp [and_comm]
      rw [hIcc, measureReal_sdiff (fun x hx ↦ by simp only [mem_Iio] at hx; simp; linarith)
        measurableSet_Iio, measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real, ← cdf_eq_real]
    rw [hval] at hreal
    refine hreal.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    rw [Measure.map_apply_of_aemeasurable (hT.forall_aemeasurable n) measurableSet_Icc,
      measureReal_def]
    congr 2
    ext ω
    simp only [mem_preimage, mem_Icc, Set.mem_ofPred_eq, abs_le, hTdef]
  -- the squeeze
  set Lq : ℕ → Ω → ℝ := fun n ω ↦ √(n : ℝ) * (quantile (Q n ω) (α / 2) - a n ω) with hLq
  set Uq : ℕ → Ω → ℝ := fun n ω ↦ √(n : ℝ) * (quantile (Q n ω) (1 - α / 2) - a n ω) with hUq
  set Cv : ℕ → Set Ω := fun n ↦ {ω | ψ₀ ∈ credibleInterval (Q n ω) α} with hCv
  set Gd : ℝ → ℕ → Set Ω := fun δ n ↦
    {ω | dist (Lq n ω) (-(σ * z)) < δ} ∩ {ω | dist (Uq n ω) (σ * z) < δ} with hGd
  have hmemC : ∀ n : ℕ, 1 ≤ n → ∀ ω, ω ∈ Cv n ↔ Lq n ω ≤ -T n ω ∧ -T n ω ≤ Uq n ω := by
    intro n hn ω
    have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    simp only [hCv, hLq, hUq, hTdef, Set.mem_ofPred_eq, credibleInterval, mem_Icc]
    rw [show -(√(n : ℝ) * (a n ω - ψ₀)) = √(n : ℝ) * (ψ₀ - a n ω) by ring,
      mul_le_mul_iff_right₀ hsq, mul_le_mul_iff_right₀ hsq]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hsub1 : ∀ δ, ∀ n : ℕ, 1 ≤ n →
      Cv n ⊆ {ω | |T n ω| ≤ σ * z + δ} ∪ (Gd δ n)ᶜ := by
    intro δ n hn ω hω
    by_cases hg : ω ∈ Gd δ n
    · left
      obtain ⟨h1, h2⟩ := (hmemC n hn ω).1 hω
      obtain ⟨g1, g2⟩ := hg
      simp only [Set.mem_ofPred_eq, Real.dist_eq, abs_lt] at g1 g2 ⊢
      rw [abs_le]
      constructor <;> linarith [g1.1, g1.2, g2.1, g2.2]
    · exact Or.inr hg
  have hsub2 : ∀ δ, ∀ n : ℕ, 1 ≤ n →
      {ω | |T n ω| ≤ σ * z - δ} ⊆ Cv n ∪ (Gd δ n)ᶜ := by
    intro δ n hn ω hω
    by_cases hg : ω ∈ Gd δ n
    · left
      refine (hmemC n hn ω).2 ?_
      obtain ⟨g1, g2⟩ := hg
      simp only [Set.mem_ofPred_eq, Real.dist_eq, abs_lt] at g1 g2 hω
      rw [abs_le] at hω
      constructor <;> linarith [g1.1, g1.2, g2.1, g2.2, hω.1, hω.2]
    · exact Or.inr hg
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨δ₀, hδ₀, hGδ⟩ := Metric.continuousAt_iff.1 hGc.continuousAt (ε / 4) hε4
  have hσz : 0 < σ * z := mul_pos hs hzpos
  set δ := min (δ₀ / 2) (σ * z / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ2 : δ ≤ σ * z / 2 := min_le_right _ _
  have hGp : |G (σ * z + δ) - (1 - α)| < ε / 4 := by
    rw [← hGz, ← Real.dist_eq]
    exact hGδ (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδ0]; exact hδ1)
  have hGm : |G (σ * z - δ) - (1 - α)| < ε / 4 := by
    rw [← hGz, ← Real.dist_eq]
    exact hGδ (by rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ0]; exact hδ1)
  have hgood := (hlo.withProbTendingToOne_dist_lt hδ0).inter (hhi.withProbTendingToOne_dist_lt hδ0)
  have hbad : Tendsto (fun n ↦ P.real (Gd δ n)ᶜ) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgood
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (hTlim (σ * z + δ) (by linarith)) (ε / 4) hε4
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (hTlim (σ * z - δ) (by linarith)) (ε / 4) hε4
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.1 hbad (ε / 4) hε4
  refine ⟨max 1 (max N₁ (max N₂ N₃)), fun n hn ↦ ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn3 : N₂ ≤ n := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  have hn4 : N₃ ≤ n := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hn
  have e1 := hN₁ n hn2
  have e2 := hN₂ n hn3
  have e3 := hN₃ n hn4
  rw [Real.dist_eq] at e1 e2 e3
  rw [sub_zero, abs_of_nonneg measureReal_nonneg] at e3
  have u1 : P.real (Cv n) ≤ P.real {ω | |T n ω| ≤ σ * z + δ} + P.real (Gd δ n)ᶜ :=
    (measureReal_mono (hsub1 δ n hn1)).trans (measureReal_union_le _ _)
  have u2 : P.real {ω | |T n ω| ≤ σ * z - δ} ≤ P.real (Cv n) + P.real (Gd δ n)ᶜ :=
    (measureReal_mono (hsub2 δ n hn1)).trans (measureReal_union_le _ _)
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at e1 e2 hGp hGm
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hGp.1, hGp.2, hGm.1, hGm.2]

/-! ### A smooth functional of a parameter -/

section Parameter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **`√n` normality implies consistency.** If `√n (θ̂_n - θ₀)` converges in distribution, then
`θ̂_n → θ₀` in probability: the scaled error is bounded in probability and `n^{-1/2} → 0`. -/
theorem tendstoInMeasure_of_tendstoInDistribution_sqrt_smul [IsProbabilityMeasure P]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {θh : ℕ → Ω → E} {θ₀ : E} {Y : Ω' → E}
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - θ₀)) atTop Y
      (fun _ ↦ P) P') :
    TendstoInMeasure P θh atTop (fun _ ↦ θ₀) := by
  have hb := hT.boundedInProbability
  have hx : TendstoInMeasure P (fun (n : ℕ) (_ : Ω) ↦ (√(n : ℝ))⁻¹) atTop 0 :=
    tendstoInMeasure_const_of_tendsto
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  have h0 := hx.smul_boundedInProbability hb
  have h1 : TendstoInMeasure P (fun (n : ℕ) ω ↦ θh n ω - θ₀) atTop (fun _ ↦ 0) := by
    refine TendstoInMeasure.congr' ?_ EventuallyEq.rfl h0
    filter_upwards [eventually_ge_atTop 1] with n hn
    refine ae_of_all _ fun ω ↦ ?_
    have hsq : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
    simp only [smul_smul, inv_mul_cancel₀ hsq, one_smul]
  rw [tendstoInMeasure_iff_dist] at h1 ⊢
  simpa [dist_eq_norm] using h1

/-- **Frequentist coverage of the credible interval of a smooth functional.** Let the posteriors
`Π_n` of a parameter in a separable Banach space satisfy the weak Bernstein and von Mises
conclusion with centering `θ̂_n` and a centered Gaussian limit `N`; let `√n (θ̂_n - θ₀)` converge
in distribution to a variable with law `N`; let `Ψ` be measurable and strictly differentiable at
`θ₀` with derivative `D`, with positive limiting variance `Var(D Z) > 0`, `Z ∼ N` (for a
nondegenerate `N` this is `D ≠ 0`). For `α ∈ (0, 1)` and `Φ(z) = 1 - α/2`, the equal tailed
credible interval of the posterior `Ψ_# Π_n` of the target covers `Ψ(θ₀)` with probability tending
to `1 - α`. -/
theorem IsBernsteinVonMisesWeak.tendsto_credibleInterval_coverage_map [CompleteSpace E]
    [SecondCountableTopology E] [IsProbabilityMeasure P] {Pn : ℕ → Ω → Measure E}
    {θh : ℕ → Ω → E} {N : Measure E} [IsGaussian N] (h : IsBernsteinVonMisesWeak P Pn θh N)
    (hN0 : ∫ x, x ∂N = 0) {θ₀ : E} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → E} (hY : HasLaw Y N P')
    (hT : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (θh n ω - θ₀)) atTop Y
      (fun _ ↦ P) P')
    {Ψ : E → ℝ} (hΨm : Measurable Ψ) {D : E →L[ℝ] ℝ} (hΨ : HasStrictFDerivAt Ψ D θ₀)
    (hσ : 0 < Var[D; N]) {α z : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hz : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    Tendsto (fun n ↦ P.real {ω | Ψ θ₀ ∈ credibleInterval ((Pn n ω).map Ψ) α}) atTop
      (𝓝 (1 - α)) := by
  have hcons := tendstoInMeasure_of_tendstoInDistribution_sqrt_smul hT
  have hL : N.map D = gaussianReal 0 (Var[D; N]).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal D]
    congr 1
    have := D.integral_comp_comm (IsGaussian.integrable_fun_id (μ := N))
    simpa [hN0] using this
  have hmap := h.map hcons hΨm hΨ
  rw [hL] at hmap
  have hgm : ∀ n : ℕ, AEMeasurable (fun ω ↦ √(n : ℝ) • (Ψ (θh n ω) - Ψ θ₀)) P := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.sqrt_zero, zero_smul]
      exact aemeasurable_const
    · have hsq : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
      have hθ : AEMeasurable (θh n) P := by
        have h1 := ((hT.forall_aemeasurable n).const_smul (√(n : ℝ))⁻¹).add_const θ₀
        refine h1.congr (ae_of_all _ fun ω ↦ ?_)
        simp [smul_smul, inv_mul_cancel₀ hsq]
      exact ((hΨm.comp_aemeasurable hθ).sub_const (Ψ θ₀)).const_smul (√(n : ℝ))
  have hTf := hT.delta_method hΨ.hasFDerivAt hgm
  have hDY : HasLaw (fun ω ↦ D (Y ω)) (gaussianReal 0 (Var[D; N]).toNNReal) P' := by
    rw [← hL]
    exact HasLaw.comp (Y := D) ⟨D.continuous.aemeasurable, rfl⟩ hY
  exact hmap.tendsto_credibleInterval_coverage hσ hDY (by simpa only [smul_eq_mul] using hTf)
    hα hz

end Parameter

/-! ### A vanishing derivative: `θ ↦ θ²` at `0` -/

/-- **The credible interval of `θ²` misses `0`.** For a probability law `μ` on `ℝ` without an
atom at `0` and `α ∈ (0, 1)`, the lower endpoint `q(α/2)` of the equal tailed credible interval
of the law of `θ²` is positive: the interval does not contain `0`. -/
theorem zero_notMem_credibleInterval_sq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h0 : μ {0} = 0) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    (0 : ℝ) ∉ credibleInterval (μ.map fun θ ↦ θ ^ 2) α := by
  intro hmem
  have hm : Measurable fun θ : ℝ ↦ θ ^ 2 := by fun_prop
  have : IsProbabilityMeasure (μ.map fun θ ↦ θ ^ 2) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hlev : α / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hle := (quantile_le_iff hlev 0).1 hmem.1
  have hpre : (fun θ : ℝ ↦ θ ^ 2) ⁻¹' Iic 0 = {0} := by
    ext θ
    simp only [mem_preimage, mem_Iic, mem_singleton_iff]
    constructor
    · intro h
      nlinarith [sq_nonneg θ]
    · rintro rfl
      simp
  rw [cdf_eq_real, map_measureReal_apply hm measurableSet_Iic, hpre, measureReal_def, h0,
    ENNReal.toReal_zero] at hle
  linarith [hα.1]

/-- **Coverage fails when the derivative vanishes.** Let the posteriors `Π_n` of a real
parameter satisfy the weak Bernstein and von Mises conclusion with a centering `θ̂_n → 0` in
probability, and have no atom at `0` (every normal posterior qualifies). For the target
`Ψ(θ) = θ²` at the truth `θ₀ = 0` the derivative is `0` and the limit law of the delta method is
the point mass at `0`, so the rescaled posterior quantiles still converge,
`√n (q_n(p) - θ̂_n²) → 0` in probability for every `p ∈ (0, 1)`; yet the credible interval
never contains `Ψ(0) = 0`, and its coverage is `0` at every sample size. -/
theorem sq_credibleInterval_coverage {Pn : ℕ → Ω → Measure ℝ} {θh : ℕ → Ω → ℝ} {N : Measure ℝ}
    (h : IsBernsteinVonMisesWeak P Pn θh N) (hcons : TendstoInMeasure P θh atTop (fun _ ↦ 0))
    (h0 : ∀ n ω, Pn n ω {0} = 0) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) :
    (∀ p ∈ Ioo (0 : ℝ) 1, TendstoInMeasure P (fun (n : ℕ) ω ↦
      √(n : ℝ) * (quantile ((Pn n ω).map fun θ ↦ θ ^ 2) p - θh n ω ^ 2)) atTop (fun _ ↦ 0)) ∧
      ∀ n, P.real {ω | (0 : ℝ) ^ 2 ∈ credibleInterval ((Pn n ω).map fun θ ↦ θ ^ 2) α} = 0 := by
  have := h.isProbabilityMeasure
  have := h.isProbabilityMeasure_limit
  refine ⟨fun p hp ↦ ?_, fun n ↦ ?_⟩
  · have hD : HasStrictFDerivAt (fun θ : ℝ ↦ θ ^ 2) (0 : ℝ →L[ℝ] ℝ) 0 := by
      have := (hasStrictDerivAt_pow 2 (0 : ℝ)).hasStrictFDerivAt
      convert this using 1
      ext
      simp
    have hmap := h.map hcons (by fun_prop) hD
    have hdirac : N.map (0 : ℝ →L[ℝ] ℝ) = Measure.dirac 0 := by
      have : ((0 : ℝ →L[ℝ] ℝ) : ℝ → ℝ) = fun _ ↦ 0 := rfl
      rw [this, Measure.map_const, measure_univ, one_smul]
    rw [hdirac] at hmap
    refine hmap.tendstoInMeasure_quantile (fun ε hε ↦ ?_) (fun ε hε ↦ ?_)
    · rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic,
        Set.indicator_of_notMem (by simp only [mem_Iic, not_le]; linarith)]
      simpa using hp.1
    · rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic,
        Set.indicator_of_mem (by simp only [mem_Iic]; linarith)]
      simpa using hp.2
  · have hempty : {ω | (0 : ℝ) ^ 2 ∈ credibleInterval ((Pn n ω).map fun θ ↦ θ ^ 2) α} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [zero_pow two_ne_zero]
      exact zero_notMem_credibleInterval_sq (h0 n ω) hα
    rw [hempty, measureReal_empty]

end PosteriorLimit

end CausalInference
