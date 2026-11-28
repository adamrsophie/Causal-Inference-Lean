/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.ConjugacyKernel
public import CausalInference.MetaAnalysis.RestrictedLikelihoodMaximizer

/-!
# Normal conjugacy for an i.i.d. sample with known variance

Let `y₁, …, yₙ` be i.i.d. `N(θ, σ²)` given `θ`, with `σ² > 0` known, and let the prior be
`θ ~ N(θ₀, σ₀²)`, `σ₀² > 0`. This is the common effect model of `MetaAnalysis.ConjugacyKernel`
with equal variances `sᵢ = σ²`, so the posterior is a corollary of
`posterior_commonEffectKernel`.

* **Posterior** (`posterior_iidNormal`): for almost every sample under the marginal law, the
  posterior is `N(B θ₀ + (1 - B) ȳ, (1/σ₀² + n/σ²)⁻¹)`, where `ȳ` is the sample mean and
  `B = (1/σ₀²) / (1/σ₀² + n/σ²)` (`priorWeight`) is the share of the prior precision in the
  posterior precision.
* **Shrinkage** (`posteriorMean_equalVar`, `priorWeight_mem_Ioo`): the posterior mean is the
  precision weighted average of the prior mean and the sample mean, a shrinkage of `ȳ` toward
  `θ₀` by the factor `B ∈ (0, 1)`; posterior mean minus sample mean is exactly `B (θ₀ - ȳ)`.
* **Large samples** (`tendsto_posteriorVariance_equalVar`, `tendsto_priorWeight`,
  `tendsto_posteriorMean_sub_sampleMean`): as `n → ∞` the posterior variance tends to `0`,
  `B → 0`, and posterior mean minus sample mean tends to `0` along any data sequence whose sample
  means are bounded (for instance a sequence whose sample means converge, as they do almost
  surely by the strong law). Some condition on the sample means is needed, because the
  difference is `B (θ₀ - ȳ)` and `B` decays like `σ² / (n σ₀²)`.

## Main definitions

* `priorWeight`.

## Main results

* `posteriorPrecision_equalVar`, `posteriorMean_equalVar`, `posterior_iidNormal`,
  `priorWeight_mem_Ioo`, `tendsto_posteriorVariance_equalVar`, `tendsto_priorWeight`,
  `tendsto_posteriorMean_sub_sampleMean`.

## References

* A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari and D. B. Rubin, *Bayesian Data
  Analysis*, third edition (2013).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal

/-- The **prior weight** `B = (1/σ₀²) / (1/σ₀² + n/σ²)`: the share of the prior precision in the
posterior precision for a sample of size `n` with variance `σ²`. -/
noncomputable def priorWeight (σ02 σ2 : ℝ) (n : ℕ) : ℝ := (1 / σ02) / (1 / σ02 + n / σ2)

theorem priorWeight_mem_Ioo {σ02 σ2 : ℝ} (hσ0 : 0 < σ02) (hσ : 0 < σ2) {n : ℕ} (hn : 0 < n) :
    priorWeight σ02 σ2 n ∈ Set.Ioo 0 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : 0 < 1 / σ02 := one_div_pos.2 hσ0
  have h2 : 0 < (n : ℝ) / σ2 := div_pos hn' hσ
  exact ⟨div_pos h1 (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

variable {ι : Type*} [Fintype ι]

/-- With equal variances the posterior precision is `1/σ₀² + n/σ²`. -/
theorem posteriorPrecision_equalVar (σ02 σ2 : ℝ) :
    posteriorPrecision σ02 (fun _ : ι => σ2) = 1 / σ02 + Fintype.card ι / σ2 := by
  simp [posteriorPrecision, ivWeight, Finset.sum_const, Finset.card_univ, div_eq_mul_inv]

/-- **The posterior mean shrinks the sample mean toward the prior mean**: with equal variances
`σ² > 0` and `n ≥ 1` observations, the posterior mean is `B θ₀ + (1 - B) ȳ` with
`B = priorWeight σ₀² σ² n`. -/
theorem posteriorMean_equalVar [Nonempty ι] {σ02 σ2 : ℝ} (hσ0 : 0 < σ02) (hσ : 0 < σ2)
    (θ0 : ℝ) (y : ι → ℝ) :
    posteriorMean θ0 σ02 (fun _ : ι => σ2) y =
      priorWeight σ02 σ2 (Fintype.card ι) * θ0 +
        (1 - priorWeight σ02 σ2 (Fintype.card ι)) * regMean y := by
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hA : 0 < 1 / σ02 + Fintype.card ι / σ2 := by positivity
  rw [posteriorMean, posteriorPrecision_equalVar, ivwEstimate_equalVar hσ.ne']
  have hW : ∑ i : ι, ivWeight (fun _ : ι => σ2) i = Fintype.card ι / σ2 := by
    simp [ivWeight, Finset.sum_const, Finset.card_univ, div_eq_mul_inv]
  rw [hW, priorWeight]
  field_simp
  ring

/-- **Posterior of the mean of an i.i.d. normal sample**: for the likelihood kernel
`θ ↦ N(θ, σ²)^{⊗n}` (`commonEffectKernel` with equal variances), `σ² > 0`, `n ≥ 1`, and the
prior `N(θ₀, σ₀²)`, `σ₀² > 0`, for almost every sample `y` under the marginal law the posterior
is `N(B θ₀ + (1 - B) ȳ, (1/σ₀² + n/σ²)⁻¹)`, `B = priorWeight σ₀² σ² n`. A corollary of
`posterior_commonEffectKernel`. -/
theorem posterior_iidNormal [Nonempty ι] {θ0 σ02 σ2 : ℝ} (hσ0 : 0 < σ02) (hσ : 0 < σ2) :
    ∀ᵐ y ∂(commonEffectKernel (fun _ : ι => σ2) ∘ₘ gaussianReal θ0 σ02.toNNReal),
      ((commonEffectKernel fun _ : ι => σ2)†(gaussianReal θ0 σ02.toNNReal)) y =
        gaussianReal (priorWeight σ02 σ2 (Fintype.card ι) * θ0 +
            (1 - priorWeight σ02 σ2 (Fintype.card ι)) * regMean y)
          ((1 / σ02 + Fintype.card ι / σ2)⁻¹).toNNReal := by
  filter_upwards [posterior_commonEffectKernel (ι := ι) (θ0 := θ0) hσ0 (s := fun _ => σ2)
    (fun _ => hσ)] with y hy
  rw [hy, posteriorMean_equalVar hσ0 hσ, posteriorVariance, posteriorPrecision_equalVar,
    one_div]

/-- The posterior mean minus the sample mean is `B (θ₀ - ȳ)`. -/
theorem posteriorMean_sub_regMean [Nonempty ι] {σ02 σ2 : ℝ} (hσ0 : 0 < σ02) (hσ : 0 < σ2)
    (θ0 : ℝ) (y : ι → ℝ) :
    posteriorMean θ0 σ02 (fun _ : ι => σ2) y - regMean y =
      priorWeight σ02 σ2 (Fintype.card ι) * (θ0 - regMean y) := by
  rw [posteriorMean_equalVar hσ0 hσ]
  ring

/-- The posterior precision `1/σ₀² + n/σ²` tends to `∞` with the sample size. -/
theorem tendsto_posteriorPrecision_card {σ02 σ2 : ℝ} (hσ : 0 < σ2) :
    Tendsto (fun n : ℕ => 1 / σ02 + n / σ2) atTop atTop :=
  tendsto_atTop_add_const_left _ _
    (Tendsto.atTop_div_const hσ tendsto_natCast_atTop_atTop)

/-- **The posterior concentrates**: the posterior variance of the mean of an i.i.d. sample of size
`n` tends to `0` as `n → ∞`. -/
theorem tendsto_posteriorVariance_equalVar {σ02 σ2 : ℝ} (hσ : 0 < σ2) :
    Tendsto (fun n : ℕ => posteriorVariance σ02 (fun _ : Fin n => σ2)) atTop (𝓝 0) := by
  simp only [posteriorVariance, posteriorPrecision_equalVar, Fintype.card_fin]
  exact tendsto_const_nhds.div_atTop (tendsto_posteriorPrecision_card hσ)

/-- The prior weight tends to `0` as the sample size grows. -/
theorem tendsto_priorWeight (σ02 : ℝ) {σ2 : ℝ} (hσ : 0 < σ2) :
    Tendsto (fun n : ℕ => priorWeight σ02 σ2 n) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_posteriorPrecision_card hσ)

/-- **The posterior mean approaches the sample mean**: along a data sequence `y` whose sample
means `ȳₙ` are bounded, the posterior mean from the first `n` observations minus `ȳₙ` tends to
`0`. Proof: the difference is `Bₙ (θ₀ - ȳₙ)` with `Bₙ → 0`. -/
theorem tendsto_posteriorMean_sub_sampleMean {θ0 σ02 σ2 : ℝ} (hσ0 : 0 < σ02) (hσ : 0 < σ2)
    (y : ℕ → ℝ) {C : ℝ} (hC : ∀ n, |regMean (fun i : Fin n => y i)| ≤ C) :
    Tendsto (fun n : ℕ => posteriorMean θ0 σ02 (fun _ : Fin (n + 1) => σ2)
        (fun i => y i) - regMean (fun i : Fin (n + 1) => y i)) atTop (𝓝 0) := by
  have hB := (tendsto_priorWeight σ02 hσ).comp (tendsto_add_atTop_nat 1)
  have hbound : ∀ n : ℕ, |priorWeight σ02 σ2 (n + 1) * (θ0 - regMean (fun i : Fin (n + 1) => y i))|
      ≤ priorWeight σ02 σ2 (n + 1) * (|θ0| + C) := fun n => by
    have hpos := (priorWeight_mem_Ioo hσ0 hσ (Nat.succ_pos n)).1
    rw [abs_mul, abs_of_pos hpos]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    exact (abs_sub _ _).trans (by linarith [hC (n + 1)])
  have hlim : Tendsto (fun n : ℕ => priorWeight σ02 σ2 (n + 1) * (|θ0| + C)) atTop (𝓝 0) := by
    simpa using hB.mul_const (|θ0| + C)
  refine squeeze_zero_norm (fun n => ?_) hlim
  rw [Real.norm_eq_abs, posteriorMean_sub_regMean hσ0 hσ, Fintype.card_fin]
  exact hbound n

end MetaAnalysis

end CausalInference
