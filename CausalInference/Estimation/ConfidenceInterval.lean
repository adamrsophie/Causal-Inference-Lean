/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.AsymptoticLinear
public import Mathlib.Probability.CDF

/-!
# Wald confidence intervals

The Wald interval for `θ` from an estimate `θhat`, a standard error estimate `σhat` and a
critical value `z` at sample size `n` is `[θhat - z σhat / √n, θhat + z σhat / √n]`.

Main results:

* `CausalInference.gaussianReal_real_Icc_neg_self`: if `Φ(z) = 1 - α / 2` for the standard
  normal distribution function `Φ` and `z ≥ 0`, then the standard normal law gives the interval
  `[-z, z]` probability `1 - α`.
* `CausalInference.tendsto_waldInterval_coverage`: if `√n (θhat n - θ)` converges in
  distribution to `N(0, σ²)` with `σ > 0`, and `σhat` is consistent for `σ`, then the coverage
  probability of the Wald interval converges to `1 - α`. The proof uses the Slutsky theorem of
  Mathlib (`MeasureTheory.TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`)
  and the portmanteau theorem
  (`MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'`).
* `CausalInference.IsAsymptoticallyLinear.tendsto_waldInterval_coverage`: the same conclusion
  for an asymptotically linear estimator with influence function `φ`, `σ² = E φ(O)²`.

Source: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapters 2, 3 and 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The Wald interval `[est - z se / √n, est + z se / √n]` built from an estimate `est`, a
standard error estimate `se`, a critical value `z` and the sample size `n`. -/
noncomputable def waldInterval (est se z : ℝ) (n : ℕ) : Set ℝ :=
  Icc (est - z * se / √n) (est + z * se / √n)

/-- For `n ≥ 1`, `θ` lies in the Wald interval exactly when `|√n (est - θ)| ≤ z se`. -/
lemma mem_waldInterval_iff {est se z θ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    θ ∈ waldInterval est se z n ↔ |√n * (est - θ)| - z * se ≤ 0 := by
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  rw [waldInterval, mem_Icc, abs_mul, abs_of_pos hs, sub_nonpos, ← le_div_iff₀' hs,
    abs_sub_le_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Two-sided standard normal probability.** If `z ≥ 0` and `Φ(z) = 1 - α / 2`, where `Φ` is
the distribution function of the standard normal law, then the standard normal law gives
`[-z, z]` probability `1 - α`. -/
theorem gaussianReal_real_Icc_neg_self {z α : ℝ} (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2) :
    (gaussianReal 0 1).real (Icc (-z) z) = 1 - α := by
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  have hIcc : Icc (-z) z = Iic z \ Iio (-z) := by
    ext x
    simp [and_comm]
  have hcdf : (gaussianReal 0 1).real (Iio z) = 1 - α / 2 := by
    rw [measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real, hzα]
  have hneg : (gaussianReal 0 1).real (Iio (-z)) = α / 2 := by
    have hsymm : (gaussianReal 0 1).map (fun x ↦ -x) = gaussianReal 0 1 := by
      simpa using gaussianReal_map_neg (μ := 0) (v := 1)
    rw [measureReal_congr Iio_ae_eq_Iic]
    conv_lhs => rw [← hsymm]
    rw [map_measureReal_apply measurable_neg measurableSet_Iic]
    have hpre : (fun x : ℝ ↦ -x) ⁻¹' Iic (-z) = (Iio z)ᶜ := by
      ext x
      simp
    rw [hpre, probReal_compl_eq_one_sub measurableSet_Iio, hcdf]
    ring
  rw [hIcc, measureReal_sdiff (fun x hx ↦ by simp only [mem_Iio] at hx; simp; linarith)
    measurableSet_Iio, ← cdf_eq_real, hzα, hneg]
  ring

/-- **Asymptotic coverage of the Wald interval.** Let `μ` be a probability measure, `θhat` and
`σhat` sequences of estimators with `σhat n` almost everywhere measurable, and suppose that
`√n (θhat n - θ)` converges in distribution to a random variable `Y` with law `N(0, σ²)`, where
`σ > 0`, and that `σhat` is consistent for `σ`. If `z ≥ 0` satisfies `Φ(z) = 1 - α / 2` for the
standard normal distribution function `Φ`, then the coverage probability
`μ {θ ∈ [θhat n - z σhat n / √n, θhat n + z σhat n / √n]}` converges to `1 - α`. -/
theorem tendsto_waldInterval_coverage {μ : Measure Ω} [IsProbabilityMeasure μ]
    {θhat σhat : ℕ → Ω → ℝ} {θ σ z α : ℝ} (hσ : 0 < σ) (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → ℝ} (hY : HasLaw Y (gaussianReal 0 (σ ^ 2).toNNReal) P')
    (hAN : TendstoInDistribution (fun (n : ℕ) ω ↦ √n * (θhat n ω - θ)) atTop Y (fun _ ↦ μ) P')
    (hσhat : IsConsistent σhat σ μ) (hσmeas : ∀ n, AEMeasurable (σhat n) μ) :
    Tendsto (fun n ↦ μ.real {ω | θ ∈ waldInterval (θhat n ω) (σhat n ω) z n}) atTop
      (𝓝 (1 - α)) := by
  set g : ℝ × ℝ → ℝ := fun p ↦ |p.1| - z * p.2 with hg
  have hgc : Continuous g := by fun_prop
  -- Slutsky: `|√n (θhat n - θ)| - z σhat n` converges in distribution to `|Y| - z σ`.
  have hW := hAN.continuous_comp_prodMk_of_tendstoInMeasure_const hgc hσhat hσmeas
  have hWlim : AEMeasurable (fun ω ↦ g (Y ω, σ)) P' := hW.aemeasurable_limit
  -- The law of the limit, expressed through the standard normal law.
  have hscale : gaussianReal 0 (σ ^ 2).toNNReal = (gaussianReal 0 1).map (σ * ·) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.coe_toNNReal _ (sq_nonneg σ)]
  have hlaw : ∀ s : Set ℝ, MeasurableSet s →
      P'.map (fun ω ↦ g (Y ω, σ)) s = gaussianReal 0 1 ((fun x ↦ |σ * x| - z * σ) ⁻¹' s) := by
    intro s hs
    have hm : MeasurableSet {x : ℝ | |x| - z * σ ∈ s} :=
      (by fun_prop : Measurable fun x : ℝ ↦ |x| - z * σ) hs
    rw [Measure.map_apply_of_aemeasurable hWlim hs]
    have := hY.measure_eq (p := fun x ↦ |x| - z * σ ∈ s) hm
    simp only [hg] at this ⊢
    rw [show {ω | |Y ω| - z * σ ∈ s} = (fun ω ↦ |Y ω| - z * σ) ⁻¹' s from rfl] at this
    rw [this, hscale]
    exact Measure.map_apply (measurable_const_mul σ) hm
  -- The boundary `{0}` of `Iic 0` carries no mass under the limit law.
  have hnull : P'.map (fun ω ↦ g (Y ω, σ)) (frontier (Iic 0)) = 0 := by
    have := nullSingletonClass_gaussianReal (μ := 0) (one_ne_zero (α := ℝ≥0))
    refine measure_mono_null (frontier_Iic_subset 0) ?_
    rw [hlaw _ (measurableSet_singleton 0)]
    refine measure_mono_null (t := {z, -z}) ?_ ((Set.toFinite _).measure_zero _)
    intro x hx
    simp only [mem_preimage, mem_singleton_iff, sub_eq_zero, abs_mul, abs_of_pos hσ] at hx
    have hx' : |x| = z := mul_left_cancel₀ hσ.ne' (hx.trans (mul_comm z σ))
    rcases abs_eq hz |>.1 hx' with h | h <;> simp [h]
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hW.tendsto
    (E := Iic 0) hnull
  have hlimval : (P'.map (fun ω ↦ g (Y ω, σ)) (Iic 0)).toReal = 1 - α := by
    rw [hlaw _ measurableSet_Iic]
    have hpre : (fun x ↦ |σ * x| - z * σ) ⁻¹' Iic 0 = Icc (-z) z := by
      ext x
      simp only [mem_preimage, mem_Iic, sub_nonpos, abs_mul, abs_of_pos hσ, mem_Icc]
      rw [mul_comm z σ, mul_le_mul_iff_right₀ hσ, abs_le]
    rw [hpre, ← measureReal_def, gaussianReal_real_Icc_neg_self hz hzα]
  have : IsProbabilityMeasure (P'.map (fun ω ↦ g (Y ω, σ))) :=
    (Measure.isProbabilityMeasure_map_iff hWlim).2 inferInstance
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hport
  rw [hlimval] at hreal
  refine hreal.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp_apply]
  rw [Measure.map_apply_of_aemeasurable (hW.forall_aemeasurable n) measurableSet_Iic,
    measureReal_def]
  congr 2
  ext ω
  simp [hg, mem_waldInterval_iff hn]

/-- **Wald interval for an asymptotically linear estimator.** Let `θhat` be asymptotically linear
at `θ` with influence function `φ` for an i.i.d. sample `O` under a probability measure `μ`, with
each `θhat n` almost everywhere measurable, and let `σ > 0` with `σ² = E φ (O 0)²`. If `σhat` is
a consistent, almost everywhere measurable estimator of `σ`, and `z ≥ 0` satisfies
`Φ(z) = 1 - α / 2`, then the coverage probability of the Wald interval converges to `1 - α`. -/
theorem IsAsymptoticallyLinear.tendsto_waldInterval_coverage {𝒪 : Type*} [MeasurableSpace 𝒪]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {O : ℕ → Ω → 𝒪} {φ : 𝒪 → ℝ}
    {θhat σhat : ℕ → Ω → ℝ} {θ σ z α : ℝ} (hO : IsIIDSample O μ)
    (h : IsAsymptoticallyLinear θhat θ φ O μ) (hmeas : ∀ n, AEMeasurable (θhat n) μ)
    (hσ : 0 < σ) (hσ2 : μ[fun ω ↦ φ (O 0 ω) ^ 2] = σ ^ 2) (hz : 0 ≤ z)
    (hzα : cdf (gaussianReal 0 1) z = 1 - α / 2)
    (hσhat : IsConsistent σhat σ μ) (hσmeas : ∀ n, AEMeasurable (σhat n) μ) :
    Tendsto (fun n ↦ μ.real {ω | θ ∈ waldInterval (θhat n ω) (σhat n ω) z n}) atTop
      (𝓝 (1 - α)) := by
  have hY : HasLaw id (gaussianReal 0 (μ[fun ω ↦ φ (O 0 ω) ^ 2]).toNNReal)
      (gaussianReal 0 (σ ^ 2).toNNReal) := by
    rw [hσ2]
    exact HasLaw.id
  exact CausalInference.tendsto_waldInterval_coverage hσ hz hzα HasLaw.id
    (h.tendstoInDistribution hO hmeas hY) hσhat hσmeas

end CausalInference
