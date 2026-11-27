/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.AsymptoticLinear
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The delta method for asymptotically linear estimators

If `θhat` is asymptotically linear at `θ` with influence function `φ` and `g : ℝ → ℝ` is
differentiable at `θ` with derivative `g'`, then `g ∘ θhat` is asymptotically linear at `g θ` with
influence function `g' φ`.

Main results:

* `CausalInference.tendstoInMeasure_mul_of_bounded`: a sequence tending to zero in probability
  times a sequence bounded in probability tends to zero in probability.
* `CausalInference.measure_le_abs_inv_sqrt_mul_sum_le`: Chebyshev's bound for the normalized sum
  `n^{-1/2} ∑_{i < n} φ (O i)` of an i.i.d. sample with mean zero, uniform in `n`.
* `CausalInference.IsAsymptoticallyLinear.sqrt_mul_sub_boundedInProbability`: for an
  asymptotically linear estimator, `√n (θhat n - θ)` is bounded in probability.
* `CausalInference.IsAsymptoticallyLinear.comp_hasDerivAt`: **the delta method**.

No measurability of `g` is assumed: the argument works with the sets
`{ω | ε ≤ |X n ω|}` directly and never with laws of `g ∘ θhat`.

Source: A. W. van der Vaart (1998), *Asymptotic Statistics*, chapter 3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace CausalInference

variable {Ω 𝒪 : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace 𝒪]

/-- **Product of a negligible and a bounded sequence.** If `X i → 0` in probability and `Y i` is
bounded in probability (for every `η > 0` there is `M > 0` with eventually
`μ {M ≤ |Y i|} ≤ η`), then `X i * Y i → 0` in probability. -/
theorem tendstoInMeasure_mul_of_bounded {ι : Type*} {l : Filter ι} {μ : Measure Ω}
    {X Y : ι → Ω → ℝ} (hX : TendstoInMeasure μ X l 0)
    (hY : ∀ η : ℝ≥0∞, 0 < η → ∃ M : ℝ, 0 < M ∧ ∀ᶠ i in l, μ {ω | M ≤ |Y i ω|} ≤ η) :
    TendstoInMeasure μ (fun i ω ↦ X i ω * Y i ω) l 0 := by
  rw [tendstoInMeasure_iff_norm] at hX ⊢
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨M, hM, hYM⟩ := hY (η / 2) (ENNReal.half_pos hη.ne')
  have hXM := ENNReal.tendsto_nhds_zero.1 (hX (ε / M) (by positivity)) (η / 2)
    (ENNReal.half_pos hη.ne')
  filter_upwards [hYM, hXM] with i hi hi'
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans
    ((add_le_add hi' hi).trans (ENNReal.add_halves η).le))
  intro ω hω
  simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.zero_apply, sub_zero, Real.norm_eq_abs]
    at hω ⊢
  by_contra! hlt
  rw [abs_mul] at hω
  have h1 : |X i ω| * M < ε := (lt_div_iff₀ hM).1 hlt.1
  nlinarith [abs_nonneg (X i ω), abs_nonneg (Y i ω)]

/-- **Chebyshev's bound for the normalized sum.** Let `O` be an i.i.d. sample under a probability
measure `μ` and `φ` measurable with `φ (O 0)` square integrable and of mean zero. Then for every
`n` and `M > 0`, `μ {M ≤ |n^{-1/2} ∑_{i < n} φ (O i)|} ≤ E φ (O 0)² / M²`. -/
theorem measure_le_abs_inv_sqrt_mul_sum_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    {O : ℕ → Ω → 𝒪} {φ : 𝒪 → ℝ} (hO : IsIIDSample O μ) (hφ : Measurable φ)
    (h2 : MemLp (fun ω ↦ φ (O 0 ω)) 2 μ) (h0 : μ[fun ω ↦ φ (O 0 ω)] = 0) (n : ℕ) {M : ℝ}
    (hM : 0 < M) :
    μ {ω | M ≤ |(√n)⁻¹ * ∑ i ∈ range n, φ (O i ω)|} ≤
      ENNReal.ofReal (μ[fun ω ↦ φ (O 0 ω) ^ 2] / M ^ 2) := by
  have hident := (hO.comp hφ).ident
  have hL2 : ∀ i, MemLp (fun ω ↦ φ (O i ω)) 2 μ := fun i ↦ (hident i).symm.memLp_snd h2
  have hXL2 : MemLp (fun ω ↦ (√n)⁻¹ * ∑ i ∈ range n, φ (O i ω)) 2 μ :=
    (memLp_finsetSum _ fun i _ ↦ hL2 i).const_mul _
  have hmean : μ[fun ω ↦ (√n)⁻¹ * ∑ i ∈ range n, φ (O i ω)] = 0 := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ (hL2 i).integrable one_le_two,
      Finset.sum_eq_zero fun i _ ↦ (hident i).integral_eq.trans h0, mul_zero]
  have hsum : Var[fun ω ↦ ∑ i ∈ range n, φ (O i ω); μ] = n * Var[fun ω ↦ φ (O 0 ω); μ] := by
    have hfn : (fun ω ↦ ∑ i ∈ range n, φ (O i ω)) = ∑ i ∈ range n, fun ω ↦ φ (O i ω) := by
      ext ω
      simp only [Finset.sum_apply]
    rw [hfn, IndepFun.variance_sum (fun i _ ↦ hL2 i)
      ((hO.pairwise_indepFun hφ).set_pairwise _),
      Finset.sum_congr rfl fun i _ ↦ (hident i).variance_eq, sum_const, card_range, nsmul_eq_mul]
  have hvar0 : Var[fun ω ↦ φ (O 0 ω); μ] = μ[fun ω ↦ φ (O 0 ω) ^ 2] :=
    variance_of_integral_eq_zero h2.aemeasurable h0
  have hcoef : (√(n : ℝ))⁻¹ ^ 2 * n ≤ 1 := by
    rw [inv_pow, Real.sq_sqrt n.cast_nonneg]
    by_cases hn : (n : ℝ) = 0
    · simp [hn]
    · rw [inv_mul_cancel₀ hn]
  have hvar : Var[fun ω ↦ (√n)⁻¹ * ∑ i ∈ range n, φ (O i ω); μ] ≤
      μ[fun ω ↦ φ (O 0 ω) ^ 2] := by
    rw [variance_const_mul, hsum, hvar0, ← mul_assoc]
    have h0' : 0 ≤ μ[fun ω ↦ φ (O 0 ω) ^ 2] := integral_nonneg fun ω ↦ sq_nonneg _
    nlinarith
  have hcheb := meas_ge_le_variance_div_sq hXL2 hM
  rw [hmean] at hcheb
  simp only [sub_zero] at hcheb
  refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
  gcongr

namespace IsAsymptoticallyLinear

variable {θhat : ℕ → Ω → ℝ} {θ : ℝ} {φ : 𝒪 → ℝ} {O : ℕ → Ω → 𝒪} {μ : Measure Ω}

/-- **Asymptotically linear estimators are `√n`-bounded in probability.** If `θhat` is
asymptotically linear at `θ` for an i.i.d. sample under a probability measure, then
`√n (θhat n - θ)` is bounded in probability: for every `η > 0` there is `M > 0` such that
eventually `μ {M ≤ |√n (θhat n - θ)|} ≤ η`. -/
theorem sqrt_mul_sub_boundedInProbability [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (h : IsAsymptoticallyLinear θhat θ φ O μ) :
    ∀ η : ℝ≥0∞, 0 < η →
      ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, μ {ω | M ≤ |√n * (θhat n ω - θ)|} ≤ η := by
  intro η hη
  set σ2 : ℝ := μ[fun ω ↦ φ (O 0 ω) ^ 2] with hσ2def
  have hσ2 : 0 ≤ σ2 := integral_nonneg fun ω ↦ sq_nonneg _
  have hmin0 : min η 1 ≠ 0 := (lt_min hη one_pos).ne'
  have hmintop : min η 1 ≠ ⊤ := ((min_le_right η 1).trans_lt ENNReal.one_lt_top).ne
  set η' : ℝ := (min η 1).toReal with hη'def
  have hη'pos : 0 < η' := ENNReal.toReal_pos hmin0 hmintop
  have hη'le : ENNReal.ofReal η' ≤ η := by
    rw [hη'def, ENNReal.ofReal_toReal hmintop]
    exact min_le_left _ _
  set M₀ : ℝ := max 1 (2 * σ2 / η') with hM₀def
  have h1 : 1 ≤ M₀ := le_max_left _ _
  have hM₀ : 0 < M₀ := one_pos.trans_le h1
  have hcheb : σ2 / M₀ ^ 2 ≤ η' / 2 := by
    have h2 : 2 * σ2 / η' ≤ M₀ := le_max_right _ _
    rw [div_le_iff₀ hη'pos] at h2
    rw [div_le_iff₀ (pow_pos hM₀ 2)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_pos hη'pos hM₀).le]
  refine ⟨M₀ + 1, by linarith, ?_⟩
  have hR := (tendstoInMeasure_iff_norm.1 h.remainder) 1 one_pos
  have hR' := ENNReal.tendsto_nhds_zero.1 hR (ENNReal.ofReal (η' / 2))
    (ENNReal.ofReal_pos.2 (half_pos hη'pos))
  filter_upwards [hR'] with n hn
  refine (measure_mono ?_).trans ((measure_union_le _ _).trans
    ((add_le_add (measure_le_abs_inv_sqrt_mul_sum_le hO h.measurable h.memLp h.integral_eq_zero
      n hM₀) hn).trans ?_))
  · intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Pi.zero_apply, sub_zero, Real.norm_eq_abs]
      at hω ⊢
    by_contra! hlt
    have hsplit := abs_add_le ((√n)⁻¹ * ∑ i ∈ range n, φ (O i ω))
      (√n * (θhat n ω - θ) - (√n)⁻¹ * ∑ i ∈ range n, φ (O i ω))
    rw [add_sub_cancel] at hsplit
    linarith [hlt.1, hlt.2]
  · calc ENNReal.ofReal (σ2 / M₀ ^ 2) + ENNReal.ofReal (η' / 2)
        ≤ ENNReal.ofReal (η' / 2) + ENNReal.ofReal (η' / 2) := by gcongr
      _ = ENNReal.ofReal η' := by
        rw [← ENNReal.ofReal_add (half_pos hη'pos).le (half_pos hη'pos).le, add_halves]
      _ ≤ η := hη'le

/-- **The delta method.** Let `θhat` be asymptotically linear at `θ` with influence function `φ`
for an i.i.d. sample `O` under a probability measure `μ`, and let `g : ℝ → ℝ` be differentiable
at `θ` with derivative `g'`. Then `g ∘ θhat` is asymptotically linear at `g θ` with influence
function `g' φ`. The proof writes `g x - g θ = g' (x - θ) + ρ x (x - θ)` with `ρ` continuous at
`θ` and `ρ θ = 0`; then `ρ (θhat n) → 0` in probability by consistency, and `√n (θhat n - θ)` is
bounded in probability. -/
theorem comp_hasDerivAt [IsProbabilityMeasure μ] (hO : IsIIDSample O μ)
    (h : IsAsymptoticallyLinear θhat θ φ O μ) {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' θ) :
    IsAsymptoticallyLinear (fun n ω ↦ g (θhat n ω)) (g θ) (fun x ↦ g' * φ x) O μ where
  measurable := h.measurable.const_mul g'
  memLp := h.memLp.const_mul g'
  integral_eq_zero := by rw [integral_const_mul, h.integral_eq_zero, mul_zero]
  remainder := by
    classical
    set ρ : ℝ → ℝ := fun x ↦ if x = θ then 0 else (g x - g θ) / (x - θ) - g' with hρ
    have hρθ : ρ θ = 0 := by simp [hρ]
    have hkey : ∀ x, g x - g θ = g' * (x - θ) + ρ x * (x - θ) := by
      intro x
      by_cases hx : x = θ
      · simp [hx]
      · have hx' : x - θ ≠ 0 := sub_ne_zero.2 hx
        simp only [hρ, hx, ↓reduceIte]
        field_simp
        ring
    have hρc : ContinuousAt ρ θ := by
      rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hρθ]
      have hs : Tendsto (fun x ↦ slope g θ x - g') (𝓝[≠] θ) (𝓝 0) := by
        simpa using (hasDerivAt_iff_tendsto_slope.1 hg).sub_const g'
      refine hs.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hx' : x ≠ θ := hx
      simp only [slope_def_field, hρ, hx', ↓reduceIte]
    have hcons : TendstoInMeasure μ (fun n ω ↦ ρ (θhat n ω)) atTop 0 := by
      have := (h.isConsistent hO).comp hρc
      rw [hρθ] at this
      exact this
    have hsum := (h.remainder.const_mul g').add
      (tendstoInMeasure_mul_of_bounded hcons (h.sqrt_mul_sub_boundedInProbability hO))
    refine hsum.congr' (Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ ?_)
      (Eventually.of_forall fun ω ↦ by simp)
    simp only [Pi.add_apply, ← mul_sum]
    rw [hkey (θhat n ω)]
    ring

end IsAsymptoticallyLinear

end CausalInference
