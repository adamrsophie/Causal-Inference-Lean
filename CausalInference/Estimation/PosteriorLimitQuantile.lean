/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitDelta
public import CausalInference.BiasAnalysis.Distributions

/-!
# Posterior quantiles and the equal tailed credible interval

The `p` quantile of a law `μ` on `ℝ` is the library's generalized inverse
`BiasAnalysis.Distributions.quantile μ p = inf {x | p ≤ F_μ(x)}`, with the Galois property
`quantile μ p ≤ x ↔ p ≤ F_μ(x)` for `p ∈ (0, 1)`. The **equal tailed credible interval** at level
`1 - α` of a posterior law `μ` of a real target is `[q(α/2), q(1 - α/2)]` (`credibleInterval`).

**Quantile limits.** Let the random laws `Q_n` on `ℝ` (posterior laws of a real target) satisfy
the weak Bernstein and von Mises conclusion with centering `a_n` and limit `L`. If the distribution
function of `L` crosses `p` strictly at `c`, that is `F_L(c - ε) < p < F_L(c + ε)` for every
`ε > 0`, then `√n (q_n(p) - a_n) → c` in probability
(`IsBernsteinVonMisesWeak.tendstoInMeasure_quantile`): `q_n(p) = a_n + c n^{-1/2} + o_p(n^{-1/2})`.
The level `p` is then automatically in `(0, 1)`. Two continuous ramps squeezed between indicators
of half lines turn the weak convergence of the rescaled posterior into bounds on its distribution
function at `a_n + (c ± ε/2) n^{-1/2}`, and the Galois property pins the quantile between them.

For the normal limit `N(0, v)`, `v > 0`, the crossing holds at `c = √v z` for the level
`p = Φ(z)` (`gaussianReal_cdf_strict_crossing`), with `Φ` the standard normal distribution
function.

## Main definitions

* `PosteriorLimit.credibleInterval`, `PosteriorLimit.ramp`.

## Main results

* `IsBernsteinVonMisesWeak.tendstoInMeasure_quantile`, `gaussianReal_cdf_strict_crossing`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

open BiasAnalysis.Distributions

/-- The **equal tailed credible interval** `[q(α/2), q(1 - α/2)]` of a law `μ` on `ℝ`, with the
library's quantile function. For `α ∈ (0, 1)` both levels lie in `(0, 1)`. -/
noncomputable def credibleInterval (μ : Measure ℝ) (α : ℝ) : Set ℝ :=
  Icc (quantile μ (α / 2)) (quantile μ (1 - α / 2))

/-! ### Ramps between indicators -/

/-- The ramp `y ↦ clamp((t - y) / δ, 0, 1)`: one on `y ≤ t - δ`, zero on `y ≥ t`. -/
noncomputable def ramp (t δ y : ℝ) : ℝ := max 0 (min 1 ((t - y) / δ))

lemma continuous_ramp (t δ : ℝ) : Continuous (ramp t δ) := by
  unfold ramp
  fun_prop

lemma abs_ramp_le (t δ y : ℝ) : |ramp t δ y| ≤ 1 := by
  unfold ramp
  rw [abs_le]
  constructor
  · linarith [le_max_left 0 (min 1 ((t - y) / δ))]
  · exact max_le zero_le_one (min_le_left _ _)

lemma ramp_le_indicator {t δ : ℝ} (hδ : 0 < δ) (y : ℝ) : ramp t δ y ≤ (Iic t).indicator 1 y := by
  unfold ramp
  by_cases h : y ≤ t
  · simp only [indicator_of_mem (show y ∈ Iic t from h), Pi.one_apply]
    exact max_le zero_le_one (min_le_left _ _)
  · have hneg : (t - y) / δ < 0 := div_neg_of_neg_of_pos (by linarith [not_le.1 h]) hδ
    simp only [indicator_of_notMem (show y ∉ Iic t from h)]
    exact max_le le_rfl ((min_le_right _ _).trans hneg.le)

lemma indicator_le_ramp {t δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    (Iic (t - δ)).indicator 1 y ≤ ramp t δ y := by
  unfold ramp
  by_cases h : y ≤ t - δ
  · simp only [indicator_of_mem (show y ∈ Iic (t - δ) from h), Pi.one_apply]
    have h1 : 1 ≤ (t - y) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [min_eq_left h1]
    exact le_max_right _ _
  · simp only [indicator_of_notMem (show y ∉ Iic (t - δ) from h)]
    exact le_max_left _ _

/-- The integral of the indicator of `{s (y - a) ≤ t}` is the mass of `(-∞, a + t / s]`. -/
lemma integral_indicator_Iic_scaled (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : 0 < s)
    (a t : ℝ) : ∫ y, (Iic t).indicator 1 (s * (y - a)) ∂μ = cdf μ (a + t / s) := by
  have hpre : (fun y ↦ s * (y - a)) ⁻¹' Iic t = Iic (a + t / s) := by
    ext y
    simp only [mem_preimage, mem_Iic]
    rw [← sub_le_iff_le_add', le_div_iff₀ hs, mul_comm]
  have hfun : (fun y ↦ (Iic t).indicator (1 : ℝ → ℝ) (s * (y - a))) =
      (Iic (a + t / s)).indicator 1 := by
    funext y
    rw [← hpre]
    rfl
  rw [hfun, integral_indicator_one measurableSet_Iic, cdf_eq_real]

/-- The bounded continuous test functions `y ↦ ramp t δ (s (y - a))`. -/
lemma integrable_ramp_comp (μ : Measure ℝ) [IsProbabilityMeasure μ] (t δ s a : ℝ) :
    Integrable (fun y ↦ ramp t δ (s * (y - a))) μ :=
  Integrable.of_bound ((continuous_ramp t δ).comp (by fun_prop)).aestronglyMeasurable 1
    (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact abs_ramp_le _ _ _)

lemma integrable_indicator_Iic_comp (μ : Measure ℝ) [IsProbabilityMeasure μ] (t s a : ℝ) :
    Integrable (fun y ↦ (Iic t).indicator (1 : ℝ → ℝ) (s * (y - a))) μ :=
  Integrable.of_bound (((measurable_one.indicator measurableSet_Iic).comp
    (by fun_prop : Measurable fun y : ℝ ↦ s * (y - a))).aestronglyMeasurable) 1
    (ae_of_all _ fun y ↦ by by_cases h : s * (y - a) ∈ Iic t <;> simp [h])

/-- **Deterministic quantile bound.** For a probability law `μ` on `ℝ`, `s > 0` and `ε > 0`: if
`∫ ramp_{c + ε/2, ε/4}(s (y - a)) dμ > p` and `∫ ramp_{c - ε/4, ε/4}(s (y - a)) dμ < p`, then
`|s (q(p) - a) - c| ≤ ε / 2`. -/
lemma abs_quantile_scaled_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {a s c p ε : ℝ}
    (hs : 0 < s) (hε : 0 < ε) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hhi : p < ∫ y, ramp (c + ε / 2) (ε / 4) (s * (y - a)) ∂μ)
    (hlo : ∫ y, ramp (c - ε / 4) (ε / 4) (s * (y - a)) ∂μ < p) :
    |s * (quantile μ p - a) - c| ≤ ε / 2 := by
  have hε4 : 0 < ε / 4 := by positivity
  have hup : p ≤ cdf μ (a + (c + ε / 2) / s) := by
    rw [← integral_indicator_Iic_scaled μ hs]
    exact (hhi.trans_le (integral_mono (integrable_ramp_comp μ _ _ s a)
      (integrable_indicator_Iic_comp μ _ s a) fun y ↦ ramp_le_indicator hε4 _)).le
  have hdown : cdf μ (a + (c - ε / 2) / s) < p := by
    rw [← integral_indicator_Iic_scaled μ hs, show c - ε / 2 = c - ε / 4 - ε / 4 by ring]
    exact (integral_mono (integrable_indicator_Iic_comp μ _ s a)
      (integrable_ramp_comp μ _ _ s a) fun y ↦ indicator_le_ramp hε4 _).trans_lt hlo
  have hQle : quantile μ p ≤ a + (c + ε / 2) / s := (quantile_le_iff hp _).2 hup
  have hQge : a + (c - ε / 2) / s < quantile μ p := by
    by_contra hle
    exact absurd ((quantile_le_iff hp _).1 (not_lt.1 hle)) (not_le.2 hdown)
  have h1 : s * (quantile μ p - a) ≤ c + ε / 2 := by
    have : quantile μ p - a ≤ (c + ε / 2) / s := by linarith
    rw [le_div_iff₀ hs] at this
    linarith
  have h2 : c - ε / 2 ≤ s * (quantile μ p - a) := by
    have : (c - ε / 2) / s ≤ quantile μ p - a := by linarith
    rw [div_le_iff₀ hs] at this
    linarith
  rw [abs_le]
  constructor <;> linarith

/-! ### Quantile limits -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A strict crossing `F_L(c - ε) < p < F_L(c + ε)` of a probability law forces `p ∈ (0, 1)`. -/
lemma mem_Ioo_of_strict_crossing {L : Measure ℝ} [IsProbabilityMeasure L] {p c : ℝ}
    (hlo : ∀ ε, 0 < ε → cdf L (c - ε) < p) (hhi : ∀ ε, 0 < ε → p < cdf L (c + ε)) :
    p ∈ Ioo (0 : ℝ) 1 :=
  ⟨(cdf_nonneg L _).trans_lt (hlo 1 one_pos), (hhi 1 one_pos).trans_le (cdf_le_one L _)⟩

/-- **Posterior quantiles from the weak Bernstein and von Mises conclusion.** Let the random
laws `Q_n` on `ℝ` satisfy `IsBernsteinVonMisesWeak P Q a L`, and let the distribution function of
`L` cross `p` strictly at `c`. Then `√n (q_n(p) - a_n) → c` in probability, where `q_n(p)` is the
`p` quantile of `Q_n`. No measurability of `ω ↦ q_n(p)` is needed: convergence in probability is
stated with the outer measure. -/
theorem IsBernsteinVonMisesWeak.tendstoInMeasure_quantile {Q : ℕ → Ω → Measure ℝ}
    {a : ℕ → Ω → ℝ} {L : Measure ℝ} (h : IsBernsteinVonMisesWeak P Q a L) {p c : ℝ}
    (hlo : ∀ ε, 0 < ε → cdf L (c - ε) < p) (hhi : ∀ ε, 0 < ε → p < cdf L (c + ε)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ √(n : ℝ) * (quantile (Q n ω) p - a n ω)) atTop
      (fun _ ↦ c) := by
  have := h.isProbabilityMeasure
  have := h.isProbabilityMeasure_limit
  have hp := mem_Ioo_of_strict_crossing hlo hhi
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  have hrI : ∀ t δ, Integrable (ramp t δ) L := fun t δ ↦ by
    simpa using integrable_ramp_comp L t δ 1 0
  have hIicI : ∀ t, Integrable ((Iic t).indicator (1 : ℝ → ℝ)) L := fun t ↦
    (integrable_const 1).indicator measurableSet_Iic
  set ℓhi := ∫ y, ramp (c + ε / 2) (ε / 4) y ∂L with hℓhi
  set ℓlo := ∫ y, ramp (c - ε / 4) (ε / 4) y ∂L with hℓlo
  have hphi : p < ℓhi := by
    have hm := integral_mono (hIicI (c + ε / 2 - ε / 4)) (hrI _ _)
      (fun y ↦ indicator_le_ramp hε4 y)
    rw [integral_indicator_one measurableSet_Iic, ← cdf_eq_real,
      show c + ε / 2 - ε / 4 = c + ε / 4 by ring] at hm
    exact (hhi _ hε4).trans_le hm
  have hplo : ℓlo < p := by
    have hm := integral_mono (hrI _ _) (hIicI (c - ε / 4)) (fun y ↦ ramp_le_indicator hε4 y)
    rw [integral_indicator_one measurableSet_Iic, ← cdf_eq_real] at hm
    exact hm.trans_lt (hlo _ hε4)
  have hbd : ∀ t δ, ∃ C, ∀ y, |ramp t δ y| ≤ C := fun t δ ↦ ⟨1, abs_ramp_le t δ⟩
  have Ahi := h.tendsto _ (continuous_ramp (c + ε / 2) (ε / 4)) (hbd _ _)
  have Alo := h.tendsto _ (continuous_ramp (c - ε / 4) (ε / 4)) (hbd _ _)
  have H := (Ahi.withProbTendingToOne_dist_lt (sub_pos.2 hphi)).inter
    (Alo.withProbTendingToOne_dist_lt (sub_pos.2 hplo))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds H
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  refine measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω
  rintro ⟨h1, h2⟩
  simp only [Set.mem_ofPred_eq] at h1 h2
  rw [Real.dist_eq, abs_lt] at h1 h2
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  simp only [smul_eq_mul] at h1 h2
  have key := abs_quantile_scaled_sub_le (Q n ω) (a := a n ω) (c := c) hs hε hp
    (by linarith [h1.1]) (by linarith [h2.2])
  rw [Real.dist_eq] at hω
  linarith

/-! ### The normal limit -/

/-- The distribution function of `N(m, v)`, `v > 0`, is strictly increasing: Lebesgue measure is
absolutely continuous with respect to it, so every nondegenerate interval has positive mass. -/
lemma cdf_gaussianReal_strictMono (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal m v)) := by
  intro x y hxy
  have hac := gaussianReal_absolutelyContinuous' m hv
  have hpos : gaussianReal m v (Ioc x y) ≠ 0 := fun h0 ↦ by
    have := hac h0
    rw [Real.volume_Ioc] at this
    exact absurd this (by simp [hxy])
  rw [cdf_eq_real, cdf_eq_real]
  have hsplit := measureReal_union (μ := gaussianReal m v) (s₁ := Iic x) (s₂ := Ioc x y)
    (Set.disjoint_left.2 fun t ht ht' ↦ by
      rw [mem_Iic] at ht
      rw [mem_Ioc] at ht'
      linarith [ht'.1]) measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hxy.le] at hsplit
  have : 0 < (gaussianReal m v).real (Ioc x y) :=
    ENNReal.toReal_pos hpos (measure_ne_top _ _)
  linarith

/-- **Strict crossing for the normal limit.** For `v > 0` and `z ∈ ℝ`, the distribution function
of `N(0, v)` crosses the level `Φ(z)` strictly at `√v z`, where `Φ` is the standard normal
distribution function. -/
theorem gaussianReal_cdf_strict_crossing {v : ℝ} (hv : 0 < v) (z : ℝ) :
    (∀ ε, 0 < ε → cdf (gaussianReal 0 v.toNNReal) (√v * z - ε) < cdf (gaussianReal 0 1) z) ∧
      (∀ ε, 0 < ε → cdf (gaussianReal 0 1) z < cdf (gaussianReal 0 v.toNNReal) (√v * z + ε)) := by
  have hs : 0 < √v := Real.sqrt_pos.2 hv
  have hvv : ((v.toNNReal : ℝ≥0) : ℝ) = √v ^ 2 := by
    rw [Real.coe_toNNReal _ hv.le, Real.sq_sqrt hv.le]
  have hΦ := cdf_gaussianReal_strictMono 0 (v := 1) one_ne_zero
  have haff : ∀ w, cdf (gaussianReal 0 v.toNNReal) (√v * w) = cdf (gaussianReal 0 1) w := by
    intro w
    simpa using cdf_gaussianReal_affine 0 hs hvv w
  constructor
  · intro ε hε
    rw [show √v * z - ε = √v * (z - ε / √v) by field_simp, haff]
    exact hΦ (by have := div_pos hε hs; linarith)
  · intro ε hε
    rw [show √v * z + ε = √v * (z + ε / √v) by field_simp, haff]
    exact hΦ (by have := div_pos hε hs; linarith)

end PosteriorLimit

end CausalInference
