/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.AggregationLog
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CausalInference.Measures.LinkJensen
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The leading order aggregation bias and the heat flow

For a smooth inverse link `ψ = g⁻¹` the aggregation bias of an arm is, to leading order in the
variance `v` of the linear predictor, `½ ψ''(η(x̄)) v`. Under Gaussian covariates the aggregate
mean is the heat flow `u(m, τ) = E ψ(N(m, τ))` of `ψ` at time `τ = v`, and
`∂_τ u = ½ ∂²_m u`.

## Main definitions

* `gaussHeat ψ m τ = ∫ ψ dN(m, τ)` for a variance `τ : ℝ≥0`.

## Main results

* `abs_integral_sub_taylor_two_le`: `|E ψ(W) - ψ(m) - ½ψ''(m) v| ≤ (M / 6) E|W - m|³` when
  `|ψ'''| ≤ M` on a convex set carrying `W`; `MultilevelModel.abs_aggBias_sub_le` states it for
  an arm of the multilevel model, with `v = (β₁ + β₂,k)ᵀ Σ (β₁ + β₂,k)`.
* `isLittleO_integral_sub_taylor_two`: the remainder is `o(v)` along any family of predictor
  laws whose standardized third absolute moments stay bounded.
* `gaussHeat_hasDerivAt`: the heat equation `∂_τ u = ½ ∂²_m u` for `τ > 0`, by Stein's identity
  (`integral_mul_eq_integral_deriv_stdGaussian`); `gaussHeat_zero_tendsto`: `u(m, τ) → ψ(m)` as
  `τ ↓ 0`.
* `MultilevelModel.armMean_eq_gaussHeat`: under Gaussian covariates the aggregate mean of arm `k`
  is `u(η_k(x̄), v_k)`.

## References

* S. L. Zeger, K.-Y. Liang and P. S. Albert, *Models for longitudinal data: a generalized
  estimating equation approach*, Biometrics 44 (1988).
* D. M. Phillippo, S. Dias, A. E. Ades, M. Belger, A. Brnabic, A. Schacht, D. Saure, Z. Kadziola
  and N. J. Welton, *Multilevel network meta-regression for population-adjusted treatment
  comparisons*, Journal of the Royal Statistical Society Series A 183 (2020).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory ProbabilityTheory Filter Topology IndirectComparison NetworkMetaAnalysis
open scoped NNReal

section Taylor

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Second order Taylor bound on a convex set, with the Lagrange constant.** If `ψ` has
derivatives `ψ₁, ψ₂, ψ₃` within a convex set `I` and `|ψ₃| ≤ M` on `I`, then for `m, w ∈ I`,
`|ψ(w) - ψ(m) - ψ₁(m)(w - m) - ½ψ₂(m)(w - m)²| ≤ (M / 6) |w - m|³`. The proof integrates the
bound three times along `t ↦ m + t (w - m)`, `t ∈ [0, 1]`. -/
theorem abs_taylor_two_le {ψ ψ₁ ψ₂ ψ₃ : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (h₁ : ∀ x ∈ I, HasDerivWithinAt ψ (ψ₁ x) I x) (h₂ : ∀ x ∈ I, HasDerivWithinAt ψ₁ (ψ₂ x) I x)
    (h₃ : ∀ x ∈ I, HasDerivWithinAt ψ₂ (ψ₃ x) I x) {M : ℝ} (hM : ∀ x ∈ I, |ψ₃ x| ≤ M)
    {m w : ℝ} (hm : m ∈ I) (hw : w ∈ I) :
    |ψ w - ψ m - ψ₁ m * (w - m) - ψ₂ m / 2 * (w - m) ^ 2| ≤ M / 6 * |w - m| ^ 3 := by
  set d := w - m with hd
  set U : Set ℝ := Set.Icc 0 1
  have hmem : ∀ t ∈ U, m + t * d ∈ I := fun t ht => by
    simpa [smul_eq_mul] using hI.add_smul_sub_mem hm hw ht
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM m hm)
  have hD : 0 ≤ |d| := abs_nonneg d
  have hcomp : ∀ {g g' : ℝ → ℝ}, (∀ x ∈ I, HasDerivWithinAt g (g' x) I x) → ∀ t ∈ U,
      HasDerivWithinAt (fun t => g (m + t * d)) (g' (m + t * d) * d) U t := by
    intro g g' hg t ht
    have ha : HasDerivWithinAt (fun t : ℝ => m + t * d) d U t := by
      simpa using ((hasDerivWithinAt_id t U).mul_const d).const_add m
    exact (hg _ (hmem t ht)).comp t ha (fun s hs => hmem s hs)
  have right : ∀ {f f' : ℝ → ℝ}, (∀ t ∈ U, HasDerivWithinAt f (f' t) U t) →
      ∀ t ∈ Set.Ico (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Set.Ici t) t := fun hf t ht =>
    (hf t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have cont : ∀ {f f' : ℝ → ℝ}, (∀ t ∈ U, HasDerivWithinAt f (f' t) U t) → ContinuousOn f U :=
    fun hf t ht => (hf t ht).continuousWithinAt
  have hU : ∀ t ∈ Set.Ico (0 : ℝ) 1, t ∈ U := fun t ht => Set.Ico_subset_Icc_self ht
  -- first integration
  set fA : ℝ → ℝ := fun t => ψ₂ (m + t * d) - ψ₂ m
  have hA' : ∀ t ∈ U, HasDerivWithinAt fA (ψ₃ (m + t * d) * d) U t := fun t ht =>
    (hcomp h₃ t ht).sub_const _
  have hA : ∀ t ∈ U, ‖fA t‖ ≤ M * |d| * t := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (B' := fun _ => M * |d|)
      (cont hA') (right hA')
      (by simp [fA]) (fun t => by simpa using (hasDerivAt_id t).const_mul (M * |d|))
      (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hM _ (hmem t (hU t ht))) hD
  -- second integration
  set fB : ℝ → ℝ := fun t => ψ₁ (m + t * d) - ψ₁ m - ψ₂ m * (t * d)
  have hB' : ∀ t ∈ U, HasDerivWithinAt fB (fA t * d) U t := fun t ht => by
    have := ((hcomp h₂ t ht).sub_const (ψ₁ m)).sub
      (((hasDerivWithinAt_id t U).mul_const d).const_mul (ψ₂ m))
    exact this.congr_deriv (by simp only [fA]; ring)
  have hB : ∀ t ∈ U, ‖fB t‖ ≤ M * |d| ^ 2 * t ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (B' := fun t => M * |d| ^ 2 * t)
      (cont hB') (right hB')
      (by simp [fB]) (fun t => ?_) (fun t ht => ?_)
    · have := ((hasDerivAt_id t).pow 2).const_mul (M * |d| ^ 2) |>.div_const 2
      exact this.congr_deriv (by simp only [id]; push_cast; ring)
    · rw [norm_mul, Real.norm_eq_abs d]
      calc ‖fA t‖ * |d| ≤ M * |d| * t * |d| := mul_le_mul_of_nonneg_right (hA t (hU t ht)) hD
        _ = M * |d| ^ 2 * t := by ring
  -- third integration
  set fC : ℝ → ℝ := fun t =>
    ψ (m + t * d) - ψ m - ψ₁ m * (t * d) - ψ₂ m / 2 * (t * d) ^ 2
  have hC' : ∀ t ∈ U, HasDerivWithinAt fC (fB t * d) U t := fun t ht => by
    have := (((hcomp h₁ t ht).sub_const (ψ m)).sub
      (((hasDerivWithinAt_id t U).mul_const d).const_mul (ψ₁ m))).sub
      ((((hasDerivWithinAt_id t U).mul_const d).pow 2).const_mul (ψ₂ m / 2))
    exact this.congr_deriv (by simp only [fB, id]; push_cast; ring)
  have hC : ∀ t ∈ U, ‖fC t‖ ≤ M * |d| ^ 3 * t ^ 3 / 6 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (B' := fun t => M * |d| ^ 3 * t ^ 2 / 2) (cont hC') (right hC')
      (by simp [fC]) (fun t => ?_) (fun t ht => ?_)
    · have := ((hasDerivAt_id t).pow 3).const_mul (M * |d| ^ 3) |>.div_const 6
      exact this.congr_deriv (by simp only [id]; push_cast; ring)
    · rw [norm_mul, Real.norm_eq_abs d]
      calc ‖fB t‖ * |d| ≤ M * |d| ^ 2 * t ^ 2 / 2 * |d| :=
            mul_le_mul_of_nonneg_right (hB t (hU t ht)) hD
        _ = M * |d| ^ 3 * t ^ 2 / 2 := by ring
  have h1 := hC 1 ⟨zero_le_one, le_rfl⟩
  simp only [fC, one_mul, one_pow, mul_one, Real.norm_eq_abs] at h1
  have hw' : m + d = w := by rw [hd]; ring
  rw [hw'] at h1
  calc _ ≤ M * |d| ^ 3 / 6 := h1
    _ = M / 6 * |w - m| ^ 3 := by rw [hd]; ring

/-- **Leading order aggregation bias, quantitative form.** If `ψ = g⁻¹` has derivatives
`ψ₁, ψ₂, ψ₃` within a convex set `I` containing `W` almost surely, with `|ψ₃| ≤ M` on `I`, then
with `m = E W` and `v = Var W`, `|E ψ(W) - ψ(m) - ½ ψ₂(m) v| ≤ (M / 6) · E|W - m|³`. -/
theorem abs_integral_sub_taylor_two_le {ψ ψ₁ ψ₂ ψ₃ : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (h₁ : ∀ x ∈ I, HasDerivWithinAt ψ (ψ₁ x) I x) (h₂ : ∀ x ∈ I, HasDerivWithinAt ψ₁ (ψ₂ x) I x)
    (h₃ : ∀ x ∈ I, HasDerivWithinAt ψ₂ (ψ₃ x) I x) {M : ℝ} (hM : ∀ x ∈ I, |ψ₃ x| ≤ M)
    {W : Ω → ℝ} (hWI : ∀ᵐ ω ∂μ, W ω ∈ I) (hW : MemLp W 2 μ)
    (hψ : Integrable (fun ω => ψ (W ω)) μ)
    (h3 : Integrable (fun ω => |W ω - ∫ x, W x ∂μ| ^ 3) μ) :
    |∫ ω, ψ (W ω) ∂μ - ψ (∫ ω, W ω ∂μ) - ψ₂ (∫ ω, W ω ∂μ) / 2 * variance W μ| ≤
      M / 6 * ∫ ω, |W ω - ∫ x, W x ∂μ| ^ 3 ∂μ := by
  set m := ∫ ω, W ω ∂μ with hm_def
  have hW1 : Integrable W μ := hW.integrable one_le_two
  have hmI : m ∈ I := by
    rcases integral_mem_interior_or_ae_eq hI.ordConnected hW1 hWI with h | h
    · exact interior_subset h
    · obtain ⟨ω, h1, h2⟩ := (hWI.and h).exists
      have h3 : W ω = m := h2
      rw [← h3]
      exact h1
  have hsq : Integrable (fun ω => (W ω - m) ^ 2) μ := (hW.sub (memLp_const m)).integrable_sq
  have hlin : Integrable (fun ω => W ω - m) μ := hW1.sub (integrable_const m)
  have hA : Integrable (fun ω => ψ (W ω) - ψ m) μ := hψ.sub (integrable_const _)
  have hB : Integrable (fun ω => ψ₁ m * (W ω - m)) μ := hlin.const_mul _
  have hC : Integrable (fun ω => ψ₂ m / 2 * (W ω - m) ^ 2) μ := hsq.const_mul _
  have hAB : Integrable (fun ω => ψ (W ω) - ψ m - ψ₁ m * (W ω - m)) μ := hA.sub hB
  have hR : Integrable (fun ω => ψ (W ω) - ψ m - ψ₁ m * (W ω - m) - ψ₂ m / 2 * (W ω - m) ^ 2)
      μ := hAB.sub hC
  have hint : ∫ ω, (ψ (W ω) - ψ m - ψ₁ m * (W ω - m) - ψ₂ m / 2 * (W ω - m) ^ 2) ∂μ =
      ∫ ω, ψ (W ω) ∂μ - ψ m - ψ₂ m / 2 * variance W μ := by
    rw [integral_sub hAB hC, integral_sub hA hB, integral_sub hψ (integrable_const _),
      integral_const_mul, integral_const_mul, integral_sub hW1 (integrable_const _),
      variance_eq_integral hW1.aemeasurable]
    simp [← hm_def]
  rw [← hint]
  calc _ ≤ ∫ ω, |ψ (W ω) - ψ m - ψ₁ m * (W ω - m) - ψ₂ m / 2 * (W ω - m) ^ 2| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ ω, M / 6 * |W ω - m| ^ 3 ∂μ := by
        refine integral_mono_ae hR.abs (h3.const_mul (M / 6)) ?_
        filter_upwards [hWI] with ω hω
        exact abs_taylor_two_le hI h₁ h₂ h₃ hM hmI hω
    _ = M / 6 * ∫ ω, |W ω - m| ^ 3 ∂μ := integral_const_mul _ _

/-- **Leading order aggregation bias.** Along a filter on which the variance `v` of the predictor
laws `ν i` tends to `0`, with `E|W - m|³ ≤ K v √v` and `|ψ₃| ≤ M` on a convex set `I` carrying
the laws, `E ψ(W) = ψ(m) + ½ ψ₂(m) v + o(v)`. -/
theorem isLittleO_integral_sub_taylor_two {ι : Type*} {l : Filter ι} {ψ ψ₁ ψ₂ ψ₃ : ℝ → ℝ}
    {I : Set ℝ}
    (hI : Convex ℝ I) (h₁ : ∀ x ∈ I, HasDerivWithinAt ψ (ψ₁ x) I x)
    (h₂ : ∀ x ∈ I, HasDerivWithinAt ψ₁ (ψ₂ x) I x) (h₃ : ∀ x ∈ I, HasDerivWithinAt ψ₂ (ψ₃ x) I x)
    {M : ℝ} (hM : ∀ x ∈ I, |ψ₃ x| ≤ M) (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hνI : ∀ i, ∀ᵐ x ∂ν i, x ∈ I) (hν2 : ∀ i, MemLp (fun x : ℝ => x) 2 (ν i))
    (hψ : ∀ i, Integrable ψ (ν i))
    (h3 : ∀ i, Integrable (fun x => |x - ∫ y, y ∂ν i| ^ 3) (ν i)) {K : ℝ}
    (hK : ∀ i, ∫ x, |x - ∫ y, y ∂ν i| ^ 3 ∂ν i ≤
      K * variance (fun x => x) (ν i) * √(variance (fun x => x) (ν i)))
    (hv : Filter.Tendsto (fun i => variance (fun x => x) (ν i)) l (nhds 0)) :
    (fun i => ∫ x, ψ x ∂ν i - ψ (∫ x, x ∂ν i) - ψ₂ (∫ x, x ∂ν i) / 2 *
      variance (fun x => x) (ν i)) =o[l] (fun i => variance (fun x => x) (ν i)) := by
  set C := |M| * max K 0 + 1 with hC
  have hC0 : 0 < C := by positivity
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hsq : Filter.Tendsto (fun i => √(variance (fun x => x) (ν i))) l (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hv
    simpa [Function.comp_def] using this
  filter_upwards [hsq.eventually (ge_mem_nhds (div_pos hc hC0))] with i hi
  set v := variance (fun x => x) (ν i)
  have hv0 : 0 ≤ v := variance_nonneg _ _
  have hb := abs_integral_sub_taylor_two_le (μ := ν i) (W := fun x => x) hI h₁ h₂ h₃ hM (hνI i)
    (hν2 i) (hψ i) (h3 i)
  have hE0 : 0 ≤ ∫ x, |x - ∫ y, y ∂ν i| ^ 3 ∂ν i := integral_nonneg fun _ => by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hv0]
  calc _ ≤ M / 6 * ∫ x, |x - ∫ y, y ∂ν i| ^ 3 ∂ν i := hb
    _ ≤ |M| * ∫ x, |x - ∫ y, y ∂ν i| ^ 3 ∂ν i :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self M, abs_nonneg M]) hE0
    _ ≤ |M| * (max K 0 * v * √v) := by
        refine mul_le_mul_of_nonneg_left ((hK i).trans ?_) (abs_nonneg M)
        gcongr
        exact le_max_left _ _
    _ ≤ C * v * √v := by
        rw [hC]; nlinarith [abs_nonneg M, le_max_right K 0, Real.sqrt_nonneg v,
          mul_nonneg hv0 (Real.sqrt_nonneg v), mul_nonneg (mul_nonneg (abs_nonneg M)
          (le_max_right K 0)) (mul_nonneg hv0 (Real.sqrt_nonneg v))]
    _ ≤ C * v * (c / C) := by gcongr
    _ = c * v := by field_simp

end Taylor

/-! ### The heat flow -/

section HeatFlow

/-- The **Gaussian heat flow** `u(m, τ) = E ψ(N(m, τ))` of a function `ψ`, for a variance
`τ ≥ 0`. -/
noncomputable def gaussHeat (ψ : ℝ → ℝ) (m : ℝ) (τ : ℝ≥0) : ℝ := ∫ z, ψ z ∂gaussianReal m τ

/-- `exp(b |s|)` is integrable for the standard normal law. -/
theorem integrable_exp_mul_abs_stdGaussian (b : ℝ) :
    Integrable (fun s => Real.exp (b * |s|)) (gaussianReal 0 1) := by
  refine ((integrable_exp_mul_gaussianReal b).add (integrable_exp_mul_gaussianReal (-b))).mono'
    (by fun_prop) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply]
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-b * s)]
  · rw [abs_of_nonpos h]
    have : b * -s = -b * s := by ring
    rw [this]; linarith [Real.exp_pos (b * s)]

/-- `|s| exp(b |s|)` is integrable for the standard normal law. -/
theorem integrable_abs_mul_exp_stdGaussian (b : ℝ) :
    Integrable (fun s => |s| * Real.exp (b * |s|)) (gaussianReal 0 1) := by
  refine (integrable_exp_mul_abs_stdGaussian (b + 1)).mono' (by fun_prop) (ae_of_all _ fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le),
    add_mul, one_mul, Real.exp_add, mul_comm]
  exact mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp |s|]) (Real.exp_pos _).le

/-- An exponential growth bound along `m' + c s`. -/
theorem abs_comp_affine_le_exp {f : ℝ → ℝ} {C a : ℝ} (hf : ∀ z, |f z| ≤ C * Real.exp (a * |z|))
    {m' c R : ℝ} (hm : |m'| ≤ R) (hc : 0 ≤ c) (s : ℝ) :
    |f (m' + c * s)| ≤ C * Real.exp (|a| * R) * Real.exp (|a| * c * |s|) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hf 0)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  refine (hf _).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC
  have h1 : |m' + c * s| ≤ R + c * |s| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hc]; linarith
  calc a * |m' + c * s| ≤ |a| * |m' + c * s| :=
        mul_le_mul_of_nonneg_right (le_abs_self a) (abs_nonneg _)
    _ ≤ |a| * (R + c * |s|) := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
    _ = _ := by ring

/-- The standard form `u(m, τ) = E ψ(m + √τ Z)`. -/
theorem gaussHeat_eq_integral_std {ψ : ℝ → ℝ} (hψ : Continuous ψ) (m : ℝ) (τ : ℝ≥0) :
    gaussHeat ψ m τ = ∫ s, ψ (m + √(τ : ℝ) * s) ∂gaussianReal 0 1 := by
  have hmap : (gaussianReal 0 1).map (fun s => m + √(τ : ℝ) * s) = gaussianReal m τ := by
    have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (√(τ : ℝ))
    rw [show (fun s => m + √(τ : ℝ) * s) = (fun x => m + x) ∘ (fun s => √(τ : ℝ) * s) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_const_add]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt τ.coe_nonneg]
  rw [gaussHeat, ← hmap, integral_map (by fun_prop) hψ.aestronglyMeasurable]

/-- Differentiation in the location under the standard normal integral. -/
theorem hasDerivAt_integral_stdGaussian_shift {f f' : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (f' z) z)
    (hf'c : Continuous f') {C a : ℝ} (hf : ∀ z, |f z| ≤ C * Real.exp (a * |z|))
    (hf' : ∀ z, |f' z| ≤ C * Real.exp (a * |z|)) {c : ℝ} (hc : 0 ≤ c) (m : ℝ) :
    HasDerivAt (fun m => ∫ s, f (m + c * s) ∂gaussianReal 0 1)
      (∫ s, f' (m + c * s) ∂gaussianReal 0 1) m := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun z => (hd z).continuousAt
  have hint : ∀ R, Integrable (fun s => C * Real.exp (|a| * R) * Real.exp (|a| * c * |s|))
      (gaussianReal 0 1) := fun R => (integrable_exp_mul_abs_stdGaussian _).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := fun m' s => f (m' + c * s)) (F' := fun m' s => f' (m' + c * s))
    (bound := fun s => C * Real.exp (|a| * (|m| + 1)) * Real.exp (|a| * c * |s|))
    (Metric.ball_mem_nhds m one_pos) ?_ ?_ ?_ ?_ (hint _) ?_).2
  · exact Eventually.of_forall fun m' => (hfc.comp (by fun_prop)).aestronglyMeasurable
  · exact (hint |m|).mono' (hfc.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact abs_comp_affine_le_exp hf le_rfl hc s)
  · exact (hf'c.comp (by fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ fun s m' hm' => ?_
    rw [Real.norm_eq_abs]
    refine abs_comp_affine_le_exp hf' ?_ hc s
    have h := Metric.mem_ball.mp hm'
    rw [Real.dist_eq] at h
    linarith [abs_sub_abs_le_abs_sub m' m, (abs_lt.mp h).2]
  · refine ae_of_all _ fun s m' _ => ?_
    exact ((hd (m' + c * s)).comp m' ((hasDerivAt_id' m').add_const (c * s))).congr_deriv
      (mul_one _)

/-- Differentiation in the variance `τ > 0` under the standard normal integral. -/
theorem hasDerivAt_integral_stdGaussian_scale {f f' : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (f' z) z)
    (hf'c : Continuous f') {C a : ℝ} (hf : ∀ z, |f z| ≤ C * Real.exp (a * |z|))
    (hf' : ∀ z, |f' z| ≤ C * Real.exp (a * |z|)) (m : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun t => ∫ s, f (m + √t * s) ∂gaussianReal 0 1)
      (∫ s, f' (m + √τ * s) * (s / (2 * √τ)) ∂gaussianReal 0 1) τ := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun z => (hd z).continuousAt
  set K := C * Real.exp (|a| * |m|) * (1 / (2 * √(τ / 2)))
  have hK : Integrable (fun s => K * (|s| * Real.exp (|a| * √(2 * τ) * |s|))) (gaussianReal 0 1) :=
    (integrable_abs_mul_exp_stdGaussian _).const_mul _
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hf 0)) (Real.exp_pos _)
  have hball : ∀ t ∈ Metric.ball τ (τ / 2), τ / 2 < t ∧ t < 2 * τ := fun t ht => by
    have h := Metric.mem_ball.mp ht
    rw [Real.dist_eq, abs_lt] at h
    constructor <;> linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (F := fun t s => f (m + √t * s)) (F' := fun t s => f' (m + √t * s) * (s / (2 * √t)))
    (bound := fun s => K * (|s| * Real.exp (|a| * √(2 * τ) * |s|)))
    (Metric.ball_mem_nhds τ (half_pos hτ)) ?_ ?_ ?_ ?_ hK ?_).2
  · exact Eventually.of_forall fun t => (hfc.comp (by fun_prop)).aestronglyMeasurable
  · exact ((integrable_exp_mul_abs_stdGaussian _).const_mul _).mono'
      (hfc.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs]; exact abs_comp_affine_le_exp hf le_rfl (Real.sqrt_nonneg τ) s)
  · exact ((hf'c.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · refine ae_of_all _ fun s t ht => ?_
    obtain ⟨h1, h2⟩ := hball t ht
    have hst : 0 < √t := Real.sqrt_pos.mpr (by linarith)
    have hlow : √(τ / 2) ≤ √t := Real.sqrt_le_sqrt h1.le
    have hlow' : 0 < √(τ / 2) := Real.sqrt_pos.mpr (by linarith)
    have hup : √t ≤ √(2 * τ) := Real.sqrt_le_sqrt h2.le
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * √t)]
    have g := abs_comp_affine_le_exp hf' le_rfl hst.le s (m' := m)
    have g2 : Real.exp (|a| * √t * |s|) ≤ Real.exp (|a| * √(2 * τ) * |s|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hup (abs_nonneg a)) (abs_nonneg s))
    have g3 : |s| / (2 * √t) ≤ |s| * (1 / (2 * √(τ / 2))) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) (by linarith))
        (abs_nonneg s)
    calc |f' (m + √t * s)| * (|s| / (2 * √t))
        ≤ (C * Real.exp (|a| * |m|) * Real.exp (|a| * √(2 * τ) * |s|)) *
            (|s| * (1 / (2 * √(τ / 2)))) := by
          refine mul_le_mul (g.trans (mul_le_mul_of_nonneg_left g2 (by positivity))) g3
            (by positivity) (by positivity)
      _ = K * (|s| * Real.exp (|a| * √(2 * τ) * |s|)) := by simp only [K]; ring
  · refine ae_of_all _ fun s t ht => ?_
    obtain ⟨h1, -⟩ := hball t ht
    have h1' := ((Real.hasDerivAt_sqrt (by linarith : t ≠ 0)).mul_const s).const_add m
    exact ((hd (m + √t * s)).comp t h1').congr_deriv (by ring)

/-- **Stein's identity** for the standard normal law: `E[Z g(Z)] = E[g'(Z)]` for a continuously
differentiable `g` of exponential growth. -/
theorem integral_mul_eq_integral_deriv_stdGaussian {g g' : ℝ → ℝ}
    (hd : ∀ s, HasDerivAt g (g' s) s) (hg'c : Continuous g')
    {K K' B : ℝ} (hg : ∀ s, |g s| ≤ K * Real.exp (B * |s|))
    (hg' : ∀ s, |g' s| ≤ K' * Real.exp (B * |s|)) :
    ∫ s, s * g s ∂gaussianReal 0 1 = ∫ s, g' s ∂gaussianReal 0 1 := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun z => (hd z).continuousAt
  set φ := gaussianPDFReal 0 1
  have hφeq : φ = fun y => (√(2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2) := by
    funext y; simp [φ, gaussianPDFReal]
  have hφ : ∀ x, HasDerivAt φ (-x * φ x) x := fun x => by
    have h := ((hasDerivAt_pow 2 x).neg.div_const 2).exp.const_mul (√(2 * Real.pi))⁻¹
    rw [hφeq]
    convert h using 1
    simp only [Nat.cast_ofNat, Pi.neg_apply]
    ring_nf
  have hiff : ∀ h : ℝ → ℝ, Integrable h (gaussianReal 0 1) →
      Integrable (fun x => φ x * h x) := fun h hh => by
    rw [gaussianReal_of_var_ne_zero _ one_ne_zero, integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF _ _) (ae_of_all _ fun _ => gaussianPDF_lt_top)] at hh
    simpa [toReal_gaussianPDF] using hh
  have hB : ∀ K₀ s, K₀ * Real.exp (B * |s|) ≤ |K₀| * Real.exp (|B| * |s|) := fun K₀ s =>
    mul_le_mul (le_abs_self K₀) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self B)
      (abs_nonneg s))) (Real.exp_pos _).le (abs_nonneg K₀)
  have ig : Integrable g (gaussianReal 0 1) :=
    ((integrable_exp_mul_abs_stdGaussian |B|).const_mul |K|).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun s => (hg s).trans (hB K s))
  have ig' : Integrable g' (gaussianReal 0 1) :=
    ((integrable_exp_mul_abs_stdGaussian |B|).const_mul |K'|).mono' hg'c.aestronglyMeasurable
      (ae_of_all _ fun s => (hg' s).trans (hB K' s))
  have isg : Integrable (fun s => s * g s) (gaussianReal 0 1) :=
    ((integrable_abs_mul_exp_stdGaussian |B|).const_mul |K|).mono' (by fun_prop)
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left ((hg s).trans (hB K s)) (abs_nonneg s))
  have ibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := g) (v := φ) (u' := g')
    (v' := fun x => -x * φ x) (fun x _ => hd x) (fun x _ => hφ x)
    (by
      have := (hiff _ isg).neg
      convert this using 1; funext x; simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by
      have := hiff _ ig'
      convert this using 1; funext x; simp only [Pi.mul_apply]; ring)
    (by
      have := hiff _ ig
      convert this using 1; funext x; simp only [Pi.mul_apply]; ring)
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have e1 : ∫ x, φ x * (x * g x) = -∫ x, g x * (-x * φ x) := by
    rw [← integral_neg]; congr 1; funext x; ring
  have e2 : ∫ x, φ x * g' x = ∫ x, g' x * φ x := by congr 1; funext x; ring
  change ∫ x, φ x * (x * g x) = ∫ x, φ x * g' x
  rw [e1, e2, ibp, neg_neg]

/-- **The heat flow of the inverse link.** For `ψ` of class `C²` with `ψ`, `ψ'` and `ψ''` bounded
by `C e^{a |z|}`, the function `u(m, τ) = E ψ(N(m, τ))` satisfies, for `τ > 0`,
`∂_m u = E ψ'`, `∂²_m u = E ψ''` and `∂_τ u = ½ ∂²_m u`: the derivative of the aggregate mean
in the predictor variance is half the average second derivative of the inverse link. The time
derivative is taken within the positive variances `t > 0`, where `u(m, t)` is
`gaussHeat ψ m t.toNNReal`. -/
theorem gaussHeat_hasDerivAt {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) {C a : ℝ}
    (h0 : ∀ z, |ψ z| ≤ C * Real.exp (a * |z|)) (h1 : ∀ z, |deriv ψ z| ≤ C * Real.exp (a * |z|))
    (h2 : ∀ z, |deriv (deriv ψ) z| ≤ C * Real.exp (a * |z|)) (m : ℝ) {τ : ℝ≥0} (hτ : 0 < τ) :
    HasDerivAt (fun m => gaussHeat ψ m τ) (gaussHeat (deriv ψ) m τ) m ∧
      HasDerivAt (fun m => gaussHeat (deriv ψ) m τ) (gaussHeat (deriv (deriv ψ)) m τ) m ∧
      HasDerivWithinAt (fun t : ℝ => gaussHeat ψ m t.toNNReal)
        (gaussHeat (deriv (deriv ψ)) m τ / 2) (Set.Ioi 0) τ := by
  have hτr : (0 : ℝ) < τ := hτ
  obtain ⟨hdiff, -, hψ1⟩ := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) ψ from hψ)
  obtain ⟨hdiff1, hc2⟩ := contDiff_one_iff_deriv.mp hψ1
  have hd0 : ∀ z, HasDerivAt ψ (deriv ψ z) z := fun z => (hdiff z).hasDerivAt
  have hd1 : ∀ z, HasDerivAt (deriv ψ) (deriv (deriv ψ) z) z := fun z => (hdiff1 z).hasDerivAt
  have hc0 : Continuous ψ := hdiff.continuous
  have hc1 : Continuous (deriv ψ) := hdiff1.continuous
  have hstd : ∀ f : ℝ → ℝ, Continuous f →
      (fun m' => gaussHeat f m' τ) = fun m' => ∫ s, f (m' + √(τ : ℝ) * s) ∂gaussianReal 0 1 :=
    fun f hf => funext fun m' => gaussHeat_eq_integral_std hf m' τ
  have hst := Real.sqrt_nonneg (τ : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · rw [hstd ψ hc0, gaussHeat_eq_integral_std hc1 m τ]
    exact hasDerivAt_integral_stdGaussian_shift hd0 hc1 h0 h1 hst m
  · rw [hstd _ hc1, gaussHeat_eq_integral_std hc2 m τ]
    exact hasDerivAt_integral_stdGaussian_shift hd1 hc2 h1 h2 hst m
  · have hG := hasDerivAt_integral_stdGaussian_scale hd0 hc1 h0 h1 m hτr
    have hstein := integral_mul_eq_integral_deriv_stdGaussian (g := fun s => deriv ψ (m + √τ * s))
      (g' := fun s => √τ * deriv (deriv ψ) (m + √τ * s))
      (fun s => by
        have h := (hd1 (m + √τ * s)).comp s (((hasDerivAt_id' s).const_mul √τ).const_add m)
        have e : deriv (deriv ψ) (m + √τ * s) * (√τ * 1) =
            √τ * deriv (deriv ψ) (m + √τ * s) := by ring
        rw [e] at h
        exact h)
      (by fun_prop)
      (K := C * Real.exp (|a| * |m|)) (K' := √τ * (C * Real.exp (|a| * |m|))) (B := |a| * √τ)
      (fun s => abs_comp_affine_le_exp h1 le_rfl hst s)
      (fun s => by
        rw [abs_mul, abs_of_nonneg hst, mul_assoc]
        exact mul_le_mul_of_nonneg_left (abs_comp_affine_le_exp h2 le_rfl hst s) hst)
    have hτ' : √(τ : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hτr).ne'
    have e : ∫ s, deriv ψ (m + √τ * s) * (s / (2 * √τ)) ∂gaussianReal 0 1 =
        gaussHeat (deriv (deriv ψ)) m τ / 2 := by
      calc ∫ s, deriv ψ (m + √τ * s) * (s / (2 * √τ)) ∂gaussianReal 0 1
          = (1 / (2 * √τ)) * ∫ s, s * deriv ψ (m + √τ * s) ∂gaussianReal 0 1 := by
            rw [← integral_const_mul]; congr 1; funext s; ring
        _ = (1 / (2 * √τ)) * (√τ * ∫ s, deriv (deriv ψ) (m + √τ * s) ∂gaussianReal 0 1) := by
            rw [hstein, integral_const_mul]
        _ = _ := by rw [gaussHeat_eq_integral_std hc2 m τ]; field_simp
    rw [e] at hG
    refine hG.hasDerivWithinAt.congr (fun t ht => ?_) ?_
    · rw [gaussHeat_eq_integral_std hc0 m, Real.coe_toNNReal _ (le_of_lt ht)]
    · rw [gaussHeat_eq_integral_std hc0 m, Real.toNNReal_coe]

/-- **The initial condition**: `u(m, 0) = ψ(m)` and `u(m, τ) → ψ(m)` as `τ → 0` in `ℝ≥0`, for
continuous `ψ` of exponential growth. -/
theorem gaussHeat_zero_tendsto {ψ : ℝ → ℝ} (hc : Continuous ψ) {C a : ℝ}
    (h0 : ∀ z, |ψ z| ≤ C * Real.exp (a * |z|)) (m : ℝ) :
    gaussHeat ψ m 0 = ψ m ∧ Tendsto (fun t => gaussHeat ψ m t) (𝓝 0) (𝓝 (ψ m)) := by
  refine ⟨by simp [gaussHeat, gaussianReal_zero_var], ?_⟩
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (h0 0)) (Real.exp_pos _)
  have key : Tendsto (fun t => ∫ s, ψ (m + √t * s) ∂gaussianReal 0 1) (𝓝[≥] 0)
      (𝓝 (∫ s, ψ (m + √0 * s) ∂gaussianReal 0 1)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => C * Real.exp (|a| * |m|) * Real.exp (|a| * 1 * |s|))
      (Eventually.of_forall fun t => (hc.comp (by fun_prop)).aestronglyMeasurable) ?_
      ((integrable_exp_mul_abs_stdGaussian _).const_mul _) (ae_of_all _ fun s => ?_)
    · filter_upwards [Ico_mem_nhdsGE one_pos] with t ht
      refine ae_of_all _ fun s => ?_
      rw [Real.norm_eq_abs]
      refine (abs_comp_affine_le_exp h0 le_rfl (Real.sqrt_nonneg t) s).trans ?_
      have : √t ≤ 1 := Real.sqrt_le_one.mpr ht.2.le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left this (abs_nonneg a)) (abs_nonneg s)))
        (mul_nonneg hC (Real.exp_pos _).le)
    · exact ((hc.comp (by fun_prop : Continuous fun t : ℝ => m + √t * s)).tendsto 0).mono_left
        nhdsWithin_le_nhds
  simp only [Real.sqrt_zero, zero_mul, add_zero, integral_const, probReal_univ, smul_eq_mul,
    one_mul] at key
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝 0) (𝓝[≥] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using NNReal.continuous_coe.tendsto 0,
      Eventually.of_forall fun t => t.2⟩
  refine (key.comp hcoe).congr fun t => ?_
  exact (gaussHeat_eq_integral_std hc m t).symm

end HeatFlow

/-! ### Arms of the multilevel model -/

namespace MultilevelModel

variable {J K : Type*} {p : ℕ}

/-- **The leading order bias of an arm.** If `ψ = g⁻¹` has derivatives `ψ₁, ψ₂, ψ₃` within a
convex set `I` that carries `η_k(X)` almost surely under `F`, with `|ψ₃| ≤ M₃` on `I`, the
coordinates have second moments and the integrands below are integrable, then
`|bias_k - ½ ψ₂(η_k(x̄)) v_k| ≤ (M₃ / 6) E|η_k(X) - η_k(x̄)|³`. -/
theorem abs_aggBias_sub_le {ψ ψ₁ ψ₂ ψ₃ : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (h₁ : ∀ x ∈ I, HasDerivWithinAt ψ (ψ₁ x) I x) (h₂ : ∀ x ∈ I, HasDerivWithinAt ψ₁ (ψ₂ x) I x)
    (h₃ : ∀ x ∈ I, HasDerivWithinAt ψ₂ (ψ₃ x) I x) {M₃ : ℝ} (hM : ∀ x ∈ I, |ψ₃ x| ≤ M₃)
    (M : MultilevelModel J K p) (α : ℝ) {F : Measure (Fin p → ℝ)} [IsProbabilityMeasure F]
    (hF : ∀ i, MemLp (fun x : Fin p → ℝ => x i) 2 F) (k : K)
    (hI' : ∀ᵐ x ∂F, M.eta α k x ∈ I) (hψ : Integrable (M.surface ψ α k) F)
    (h3 : Integrable (fun x => |M.eta α k x - M.eta α k (covMean F)| ^ 3) F) :
    |M.aggBias ψ α F k - ψ₂ (M.eta α k (covMean F)) / 2 * slopeVar F (M.β₁ + M.β₂ k)| ≤
      M₃ / 6 * ∫ x, |M.eta α k x - M.eta α k (covMean F)| ^ 3 ∂F := by
  have h1 : ∀ i, Integrable (fun x : Fin p → ℝ => x i) F := fun i => (hF i).integrable one_le_two
  have hm := M.integral_eta α h1 k
  have e : M.eta α k = fun x => (α + M.γ k) + x ⬝ᵥ (M.β₁ + M.β₂ k) :=
    funext fun x => eta_eq_affine M α k x
  have hW : MemLp (M.eta α k) 2 F := by
    have e' : M.eta α k = fun x => (α + M.γ k) + ∑ i, x i * (M.β₁ + M.β₂ k) i :=
      funext fun x => by rw [eta_eq_affine]; rfl
    rw [e']
    exact (memLp_const _).add (memLp_finsetSum _ fun i _ => (hF i).mul_const _)
  have hvar : Var[M.eta α k; F] = slopeVar F (M.β₁ + M.β₂ k) := by
    rw [slopeVar_eq_variance hF, e]
    exact variance_const_add ((by unfold dotProduct; fun_prop :
      Continuous fun x : Fin p → ℝ => x ⬝ᵥ (M.β₁ + M.β₂ k)).aestronglyMeasurable) _
  rw [← hm] at h3 ⊢
  have := abs_integral_sub_taylor_two_le (W := M.eta α k) hI h₁ h₂ h₃ hM hI' hW hψ h3
  rw [hvar] at this
  rw [aggBias, ← hm]
  exact this

/-- **Under Gaussian covariates the aggregate mean is the heat flow** of the inverse link at the
plug in predictor and time `v_k`: `armMean = u(η_k(x̄), v_k)`. -/
theorem armMean_eq_gaussHeat {ψ : ℝ → ℝ} (hψ : Measurable ψ) (M : MultilevelModel J K p)
    (α : ℝ) (F : Measure (Fin p → ℝ)) [IsGaussian F] (k : K) :
    M.armMean ψ α F k =
      gaussHeat ψ (M.eta α k (covMean F)) (slopeVar F (M.β₁ + M.β₂ k)).toNNReal := by
  have hL := M.hasLaw_eta_gaussian α F k
  rw [armMean, gaussHeat, ← hL.map_eq, integral_map hL.aemeasurable hψ.aestronglyMeasurable]
  rfl

end MultilevelModel

end NetworkMetaRegression

end CausalInference
