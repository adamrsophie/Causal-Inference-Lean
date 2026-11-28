/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolutionGeneral
public import CausalInference.Estimation.HajekConvolutionVector
public import CausalInference.Estimation.ProductFamilyRegularSmooth

/-!
# A regular estimator with a limit law that is not Gaussian

In the normal location family `N(θ, 1)` (information `1`) consider, at a fixed `θ₀`,

`T_n(x) = x̄_n + n^{-1/2} s(x_0 - θ₀)`, with `s(y) = 1` for `y > 0` and `s(y) = -1` otherwise.

Here `θ₀` is a fixed known constant built into the statistic, which is a measurable function of
the sample alone. Regularity is a local property, and `T` is proved regular at the single point
`θ₀`; nothing is claimed at other points.

Under `θ_n = θ₀ + h / √n` the statistic `√n (T_n - θ_n)` is the sum of
`n^{-1/2} ∑ (x_i - θ_n) + s(x_0 - θ₀)`; its characteristic function factorizes over the
coordinates of the sample, and it tends to `e^{-t²/2} cos t`, the characteristic function of the
mixture `L = ½ N(1, 1) + ½ N(-1, 1)`, whatever `h`. So `T` is regular at `θ₀` with limit `L`. The
law `L` is not Gaussian: its characteristic function vanishes at `π/2`, and a Gaussian
characteristic function never vanishes. Hence `hajek_convolution_bound` (Gaussian limits) does not
apply to `T`, while `hajek_convolution_bound_general` does, and gives `1 = I(θ₀)⁻¹ ≤ Var(L) = 2`.

## Main definitions

* `CausalInference.ParametricFamily.stepSign`: the step `s(y) = 1` for `y > 0`, `-1` otherwise.
* `CausalInference.ParametricFamily.signMixture`: the law `½ N(1, 1) + ½ N(-1, 1)`.
* `CausalInference.ParametricFamily.signShiftedMean θ₀`: the estimator `T`.

## Main results

* `charFun_signMixture`: the characteristic function of `L` is `e^{-t²/2} cos t`.
* `signMixture_ne_gaussianReal`: `L` is not a Gaussian law.
* `variance_signMixture`: `Var(L) = 2`.
* `signShiftedMean_isHajekRegular`: `T` is regular at `θ₀` with limit `L`.
* `signShiftedMean_not_isHajekRegular_gaussian`: `T` has no Gaussian limit law.
* `signShiftedMean_convolution_bound`: the general bound for `T`, `I(θ₀)⁻¹ ≤ Var(L)`, with both
  sides computed: `1 ≤ 2`.
* `realSampleMean_convolution_bound_general`: the Gaussian instance through the general theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference

namespace ParametricFamily

/-! ### The limit law -/

/-- The step function `s(y) = 1` for `y > 0` and `s(y) = -1` for `y ≤ 0`. -/
noncomputable def stepSign (y : ℝ) : ℝ := if 0 < y then 1 else -1

lemma measurable_stepSign : Measurable stepSign :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

/-- `e^{i t s(z)} = cos t + i s(z) sin t`, since `s(z) = ± 1`. -/
lemma exp_stepSign (t z : ℝ) :
    cexp (((t * stepSign z : ℝ) : ℂ) * I) =
      (Real.cos t : ℂ) + ((stepSign z * Real.sin t : ℝ) : ℂ) * I := by
  unfold stepSign
  split_ifs
  · simp only [mul_one, one_mul]
    rw [exp_mul_I, ofReal_cos, ofReal_sin]
  · simp only [mul_neg, mul_one, neg_mul, one_mul, ofReal_neg]
    rw [show -((t : ℂ) * I) = (-(t : ℂ)) * I by ring, exp_mul_I, cos_neg, sin_neg, ofReal_cos,
      ofReal_sin]
    ring

/-- The standard normal law puts no mass on `0`. -/
lemma ae_ne_zero_gaussianReal_zero_one : ∀ᵐ z ∂gaussianReal 0 1, z ≠ 0 := by
  have h0 : gaussianReal 0 1 {0} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton)
  rw [ae_iff]
  simpa using h0

/-- `E[s(Z)] = 0` for a standard normal `Z`, by the symmetry `Z ↦ -Z` and `P(Z = 0) = 0`. -/
lemma integral_stepSign_gaussianReal : ∫ z, stepSign z ∂gaussianReal 0 1 = 0 := by
  have hsym : ∫ z, stepSign z ∂gaussianReal 0 1 = ∫ z, stepSign (-z) ∂gaussianReal 0 1 := by
    conv_lhs => rw [← neg_zero, ← gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)]
    rw [integral_map (by fun_prop) measurable_stepSign.aestronglyMeasurable]
  have hodd : ∫ z, stepSign (-z) ∂gaussianReal 0 1 = -∫ z, stepSign z ∂gaussianReal 0 1 := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_ne_zero_gaussianReal_zero_one.mono fun z hz ↦ ?_)
    unfold stepSign
    rcases lt_or_gt_of_ne hz with h | h
    · simp [h, not_lt.2 h.le]
    · simp [h, not_lt.2 (neg_nonpos.2 h.le)]
  linarith

/-- `E[e^{i t s(Z)}] = cos t` for a standard normal `Z`. -/
lemma integral_exp_stepSign_gaussianReal (t : ℝ) :
    ∫ z, cexp (((t * stepSign z : ℝ) : ℂ) * I) ∂gaussianReal 0 1 = Real.cos t := by
  simp_rw [exp_stepSign]
  have hb : Integrable (fun z ↦ stepSign z) (gaussianReal 0 1) :=
    Integrable.of_bound measurable_stepSign.aestronglyMeasurable 1
      (Eventually.of_forall fun z ↦ by unfold stepSign; split_ifs <;> simp)
  rw [integral_add (integrable_const _), integral_const, integral_mul_const,
    integral_complex_ofReal, integral_mul_const, integral_stepSign_gaussianReal]
  · simp
  · exact ((hb.mul_const _).ofReal).mul_const _

/-- **The mixture `½ N(1, 1) + ½ N(-1, 1)`**, the law of `Z + s(ε)` for independent standard
normal `Z` and `ε`. -/
noncomputable def signMixture : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • gaussianReal 1 1 + (2⁻¹ : ℝ≥0∞) • gaussianReal (-1) 1

instance : IsProbabilityMeasure signMixture := by
  constructor
  simp only [signMixture, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- Integrals against the mixture are averages of the two Gaussian integrals. -/
lemma integral_signMixture {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (h1 : Integrable f (gaussianReal 1 1)) (h2 : Integrable f (gaussianReal (-1) 1)) :
    ∫ x, f x ∂signMixture =
      (2⁻¹ : ℝ) • ∫ x, f x ∂gaussianReal 1 1 + (2⁻¹ : ℝ) • ∫ x, f x ∂gaussianReal (-1) 1 := by
  rw [signMixture, integral_add_measure (h1.smul_measure (by simp))
    (h2.smul_measure (by simp)), integral_smul_measure, integral_smul_measure]
  simp

/-- **The characteristic function of the mixture** is `e^{-t²/2} cos t`. -/
theorem charFun_signMixture (t : ℝ) :
    charFun signMixture t = cexp (-(t : ℂ) ^ 2 / 2) * Real.cos t := by
  have hi : ∀ m : ℝ, Integrable (fun x : ℝ ↦ cexp (t * x * I)) (gaussianReal m 1) := fun m ↦
    (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun x ↦ by
      rw [show (t : ℂ) * x * I = ((t * x : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I])
  have e : ∀ s : ℝ, cexp ((t : ℂ) * (s : ℂ) * I - (((1 : ℝ≥0) : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) =
      cexp ((t : ℂ) * (s : ℂ) * I) * cexp (-(t : ℂ) ^ 2 / 2) := fun s ↦ by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [charFun_apply_real, integral_signMixture (hi 1) (hi (-1)), ← charFun_apply_real,
    ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal, e, e, ofReal_cos,
    Complex.cos]
  simp only [ofReal_one, ofReal_neg, real_smul, ofReal_inv, ofReal_ofNat]
  ring_nf

/-- **The mixture is not a Gaussian law**: its characteristic function vanishes at `π/2`, while
`charFun (N(m, v)) t = e^{i t m - v t²/2}` never vanishes. -/
theorem signMixture_ne_gaussianReal (m : ℝ) (v : ℝ≥0) : signMixture ≠ gaussianReal m v := by
  intro h
  have h1 := charFun_signMixture (Real.pi / 2)
  rw [Real.cos_pi_div_two, ofReal_zero, mul_zero, h, charFun_gaussianReal] at h1
  exact Complex.exp_ne_zero _ h1

/-- The mixture has a finite second moment. -/
lemma memLp_signMixture : MemLp id 2 signMixture :=
  ((memLp_id_gaussianReal 2).smul_measure (by simp)).add_measure
    ((memLp_id_gaussianReal 2).smul_measure (by simp))

/-- **The variance of the mixture is `2`**: mean `0` and second moment `½ (1 + 1) + ½ (1 + 1)`. -/
theorem variance_signMixture : Var[id; signMixture] = 2 := by
  have hm : ∀ m : ℝ, ∫ x, x ^ 2 ∂gaussianReal m 1 = m ^ 2 + 1 := fun m ↦ by
    have h := variance_eq_sub (μ := gaussianReal m 1) (memLp_id_gaussianReal 2)
    rw [variance_id_gaussianReal] at h
    simp only [id, Pi.pow_apply, NNReal.coe_one] at h
    rw [integral_id_gaussianReal] at h
    linarith
  have hi : ∀ m : ℝ, Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal m 1) := fun m ↦
    (memLp_id_gaussianReal 2).integrable_sq
  have hi1 : ∀ m : ℝ, Integrable (fun x : ℝ ↦ x) (gaussianReal m 1) := fun m ↦
    (memLp_id_gaussianReal 1).integrable le_rfl
  rw [variance_eq_sub memLp_signMixture]
  simp only [id, Pi.pow_apply]
  rw [integral_signMixture (hi 1) (hi (-1)), integral_signMixture (hi1 1) (hi1 (-1)), hm, hm,
    integral_id_gaussianReal, integral_id_gaussianReal]
  norm_num

/-! ### The estimator and its characteristic function -/

/-- **The sample mean shifted by a sign.** `T_n(x) = x̄_n + n^{-1/2} s(x_0 - θ₀)`, the second
term written as a sum over the coordinates to which only the coordinate `0` contributes. -/
noncomputable def signShiftedMean (θ₀ : ℝ) (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  realSampleMean n x +
    (√(n : ℝ))⁻¹ * ∑ i : Fin n, if (i : ℕ) = 0 then stepSign (x i - θ₀) else 0

lemma measurable_signShiftedMean (θ₀ : ℝ) (n : ℕ) : Measurable (signShiftedMean θ₀ n) := by
  unfold signShiftedMean
  have h2 : Measurable fun x : Fin n → ℝ ↦
      ∑ i : Fin n, if (i : ℕ) = 0 then stepSign (x i - θ₀) else 0 := by
    refine Finset.measurable_sum _ fun i _ ↦ ?_
    split_ifs
    · exact measurable_stepSign.comp ((measurable_pi_apply i).sub_const _)
    · exact measurable_const
  exact (measurable_realSampleMean n).add (measurable_const.mul h2)

/-- The contribution `c (y - θ) + [i = 0] s(y - θ₀)` of the coordinate `i` to
`√n (T_n - θ)`, with `c = n^{-1/2}`. -/
noncomputable def signShiftedTerm (θ₀ θ c : ℝ) {n : ℕ} (i : Fin n) (y : ℝ) : ℝ :=
  c * (y - θ) + if (i : ℕ) = 0 then stepSign (y - θ₀) else 0

/-- `√n (T_n(x) - θ) = ∑ᵢ (n^{-1/2} (x_i - θ) + [i = 0] s(x_0 - θ₀))` for `n ≥ 1`. -/
lemma sqrt_mul_signShiftedMean_sub {θ₀ θ : ℝ} {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    √(n : ℝ) * (signShiftedMean θ₀ n x - θ) =
      ∑ i, signShiftedTerm θ₀ θ (√(n : ℝ))⁻¹ i (x i) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn'.le
  have hs0 : √(n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn').ne'
  simp only [signShiftedMean, signShiftedTerm, realSampleMean, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  linear_combination (∑ i, x i - (n : ℝ) * θ) * hs

/-- **The characteristic function of `√n (T_n - θ)` under `N(θ, 1)^n`**, `n = m + 1`, with
`c = n^{-1/2}`: it factorizes into the factor of the coordinate `0`,
`∫ e^{i t (c (y - θ) + s(y - θ₀))} dN(θ, 1)(y)`, and `m` Gaussian factors `e^{-(t c)²/2}`. -/
lemma integral_exp_signShiftedMean (θ₀ θ t : ℝ) (m : ℕ) :
    ∫ x, cexp (((t * (√((m + 1 : ℕ) : ℝ) * (signShiftedMean θ₀ (m + 1) x - θ)) : ℝ) : ℂ) * I)
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ gaussianReal θ 1) =
      (∫ y, cexp (((t * ((√((m + 1 : ℕ) : ℝ))⁻¹ * (y - θ) + stepSign (y - θ₀)) : ℝ) : ℂ) * I)
        ∂gaussianReal θ 1) *
        cexp ((-(t * (√((m + 1 : ℕ) : ℝ))⁻¹) ^ 2 / 2 : ℝ) : ℂ) ^ m := by
  set c := (√((m + 1 : ℕ) : ℝ))⁻¹ with hc
  have hpt : ∀ x : Fin (m + 1) → ℝ,
      cexp (((t * (√((m + 1 : ℕ) : ℝ) * (signShiftedMean θ₀ (m + 1) x - θ)) : ℝ) : ℂ) * I) =
        ∏ i, cexp (((t * signShiftedTerm θ₀ θ c i (x i) : ℝ) : ℂ) * I) := by
    intro x
    rw [sqrt_mul_signShiftedMean_sub (Nat.succ_pos m), Finset.mul_sum, ofReal_sum,
      Finset.sum_mul, Complex.exp_sum]
  simp_rw [hpt]
  rw [integral_fintype_prod_eq_prod
    (f := fun i y ↦ cexp (((t * signShiftedTerm θ₀ θ c i y : ℝ) : ℂ) * I)), Fin.prod_univ_succ]
  have hj : ∀ j : Fin m, ∫ y, cexp (((t * signShiftedTerm θ₀ θ c j.succ y : ℝ) : ℂ) * I)
      ∂gaussianReal θ 1 = cexp ((-(t * c) ^ 2 / 2 : ℝ) : ℂ) := by
    intro j
    simp only [signShiftedTerm, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte, add_zero]
    have hmap := gaussianReal_map_sub_const (μ := θ) (v := 1) θ
    rw [sub_self] at hmap
    calc ∫ y, cexp (((t * (c * (y - θ)) : ℝ) : ℂ) * I) ∂gaussianReal θ 1
        = ∫ z, cexp (((t * (c * z) : ℝ) : ℂ) * I) ∂(gaussianReal θ 1).map (· - θ) :=
          (integral_map (φ := fun y : ℝ ↦ y - θ)
            (f := fun z : ℝ ↦ cexp (((t * (c * z) : ℝ) : ℂ) * I))
            (measurable_sub_const θ).aemeasurable
            (Continuous.aestronglyMeasurable (by fun_prop))).symm
      _ = charFun (gaussianReal 0 1) (t * c) := by
          rw [hmap, charFun_apply_real]
          congr 1
          funext z
          push_cast
          ring_nf
      _ = cexp ((-(t * c) ^ 2 / 2 : ℝ) : ℂ) := by
          rw [charFun_gaussianReal]
          push_cast
          ring_nf
  simp only [hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp [signShiftedTerm]

/-! ### Regularity -/

/-- **The factor of the coordinate `0` tends to `cos t`.** Under `θ_n = θ₀ + h / √n`, with
`n = m + 1` and `c = n^{-1/2}`, `∫ e^{i t (c (y - θ_n) + s(y - θ₀))} dN(θ_n, 1)(y)` is
`∫ e^{i t (c z + s(z + h c))} dN(0, 1)(z)`, which tends to `∫ e^{i t s(z)} dN(0, 1)(z) = cos t` by
dominated convergence, since `s(z + h c) = s(z)` eventually for `z ≠ 0`. -/
lemma tendsto_integral_exp_stepSign (θ₀ h t : ℝ) :
    Tendsto (fun m : ℕ ↦ ∫ y, cexp (((t * ((√((m + 1 : ℕ) : ℝ))⁻¹ *
        (y - (θ₀ + h / √((m + 1 : ℕ) : ℝ))) + stepSign (y - θ₀)) : ℝ) : ℂ) * I)
        ∂gaussianReal (θ₀ + h / √((m + 1 : ℕ) : ℝ)) 1) atTop (𝓝 (Real.cos t : ℂ)) := by
  have hs := measurable_stepSign
  let c : ℕ → ℝ := fun m ↦ (√((m + 1 : ℕ) : ℝ))⁻¹
  have hc0 : Tendsto c atTop (𝓝 0) := tendsto_inv_sqrt_natCast.comp (tendsto_add_atTop_nat 1)
  have hδ : Tendsto (fun m ↦ h * c m) atTop (𝓝 0) := by simpa using hc0.const_mul h
  have hrw : ∀ m : ℕ, ∫ y, cexp (((t * ((√((m + 1 : ℕ) : ℝ))⁻¹ *
        (y - (θ₀ + h / √((m + 1 : ℕ) : ℝ))) + stepSign (y - θ₀)) : ℝ) : ℂ) * I)
        ∂gaussianReal (θ₀ + h / √((m + 1 : ℕ) : ℝ)) 1 =
      ∫ z, cexp ((((t * (c m * z + stepSign (z + h * c m))) : ℝ) : ℂ) * I) ∂gaussianReal 0 1 := by
    intro m
    have hmap := gaussianReal_map_add_const (μ := (0 : ℝ)) (v := 1)
      (θ₀ + h / √((m + 1 : ℕ) : ℝ))
    rw [zero_add] at hmap
    rw [← hmap, integral_map (measurable_add_const _).aemeasurable
      (Measurable.aestronglyMeasurable (by fun_prop))]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    dsimp only
    rw [show z + (θ₀ + h / √((m + 1 : ℕ) : ℝ)) - (θ₀ + h / √((m + 1 : ℕ) : ℝ)) = z by ring,
      show z + (θ₀ + h / √((m + 1 : ℕ) : ℝ)) - θ₀ = z + h * c m by simp only [c]; ring]
  simp_rw [hrw]
  rw [← integral_exp_stepSign_gaussianReal t]
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ 1)
    (fun m ↦ Measurable.aestronglyMeasurable (by fun_prop)) (integrable_const 1)
    (fun m ↦ Eventually.of_forall fun z ↦ by rw [norm_exp_ofReal_mul_I]) ?_
  filter_upwards [ae_ne_zero_gaussianReal_zero_one] with z hz
  have hev : ∀ᶠ m in atTop, stepSign (z + h * c m) = stepSign z := by
    have hz' : Tendsto (fun m ↦ z + h * c m) atTop (𝓝 z) := by
      simpa using (tendsto_const_nhds (x := z)).add hδ
    rcases lt_or_gt_of_ne hz with hneg | hpos
    · filter_upwards [hz'.eventually (gt_mem_nhds (show z < 0 / 2 by simpa using hneg))]
        with m hm
      have hm' : z + h * c m ≤ 0 := by linarith
      simp [stepSign, not_lt.2 hm', not_lt.2 hneg.le]
    · filter_upwards [hz'.eventually (lt_mem_nhds hpos)] with m hm
      simp [stepSign, hm, hpos]
  have hcont : Continuous fun u : ℝ ↦ cexp ((((t * (u * z + stepSign z)) : ℝ) : ℂ) * I) := by
    fun_prop
  have hlim := (hcont.tendsto 0).comp hc0
  simp only [zero_mul, zero_add] at hlim
  refine hlim.congr' (hev.mono fun m hm ↦ ?_)
  simp only [Function.comp_apply, hm]

/-- **The estimator is regular at `θ₀` with the mixture as limit law.** For every local
parameter `h`, the characteristic function of `√n (T_n - θ_n)` under `N(θ_n, 1)^n` is the
coordinate `0` factor times `e^{-t² (n - 1) / (2 n)}`; it tends to `cos t · e^{-t²/2}`, the
characteristic function of `L`, and Lévy's continuity theorem gives weak convergence to `L`. -/
theorem signShiftedMean_isHajekRegular (θ₀ : ℝ) :
    normalLocation.IsHajekRegular (signShiftedMean θ₀) θ₀ signMixture := by
  refine ⟨measurable_signShiftedMean θ₀, fun h f ↦ ?_⟩
  have hg : ∀ n : ℕ, Measurable fun x : Fin n → ℝ ↦
      √(n : ℝ) * (signShiftedMean θ₀ n x - (θ₀ + h / √(n : ℝ))) :=
    fun n ↦ measurable_const.mul ((measurable_signShiftedMean θ₀ n).sub_const _)
  let ν : ℕ → Measure ℝ := fun n ↦
    (Measure.pi fun _ : Fin n ↦ gaussianReal (θ₀ + h / √(n : ℝ)) 1).map
      fun x ↦ √(n : ℝ) * (signShiftedMean θ₀ n x - (θ₀ + h / √(n : ℝ)))
  have hν : ∀ᶠ n in atTop, IsProbabilityMeasure (ν n) :=
    Eventually.of_forall fun n ↦ by dsimp only [ν]; infer_instance
  have hlaw : ∀ n : ℕ, (normalLocation.pi n).law (θ₀ + h / √(n : ℝ)) =
      Measure.pi fun _ : Fin n ↦ gaussianReal (θ₀ + h / √(n : ℝ)) 1 := fun n ↦ by
    rw [pi_law n (Set.mem_univ _), normalLocation_law]
  have hB : ∀ t : ℝ, ∀ m : ℕ, cexp ((-(t * (√((m + 1 : ℕ) : ℝ))⁻¹) ^ 2 / 2 : ℝ) : ℂ) ^ m =
      cexp ((-(t ^ 2 / 2) * ((m : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) := by
    intro t m
    rw [← Complex.exp_nat_mul]
    congr 1
    have hsq : (√((m + 1 : ℕ) : ℝ))⁻¹ ^ 2 = ((m : ℝ) + 1)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_succ]
    rw [← ofReal_natCast, ← ofReal_mul]
    congr 1
    rw [mul_pow, hsq]
    field_simp
  have hchar : ∀ t, Tendsto (fun n ↦ charFun (ν n) t) atTop (𝓝 (charFun signMixture t)) := by
    intro t
    rw [← tendsto_add_atTop_iff_nat 1, charFun_signMixture, mul_comm]
    have he : ∀ m : ℕ, charFun (ν (m + 1)) t =
        (∫ y, cexp (((t * ((√((m + 1 : ℕ) : ℝ))⁻¹ *
          (y - (θ₀ + h / √((m + 1 : ℕ) : ℝ))) + stepSign (y - θ₀)) : ℝ) : ℂ) * I)
          ∂gaussianReal (θ₀ + h / √((m + 1 : ℕ) : ℝ)) 1) *
        cexp ((-(t ^ 2 / 2) * ((m : ℝ) / ((m : ℝ) + 1)) : ℝ) : ℂ) := by
      intro m
      rw [← hB, ← integral_exp_signShiftedMean, charFun_apply_real,
        integral_map (hg _).aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      push_cast
      ring_nf
    simp_rw [he]
    refine (tendsto_integral_exp_stepSign θ₀ h t).mul ?_
    rw [show cexp (-(t : ℂ) ^ 2 / 2) = cexp ((-(t ^ 2 / 2) * 1 : ℝ) : ℂ) by
      congr 1; push_cast; ring]
    have hc : Continuous fun u : ℝ ↦ cexp ((-(t ^ 2 / 2) * u : ℝ) : ℂ) := by fun_prop
    exact (hc.tendsto 1).comp (tendsto_natCast_div_add_atTop (1 : ℝ))
  have key := (tendsto_integral_iff_tendsto_charFun hν).2 hchar f
  refine key.congr fun n ↦ ?_
  rw [integral_map (hg n).aemeasurable f.continuous.aestronglyMeasurable, hlaw]

/-- **The estimator has no Gaussian limit law**: it is not regular at `θ₀` with limit `N(m, V)`
for any `m` and `V`, since weak limits are unique and the mixture is not Gaussian. In particular
`hajek_convolution_bound`, which needs the limit `N(0, V)`, does not apply to it. -/
theorem signShiftedMean_not_isHajekRegular_gaussian (θ₀ m : ℝ) (V : ℝ≥0) :
    ¬ normalLocation.IsHajekRegular (signShiftedMean θ₀) θ₀ (gaussianReal m V) := by
  intro hG
  have hT := signShiftedMean_isHajekRegular θ₀
  refine signMixture_ne_gaussianReal m V (ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_)
  exact tendsto_nhds_unique (hT.tendsto 0 f) (hG.tendsto 0 f)

/-- **The general bound for the estimator with a non Gaussian limit.** In the normal location
family every hypothesis of `hajek_convolution_bound_general` holds at `θ₀` for `T`, and the bound
reads `I(θ₀)⁻¹ = 1 ≤ 2 = Var(L)`. -/
theorem signShiftedMean_convolution_bound (θ₀ : ℝ) :
    (normalLocation.fisherInfo θ₀)⁻¹ ≤ Var[id; signMixture] ∧
      (normalLocation.fisherInfo θ₀)⁻¹ = 1 ∧ Var[id; signMixture] = 2 :=
  ⟨hajek_convolution_bound_general (normalLocation_isRegularAt θ₀)
    (normalLocation_isScoreRegular θ₀ one_pos)
    ((normalLocation_isSmoothOnBall θ₀ 2).ae_hasDerivAt_logLik one_lt_two)
    (by rw [normalLocation_fisherInfo]; exact one_pos) (signShiftedMean_isHajekRegular θ₀)
    memLp_signMixture, by rw [normalLocation_fisherInfo, inv_one], variance_signMixture⟩

/-- **The Gaussian instance through the general bound.** The sample mean in the normal location
family is regular with limit `N(0, 1)`, which has a finite second moment, and the general bound
holds with equality: `I(θ₀)⁻¹ = 1 = Var(N(0, 1))`. -/
theorem realSampleMean_convolution_bound_general (θ₀ : ℝ) :
    (normalLocation.fisherInfo θ₀)⁻¹ ≤ Var[id; gaussianReal 0 1] ∧
      (normalLocation.fisherInfo θ₀)⁻¹ = Var[id; gaussianReal 0 1] :=
  ⟨hajek_convolution_bound_general (normalLocation_isRegularAt θ₀)
    (normalLocation_isScoreRegular θ₀ one_pos)
    ((normalLocation_isSmoothOnBall θ₀ 2).ae_hasDerivAt_logLik one_lt_two)
    (by rw [normalLocation_fisherInfo]; exact one_pos) (realSampleMean_isHajekRegular θ₀)
    (memLp_id_gaussianReal 2), by
    rw [normalLocation_fisherInfo, inv_one, variance_id_gaussianReal, NNReal.coe_one]⟩

end ParametricFamily

end CausalInference
