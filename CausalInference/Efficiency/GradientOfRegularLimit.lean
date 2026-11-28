/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.HajekConvolution
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Exponential tilts of a bivariate Gaussian limit

The limit theory behind the gradient of a regular estimator. Under the null law, the pair
`(√n (T_n - ψ), S_n)` of a centered asymptotically linear estimator and a normalized score sum
has subsequential joint limits `ρ` on `ℝ × ℝ`; every linear combination `a X + b Z` has a
Gaussian limit, so `ρ` is a Gaussian measure (`isGaussian_of_map_linear`).
For a Gaussian `ρ` with marginals `N(0, V)` and `N(0, I)` the exponential tilt
`e^{h z - h² I / 2} dρ(x, z)`, seen through `x`, is the shift of `N(0, V)` by `h c`, where
`c = ∫ x z dρ` is the covariance (`integral_mul_exp_of_isGaussian`). Decorrelating,
`x - (c / I) z` is independent of `z` (`HasGaussianLaw.indepFun_of_covariance_eq_zero`), and the
tilt moves `z` from `N(0, I)` to `N(h I, I)` (`integral_mul_exp_gaussianReal`).

## Main definitions

None; the file proves facts about Gaussian measures on `ℝ × ℝ`.

## Main results

* `integral_mul_exp_of_isGaussian`: `∫ f(x) e^{h z - h² I / 2} dρ = ∫ f(x + h c) dN(0, V)`.
* `isGaussian_of_map_linear`: a law all of whose linear images are centered Gaussian is
  Gaussian.
* `integral_fst_mul_snd_of_map_add`: its covariance from the law of the sum.
* `integral_exp_tilt_gaussianReal`: the tilt `e^{h z - h² I / 2}` has mass one under `N(0, I)`.
* `eq_zero_of_integral_add_gaussianReal`: a shift `m` with `N(m, V) = N(0, V)` is `0`.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998).
* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, third edition, Wiley
  (2003).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace CausalInference
namespace Efficiency

section GaussianTilt

variable {ρ : Measure (ℝ × ℝ)}

/-- The second moment of a coordinate with law `N(0, v)`. -/
theorem integral_fst_sq_of_map {v : ℝ≥0} (hX : ρ.map Prod.fst = gaussianReal 0 v) :
    ∫ p, p.1 ^ 2 ∂ρ = v := by
  rw [← integral_sq_gaussianReal v, ← hX, integral_map measurable_fst.aemeasurable
    (by fun_prop)]

theorem integral_snd_sq_of_map {v : ℝ≥0} (hZ : ρ.map Prod.snd = gaussianReal 0 v) :
    ∫ p, p.2 ^ 2 ∂ρ = v := by
  rw [← integral_sq_gaussianReal v, ← hZ, integral_map measurable_snd.aemeasurable
    (by fun_prop)]

theorem integral_fst_of_map {v : ℝ≥0} (hX : ρ.map Prod.fst = gaussianReal 0 v) :
    ∫ p, p.1 ∂ρ = 0 := by
  rw [← integral_id_gaussianReal (μ := 0) (v := v), ← hX,
    integral_map measurable_fst.aemeasurable (by fun_prop)]

theorem integral_snd_of_map {v : ℝ≥0} (hZ : ρ.map Prod.snd = gaussianReal 0 v) :
    ∫ p, p.2 ∂ρ = 0 := by
  rw [← integral_id_gaussianReal (μ := 0) (v := v), ← hZ,
    integral_map measurable_snd.aemeasurable (by fun_prop)]

theorem integrable_fst_of_map {v : ℝ≥0} (hX : ρ.map Prod.fst = gaussianReal 0 v) :
    Integrable (fun p : ℝ × ℝ ↦ p.1) ρ :=
  integrable_comp_fst_of_map hX (g := id)
    ((memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl)

theorem integrable_snd_of_map {v : ℝ≥0} (hZ : ρ.map Prod.snd = gaussianReal 0 v) :
    Integrable (fun p : ℝ × ℝ ↦ p.2) ρ :=
  integrable_comp_snd_of_map hZ (g := id)
    ((memLp_id_gaussianReal (μ := 0) (v := v) 1).integrable le_rfl)

/-- The tilt `e^{h z - h² I / 2}` is integrable under `N(0, I)`. -/
theorem integrable_exp_tilt_gaussianReal (h I : ℝ) (v : ℝ≥0) :
    Integrable (fun z ↦ Real.exp (h * z - h ^ 2 * I / 2)) (gaussianReal 0 v) := by
  refine ((integrable_exp_mul_gaussianReal h).div_const (Real.exp (h ^ 2 * I / 2))).congr
    (Eventually.of_forall fun z ↦ ?_)
  simp only [Real.exp_sub]

/-- **The exponential tilt of a bivariate Gaussian law.** Let `ρ` be a Gaussian measure on
`ℝ × ℝ` with marginals `N(0, V)` and `N(0, I)`, `I ≥ 0`, and covariance `c = ∫ x z dρ`. Then for
every `h` and bounded continuous `f`,
`∫ f(x) e^{h z - h² I / 2} dρ(x, z) = ∫ f(x + h c) dN(0, V)`: the tilt shifts the first
coordinate by `h c`. For `I > 0`, `x - (c / I) z` is uncorrelated with `z`, hence independent of
it, and the tilt in `z` alone is the Gaussian shift identity `integral_mul_exp_gaussianReal`; for
`I = 0`, `z = 0` almost surely and `c = 0`. -/
theorem integral_mul_exp_of_isGaussian [IsGaussian ρ] {V : ℝ≥0} {I : ℝ} (hI : 0 ≤ I)
    (hX : ρ.map Prod.fst = gaussianReal 0 V) (hZ : ρ.map Prod.snd = gaussianReal 0 I.toNNReal)
    (h : ℝ) (f : ℝ →ᵇ ℝ) :
    ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂ρ =
      ∫ x, f (x + h * ∫ p, p.1 * p.2 ∂ρ) ∂gaussianReal 0 V := by
  set c := ∫ p, p.1 * p.2 ∂ρ with hc
  rcases hI.eq_or_lt with hI0 | hIpos
  · -- a degenerate score: `z = 0` almost surely
    have hz : ∀ᵐ p ∂ρ, p.2 = 0 := by
      have : ∀ᵐ z ∂(ρ.map Prod.snd), z = 0 := by
        rw [hZ, ← hI0, Real.toNNReal_zero, gaussianReal_zero_var, ae_dirac_eq]
        exact Filter.eventually_pure.2 rfl
      exact ae_of_ae_map measurable_snd.aemeasurable this
    have hc0 : c = 0 := integral_eq_zero_of_ae (hz.mono fun p hp ↦ by simp [hp])
    rw [hc0, integral_congr_ae (hz.mono fun p hp ↦ (by simp [hp, ← hI0] :
      f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) = f p.1)), ← hX]
    simp only [mul_zero, add_zero]
    exact (integral_map measurable_fst.aemeasurable f.continuous.aestronglyMeasurable).symm
  -- decorrelate
  set k := c / I with hk
  have hkI : k * I = c := by rw [hk]; field_simp
  let M : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ - k • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hM : ∀ p : ℝ × ℝ, M p = (p.1 - k * p.2, p.2) := fun p ↦ by simp [M]
  have hMm : Measurable M := M.continuous.measurable
  have hx := integrable_fst_of_map hX
  have hz := integrable_snd_of_map hZ
  have hxz := integrable_fst_mul_snd hX hZ
  have hz2 := integrable_sq_snd hZ
  have hz2v : ∫ p, p.2 ^ 2 ∂ρ = I := by
    rw [integral_snd_sq_of_map hZ, Real.coe_toNNReal _ hI]
  have hm1 : ∫ q, q.1 ∂(ρ.map M) = 0 := by
    rw [integral_map hMm.aemeasurable (by fun_prop)]
    simp only [hM]
    rw [integral_sub hx (hz.const_mul k), integral_const_mul, integral_fst_of_map hX,
      integral_snd_of_map hZ]
    ring
  have hm2 : ∫ q, q.2 ∂(ρ.map M) = 0 := by
    rw [integral_map hMm.aemeasurable (by fun_prop)]
    simp only [hM]
    exact integral_snd_of_map hZ
  have hcov : cov[Prod.fst, Prod.snd; ρ.map M] = 0 := by
    rw [covariance]
    change ∫ q, (q.1 - ∫ q, q.1 ∂(ρ.map M)) * (q.2 - ∫ q, q.2 ∂(ρ.map M)) ∂(ρ.map M) = 0
    rw [hm1, hm2, integral_map hMm.aemeasurable (by fun_prop)]
    simp only [hM, sub_zero]
    have e : ∀ p : ℝ × ℝ, (p.1 - k * p.2) * p.2 = p.1 * p.2 - k * p.2 ^ 2 := fun p ↦ by ring
    simp only [e]
    rw [integral_sub hxz (hz2.const_mul k), integral_const_mul, hz2v, hkI, hc, sub_self]
  have hind : IndepFun Prod.fst Prod.snd (ρ.map M) :=
    HasGaussianLaw.indepFun_of_covariance_eq_zero ⟨aemeasurable_id, by
      rw [show (fun ω : ℝ × ℝ ↦ (ω.1, ω.2)) = id from rfl, Measure.map_id]; infer_instance⟩ hcov
  have hprod : ρ.map M = ((ρ.map M).map Prod.fst).prod ((ρ.map M).map Prod.snd) := by
    have := (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
      measurable_snd.aemeasurable).1 hind
    rwa [show (fun ω : ℝ × ℝ ↦ (ω.1, ω.2)) = id from rfl, Measure.map_id] at this
  have hsnd : (ρ.map M).map Prod.snd = gaussianReal 0 I.toNNReal := by
    rw [Measure.map_map measurable_snd hMm]
    exact hZ
  set R := (ρ.map M).map Prod.fst with hR
  rw [hsnd] at hprod
  set N := gaussianReal 0 I.toNNReal with hN
  have hv : I.toNNReal ≠ 0 := by simpa using hIpos
  have hE := integrable_exp_tilt_gaussianReal h I I.toNNReal
  have hint1 : Integrable (fun q : ℝ × ℝ ↦ f (q.1 + k * q.2) *
      Real.exp (h * q.2 - h ^ 2 * I / 2)) (R.prod N) := by
    refine ((integrable_const (‖f‖)).mul_prod hE).mono'
      ((f.continuous.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun q ↦ ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (Real.exp_pos _).le
  have hint2 : Integrable (fun q : ℝ × ℝ ↦ f (q.1 + k * q.2 + h * c)) (R.prod N) :=
    Integrable.of_bound (f.continuous.comp (by fun_prop)).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun q ↦ f.norm_coe_le_norm _)
  calc ∫ p, f p.1 * Real.exp (h * p.2 - h ^ 2 * I / 2) ∂ρ
      = ∫ q, f (q.1 + k * q.2) * Real.exp (h * q.2 - h ^ 2 * I / 2) ∂(ρ.map M) := by
        rw [integral_map (f := fun q : ℝ × ℝ ↦ f (q.1 + k * q.2) *
          Real.exp (h * q.2 - h ^ 2 * I / 2)) hMm.aemeasurable
          ((f.continuous.comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable]
        simp only [hM, sub_add_cancel]
    _ = ∫ r, ∫ z, f (r + k * z) * Real.exp (h * z - h ^ 2 * I / 2) ∂N ∂R := by
        rw [hprod, integral_prod _ hint1]
    _ = ∫ r, ∫ z, f (r + k * z + h * c) ∂N ∂R := by
        refine integral_congr_ae (Eventually.of_forall fun r ↦ ?_)
        have e := integral_mul_exp_gaussianReal hv h (f := fun z ↦ f (r + k * z))
          (f.continuous.comp (by fun_prop)).measurable
        rw [Real.coe_toNNReal _ hI] at e
        simp only
        rw [e]
        refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
        simp only
        rw [← hkI]
        ring_nf
    _ = ∫ q, f (q.1 + k * q.2 + h * c) ∂(ρ.map M) := by
        rw [hprod, integral_prod _ hint2]
    _ = ∫ p, f (p.1 + h * c) ∂ρ := by
        rw [integral_map (f := fun q : ℝ × ℝ ↦ f (q.1 + k * q.2 + h * c)) hMm.aemeasurable
          (f.continuous.comp (by fun_prop)).aestronglyMeasurable]
        simp only [hM, sub_add_cancel]
    _ = ∫ x, f (x + h * c) ∂gaussianReal 0 V := by
        rw [← hX, integral_map (f := fun x : ℝ ↦ f (x + h * c)) measurable_fst.aemeasurable
          (f.continuous.comp (by fun_prop)).aestronglyMeasurable]

/-- The tilt `e^{h z - h² I / 2}` has mass one under `N(0, I)`, also for `I = 0`. -/
theorem integral_exp_tilt_gaussianReal (h : ℝ) {I : ℝ} (hI : 0 ≤ I) :
    ∫ z, Real.exp (h * z - h ^ 2 * I / 2) ∂gaussianReal 0 I.toNNReal = 1 := by
  have hm := congrFun (mgf_id_gaussianReal (μ := 0) (v := I.toNNReal)) h
  simp only [mgf, id, Real.coe_toNNReal _ hI, zero_mul, zero_add] at hm
  simp_rw [Real.exp_sub]
  rw [integral_div, show ∫ z, Real.exp (h * z) ∂gaussianReal 0 I.toNNReal =
    ∫ z, Real.exp (h * z) ∂gaussianReal 0 I.toNNReal from rfl]
  rw [show (∫ z, Real.exp (h * z) ∂gaussianReal 0 I.toNNReal) = Real.exp (I * h ^ 2 / 2) by
    rw [← hm]]
  rw [show h ^ 2 * I / 2 = I * h ^ 2 / 2 by ring, div_self (Real.exp_pos _).ne']

/-- **A law on `ℝ × ℝ` all of whose linear images are centered Gaussian is Gaussian.** -/
theorem isGaussian_of_map_linear
    (hlin : ∀ a b : ℝ, ∃ v : ℝ≥0, ρ.map (fun p ↦ a * p.1 + b * p.2) = gaussianReal 0 v) :
    IsGaussian ρ := by
  refine isGaussian_of_map_eq_gaussianReal fun L ↦ ?_
  obtain ⟨v, hv⟩ := hlin (L (1, 0)) (L (0, 1))
  refine ⟨0, v, ?_⟩
  have e : (L : ℝ × ℝ → ℝ) = fun p ↦ L (1, 0) * p.1 + L (0, 1) * p.2 := by
    funext p
    have hp : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm p.1, mul_comm p.2]
  rw [e, hv]

/-- **The covariance from the law of the sum.** If `ρ` has marginals `N(0, V)` and `N(0, I)` and
`x + z` has law `N(0, W)` under `ρ`, then `∫ x z dρ = (W - V - I) / 2`. -/
theorem integral_fst_mul_snd_of_map_add {V I W : ℝ≥0} (hX : ρ.map Prod.fst = gaussianReal 0 V)
    (hZ : ρ.map Prod.snd = gaussianReal 0 I)
    (hW : ρ.map (fun p ↦ p.1 + p.2) = gaussianReal 0 W) :
    ∫ p, p.1 * p.2 ∂ρ = ((W : ℝ) - V - I) / 2 := by
  have hW2 : ∫ p, (p.1 + p.2) ^ 2 ∂ρ = W := by
    rw [← integral_sq_gaussianReal W, ← hW,
      integral_map (by fun_prop) (by fun_prop)]
  have e : ∀ p : ℝ × ℝ, (p.1 + p.2) ^ 2 = p.1 ^ 2 + 2 * (p.1 * p.2) + p.2 ^ 2 := fun p ↦ by ring
  simp only [e] at hW2
  have i1 : Integrable (fun p : ℝ × ℝ ↦ p.1 ^ 2) ρ := integrable_sq_fst hX
  have i2 : Integrable (fun p : ℝ × ℝ ↦ 2 * (p.1 * p.2)) ρ :=
    (integrable_fst_mul_snd hX hZ).const_mul 2
  have i3 : Integrable (fun p : ℝ × ℝ ↦ p.2 ^ 2) ρ := integrable_sq_snd hZ
  have s1 := integral_add (i1.add i2) i3
  have s2 := integral_add i1 i2
  simp only [Pi.add_apply] at s1 s2
  rw [s1, s2, integral_const_mul, integral_fst_sq_of_map hX, integral_snd_sq_of_map hZ] at hW2
  linarith

/-- **A Gaussian law determines its mean.** If shifting by `m` leaves the integrals of all
bounded continuous functions under `N(0, V)` unchanged, then `m = 0`. -/
theorem eq_zero_of_integral_add_gaussianReal {V : ℝ≥0} {m : ℝ}
    (h : ∀ f : ℝ →ᵇ ℝ, ∫ x, f (x + m) ∂gaussianReal 0 V = ∫ x, f x ∂gaussianReal 0 V) :
    m = 0 := by
  have hmeq : (gaussianReal 0 V).map (· + m) = gaussianReal 0 V := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
    rw [integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
    exact h f
  rw [gaussianReal_map_add_const, zero_add, gaussianReal_ext_iff] at hmeq
  exact hmeq.1

end GaussianTilt

end Efficiency
end CausalInference
