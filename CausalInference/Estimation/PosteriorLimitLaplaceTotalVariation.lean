/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.PosteriorLimitLaplaceCore
public import CausalInference.Estimation.PosteriorLimitTotalVariation

/-!
# Total variation between a posterior and its normal approximation

**The posterior.** For a reference measure `ρ` on the parameter space, a prior density `π` and a
likelihood `L` (nonnegative functions), the posterior is the prior `π ρ` reweighted by `L` and
normalized (`densityPosterior`):

  `Π = (∫ L d(π ρ))⁻¹ · (π ρ).withDensity L`,

the form in which `normalLocationPosterior_eq` states the posterior of the normal location model.
When `0 < ∫ π L dρ < ∞` it is the probability law with density `π L / ∫ π L`
(`densityPosterior_eq_withDensity`). It is stated as this normalized density, not as Mathlib's
posterior kernel `ProbabilityTheory.posterior`: that kernel is the disintegration of the joint
law and is determined only almost everywhere under the marginal law of the data, while here the
posterior is needed at every data value.

**The bound** (`tvDist_densityPosterior_gaussian_le`). Let the log likelihood `ℓ` be concave on
`ℝ^p` with the quadratic expansion `|ℓ(m + u) - ℓ(m) + (n/2) uᵀMu| ≤ η n ‖u‖²` on `‖u‖ ≤ δ`,
where `M` is positive definite with `λ‖u‖² ≤ uᵀMu` and `0 ≤ η ≤ λ/4`, and let the prior density
`π` be integrable with `∫ π > 0`, vary by at most `o` on the ball of radius `δ` around `m`, and
be positive at `θ₀`. Then the posterior of the likelihood `e^ℓ` satisfies

  `‖Π - N(m, n⁻¹ M⁻¹)‖ ≤ (2K/π(θ₀)) [(o + 8π(θ₀)η/λ) G(λ/8)
      + e^{-nλδ²/4} ((√n)^p ∫π + π(θ₀) G(λ/4))]`,

with `K = (2π)^{-p/2} √det M` and `G(b) = (π/b)^{p/2}`. The proof normalizes both densities by
Scheffé's argument (`integral_abs_div_sub_div_le`) and applies the Laplace estimate
`integral_abs_mul_exp_sub_gaussian_le`.

**How it tends to zero.** The second term is `C n^{p/2} e^{-nλδ²/4} + C' e^{-nλδ²/4}` for fixed
`δ` and tends to `0` as `n → ∞`. The first term does not depend on `n`; it is small when the
radius `δ` is small, because then the oscillation `o` of the prior near a point of continuity is
small and the expansion error `η` is small. In the applications `δ` and `η` are fixed first from
the target accuracy and then `n` is taken large.

**Change of parameter.** `IsBernsteinVonMises.map_continuousLinearEquiv` transports the
Bernstein and von Mises conclusion along a continuous linear isomorphism of parameter spaces,
for example from `EuclideanSpace ℝ ι` to `ι → ℝ`; `map_densityPosterior` transports the
posterior along a measurable isomorphism.

## Main definitions

* `PosteriorLimit.densityPosterior`.

## Main results

* `densityPosterior_eq_withDensity`, `isProbabilityMeasure_densityPosterior`,
  `map_densityPosterior`.
* `integral_abs_div_sub_div_le`, `tvDist_densityPosterior_gaussian_le`.
* `IsBernsteinVonMises.map_continuousLinearEquiv`.

## References

* H. Scheffé (1947), *A useful convergence theorem for probability distributions*, Annals of
  Mathematical Statistics 18.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), chapter 10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open scoped ENNReal NNReal

namespace CausalInference

namespace PosteriorLimit

/-! ### The posterior of a prior with a density -/

section Posterior

variable {Θ : Type*} [MeasurableSpace Θ]

/-- The **posterior** of the prior `π ρ` (density `π` against the reference measure `ρ`) under the
likelihood `L`: the prior reweighted by `L` and normalized,
`(∫ L d(π ρ))⁻¹ · (π ρ).withDensity L`. -/
noncomputable def densityPosterior (ρ : Measure Θ) (p L : Θ → ℝ) : Measure Θ :=
  (∫⁻ θ, ENNReal.ofReal (L θ) ∂ρ.withDensity fun θ ↦ ENNReal.ofReal (p θ))⁻¹ •
    (ρ.withDensity fun θ ↦ ENNReal.ofReal (p θ)).withDensity fun θ ↦ ENNReal.ofReal (L θ)

variable {ρ : Measure Θ} {p L : Θ → ℝ}

/-- **The posterior is the normalized density.** If the prior density and the likelihood are
measurable and nonnegative, and `π L` is integrable with positive integral, the posterior has
density `π L / ∫ π L`. -/
theorem densityPosterior_eq_withDensity (hpm : Measurable p) (hp0 : ∀ θ, 0 ≤ p θ)
    (hLm : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) (hpi : Integrable (fun θ ↦ p θ * L θ) ρ)
    (hZ : 0 < ∫ θ, p θ * L θ ∂ρ) :
    densityPosterior ρ p L =
      ρ.withDensity fun θ ↦ ENNReal.ofReal (p θ * L θ / ∫ θ', p θ' * L θ' ∂ρ) := by
  unfold densityPosterior
  have hc : ∫⁻ θ, ENNReal.ofReal (L θ) ∂(ρ.withDensity fun θ ↦ ENNReal.ofReal (p θ)) =
      ENNReal.ofReal (∫ θ, p θ * L θ ∂ρ) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hpm.ennreal_ofReal hLm.ennreal_ofReal,
      ofReal_integral_eq_lintegral_ofReal hpi (ae_of_all _ fun θ ↦ mul_nonneg (hp0 θ) (hL0 θ))]
    congr 1
    funext θ
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (hp0 θ)]
  rw [hc, ← withDensity_mul _ hpm.ennreal_ofReal hLm.ennreal_ofReal,
    ← withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne')]
  congr 1
  funext θ
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hZ, ENNReal.ofReal_mul (hp0 θ), div_eq_mul_inv, mul_comm]

/-- **The posterior is a probability law** when `π L` is integrable with positive integral. -/
theorem isProbabilityMeasure_densityPosterior (hpm : Measurable p) (hp0 : ∀ θ, 0 ≤ p θ)
    (hLm : Measurable L) (hL0 : ∀ θ, 0 ≤ L θ) (hpi : Integrable (fun θ ↦ p θ * L θ) ρ)
    (hZ : 0 < ∫ θ, p θ * L θ ∂ρ) : IsProbabilityMeasure (densityPosterior ρ p L) := by
  rw [densityPosterior_eq_withDensity hpm hp0 hLm hL0 hpi hZ]
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hpi.div_const _)
      (ae_of_all _ fun θ ↦ div_nonneg (mul_nonneg (hp0 θ) (hL0 θ)) hZ.le),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]

/-- **The posterior under a change of parameter.** For a measurable isomorphism `e`, the image of
the posterior is the posterior for the image reference measure, with the prior density and the
likelihood read through `e⁻¹`. -/
theorem map_densityPosterior {Θ' : Type*} [MeasurableSpace Θ'] (e : Θ ≃ᵐ Θ')
    (hpm : Measurable p) (hLm : Measurable L) :
    (densityPosterior ρ p L).map e = densityPosterior (ρ.map e) (p ∘ e.symm) (L ∘ e.symm) := by
  unfold densityPosterior
  rw [Measure.map_smul, map_withDensity_of_measurableEquiv _ e hLm.ennreal_ofReal,
    map_withDensity_of_measurableEquiv _ e hpm.ennreal_ofReal]
  · congr 2
    rw [show (fun θ ↦ ENNReal.ofReal ((p ∘ e.symm) θ)) = (fun θ ↦ ENNReal.ofReal (p θ)) ∘ e.symm
      from rfl, ← map_withDensity_of_measurableEquiv _ e hpm.ennreal_ofReal, lintegral_map_equiv]
    simp
  · exact e.measurable.aemeasurable

end Posterior

/-! ### Normalizing two densities -/

section Normalize

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- **Normalizing two densities.** For nonnegative integrable `g, G` with `a = ∫ g > 0` and
`b = ∫ G > 0`, `∫ |g/a - G/b| ≤ 2 ∫ |g - G| / b`. -/
lemma integral_abs_div_sub_div_le {g G : E → ℝ} (hg : Integrable g μ) (hG : Integrable G μ)
    (hg0 : ∀ x, 0 ≤ g x) (ha : 0 < ∫ x, g x ∂μ) (hb : 0 < ∫ x, G x ∂μ) :
    ∫ x, |g x / (∫ y, g y ∂μ) - G x / (∫ y, G y ∂μ)| ∂μ ≤
      2 * (∫ x, |g x - G x| ∂μ) / ∫ y, G y ∂μ := by
  set a := ∫ y, g y ∂μ with hadef
  set b := ∫ y, G y ∂μ with hbdef
  have hab : |b - a| ≤ ∫ x, |g x - G x| ∂μ := by
    rw [abs_sub_comm, hadef, hbdef, ← integral_sub hg hG]
    exact abs_integral_le_integral_abs
  have hpt : ∀ x, |g x / a - G x / b| ≤ g x * (|b - a| / (a * b)) + |g x - G x| / b := by
    intro x
    have h : g x / a - G x / b = g x * ((b - a) / (a * b)) + (g x - G x) / b := by
      field_simp
      ring
    rw [h]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_div, abs_div, abs_of_nonneg (hg0 x), abs_of_pos (mul_pos ha hb),
      abs_of_pos hb]
  have hi1 : Integrable (fun x ↦ g x * (|b - a| / (a * b))) μ := hg.mul_const _
  have hi2 : Integrable (fun x ↦ |g x - G x| / b) μ := (hg.sub hG).abs.div_const _
  have hm : Integrable (fun x ↦ |g x / a - G x / b|) μ :=
    ((hg.div_const _).sub (hG.div_const _)).abs
  calc ∫ x, |g x / a - G x / b| ∂μ
      ≤ ∫ x, (g x * (|b - a| / (a * b)) + |g x - G x| / b) ∂μ :=
        integral_mono hm (hi1.add hi2) hpt
    _ = a * (|b - a| / (a * b)) + (∫ x, |g x - G x| ∂μ) / b := by
        rw [integral_add hi1 hi2, integral_mul_const, integral_div]
    _ = |b - a| / b + (∫ x, |g x - G x| ∂μ) / b := by
        field_simp
    _ ≤ 2 * (∫ x, |g x - G x| ∂μ) / b := by
        rw [← add_div, two_mul]
        exact div_le_div_of_nonneg_right (by linarith) hb.le

end Normalize

/-! ### The total variation bound -/

section Bound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The deterministic Bernstein and von Mises bound.** Let the log likelihood `ℓ` be concave on
`ℝ^p` with `|ℓ(m + u) - ℓ(m) + (n/2) uᵀMu| ≤ η n ‖u‖²` for `‖u‖ ≤ δ`, where `M` is positive
definite, `λ‖u‖² ≤ uᵀMu` with `λ > 0`, `0 ≤ η ≤ λ/4` and `n, δ > 0`. Let the prior density `π` be
measurable, nonnegative and integrable with `∫ π > 0`, positive at `θ₀`, and vary by at most `o`
on the ball of radius `δ` around `m`. Then the total variation distance between the posterior of
the likelihood `e^ℓ` and `N(m, n⁻¹ M⁻¹)` is at most
`(2K/π(θ₀)) [(o + 8π(θ₀)η/λ) G(λ/8) + e^{-nλδ²/4} ((√n)^p ∫π + π(θ₀) G(λ/4))]`, with
`K = (2π)^{-p/2} √det M` (`gaussianNormConst`) and `G(b) = (π/b)^{p/2}` (`gaussianMass`).

For fixed `δ` the second term tends to `0` as `n → ∞`, since `n^{p/2} e^{-nλδ²/4} → 0`; the
first term is small when `o` and `η` are small, which a prior continuous at the center and an
expansion error vanishing with the radius give for small `δ`. -/
theorem tvDist_densityPosterior_gaussian_le {M : Matrix ι ι ℝ} (hM : M.PosDef) {lam : ℝ}
    (hlam : 0 < lam) (hQ : ∀ v, lam * ‖v‖ ^ 2 ≤ quadForm M v) {p : EuclideanSpace ℝ ι → ℝ}
    (hpm : Measurable p) (hp0 : ∀ θ, 0 ≤ p θ) (hpi : Integrable p) (hpZ : 0 < ∫ θ, p θ)
    {ℓ : EuclideanSpace ℝ ι → ℝ} (hℓ : ConcaveOn ℝ univ ℓ) {m θ₀ : EuclideanSpace ℝ ι}
    {n η δ o : ℝ} (hn : 0 < n) (hη0 : 0 ≤ η) (hη : η ≤ lam / 4) (hδ : 0 < δ)
    (hquad : ∀ u, ‖u‖ ≤ δ → |ℓ (m + u) - ℓ m + n / 2 * quadForm M u| ≤ η * n * ‖u‖ ^ 2)
    (hosc : ∀ θ, ‖θ - m‖ ≤ δ → |p θ - p θ₀| ≤ o) (hpθ₀ : 0 < p θ₀) :
    tvDist (densityPosterior volume p fun θ ↦ Real.exp (ℓ θ))
      ((multivariateGaussian 0 M⁻¹).map fun u ↦ m + (√n)⁻¹ • u) ≤
      2 * gaussianNormConst M / p θ₀ *
        ((o + 8 * p θ₀ * η / lam) * gaussianMass ι (lam / 8) +
          Real.exp (-(n * lam / 4) * δ ^ 2) *
            ((√n) ^ Fintype.card ι * (∫ θ, p θ) + p θ₀ * gaussianMass ι (lam / 4))) := by
  have hℓm : Measurable ℓ := (continuousOn_univ.mp (hℓ.continuousOn isOpen_univ)).measurable
  obtain ⟨hle0, hlap⟩ := integral_abs_mul_exp_sub_gaussian_le hlam hQ hpm hp0 hpi hℓ hn hη0 hη
    hδ hquad hosc
  set K := gaussianNormConst M with hK
  have hK0 : 0 < K := gaussianNormConst_pos hM
  have hsn : 0 < (√n) ^ Fintype.card ι := pow_pos (Real.sqrt_pos.2 hn) _
  set L : EuclideanSpace ℝ ι → ℝ := fun θ ↦ Real.exp (ℓ θ) with hLdef
  have hLm : Measurable L := hℓm.exp
  have hL : ∀ θ, 0 < L θ := fun θ ↦ Real.exp_pos _
  -- the two unnormalized densities
  set g : EuclideanSpace ℝ ι → ℝ := fun θ ↦ p θ * Real.exp (ℓ θ - ℓ m) with hg
  set G : EuclideanSpace ℝ ι → ℝ :=
    fun θ ↦ p θ₀ * Real.exp (-(n / 2) * quadForm M (θ - m)) with hG
  set c := (√n) ^ Fintype.card ι * K / p θ₀ with hc
  have hc0 : 0 < c := by positivity
  set r : EuclideanSpace ℝ ι → ℝ := fun θ ↦ c * G θ with hr
  have hq : Measurable fun θ ↦ quadForm M (θ - m) :=
    (continuous_quadForm M).measurable.comp (measurable_id.sub_const m)
  have hgm : Measurable g := by
    simp only [hg]
    fun_prop
  have hGm : Measurable G := by
    simp only [hG]
    fun_prop
  have hg0 : ∀ θ, 0 ≤ g θ := fun θ ↦ mul_nonneg (hp0 θ) (Real.exp_pos _).le
  have hgle : ∀ θ, g θ ≤ p θ := fun θ ↦ by
    simp only [hg]
    exact mul_le_of_le_one_right (hp0 θ) (Real.exp_le_one_iff.2 (hle0 θ))
  have hgi : Integrable g := hpi.mono' hgm.aestronglyMeasurable (ae_of_all _ fun θ ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 θ)]; exact hgle θ)
  have hGb : ∀ θ, G θ ≤ p θ₀ * Real.exp (-(n * lam / 2) * ‖θ - m‖ ^ 2) := fun θ ↦ by
    simp only [hG]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hpθ₀.le
    have := hQ (θ - m)
    nlinarith
  have hGi : Integrable G :=
    ((integrable_exp_neg_mul_sq_norm_sub (b := n * lam / 2) (by positivity) m).const_mul
      (p θ₀)).mono' hGm.aestronglyMeasurable (ae_of_all _ fun θ ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpθ₀.le (Real.exp_pos _).le)]
        exact hGb θ)
  -- the normal approximation has density `r = c G`
  have htarget : (multivariateGaussian 0 M⁻¹).map (fun u ↦ m + (√n)⁻¹ • u) =
      volume.withDensity fun θ ↦ ENNReal.ofReal (r θ) := by
    rw [map_affine_multivariateGaussian_inv_eq_withDensity hM m hn]
    congr 1
    funext θ
    congr 1
    simp only [hr, hG, hc, hK]
    field_simp [hpθ₀.ne']
  have hr0 : ∀ θ, 0 ≤ r θ := fun θ ↦
    mul_nonneg hc0.le (mul_nonneg hpθ₀.le (Real.exp_pos _).le)
  have hri : Integrable r := hGi.const_mul _
  have hr1 : ∫ θ, r θ = 1 := by
    have hprob : IsProbabilityMeasure (volume.withDensity fun θ ↦ ENNReal.ofReal (r θ)) := by
      rw [← htarget]
      exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
    have h := hprob.measure_univ
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hr0) hri.aestronglyMeasurable, h]
    simp
  have hGint : ∫ θ, G θ = c⁻¹ := by
    have : ∫ θ, r θ = c * ∫ θ, G θ := integral_const_mul _ _
    rw [hr1] at this
    field_simp
    linarith
  -- the posterior has density `g / ∫ g`
  have hLle : ∀ θ, L θ ≤ L m := fun θ ↦ Real.exp_le_exp.2 (by linarith [hle0 θ])
  have hpLi : Integrable fun θ ↦ p θ * L θ :=
    (hpi.mul_const (L m)).mono' (hpm.mul hLm).aestronglyMeasurable (ae_of_all _ fun θ ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 θ) (hL θ).le)]
      exact mul_le_mul_of_nonneg_left (hLle θ) (hp0 θ))
  have hZ : 0 < ∫ θ, p θ * L θ := by
    rw [integral_pos_iff_support_of_nonneg (fun θ ↦ mul_nonneg (hp0 θ) (hL θ).le) hpLi]
    rw [integral_pos_iff_support_of_nonneg hp0 hpi] at hpZ
    refine hpZ.trans_le (measure_mono fun θ hθ ↦ ?_)
    exact mul_ne_zero hθ (hL θ).ne'
  have hgL : ∀ θ, g θ = p θ * L θ / L m := fun θ ↦ by
    simp only [hg, hLdef]
    rw [Real.exp_sub]
    ring
  have hgint : ∫ θ, g θ = (∫ θ, p θ * L θ) / L m := by
    rw [← integral_div]
    exact integral_congr_ae (ae_of_all _ hgL)
  have hgpos : 0 < ∫ θ, g θ := by
    rw [hgint]
    exact div_pos hZ (hL m)
  rw [densityPosterior_eq_withDensity hpm hp0 hLm (fun θ ↦ (hL θ).le) hpLi hZ, htarget]
  have hpost0 : ∀ θ, 0 ≤ p θ * L θ / ∫ θ', p θ' * L θ' := fun θ ↦
    div_nonneg (mul_nonneg (hp0 θ) (hL θ).le) hZ.le
  refine (tvDist_withDensity_le (hpLi.div_const _) hri hpost0 hr0).trans ?_
  have hpost : ∀ θ, p θ * L θ / (∫ θ', p θ' * L θ') = g θ / ∫ θ', g θ' := fun θ ↦ by
    rw [hgL, hgint]
    field_simp [(hL m).ne']
  have hrr : ∀ θ, r θ = G θ / ∫ θ', G θ' := fun θ ↦ by
    rw [hGint, div_inv_eq_mul, mul_comm]
  calc ∫ θ, |p θ * L θ / (∫ θ', p θ' * L θ') - r θ|
      = ∫ θ, |g θ / (∫ θ', g θ') - G θ / ∫ θ', G θ'| := by
        refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
        simp only
        rw [hpost, hrr]
    _ ≤ 2 * (∫ θ, |g θ - G θ|) / ∫ θ, G θ :=
        integral_abs_div_sub_div_le hgi hGi hg0 hgpos (by rw [hGint]; positivity)
    _ = 2 * c * ∫ θ, |g θ - G θ| := by
        rw [hGint]
        field_simp
    _ ≤ 2 * c * ((o + 8 * p θ₀ * η / lam) * gaussianMass ι (n * lam / 8) +
          Real.exp (-(n * lam / 4) * δ ^ 2) *
            ((∫ θ, p θ) + p θ₀ * gaussianMass ι (n * lam / 4))) :=
        mul_le_mul_of_nonneg_left hlap (by positivity)
    _ = _ := by
        have h8 := sqrt_pow_mul_gaussianMass (ι := ι) hn (b := lam / 8) (by positivity)
        have h4 := sqrt_pow_mul_gaussianMass (ι := ι) hn (b := lam / 4) (by positivity)
        rw [show n * lam / 8 = n * (lam / 8) by ring, show n * lam / 4 = n * (lam / 4) by ring,
          ← h8, ← h4, hc]
        field_simp

end Bound

/-! ### Change of parameter in the Bernstein and von Mises conclusion -/

section Transport

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **The Bernstein and von Mises conclusion under a linear change of parameter.** For a
continuous linear isomorphism `e : E ≃ F`, if the posteriors `Π_n` on `E` satisfy the total
variation conclusion with centering `θ̂_n` and limit `N`, their images `e_# Π_n` satisfy it with
centering `e θ̂_n` and limit `e_# N`: `e` commutes with the affine maps
`z ↦ θ̂_n + n^{-1/2} z`, and a measurable isomorphism preserves total variation. -/
theorem IsBernsteinVonMises.map_continuousLinearEquiv {P : Measure Ω} {Pn : ℕ → Ω → Measure E}
    {θh : ℕ → Ω → E} {N : Measure E} (h : IsBernsteinVonMises P Pn θh N) (e : E ≃L[ℝ] F) :
    IsBernsteinVonMises P (fun n ω ↦ (Pn n ω).map e) (fun n ω ↦ e (θh n ω)) (N.map e) := by
  have := h.isProbabilityMeasure_limit
  have hem : Measurable e := e.continuous.measurable
  have hsm : Measurable e.symm := e.symm.continuous.measurable
  refine ⟨fun n ω ↦ ?_, ?_, ?_⟩
  · have := h.isProbabilityMeasure n ω
    exact (Measure.isProbabilityMeasure_map_iff hem.aemeasurable).2 inferInstance
  · exact (Measure.isProbabilityMeasure_map_iff hem.aemeasurable).2 inferInstance
  · convert h.tendsto using 3 with n ω
    have := h.isProbabilityMeasure n ω
    have hmap : (N.map e).map (fun z ↦ e (θh n ω) + (√(n : ℝ))⁻¹ • z) =
        (N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z).map e := by
      rw [Measure.map_map (by fun_prop) hem, Measure.map_map hem (by fun_prop)]
      congr 1
      funext z
      simp [map_add, map_smul]
    have : IsProbabilityMeasure (N.map fun z ↦ θh n ω + (√(n : ℝ))⁻¹ • z) :=
      (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
    rw [hmap, tvDist_map_eq_of_leftInverse hem hsm fun x ↦ e.symm_apply_apply x]

end Transport

end PosteriorLimit

end CausalInference
