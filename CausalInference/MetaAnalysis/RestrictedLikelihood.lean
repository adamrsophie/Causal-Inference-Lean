/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.MetaAnalysis.GaussianLikelihood
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Meta-analysis: restricted maximum likelihood for the between study variance

Given `τ² = t`, the estimates of the Gaussian random effects model are independent with
`Yᵢ ~ N(θ, vᵢ + t)` and their likelihood is `θ ↦ ∏ᵢ φ(yᵢ; θ, vᵢ + t)` (`commonEffectLikelihood`
of the shifted variances). With the random effects weights `w̃ᵢ = 1 / (vᵢ + t)`, the
**restricted log likelihood** of `t` is (`restrictedLogLik`)

`ℓ_R(t) = -½ ∑ᵢ log(vᵢ + t) - ½ log(∑ᵢ w̃ᵢ) - ½ ∑ᵢ w̃ᵢ (yᵢ - θ̂(t))²`,

the last sum being Cochran's `Q` with the weights `w̃ᵢ`.

**What it is.** The restricted likelihood is the likelihood with the mean effect integrated
out: `∫ ∏ᵢ φ(yᵢ; θ, vᵢ + t) dθ = (2π)^{-(k-1)/2} exp(ℓ_R(t))` for every `t` with all
`vᵢ + t > 0` (`integral_commonEffectLikelihood`). Proof: the weighted sum of squares
decomposition `∑ w̃ᵢ (yᵢ - θ)² = Q + (∑ w̃ᵢ)(θ - θ̂)²` and the Gaussian integral in `θ`. The
constant does not depend on `t`, so `ℓ_R` and the integrated likelihood have the same maximizers.

**The score equation.** `ℓ_R` is differentiable wherever all `vᵢ + t > 0`, with derivative the
**restricted score** `½ (∑ w̃ᵢ² (yᵢ - θ̂)² - c(t))`, `c(t) = ∑ w̃ᵢ - ∑ w̃ᵢ² / ∑ w̃ᵢ` the slope
`cochranQSlope` of the shifted variances (`hasDerivAt_restrictedLogLik`). Hence
(`restrictedLogLik_firstOrder`):

* every maximizer `t > 0` on `[0, ∞)` solves the score equation `∑ w̃ᵢ² (yᵢ - θ̂)² = c(t)`;
* for `t ≥ 0` the score equation is equivalent to the **fixed point equation**
  `t = ∑ w̃ᵢ² ((yᵢ - θ̂)² - vᵢ) / ∑ w̃ᵢ² + 1 / ∑ w̃ᵢ`, the iteration used to compute the estimate;
* a maximizer at the boundary `t = 0` has restricted score `≤ 0` at `0`.

These are first order conditions. Neither the existence nor the uniqueness of a maximizer is
proved here.

## Main definitions

* `restrictedLogLik`, `restrictedScore`.

## Main results

* `cochranQ_eq_sum_sq_sub`, `integral_commonEffectLikelihood`, `hasDerivAt_restrictedLogLik`,
  `restrictedLogLik_firstOrder`.

## References

* H. D. Patterson and R. Thompson, *Recovery of inter-block information when block sizes are
  unequal*, Biometrika 58 (1971).
-/

@[expose] public section

namespace CausalInference

namespace MetaAnalysis

open MeasureTheory Finset Filter Topology PopulationAdjustment

variable {ι : Type*} [Fintype ι]

/-- `Q = ∑ wᵢ yᵢ² - (∑ wᵢ yᵢ)² / ∑ wᵢ`, for any variances (both sides use `x / 0 = 0` when
`∑ wᵢ = 0`). -/
theorem cochranQ_eq_sum_sq_sub (s y : ι → ℝ) :
    cochranQ s y = ∑ i, ivWeight s i * y i ^ 2 -
      (∑ i, ivWeight s i * y i) ^ 2 / ∑ i, ivWeight s i := by
  have hexp : ∀ i, ivWeight s i * (y i - ivwEstimate s y) ^ 2 = ivWeight s i * y i ^ 2 -
      2 * ivwEstimate s y * (ivWeight s i * y i) + ivwEstimate s y ^ 2 * ivWeight s i :=
    fun i => by ring
  rw [cochranQ]
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [ivwEstimate, weightedMean]
  rcases eq_or_ne (∑ i, ivWeight s i) 0 with h | h
  · simp [h]
  · field_simp
    ring

/-- The **restricted log likelihood** of the between study variance `t`:
`ℓ_R(t) = -½ ∑ log(vᵢ + t) - ½ log(∑ w̃ᵢ) - ½ Q(t)`, with `w̃ᵢ = 1 / (vᵢ + t)` and `Q(t)` Cochran's
`Q` with these weights (Patterson and Thompson 1971). -/
noncomputable def restrictedLogLik (v y : ι → ℝ) (t : ℝ) : ℝ :=
  -(1 / 2) * ∑ i, Real.log (v i + t) - 1 / 2 * Real.log (∑ i, ivWeight (fun i => v i + t) i) -
    1 / 2 * cochranQ (fun i => v i + t) y

/-- The **restricted score** `½ (∑ w̃ᵢ² (yᵢ - θ̂(t))² - c(t))`, with `c(t)` the slope
`cochranQSlope` of the shifted variances. -/
noncomputable def restrictedScore (v y : ι → ℝ) (t : ℝ) : ℝ :=
  1 / 2 * (∑ i, ivWeight (fun i => v i + t) i ^ 2 *
      (y i - ivwEstimate (fun i => v i + t) y) ^ 2 - cochranQSlope fun i => v i + t)

/-- `exp(-½ log x) = 1 / √x` for `x > 0`. -/
theorem exp_neg_half_log {x : ℝ} (hx : 0 < x) : Real.exp (-(1 / 2) * Real.log x) = (√x)⁻¹ := by
  rw [show -(1 / 2) * Real.log x = -(Real.log x / 2) by ring, ← Real.log_sqrt hx.le,
    Real.exp_neg, Real.exp_log (Real.sqrt_pos.2 hx)]

/-- **The restricted likelihood is the likelihood with the mean effect integrated out**: for
`t` with all `vᵢ + t > 0` and at least one study,
`∫ ∏ᵢ φ(yᵢ; θ, vᵢ + t) dθ = √(2π) (√(2π))⁻ᵏ exp(ℓ_R(t))`, that is `(2π)^{-(k-1)/2} exp(ℓ_R(t))`.
The constant does not depend on `t`. -/
theorem integral_commonEffectLikelihood [Nonempty ι] {v : ι → ℝ} {t : ℝ}
    (ht : ∀ i, 0 < v i + t) (y : ι → ℝ) :
    ∫ θ, commonEffectLikelihood (fun i => v i + t) θ y =
      √(2 * Real.pi) * (√(2 * Real.pi))⁻¹ ^ Fintype.card ι *
        Real.exp (restrictedLogLik v y t) := by
  set s : ι → ℝ := fun i => v i + t with hs
  have hW := sum_ivWeight_pos ht
  set W := ∑ i, ivWeight s i
  have hπ : 0 < 2 * Real.pi := by positivity
  have hL : ∀ θ, commonEffectLikelihood s θ y = (∏ i, (√(2 * Real.pi * s i))⁻¹) *
      Real.exp (-(1 / 2) * cochranQ s y) *
        Real.exp (-(W / 2) * (θ - ivwEstimate s y) ^ 2) := by
    intro θ
    rw [commonEffectLikelihood_eq ht, mul_assoc, ← Real.exp_add]
    congr 2
    rw [cochranQ_eq_sub ht y θ]
    ring
  simp only [hL]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun θ => Real.exp (-(W / 2) * θ ^ 2)) (ivwEstimate s y), integral_gaussian]
  have hprod : ∏ i, (√(2 * Real.pi * s i))⁻¹ =
      (√(2 * Real.pi))⁻¹ ^ Fintype.card ι * Real.exp (-(1 / 2) * ∑ i, Real.log (s i)) := by
    rw [Finset.mul_sum, Real.exp_sum]
    simp only [Real.sqrt_mul hπ.le, mul_inv, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (exp_neg_half_log (ht i)).symm
  have hsq : √(Real.pi / (W / 2)) = √(2 * Real.pi) * Real.exp (-(1 / 2) * Real.log W) := by
    rw [exp_neg_half_log hW, show Real.pi / (W / 2) = 2 * Real.pi / W by field_simp,
      Real.sqrt_div hπ.le, div_eq_mul_inv]
  have hR : restrictedLogLik v y t = -(1 / 2) * ∑ i, Real.log (s i) +
      -(1 / 2) * Real.log W + -(1 / 2) * cochranQ s y := by
    simp only [restrictedLogLik, s, W]
    ring
  rw [hprod, hsq, hR, Real.exp_add, Real.exp_add]
  ring

/-- **The derivative of the restricted log likelihood**: wherever all `vᵢ + t > 0`,
`ℓ_R'(t)` is the restricted score. Proof: `dw̃ᵢ/dt = -w̃ᵢ²`, the representation
`Q = ∑ w̃ᵢ yᵢ² - (∑ w̃ᵢ yᵢ)² / ∑ w̃ᵢ`, and the quotient rule. -/
theorem hasDerivAt_restrictedLogLik [Nonempty ι] {v : ι → ℝ} (y : ι → ℝ) {t : ℝ}
    (ht : ∀ i, 0 < v i + t) :
    HasDerivAt (restrictedLogLik v y) (restrictedScore v y t) t := by
  set a : ι → ℝ := fun i => ivWeight (fun i => v i + t) i with ha_def
  have hapos : ∀ i, 0 < a i := fun i => one_div_pos.2 (ht i)
  have ha : ∀ i, HasDerivAt (fun u => ivWeight (fun i => v i + u) i) (-(a i ^ 2)) t := by
    intro i
    have := ((hasDerivAt_id t).const_add (v i)).inv (ht i).ne'
    have he : (fun u => ivWeight (fun i => v i + u) i) = fun u => (v i + id u)⁻¹ := by
      funext u; simp [ivWeight]
    rw [he]
    convert this using 1
    simp only [ha_def, ivWeight, id]
    field_simp
  have hsum : ∀ c : ι → ℝ, HasDerivAt (fun u => ∑ i, ivWeight (fun i => v i + u) i * c i)
      (∑ i, -(a i ^ 2) * c i) t := fun c =>
    HasDerivAt.fun_sum fun i _ => (ha i).mul_const (c i)
  have hA1 : HasDerivAt (fun u => ∑ i, ivWeight (fun i => v i + u) i) (∑ i, -(a i ^ 2)) t :=
    HasDerivAt.fun_sum fun i _ => ha i
  have hA1pos : 0 < ∑ i, ivWeight (fun i => v i + t) i := sum_ivWeight_pos ht
  have hlog : HasDerivAt (fun u => ∑ i, Real.log (v i + u)) (∑ i, a i) t := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have := ((hasDerivAt_id t).const_add (v i)).log (ht i).ne'
    simpa [ha_def, ivWeight] using this
  have hfun : restrictedLogLik v y = fun u => -(1 / 2) * ∑ i, Real.log (v i + u) -
      1 / 2 * Real.log (∑ i, ivWeight (fun i => v i + u) i) -
      1 / 2 * (∑ i, ivWeight (fun i => v i + u) i * y i ^ 2 -
        (∑ i, ivWeight (fun i => v i + u) i * y i) ^ 2 /
          ∑ i, ivWeight (fun i => v i + u) i) := by
    funext u
    rw [restrictedLogLik, cochranQ_eq_sum_sq_sub]
  rw [hfun]
  have hd := ((hlog.const_mul (-(1 / 2))).sub ((hA1.log hA1pos.ne').const_mul (1 / 2))).sub
    (((hsum fun i => y i ^ 2).sub (((hsum y).pow 2).div hA1 hA1pos.ne')).const_mul (1 / 2))
  convert hd using 1
  have hai : ∀ i, ivWeight (fun i => v i + t) i = a i := fun i => rfl
  have hA1ne : ∑ i, a i ≠ 0 := hA1pos.ne'
  simp only [restrictedScore, cochranQSlope, Pi.pow_apply, hai, ivwEstimate, weightedMean]
  set N := ∑ i, a i * y i
  set A1 := ∑ i, a i
  have hexp : ∀ i, a i ^ 2 * (y i - N / A1) ^ 2 = a i ^ 2 * y i ^ 2 -
      2 * (N / A1) * (a i ^ 2 * y i) + (N / A1) ^ 2 * a i ^ 2 := fun i => by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_neg_distrib, neg_mul]
  field_simp
  ring

/-- **First order conditions for the restricted maximum likelihood estimate** (Patterson and
Thompson 1971). For known `vᵢ > 0`, at least one study and data `y`, with `ℓ_R` maximized over
`t ≥ 0`:

* `ℓ_R` is differentiable at every `t ≥ 0`, with derivative the restricted score;
* every maximizer `t > 0` solves the score equation `∑ w̃ᵢ² (yᵢ - θ̂)² = c(t)`;
* for `t ≥ 0` the score equation is equivalent to the fixed point equation
  `t = ∑ w̃ᵢ² ((yᵢ - θ̂)² - vᵢ) / ∑ w̃ᵢ² + 1 / ∑ w̃ᵢ`;
* a maximizer at `0` has restricted score `≤ 0` at `0`.

Proof: an interior maximizer is a local maximum, so the derivative vanishes; the fixed point
form uses `w̃ᵢ (vᵢ + t) = 1`; at the boundary the right difference quotients are `≤ 0`. -/
theorem restrictedLogLik_firstOrder [Nonempty ι] {v : ι → ℝ} (hv : ∀ i, 0 < v i) (y : ι → ℝ) :
    (∀ t, 0 ≤ t → HasDerivAt (restrictedLogLik v y) (restrictedScore v y t) t) ∧
      (∀ t, 0 < t → IsMaxOn (restrictedLogLik v y) (Set.Ici 0) t →
        ∑ i, ivWeight (fun i => v i + t) i ^ 2 *
            (y i - ivwEstimate (fun i => v i + t) y) ^ 2 =
          cochranQSlope fun i => v i + t) ∧
      (∀ t, 0 ≤ t →
        (∑ i, ivWeight (fun i => v i + t) i ^ 2 *
              (y i - ivwEstimate (fun i => v i + t) y) ^ 2 =
            cochranQSlope (fun i => v i + t) ↔
          t = (∑ i, ivWeight (fun i => v i + t) i ^ 2 *
                ((y i - ivwEstimate (fun i => v i + t) y) ^ 2 - v i)) /
              (∑ i, ivWeight (fun i => v i + t) i ^ 2) +
            1 / ∑ i, ivWeight (fun i => v i + t) i)) ∧
      (IsMaxOn (restrictedLogLik v y) (Set.Ici 0) 0 → restrictedScore v y 0 ≤ 0) := by
  have hd : ∀ t, 0 ≤ t → HasDerivAt (restrictedLogLik v y) (restrictedScore v y t) t :=
    fun t ht => hasDerivAt_restrictedLogLik y fun i => by linarith [hv i]
  refine ⟨hd, fun t ht hmax => ?_, fun t ht => ?_, fun hmax => ?_⟩
  · have hloc : IsLocalMax (restrictedLogLik v y) t := hmax.isLocalMax (Ici_mem_nhds ht)
    have h0 := hloc.hasDerivAt_eq_zero (hd t ht.le)
    simp only [restrictedScore] at h0
    linarith
  · set a : ι → ℝ := fun i => ivWeight (fun i => v i + t) i with ha_def
    have hapos : ∀ i, 0 < a i := fun i => one_div_pos.2 (by linarith [hv i])
    have hA1 : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => hapos i) Finset.univ_nonempty
    have hA2 : 0 < ∑ i, a i ^ 2 :=
      Finset.sum_pos (fun i _ => pow_pos (hapos i) 2) Finset.univ_nonempty
    have hterm : ∀ i, a i ^ 2 * ((y i - ivwEstimate (fun i => v i + t) y) ^ 2 - v i) =
        a i ^ 2 * (y i - ivwEstimate (fun i => v i + t) y) ^ 2 - a i + t * a i ^ 2 := by
      intro i
      have h1 : a i * (v i + t) = 1 := by
        rw [mul_comm]
        exact mul_ivWeight (v := fun i => v i + t) (fun j => by linarith [hv j]) i
      linear_combination (-a i) * h1
    have hai : ∀ i, ivWeight (fun i => v i + t) i = a i := fun i => rfl
    simp only [hai, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [cochranQSlope]
    simp only [hai]
    set R := ∑ i, a i ^ 2 * (y i - ivwEstimate (fun i => v i + t) y) ^ 2
    set A1 := ∑ i, a i
    set A2 := ∑ i, a i ^ 2
    constructor
    · intro h
      rw [h]
      field_simp
      ring
    · intro h
      have key : (R - A1 + t * A2) / A2 = t - 1 / A1 := by linarith
      rw [div_eq_iff hA2.ne'] at key
      field_simp at key ⊢
      linear_combination key
  · have hslope := (hd 0 le_rfl).tendsto_slope_zero_right
    refine le_of_tendsto hslope ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hle := isMaxOn_iff.1 hmax (0 + h) (show 0 + h ∈ Set.Ici 0 by
      rw [zero_add]; exact le_of_lt hh)
    simp only [smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt hh)) (sub_nonpos.2 hle)

end MetaAnalysis

end CausalInference
