/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaAnalysis.ProbitAggregation

/-!
# The probit non collapsibility gap arm by arm

Write `Φ = cdf (gaussianReal 0 1)`. In the probit model with arm risks `Φ(a_t + ρ_t x)` and a
Gaussian covariate `X ∼ N(m, s)`, the marginal probit effect minus the conditional probit effect
at the covariate mean `m` splits into one bracket per arm,

`[probit(∫ Φ(a₁ + ρ₁ x) dN) - (a₁ + ρ₁ m)] - [probit(∫ Φ(a₀ + ρ₀ x) dN) - (a₀ + ρ₀ m)]`,

and each bracket is the averaging gap of the arm on the probit scale (`averagingGap`).

* **Closed form of a bracket** (`averagingGap_probit_gaussian`): the bracket of an arm with
  linear predictor `a + ρ x` is `(a + ρ m)(κ - 1)`, with the attenuation factor
  `κ = 1 / √(1 + ρ² s)` (`probitAttenuation s ρ`).
* **Sign of a bracket** (`averagingGap_probit_gaussian_mul_nonpos`,
  `averagingGap_probit_gaussian_eq_zero_iff`, `averagingGap_probit_gaussian_sign`): the bracket
  has the sign opposite to the linear predictor at the mean `a + ρ m`; it is zero exactly when
  `ρ = 0`, `s = 0` or `a + ρ m = 0`; otherwise it lies strictly between `0` and `-(a + ρ m)`:
  the probit of the marginal risk is pulled toward zero, never past it.
* **The gap of the contrast** (`linkMarginal_sub_linkContrast_probit_gaussian`): the marginal
  effect minus the conditional effect at the mean (which is also the average conditional effect)
  is the difference of the two brackets, in closed form
  `(a₁ + ρ₁ m)(κ₁ - 1) - (a₀ + ρ₀ m)(κ₀ - 1)`.
* **A computed instance** (`linkMarginal_sub_linkContrast_probit_example`): with `X ∼ N(1, 3)`,
  arms `Φ(-5 + 4 x)` and `Φ(1 + x)`, the factors are `1/7` and `1/2`, the brackets `6/7` and
  `-1`, the conditional effect at the mean `3`, the marginal effect `8/7`, and the gap `-13/7`.

## Main results

* `averagingGap_probit_gaussian_eq`, `averagingGap_probit_gaussian`.
* `averagingGap_probit_gaussian_mul_nonpos`, `averagingGap_probit_gaussian_eq_zero_iff`,
  `averagingGap_probit_gaussian_sign`.
* `linkMarginal_sub_linkContrast_probit_gaussian`.
* `linkMarginal_sub_linkContrast_probit_example`.

## References

* S. L. Zeger, K.-Y. Liang and P. S. Albert, *Models for longitudinal data: a generalized
  estimating equation approach*, Biometrics 44 (1988).
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaAnalysis

open MeasureTheory ProbabilityTheory EffectMeasure
open scoped NNReal

/-- **The bracket of an arm is its averaging gap on the probit scale**: for the arm risk
`Φ(a + ρ x)` and `X ∼ N(m, s)`, `J_probit = probit(∫ Φ(a + ρ x) dN(m, s)) - (a + ρ m)`. -/
theorem averagingGap_probit_gaussian_eq (m : ℝ) (s : ℝ≥0) (a ρ : ℝ) :
    averagingGap probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) =
      probit (∫ x, cdf (gaussianReal 0 1) (a + ρ * x) ∂gaussianReal m s) - (a + ρ * m) := by
  have hi : Integrable (fun x : ℝ => x) (gaussianReal m s) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  rw [averagingGap]
  congr 1
  simp only [probit_cdf]
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul,
    integral_id_gaussianReal]
  simp

/-- **Closed form of the bracket of an arm** (Zeger, Liang and Albert 1988, for the
attenuation): for the arm risk `Φ(a + ρ x)` and `X ∼ N(m, s)`,
`probit(∫ Φ(a + ρ x) dN(m, s)) - (a + ρ m) = (a + ρ m)(κ - 1)` with `κ = 1 / √(1 + ρ² s)`. -/
theorem averagingGap_probit_gaussian (m : ℝ) (s : ℝ≥0) (a ρ : ℝ) :
    averagingGap probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) =
      (a + ρ * m) * (probitAttenuation s ρ - 1) := by
  have hX : HasLaw (fun x : ℝ => x) (gaussianReal m s) (gaussianReal m s) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  rw [averagingGap_probit_gaussian_eq, hX.integral_cdf_affine, probit_cdf, probitAttenuation]
  ring

/-- **The bracket never has the sign of the linear predictor at the mean**:
`J · (a + ρ m) ≤ 0`. -/
theorem averagingGap_probit_gaussian_mul_nonpos (m : ℝ) (s : ℝ≥0) (a ρ : ℝ) :
    averagingGap probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) *
      (a + ρ * m) ≤ 0 := by
  rw [averagingGap_probit_gaussian]
  have h1 := probitAttenuation_le_one (NNReal.coe_nonneg s) ρ
  have : (a + ρ * m) * (probitAttenuation s ρ - 1) * (a + ρ * m) =
      (a + ρ * m) ^ 2 * (probitAttenuation s ρ - 1) := by ring
  rw [this]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)

/-- **The bracket vanishes exactly in the collapsible cases**: it is zero iff the arm has no
slope, `ρ = 0`, the covariate does not vary, `s = 0`, or the linear predictor vanishes at the
mean, `a + ρ m = 0`. -/
theorem averagingGap_probit_gaussian_eq_zero_iff (m : ℝ) (s : ℝ≥0) (a ρ : ℝ) :
    averagingGap probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) = 0 ↔
      ρ = 0 ∨ (s : ℝ) = 0 ∨ a + ρ * m = 0 := by
  rw [averagingGap_probit_gaussian, mul_eq_zero, sub_eq_zero,
    probitAttenuation_eq_one_iff (NNReal.coe_nonneg s) ρ]
  tauto

/-- **The sign of the bracket**: for a nonzero slope `ρ` and a varying covariate `s > 0`, the
bracket lies strictly between `0` and `-(a + ρ m)`: it is negative with `-(a + ρ m)` below it
when `a + ρ m > 0`, and positive with `-(a + ρ m)` above it when `a + ρ m < 0`. -/
theorem averagingGap_probit_gaussian_sign (m : ℝ) (s : ℝ≥0) (a : ℝ) {ρ : ℝ} (hρ : ρ ≠ 0)
    (hs : 0 < (s : ℝ)) :
    (0 < a + ρ * m →
        -(a + ρ * m) < averagingGap probit (gaussianReal m s)
            (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) ∧
          averagingGap probit (gaussianReal m s)
            (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) < 0) ∧
      (a + ρ * m < 0 →
        0 < averagingGap probit (gaussianReal m s)
            (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) ∧
          averagingGap probit (gaussianReal m s)
            (fun x => cdf (gaussianReal 0 1) (a + ρ * x)) < -(a + ρ * m)) := by
  rw [averagingGap_probit_gaussian]
  have h0 := probitAttenuation_pos (NNReal.coe_nonneg s) ρ
  have h1 : probitAttenuation s ρ < 1 :=
    lt_of_le_of_ne (probitAttenuation_le_one (NNReal.coe_nonneg s) ρ)
      fun h => ((probitAttenuation_eq_one_iff (NNReal.coe_nonneg s) ρ).1 h).elim hρ hs.ne'
  exact ⟨fun hp => ⟨by nlinarith, by nlinarith⟩, fun hn => ⟨by nlinarith, by nlinarith⟩⟩

/-- **The non collapsibility gap of the probit contrast, arm by arm.** With `X ∼ N(m, s)` and
arm risks `Φ(a_t + ρ_t x)`: the conditional probit effect at the covariate mean,
`(a₁ + ρ₁ m) - (a₀ + ρ₀ m)`, equals the average conditional effect; and the marginal effect
minus it is the difference of the two brackets
`[probit(∫ Φ(a₁ + ρ₁ x) dN) - (a₁ + ρ₁ m)] - [probit(∫ Φ(a₀ + ρ₀ x) dN) - (a₀ + ρ₀ m)]`,
that is `(a₁ + ρ₁ m)(κ₁ - 1) - (a₀ + ρ₀ m)(κ₀ - 1)` with `κ_t = 1 / √(1 + ρ_t² s)`. -/
theorem linkMarginal_sub_linkContrast_probit_gaussian (m : ℝ) (s : ℝ≥0) (a₀ a₁ ρ₀ ρ₁ : ℝ) :
    linkContrast probit (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) m =
      linkConditional probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) ∧
      linkMarginal probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
          (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) -
        linkContrast probit (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
          (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) m =
        (probit (∫ x, cdf (gaussianReal 0 1) (a₁ + ρ₁ * x) ∂gaussianReal m s) - (a₁ + ρ₁ * m)) -
          (probit (∫ x, cdf (gaussianReal 0 1) (a₀ + ρ₀ * x) ∂gaussianReal m s) -
            (a₀ + ρ₀ * m)) ∧
      linkMarginal probit (gaussianReal m s) (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
          (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) -
        linkContrast probit (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
          (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) m =
        (a₁ + ρ₁ * m) * (probitAttenuation s ρ₁ - 1) -
          (a₀ + ρ₀ * m) * (probitAttenuation s ρ₀ - 1) := by
  have hc : linkContrast probit (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
      (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) m = (a₁ + ρ₁ * m) - (a₀ + ρ₀ * m) := by
    rw [linkContrast, probit_cdf, probit_cdf]
  have hbr : ∀ a ρ : ℝ,
      probit (∫ x, cdf (gaussianReal 0 1) (a + ρ * x) ∂gaussianReal m s) - (a + ρ * m) =
        (a + ρ * m) * (probitAttenuation s ρ - 1) := fun a ρ => by
    rw [← averagingGap_probit_gaussian_eq, averagingGap_probit_gaussian]
  have h2 : linkMarginal probit (gaussianReal m s)
        (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) -
      linkContrast probit (fun x => cdf (gaussianReal 0 1) (a₀ + ρ₀ * x))
        (fun x => cdf (gaussianReal 0 1) (a₁ + ρ₁ * x)) m =
      (probit (∫ x, cdf (gaussianReal 0 1) (a₁ + ρ₁ * x) ∂gaussianReal m s) - (a₁ + ρ₁ * m)) -
        (probit (∫ x, cdf (gaussianReal 0 1) (a₀ + ρ₀ * x) ∂gaussianReal m s) -
          (a₀ + ρ₀ * m)) := by
    rw [hc, linkMarginal]
    ring
  refine ⟨?_, h2, ?_⟩
  · rw [hc, (linkMarginal_sub_linkConditional_probit m s a₀ a₁ ρ₀ ρ₁).1]
    ring
  · rw [h2, hbr, hbr]

/-- **A computed instance.** With `X ∼ N(1, 3)` and arm risks `Φ(-5 + 4 x)` (control) and
`Φ(1 + x)` (treatment), the attenuation factors are `1/7` and `1/2`; the brackets are `6/7`
(the linear predictor at the mean is `-1 < 0`, the bracket is positive) and `-1` (the linear
predictor at the mean is `2 > 0`, the bracket is negative); the conditional effect at the mean
is `3`, the marginal effect is `8/7`, and their difference is `-13/7`. -/
theorem linkMarginal_sub_linkContrast_probit_example :
    probitAttenuation 3 4 = 1 / 7 ∧ probitAttenuation 3 1 = 1 / 2 ∧
      averagingGap probit (gaussianReal 1 3) (fun x => cdf (gaussianReal 0 1) (-5 + 4 * x)) =
        6 / 7 ∧
      averagingGap probit (gaussianReal 1 3) (fun x => cdf (gaussianReal 0 1) (1 + 1 * x)) = -1 ∧
      linkContrast probit (fun x => cdf (gaussianReal 0 1) (-5 + 4 * x))
          (fun x => cdf (gaussianReal 0 1) (1 + 1 * x)) 1 = 3 ∧
      linkMarginal probit (gaussianReal 1 3) (fun x => cdf (gaussianReal 0 1) (-5 + 4 * x))
          (fun x => cdf (gaussianReal 0 1) (1 + 1 * x)) = 8 / 7 ∧
      linkMarginal probit (gaussianReal 1 3) (fun x => cdf (gaussianReal 0 1) (-5 + 4 * x))
          (fun x => cdf (gaussianReal 0 1) (1 + 1 * x)) -
        linkContrast probit (fun x => cdf (gaussianReal 0 1) (-5 + 4 * x))
          (fun x => cdf (gaussianReal 0 1) (1 + 1 * x)) 1 = -13 / 7 := by
  have hs : (((3 : ℝ≥0)) : ℝ) = 3 := by norm_num
  have hk0 : probitAttenuation 3 4 = 1 / 7 := by
    rw [probitAttenuation, show (1 + (4 : ℝ) ^ 2 * 3) = 7 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hk1 : probitAttenuation 3 1 = 1 / 2 := by
    rw [probitAttenuation, show (1 + (1 : ℝ) ^ 2 * 3) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hg0 : averagingGap probit (gaussianReal 1 3)
      (fun x => cdf (gaussianReal 0 1) (-5 + 4 * x)) = 6 / 7 := by
    rw [averagingGap_probit_gaussian, hs, hk0]
    norm_num
  have hg1 : averagingGap probit (gaussianReal 1 3)
      (fun x => cdf (gaussianReal 0 1) (1 + 1 * x)) = -1 := by
    rw [averagingGap_probit_gaussian, hs, hk1]
    norm_num
  obtain ⟨-, h2, h3⟩ := linkMarginal_sub_linkContrast_probit_gaussian 1 3 (-5) 1 4 1
  have hc : linkContrast probit (fun x => cdf (gaussianReal 0 1) (-5 + 4 * x))
      (fun x => cdf (gaussianReal 0 1) (1 + 1 * x)) 1 = 3 := by
    rw [linkContrast, probit_cdf, probit_cdf]
    norm_num
  rw [hs, hk0, hk1, hc] at h3
  refine ⟨hk0, hk1, hg0, hg1, hc, by linarith, by rw [hc]; linarith⟩

end NetworkMetaAnalysis

end CausalInference
