/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.Score
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# The information inequality

For a dominated parametric family and two parameters `θ₀, θ ∈ Θ`, the expected log-likelihood
under the true parameter is maximized at the truth:
`E_θ₀[log f(X;θ)] ≤ E_θ₀[log f(X;θ₀)]`, and equality forces `P_θ = P_θ₀`. When the parameter is
point identified from the law, equality holds only at `θ = θ₀`; this is the identification of the
true parameter on which the consistency of the maximum likelihood estimator rests. The
Kullback-Leibler form uses Mathlib's divergence `InformationTheory.klDiv`.

Lean's `Real.log 0 = 0`, where the mathematical convention is `log 0 = -∞`. The integrability of
`log f(X;θ)` under `P_θ₀` therefore does not imply `f(X;θ) > 0` almost surely, and this
positivity is a separate hypothesis.

## Main results

* `CausalInference.mul_log_sub_log_le`, `CausalInference.eq_of_mul_log_sub_log_eq`: the pointwise
  inequality `a (log b - log a) ≤ b - a` for `a, b > 0` and its equality case.
* `CausalInference.ParametricFamily.integral_logLik_le`: the information inequality, with
  `P_θ = P_θ₀` in the equality case.
* `CausalInference.ParametricFamily.integral_logLik_lt`, `integral_logLik_eq_iff`: under point
  identification, the inequality is strict for `θ ≠ θ₀`.
* `CausalInference.ParametricFamily.klDiv_law_eq_zero_iff`, `klDiv_law_pos`: the
  Kullback-Leibler divergence between `P_θ₀` and `P_θ` vanishes exactly at `θ = θ₀` under point
  identification.

References: S. Kullback and R. A. Leibler (1951), *On information and sufficiency*, Annals of
Mathematical Statistics; E. L. Lehmann and G. Casella (1998), *Theory of Point Estimation*,
2nd edition, chapter 6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter InformationTheory
open scoped ENNReal

namespace CausalInference

/-- The pointwise inequality `a (log b - log a) ≤ b - a` for `a, b > 0`: `log u ≤ u - 1` at
`u = b / a`, multiplied by `a`. -/
theorem mul_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * (Real.log b - Real.log a) ≤ b - a := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have h' := mul_le_mul_of_nonneg_left h ha.le
  have h3 : a * (b / a - 1) = b - a := by field_simp
  linarith

/-- The equality case of `mul_log_sub_log_le`: equality forces `b = a`, since otherwise
`log (b / a) ≠ 0` and `log u + 1 < exp (log u) = u`. -/
theorem eq_of_mul_log_sub_log_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a * (Real.log b - Real.log a) = b - a) : b = a := by
  by_contra hne
  have hl : Real.log (b / a) ≠ 0 := fun h0 ↦
    hne ((div_eq_one_iff_eq ha.ne').1 (Real.eq_one_of_pos_of_log_eq_zero (div_pos hb ha) h0))
  have h1 := Real.add_one_lt_exp hl
  rw [Real.exp_log (div_pos hb ha), Real.log_div hb.ne' ha.ne'] at h1
  have h2 := mul_lt_mul_of_pos_left h1 ha
  rw [mul_add, mul_one, mul_div_cancel₀ _ ha.ne'] at h2
  linarith

namespace ParametricFamily

variable {P S : Type*} [MeasurableSpace S] {F : ParametricFamily P S}

/-- **The information inequality.** Let `θ₀, θ ∈ Θ`, let `f(X;θ) > 0` almost surely under
`P_θ₀`, and let `log f(·;θ₀)` and `log f(·;θ)` be `P_θ₀`-integrable. Then
`E_θ₀[log f(X;θ)] ≤ E_θ₀[log f(X;θ₀)]`, and equality forces `P_θ = P_θ₀`.

Proof: `D = (f_θ - f_θ₀) - f_θ₀ (log f_θ - log f_θ₀)` is `ν`-almost everywhere nonnegative (by
`mul_log_sub_log_le` where `f_θ₀ > 0`, and `D = f_θ ≥ 0` where `f_θ₀ = 0`), and its `ν`-integral
is the gap `E_θ₀[log f_θ₀] - E_θ₀[log f_θ]`, because both densities integrate to one. If the gap
vanishes, `D = 0` almost everywhere, so `f_θ = f_θ₀` almost everywhere
(`eq_of_mul_log_sub_log_eq`). -/
theorem integral_logLik_le {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ)
    (hpos : ∀ᵐ x ∂F.law θ₀, 0 < F.density θ x)
    (hl₀ : Integrable (F.logLik θ₀) (F.law θ₀)) (hl : Integrable (F.logLik θ) (F.law θ₀)) :
    ∫ x, F.logLik θ x ∂F.law θ₀ ≤ ∫ x, F.logLik θ₀ x ∂F.law θ₀ ∧
      (∫ x, F.logLik θ x ∂F.law θ₀ = ∫ x, F.logLik θ₀ x ∂F.law θ₀ → F.law θ = F.law θ₀) := by
  set g₀ := F.density θ₀
  set g := F.density θ
  rw [integrable_law_iff hθ₀] at hl₀ hl
  rw [integral_law hθ₀, integral_law hθ₀]
  have hposν : ∀ᵐ x ∂F.ν, 0 < g₀ x → 0 < g x := by
    rw [law, ae_withDensity_iff (F.measurable_density θ₀).ennreal_ofReal] at hpos
    filter_upwards [hpos] with x hx hp
    exact hx (by simpa using hp)
  set D : S → ℝ := fun x ↦ (g x - g₀ x) - (g₀ x * F.logLik θ x - g₀ x * F.logLik θ₀ x)
    with hD
  have hDi : Integrable D F.ν :=
    ((F.integrable_density θ hθ).sub (F.integrable_density θ₀ hθ₀)).sub (hl.sub hl₀)
  have hD0 : 0 ≤ᵐ[F.ν] D := by
    filter_upwards [hposν] with x hx
    rcases (F.density_nonneg θ₀ hθ₀ x).eq_or_lt with h0 | h0
    · simp only [hD, Pi.zero_apply, g₀, ← h0, zero_mul, sub_zero]
      exact F.density_nonneg θ hθ x
    · have := mul_log_sub_log_le h0 (hx h0)
      simp only [hD, Pi.zero_apply, logLik]
      linarith [mul_sub (g₀ x) (Real.log (g x)) (Real.log (g₀ x))]
  have hDint : ∫ x, D x ∂F.ν =
      -(∫ x, g₀ x * F.logLik θ x ∂F.ν - ∫ x, g₀ x * F.logLik θ₀ x ∂F.ν) := by
    have e1 : ∫ x, D x ∂F.ν = ∫ x, (g x - g₀ x) ∂F.ν -
        ∫ x, (g₀ x * F.logLik θ x - g₀ x * F.logLik θ₀ x) ∂F.ν :=
      integral_sub ((F.integrable_density θ hθ).sub (F.integrable_density θ₀ hθ₀)) (hl.sub hl₀)
    rw [e1, integral_sub (F.integrable_density θ hθ) (F.integrable_density θ₀ hθ₀),
      integral_sub hl hl₀, F.integral_density θ hθ, F.integral_density θ₀ hθ₀]
    ring
  have hDnn : 0 ≤ ∫ x, D x ∂F.ν := integral_nonneg_of_ae hD0
  refine ⟨by linarith, fun heq ↦ ?_⟩
  have hz : ∫ x, D x ∂F.ν = 0 := by rw [hDint, heq, sub_self, neg_zero]
  have hDae := (integral_eq_zero_iff_of_nonneg_ae hD0 hDi).1 hz
  rw [law_eq_law_iff hθ hθ₀]
  filter_upwards [hDae, hposν] with x hx hxp
  simp only [hD, Pi.zero_apply] at hx
  rcases (F.density_nonneg θ₀ hθ₀ x).eq_or_lt with h0 | h0
  · change g x = g₀ x
    have h0' : g₀ x = 0 := h0.symm
    rw [h0'] at hx ⊢
    simpa using hx
  · refine eq_of_mul_log_sub_log_eq h0 (hxp h0) ?_
    simp only [logLik] at hx
    linarith [mul_sub (g₀ x) (Real.log (g x)) (Real.log (g₀ x))]

/-- **Identification by the information inequality.** If the parameter is point identified on
`Θ` from the law (`CausalInference.PointIdentified`), then under the hypotheses of
`integral_logLik_le` the expected log-likelihoods are equal if and only if `θ = θ₀`. -/
theorem integral_logLik_eq_iff (hid : PointIdentified F.Θ F.law id) {θ₀ θ : P}
    (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ) (hpos : ∀ᵐ x ∂F.law θ₀, 0 < F.density θ x)
    (hl₀ : Integrable (F.logLik θ₀) (F.law θ₀)) (hl : Integrable (F.logLik θ) (F.law θ₀)) :
    ∫ x, F.logLik θ x ∂F.law θ₀ = ∫ x, F.logLik θ₀ x ∂F.law θ₀ ↔ θ = θ₀ :=
  ⟨fun h ↦ hid θ hθ θ₀ hθ₀ ((integral_logLik_le hθ₀ hθ hpos hl₀ hl).2 h),
    fun h ↦ by rw [h]⟩

/-- **The true parameter is the unique maximizer of the expected log-likelihood.** Under point
identification and the hypotheses of `integral_logLik_le`, for `θ ≠ θ₀`,
`E_θ₀[log f(X;θ)] < E_θ₀[log f(X;θ₀)]`. -/
theorem integral_logLik_lt (hid : PointIdentified F.Θ F.law id) {θ₀ θ : P}
    (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ) (hne : θ ≠ θ₀) (hpos : ∀ᵐ x ∂F.law θ₀, 0 < F.density θ x)
    (hl₀ : Integrable (F.logLik θ₀) (F.law θ₀)) (hl : Integrable (F.logLik θ) (F.law θ₀)) :
    ∫ x, F.logLik θ x ∂F.law θ₀ < ∫ x, F.logLik θ₀ x ∂F.law θ₀ :=
  lt_of_le_of_ne (integral_logLik_le hθ₀ hθ hpos hl₀ hl).1
    fun h ↦ hne ((integral_logLik_eq_iff hid hθ₀ hθ hpos hl₀ hl).1 h)

/-- **The Kullback-Leibler divergence identifies the parameter.** If the parameter is point
identified on `Θ` from the law, then for `θ₀, θ ∈ Θ` the divergence `KL(P_θ₀ ‖ P_θ)` (Mathlib's
`InformationTheory.klDiv`, with values in `[0, ∞]`) vanishes if and only if `θ = θ₀`. No
integrability of the log-likelihood ratio is needed: a non integrable ratio gives the value `∞`. -/
theorem klDiv_law_eq_zero_iff (hid : PointIdentified F.Θ F.law id) {θ₀ θ : P}
    (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ) : klDiv (F.law θ₀) (F.law θ) = 0 ↔ θ = θ₀ := by
  have := isProbabilityMeasure_law hθ₀
  have := isProbabilityMeasure_law hθ
  rw [klDiv_eq_zero_iff]
  exact ⟨fun h ↦ hid θ hθ θ₀ hθ₀ h.symm, fun h ↦ by rw [h]⟩

/-- Under point identification, `KL(P_θ₀ ‖ P_θ) > 0` for `θ ≠ θ₀` in `Θ`. -/
theorem klDiv_law_pos (hid : PointIdentified F.Θ F.law id) {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ)
    (hθ : θ ∈ F.Θ) (hne : θ ≠ θ₀) : 0 < klDiv (F.law θ₀) (F.law θ) :=
  pos_iff_ne_zero.2 fun h ↦ hne ((klDiv_law_eq_zero_iff hid hθ₀ hθ).1 h)

end ParametricFamily

end CausalInference
