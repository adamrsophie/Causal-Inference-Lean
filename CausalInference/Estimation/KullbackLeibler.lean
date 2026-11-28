/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Estimation.InformationInequality
public import CausalInference.Estimation.BernoulliFamily
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The Kullback-Leibler divergence between two members of a dominated family

For a dominated family `P_θ = f(·;θ) ν` with `ν` σ-finite, the Radon-Nikodym derivative of `P_θ₀`
with respect to `P_θ` is the density ratio `f(·;θ₀) / f(·;θ)` wherever `f(·;θ) > 0` holds
`ν`-almost everywhere. Positivity also gives `P_θ₀ ≪ P_θ`. The divergence is then the expected log
likelihood ratio:

`KL(P_θ₀ ‖ P_θ) = E_θ₀[ℓ(θ₀;X)] - E_θ₀[ℓ(θ;X)]`,

both expectations being taken under the true law `P_θ₀`. The divergence is finite exactly when
the log likelihood ratio `ℓ(θ₀;·) - ℓ(θ;·)` is `P_θ₀`-integrable, in particular when each
log density is.

## Main results

* `CausalInference.rnDeriv_withDensity_withDensity`: for `ν` σ-finite and `g ≠ 0, ∞`
  `ν`-almost everywhere, `(ν.withDensity f).rnDeriv (ν.withDensity g) =ᵐ[ν] f / g`.
* `CausalInference.ParametricFamily.law_absolutelyContinuous`: `P_θ₀ ≪ P_θ`.
* `CausalInference.ParametricFamily.llr_law_ae_eq`: the log likelihood ratio is
  `ℓ(θ₀;·) - ℓ(θ;·)`, `P_θ₀`-almost everywhere.
* `CausalInference.ParametricFamily.klDiv_law_ne_top_iff`: finiteness of the divergence.
* `CausalInference.ParametricFamily.toReal_klDiv_law`: the expected log likelihood ratio form.
* `CausalInference.ParametricFamily.bernoulli_toReal_klDiv`: the Bernoulli closed form.

References: S. Kullback and R. A. Leibler (1951), *On information and sufficiency*, Annals of
Mathematical Statistics.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter InformationTheory
open scoped ENNReal

namespace CausalInference

/-- **Radon-Nikodym derivative of one density measure with respect to another.** If `ν` is
σ-finite, `f` is measurable and finite `ν`-almost everywhere, and `g` is measurable with
`0 < g < ∞` `ν`-almost everywhere, then `d(fν)/d(gν) = f / g`, `ν`-almost everywhere. -/
theorem rnDeriv_withDensity_withDensity {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [SigmaFinite ν] {f g : α → ℝ≥0∞} (hf : Measurable f) (hf_top : ∀ᵐ x ∂ν, f x ≠ ∞)
    (hg : Measurable g) (hg0 : ∀ᵐ x ∂ν, g x ≠ 0) (hg_top : ∀ᵐ x ∂ν, g x ≠ ∞) :
    (ν.withDensity f).rnDeriv (ν.withDensity g) =ᵐ[ν] fun x ↦ f x / g x := by
  have := SigmaFinite.withDensity_of_ne_top hf_top
  have h1 := Measure.rnDeriv_withDensity_right (ν.withDensity f) ν hg.aemeasurable hg0 hg_top
  have h2 := Measure.rnDeriv_withDensity ν hf
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2, ENNReal.div_eq_inv_mul]

namespace ParametricFamily

variable {P S : Type*} [MeasurableSpace S] {F : ParametricFamily P S} [SigmaFinite F.ν]

omit [SigmaFinite F.ν] in
/-- If `f(·;θ) > 0` holds `ν`-almost everywhere, every law of the family is absolutely continuous
with respect to `P_θ`. -/
theorem law_absolutelyContinuous {θ₀ θ : P} (hpos : ∀ᵐ x ∂F.ν, 0 < F.density θ x) :
    F.law θ₀ ≪ F.law θ :=
  (withDensity_absolutelyContinuous _ _).trans
    (withDensity_absolutelyContinuous' (F.measurable_density θ).ennreal_ofReal.aemeasurable
      (hpos.mono fun x hx ↦ by simpa using hx))

/-- The Radon-Nikodym derivative `dP_θ₀/dP_θ` is the density ratio, `ν`-almost everywhere, when
`f(·;θ) > 0` holds `ν`-almost everywhere. -/
theorem rnDeriv_law {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hpos : ∀ᵐ x ∂F.ν, 0 < F.density θ x) :
    (F.law θ₀).rnDeriv (F.law θ) =ᵐ[F.ν]
      fun x ↦ ENNReal.ofReal (F.density θ₀ x) / ENNReal.ofReal (F.density θ x) := by
  have := isProbabilityMeasure_law hθ₀
  exact rnDeriv_withDensity_withDensity (F.measurable_density θ₀).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top) (F.measurable_density θ).ennreal_ofReal
    (hpos.mono fun x hx ↦ by simpa using hx) (ae_of_all _ fun _ ↦ ENNReal.ofReal_ne_top)

/-- **The log likelihood ratio of two members of the family** is `ℓ(θ₀;·) - ℓ(θ;·)`,
`P_θ₀`-almost everywhere, when `f(·;θ) > 0` holds `ν`-almost everywhere. -/
theorem llr_law_ae_eq {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ)
    (hpos : ∀ᵐ x ∂F.ν, 0 < F.density θ x) :
    llr (F.law θ₀) (F.law θ) =ᵐ[F.law θ₀] fun x ↦ F.logLik θ₀ x - F.logLik θ x := by
  filter_upwards [ae_law_of_ae (F := F) (θ := θ₀) (rnDeriv_law hθ₀ hpos),
    ae_law_of_ae (F := F) (θ := θ₀) hpos, ae_law_pos (F := F) (θ := θ₀)] with x hx hxpos hx0
  rw [llr, hx, ENNReal.toReal_div, ENNReal.toReal_ofReal (F.density_nonneg θ₀ hθ₀ x),
    ENNReal.toReal_ofReal (F.density_nonneg θ hθ x), Real.log_div hx0.ne' hxpos.ne', logLik,
    logLik]

/-- **Finiteness of the divergence.** When `f(·;θ) > 0` holds `ν`-almost everywhere,
`KL(P_θ₀ ‖ P_θ) < ∞` if and only if `ℓ(θ₀;·) - ℓ(θ;·)` is `P_θ₀`-integrable. -/
theorem klDiv_law_ne_top_iff {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ)
    (hpos : ∀ᵐ x ∂F.ν, 0 < F.density θ x) :
    klDiv (F.law θ₀) (F.law θ) ≠ ∞ ↔
      Integrable (fun x ↦ F.logLik θ₀ x - F.logLik θ x) (F.law θ₀) := by
  rw [klDiv_ne_top_iff, integrable_congr (llr_law_ae_eq hθ₀ hθ hpos)]
  exact and_iff_right (law_absolutelyContinuous hpos)

/-- **The divergence as an expected log likelihood ratio.** If `θ₀, θ ∈ Θ`, `f(·;θ) > 0` holds
`ν`-almost everywhere (this gives `P_θ₀ ≪ P_θ`), and both log densities `ℓ(θ₀;·)` and `ℓ(θ;·)`
are integrable under the true law `P_θ₀`, then the divergence is finite and
`KL(P_θ₀ ‖ P_θ) = E_θ₀[ℓ(θ₀;X)] - E_θ₀[ℓ(θ;X)]`. -/
theorem toReal_klDiv_law {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ)
    (hpos : ∀ᵐ x ∂F.ν, 0 < F.density θ x) (hl₀ : Integrable (F.logLik θ₀) (F.law θ₀))
    (hl : Integrable (F.logLik θ) (F.law θ₀)) :
    klDiv (F.law θ₀) (F.law θ) ≠ ∞ ∧
      (klDiv (F.law θ₀) (F.law θ)).toReal =
        ∫ x, F.logLik θ₀ x ∂F.law θ₀ - ∫ x, F.logLik θ x ∂F.law θ₀ := by
  have := isProbabilityMeasure_law hθ₀
  have := isProbabilityMeasure_law hθ
  refine ⟨(klDiv_law_ne_top_iff hθ₀ hθ hpos).2 (hl₀.sub hl), ?_⟩
  rw [toReal_klDiv_of_measure_eq (law_absolutelyContinuous hpos) (by simp),
    integral_congr_ae (llr_law_ae_eq hθ₀ hθ hpos), integral_sub hl₀ hl]

/-- The divergence in `ℝ≥0∞`, under the hypotheses of `toReal_klDiv_law`. -/
theorem klDiv_law_eq_ofReal {θ₀ θ : P} (hθ₀ : θ₀ ∈ F.Θ) (hθ : θ ∈ F.Θ)
    (hpos : ∀ᵐ x ∂F.ν, 0 < F.density θ x) (hl₀ : Integrable (F.logLik θ₀) (F.law θ₀))
    (hl : Integrable (F.logLik θ) (F.law θ₀)) :
    klDiv (F.law θ₀) (F.law θ) =
      ENNReal.ofReal (∫ x, F.logLik θ₀ x ∂F.law θ₀ - ∫ x, F.logLik θ x ∂F.law θ₀) := by
  obtain ⟨h1, h2⟩ := toReal_klDiv_law hθ₀ hθ hpos hl₀ hl
  rw [← h2, ENNReal.ofReal_toReal h1]

/-- **The Bernoulli divergence in closed form**: for `p₀, p ∈ (0, 1)`,
`KL(Bernoulli(p₀) ‖ Bernoulli(p)) = p₀ log (p₀ / p) + (1 - p₀) log ((1 - p₀) / (1 - p))`. -/
theorem bernoulli_toReal_klDiv {p₀ p : ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    klDiv (bernoulli.law p₀) (bernoulli.law p) ≠ ∞ ∧
      (klDiv (bernoulli.law p₀) (bernoulli.law p)).toReal =
        p₀ * Real.log (p₀ / p) + (1 - p₀) * Real.log ((1 - p₀) / (1 - p)) := by
  have := isProbabilityMeasure_law (F := bernoulli) hp₀
  have hint : ∀ q, Integrable (bernoulli.logLik q) (bernoulli.law p₀) := fun _ ↦
    Integrable.of_finite
  obtain ⟨h1, h2⟩ := toReal_klDiv_law hp₀ hp
    (ae_of_all _ fun x ↦ bernoulli_density_pos hp x) (hint p₀) (hint p)
  refine ⟨h1, ?_⟩
  have a0 : p₀ ≠ 0 := hp₀.1.ne'
  have a1 : 1 - p₀ ≠ 0 := by linarith [hp₀.2]
  have b0 : p ≠ 0 := hp.1.ne'
  have b1 : 1 - p ≠ 0 := by linarith [hp.2]
  rw [h2, bernoulli_integral_law hp₀, bernoulli_integral_law hp₀, Real.log_div a0 b0,
    Real.log_div a1 b1]
  simp only [logLik, bernoulli_density, ite_true, Bool.false_eq_true, ite_false]
  ring

end ParametricFamily

end CausalInference
