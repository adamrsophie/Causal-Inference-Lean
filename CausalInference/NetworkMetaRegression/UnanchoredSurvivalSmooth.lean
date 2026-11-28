/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.NetworkMetaRegression.UnanchoredSurvivalMedian
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Smoothness of the target functionals in the model parameter

**Time scale: continuous.** A family of integrands `G(ξ; x)`, continuously differentiable in
`ξ` with local integrable envelopes of the derivative (`HasDerivEnvelope`), has a continuously
differentiable integral (`contDiff_integral_of_derivEnvelope`). Applied to the conditional
survival curves of a model, the target survival `ξ ↦ ∫ S(ξ; t, x) F(dx)` and the restricted mean
`ξ ↦ ∫₀^τ ∫ S(ξ; s, x) F(dx) ds` are continuously differentiable (`contDiff_targetFunctionals`);
so are the marginal hazard `∫ N / ∫ D` where `∫ D > 0`, the hazard ratio and its logarithm, and
the median where the marginal density at the median is positive and each curve is injective in
time (`contDiff_targetMedian`).

For the proportional hazards model with the multilevel linear predictor `c + xᵀb`,
`S(ξ; t, x) = exp(-e^{c + xᵀb} H₀(t))`, the envelope is `e^{-1} (1 + Σⱼ |xⱼ|)`, so the target
survival and the restricted mean are continuously differentiable in `ξ = (c, b)` for every target
law with integrable coordinates (`contDiff_targetFunctionals_ph`).

## Main results

* `contDiff_integral_of_derivEnvelope`, `contDiff_targetFunctionals`.
* `contDiff_marginalHazard`, `contDiff_marginalHazardRatio`, `contDiff_targetMedian`.
* `linearPredictorCLM`, `hasFDerivAt_phSurvival_linear`, `contDiff_targetFunctionals_ph`,
  `contDiff_targetFunctionals_ph_instance`.
-/

@[expose] public section

namespace CausalInference

namespace NetworkMetaRegression

open MeasureTheory Filter Topology Set
open Survival.ContinuousTime

section Envelope

variable {E 𝒳 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace 𝒳]

/-- **Local integrable envelopes of the parameter derivative.** The integrand `G(ξ; x)` is
integrable in `x`, differentiable in `ξ` with derivative `G'(ξ; x)`, continuous in `ξ` and
measurable in `x`, and near every `ξ₀` the norm `‖G'(ξ; x)‖` has an integrable envelope. -/
structure HasDerivEnvelope (μ : Measure 𝒳) (G : E → 𝒳 → ℝ) (G' : E → 𝒳 → E →L[ℝ] ℝ) :
    Prop where
  integrable : ∀ ξ, Integrable (G ξ) μ
  aestronglyMeasurable_deriv : ∀ ξ, AEStronglyMeasurable (G' ξ) μ
  hasFDerivAt : ∀ x ξ, HasFDerivAt (fun ξ => G ξ x) (G' ξ x) ξ
  continuous_deriv : ∀ x, Continuous fun ξ => G' ξ x
  envelope : ∀ ξ₀, ∃ U ∈ 𝓝 ξ₀, ∃ g : 𝒳 → ℝ, Integrable g μ ∧
    ∀ᵐ x ∂μ, ∀ ξ ∈ U, ‖G' ξ x‖ ≤ g x

/-- **Differentiation under the integral sign**: under `HasDerivEnvelope`, `ξ ↦ ∫ G(ξ; x) dμ`
has derivative `∫ G'(ξ; x) dμ` and is continuously differentiable. -/
theorem contDiff_integral_of_derivEnvelope {μ : Measure 𝒳} {G : E → 𝒳 → ℝ}
    {G' : E → 𝒳 → E →L[ℝ] ℝ} (hG : HasDerivEnvelope μ G G') :
    (∀ ξ, HasFDerivAt (fun ξ => ∫ x, G ξ x ∂μ) (∫ x, G' ξ x ∂μ) ξ) ∧
      ContDiff ℝ 1 (fun ξ => ∫ x, G ξ x ∂μ) := by
  have hD : ∀ ξ₀, HasFDerivAt (fun ξ => ∫ x, G ξ x ∂μ) (∫ x, G' ξ₀ x ∂μ) ξ₀ := by
    intro ξ₀
    obtain ⟨U, hU, g, hg, hb⟩ := hG.envelope ξ₀
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le hU
      (Eventually.of_forall fun ξ => (hG.integrable ξ).aestronglyMeasurable) (hG.integrable ξ₀)
      (hG.aestronglyMeasurable_deriv ξ₀) hb hg (ae_of_all _ fun x ξ _ => hG.hasFDerivAt x ξ)
  refine ⟨hD, contDiff_one_iff_hasFDerivAt.2 ⟨fun ξ => ∫ x, G' ξ x ∂μ, ?_, hD⟩⟩
  refine continuous_iff_continuousAt.2 fun ξ₀ => ?_
  obtain ⟨U, hU, g, hg, hb⟩ := hG.envelope ξ₀
  exact continuousAt_of_dominated (Eventually.of_forall hG.aestronglyMeasurable_deriv)
    (Filter.mem_of_superset hU fun ξ hξ => hb.mono fun x hx => hx ξ hξ) hg
    (ae_of_all _ fun x => (hG.continuous_deriv x).continuousAt)

/-- **The target survival and restricted mean are continuously differentiable.** Let the
conditional survival `S(ξ; t, x)` be jointly measurable in `(t, x)` with `|S| ≤ 1` at `t ≥ 0`,
differentiable in `ξ` with a jointly measurable derivative `S'(ξ; t, x)` continuous in `ξ`, and
let `‖S'‖` have local integrable envelopes uniform over each horizon `[0, τ]`. Then for every
`t ≥ 0` the target survival `ξ ↦ ∫ S(ξ; t, x) F(dx)` has derivative `∫ S'(ξ; t, x) F(dx)` and is
continuously differentiable, and for every `τ ≥ 0` so is the restricted mean
`ξ ↦ ∫₀^τ ∫ S(ξ; s, x) F(dx) ds`. -/
theorem contDiff_targetFunctionals (F : Measure 𝒳) [IsProbabilityMeasure F]
    (S : E → ℝ → 𝒳 → ℝ) (S' : E → ℝ → 𝒳 → E →L[ℝ] ℝ)
    (hSm : ∀ ξ, StronglyMeasurable (Function.uncurry (S ξ)))
    (hS'm : ∀ ξ, StronglyMeasurable (Function.uncurry (S' ξ)))
    (hb : ∀ ξ t, 0 ≤ t → ∀ x, |S ξ t x| ≤ 1)
    (hd : ∀ t x ξ, HasFDerivAt (fun ξ => S ξ t x) (S' ξ t x) ξ)
    (hc : ∀ t x, Continuous fun ξ => S' ξ t x)
    (henv : ∀ τ ξ₀, ∃ U ∈ 𝓝 ξ₀, ∃ g : 𝒳 → ℝ, Integrable g F ∧
      ∀ s ∈ Icc 0 τ, ∀ x, ∀ ξ ∈ U, ‖S' ξ s x‖ ≤ g x) :
    (∀ t, 0 ≤ t → (∀ ξ, HasFDerivAt (fun ξ => ∫ x, S ξ t x ∂F) (∫ x, S' ξ t x ∂F) ξ) ∧
        ContDiff ℝ 1 (fun ξ => ∫ x, S ξ t x ∂F)) ∧
      ∀ τ, 0 ≤ τ → ContDiff ℝ 1 (fun ξ => restrictedMean (fun s => ∫ x, S ξ s x ∂F) τ) := by
  refine ⟨fun t ht => contDiff_integral_of_derivEnvelope ⟨fun ξ => ?_, fun ξ => ?_,
    fun x ξ => hd t x ξ, fun x => hc t x, fun ξ₀ => ?_⟩, fun τ hτ => ?_⟩
  · exact Integrable.of_bound
      ((hSm ξ).comp_measurable measurable_prodMk_left).aestronglyMeasurable
      1 (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb ξ t ht x)
  · exact ((hS'm ξ).comp_measurable measurable_prodMk_left).aestronglyMeasurable
  · obtain ⟨U, hU, g, hg, hgb⟩ := henv t ξ₀
    exact ⟨U, hU, g, hg, ae_of_all _ fun x ξ hξ => hgb t ⟨ht, le_rfl⟩ x ξ hξ⟩
  set ν := (volume.restrict (Ioc (0 : ℝ) τ)).prod F with hν
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) τ)) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hmem : ∀ᵐ q ∂ν, q.1 ∈ Ioc 0 τ :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  have hint : ∀ ξ, Integrable (Function.uncurry (S ξ)) ν := fun ξ =>
    Integrable.of_bound (hSm ξ).aestronglyMeasurable 1 (hmem.mono fun q hq => by
      rw [Real.norm_eq_abs]; exact hb ξ q.1 hq.1.le q.2)
  have heq : (fun ξ => restrictedMean (fun s => ∫ x, S ξ s x ∂F) τ) =
      fun ξ => ∫ q, Function.uncurry (S ξ) q ∂ν := by
    funext ξ
    rw [restrictedMean, intervalIntegral.integral_of_le hτ, hν, integral_prod _ (hint ξ)]
    rfl
  rw [heq]
  refine (contDiff_integral_of_derivEnvelope ⟨hint, fun ξ => (hS'm ξ).aestronglyMeasurable,
    fun q ξ => hd q.1 q.2 ξ, fun q => hc q.1 q.2, fun ξ₀ => ?_⟩).2
  obtain ⟨U, hU, g, hg, hgb⟩ := henv τ ξ₀
  refine ⟨U, hU, fun q => 1 * g q.2, (integrable_const (1 : ℝ)).mul_prod hg, ?_⟩
  filter_upwards [hmem] with q hq ξ hξ
  rw [one_mul]
  exact hgb q.1 ⟨hq.1.le, hq.2⟩ q.2 ξ hξ

/-- **The marginal hazard is continuously differentiable**: for a numerator `N(ξ; x)` (the
conditional density at `t`) and a denominator `D(ξ; x)` (the conditional survival at `t`) with
local derivative envelopes and `∫ D(ξ; x) F(dx) > 0`, the marginal hazard `ξ ↦ ∫ N / ∫ D` is
continuously differentiable. -/
theorem contDiff_marginalHazard {F : Measure 𝒳} {N D : E → 𝒳 → ℝ}
    {N' D' : E → 𝒳 → E →L[ℝ] ℝ} (hN : HasDerivEnvelope F N N') (hD : HasDerivEnvelope F D D')
    (hpos : ∀ ξ, 0 < ∫ x, D ξ x ∂F) :
    ContDiff ℝ 1 (fun ξ => (∫ x, N ξ x ∂F) / ∫ x, D ξ x ∂F) :=
  (contDiff_integral_of_derivEnvelope hN).2.div (contDiff_integral_of_derivEnvelope hD).2
    fun ξ => (hpos ξ).ne'

/-- **The marginal hazard ratio and its logarithm are continuously differentiable** for the
marginal hazards `∫ N_k / ∫ D_k` of two arms with positive numerators and denominators. -/
theorem contDiff_marginalHazardRatio {F : Measure 𝒳} {NA DA NB DB : E → 𝒳 → ℝ}
    {NA' DA' NB' DB' : E → 𝒳 → E →L[ℝ] ℝ} (hNA : HasDerivEnvelope F NA NA')
    (hDA : HasDerivEnvelope F DA DA') (hNB : HasDerivEnvelope F NB NB')
    (hDB : HasDerivEnvelope F DB DB') (hNA0 : ∀ ξ, 0 < ∫ x, NA ξ x ∂F)
    (hDA0 : ∀ ξ, 0 < ∫ x, DA ξ x ∂F) (hNB0 : ∀ ξ, 0 < ∫ x, NB ξ x ∂F)
    (hDB0 : ∀ ξ, 0 < ∫ x, DB ξ x ∂F) :
    ContDiff ℝ 1 (fun ξ => ((∫ x, NA ξ x ∂F) / ∫ x, DA ξ x ∂F) /
        ((∫ x, NB ξ x ∂F) / ∫ x, DB ξ x ∂F)) ∧
      ContDiff ℝ 1 (fun ξ => Real.log (((∫ x, NA ξ x ∂F) / ∫ x, DA ξ x ∂F) /
        ((∫ x, NB ξ x ∂F) / ∫ x, DB ξ x ∂F))) := by
  have hA := contDiff_marginalHazard hNA hDA hDA0
  have hB := contDiff_marginalHazard hNB hDB hDB0
  have hBpos : ∀ ξ, 0 < (∫ x, NB ξ x ∂F) / ∫ x, DB ξ x ∂F := fun ξ => div_pos (hNB0 ξ) (hDB0 ξ)
  have hR := hA.div hB fun ξ => (hBpos ξ).ne'
  exact ⟨hR, hR.log fun ξ => (div_pos (div_pos (hNA0 ξ) (hDA0 ξ)) (hBpos ξ)).ne'⟩

/-- **The target median is continuously differentiable.** Let the conditional survival
`S((ξ, t); x)` have local derivative envelopes in the joint argument `(ξ, t)`, let `m(ξ)` be a
median of the target survival `M(ξ, t) = ∫ S((ξ, t); x) F(dx)` (`M(ξ, m(ξ)) = 1/2`), let each
`t ↦ M(ξ, t)` be injective and let its time derivative at `m(ξ)` be nonzero. Then `m` is
continuously differentiable. -/
theorem contDiff_targetMedian [CompleteSpace E] (F : Measure 𝒳) {S : E × ℝ → 𝒳 → ℝ}
    {S' : E × ℝ → 𝒳 → (E × ℝ) →L[ℝ] ℝ} (hS : HasDerivEnvelope F S S') {med : E → ℝ}
    (hmed : ∀ ξ, ∫ x, S (ξ, med ξ) x ∂F = 1 / 2)
    (hinj : ∀ ξ, Function.Injective fun t => ∫ x, S (ξ, t) x ∂F)
    (hdens : ∀ ξ, ∃ d ≠ 0, HasDerivAt (fun t => ∫ x, S (ξ, t) x ∂F) d (med ξ)) :
    ContDiff ℝ 1 med := by
  have hC := (contDiff_integral_of_derivEnvelope hS).2
  refine contDiff_iff_contDiffAt.2 fun ξ₀ => ?_
  obtain ⟨d, hd0, hd⟩ := hdens ξ₀
  exact contDiffAt_median (M := fun q => ∫ x, S q x ∂F) hC.contDiffAt hd hd0
    (Eventually.of_forall hmed) (Eventually.of_forall hinj)

end Envelope

/-! ### The proportional hazards model -/

section Proportional

variable {p : ℕ}

/-- The linear predictor `ξ = (c, b) ↦ c + xᵀb` as a continuous linear map of the parameter. -/
noncomputable def linearPredictorCLM (x : Fin p → ℝ) : (ℝ × (Fin p → ℝ)) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ (Fin p → ℝ) +
    ∑ j, x j • (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ (Fin p → ℝ))

theorem linearPredictorCLM_apply (x : Fin p → ℝ) (ξ : ℝ × (Fin p → ℝ)) :
    linearPredictorCLM x ξ = ξ.1 + x ⬝ᵥ ξ.2 := by
  simp [linearPredictorCLM, dotProduct]

theorem norm_linearPredictorCLM_le (x : Fin p → ℝ) :
    ‖linearPredictorCLM x‖ ≤ 1 + ∑ j, |x j| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ξ => ?_
  rw [linearPredictorCLM_apply, Real.norm_eq_abs, dotProduct]
  have h1 : |ξ.1| ≤ ‖ξ‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le ξ
  have h2 : ∀ j, |ξ.2 j| ≤ ‖ξ‖ := fun j => by
    rw [← Real.norm_eq_abs]; exact (norm_le_pi_norm ξ.2 j).trans (norm_snd_le ξ)
  calc |ξ.1 + ∑ j, x j * ξ.2 j| ≤ |ξ.1| + ∑ j, |x j| * |ξ.2 j| := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        simp only [abs_mul]
    _ ≤ ‖ξ‖ + ∑ j, |x j| * ‖ξ‖ := by
        gcongr with j
        exact h2 j
    _ = (1 + ∑ j, |x j|) * ‖ξ‖ := by rw [add_mul, one_mul, Finset.sum_mul]

/-- The **parameter derivative** of the proportional hazards survival
`exp(-e^{c + xᵀb} H₀(t))`: `-S(ξ; t, x) e^{c + xᵀb} H₀(t)` times the linear predictor map. -/
noncomputable def phSurvivalParamDeriv (h₀ : ℝ → ℝ) (ξ : ℝ × (Fin p → ℝ)) (t : ℝ)
    (x : Fin p → ℝ) : (ℝ × (Fin p → ℝ)) →L[ℝ] ℝ :=
  (-(Real.exp (-(Real.exp (ξ.1 + x ⬝ᵥ ξ.2) * cumHazard h₀ t)) *
    (Real.exp (ξ.1 + x ⬝ᵥ ξ.2) * cumHazard h₀ t))) • linearPredictorCLM x

theorem phSurvival_linear_eq (h₀ : ℝ → ℝ) (ξ : ℝ × (Fin p → ℝ)) (t : ℝ) (x : Fin p → ℝ) :
    phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2) x t =
      Real.exp (-(Real.exp (ξ.1 + x ⬝ᵥ ξ.2) * cumHazard h₀ t)) := rfl

/-- The proportional hazards survival has parameter derivative `phSurvivalParamDeriv`. -/
theorem hasFDerivAt_phSurvival_linear (h₀ : ℝ → ℝ) (t : ℝ) (x : Fin p → ℝ)
    (ξ : ℝ × (Fin p → ℝ)) :
    HasFDerivAt (fun ξ : ℝ × (Fin p → ℝ) =>
        phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2) x t)
      (phSurvivalParamDeriv h₀ ξ t x) ξ := by
  have hf : (fun ξ : ℝ × (Fin p → ℝ) =>
      phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2) x t) =
      fun ξ => Real.exp (-(Real.exp (linearPredictorCLM x ξ) * cumHazard h₀ t)) := by
    funext ξ
    rw [phSurvival_linear_eq, linearPredictorCLM_apply]
  have h := (((linearPredictorCLM x).hasFDerivAt (x := ξ)).exp.mul_const
    (cumHazard h₀ t)).neg.exp
  rw [hf]
  refine h.congr_fderiv ?_
  rw [phSurvivalParamDeriv, ← linearPredictorCLM_apply x ξ, Pi.neg_apply, smul_neg, smul_smul,
    smul_smul]
  module

/-- **The proportional hazards target functionals are continuously differentiable.** For a
locally integrable baseline hazard, nonnegative at nonnegative times, and a target covariate law
`F` with integrable coordinates, the target survival `ξ ↦ ∫ exp(-e^{c + xᵀb} H₀(t)) F(dx)`
(`t ≥ 0`) and its restricted mean on `[0, τ]` (`τ ≥ 0`) are continuously differentiable in
`ξ = (c, b)`. -/
theorem contDiff_targetFunctionals_ph {h₀ : ℝ → ℝ}
    (hloc : ∀ a b, IntervalIntegrable h₀ volume a b) (hnn : ∀ u, 0 ≤ u → 0 ≤ h₀ u)
    (F : Measure (Fin p → ℝ)) [IsProbabilityMeasure F] (hx : ∀ j, Integrable (fun x => x j) F) :
    (∀ t, 0 ≤ t → ContDiff ℝ 1 fun ξ : ℝ × (Fin p → ℝ) =>
        popSurvival F (phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2)) t) ∧
      ∀ τ, 0 ≤ τ → ContDiff ℝ 1 fun ξ : ℝ × (Fin p → ℝ) =>
        restrictedMean (popSurvival F (phSurvival (cumHazard h₀)
          (linearRelativeHazard ξ.1 ξ.2))) τ := by
  have hcH := continuous_cumHazard hloc
  have hcL : Continuous fun x : Fin p → ℝ => linearPredictorCLM x := by
    unfold linearPredictorCLM
    fun_prop
  have hS1 : ∀ ξ : ℝ × (Fin p → ℝ), ∀ t, 0 ≤ t → ∀ x : Fin p → ℝ,
      |phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2) x t| ≤ 1 := fun ξ t ht x => by
    rw [phSurvival_linear_eq, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (Real.exp_pos _).le (cumHazard_nonneg hnn ht)
  have main := contDiff_targetFunctionals F
    (fun (ξ : ℝ × (Fin p → ℝ)) t x =>
      phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2) x t)
    (fun ξ t x => phSurvivalParamDeriv h₀ ξ t x) (fun ξ => ?_) (fun ξ => ?_) hS1
    (fun t x ξ => hasFDerivAt_phSurvival_linear h₀ t x ξ) (fun t x => ?_) (fun τ ξ₀ => ?_)
  · exact ⟨fun t ht => (main.1 t ht).2, main.2⟩
  · refine Continuous.stronglyMeasurable ?_
    change Continuous fun q : ℝ × (Fin p → ℝ) =>
      phSurvival (cumHazard h₀) (linearRelativeHazard ξ.1 ξ.2) q.2 q.1
    simp only [phSurvival_linear_eq, dotProduct]
    fun_prop
  · refine Continuous.stronglyMeasurable ?_
    change Continuous fun q : ℝ × (Fin p → ℝ) => phSurvivalParamDeriv h₀ ξ q.1 q.2
    unfold phSurvivalParamDeriv
    simp only [dotProduct]
    fun_prop
  · unfold phSurvivalParamDeriv
    simp only [dotProduct]
    fun_prop
  · refine ⟨univ, univ_mem, fun x => Real.exp (-1) * (1 + ∑ j, |x j|),
      ((integrable_const 1).add (integrable_finsetSum _ fun j _ => (hx j).abs)).const_mul _,
      fun s hs x ξ _ => ?_⟩
    rw [phSurvivalParamDeriv, norm_smul, Real.norm_eq_abs, abs_neg]
    have hu : 0 ≤ Real.exp (ξ.1 + x ⬝ᵥ ξ.2) * cumHazard h₀ s :=
      mul_nonneg (Real.exp_pos _).le (cumHazard_nonneg hnn hs.1)
    have habs : |Real.exp (-(Real.exp (ξ.1 + x ⬝ᵥ ξ.2) * cumHazard h₀ s)) *
        (Real.exp (ξ.1 + x ⬝ᵥ ξ.2) * cumHazard h₀ s)| ≤ Real.exp (-1) := by
      rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hu), mul_comm]
      exact Real.mul_exp_neg_le_exp_neg_one _
    exact mul_le_mul habs (norm_linearPredictorCLM_le x) (norm_nonneg _) (Real.exp_pos _).le

/-- **Instance: a unit baseline, a two valued covariate.** With `h₀ = 1` and the covariate law
putting mass `1/2` at `0` and at `1`, every hypothesis of `contDiff_targetFunctionals_ph` holds,
so the target survival at every `t ≥ 0` and the restricted mean on every `[0, τ]` are
continuously differentiable in `ξ = (c, b)`. -/
theorem contDiff_targetFunctionals_ph_instance :
    (∀ t, 0 ≤ t → ContDiff ℝ 1 fun ξ : ℝ × (Fin 1 → ℝ) =>
        popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
          (phSurvival (cumHazard fun _ => 1) (linearRelativeHazard ξ.1 ξ.2)) t) ∧
      ∀ τ, 0 ≤ τ → ContDiff ℝ 1 fun ξ : ℝ × (Fin 1 → ℝ) =>
        restrictedMean (popSurvival (twoAtomLaw ![0] ![1] (1 / 2))
          (phSurvival (cumHazard fun _ => 1) (linearRelativeHazard ξ.1 ξ.2))) τ := by
  have := isProbabilityMeasure_twoAtomLaw (x₁ := ![(0 : ℝ)]) (x₂ := ![1]) (t := 1 / 2)
    (by norm_num) (by norm_num)
  exact contDiff_targetFunctionals_ph (fun a b => intervalIntegrable_const)
    (fun _ _ => zero_le_one) _ fun _ => integrable_twoAtomLaw _

end Proportional

end NetworkMetaRegression

end CausalInference
