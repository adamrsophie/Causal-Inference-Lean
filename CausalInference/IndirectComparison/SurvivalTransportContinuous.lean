/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.SurvivalTransport
public import CausalInference.Survival.RestrictedMeanCollapsible
public import CausalInference.Survival.HazardMixtureGeneral

/-!
# Survival effects under shared effect modifiers, in continuous time

**Time scale: continuous.** The conditional survival curves `S t x` of the arms `t` at the
covariate values `x : Fin p → ℝ` form families of survival curves
(`Survival.ContinuousTime.IsSurvivalFamily`); the population curve of an arm under a covariate
law `P` is `popSurvival P (S t)`, and its restricted mean up to `τ` is
`restrictedMean (popSurvival P (S t)) τ`. These are the continuous counterparts of the discrete
statements of `IndirectComparison.SurvivalTransport`.

**The restricted mean on the identity scale.** If the conditional restricted means follow an
anchored model on the identity scale almost surely under `P`,
`restrictedMean (S t x) τ = η_t(x)`, and the arms `b`, `c` share their effect modifiers, then
the marginal difference of the restricted means and the average conditional difference are both
`γ_b - γ_c` (`restrictedMean_sub_eq_of_shared`), so they are the same under every covariate law
with such a model (`restrictedMean_sub_transport_of_shared`). The model is stated almost surely
under the covariate law: a restricted mean lies in `[0, τ]`, so a model equation at every
covariate value forces every slope of the predictor to vanish
(`predictor_slope_eq_zero_of_forall`). The instance (`restrictedMean_shared_example`) has
prognostic slope `1/2` and shared interactions `1/2`.

**The log hazard ratio.** In a proportional hazards model with conditional hazards
`h₀(s) exp(η_t(x))` and shared effect modifiers, the conditional log hazard ratio of `b`
against `c` is `γ_b - γ_c` at every covariate value, so its average is the same under every
covariate law (`logHazardRatio_conditional_eq_of_shared`). The marginal log hazard ratio, the
logarithm of the ratio of the population hazards, is `γ_b - γ_c` under a point mass but differs
from it under every law under which `η_c` is not almost surely constant, when `γ_b ≠ γ_c`
(`logHazardRatio_marginal_ne_of_shared`). With hazards `1, 2` (control) and `2, 4` (treated) in
two equally likely strata, the marginal hazard ratio at time `log 2` is `9/5`, against `2` in
one stratum alone (`logHazardRatio_marginal_example`).

**The restricted mean reported from a log hazard model.** With the same hazards and the horizon
`log 2`, the conditional difference of the restricted means is `-1/8` in one stratum and `-9/64`
in the other; the average conditional difference and the marginal difference are `-17/128` under
equally likely strata and `-1/8` under the first stratum alone
(`restrictedMean_sub_not_transported_of_logHazard`).

## Main definitions

* `stepCurve`, `phCurve`, `phModel`.

## Main results

* `restrictedMean_sub_eq_of_shared`, `restrictedMean_sub_transport_of_shared`,
  `predictor_slope_eq_zero_of_forall`, `restrictedMean_shared_example`.
* `curveHazard_phCurve`, `logHazardRatio_conditional_eq_of_shared`,
  `logHazardRatio_marginal_ne_of_shared`, `logHazardRatio_marginal_example`,
  `logHazardRatio_marginal_ne_example`.
* `restrictedMean_phCurve_strata`, `restrictedMean_sub_not_transported_of_logHazard`.

## References

* P. Royston and M. K. B. Parmar, *Restricted mean survival time: an alternative to the hazard
  ratio for the design and analysis of randomized trials with a time-to-event outcome*, BMC
  Medical Research Methodology 13 (2013).
* M. A. Hernán, *The hazards of hazard ratios*, Epidemiology 21 (2010).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure Survival.ContinuousTime Bias.HazardMixture

/-! ### The restricted mean on the identity scale -/

section RestrictedMean

variable {ι : Type*} {p : ℕ}

/-- **The difference in restricted mean under shared effect modifiers, in continuous time.**
Let the conditional curves `S b x`, `S c x` of the arms `b`, `c` be families of survival curves,
`τ ≥ 0`, and `P` a covariate probability law. If the conditional restricted means up to `τ` are
`P`-almost surely the predictors `η_b`, `η_c` of an anchored model on the identity scale, and
`b`, `c` share their effect modifiers, then the difference of the restricted means of the two
population curves and the average conditional difference are both `γ_b - γ_c`. -/
theorem restrictedMean_sub_eq_of_shared {S : ι → (Fin p → ℝ) → ℝ → ℝ} {b c : ι}
    (hSb : IsSurvivalFamily (S b)) (hSc : IsSurvivalFamily (S c)) {τ : ℝ} (hτ : 0 ≤ τ)
    {M : AnchoredModel ι p} {E : Set ι} (hE : M.SharedEffectModifiers E) (hb : b ∈ E)
    (hc : c ∈ E) (P : Measure (Fin p → ℝ)) [IsProbabilityMeasure P]
    (hmb : ∀ᵐ x ∂P, restrictedMean (S b x) τ = M.predictor b x)
    (hmc : ∀ᵐ x ∂P, restrictedMean (S c x) τ = M.predictor c x) :
    restrictedMean (popSurvival P (S b)) τ - restrictedMean (popSurvival P (S c)) τ =
        M.γ b - M.γ c ∧
      linkConditional id P (fun x => restrictedMean (S c x) τ)
          (fun x => restrictedMean (S b x) τ) = M.γ b - M.γ c := by
  have hd : ∀ᵐ x ∂P, restrictedMean (S b x) τ - restrictedMean (S c x) τ = M.γ b - M.γ c := by
    filter_upwards [hmb, hmc] with x hxb hxc
    rw [hxb, hxc, AnchoredModel.predictor_sub_of_shared hE hb hc]
  have hm := restrictedMean_popSurvival_sub_of_ae_eq hSc hSb P hτ hd
  exact ⟨hm, (restrictedMean_popSurvival_sub hSc hSb P hτ).2.2 ▸ hm⟩

/-- **The difference in restricted mean transports under shared effect modifiers, in continuous
time.** If the conditional restricted means of the arms `b`, `c`, which share their effect
modifiers, follow one anchored model on the identity scale almost surely under the covariate
probability laws `P` and `Q`, then the marginal differences of the restricted means are equal,
and so are the average conditional differences. -/
theorem restrictedMean_sub_transport_of_shared {S : ι → (Fin p → ℝ) → ℝ → ℝ} {b c : ι}
    (hSb : IsSurvivalFamily (S b)) (hSc : IsSurvivalFamily (S c)) {τ : ℝ} (hτ : 0 ≤ τ)
    {M : AnchoredModel ι p} {E : Set ι} (hE : M.SharedEffectModifiers E) (hb : b ∈ E)
    (hc : c ∈ E) (P Q : Measure (Fin p → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hmb : ∀ᵐ x ∂P, restrictedMean (S b x) τ = M.predictor b x)
    (hmc : ∀ᵐ x ∂P, restrictedMean (S c x) τ = M.predictor c x)
    (hmb' : ∀ᵐ x ∂Q, restrictedMean (S b x) τ = M.predictor b x)
    (hmc' : ∀ᵐ x ∂Q, restrictedMean (S c x) τ = M.predictor c x) :
    restrictedMean (popSurvival P (S b)) τ - restrictedMean (popSurvival P (S c)) τ =
        restrictedMean (popSurvival Q (S b)) τ - restrictedMean (popSurvival Q (S c)) τ ∧
      linkConditional id P (fun x => restrictedMean (S c x) τ)
          (fun x => restrictedMean (S b x) τ) =
        linkConditional id Q (fun x => restrictedMean (S c x) τ)
          (fun x => restrictedMean (S b x) τ) := by
  obtain ⟨h1, h2⟩ := restrictedMean_sub_eq_of_shared hSb hSc hτ hE hb hc P hmb hmc
  obtain ⟨h1', h2'⟩ := restrictedMean_sub_eq_of_shared hSb hSc hτ hE hb hc Q hmb' hmc'
  exact ⟨h1.trans h1'.symm, h2.trans h2'.symm⟩

/-- An affine function `a + ∑ⱼ xⱼ kⱼ` of `x : Fin p → ℝ` with values in `[0, τ]` at every `x`
has every slope `kⱼ = 0`. -/
theorem slope_eq_zero_of_bounded {a τ : ℝ} {k : Fin p → ℝ}
    (h : ∀ x : Fin p → ℝ, 0 ≤ a + ∑ j, x j * k j ∧ a + ∑ j, x j * k j ≤ τ) (j : Fin p) :
    k j = 0 := by
  have hl : ∀ u : ℝ, 0 ≤ a + u * k j ∧ a + u * k j ≤ τ := fun u => by
    have := h (Pi.single j u)
    simpa [Pi.single_apply] using this
  by_contra hk
  have h1 := (hl ((τ + 1 - a) / k j)).2
  rw [div_mul_cancel₀ _ hk] at h1
  linarith

/-- **A model equation at every covariate value forces zero slopes.** If the conditional
restricted means of a family of survival curves are the predictor `η_t` of an anchored model at
every covariate value, then `η_t` does not depend on the covariates: `β₁ j + β₂ t j = 0` for
every `j`. This is why the model equation of `restrictedMean_sub_eq_of_shared` is required only
almost surely under the covariate law. -/
theorem predictor_slope_eq_zero_of_forall {S : (Fin p → ℝ) → ℝ → ℝ} (hS : IsSurvivalFamily S)
    {τ : ℝ} (hτ : 0 ≤ τ) {M : AnchoredModel ι p} {t : ι}
    (hm : ∀ x, restrictedMean (S x) τ = M.predictor t x) (j : Fin p) :
    M.β₁ j + M.β₂ t j = 0 := by
  have h : ∀ x : Fin p → ℝ, 0 ≤ (M.α + M.γ t) + ∑ j, x j * (M.β₁ j + M.β₂ t j) ∧
      (M.α + M.γ t) + ∑ j, x j * (M.β₁ j + M.β₂ t j) ≤ τ := fun x => by
    have e : (M.α + M.γ t) + ∑ j, x j * (M.β₁ j + M.β₂ t j) = M.predictor t x := by
      simp only [AnchoredModel.predictor, anchoredPredictor, mul_add, Finset.sum_add_distrib]
      ring
    rw [e, ← hm x]
    exact ⟨restrictedMean_nonneg (hS.nonneg x) hτ,
      restrictedMean_le (hS.isSurvivalCurve x) hτ⟩
  exact slope_eq_zero_of_bounded h j

/-- The conditional curves of the restricted mean instance: an event at the time
`max 0 (η_t(x))`, with `η_t` the predictor of `rmstModel`. -/
noncomputable def stepCurve (t : Fin 3) (x : Fin 1 → ℝ) (s : ℝ) : ℝ :=
  stepSurvival (max 0 (rmstModel.predictor t x)) s

/-- The linear predictor of an anchored model is measurable. -/
theorem measurable_predictor (M : AnchoredModel ι p) (t : ι) : Measurable (M.predictor t) := by
  unfold AnchoredModel.predictor anchoredPredictor; fun_prop

theorem isSurvivalFamily_stepCurve (t : Fin 3) : IsSurvivalFamily (stepCurve t) := by
  refine ⟨Measurable.ite (measurableSet_lt measurable_snd
    ((measurable_const.max (measurable_predictor rmstModel t)).comp measurable_fst))
    measurable_const measurable_const, fun x s _ => ?_, fun x s _ => ?_⟩ <;>
  · simp only [stepCurve, stepSurvival]; split_ifs <;> norm_num

/-- Where the predictor lies in `[0, 4]`, the restricted mean of the step curve up to `4` is the
predictor. -/
theorem restrictedMean_stepCurve {t : Fin 3} {x : Fin 1 → ℝ}
    (h : 0 ≤ rmstModel.predictor t x ∧ rmstModel.predictor t x ≤ 4) :
    restrictedMean (stepCurve t x) 4 = rmstModel.predictor t x := by
  rw [show stepCurve t x = stepSurvival (max 0 (rmstModel.predictor t x)) from rfl,
    restrictedMean_stepSurvival (le_max_left _ _) (by norm_num),
    max_eq_right h.1, min_eq_left h.2]

theorem rmstModel_predictor_signCov (t : Fin 3) (v : Bool) :
    0 ≤ rmstModel.predictor t (signCov v) ∧ rmstModel.predictor t (signCov v) ≤ 4 := by
  fin_cases t <;> cases v <;>
    norm_num [AnchoredModel.predictor, anchoredPredictor, signCov, rmstModel]

/-- The model equation of the instance holds under every law carried by `±1`. -/
theorem stepCurve_ae_signLaw (t : Fin 3) :
    ∀ᵐ x ∂signLaw, restrictedMean (stepCurve t x) 4 = rmstModel.predictor t x := by
  have hset : MeasurableSet
      {x : Fin 1 → ℝ | 0 ≤ rmstModel.predictor t x ∧ rmstModel.predictor t x ≤ 4} :=
    (measurableSet_le measurable_const (measurable_predictor rmstModel t)).inter
      (measurableSet_le (measurable_predictor rmstModel t) measurable_const)
  have h : ∀ᵐ x ∂signLaw, 0 ≤ rmstModel.predictor t x ∧ rmstModel.predictor t x ≤ 4 :=
    (ae_map_iff (measurable_of_finite signCov).aemeasurable hset).2
      (ae_halfLaw_iff.2 fun v => rmstModel_predictor_signCov t v)
  exact h.mono fun x hx => restrictedMean_stepCurve hx

theorem stepCurve_ae_dirac (t : Fin 3) :
    ∀ᵐ x ∂(Measure.dirac (signCov true)),
      restrictedMean (stepCurve t x) 4 = rmstModel.predictor t x := by
  rw [ae_dirac_eq, Filter.eventually_pure]
  exact restrictedMean_stepCurve (rmstModel_predictor_signCov t true)

/-- **An instance with a nonzero slope and nonzero shared interactions.** The model
`rmstModel` has prognostic slope `1/2` and interactions `1/2` for the treatments `1`, `2`, which
share their effect modifiers. The step curves `stepCurve t` have conditional restricted means up
to `4` equal to the predictors under the law `signLaw` of two equally likely strata at `∓1`
and under the point mass at `1`. The difference of the restricted means of the population
curves of `2` and `1` is `1 = γ_2 - γ_1` under both laws, while the difference of `1` and the
reference `0`, whose interactions differ, is `1/2` under the first and `1` under the second.
The average conditional differences of `2` and `1` agree under the two laws
(`restrictedMean_sub_transport_of_shared`). -/
theorem restrictedMean_shared_example :
    rmstModel.β₁ 0 = 1 / 2 ∧ rmstModel.β₂ 1 = rmstModel.β₂ 2 ∧ rmstModel.β₂ 1 0 = 1 / 2 ∧
      restrictedMean (popSurvival signLaw (stepCurve 2)) 4 -
          restrictedMean (popSurvival signLaw (stepCurve 1)) 4 = 1 ∧
      restrictedMean (popSurvival (Measure.dirac (signCov true)) (stepCurve 2)) 4 -
          restrictedMean (popSurvival (Measure.dirac (signCov true)) (stepCurve 1)) 4 = 1 ∧
      restrictedMean (popSurvival signLaw (stepCurve 1)) 4 -
          restrictedMean (popSurvival signLaw (stepCurve 0)) 4 = 1 / 2 ∧
      restrictedMean (popSurvival (Measure.dirac (signCov true)) (stepCurve 1)) 4 -
          restrictedMean (popSurvival (Measure.dirac (signCov true)) (stepCurve 0)) 4 = 1 ∧
      linkConditional id signLaw (fun x => restrictedMean (stepCurve 1 x) 4)
          (fun x => restrictedMean (stepCurve 2 x) 4) =
        linkConditional id (Measure.dirac (signCov true))
          (fun x => restrictedMean (stepCurve 1 x) 4)
          (fun x => restrictedMean (stepCurve 2 x) 4) := by
  have hE : rmstModel.SharedEffectModifiers {1, 2} := by
    intro b hb c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
    rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl
  have hγ : rmstModel.γ 2 - rmstModel.γ 1 = 1 := by norm_num [rmstModel]
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have hS := isSurvivalFamily_stepCurve
  refine ⟨by norm_num [rmstModel], rfl, by norm_num [rmstModel], ?_, ?_, ?_, ?_,
    (restrictedMean_sub_transport_of_shared (hS 2) (hS 1) h4 hE (by simp) (by simp) signLaw _
      (stepCurve_ae_signLaw 2) (stepCurve_ae_signLaw 1) (stepCurve_ae_dirac 2)
      (stepCurve_ae_dirac 1)).2⟩
  · rw [(restrictedMean_sub_eq_of_shared (hS 2) (hS 1) h4 hE (by simp) (by simp) signLaw
      (stepCurve_ae_signLaw 2) (stepCurve_ae_signLaw 1)).1, hγ]
  · rw [(restrictedMean_sub_eq_of_shared (hS 2) (hS 1) h4 hE (by simp) (by simp) _
      (stepCurve_ae_dirac 2) (stepCurve_ae_dirac 1)).1, hγ]
  · rw [(restrictedMean_popSurvival_sub (hS 0) (hS 1) signLaw h4).1]
    have he : ∀ᵐ x ∂signLaw, restrictedMean (stepCurve 1 x) 4 - restrictedMean (stepCurve 0 x) 4
        = rmstModel.predictor 1 x - rmstModel.predictor 0 x := by
      filter_upwards [stepCurve_ae_signLaw 1, stepCurve_ae_signLaw 0] with x h1 h0
      rw [h1, h0]
    rw [integral_congr_ae he, integral_signLaw
      (f := fun x => rmstModel.predictor 1 x - rmstModel.predictor 0 x)
      ((measurable_predictor rmstModel 1).sub (measurable_predictor rmstModel 0))]
    norm_num [AnchoredModel.predictor, anchoredPredictor, signCov, rmstModel]
  · rw [(restrictedMean_popSurvival_sub (hS 0) (hS 1) _ h4).1, integral_dirac,
      restrictedMean_stepCurve (rmstModel_predictor_signCov 1 true),
      restrictedMean_stepCurve (rmstModel_predictor_signCov 0 true)]
    norm_num [AnchoredModel.predictor, anchoredPredictor, signCov, rmstModel]

end RestrictedMean

/-! ### The log hazard ratio -/

section LogHazard

variable {ι : Type*} {p : ℕ}

/-- The conditional curves of a **proportional hazards model on the log hazard scale**: the
arm `t` has conditional hazard `h₀(s) exp(η_t(x))`, with `η_t` the predictor of the anchored
model `M` and `Λ₀` the baseline cumulative hazard. -/
noncomputable def phCurve (M : AnchoredModel ι p) (Λ₀ : ℝ → ℝ) (t : ι) :
    (Fin p → ℝ) → ℝ → ℝ :=
  phSurvival Λ₀ (fun x => Real.exp (M.predictor t x))

theorem isSurvivalFamily_phCurve (M : AnchoredModel ι p) {Λ₀ : ℝ → ℝ} (hΛ : Measurable Λ₀)
    (hΛ0 : ∀ s, 0 ≤ s → 0 ≤ Λ₀ s) (t : ι) : IsSurvivalFamily (phCurve M Λ₀ t) :=
  isSurvivalFamily_phSurvival (measurable_predictor M t).exp (fun _ => (Real.exp_pos _).le) hΛ
    hΛ0

/-- The conditional hazard of the arm `t` at a time where `Λ₀` has derivative `h₀` is
`exp(η_t(x)) h₀`. -/
theorem curveHazard_phCurve (M : AnchoredModel ι p) {Λ₀ : ℝ → ℝ} {h₀ s : ℝ}
    (hΛ : HasDerivAt Λ₀ h₀ s) (t : ι) (x : Fin p → ℝ) :
    curveHazard (phCurve M Λ₀ t x) s = Real.exp (M.predictor t x) * h₀ :=
  curveHazard_phSurvival hΛ _ x

/-- **The conditional log hazard ratio transports under shared effect modifiers.** In the
proportional hazards model `phCurve M Λ₀`, at a time where `Λ₀` has derivative `h₀ > 0`, the
conditional log hazard ratio of the arms `b`, `c` sharing their effect modifiers is
`γ_b - γ_c` at every covariate value, so its average is `γ_b - γ_c` under every covariate
probability law. -/
theorem logHazardRatio_conditional_eq_of_shared {M : AnchoredModel ι p} {E : Set ι}
    (hE : M.SharedEffectModifiers E) {b c : ι} (hb : b ∈ E) (hc : c ∈ E) {Λ₀ : ℝ → ℝ}
    {h₀ s : ℝ} (hΛ : HasDerivAt Λ₀ h₀ s) (hh₀ : 0 < h₀) :
    (∀ x, linkContrast Real.log (fun x => curveHazard (phCurve M Λ₀ c x) s)
        (fun x => curveHazard (phCurve M Λ₀ b x) s) x = M.γ b - M.γ c) ∧
      ∀ (P : Measure (Fin p → ℝ)) [IsProbabilityMeasure P],
        linkConditional Real.log P (fun x => curveHazard (phCurve M Λ₀ c x) s)
          (fun x => curveHazard (phCurve M Λ₀ b x) s) = M.γ b - M.γ c := by
  have h : ∀ x, linkContrast Real.log (fun x => curveHazard (phCurve M Λ₀ c x) s)
      (fun x => curveHazard (phCurve M Λ₀ b x) s) x = M.γ b - M.γ c := fun x => by
    simp only [linkContrast, curveHazard_phCurve M hΛ]
    rw [Real.log_mul (Real.exp_pos _).ne' hh₀.ne', Real.log_mul (Real.exp_pos _).ne' hh₀.ne',
      Real.log_exp, Real.log_exp]
    linarith [AnchoredModel.predictor_sub_of_shared hE hb hc x]
  refine ⟨h, fun P _ => ?_⟩
  simp [linkConditional, h]

/-- Under shared effect modifiers the relative hazard of `b` is `exp(γ_b - γ_c)` times the
relative hazard of `c`. -/
theorem phCurve_eq_of_shared {M : AnchoredModel ι p} {E : Set ι}
    (hE : M.SharedEffectModifiers E) {b c : ι} (hb : b ∈ E) (hc : c ∈ E) (Λ₀ : ℝ → ℝ) :
    phCurve M Λ₀ b =
      phSurvival Λ₀ (fun x => Real.exp (M.γ b - M.γ c) * Real.exp (M.predictor c x)) := by
  funext x s
  have key : Real.exp (M.predictor b x) =
      Real.exp (M.γ b - M.γ c) * Real.exp (M.predictor c x) := by
    rw [← Real.exp_add]
    congr 1
    linarith [AnchoredModel.predictor_sub_of_shared hE hb hc x]
  simp only [phCurve, phSurvival, key]

/-- **The marginal log hazard ratio does not transport under shared effect modifiers.** In the
proportional hazards model `phCurve M Λ₀`, let `b`, `c` share their effect modifiers with
`γ_b ≠ γ_c`, and take a time with `Λ₀ s > 0` at which `Λ₀` has derivative `h₀ > 0`. The marginal
log hazard ratio, the logarithm of the ratio of the population hazards, is `γ_b - γ_c` under
every point mass, and differs from `γ_b - γ_c` under every covariate probability law under which
`η_c` is not almost surely constant. -/
theorem logHazardRatio_marginal_ne_of_shared {M : AnchoredModel ι p} {E : Set ι}
    (hE : M.SharedEffectModifiers E) {b c : ι} (hb : b ∈ E) (hc : c ∈ E) (hγ : M.γ b ≠ M.γ c)
    {Λ₀ : ℝ → ℝ} {h₀ s : ℝ} (hΛ : HasDerivAt Λ₀ h₀ s) (hΛs : 0 < Λ₀ s) (hh₀ : 0 < h₀)
    (P : Measure (Fin p → ℝ)) [IsProbabilityMeasure P]
    (hnc : ¬ ∃ a, ∀ᵐ x ∂P, M.predictor c x = a) (x₀ : Fin p → ℝ) :
    Real.log (popHazard (Measure.dirac x₀) (phCurve M Λ₀ b) s /
        popHazard (Measure.dirac x₀) (phCurve M Λ₀ c) s) = M.γ b - M.γ c ∧
      Real.log (popHazard P (phCurve M Λ₀ b) s / popHazard P (phCurve M Λ₀ c) s) ≠
        M.γ b - M.γ c := by
  have hρ : Measurable fun x => Real.exp (M.predictor c x) := (measurable_predictor M c).exp
  have hnc' : ¬ ∃ a, ∀ᵐ x ∂P, Real.exp (M.predictor c x) = a := by
    rintro ⟨a, ha⟩
    exact hnc ⟨Real.log a, ha.mono fun x hx => by rw [← hx, Real.log_exp]⟩
  have hψ1 : Real.exp (M.γ b - M.γ c) ≠ 1 := fun h =>
    hγ (by linarith [Real.exp_eq_one_iff (M.γ b - M.γ c) |>.1 h])
  obtain ⟨h1, h2⟩ := popHazard_ratio_ne_dirac hρ (fun x => Real.exp_pos _) hnc'
    (Real.exp_pos _) hψ1 hΛ hΛs hh₀ x₀
  have ec : phCurve M Λ₀ c = phSurvival Λ₀ (fun x => Real.exp (M.predictor c x)) := rfl
  rw [phCurve_eq_of_shared hE hb hc, ec]
  refine ⟨by rw [h1, Real.log_exp], fun h => h2 ?_⟩
  have hpos := div_pos
    (popHazard_pos (ν := P) (hρ.const_mul (Real.exp (M.γ b - M.γ c)))
      (Filter.Eventually.of_forall fun x => mul_pos (Real.exp_pos _) (Real.exp_pos _)) hΛ hΛs hh₀)
    (popHazard_pos (ν := P) hρ (Filter.Eventually.of_forall fun x => Real.exp_pos _) hΛ hΛs hh₀)
  rw [← Real.exp_log hpos, h]

/-- The model of the counterexamples, on one covariate for the arms `false` (control) and `true`
(treated): intercept `0`, prognostic slope `log 2`, relative effect `log 2` for the treated arm
and no interactions, so the two arms share their effect modifiers. -/
noncomputable def phModel : AnchoredModel Bool 1 :=
  ⟨0, fun _ => Real.log 2, fun a => if a then Real.log 2 else 0, fun _ => 0⟩

/-- The covariate law of two equally likely strata at the covariate values `0` and `1`. -/
noncomputable def strataLaw : Measure (Fin 1 → ℝ) := halfLaw.map strataCov

instance : IsProbabilityMeasure strataLaw := by unfold strataLaw; infer_instance

/-- The hazard of the arm `a` in the stratum `u` of `phModel`, under the unit baseline. -/
def phRate (a u : Bool) : ℕ := (if a then 2 else 1) * (if u then 2 else 1)

/-- The relative hazards of `phModel` on the strata: `1`, `2` for the control arm and `2`, `4`
for the treated arm. -/
theorem exp_phModel_predictor (a u : Bool) :
    Real.exp (phModel.predictor a (strataCov u)) = (phRate a u : ℝ) := by
  have e : Real.exp (Real.log 2 + Real.log 2) = 4 := by
    rw [Real.exp_add, Real.exp_log two_pos]; norm_num
  cases a <;> cases u <;>
    simp [phModel, AnchoredModel.predictor, anchoredPredictor, strataCov, phRate, e,
      Real.exp_log two_pos]

theorem shared_phModel : phModel.SharedEffectModifiers Set.univ := fun _ _ _ _ => rfl

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

/-- The population hazards of `phModel` under `strataLaw` at the time `log 2`, with the unit
baseline: `4/3` for the control arm and `12/5` for the treated arm. -/
theorem popHazard_phModel_strataLaw (a : Bool) :
    popHazard strataLaw (phCurve phModel id a) (Real.log 2) = if a then 12 / 5 else 4 / 3 := by
  rw [strataLaw, popHazard_map (isSurvivalFamily_phCurve phModel measurable_id
    (fun s hs => hs) a).measurable (measurable_of_finite strataCov)]
  change popHazard halfLaw (phSurvival id fun u => Real.exp (phModel.predictor a (strataCov u)))
    (Real.log 2) = _
  rw [popHazard_stratumLaw isWeights_half]
  have hr : (fun u => Real.exp (phModel.predictor a (strataCov u))) =
      fun u => (phRate a u : ℝ) := funext (exp_phModel_predictor a)
  rw [hr]
  simp only [mixHazard, mixDensity, mixSurvival, Fintype.sum_bool, exp_neg_mul_log_two]
  cases a <;> norm_num [phRate]

/-- **The marginal hazard ratio depends on the covariate law: numbers.** In `phModel` with the
unit baseline the conditional hazards are `1`, `2` (control) and `2`, `4` (treated) on the
strata `0`, `1`, so the conditional log hazard ratio is `log 2` at every covariate value. At the
time `log 2` the population hazards under `strataLaw` are `4/3` and `12/5`, with ratio `9/5`;
under the point mass at the stratum `0` the ratio is `2`. The marginal log hazard ratios
`log (9/5)` and `log 2` differ. -/
theorem logHazardRatio_marginal_example :
    (∀ x, linkContrast Real.log (fun x => curveHazard (phCurve phModel id false x) (Real.log 2))
        (fun x => curveHazard (phCurve phModel id true x) (Real.log 2)) x = Real.log 2) ∧
      popHazard strataLaw (phCurve phModel id false) (Real.log 2) = 4 / 3 ∧
      popHazard strataLaw (phCurve phModel id true) (Real.log 2) = 12 / 5 ∧
      popHazard strataLaw (phCurve phModel id true) (Real.log 2) /
          popHazard strataLaw (phCurve phModel id false) (Real.log 2) = 9 / 5 ∧
      popHazard (Measure.dirac (strataCov false)) (phCurve phModel id true) (Real.log 2) /
          popHazard (Measure.dirac (strataCov false)) (phCurve phModel id false)
            (Real.log 2) = 2 ∧
      Real.log (9 / 5) ≠ Real.log 2 := by
  have hc := (logHazardRatio_conditional_eq_of_shared shared_phModel (Set.mem_univ true)
    (Set.mem_univ false) (hasDerivAt_id (Real.log 2)) one_pos).1
  have hγ : phModel.γ true - phModel.γ false = Real.log 2 := by simp [phModel]
  refine ⟨fun x => (hc x).trans hγ, by simpa using popHazard_phModel_strataLaw false,
    by simpa using popHazard_phModel_strataLaw true, ?_, ?_, ?_⟩
  · rw [popHazard_phModel_strataLaw, popHazard_phModel_strataLaw]
    norm_num
  · rw [popHazard_dirac, popHazard_dirac, curveHazard_phCurve _ (hasDerivAt_id _),
      curveHazard_phCurve _ (hasDerivAt_id _), exp_phModel_predictor, exp_phModel_predictor]
    norm_num [phRate]
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.2 (by norm_num : (0 : ℝ) < 9 / 5))
      (Set.mem_Ioi.2 two_pos) h
    norm_num at this

/-- The predictor of either arm of `phModel` is not almost surely constant under
`strataLaw`. -/
theorem not_ae_const_phModel (a : Bool) :
    ¬ ∃ c, ∀ᵐ x ∂strataLaw, phModel.predictor a x = c := by
  rintro ⟨c, hc⟩
  have h := ae_halfLaw_iff.1 (ae_of_ae_map (measurable_of_finite strataCov).aemeasurable hc)
  have h1 := h true
  have h0 := h false
  have := log_two_pos'
  cases a <;> simp [phModel, AnchoredModel.predictor, anchoredPredictor, strataCov] at h1 h0 <;>
    linarith

/-- **The general statement applies to the example**: every hypothesis of
`logHazardRatio_marginal_ne_of_shared` holds for `phModel` under `strataLaw` at the time
`log 2`, for the treated arm against the control arm (`ψ = 2 > 1`) and for the control arm
against the treated arm (`ψ = 1/2 < 1`). -/
theorem logHazardRatio_marginal_ne_example :
    Real.log (popHazard strataLaw (phCurve phModel id true) (Real.log 2) /
        popHazard strataLaw (phCurve phModel id false) (Real.log 2)) ≠ Real.log 2 ∧
      Real.log (popHazard strataLaw (phCurve phModel id false) (Real.log 2) /
        popHazard strataLaw (phCurve phModel id true) (Real.log 2)) ≠ -Real.log 2 := by
  have hγ1 : phModel.γ true ≠ phModel.γ false := by simp [phModel, log_two_pos'.ne']
  have h1 := (logHazardRatio_marginal_ne_of_shared shared_phModel (Set.mem_univ true)
    (Set.mem_univ false) hγ1 (hasDerivAt_id _) log_two_pos' one_pos strataLaw
    (not_ae_const_phModel false) (strataCov false)).2
  have h2 := (logHazardRatio_marginal_ne_of_shared shared_phModel (Set.mem_univ false)
    (Set.mem_univ true) hγ1.symm (hasDerivAt_id _) log_two_pos' one_pos strataLaw
    (not_ae_const_phModel true) (strataCov false)).2
  simp only [phModel, ite_true, ite_false, Bool.false_eq_true, sub_zero, zero_sub] at h1 h2
  exact ⟨h1, h2⟩

end LogHazard

/-! ### The restricted mean reported from a log hazard model -/

section LogHazardRMST

/-- The conditional restricted means of `phModel` up to the horizon `log 2`, with the unit
baseline: `1/2`, `3/8` for the control arm and `3/8`, `15/64` for the treated arm on the
strata `0`, `1`. -/
theorem restrictedMean_phCurve_strata (a u : Bool) :
    restrictedMean (phCurve phModel id a (strataCov u)) (Real.log 2) =
      (1 - 1 / 2 ^ phRate a u) / (phRate a u : ℝ) := by
  have hpos : (0 : ℝ) < phRate a u := by cases a <;> cases u <;> norm_num [phRate]
  rw [show phCurve phModel id a (strataCov u) =
      fun s => Real.exp (-(Real.exp (phModel.predictor a (strataCov u)) * s)) from rfl,
    exp_phModel_predictor, restrictedMean_exp_mul hpos.ne', exp_neg_mul_log_two]

/-- **The difference in restricted mean from a log hazard model does not transport.** In
`phModel` with the unit baseline (conditional hazards `1`, `2` for the control arm and `2`,
`4` for the treated arm, a log hazard model with shared effect modifiers,
`logHazardRatio_marginal_example`), the conditional difference of the restricted means up to
`log 2` is `-1/8` in the stratum `0` and `-9/64` in the stratum `1`. Hence the average
conditional difference and the marginal difference of the restricted means of the population
curves are `-17/128` under `strataLaw` and `-1/8` under the point mass at the stratum `0`. -/
theorem restrictedMean_sub_not_transported_of_logHazard :
    linkConditional id strataLaw (fun x => restrictedMean (phCurve phModel id false x) (Real.log 2))
        (fun x => restrictedMean (phCurve phModel id true x) (Real.log 2)) = -17 / 128 ∧
      linkConditional id (Measure.dirac (strataCov false))
          (fun x => restrictedMean (phCurve phModel id false x) (Real.log 2))
          (fun x => restrictedMean (phCurve phModel id true x) (Real.log 2)) = -1 / 8 ∧
      restrictedMean (popSurvival strataLaw (phCurve phModel id true)) (Real.log 2) -
          restrictedMean (popSurvival strataLaw (phCurve phModel id false)) (Real.log 2) =
        -17 / 128 ∧
      restrictedMean (popSurvival (Measure.dirac (strataCov false)) (phCurve phModel id true))
            (Real.log 2) -
          restrictedMean (popSurvival (Measure.dirac (strataCov false))
            (phCurve phModel id false)) (Real.log 2) = -1 / 8 := by
  have hS := isSurvivalFamily_phCurve phModel measurable_id (fun s hs => hs)
  have hτ := log_two_pos'.le
  have hP : linkConditional id strataLaw
      (fun x => restrictedMean (phCurve phModel id false x) (Real.log 2))
      (fun x => restrictedMean (phCurve phModel id true x) (Real.log 2)) = -17 / 128 := by
    have hm : AEStronglyMeasurable (fun x =>
        restrictedMean (phCurve phModel id true x) (Real.log 2) -
          restrictedMean (phCurve phModel id false x) (Real.log 2)) (halfLaw.map strataCov) :=
      ((integrable_restrictedMean (hS true) _ hτ).sub
        (integrable_restrictedMean (hS false) _ hτ)).aestronglyMeasurable
    simp only [linkConditional, linkContrast, id]
    rw [strataLaw, integral_map (measurable_of_finite strataCov).aemeasurable hm, integral_halfLaw,
      restrictedMean_phCurve_strata, restrictedMean_phCurve_strata,
      restrictedMean_phCurve_strata, restrictedMean_phCurve_strata]
    norm_num [phRate]
  have hQ : linkConditional id (Measure.dirac (strataCov false))
      (fun x => restrictedMean (phCurve phModel id false x) (Real.log 2))
      (fun x => restrictedMean (phCurve phModel id true x) (Real.log 2)) = -1 / 8 := by
    simp only [linkConditional, linkContrast, id]
    rw [integral_dirac, restrictedMean_phCurve_strata, restrictedMean_phCurve_strata]
    norm_num [phRate]
  refine ⟨hP, hQ, ?_, ?_⟩
  · rw [(restrictedMean_popSurvival_sub (hS false) (hS true) strataLaw hτ).2.2, hP]
  · rw [(restrictedMean_popSurvival_sub (hS false) (hS true) _ hτ).2.2, hQ]

end LogHazardRMST

end IndirectComparison

end CausalInference
