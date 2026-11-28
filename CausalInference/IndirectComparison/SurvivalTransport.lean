/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.IndirectComparison.AnchoredPredictor
public import CausalInference.IndirectComparison.Constancy
public import CausalInference.Transport.Survival
public import CausalInference.Survival.Comparison

/-!
# Survival effects under shared effect modifiers, in discrete time

Survival times are discrete, `T(t) : Ω → ℕ`, and the restricted mean survival time up to the
horizon `τ` is `rmst μ T τ = E[min(T, τ)]` (`Survival.rmst`, `Survival.rmst_eq_integral_min`).

**The restricted mean on the identity scale.** A population whose outcome of arm `t` is
`min(T(t), τ)` (`rmstPopulation`) has the restricted means as arm means
(`rmstPopulation_armMean`). If the conditional restricted means follow an anchored model on the
identity scale, `E[min(T(t), τ) | X] = η_t(X)` almost surely (`Population.IsCondMean`), and the
arms `b`, `c` share their effect modifiers, then both the average conditional difference and the
marginal difference of the restricted means are `γ_b - γ_c` (`rmst_sub_eq_of_shared`), so they
are the same in every population with such a model (`rmst_sub_transport_of_shared`). The model is
stated almost surely under the covariate law: a conditional restricted mean lies in `[0, τ]`, so a
linear predictor with a nonzero slope can be a conditional restricted mean only on a bounded
covariate support. The instance (`rmst_shared_example`) has prognostic slope `1/2` and shared
interactions `1/2`; the difference of the two arms sharing their modifiers is `1` in two
populations, while the difference against the reference, whose modifier differs, is `1/2` in one
and `1` in the other.

**The hazard ratio.** Discrete stratum hazards following an anchored model on the log hazard
scale with shared effect modifiers have a conditional log hazard ratio equal to the difference of
the relative effects at every covariate value (`logHazardModel_example`), but the marginal log
hazard ratio of the same stratum hazards differs between populations
(`Transport.marginal_hazardRatio_not_transportable`).

**The restricted mean reported from a log hazard model.** Under the same stratum hazards, with
event times on `{1, 2, 3}` and hazard `h` at times `1` and `2` (`hazardArm`), the conditional
difference of the restricted means up to `3` is `57/400` in one stratum and `9/16` in the other
(`rmst_sub_not_transported_of_logHazard`): reported on the restricted mean scale, a log hazard
model with shared effect modifiers transports neither the average conditional nor the marginal
difference.

## Main definitions

* `rmstPopulation`, `rmstModel`, `logHazardModel`, `hazardArm`.

## Main results

* `rmstPopulation_armMean`, `rmst_sub_eq_of_shared`, `rmst_sub_transport_of_shared`,
  `rmst_shared_example`.
* `logHazardModel_example`, `hazard_hazardArm`, `rmst_hazardArm`,
  `rmst_sub_not_transported_of_logHazard`.

## References

* P. Royston and M. K. B. Parmar, *Restricted mean survival time: an alternative to the hazard
  ratio for the design and analysis of randomized trials with a time-to-event outcome*, BMC
  Medical Research Methodology 13 (2013).
* M. A. Hernán, *The hazards of hazard ratios*, Epidemiology 21 (2010).
-/

@[expose] public section

namespace CausalInference

namespace IndirectComparison

open MeasureTheory ProbabilityTheory EffectMeasure Survival

/-! ### The restricted mean on the identity scale -/

section RMST

variable {Ω ι : Type*} [MeasurableSpace Ω] {p : ℕ}

/-- The **restricted mean population** of survival times `T(t)` at the horizon `τ`: the outcome
of the arm `t` is `min(T(t), τ)`. -/
noncomputable def rmstPopulation {𝒳 : Type*} (μ : Measure Ω) (X : Ω → 𝒳) (T : ι → Ω → ℕ)
    (τ : ℕ) : Population Ω 𝒳 ι :=
  ⟨μ, X, fun t => Transport.truncTime (T t) τ⟩

instance {𝒳 : Type*} {μ : Measure Ω} [h : IsProbabilityMeasure μ] {X : Ω → 𝒳}
    {T : ι → Ω → ℕ} {τ : ℕ} : IsProbabilityMeasure (rmstPopulation μ X T τ).μ := h

instance {𝒳 : Type*} {μ : Measure Ω} [h : IsFiniteMeasure μ] {X : Ω → 𝒳}
    {T : ι → Ω → ℕ} {τ : ℕ} : IsFiniteMeasure (rmstPopulation μ X T τ).μ := h

/-- The arm means of the restricted mean population are the restricted means. -/
theorem rmstPopulation_armMean {𝒳 : Type*} {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → 𝒳}
    {T : ι → Ω → ℕ} {t : ι} (hT : Measurable (T t)) (τ : ℕ) :
    (rmstPopulation μ X T τ).armMean t = rmst μ (T t) τ :=
  (rmst_eq_integral_min hT τ).symm

/-- **The restricted mean difference under shared effect modifiers.** In a probability
population with measurable covariates and survival times, if the predictors `η_b`, `η_c` of an
anchored model on the identity scale are conditional restricted means of the arms `b`, `c` at
the horizon `τ`, and `b`, `c` share their effect modifiers, then the marginal difference of the
restricted means and the average conditional difference under the covariate law are both
`γ_b - γ_c`. -/
theorem rmst_sub_eq_of_shared {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin p → ℝ}
    (hX : Measurable X) {T : ι → Ω → ℕ} (hT : ∀ t, Measurable (T t)) {τ : ℕ}
    {M : AnchoredModel ι p} {S : Set ι} (hS : M.SharedEffectModifiers S) {b c : ι} (hb : b ∈ S)
    (hc : c ∈ S) (hmb : (rmstPopulation μ X T τ).IsCondMean b (M.predictor b))
    (hmc : (rmstPopulation μ X T τ).IsCondMean c (M.predictor c)) :
    rmst μ (T b) τ - rmst μ (T c) τ = M.γ b - M.γ c ∧
      linkConditional id (rmstPopulation μ X T τ).covLaw (M.predictor c) (M.predictor b) =
        M.γ b - M.γ c := by
  have := Population.isProbabilityMeasure_covLaw (P := rmstPopulation μ X T τ) hX
  have hY : ∀ t, Integrable ((rmstPopulation μ X T τ).Y t) (rmstPopulation μ X T τ).μ :=
    fun t => Transport.integrable_truncTime (hT t) τ
  refine ⟨?_, ?_⟩
  · rw [← rmstPopulation_armMean (X := X) (hT b), ← rmstPopulation_armMean (X := X) (hT c)]
    change (rmstPopulation μ X T τ).marginalEffect id c b = _
    rw [Population.marginalEffect_eq_linkMarginal id hX (hY c) (hY b) hmc hmb]
    exact linkMarginal_id_eq_of_shared hS hb hc _ (hmb.integrable hX) (hmc.integrable hX)
  · exact linkConditional_eq_of_shared (D := Set.univ) (g := id) (ginv := id) (fun _ _ => rfl)
      hS hb hc _ (Filter.Eventually.of_forall fun _ => ⟨⟨_, trivial, rfl⟩, ⟨_, trivial, rfl⟩⟩)

/-- **The restricted mean difference transports under shared effect modifiers.** If in two
probability populations the predictors of one anchored model on the identity scale are
conditional restricted means of the arms `b`, `c` sharing their effect modifiers, the marginal
differences of the restricted means at the horizon `τ` are equal. -/
theorem rmst_sub_transport_of_shared {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω}
    {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {X : Ω → Fin p → ℝ}
    {X' : Ω' → Fin p → ℝ} (hX : Measurable X) (hX' : Measurable X') {T : ι → Ω → ℕ}
    {T' : ι → Ω' → ℕ} (hT : ∀ t, Measurable (T t)) (hT' : ∀ t, Measurable (T' t)) {τ : ℕ}
    {M : AnchoredModel ι p} {S : Set ι} (hS : M.SharedEffectModifiers S) {b c : ι} (hb : b ∈ S)
    (hc : c ∈ S) (hmb : (rmstPopulation μ X T τ).IsCondMean b (M.predictor b))
    (hmc : (rmstPopulation μ X T τ).IsCondMean c (M.predictor c))
    (hmb' : (rmstPopulation μ' X' T' τ).IsCondMean b (M.predictor b))
    (hmc' : (rmstPopulation μ' X' T' τ).IsCondMean c (M.predictor c)) :
    rmst μ (T b) τ - rmst μ (T c) τ = rmst μ' (T' b) τ - rmst μ' (T' c) τ := by
  rw [(rmst_sub_eq_of_shared hX hT hS hb hc hmb hmc).1,
    (rmst_sub_eq_of_shared hX' hT' hS hb hc hmb' hmc').1]

end RMST

/-- The anchored model of the restricted mean instance, on one covariate for the treatments
`0, 1, 2`: intercept `3/2`, prognostic slope `1/2`, relative effects `(0, 1/2, 3/2)` and
interactions `(0, 1/2, 1/2)`; the treatments `1`, `2` share their effect modifiers. -/
noncomputable def rmstModel : AnchoredModel (Fin 3) 1 :=
  ⟨3 / 2, fun _ => 1 / 2, ![0, 1 / 2, 3 / 2], ![0, fun _ => 1 / 2, fun _ => 1 / 2]⟩

/-- The survival times of the instance on two strata: `(1, 2)`, `(1, 3)` and `(2, 4)` for the
arms `0, 1, 2` at the strata `(false, true)`. -/
def rmstTimes (t : Fin 3) (v : Bool) : ℕ := ![if v then 2 else 1, if v then 3 else 1,
  if v then 4 else 2] t

theorem rmstModel_isCondMean (ν : Measure Bool) [IsProbabilityMeasure ν] (t : Fin 3) :
    (rmstPopulation ν signCov rmstTimes 4).IsCondMean t (rmstModel.predictor t) := by
  refine Population.isCondMean_of_eq_comp (measurable_of_finite _)
    (by unfold AnchoredModel.predictor anchoredPredictor; fun_prop) ?_ Integrable.of_finite
  funext v
  fin_cases t <;> cases v <;>
    norm_num [rmstPopulation, Transport.truncTime, rmstTimes, AnchoredModel.predictor,
      anchoredPredictor, signCov, rmstModel]

/-- **An instance with numbers.** With two equally likely strata at the covariate values `∓1`
and survival times `rmstTimes`, the conditional restricted means up to `4` are the predictors of
`rmstModel`, which has a nonzero prognostic slope and nonzero shared interactions. The
difference of the restricted means of `2` and `1` is `1 = γ_2 - γ_1` both in this population
and in the population concentrated on the stratum `true`, while the difference of `1` and the
reference `0`, whose interactions differ, is `1/2` in the first and `1` in the second. -/
theorem rmst_shared_example :
    rmst halfLaw (rmstTimes 2) 4 - rmst halfLaw (rmstTimes 1) 4 = 1 ∧
      rmst (Measure.dirac true) (rmstTimes 2) 4 - rmst (Measure.dirac true) (rmstTimes 1) 4 =
        1 ∧
      rmst halfLaw (rmstTimes 1) 4 - rmst halfLaw (rmstTimes 0) 4 = 1 / 2 ∧
      rmst (Measure.dirac true) (rmstTimes 1) 4 - rmst (Measure.dirac true) (rmstTimes 0) 4 =
        1 := by
  have hS : rmstModel.SharedEffectModifiers {1, 2} := by
    intro b hb c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb hc
    rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;> rfl
  have hγ : rmstModel.γ 2 - rmstModel.γ 1 = 1 := by norm_num [rmstModel]
  have hT : ∀ t, Measurable (rmstTimes t) := fun _ => measurable_of_finite _
  have key := fun (ν : Measure Bool) [IsProbabilityMeasure ν] =>
    (rmst_sub_eq_of_shared (measurable_of_finite signCov) hT hS (by simp) (by simp)
      (rmstModel_isCondMean ν 2) (rmstModel_isCondMean ν 1)).1
  have hm : ∀ (ν : Measure Bool) [IsFiniteMeasure ν] (t : Fin 3),
      rmst ν (rmstTimes t) 4 = ∫ v, ((min (rmstTimes t v) 4 : ℕ) : ℝ) ∂ν :=
    fun ν _ t => rmst_eq_integral_min (hT t) 4
  refine ⟨(key halfLaw).trans hγ, (key (Measure.dirac true)).trans hγ, ?_, ?_⟩
  · rw [hm, hm, integral_halfLaw, integral_halfLaw]
    norm_num [rmstTimes]
  · rw [hm, hm, integral_dirac, integral_dirac]
    norm_num [rmstTimes]

/-! ### The hazard ratio and the log hazard scale -/

section Hazard

open Bias.HazardRatio PropHazards PropHazardsExample

/-- The covariate of the frailty stratum `u`: `1` when `u` holds, `0` otherwise. -/
noncomputable def strataCov (u : Bool) : Fin 1 → ℝ := fun _ => if u then 1 else 0

/-- The anchored model on the log hazard scale of the stratum hazards `phRisk (1/2) ncRisk`:
predictors `log (1/2) + x log (1/5)` for the untreated arm `false` and `log (1/2)` more for the
treated arm `true`; there are no interactions, so the two arms share their effect modifiers. -/
noncomputable def logHazardModel : AnchoredModel Bool 1 :=
  ⟨Real.log (1 / 2), fun _ => Real.log (1 / 5), fun a => if a then Real.log (1 / 2) else 0,
    fun _ => 0⟩

/-- **The stratum hazards of the non-collapsibility example follow a log hazard model with
shared effect modifiers.** The stratum hazards `phRisk (1/2) ncRisk a u` (untreated `1/10` and
`1/2`, treated half of those) are `exp(η_a(x_u))` for `logHazardModel`; the conditional log
hazard ratio of the treated against the untreated arm is `log (1/2) = γ_true - γ_false` at every
covariate value; yet the marginal period `2` hazard ratio is `329/578` when the strata have mass
`1/2` each and `1/2` when the first stratum has all the mass, so the marginal log hazard ratios
differ. -/
theorem logHazardModel_example :
    (∀ a u, Real.exp (logHazardModel.predictor a (strataCov u)) = phRisk (1 / 2) ncRisk a u) ∧
      logHazardModel.SharedEffectModifiers Set.univ ∧
      (∀ x, linkContrast Real.log (fun y => Real.exp (logHazardModel.predictor false y))
        (fun y => Real.exp (logHazardModel.predictor true y)) x = Real.log (1 / 2)) ∧
      hazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) true /
          hazard2 exHalf exHalf (phRisk (1 / 2) ncRisk) (phRisk (1 / 2) ncRisk) false =
        329 / 578 ∧
      hazard2 exHalf (fun u => if u then 1 else 0) (phRisk (1 / 2) ncRisk)
          (phRisk (1 / 2) ncRisk) true /
        hazard2 exHalf (fun u => if u then 1 else 0) (phRisk (1 / 2) ncRisk)
          (phRisk (1 / 2) ncRisk) false = 1 / 2 ∧
      Real.log (329 / 578) ≠ Real.log (1 / 2) := by
  have hS : logHazardModel.SharedEffectModifiers Set.univ := fun _ _ _ _ => rfl
  obtain ⟨-, h2, h3, h4⟩ := Transport.marginal_hazardRatio_not_transportable
  refine ⟨fun a u => ?_, hS, fun x => ?_, h2, h3, h4⟩
  · cases a <;> cases u <;>
      simp [logHazardModel, AnchoredModel.predictor, anchoredPredictor, strataCov, phRisk, ncRisk,
        Real.exp_add, Real.exp_neg, Real.exp_log] <;> norm_num
  · simp only [linkContrast, Real.log_exp]
    rw [AnchoredModel.predictor_sub_of_shared hS trivial trivial]
    simp [logHazardModel]

end Hazard

/-! ### The restricted mean reported from a log hazard model -/

section HazardRMST

open Survival.ComparisonExample

/-- An event time on `{1, 2, 3}` with hazard `h` at times `1` and `2`: masses `h`, `(1 - h) h`
and `(1 - h)²`. -/
noncomputable def hazardArm (h : ℝ) : Measure ℕ := threePoint h ((1 - h) * h) ((1 - h) ^ 2)

theorem hazardArm_real {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) (s : Set ℕ) :
    (hazardArm h).real s = s.indicator (fun _ => h) 1 + s.indicator (fun _ => (1 - h) * h) 2 +
      s.indicator (fun _ => (1 - h) ^ 2) 3 :=
  threePoint_real h0 (mul_nonneg (by linarith) h0) (sq_nonneg _) s

/-- The hazard of `hazardArm h` is `h` at times `1` and `2`, for `0 ≤ h < 1`. -/
theorem hazard_hazardArm {h : ℝ} (h0 : 0 ≤ h) (h1 : h < 1) :
    hazard (hazardArm h) id 1 = h ∧ hazard (hazardArm h) id 2 = h := by
  have hne : (1 - h) ≠ 0 := by linarith
  constructor
  · simp only [hazard, atRisk, hazardArm_real h0 h1.le, id]
    simp [Set.indicator]
    field_simp
    ring
  · simp only [hazard, atRisk, hazardArm_real h0 h1.le, id]
    simp [Set.indicator]
    field_simp
    ring

/-- The restricted mean of `hazardArm h` up to `3` is `1 + (1 - h) + (1 - h)²`. -/
theorem rmst_hazardArm {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    rmst (hazardArm h) id 3 = 1 + (1 - h) + (1 - h) ^ 2 := by
  simp only [rmst, survival, Finset.sum_range_succ, Finset.sum_range_zero, hazardArm_real h0 h1,
    id]
  simp [Set.indicator]
  ring

/-- **The restricted mean difference from a log hazard model is not transported.** Give the
strata `u` of `logHazardModel` event times with the stratum hazards `phRisk (1/2) ncRisk a u` at
times `1` and `2` (`hazardArm`), so the conditional hazard ratio of the treated against the
untreated arm is `1/2` at both times in both strata (at time `3` every remaining unit has the
event in both arms; the restricted mean up to `3` does not depend on it). The conditional
difference of the restricted means up to `3` is `57/400` in the stratum `true` and `9/16` in the
stratum `false`. Hence in the populations concentrated on one stratum both the average
conditional difference and the marginal difference `linkMarginal id` of the conditional
restricted means differ between the two populations. -/
theorem rmst_sub_not_transported_of_logHazard :
    (∀ a u, ∀ k ∈ ({1, 2} : Set ℕ),
      hazard (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk a u)) id k =
        PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk a u) ∧
      linkConditional id (Measure.dirac true)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            false u)) id 3)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            true u)) id 3) = 57 / 400 ∧
      linkConditional id (Measure.dirac false)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            false u)) id 3)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            true u)) id 3) = 9 / 16 ∧
      linkMarginal id (Measure.dirac true)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            false u)) id 3)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            true u)) id 3) = 57 / 400 ∧
      linkMarginal id (Measure.dirac false)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            false u)) id 3)
          (fun u => rmst (hazardArm (PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk
            true u)) id 3) = 9 / 16 := by
  have hr : ∀ a u, 0 ≤ PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk a u ∧
      PropHazards.phRisk (1 / 2) PropHazardsExample.ncRisk a u < 1 := fun a u => by
    cases a <;> cases u <;>
      norm_num [PropHazards.phRisk, PropHazardsExample.ncRisk]
  refine ⟨fun a u k hk => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
    rcases hk with rfl | rfl
    · exact (hazard_hazardArm (hr a u).1 (hr a u).2).1
    · exact (hazard_hazardArm (hr a u).1 (hr a u).2).2
  · simp only [linkConditional, linkContrast, integral_dirac, id,
      rmst_hazardArm (hr _ _).1 (hr _ _).2.le]
    norm_num [PropHazards.phRisk, PropHazardsExample.ncRisk]
  · simp only [linkConditional, linkContrast, integral_dirac, id,
      rmst_hazardArm (hr _ _).1 (hr _ _).2.le]
    norm_num [PropHazards.phRisk, PropHazardsExample.ncRisk]
  · simp only [linkMarginal, integral_dirac, id, rmst_hazardArm (hr _ _).1 (hr _ _).2.le]
    norm_num [PropHazards.phRisk, PropHazardsExample.ncRisk]
  · simp only [linkMarginal, integral_dirac, id, rmst_hazardArm (hr _ _).1 (hr _ _).2.le]
    norm_num [PropHazards.phRisk, PropHazardsExample.ncRisk]

end HazardRMST

end IndirectComparison

end CausalInference
