/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Surrogacy.Criteria
public import CausalInference.Mediation.Counterexamples

/-!
# Surrogate endpoints: countermodels

Finite countermodels for the causal claims about surrogate endpoints in NICE DSU Technical
Support Document 20, Section 3.1.2, and Technical Support Document 5, Section 3.1. All models
live on the eight point space `Ω₀ = Bool × Bool × Bool` with the uniform measure `μ₀` of
`Mediation.Counterexample`; write a point as `(A, U, V)`. The treatment is the fair coin `A`,
independent of all potential outcomes (a randomized trial), and the unmeasured coins `U`, `V`
drive the surrogate and the final outcome.

## Main results

* Prentice criteria and the natural direct effect (TSD 20, Section 3.1.2: the Prentice criteria
  "do not guarantee a causal relationship").
  - `prenticeHolds`: all four Prentice criteria hold (the observed final outcome is a function of
    the observed surrogate), yet the natural direct effect is `1` (`prenticeHolds_nde`).
  - `noDirectEffect`: the treatment has no direct effect (`Y a m` does not depend on `a`, so
    both natural direct effects vanish), the first three criteria hold, yet full capture fails
    (`noDirectEffect_not_fullCapture`), because `V` confounds surrogate and outcome.
* The surrogate paradox (TSD 20, Section 3.1.2: an individual-level association, "level 2"
  evidence, does not establish that treatments improving the surrogate improve the final
  outcome): in `paradox`, the surrogate has a positive causal effect on
  the final outcome for every unit, the treatment has no direct effect, the treatment raises the
  surrogate on average (`paradox_surrogate_effect`, `+1/4`) and the surrogate is positively
  associated with the final outcome within each arm (`paradox_within_arm`), yet the average
  effect of the treatment on the final outcome is negative (`paradox_te`, `-1/4`).
* The single mapping hypothesis (TSD 5, Section 3.1; positive result `single_mapping`): two
  treatments with the same probability of the short-term outcome but different mean final
  outcomes, so no map from short-term to final outcome serves both.
  - `mappingDirect_not_single`: the short-term outcome is independent of its effect on the final
    outcome, but the treatment has a direct effect.
  - `mappingConfounded_not_single`: no direct effect, but the short-term outcome and its effect
    on the final outcome are dependent.

## Sources

* NICE DSU Technical Support Document 20 (S. Bujkiewicz et al., 2019), Section 3.1.2.
* NICE DSU Technical Support Document 5 (S. Dias et al., 2011, updated 2012), Section 3.1.
* R. L. Prentice (1989), Surrogate endpoints in clinical trials: definition and operational
  criteria, Statistics in Medicine 8 (reference [65] of TSD 20).
* T. J. VanderWeele (2013), Surrogate measures and consistent surrogates, Biometrics 69
  (reference [67] of TSD 20).
* H. Chen, Z. Geng and J. Jia (2007), Criteria for surrogate end points, Journal of the Royal
  Statistical Society B 69 (the surrogate paradox; not cited in TSD 20).
-/

@[expose] public section

namespace CausalInference

namespace Surrogacy

namespace Counterexample

open MeasureTheory ProbabilityTheory Mediation Mediation.Counterexample

/-- Conditional means under `μ₀` are ratios of sums over the eight points. -/
theorem condMean_μ₀ (s : Set Ω₀) (f : Ω₀ → ℝ) :
    condMean μ₀ s f = (∑ ω, s.indicator f ω) / ∑ ω, s.indicator (1 : Ω₀ → ℝ) ω := by
  rw [condMean_eq, μ₀_real_eq_sum, ← integral_indicator (Set.toFinite s).measurableSet,
    integral_μ₀]
  ring

/-! ### All four Prentice criteria with a nonzero natural direct effect -/

/-- Write `C = U ∧ V`. The surrogate is `S 0 = C` and `S 1 = ¬C`, and the final outcome is
`Y a m = a + m - [m ≠ C]`: a direct effect `+1` of the treatment, offset in the observed data by
the dependence of `Y` on `C`, which also drives the surrogate. -/
def prenticeHolds : MediationModel Ω₀ Bool where
  A ω := ω.1
  M a ω := if a then !(ω.2.1 && ω.2.2) else (ω.2.1 && ω.2.2)
  Y a m ω := (if a then 1 else 0) + (if m then 1 else 0) - (if m = (ω.2.1 && ω.2.2) then 0 else 1)

/-- In `prenticeHolds` the observed final outcome equals the observed surrogate, so it is
independent of the treatment given the surrogate in every sense. -/
theorem prenticeHolds_Yobs (ω : Ω₀) :
    prenticeHolds.Yobs ω = if prenticeHolds.Mobs ω then 1 else 0 := by
  obtain ⟨a, u, v⟩ := ω
  cases a <;> cases u <;> cases v <;>
    simp [prenticeHolds, MediationModel.Yobs, MediationModel.Mobs]

/-- Every cell `A = a, S = s` of `prenticeHolds` has positive probability. -/
theorem prenticeHolds_cell_pos (a s : Bool) :
    μ₀ (prenticeHolds.A ⁻¹' {a} ∩ prenticeHolds.Mobs ⁻¹' {s}) ≠ 0 := by
  cases a <;> cases s
  · exact μ₀_ne_zero_of_mem (ω := (false, false, false)) (by simp [prenticeHolds,
      MediationModel.Mobs])
  · exact μ₀_ne_zero_of_mem (ω := (false, true, true)) (by simp [prenticeHolds,
      MediationModel.Mobs])
  · exact μ₀_ne_zero_of_mem (ω := (true, true, true)) (by simp [prenticeHolds,
      MediationModel.Mobs])
  · exact μ₀_ne_zero_of_mem (ω := (true, false, false)) (by simp [prenticeHolds,
      MediationModel.Mobs])

/-- The treatment of `prenticeHolds` is randomized: `A` is independent of all potential
outcomes jointly. -/
theorem prenticeHolds_randomized :
    IndepFun prenticeHolds.A
      (fun ω => (fun a => prenticeHolds.M a ω, fun a m => prenticeHolds.Y a m ω)) μ₀ :=
  indepFun_prod measurable_id (measurable_of_finite fun ω : Bool × Bool =>
    ((fun a : Bool => if a then !(ω.1 && ω.2) else (ω.1 && ω.2)),
      fun (a m : Bool) => (if a then (1 : ℝ) else 0) + (if m then 1 else 0) -
        (if m = (ω.1 && ω.2) then 0 else 1)))

/-- All four Prentice criteria hold in `prenticeHolds`: `P(S = 1 | A) = 3/4` against `1/4`,
`E[Y | S] = 1` against `0`, `E[Y | A] = 3/4` against `1/4`, and full capture. -/
theorem prenticeHolds_criteria : PrenticeCriteria prenticeHolds μ₀ where
  treatment_affects_surrogate := by
    simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [Set.indicator, prenticeHolds, MediationModel.Mobs]
    norm_num
  surrogate_predicts_outcome := by
    simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [Set.indicator, prenticeHolds, MediationModel.Mobs, MediationModel.Yobs]
    norm_num
  treatment_affects_outcome := by
    simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
    simp [Set.indicator, prenticeHolds, MediationModel.Mobs, MediationModel.Yobs]
    norm_num
  full_capture s := by
    simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
    cases s
    · simp [Set.indicator, prenticeHolds, MediationModel.Mobs, MediationModel.Yobs]
    · simp [Set.indicator, prenticeHolds, MediationModel.Mobs, MediationModel.Yobs]
      norm_num

/-- The pure natural direct effect of `prenticeHolds` is `1`, although all four Prentice
criteria hold. -/
theorem prenticeHolds_nde : prenticeHolds.nde μ₀ false = 1 := by
  simp only [MediationModel.nde, MediationModel.nested, integral_μ₀, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [prenticeHolds]
  norm_num

/-! ### No direct effect without full capture -/

/-- The surrogate is `S 0 = U` and `S 1 = U ∨ V`, and the final outcome is `Y a m = m + V`,
which does not depend on the treatment: no direct effect. The coin `V` raises both the
surrogate under treatment and the final outcome. -/
def noDirectEffect : MediationModel Ω₀ Bool where
  A ω := ω.1
  M a ω := if a then (ω.2.1 || ω.2.2) else ω.2.1
  Y _ m ω := (if m then 1 else 0) + (if ω.2.2 then 1 else 0)

/-- The treatment of `noDirectEffect` is randomized. -/
theorem noDirectEffect_randomized :
    IndepFun noDirectEffect.A
      (fun ω => (fun a => noDirectEffect.M a ω, fun a m => noDirectEffect.Y a m ω)) μ₀ :=
  indepFun_prod measurable_id (measurable_of_finite fun ω : Bool × Bool =>
    ((fun a : Bool => if a then (ω.1 || ω.2) else ω.1),
      fun (_ m : Bool) => (if m then (1 : ℝ) else 0) + (if ω.2 then 1 else 0)))

/-- Both natural direct effects of `noDirectEffect` vanish. -/
theorem noDirectEffect_nde (a' : Bool) : noDirectEffect.nde μ₀ a' = 0 := by
  simp [MediationModel.nde, MediationModel.nested, noDirectEffect]

/-- Every cell `A = a, S = s` of `noDirectEffect` has positive probability. -/
theorem noDirectEffect_cell_pos (a s : Bool) :
    μ₀ (noDirectEffect.A ⁻¹' {a} ∩ noDirectEffect.Mobs ⁻¹' {s}) ≠ 0 := by
  refine μ₀_ne_zero_of_mem (ω := (a, s, s)) ?_
  cases a <;> cases s <;> simp [noDirectEffect, MediationModel.Mobs]

/-- The first three Prentice criteria hold in `noDirectEffect`: `P(S = 1 | A) = 3/4` against
`1/2`, `E[Y | S] = 8/5` against `1/3`, `E[Y | A] = 5/4` against `1`. -/
theorem noDirectEffect_criteria :
    condMean μ₀ (noDirectEffect.A ⁻¹' {true}) (fun ω => if noDirectEffect.Mobs ω then 1 else 0) ≠
        condMean μ₀ (noDirectEffect.A ⁻¹' {false})
          (fun ω => if noDirectEffect.Mobs ω then 1 else 0) ∧
      condMean μ₀ (noDirectEffect.Mobs ⁻¹' {true}) noDirectEffect.Yobs ≠
        condMean μ₀ (noDirectEffect.Mobs ⁻¹' {false}) noDirectEffect.Yobs ∧
      condMean μ₀ (noDirectEffect.A ⁻¹' {true}) noDirectEffect.Yobs ≠
        condMean μ₀ (noDirectEffect.A ⁻¹' {false}) noDirectEffect.Yobs := by
  simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [Set.indicator, noDirectEffect, MediationModel.Mobs, MediationModel.Yobs]
  norm_num

/-- Full capture fails in `noDirectEffect`: `E[Y | A = 1, S = 0] = 0` while
`E[Y | A = 0, S = 0] = 1/2`, although the treatment has no direct effect. -/
theorem noDirectEffect_not_fullCapture : ¬ PrenticeCriteria noDirectEffect μ₀ := by
  intro h
  have := h.full_capture false
  simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool] at this
  simp [Set.indicator, noDirectEffect, MediationModel.Mobs, MediationModel.Yobs] at this
  norm_num at this

/-! ### The surrogate paradox -/

/-- The surrogate is `S 0 = U` and `S 1 = V` if `U`, `1` otherwise, so the treatment raises the
surrogate for the units with `U = 0` and lowers it for the units with `U = 1, V = 0`. The final
outcome is `Y a m = m w` with `w = 3` on `U = 1, V = 0` and `w = 1` otherwise: it does not
depend on the treatment and increases with the surrogate for every unit. -/
def paradox : MediationModel Ω₀ Bool where
  A ω := ω.1
  M a ω := if a then (if ω.2.1 then ω.2.2 else true) else ω.2.1
  Y _ m ω := if m then (if ω.2.1 && !ω.2.2 then 3 else 1) else 0

/-- The treatment of `paradox` is randomized. -/
theorem paradox_randomized :
    IndepFun paradox.A (fun ω => (fun a => paradox.M a ω, fun a m => paradox.Y a m ω)) μ₀ :=
  indepFun_prod measurable_id (measurable_of_finite fun ω : Bool × Bool =>
    ((fun a : Bool => if a then (if ω.1 then ω.2 else true) else ω.1),
      fun (_ m : Bool) => if m then (if ω.1 && !ω.2 then (3 : ℝ) else 1) else 0))

/-- In `paradox` the surrogate has a positive causal effect on the final outcome for every unit
and under both treatments. -/
theorem paradox_unit_effect (a : Bool) (ω : Ω₀) : paradox.Y a false ω < paradox.Y a true ω := by
  obtain ⟨_, u, v⟩ := ω
  cases u <;> cases v <;> norm_num [paradox]

/-- Both natural direct effects of `paradox` vanish. -/
theorem paradox_nde (a' : Bool) : paradox.nde μ₀ a' = 0 := by
  simp [MediationModel.nde, MediationModel.nested, paradox]

/-- The treatment raises the surrogate on average: `P(S 1 = 1) - P(S 0 = 1) = 3/4 - 1/2`. -/
theorem paradox_surrogate_effect :
    ∫ ω, ((if paradox.M true ω then (1 : ℝ) else 0) - (if paradox.M false ω then 1 else 0)) ∂μ₀ =
      1 / 4 := by
  simp only [integral_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [paradox]
  norm_num

/-- The treatment lowers the final outcome on average: the total effect is `-1/4`. -/
theorem paradox_te : paradox.te μ₀ = -1 / 4 := by
  simp only [MediationModel.te, MediationModel.nested, integral_μ₀, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [paradox]
  norm_num

/-- Every cell `A = a, S = s` of `paradox` has positive probability. -/
theorem paradox_cell_pos (a s : Bool) :
    μ₀ (paradox.A ⁻¹' {a} ∩ paradox.Mobs ⁻¹' {s}) ≠ 0 := by
  refine μ₀_ne_zero_of_mem (ω := (a, a || s, s)) ?_
  cases a <;> cases s <;> simp [paradox, MediationModel.Mobs]

/-- Within each arm of the trial the surrogate is positively associated with the final outcome:
`E[Y | A = a, S = 0] < E[Y | A = a, S = 1]`. -/
theorem paradox_within_arm (a : Bool) :
    condMean μ₀ (paradox.A ⁻¹' {a} ∩ paradox.Mobs ⁻¹' {false}) paradox.Yobs <
      condMean μ₀ (paradox.A ⁻¹' {a} ∩ paradox.Mobs ⁻¹' {true}) paradox.Yobs := by
  simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> simp [Set.indicator, paradox, MediationModel.Mobs, MediationModel.Yobs] <;>
    norm_num

/-- What the trial observes in `paradox`: the difference in means of the surrogate between the
arms is `1/4` and the difference in means of the final outcome is `-1/4`. -/
theorem paradox_observed :
    condMean μ₀ (paradox.A ⁻¹' {true}) (fun ω => if paradox.Mobs ω then 1 else 0) -
        condMean μ₀ (paradox.A ⁻¹' {false}) (fun ω => if paradox.Mobs ω then 1 else 0) = 1 / 4 ∧
      condMean μ₀ (paradox.A ⁻¹' {true}) paradox.Yobs -
        condMean μ₀ (paradox.A ⁻¹' {false}) paradox.Yobs = -1 / 4 := by
  simp only [condMean_μ₀, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [Set.indicator, paradox, MediationModel.Mobs, MediationModel.Yobs]
  norm_num

/-! ### The single mapping hypothesis fails without its assumptions -/

/-- Two treatments `t : Bool` with the same short-term outcome `S t = U` and a direct effect on
the final outcome, `Y t m = t`. -/
def mappingDirectS (_ : Bool) (ω : Ω₀) : Bool := ω.2.1

/-- The final outcome of the direct effect countermodel: `Y t m = t`. -/
def mappingDirectY (t _ : Bool) (_ : Ω₀) : ℝ := if t then 1 else 0

/-- In the direct effect countermodel the short-term outcome is independent of its (zero) effect
on the final outcome, but the two treatments have the same probability of the short-term
outcome and different mean final outcomes, so no map `g` from the probability of the short-term
outcome to the mean final outcome serves both. -/
theorem mappingDirect_not_single :
    (∀ t, IndepFun (mappingDirectS t)
      (fun ω => mappingDirectY false true ω - mappingDirectY false false ω) μ₀) ∧
    ¬ ∃ g : ℝ → ℝ, ∀ t, ∫ ω, mappingDirectY t (mappingDirectS t ω) ω ∂μ₀ =
      g (μ₀.real {ω | mappingDirectS t ω = true}) := by
  refine ⟨fun t => ?_, fun ⟨g, hg⟩ => ?_⟩
  · simp only [mappingDirectY, sub_self]
    exact indepFun_const_right _ _
  · have h1 := hg true
    have h0 := hg false
    simp only [mappingDirectS, mappingDirectY] at h1 h0
    simp at h1 h0
    linarith

/-- Two treatments with short-term outcomes `S 0 = U` and `S 1 = ¬U`. -/
def mappingConfoundedS (t : Bool) (ω : Ω₀) : Bool := if t then !ω.2.1 else ω.2.1

/-- The final outcome of the confounded countermodel, `Y t m = [m = U]`, does not depend on the
treatment. -/
def mappingConfoundedY (_ m : Bool) (ω : Ω₀) : ℝ := if m = ω.2.1 then 1 else 0

/-- In the confounded countermodel the treatment has no direct effect, but `S 0 = U` is not
independent of the effect `Y 1 - Y 0 = ±1` of the short-term outcome, which is `+1` exactly when
`U = 1`; both treatments give `P(S = 1) = 1/2`, yet the mean final outcomes are `1` and `0`, so
no map `g` serves both. -/
theorem mappingConfounded_not_single :
    (∀ t m, mappingConfoundedY t m = mappingConfoundedY false m) ∧
    ¬ IndepFun (mappingConfoundedS false)
      (fun ω => mappingConfoundedY false true ω - mappingConfoundedY false false ω) μ₀ ∧
    ¬ ∃ g : ℝ → ℝ, ∀ t, ∫ ω, mappingConfoundedY t (mappingConfoundedS t ω) ω ∂μ₀ =
      g (μ₀.real {ω | mappingConfoundedS t ω = true}) := by
  refine ⟨fun _ _ => rfl, fun h => ?_, fun ⟨g, hg⟩ => ?_⟩
  · have h' := congrArg ENNReal.toReal (h.measure_inter_preimage_eq_mul {true} {1}
      (measurableSet_singleton _) (measurableSet_singleton _))
    rw [ENNReal.toReal_mul] at h'
    simp only [← measureReal_def, μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool] at h'
    simp [Set.indicator, mappingConfoundedS, mappingConfoundedY] at h'
    norm_num at h'
  · have h1 := hg true
    have h0 := hg false
    have e : μ₀.real {ω | mappingConfoundedS true ω = true} =
        μ₀.real {ω | mappingConfoundedS false ω = true} := by
      simp only [μ₀_real_eq_sum, Fintype.sum_prod_type, Fintype.sum_bool]
      simp [Set.indicator, mappingConfoundedS]
    rw [e] at h1
    simp only [integral_μ₀, Fintype.sum_prod_type, Fintype.sum_bool] at h1 h0
    simp [mappingConfoundedS, mappingConfoundedY] at h1 h0
    linarith

end Counterexample

end Surrogacy

end CausalInference
