/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Bias formulas for unmeasured confounding

Population-level, finite and algebraic sensitivity analysis for a binary treatment `A` and a
binary unmeasured confounder `U`. The data are summarized by the stratum means
`m a u = E[Y | A = a, U = u]` (or the stratum risks `R u = P(Y = 1 | A = a, U = u)`) and the
prevalences `π a = P(U = 1 | A = a)`. By the law of total expectation the observed mean in arm
`a` is `π a * m a true + (1 - π a) * m a false`. If `U` suffices for confounding control, the
causal contrast is the `U`-standardized difference
`∑ u, P(U = u) * (m true u - m false u)`, written with `r = P(U = 1)`.

## Main results

* `unadjustedBias_eq`: the general bias formula of VanderWeele and Arah for the unadjusted
  difference in means, `γ₁ (π₁ - r) - γ₀ (π₀ - r)` with `γ_a = m a 1 - m a 0`.
* `unadjustedBias_eq_of_no_interaction`: with no `A`-`U` interaction on the additive scale
  (`γ₁ = γ₀ = γ`), the bias is `γ * (π₁ - π₀)`.
* `cornfield_prevalence`: Cornfield's condition. If treatment has no effect within levels of `U`,
  `U` is coded as a risk factor, and the observed risk ratio exceeds one, then the prevalence
  ratio `π₁ / π₀` is at least the observed risk ratio. `cornfield_prevalence_coding_needed` shows
  that the coding hypothesis cannot be dropped, and `cornfield_prevalence_max` gives the
  coding-free form.
* `cornfield_riskRatio`: under the same null, the risk ratio of `U` for the outcome is at least
  the observed risk ratio.
* `evalue_bound`: the Ding and VanderWeele joint bounding factor: the observed risk ratio is at
  most `RR_UD * RR_EU / (RR_UD + RR_EU - 1)`.

## References

* J. Cornfield, W. Haenszel, E. C. Hammond, A. M. Lilienfeld, M. B. Shimkin, E. L. Wynder,
  *Smoking and lung cancer: recent evidence and a discussion of some questions*, Journal of the
  National Cancer Institute (1959).
* T. J. VanderWeele and O. A. Arah, *Bias formulas for sensitivity analysis of unmeasured
  confounding for general outcomes, treatments, and confounders*, Epidemiology (2011).
* P. Ding and T. J. VanderWeele, *Sensitivity analysis without assumptions*, Epidemiology (2016).
-/

@[expose] public section

namespace CausalInference

namespace BiasFormulas

/-- The observed mean `E[Y | A = a] = π a * m a true + (1 - π a) * m a false`, by the law of total
expectation over the binary confounder `U`, where `m a u = E[Y | A = a, U = u]` and
`π a = P(U = 1 | A = a)`. -/
def observedMean (m : Bool → Bool → ℝ) (π : Bool → ℝ) (a : Bool) : ℝ :=
  π a * m a true + (1 - π a) * m a false

/-- The `U`-standardized treatment effect
`r * (m true true - m false true) + (1 - r) * (m true false - m false false)` with reference
prevalence `r = P(U = 1)`. When `U` suffices for confounding control this is the average causal
effect `E[Y^1] - E[Y^0]`. -/
def standardizedEffect (m : Bool → Bool → ℝ) (r : ℝ) : ℝ :=
  r * (m true true - m false true) + (1 - r) * (m true false - m false false)

/-- The bias of the unadjusted difference in observed means relative to the standardized effect. -/
def unadjustedBias (m : Bool → Bool → ℝ) (π : Bool → ℝ) (r : ℝ) : ℝ :=
  (observedMean m π true - observedMean m π false) - standardizedEffect m r

/-- General bias formula (VanderWeele and Arah 2011, binary `U`): the bias of the unadjusted
difference in means equals
`(m 1 1 - m 1 0) (π 1 - r) - (m 0 1 - m 0 0) (π 0 - r)`. The identity holds for every reference
prevalence `r`. -/
theorem unadjustedBias_eq (m : Bool → Bool → ℝ) (π : Bool → ℝ) (r : ℝ) :
    unadjustedBias m π r =
      (m true true - m true false) * (π true - r) -
        (m false true - m false false) * (π false - r) := by
  unfold unadjustedBias observedMean standardizedEffect
  ring

/-- Simple bias formula (VanderWeele and Arah 2011): if the effect of `U` on the outcome is the same
value `γ` in both treatment arms (no interaction), the bias of the unadjusted difference in means
is `γ * (P(U = 1 | A = 1) - P(U = 1 | A = 0))`, whatever the reference prevalence `r`. -/
theorem unadjustedBias_eq_of_no_interaction {m : Bool → Bool → ℝ} {γ : ℝ}
    (h₁ : m true true - m true false = γ) (h₀ : m false true - m false false = γ)
    (π : Bool → ℝ) (r : ℝ) :
    unadjustedBias m π r = γ * (π true - π false) := by
  rw [unadjustedBias_eq, h₁, h₀]
  ring

/-- The observed risk `P(Y = 1 | A = a) = π a * R true + (1 - π a) * R false` under the null of no
treatment effect within levels of `U`: `R u = P(Y = 1 | A = a, U = u)` does not depend on `a`. -/
def observedRisk (R : Bool → ℝ) (π : Bool → ℝ) (a : Bool) : ℝ :=
  π a * R true + (1 - π a) * R false

/-- Cornfield's condition for the prevalence ratio. Assume no effect of treatment within levels of
`U`, that `U` is coded as a risk factor (`0 ≤ R false ≤ R true`), `P(U = 1 | A = 0) > 0`, and a
positive observed risk in the untreated arm. If the observed risk ratio exceeds one, then
`P(U = 1 | A = 1) / P(U = 1 | A = 0)` is at least the observed risk ratio. -/
theorem cornfield_prevalence {R π : Bool → ℝ} (hR₀ : 0 ≤ R false) (hR : R false ≤ R true)
    (hπ₀ : 0 < π false) (hobs₀ : 0 < observedRisk R π false)
    (hRR : 1 < observedRisk R π true / observedRisk R π false) :
    observedRisk R π true / observedRisk R π false ≤ π true / π false := by
  rw [one_lt_div hobs₀] at hRR
  rw [div_le_div_iff₀ hobs₀ hπ₀]
  unfold observedRisk at *
  have hle : π false ≤ π true := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_nonneg (sub_nonneg.2 h.le) (sub_nonneg.2 hR)]
  nlinarith [mul_nonneg hR₀ (sub_nonneg.2 hle)]

/-- Cornfield's condition for the confounder-outcome risk ratio. Under the null of no effect within
levels of `U`, with `0 < R false ≤ R true` and prevalences `0 ≤ π false`, `π true ≤ 1`, the risk
ratio `R true / R false` of `U` for the outcome is at least the observed risk ratio. -/
theorem cornfield_riskRatio {R π : Bool → ℝ} (hR₀ : 0 < R false) (hR : R false ≤ R true)
    (hπ₀ : 0 ≤ π false) (hπ₁ : π true ≤ 1) :
    observedRisk R π true / observedRisk R π false ≤ R true / R false := by
  have hobs : R false ≤ observedRisk R π false := by
    unfold observedRisk
    nlinarith
  have hobs₁ : observedRisk R π true ≤ R true := by
    unfold observedRisk
    nlinarith
  rw [div_le_div_iff₀ (by linarith) hR₀]
  nlinarith [mul_le_mul_of_nonneg_right hobs₁ hR₀.le,
    mul_le_mul_of_nonneg_left hobs (by linarith : 0 ≤ R true)]

/-- Recoding the confounder (`U ↦ 1 - U`) leaves the observed risks unchanged. -/
theorem observedRisk_recode (R π : Bool → ℝ) (a : Bool) :
    observedRisk (fun u => R (!u)) (fun a => 1 - π a) a = observedRisk R π a := by
  unfold observedRisk
  simp only [Bool.not_true, Bool.not_false]
  ring

/-- Coding-free Cornfield condition: under the null of no effect within levels of `U`, with
`0 < P(U = 1 | A = 0) < 1` and observed risk ratio above one, the larger of the prevalence ratios
of `U = 1` and of `U = 0` is at least the observed risk ratio. -/
theorem cornfield_prevalence_max {R π : Bool → ℝ} (hR₀ : 0 ≤ R false) (hR₁ : 0 ≤ R true)
    (hπ₀ : 0 < π false) (hπ₀' : π false < 1) (hobs₀ : 0 < observedRisk R π false)
    (hRR : 1 < observedRisk R π true / observedRisk R π false) :
    observedRisk R π true / observedRisk R π false ≤
      max (π true / π false) ((1 - π true) / (1 - π false)) := by
  rcases le_total (R false) (R true) with h | h
  · exact le_max_of_le_left (cornfield_prevalence hR₀ h hπ₀ hobs₀ hRR)
  · refine le_max_of_le_right ?_
    have key := cornfield_prevalence (R := fun u => R (!u)) (π := fun a => 1 - π a) hR₁ h
      (by simpa using hπ₀') (by rwa [observedRisk_recode])
      (by rwa [observedRisk_recode, observedRisk_recode])
    rwa [observedRisk_recode, observedRisk_recode] at key

/-- The coding hypothesis `R false ≤ R true` cannot be dropped from `cornfield_prevalence`: with
`R = (1, 0)` and prevalences `π = (1/2, 1/4)` (untreated, treated) the observed risk ratio is
`3/2 > 1`, yet the prevalence ratio is `1/2`. -/
theorem cornfield_prevalence_coding_needed :
    ∃ R π : Bool → ℝ, 0 ≤ R true ∧ 0 ≤ R false ∧ 0 < π false ∧ π false < 1 ∧ 0 < π true ∧
      π true < 1 ∧ 0 < observedRisk R π false ∧
      1 < observedRisk R π true / observedRisk R π false ∧
      π true / π false < observedRisk R π true / observedRisk R π false := by
  refine ⟨fun u => if u then 0 else 1, fun a => if a then 1 / 4 else 1 / 2, ?_⟩
  simp only [observedRisk]
  norm_num

/-- The joint bounding factor of Ding and VanderWeele (2016) for a binary confounder. Under the null
of no effect within levels of `U`, with `U` coded as a risk factor (`0 < R false ≤ R true`) and
more prevalent among the treated (`0 < π false ≤ π true ≤ 1`), write
`RR_UD = R true / R false` and `RR_EU = π true / π false`. Then the observed risk ratio is at most
`RR_UD * RR_EU / (RR_UD + RR_EU - 1)`. -/
theorem evalue_bound {R π : Bool → ℝ} (hR₀ : 0 < R false) (hR : R false ≤ R true)
    (hπ₀ : 0 < π false) (hπ : π false ≤ π true) (hπ₁ : π true ≤ 1) :
    observedRisk R π true / observedRisk R π false ≤
      (R true / R false) * (π true / π false) / (R true / R false + π true / π false - 1) := by
  have hobs : 0 < observedRisk R π false := by
    unfold observedRisk
    nlinarith
  have hD : 0 < R true * π false + π true * R false - R false * π false := by nlinarith
  have e : (R true / R false) * (π true / π false) / (R true / R false + π true / π false - 1) =
      R true * π true / (R true * π false + π true * R false - R false * π false) := by
    field_simp
  rw [e, div_le_div_iff₀ hobs hD]
  unfold observedRisk
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hR₀.le (sub_nonneg.2 hR)) (sub_nonneg.2 hπ))
    (sub_nonneg.2 hπ₁)]

end BiasFormulas

end CausalInference
