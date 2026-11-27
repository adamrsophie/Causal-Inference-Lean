/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.DifferenceInDifferences.TwoPeriod
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Parallel trends depends on the scale

Parallel trends is an assumption about the untreated group means on a chosen scale. On the
additive scale it says that the untreated means of the two groups change by the same amount;
on the log scale (the scale of a log-linear model for a positive outcome, applied to the group
means) it says that they change by the same factor. The two assumptions are different, they
identify the ATT by different formulas, and both hold only in degenerate cases.

Probability setting: the elementary results are about four real numbers, the untreated means
`a₀, a₁` (treated group, before and after) and `b₀, b₁` (comparison group); the model results
use the two by two design of `TwoPeriod.lean` on a measure space `(Ω, μ)` with conditional means
taken against `ProbabilityTheory.cond`. The log scale is applied to the group means, not to unit
outcomes (`log E[Y]`, not `E[log Y]`), and every mean entering a logarithm is assumed positive.

## Main definitions

* `DiDScale.AdditiveParallel`, `DiDScale.LogParallel`, `DiDScale.LogitParallel`: parallel trends
  of four means on the additive, log, and logit scales.
* `DiDScale.LogParallelTrends`: log-scale parallel trends of untreated means in the two by two
  model.
* `DiDScale.ratioDid`: the observed estimand of the ATT under log-scale parallel trends,
  `E[Yobs post | G = 1] - E[Yobs pre | G = 1] · E[Yobs post | G = 0] / E[Yobs pre | G = 0]`.

## Main results

* `DiDScale.additiveParallel_and_logParallel_iff`: for positive means, both scales hold iff the
  untreated trend is zero in both groups or the two groups have equal means in both periods.
* `DiDScale.additive_not_log`, `DiDScale.log_not_additive`: neither assumption implies the other.
* `DiDScale.logit_example`: the same dichotomy fails for the logit scale; means `0.2 → 0.3` and
  `0.7 → 0.8` are parallel on both the additive and the logit scales.
* `DiDScale.att_eq_ratioDid`: under consistency, no anticipation, and log-scale parallel trends,
  the ATT equals `ratioDid`.
* `DiDScale.cexLog_spec`: a model with log-scale parallel trends and no treatment effect in which
  additive parallel trends fails and the difference in differences is `-1`; `ratioDid` is `0`.
* `DiDScale.cexAdd_spec`: a model with additive parallel trends and no treatment effect in which
  log-scale parallel trends fails and `ratioDid` is `1 / 2`.

Source: NICE DSU Technical Support Document 17 (Faria, Hernandez Alava, Manca, Wailoo, 2015),
Section 2.5.1, which notes that the difference in differences approach has been extended to
nonlinear models; the formal statements here are this library's.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CausalInference

namespace DiDScale

/-! ### Four means -/

/-- **Additive parallel trends** of untreated means: `a₁ - a₀ = b₁ - b₀`. -/
def AdditiveParallel (a₀ a₁ b₀ b₁ : ℝ) : Prop := a₁ - a₀ = b₁ - b₀

/-- **Log-scale parallel trends** of untreated means: `log a₁ - log a₀ = log b₁ - log b₀`.
Meaningful for positive means only. -/
def LogParallel (a₀ a₁ b₀ b₁ : ℝ) : Prop := Real.log a₁ - Real.log a₀ = Real.log b₁ - Real.log b₀

/-- The logit `log (p / (1 - p))`, meaningful for `0 < p < 1`. -/
noncomputable def logit (p : ℝ) : ℝ := Real.log (p / (1 - p))

/-- **Logit-scale parallel trends** of untreated means (probabilities):
`logit a₁ - logit a₀ = logit b₁ - logit b₀`. -/
def LogitParallel (a₀ a₁ b₀ b₁ : ℝ) : Prop := logit a₁ - logit a₀ = logit b₁ - logit b₀

/-- For positive means, log-scale parallel trends says the ratios agree,
`a₁ / a₀ = b₁ / b₀`, written without division as `a₁ b₀ = b₁ a₀`. -/
theorem logParallel_iff_mul {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁) (hb₀ : 0 < b₀)
    (hb₁ : 0 < b₁) : LogParallel a₀ a₁ b₀ b₁ ↔ a₁ * b₀ = b₁ * a₀ := by
  rw [LogParallel, ← Real.log_div ha₁.ne' ha₀.ne', ← Real.log_div hb₁.ne' hb₀.ne']
  constructor
  · intro h
    have := Real.log_injOn_pos (div_pos ha₁ ha₀) (div_pos hb₁ hb₀) h
    field_simp at this
    linarith
  · intro h
    congr 1
    field_simp
    linarith

/-- **Parallel trends on both scales.** For positive untreated means, additive and log-scale
parallel trends hold together iff the untreated trend is zero in both groups, or the two groups
have the same untreated mean in both periods. -/
theorem additiveParallel_and_logParallel_iff {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : 0 < a₀) (ha₁ : 0 < a₁)
    (hb₀ : 0 < b₀) (hb₁ : 0 < b₁) :
    AdditiveParallel a₀ a₁ b₀ b₁ ∧ LogParallel a₀ a₁ b₀ b₁ ↔
      (a₁ = a₀ ∧ b₁ = b₀) ∨ (a₀ = b₀ ∧ a₁ = b₁) := by
  rw [logParallel_iff_mul ha₀ ha₁ hb₀ hb₁, AdditiveParallel]
  constructor
  · rintro ⟨hadd, hmul⟩
    have hb₁' : b₁ = b₀ + (a₁ - a₀) := by linarith
    rw [hb₁'] at hmul
    have : (a₁ - a₀) * (b₀ - a₀) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · subst h1 h2; constructor <;> ring
    · subst h1 h2; constructor <;> ring

/-- **Additive does not imply log-scale parallel trends.** Means `1 → 2` and `2 → 3`. -/
theorem additive_not_log : AdditiveParallel 1 2 2 3 ∧ ¬ LogParallel 1 2 2 3 := by
  rw [logParallel_iff_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [AdditiveParallel]

/-- **Log-scale does not imply additive parallel trends.** Means `1 → 2` and `2 → 4`. -/
theorem log_not_additive : LogParallel 1 2 2 4 ∧ ¬ AdditiveParallel 1 2 2 4 := by
  rw [logParallel_iff_mul (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [AdditiveParallel]

/-- **The dichotomy does not extend to the logit scale.** Untreated means `0.2 → 0.3` (treated
group) and `0.7 → 0.8` (comparison group) are parallel on both the additive and the logit
scales, although the trends are not zero and the baselines differ: the log odds ratios are both
`log (12 / 7)`. -/
theorem logit_example :
    AdditiveParallel 0.2 0.3 0.7 0.8 ∧ LogitParallel 0.2 0.3 0.7 0.8 ∧ (0.3 : ℝ) ≠ 0.2 ∧
      (0.2 : ℝ) ≠ 0.7 := by
  refine ⟨by norm_num [AdditiveParallel], ?_, by norm_num, by norm_num⟩
  rw [LogitParallel, logit, logit, logit, logit, ← Real.log_div (by norm_num) (by norm_num),
    ← Real.log_div (by norm_num) (by norm_num)]
  norm_num

/-! ### The two by two model -/

open TwoPeriod TwoPeriod.Period

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Log-scale parallel trends** in the two by two model: the untreated means satisfy
`log E[Y post 0 | G = 1] - log E[Y pre 0 | G = 1]
  = log E[Y post 0 | G = 0] - log E[Y pre 0 | G = 0]`. -/
def LogParallelTrends (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : Prop :=
  LogParallel (∫ ω, Y pre false ω ∂μ[|treated G]) (∫ ω, Y post false ω ∂μ[|treated G])
    (∫ ω, Y pre false ω ∂μ[|control G]) (∫ ω, Y post false ω ∂μ[|control G])

/-- Under integrability of the untreated outcomes given each group, (additive) parallel trends
is additive parallel trends of the four untreated means. -/
theorem parallelTrends_iff_additiveParallel {μ : Measure Ω} {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} (hT0 : ∀ t, Integrable (Y t false) μ[|treated G])
    (hC0 : ∀ t, Integrable (Y t false) μ[|control G]) :
    ParallelTrends μ G Y ↔
      AdditiveParallel (∫ ω, Y pre false ω ∂μ[|treated G]) (∫ ω, Y post false ω ∂μ[|treated G])
        (∫ ω, Y pre false ω ∂μ[|control G]) (∫ ω, Y post false ω ∂μ[|control G]) := by
  rw [ParallelTrends, AdditiveParallel, integral_sub (hT0 _) (hT0 _),
    integral_sub (hC0 _) (hC0 _)]

/-- **The ratio estimand.** The observed treated change against the comparison group's
proportional change: `E[Yobs post | G = 1] - E[Yobs pre | G = 1] · E[Yobs post | G = 0] /
E[Yobs pre | G = 0]`. -/
noncomputable def ratioDid (μ : Measure Ω) (G : Ω → Bool) (Yobs : Period → Ω → ℝ) : ℝ :=
  (∫ ω, Yobs post ω ∂μ[|treated G]) -
    (∫ ω, Yobs pre ω ∂μ[|treated G]) * (∫ ω, Yobs post ω ∂μ[|control G]) /
      (∫ ω, Yobs pre ω ∂μ[|control G])

/-- **Identification of the ATT under log-scale parallel trends.** Under consistency, no
anticipation, and log-scale parallel trends of untreated means, with the four untreated means
positive and the treatment-period potential outcomes integrable given `G = 1`, the ATT equals
`ratioDid`: the treated group's untreated mean in the treatment period is its pre-period mean
scaled by the comparison group's growth factor. Positivity of the means also makes both groups
non-null. -/
theorem att_eq_ratioDid {μ : Measure Ω} {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ}
    {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G)) (hcons : Consistency G Y Yobs)
    (hNA : NoAnticipation μ G Y) (hLPT : LogParallelTrends μ G Y)
    (hT0pre : 0 < ∫ ω, Y pre false ω ∂μ[|treated G])
    (hT0post : 0 < ∫ ω, Y post false ω ∂μ[|treated G])
    (hC0pre : 0 < ∫ ω, Y pre false ω ∂μ[|control G])
    (hC0post : 0 < ∫ ω, Y post false ω ∂μ[|control G])
    (hT1 : Integrable (Y post true) μ[|treated G]) (hT0 : Integrable (Y post false) μ[|treated G]) :
    att μ G Y = ratioDid μ G Yobs := by
  have hC : MeasurableSet (control G) := control_eq_compl G ▸ hG.compl
  have hmul := (logParallel_iff_mul hT0pre hT0post hC0pre hC0post).mp hLPT
  have eT : ∀ t, ∫ ω, Yobs t ω ∂μ[|treated G] = ∫ ω, Y t true ω ∂μ[|treated G] := fun t =>
    DiD.integral_cond_congr hG fun ω hω => by rw [hcons, show G ω = true from hω]
  have eC : ∀ t, ∫ ω, Yobs t ω ∂μ[|control G] = ∫ ω, Y t false ω ∂μ[|control G] := fun t =>
    DiD.integral_cond_congr hC fun ω hω => by rw [hcons, show G ω = false from hω]
  have hna : ∫ ω, Y pre true ω ∂μ[|treated G] = ∫ ω, Y pre false ω ∂μ[|treated G] := hNA
  rw [att, ratioDid, eT, eT, eC, eC, hna, integral_sub hT1 hT0]
  field_simp
  linarith

/-! ### Countermodels on the two-unit population of `TwoPeriod.lean`

Each unit has probability `1 / 2`, so overlap `0 < P(G = 1) < 1` holds (see
`TwoPeriod.cex_did_ne_att`), and observed outcomes are defined by consistency. -/

section Counterexamples

theorem cex_condT (f : Bool → ℝ) : ∫ ω, f ω ∂cexMeasure[|treated id] = f true := by
  rw [show treated (id : Bool → Bool) = {true} from cex_treated]
  exact DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (cex_measure_ne_zero true)
    fun ω hω => by rw [Set.mem_singleton_iff.mp hω]

theorem cex_condC (f : Bool → ℝ) : ∫ ω, f ω ∂cexMeasure[|control id] = f false := by
  rw [show control (id : Bool → Bool) = {false} from cex_control]
  exact DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (cex_measure_ne_zero false)
    fun ω hω => by rw [Set.mem_singleton_iff.mp hω]

/-- Potential outcomes with proportional growth and no treatment effect: the treated unit's
outcome is `1` before and `2` after, the comparison unit's `2` before and `4` after, along both
paths. -/
def cexLogY : Period → Bool → Bool → ℝ
  | .pre, _, ω => if ω then 1 else 2
  | .post, _, ω => if ω then 2 else 4

/-- Potential outcomes with additive growth and no treatment effect: the treated unit's outcome
is `1` before and `2` after, the comparison unit's `2` before and `3` after, along both
paths. -/
def cexAddY : Period → Bool → Bool → ℝ
  | .pre, _, ω => if ω then 1 else 2
  | .post, _, ω => if ω then 2 else 3

/-- Observed outcomes defined by consistency from potential outcomes `Y`. -/
def cexObs (Y : Period → Bool → Bool → ℝ) (t : Period) (ω : Bool) : ℝ := Y t (cexGroup ω) ω

theorem cex_consistency (Y : Period → Bool → Bool → ℝ) : Consistency cexGroup Y (cexObs Y) :=
  fun _ _ => rfl

/-- **Log-scale parallel trends without additive parallel trends.** With proportional growth
and no treatment effect, no anticipation and log-scale parallel trends hold and additive
parallel trends fails; the ATT and `ratioDid` are `0` but the difference in differences is
`-1`. -/
theorem cexLog_spec :
    Consistency cexGroup cexLogY (cexObs cexLogY) ∧
      NoAnticipation cexMeasure cexGroup cexLogY ∧ LogParallelTrends cexMeasure cexGroup cexLogY ∧
      ¬ ParallelTrends cexMeasure cexGroup cexLogY ∧ att cexMeasure cexGroup cexLogY = 0 ∧
      ratioDid cexMeasure cexGroup (cexObs cexLogY) = 0 ∧
      did cexMeasure cexGroup (cexObs cexLogY) = -1 := by
  refine ⟨cex_consistency _, ?_⟩
  have hlog : LogParallel 1 2 2 4 := log_not_additive.1
  simp only [NoAnticipation, LogParallelTrends, ParallelTrends, att, ratioDid, did, cexObs,
    cexGroup, cexLogY, cex_condT, cex_condC]
  norm_num
  exact hlog

/-- **Additive parallel trends without log-scale parallel trends.** With additive growth and no
treatment effect, no anticipation and additive parallel trends hold and log-scale parallel
trends fails; the ATT and the difference in differences are `0` but `ratioDid` is `1 / 2`. -/
theorem cexAdd_spec :
    Consistency cexGroup cexAddY (cexObs cexAddY) ∧
      NoAnticipation cexMeasure cexGroup cexAddY ∧ ParallelTrends cexMeasure cexGroup cexAddY ∧
      ¬ LogParallelTrends cexMeasure cexGroup cexAddY ∧ att cexMeasure cexGroup cexAddY = 0 ∧
      did cexMeasure cexGroup (cexObs cexAddY) = 0 ∧
      ratioDid cexMeasure cexGroup (cexObs cexAddY) = 1 / 2 := by
  refine ⟨cex_consistency _, ?_⟩
  have hlog : ¬ LogParallel 1 2 2 3 := additive_not_log.2
  simp only [NoAnticipation, LogParallelTrends, ParallelTrends, att, ratioDid, did, cexObs,
    cexGroup, cexAddY, cex_condT, cex_condC]
  norm_num
  exact hlog

end Counterexamples

end DiDScale

end CausalInference
