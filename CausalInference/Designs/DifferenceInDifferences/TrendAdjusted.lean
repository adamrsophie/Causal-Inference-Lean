/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.DifferenceInDifferences.TwoPeriod

/-!
# Differential trend adjusted difference in differences

A two-group design with three periods: an early pre-treatment period `base`, a late
pre-treatment period `pre`, and the treatment period `post`. When parallel trends may fail, the
differential trend adjusted estimator subtracts from the difference in differences between
`pre` and `post` the placebo difference in differences between `base` and `pre`. It identifies
the ATT when the differential trend of untreated outcomes is the same in both windows, even if
that differential trend is not zero.

Probability setting: a finite (for identification, probability) measure `μ` on a measurable
space `Ω` with panel data, conditional means taken against `ProbabilityTheory.cond`, as in
`TwoPeriod.lean`. Each window of two consecutive periods is a two by two design, and the results
reuse `TwoPeriod.did_sub_att_of_integrable_cond` on both windows.

## Main definitions

* `TrendAdjusted.Period`, `TrendAdjusted.window`: the three periods and the two by two design
  carried by a pair of periods.
* `TrendAdjusted.didBetween`, `TrendAdjusted.trendGapBetween`, `TrendAdjusted.anticipationGap`.
* `TrendAdjusted.trendAdjustedDid`: `DiD(pre → post) - DiD(base → pre)`.
* `TrendAdjusted.NoAnticipation` (in both pre-treatment periods), `TrendAdjusted.EqualTrends`.

## Main results

* `TrendAdjusted.trendAdjustedDid_sub_att`: the exact bias of the adjusted estimator,
  `trendGap(pre → post) - trendGap(base → pre) + 2 a(pre) - a(base)`, where `a(t)` is the
  anticipation gap in period `t`; no assumption on trends or anticipation.
* `TrendAdjusted.trendAdjustedDid_sub_att_of_noAnticipation`: under no anticipation in both
  pre-treatment periods, the bias is the change of the differential trend.
* `TrendAdjusted.att_eq_trendAdjustedDid`: identification under no anticipation and equal
  differential trends.
* `TrendAdjusted.cexLinear_spec`: a linear differential trend; parallel trends fails, the plain
  difference in differences is biased, and the adjusted estimator recovers the ATT.
* `TrendAdjusted.cexShock_spec`: a shock to the treated group in the treatment period; equal
  trends fails and the adjusted estimator is biased.
* `TrendAdjusted.cexDip_spec`: anticipation in the late pre-treatment period (a dip in the
  treated outcome); the adjusted estimator has bias twice the anticipation gap.

Source: NICE DSU Technical Support Document 17 (Faria, Hernandez Alava, Manca, Wailoo, 2015),
Section 2.5.1 and the note to Question 21, citing Bell, Blundell and Van Reenen (1999),
*Getting the unemployed back to work: an evaluation of the New Deal proposals*, for the
differential trend adjusted estimator, which "needs historical data with a similar trend before
treatment".
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CausalInference

namespace TrendAdjusted

open TwoPeriod (treated control)

/-- The three periods: the early pre-treatment period `base`, the late pre-treatment period
`pre`, and the treatment period `post`. -/
inductive Period
  | base
  | pre
  | post
  deriving DecidableEq

open Period

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The two by two design carried by the periods `s` (first) and `t` (second). -/
def window (s t : Period) : TwoPeriod.Period → Period
  | .pre => s
  | .post => t

/-- Potential outcomes restricted to the window `(s, t)`. -/
def restrictY (Y : Period → Bool → Ω → ℝ) (s t : Period) : TwoPeriod.Period → Bool → Ω → ℝ :=
  fun p => Y (window s t p)

/-- Observed outcomes restricted to the window `(s, t)`. -/
def restrictObs (Yobs : Period → Ω → ℝ) (s t : Period) : TwoPeriod.Period → Ω → ℝ :=
  fun p => Yobs (window s t p)

/-- **Consistency.** `Y t d` is the potential outcome in period `t` along treatment path `d`
(`d = true`: treated in period `post`; `d = false`: never treated). The observed outcome is the
potential outcome along the path of the unit's own group. -/
def Consistency (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) (Yobs : Period → Ω → ℝ) : Prop :=
  ∀ t ω, Yobs t ω = Y t (G ω) ω

omit [MeasurableSpace Ω] in
theorem Consistency.restrict {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ}
    {Yobs : Period → Ω → ℝ} (h : Consistency G Y Yobs) (s t : Period) :
    TwoPeriod.Consistency G (restrictY Y s t) (restrictObs Yobs s t) := fun _ ω => h _ ω

/-- The observed difference in differences between periods `s` and `t`. -/
noncomputable def didBetween (μ : Measure Ω) (G : Ω → Bool) (Yobs : Period → Ω → ℝ)
    (s t : Period) : ℝ :=
  TwoPeriod.did μ G (restrictObs Yobs s t)

/-- The differential trend of untreated outcomes between periods `s` and `t`,
`E[Y t 0 - Y s 0 | G = 1] - E[Y t 0 - Y s 0 | G = 0]`. -/
noncomputable def trendGapBetween (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ)
    (s t : Period) : ℝ :=
  TwoPeriod.trendGap μ G (restrictY Y s t)

/-- The anticipation gap in period `t`, `E[Y t 0 | G = 1] - E[Y t 1 | G = 1]`. -/
noncomputable def anticipationGap (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ)
    (t : Period) : ℝ :=
  ∫ ω, Y t false ω ∂μ[|treated G] - ∫ ω, Y t true ω ∂μ[|treated G]

/-- The ATT in the treatment period, `E[Y post 1 - Y post 0 | G = 1]`. -/
noncomputable def att (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : ℝ :=
  ∫ ω, (Y post true ω - Y post false ω) ∂μ[|treated G]

/-- **The differential trend adjusted difference in differences**,
`DiD(pre → post) - DiD(base → pre)`: the difference in differences of the treatment window
minus the placebo difference in differences of the pre-treatment window. -/
noncomputable def trendAdjustedDid (μ : Measure Ω) (G : Ω → Bool) (Yobs : Period → Ω → ℝ) :
    ℝ :=
  didBetween μ G Yobs pre post - didBetween μ G Yobs base pre

/-- **No anticipation in both pre-treatment periods:** `E[Y t 1 | G = 1] = E[Y t 0 | G = 1]`
for `t = base` and `t = pre`. -/
def NoAnticipation (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : Prop :=
  ∫ ω, Y base true ω ∂μ[|treated G] = ∫ ω, Y base false ω ∂μ[|treated G] ∧
    ∫ ω, Y pre true ω ∂μ[|treated G] = ∫ ω, Y pre false ω ∂μ[|treated G]

/-- **Equal differential trends:** the differential trend of untreated outcomes in the
treatment window equals that of the pre-treatment window. It holds when parallel trends holds
in both windows, but also when the groups' untreated trends differ by the same amount in both
windows. -/
def EqualTrends (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : Prop :=
  trendGapBetween μ G Y pre post = trendGapBetween μ G Y base pre

theorem noAnticipation_iff {μ : Measure Ω} {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ} :
    NoAnticipation μ G Y ↔ anticipationGap μ G Y base = 0 ∧ anticipationGap μ G Y pre = 0 := by
  unfold NoAnticipation anticipationGap
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Parallel trends in both windows implies equal differential trends. -/
theorem equalTrends_of_parallelTrends {μ : Measure Ω} {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} (h1 : TwoPeriod.ParallelTrends μ G (restrictY Y pre post))
    (h0 : TwoPeriod.ParallelTrends μ G (restrictY Y base pre)) : EqualTrends μ G Y := by
  rw [EqualTrends, trendGapBetween, trendGapBetween,
    TwoPeriod.parallelTrends_iff_trendGap_eq_zero.mp h1,
    TwoPeriod.parallelTrends_iff_trendGap_eq_zero.mp h0]

/-- **Exact bias of the trend adjusted difference in differences.** For a finite measure under
which both groups have positive mass, under consistency, with treated-path outcomes integrable
given `G = 1` and untreated outcomes integrable given `G = 1` and given `G = 0`, and with no
assumption on trends or anticipation,
`DiD(pre → post) - DiD(base → pre) - ATT
  = (trendGap(pre → post) - trendGap(base → pre)) + 2 a(pre) - a(base)`.
The anticipation gap of the late pre-treatment period enters twice: once through the treatment
window and once through the placebo window. -/
theorem trendAdjustedDid_sub_att {μ : Measure Ω} [IsFiniteMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hT : μ (treated G) ≠ 0) (hC : μ (control G) ≠ 0) (hcons : Consistency G Y Yobs)
    (hT1 : ∀ t, Integrable (Y t true) μ[|treated G])
    (hT0 : ∀ t, Integrable (Y t false) μ[|treated G])
    (hC0 : ∀ t, Integrable (Y t false) μ[|control G]) :
    trendAdjustedDid μ G Yobs - att μ G Y
      = (trendGapBetween μ G Y pre post - trendGapBetween μ G Y base pre)
        + 2 * anticipationGap μ G Y pre - anticipationGap μ G Y base := by
  have h1 := TwoPeriod.did_sub_att_of_integrable_cond hG hT hC (hcons.restrict pre post)
    (fun _ => hT1 _) (fun _ => hT0 _) fun _ => hC0 _
  have h0 := TwoPeriod.did_sub_att_of_integrable_cond hG hT hC (hcons.restrict base pre)
    (fun _ => hT1 _) (fun _ => hT0 _) fun _ => hC0 _
  have hatt0 : TwoPeriod.att μ G (restrictY Y base pre) = - anticipationGap μ G Y pre := by
    change ∫ ω, (Y pre true ω - Y pre false ω) ∂μ[|treated G] = _
    rw [anticipationGap, integral_sub (hT1 _) (hT0 _)]
    ring
  rw [hatt0] at h0
  have ha1 : TwoPeriod.anticipationGap μ G (restrictY Y pre post) = anticipationGap μ G Y pre :=
    rfl
  have ha0 : TwoPeriod.anticipationGap μ G (restrictY Y base pre) =
      anticipationGap μ G Y base := rfl
  have hatt : TwoPeriod.att μ G (restrictY Y pre post) = att μ G Y := rfl
  rw [ha1, hatt] at h1
  rw [ha0] at h0
  rw [trendAdjustedDid, didBetween, didBetween, trendGapBetween, trendGapBetween]
  linarith

/-- **Bias under no anticipation.** Under the hypotheses of `trendAdjustedDid_sub_att` and no
anticipation in both pre-treatment periods, the trend adjusted difference in differences minus
the ATT equals the change in the differential trend,
`trendGap(pre → post) - trendGap(base → pre)`. -/
theorem trendAdjustedDid_sub_att_of_noAnticipation {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ}
    (hG : MeasurableSet (treated G)) (hT : μ (treated G) ≠ 0) (hC : μ (control G) ≠ 0)
    (hcons : Consistency G Y Yobs) (hNA : NoAnticipation μ G Y)
    (hT1 : ∀ t, Integrable (Y t true) μ[|treated G])
    (hT0 : ∀ t, Integrable (Y t false) μ[|treated G])
    (hC0 : ∀ t, Integrable (Y t false) μ[|control G]) :
    trendAdjustedDid μ G Yobs - att μ G Y
      = trendGapBetween μ G Y pre post - trendGapBetween μ G Y base pre := by
  rw [trendAdjustedDid_sub_att hG hT hC hcons hT1 hT0 hC0, (noAnticipation_iff.mp hNA).1,
    (noAnticipation_iff.mp hNA).2]
  ring

/-- **Identification by the differential trend adjusted difference in differences.** On a
probability space with overlap `0 < P(G = 1) < 1`, under consistency, no anticipation in both
pre-treatment periods, and equal differential trends in the two windows, with treated-path
outcomes integrable given `G = 1` and untreated outcomes integrable given `G = 1` and given
`G = 0`, the ATT equals `DiD(pre → post) - DiD(base → pre)`. Parallel trends is not assumed. -/
theorem att_eq_trendAdjustedDid {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hcons : Consistency G Y Yobs) (hNA : NoAnticipation μ G Y) (hET : EqualTrends μ G Y)
    (hpos : 0 < μ (treated G)) (hlt : μ (treated G) < 1)
    (hT1 : ∀ t, Integrable (Y t true) μ[|treated G])
    (hT0 : ∀ t, Integrable (Y t false) μ[|treated G])
    (hC0 : ∀ t, Integrable (Y t false) μ[|control G]) :
    att μ G Y = trendAdjustedDid μ G Yobs := by
  have h := trendAdjustedDid_sub_att_of_noAnticipation hG hpos.ne'
    (TwoPeriod.control_ne_zero hG hlt) hcons hNA hT1 hT0 hC0
  rw [hET, sub_self] at h
  linarith

/-! ### Counterexamples on the two-unit population of `TwoPeriod.lean`

Each unit has probability `1 / 2`, so overlap `0 < P(G = 1) < 1` holds (see
`TwoPeriod.cex_did_ne_att`), and observed outcomes are defined by consistency. -/

section Counterexamples

open TwoPeriod (cexMeasure cexGroup cex_treated cex_control cex_measure_ne_zero)

theorem cex_condT (f : Bool → ℝ) : ∫ ω, f ω ∂cexMeasure[|treated id] = f true := by
  rw [show treated (id : Bool → Bool) = {true} from cex_treated]
  exact DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (cex_measure_ne_zero true)
    fun ω hω => by rw [Set.mem_singleton_iff.mp hω]

theorem cex_condC (f : Bool → ℝ) : ∫ ω, f ω ∂cexMeasure[|control id] = f false := by
  rw [show control (id : Bool → Bool) = {false} from cex_control]
  exact DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (cex_measure_ne_zero false)
    fun ω hω => by rw [Set.mem_singleton_iff.mp hω]

/-- The numeric index of a period: `base ↦ 0`, `pre ↦ 1`, `post ↦ 2`. -/
def Period.index : Period → ℝ
  | base => 0
  | pre => 1
  | post => 2

/-- Potential outcomes with a linear differential trend and no treatment effect: the treated
unit's outcome is `0, 1, 2` in `base, pre, post` along both paths; the comparison unit's
outcome is `0` throughout. -/
def cexLinearY (t : Period) (_d : Bool) (ω : Bool) : ℝ := if ω then t.index else 0

/-- A shock to the treated group in the treatment period, no treatment effect: the treated
unit's outcome is `0, 0, 1`; the comparison unit's outcome is `0` throughout. -/
def cexShockY (t : Period) (_d : Bool) (ω : Bool) : ℝ := if ω && t == post then 1 else 0

/-- Anticipation in the late pre-treatment period (a dip) and no effect in the treatment
period: every untreated outcome is `0`; along the treated path the treated unit's outcome is
`-1` in period `pre` and `0` otherwise. -/
def cexDipY (t : Period) (d : Bool) (ω : Bool) : ℝ := if ω && d && t == pre then -1 else 0

/-- Observed outcomes defined by consistency from potential outcomes `Y`. -/
def cexObs (Y : Period → Bool → Bool → ℝ) (t : Period) (ω : Bool) : ℝ := Y t (cexGroup ω) ω

theorem cex_consistency (Y : Period → Bool → Bool → ℝ) : Consistency cexGroup Y (cexObs Y) :=
  fun _ _ => rfl

/-- **Linear differential trend.** Parallel trends fails in the treatment window (the
differential trend is `1`) and the plain difference in differences equals `1`, but trends are
equal across windows, no anticipation holds, and the adjusted estimator equals the ATT, `0`. -/
theorem cexLinear_spec :
    Consistency cexGroup cexLinearY (cexObs cexLinearY) ∧
      NoAnticipation cexMeasure cexGroup cexLinearY ∧ EqualTrends cexMeasure cexGroup cexLinearY ∧
      trendGapBetween cexMeasure cexGroup cexLinearY pre post = 1 ∧
      didBetween cexMeasure cexGroup (cexObs cexLinearY) pre post = 1 ∧
      att cexMeasure cexGroup cexLinearY = 0 ∧
      trendAdjustedDid cexMeasure cexGroup (cexObs cexLinearY) = 0 := by
  refine ⟨cex_consistency _, ?_⟩
  simp [NoAnticipation, EqualTrends, trendGapBetween, didBetween, att, trendAdjustedDid,
    TwoPeriod.trendGap, TwoPeriod.did, restrictY, restrictObs, window, cexObs, cexLinearY,
    cex_condT, cex_condC, Period.index, cexGroup]
  norm_num

/-- **Unequal differential trends.** No anticipation holds, but the differential trend is `1`
in the treatment window and `0` in the pre-treatment window; the adjusted estimator equals `1`
while the ATT is `0`. -/
theorem cexShock_spec :
    Consistency cexGroup cexShockY (cexObs cexShockY) ∧
      NoAnticipation cexMeasure cexGroup cexShockY ∧
      trendGapBetween cexMeasure cexGroup cexShockY pre post = 1 ∧
      trendGapBetween cexMeasure cexGroup cexShockY base pre = 0 ∧
      ¬ EqualTrends cexMeasure cexGroup cexShockY ∧
      att cexMeasure cexGroup cexShockY = 0 ∧
      trendAdjustedDid cexMeasure cexGroup (cexObs cexShockY) = 1 := by
  refine ⟨cex_consistency _, ?_⟩
  simp [NoAnticipation, EqualTrends, trendGapBetween, didBetween, att, trendAdjustedDid,
    TwoPeriod.trendGap, TwoPeriod.did, restrictY, restrictObs, window, cexObs, cexShockY,
    cex_condT, cex_condC, cexGroup]

/-- **Anticipation in the late pre-treatment period.** Equal (indeed parallel) trends holds
and the ATT is `0`, but the anticipation gap in period `pre` is `1`; the adjusted estimator
equals `2`, twice the anticipation gap. -/
theorem cexDip_spec :
    Consistency cexGroup cexDipY (cexObs cexDipY) ∧ EqualTrends cexMeasure cexGroup cexDipY ∧
      anticipationGap cexMeasure cexGroup cexDipY base = 0 ∧
      anticipationGap cexMeasure cexGroup cexDipY pre = 1 ∧
      ¬ NoAnticipation cexMeasure cexGroup cexDipY ∧
      att cexMeasure cexGroup cexDipY = 0 ∧
      trendAdjustedDid cexMeasure cexGroup (cexObs cexDipY) = 2 := by
  refine ⟨cex_consistency _, ?_⟩
  simp [NoAnticipation, EqualTrends, trendGapBetween, didBetween, att, trendAdjustedDid,
    anticipationGap, TwoPeriod.trendGap, TwoPeriod.did, restrictY, restrictObs, window, cexObs,
    cexDipY, cex_condT, cex_condC, cexGroup]
  norm_num

end Counterexamples

end TrendAdjusted

end CausalInference
