/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.UniformOn

/-!
# Two by two difference in differences

Identification of the average treatment effect on the treated (ATT) in the canonical design with
two groups and two periods, on a probability space `(Ω, μ)` with conditional means taken against
`ProbabilityTheory.cond` (`μ[|s]`).

Potential outcomes `Y t d` are indexed by the period `t ∈ {pre, post}` and the treatment path
`d` (`true`: treated in the post period; `false`: never treated). Observed outcomes are separate
functions linked to potential outcomes by consistency, so that no anticipation is a genuine
assumption about the pre period.

## Main definitions

* `TwoPeriod.Consistency`, `TwoPeriod.NoAnticipation`, `TwoPeriod.ParallelTrends`.
* `TwoPeriod.att`, `TwoPeriod.did`, `TwoPeriod.trendGap`, `TwoPeriod.anticipationGap`.

## Main results

* `DiD.did_sub_effect_eq`: the generic bias decomposition for two arbitrary events, reused for
  the staggered designs.
* `TwoPeriod.did_sub_att`: `DiD - ATT = trendGap + anticipationGap`, with no parallel trends.
* `TwoPeriod.att_eq_did`: identification of the ATT under consistency, no anticipation,
  parallel trends, and integrability.
* `TwoPeriod.cex_did_ne_att`: a concrete two-unit model where parallel trends fails and
  `DiD = 1 ≠ 0 = ATT`.
* `TwoPeriod.att_eq_sum_treatedWeight_mul_didCell`: identification under conditional parallel
  trends given a covariate with finitely many values.

Sources: the textbook two by two argument; Callaway and Sant'Anna (2021), *Difference-in-differences
with multiple time periods*, for the formulation with potential outcomes indexed by
treatment paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CausalInference

namespace DiD

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A function integrable for `μ` is integrable for every conditional measure `μ[|s]`. -/
theorem integrable_cond {μ : Measure Ω} {f : Ω → ℝ} (hf : Integrable f μ) (s : Set Ω) :
    Integrable f μ[|s] := by
  by_cases hs : μ s = 0
  · simp [cond_eq_zero_of_meas_eq_zero hs]
  · exact (hf.restrict).smul_measure (ENNReal.inv_ne_top.mpr hs)

/-- Conditional means given a measurable event `s` only depend on the values on `s`. -/
theorem integral_cond_congr {μ : Measure Ω} {s : Set Ω} (hs : MeasurableSet s) {f g : Ω → ℝ}
    (h : ∀ ω ∈ s, f ω = g ω) : ∫ ω, f ω ∂μ[|s] = ∫ ω, g ω ∂μ[|s] := by
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem hs] with ω hω using h ω hω

/-- If `f` equals the constant `k` on a measurable event `s` of positive finite measure, then
the conditional mean of `f` given `s` is `k`. -/
theorem integral_cond_eq_of_eqOn {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) (hμs : μ s ≠ 0) {f : Ω → ℝ} {k : ℝ} (h : ∀ ω ∈ s, f ω = k) :
    ∫ ω, f ω ∂μ[|s] = k := by
  have := cond_isProbabilityMeasure (μ := μ) hμs
  rw [integral_cond_congr hs h]
  simp

/-- **Generic two by two bias decomposition.** Let `s` (treated) and `c` (comparison) be
events, `opre, opost` observed outcomes, and `y1pre, y1post` (treated path) and
`y0pre, y0post` (untreated path) potential outcomes, with `y1post, y0pre, y0post`
integrable. If observed outcomes equal the treated path almost surely given `s` and the
untreated path almost surely given `c`, then the difference in differences of observed
conditional means, minus the effect `E[y1post - y0post | s]`, equals the differential
trend of untreated outcomes `E[y0post - y0pre | s] - E[y0post - y0pre | c]` plus the
anticipation term `E[y0pre | s] - E[y1pre | s]`. No parallel trends is assumed. -/
theorem did_sub_effect_eq {μ : Measure Ω} {s c : Set Ω}
    {opre opost y1pre y1post y0pre y0post : Ω → ℝ}
    (hpre_s : ∀ᵐ ω ∂μ[|s], opre ω = y1pre ω) (hpost_s : ∀ᵐ ω ∂μ[|s], opost ω = y1post ω)
    (hpre_c : ∀ᵐ ω ∂μ[|c], opre ω = y0pre ω) (hpost_c : ∀ᵐ ω ∂μ[|c], opost ω = y0post ω)
    (hi1post : Integrable y1post μ) (hi0pre : Integrable y0pre μ) (hi0post : Integrable y0post μ) :
    ((∫ ω, opost ω ∂μ[|s] - ∫ ω, opre ω ∂μ[|s]) - (∫ ω, opost ω ∂μ[|c] - ∫ ω, opre ω ∂μ[|c]))
        - ∫ ω, (y1post ω - y0post ω) ∂μ[|s]
      = (∫ ω, (y0post ω - y0pre ω) ∂μ[|s] - ∫ ω, (y0post ω - y0pre ω) ∂μ[|c])
        + (∫ ω, y0pre ω ∂μ[|s] - ∫ ω, y1pre ω ∂μ[|s]) := by
  rw [integral_congr_ae hpre_s, integral_congr_ae hpost_s,
    integral_congr_ae hpre_c, integral_congr_ae hpost_c,
    integral_sub (integrable_cond hi1post s) (integrable_cond hi0post s),
    integral_sub (integrable_cond hi0post s) (integrable_cond hi0pre s),
    integral_sub (integrable_cond hi0post c) (integrable_cond hi0pre c)]
  ring

/-- For a finite measure, the set integral over `s` is `μ(s)` times the conditional mean given
`s`. Both sides vanish when `μ s = 0`. -/
theorem setIntegral_eq_measureReal_mul_integral_cond {μ : Measure Ω} [IsFiniteMeasure μ]
    {s : Set Ω} (f : Ω → ℝ) : ∫ ω in s, f ω ∂μ = μ.real s * ∫ ω, f ω ∂μ[|s] := by
  by_cases hs : μ s = 0
  · simp [Measure.restrict_eq_zero.mpr hs, measureReal_def, hs]
  · have hr : μ.real s ≠ 0 := by
      rw [measureReal_def]
      exact ENNReal.toReal_ne_zero.mpr ⟨hs, measure_ne_top μ s⟩
    rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
      ← measureReal_def]
    field_simp

/-- **Law of total expectation over a finite covariate.** For a finite measure, a measurable
event `s` of positive measure, a measurable covariate `X` with finitely many values, and an
integrable `f`, `E[f | s] = ∑ₓ (μ(s ∩ {X = x}) / μ(s)) E[f | s ∩ {X = x}]`. -/
theorem integral_cond_eq_sum {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω}
    (hs : MeasurableSet s) (hμs : μ s ≠ 0) {X : Ω → α} (hX : Measurable X) {f : Ω → ℝ}
    (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ[|s] = ∑ x, (μ.real (s ∩ X ⁻¹' {x}) / μ.real s) *
      ∫ ω, f ω ∂μ[|s ∩ X ⁻¹' {x}] := by
  have hcells : ∀ x, MeasurableSet (s ∩ X ⁻¹' {x}) := fun x => hs.inter (hX (.singleton x))
  have hunion : (⋃ x, s ∩ X ⁻¹' {x}) = s := by ext ω; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun x => s ∩ X ⁻¹' {x}) := by
    intro x y hxy
    refine Set.disjoint_left.mpr fun ω hx hy => hxy ?_
    exact hx.2.symm.trans hy.2
  have htot : ∫ ω in s, f ω ∂μ = ∑ x, ∫ ω in s ∩ X ⁻¹' {x}, f ω ∂μ := by
    conv_lhs => rw [← hunion]
    exact integral_iUnion_fintype hcells hdisj fun x => hf.integrableOn
  have h0 : μ.real s ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨hμs, measure_ne_top μ s⟩
  have key := setIntegral_eq_measureReal_mul_integral_cond (μ := μ) (s := s) f
  rw [htot] at key
  simp_rw [setIntegral_eq_measureReal_mul_integral_cond (μ := μ) f] at key
  rw [Finset.sum_congr rfl fun x _ => by rw [div_mul_eq_mul_div], ← Finset.sum_div, key]
  field_simp

end DiD

namespace TwoPeriod

/-- The two periods of the canonical design: before and after treatment. -/
inductive Period
  | pre
  | post
  deriving DecidableEq

open Period

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The treated group `{G = true}`. -/
def treated (G : Ω → Bool) : Set Ω := {ω | G ω = true}

/-- The comparison group `{G = false}`. -/
def control (G : Ω → Bool) : Set Ω := {ω | G ω = false}

omit [MeasurableSpace Ω] in
theorem control_eq_compl (G : Ω → Bool) : control G = (treated G)ᶜ := by
  ext ω
  simp [control, treated]

/-- **Consistency.** `Y t d` is the potential outcome in period `t` along treatment path `d`
(`d = true`: treated in the post period; `d = false`: never treated). The observed outcome in
each period is the potential outcome along the path of the unit's own group. -/
def Consistency (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) (Yobs : Period → Ω → ℝ) : Prop :=
  ∀ t ω, Yobs t ω = Y t (G ω) ω

/-- **No anticipation.** In the pre period, the treated group's mean outcome along the treated
path equals its mean untreated outcome: `E[Y pre 1 | G = 1] = E[Y pre 0 | G = 1]`. -/
def NoAnticipation (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : Prop :=
  ∫ ω, Y pre true ω ∂μ[|treated G] = ∫ ω, Y pre false ω ∂μ[|treated G]

/-- **Parallel trends** in untreated potential outcomes:
`E[Y post 0 - Y pre 0 | G = 1] = E[Y post 0 - Y pre 0 | G = 0]`. -/
def ParallelTrends (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : Prop :=
  ∫ ω, (Y post false ω - Y pre false ω) ∂μ[|treated G]
    = ∫ ω, (Y post false ω - Y pre false ω) ∂μ[|control G]

/-- The average treatment effect on the treated, `E[Y post 1 - Y post 0 | G = 1]`. -/
noncomputable def att (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : ℝ :=
  ∫ ω, (Y post true ω - Y post false ω) ∂μ[|treated G]

/-- The observed difference in differences of conditional means,
`(E[Yobs post | G = 1] - E[Yobs pre | G = 1]) - (E[Yobs post | G = 0] - E[Yobs pre | G = 0])`. -/
noncomputable def did (μ : Measure Ω) (G : Ω → Bool) (Yobs : Period → Ω → ℝ) : ℝ :=
  (∫ ω, Yobs post ω ∂μ[|treated G] - ∫ ω, Yobs pre ω ∂μ[|treated G])
    - (∫ ω, Yobs post ω ∂μ[|control G] - ∫ ω, Yobs pre ω ∂μ[|control G])

/-- The differential trend in untreated outcomes,
`E[Y post 0 - Y pre 0 | G = 1] - E[Y post 0 - Y pre 0 | G = 0]`; it is zero exactly under
parallel trends. -/
noncomputable def trendGap (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ) : ℝ :=
  ∫ ω, (Y post false ω - Y pre false ω) ∂μ[|treated G]
    - ∫ ω, (Y post false ω - Y pre false ω) ∂μ[|control G]

/-- The anticipation gap `E[Y pre 0 | G = 1] - E[Y pre 1 | G = 1]`; it is zero exactly under
no anticipation. -/
noncomputable def anticipationGap (μ : Measure Ω) (G : Ω → Bool)
    (Y : Period → Bool → Ω → ℝ) : ℝ :=
  ∫ ω, Y pre false ω ∂μ[|treated G] - ∫ ω, Y pre true ω ∂μ[|treated G]

theorem parallelTrends_iff_trendGap_eq_zero {μ : Measure Ω} {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} : ParallelTrends μ G Y ↔ trendGap μ G Y = 0 :=
  sub_eq_zero.symm

theorem noAnticipation_iff_anticipationGap_eq_zero {μ : Measure Ω} {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} : NoAnticipation μ G Y ↔ anticipationGap μ G Y = 0 := by
  rw [anticipationGap, sub_eq_zero, NoAnticipation, eq_comm]

/-- **Exact bias of difference in differences.** Under consistency and integrability, with no
parallel trends and no no-anticipation assumption, the observed difference in differences minus
the ATT equals the differential trend in untreated outcomes plus the anticipation gap. -/
theorem did_sub_att {μ : Measure Ω} {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ}
    {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G)) (hcons : Consistency G Y Yobs)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    did μ G Yobs - att μ G Y = trendGap μ G Y + anticipationGap μ G Y := by
  have hC : MeasurableSet (control G) := control_eq_compl G ▸ hG.compl
  have key := DiD.did_sub_effect_eq (μ := μ) (opre := Yobs pre) (opost := Yobs post)
    (y1pre := Y pre true) (y1post := Y post true) (y0pre := Y pre false)
    (y0post := Y post false)
    (ae_cond_of_forall_mem hG fun ω hω => by rw [hcons, show G ω = true from hω])
    (ae_cond_of_forall_mem hG fun ω hω => by rw [hcons, show G ω = true from hω])
    (ae_cond_of_forall_mem hC fun ω hω => by rw [hcons, show G ω = false from hω])
    (ae_cond_of_forall_mem hC fun ω hω => by rw [hcons, show G ω = false from hω])
    (hY _ _) (hY _ _) (hY _ _)
  simpa [did, att, trendGap, anticipationGap] using key

/-- **Bias under no anticipation.** Under consistency, no anticipation, and integrability,
without parallel trends, `DiD - ATT` equals the differential trend in untreated outcomes. -/
theorem did_sub_att_of_noAnticipation {μ : Measure Ω} {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hcons : Consistency G Y Yobs) (hNA : NoAnticipation μ G Y)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    did μ G Yobs - att μ G Y = trendGap μ G Y := by
  rw [did_sub_att hG hcons hY, noAnticipation_iff_anticipationGap_eq_zero.mp hNA, add_zero]

/-- **Identification of the ATT in the two by two design.** Under consistency, no
anticipation, parallel trends in untreated potential outcomes, and integrability of every
potential outcome, with overlap `0 < P(G = 1) < 1`, the ATT `E[Y post 1 - Y post 0 | G = 1]`
equals the observed difference in differences. Overlap excludes the degenerate case in which
one of the conditional measures `μ[|G = 1]`, `μ[|G = 0]` is the zero measure; the linear
argument itself does not use it. -/
theorem att_eq_did {μ : Measure Ω} {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ}
    {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G)) (hcons : Consistency G Y Yobs)
    (hNA : NoAnticipation μ G Y) (hPT : ParallelTrends μ G Y)
    (_hpos : 0 < μ (treated G)) (_hlt : μ (treated G) < 1)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ G Y = did μ G Yobs := by
  have h := did_sub_att_of_noAnticipation hG hcons hNA hY
  rw [parallelTrends_iff_trendGap_eq_zero.mp hPT] at h
  linarith

/-! ### A counterexample: parallel trends fails -/

section Counterexample

/-- The two-point population `Bool` with the uniform probability measure; `true` is the treated
unit and `false` the comparison unit. -/
noncomputable def cexMeasure : Measure Bool := uniformOn Set.univ

instance : IsProbabilityMeasure cexMeasure := by
  unfold cexMeasure
  infer_instance

/-- The group indicator of the counterexample: unit `ω` is treated iff `ω = true`. -/
def cexGroup : Bool → Bool := id

/-- Potential outcomes of the counterexample. Untreated outcomes are `0` in the pre period for
both units; in the post period the treated unit's untreated outcome rises to `1` and the
comparison unit's stays at `0`. The treatment has no effect: both paths coincide. -/
def cexY : Period → Bool → Bool → ℝ
  | .pre, _, _ => 0
  | .post, _, ω => if ω then 1 else 0

/-- Observed outcomes of the counterexample, defined by consistency. -/
def cexYobs (t : Period) (ω : Bool) : ℝ := cexY t (cexGroup ω) ω

theorem cex_consistency : Consistency cexGroup cexY cexYobs := fun _ _ => rfl

theorem cex_noAnticipation : NoAnticipation cexMeasure cexGroup cexY := rfl

theorem cex_measure_ne_zero (b : Bool) : cexMeasure {b} ≠ 0 := by
  rw [cexMeasure, Ne, uniformOn_eq_zero_iff Set.finite_univ]
  simp

theorem cex_treated : treated cexGroup = {true} := by
  ext ω
  simp [treated, cexGroup]

theorem cex_control : control cexGroup = {false} := by
  ext ω
  simp [control, cexGroup]

/-- In the counterexample the ATT is `0`. -/
theorem cex_att : att cexMeasure cexGroup cexY = 0 := by
  simp [att, cexY]

/-- In the counterexample the trend gap is `1`: parallel trends fails. -/
theorem cex_trendGap : trendGap cexMeasure cexGroup cexY = 1 := by
  rw [trendGap, cex_treated, cex_control,
    DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (cex_measure_ne_zero true)
      (k := 1) (by simp [cexY]),
    DiD.integral_cond_eq_of_eqOn (MeasurableSet.singleton _) (cex_measure_ne_zero false)
      (k := 0) (by simp [cexY])]
  norm_num

theorem cex_not_parallelTrends : ¬ ParallelTrends cexMeasure cexGroup cexY := by
  rw [parallelTrends_iff_trendGap_eq_zero, cex_trendGap]
  norm_num

/-- **Counterexample.** In a concrete two-unit model satisfying consistency, no anticipation,
overlap, and integrability, but not parallel trends, the difference in differences equals `1`
while the ATT equals `0`. -/
theorem cex_did_ne_att :
    did cexMeasure cexGroup cexYobs = 1 ∧ att cexMeasure cexGroup cexY = 0 ∧
      did cexMeasure cexGroup cexYobs ≠ att cexMeasure cexGroup cexY := by
  have h := did_sub_att_of_noAnticipation (μ := cexMeasure) (Yobs := cexYobs)
    (by rw [cex_treated]; exact MeasurableSet.singleton _) cex_consistency cex_noAnticipation
    (fun _ _ => Integrable.of_finite)
  rw [cex_trendGap, cex_att] at h
  refine ⟨by linarith, cex_att, ?_⟩
  rw [cex_att]
  linarith

end Counterexample

/-! ### Conditional parallel trends given a finite covariate -/

section Conditional

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The treated stratum `{G = 1, X = x}`. -/
def treatedCell (G : Ω → Bool) (X : Ω → α) (x : α) : Set Ω := treated G ∩ X ⁻¹' {x}

/-- The comparison stratum `{G = 0, X = x}`. -/
def controlCell (G : Ω → Bool) (X : Ω → α) (x : α) : Set Ω := control G ∩ X ⁻¹' {x}

/-- **No anticipation within strata:** for every `x`,
`E[Y pre 1 | G = 1, X = x] = E[Y pre 0 | G = 1, X = x]`. -/
def CondNoAnticipation (μ : Measure Ω) (G : Ω → Bool) (X : Ω → α)
    (Y : Period → Bool → Ω → ℝ) : Prop :=
  ∀ x, ∫ ω, Y pre true ω ∂μ[|treatedCell G X x] = ∫ ω, Y pre false ω ∂μ[|treatedCell G X x]

/-- **Overlap within strata:** every covariate value carried by treated units is also carried
by comparison units, `P(G = 1, X = x) > 0 → P(G = 0, X = x) > 0`. -/
def StratumOverlap (μ : Measure Ω) (G : Ω → Bool) (X : Ω → α) : Prop :=
  ∀ x, μ (treatedCell G X x) ≠ 0 → μ (controlCell G X x) ≠ 0

/-- **Conditional parallel trends:** for every covariate value `x` carried by both groups,
`E[Y post 0 - Y pre 0 | G = 1, X = x] = E[Y post 0 - Y pre 0 | G = 0, X = x]`. -/
def CondParallelTrends (μ : Measure Ω) (G : Ω → Bool) (X : Ω → α)
    (Y : Period → Bool → Ω → ℝ) : Prop :=
  ∀ x, μ (treatedCell G X x) ≠ 0 → μ (controlCell G X x) ≠ 0 →
    ∫ ω, (Y post false ω - Y pre false ω) ∂μ[|treatedCell G X x]
      = ∫ ω, (Y post false ω - Y pre false ω) ∂μ[|controlCell G X x]

/-- The observed difference in differences within stratum `X = x`. -/
noncomputable def didCell (μ : Measure Ω) (G : Ω → Bool) (X : Ω → α)
    (Yobs : Period → Ω → ℝ) (x : α) : ℝ :=
  (∫ ω, Yobs post ω ∂μ[|treatedCell G X x] - ∫ ω, Yobs pre ω ∂μ[|treatedCell G X x])
    - (∫ ω, Yobs post ω ∂μ[|controlCell G X x] - ∫ ω, Yobs pre ω ∂μ[|controlCell G X x])

/-- The weight of stratum `x` among the treated, `P(X = x | G = 1)`. -/
noncomputable def treatedWeight (μ : Measure Ω) (G : Ω → Bool) (X : Ω → α) (x : α) : ℝ :=
  μ.real (treatedCell G X x) / μ.real (treated G)

/-- The stratum weights `P(X = x | G = 1)` sum to one when the treated group has positive
probability. -/
theorem sum_treatedWeight {μ : Measure Ω} [IsFiniteMeasure μ] {G : Ω → Bool} {X : Ω → α}
    (hG : MeasurableSet (treated G)) (hX : Measurable X) (hpos : μ (treated G) ≠ 0) :
    ∑ x, treatedWeight μ G X x = 1 := by
  have h1 := DiD.integral_cond_eq_sum (μ := μ) hG hpos hX (f := fun _ => (1 : ℝ))
    (integrable_const 1)
  have := cond_isProbabilityMeasure (μ := μ) hpos
  simp only [integral_const, smul_eq_mul, mul_one, probReal_univ] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [treatedWeight, treatedCell]
  by_cases hx : μ (treated G ∩ X ⁻¹' {x}) = 0
  · simp [measureReal_def, hx]
  · have := cond_isProbabilityMeasure (μ := μ) hx
    simp

/-- **Identification under conditional parallel trends (finite covariate).** Let `X` be a
measurable covariate with finitely many values. Under consistency, no anticipation within
strata, overlap within strata, conditional parallel trends, a treated group of positive
probability, and integrability of every potential
outcome, the ATT equals the treated-weighted average of the stratum differences in differences:
`ATT = ∑ₓ P(X = x | G = 1) DiD(x)`. This is a finite-covariate result; the general version with
a measurable covariate and Mathlib conditional expectation is not stated here. -/
theorem att_eq_sum_treatedWeight_mul_didCell {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : Ω → Bool} {X : Ω → α} {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ}
    (hG : MeasurableSet (treated G)) (hX : Measurable X) (hcons : Consistency G Y Yobs)
    (hNA : CondNoAnticipation μ G X Y) (hov : StratumOverlap μ G X)
    (hPT : CondParallelTrends μ G X Y) (hpos : μ (treated G) ≠ 0)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ G Y = ∑ x, treatedWeight μ G X x * didCell μ G X Yobs x := by
  have hC : MeasurableSet (control G) := control_eq_compl G ▸ hG.compl
  rw [att, DiD.integral_cond_eq_sum (f := fun ω => Y post true ω - Y post false ω) hG hpos hX
    ((hY post true).sub (hY post false))]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ (treatedCell G X x) = 0
  · have hx' : μ (treated G ∩ X ⁻¹' {x}) = 0 := hx
    simp [treatedWeight, measureReal_def, hx, hx']
  · congr 1
    have hT := hG.inter (hX (.singleton x))
    have hCx := hC.inter (hX (.singleton x))
    have key := DiD.did_sub_effect_eq (μ := μ) (opre := Yobs pre) (opost := Yobs post)
      (y1pre := Y pre true) (y1post := Y post true) (y0pre := Y pre false)
      (y0post := Y post false)
      (ae_cond_of_forall_mem hT fun ω hω => by rw [hcons, show G ω = true from hω.1])
      (ae_cond_of_forall_mem hT fun ω hω => by rw [hcons, show G ω = true from hω.1])
      (ae_cond_of_forall_mem hCx fun ω hω => by rw [hcons, show G ω = false from hω.1])
      (ae_cond_of_forall_mem hCx fun ω hω => by rw [hcons, show G ω = false from hω.1])
      (hY _ _) (hY _ _) (hY _ _)
    have hpt := hPT x hx (hov x hx)
    have hna := hNA x
    simp only [treatedCell, controlCell] at hpt hna
    rw [hpt, hna, sub_self, sub_self, add_zero, sub_eq_zero] at key
    rw [didCell, treatedCell, controlCell, key]

end Conditional

end TwoPeriod

end CausalInference
