/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

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

* `TwoPeriod.Consistency`, `TwoPeriod.NoAnticipation` (mean form),
  `TwoPeriod.UnitNoAnticipation` (unit-level form), `TwoPeriod.ParallelTrends`.
* `TwoPeriod.att`, `TwoPeriod.did`, `TwoPeriod.trendGap`, `TwoPeriod.anticipationGap`.

## Main results

* `DiD.did_sub_effect_eq`: the generic bias decomposition for two arbitrary events, reused for
  the staggered designs.
* `TwoPeriod.did_sub_att`: `DiD - ATT = trendGap + anticipationGap`, with no parallel trends.
* `TwoPeriod.att_eq_did`: identification of the ATT on a probability space under consistency,
  no anticipation, parallel trends, overlap, and integrability; `att_eq_did_of_integrable_cond`
  needs only the moments that enter the comparison.
* `TwoPeriod.noAnticipation_of_unitNoAnticipation`: the unit-level assumption implies the mean
  form under consistency.
* `TwoPeriod.cex_did_ne_att`: a concrete two-unit model satisfying consistency, no
  anticipation, and overlap where parallel trends fails and `DiD = 1`, `ATT = 0`.
* `TwoPeriod.att_eq_sum_treatedWeight_mul_didCell`: identification under conditional parallel
  trends given a covariate with finitely many values.
* `TwoPeriod.att_eq_integral_sub_integral_comp`: identification under conditional parallel
  trends given a general measurable covariate, stated with Mathlib conditional expectations.

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
events of positive measure under a finite measure `μ`, `opre, opost` observed outcomes, and
`y1pre, y1post` (treated path, integrable given `s`) and `y0pre, y0post` (untreated path,
integrable given `s` and given `c`) potential outcomes. If observed outcomes equal the
treated path almost surely given `s` and the untreated path almost surely given `c`, then the
difference in differences of observed conditional means, minus the effect
`E[y1post - y0post | s]`, equals the differential trend of untreated outcomes
`E[y0post - y0pre | s] - E[y0post - y0pre | c]` plus the anticipation term
`E[y0pre | s] - E[y1pre | s]`. No parallel trends is assumed. The positivity
and integrability hypotheses guarantee that every conditional mean in the identity is a genuine
mean; the linear argument itself does not use positivity or the integrability of `y1pre`. -/
theorem did_sub_effect_eq {μ : Measure Ω} [IsFiniteMeasure μ] {s c : Set Ω}
    {opre opost y1pre y1post y0pre y0post : Ω → ℝ} (_hs : μ s ≠ 0) (_hc : μ c ≠ 0)
    (hpre_s : ∀ᵐ ω ∂μ[|s], opre ω = y1pre ω) (hpost_s : ∀ᵐ ω ∂μ[|s], opost ω = y1post ω)
    (hpre_c : ∀ᵐ ω ∂μ[|c], opre ω = y0pre ω) (hpost_c : ∀ᵐ ω ∂μ[|c], opost ω = y0post ω)
    (_hi1pre : Integrable y1pre μ[|s]) (hi1post : Integrable y1post μ[|s])
    (hi0pre_s : Integrable y0pre μ[|s]) (hi0post_s : Integrable y0post μ[|s])
    (hi0pre_c : Integrable y0pre μ[|c]) (hi0post_c : Integrable y0post μ[|c]) :
    ((∫ ω, opost ω ∂μ[|s] - ∫ ω, opre ω ∂μ[|s]) - (∫ ω, opost ω ∂μ[|c] - ∫ ω, opre ω ∂μ[|c]))
        - ∫ ω, (y1post ω - y0post ω) ∂μ[|s]
      = (∫ ω, (y0post ω - y0pre ω) ∂μ[|s] - ∫ ω, (y0post ω - y0pre ω) ∂μ[|c])
        + (∫ ω, y0pre ω ∂μ[|s] - ∫ ω, y1pre ω ∂μ[|s]) := by
  rw [integral_congr_ae hpre_s, integral_congr_ae hpost_s,
    integral_congr_ae hpre_c, integral_congr_ae hpost_c,
    integral_sub hi1post hi0post_s, integral_sub hi0post_s hi0pre_s,
    integral_sub hi0post_c hi0pre_c]
  ring

/-- **Generic two by two bias decomposition, mean form.** The same identity as
`did_sub_effect_eq` when observed outcomes are only known to agree in conditional mean with the
relevant potential outcomes: `E[opre | s] = E[y1pre | s]`, `E[opost | s] = E[y1post | s]`,
`E[opre | c] = E[y0pre | c]`, and `E[opost | c] = E[y0post | c]`. The observed outcomes are
assumed integrable under both conditional measures so that the observed conditional means are
genuine means. -/
theorem did_sub_effect_eq_of_integral {μ : Measure Ω} [IsFiniteMeasure μ] {s c : Set Ω}
    {opre opost y1pre y1post y0pre y0post : Ω → ℝ} (_hs : μ s ≠ 0) (_hc : μ c ≠ 0)
    (hpre_s : ∫ ω, opre ω ∂μ[|s] = ∫ ω, y1pre ω ∂μ[|s])
    (hpost_s : ∫ ω, opost ω ∂μ[|s] = ∫ ω, y1post ω ∂μ[|s])
    (hpre_c : ∫ ω, opre ω ∂μ[|c] = ∫ ω, y0pre ω ∂μ[|c])
    (hpost_c : ∫ ω, opost ω ∂μ[|c] = ∫ ω, y0post ω ∂μ[|c])
    (_hopre_s : Integrable opre μ[|s]) (_hopost_s : Integrable opost μ[|s])
    (_hopre_c : Integrable opre μ[|c]) (_hopost_c : Integrable opost μ[|c])
    (_hi1pre : Integrable y1pre μ[|s]) (hi1post : Integrable y1post μ[|s])
    (hi0pre_s : Integrable y0pre μ[|s]) (hi0post_s : Integrable y0post μ[|s])
    (hi0pre_c : Integrable y0pre μ[|c]) (hi0post_c : Integrable y0post μ[|c]) :
    ((∫ ω, opost ω ∂μ[|s] - ∫ ω, opre ω ∂μ[|s]) - (∫ ω, opost ω ∂μ[|c] - ∫ ω, opre ω ∂μ[|c]))
        - ∫ ω, (y1post ω - y0post ω) ∂μ[|s]
      = (∫ ω, (y0post ω - y0pre ω) ∂μ[|s] - ∫ ω, (y0post ω - y0pre ω) ∂μ[|c])
        + (∫ ω, y0pre ω ∂μ[|s] - ∫ ω, y1pre ω ∂μ[|s]) := by
  rw [hpre_s, hpost_s, hpre_c, hpost_c,
    integral_sub hi1post hi0post_s, integral_sub hi0post_s hi0pre_s,
    integral_sub hi0post_c hi0pre_c]
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

/-- **Unit-level no anticipation** (almost surely): every treated unit's observed pre-period
outcome is its untreated potential outcome, `G ω = 1 → Yobs pre ω = Y pre 0 ω` for almost every
`ω`. Under consistency it implies the mean form `NoAnticipation`
(`noAnticipation_of_unitNoAnticipation`). -/
def UnitNoAnticipation (μ : Measure Ω) (G : Ω → Bool) (Y : Period → Bool → Ω → ℝ)
    (Yobs : Period → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, G ω = true → Yobs pre ω = Y pre false ω

/-- The pointwise form `∀ ω ∈ treated G, Yobs pre ω = Y pre false ω` implies the almost sure
unit-level no anticipation. -/
theorem unitNoAnticipation_of_forall {μ : Measure Ω} {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ}
    (h : ∀ ω ∈ treated G, Yobs pre ω = Y pre false ω) : UnitNoAnticipation μ G Y Yobs :=
  ae_of_all _ fun ω hω => h ω hω

/-- **Unit-level no anticipation implies the mean form.** Under consistency, if almost every
treated unit's observed pre-period outcome is its untreated potential outcome, then
`E[Y pre 1 | G = 1] = E[Y pre 0 | G = 1]`. -/
theorem noAnticipation_of_unitNoAnticipation {μ : Measure Ω} {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hcons : Consistency G Y Yobs) (h : UnitNoAnticipation μ G Y Yobs) :
    NoAnticipation μ G Y := by
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem hG, cond_absolutelyContinuous.ae_le h] with ω hω hna
  have hω' : G ω = true := hω
  have := hna hω'
  rw [hcons, hω'] at this
  exact this

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

/-- **Exact bias of difference in differences, local moments.** For a finite measure under
which both groups have positive mass, under consistency, with no parallel trends and no
no-anticipation assumption, the observed difference in differences minus the ATT equals the
differential trend in untreated outcomes plus the anticipation gap. Only the moments that enter
the comparison are required: the treated-path outcomes given `G = 1`, and the untreated
outcomes given `G = 1` and given `G = 0`. -/
theorem did_sub_att_of_integrable_cond {μ : Measure Ω} [IsFiniteMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hT : μ (treated G) ≠ 0) (hCpos : μ (control G) ≠ 0) (hcons : Consistency G Y Yobs)
    (hT1 : ∀ t, Integrable (Y t true) μ[|treated G])
    (hT0 : ∀ t, Integrable (Y t false) μ[|treated G])
    (hC0 : ∀ t, Integrable (Y t false) μ[|control G]) :
    did μ G Yobs - att μ G Y = trendGap μ G Y + anticipationGap μ G Y := by
  have hC : MeasurableSet (control G) := control_eq_compl G ▸ hG.compl
  have key := DiD.did_sub_effect_eq (μ := μ) (opre := Yobs pre) (opost := Yobs post)
    (y1pre := Y pre true) (y1post := Y post true) (y0pre := Y pre false)
    (y0post := Y post false) hT hCpos
    (ae_cond_of_forall_mem hG fun ω hω => by rw [hcons, show G ω = true from hω])
    (ae_cond_of_forall_mem hG fun ω hω => by rw [hcons, show G ω = true from hω])
    (ae_cond_of_forall_mem hC fun ω hω => by rw [hcons, show G ω = false from hω])
    (ae_cond_of_forall_mem hC fun ω hω => by rw [hcons, show G ω = false from hω])
    (hT1 _) (hT1 _) (hT0 _) (hT0 _) (hC0 _) (hC0 _)
  simpa [did, att, trendGap, anticipationGap] using key

/-- **Exact bias of difference in differences.** For a finite measure under which both groups
have positive mass, under consistency and integrability, with no parallel trends and no
no-anticipation assumption, the observed difference in differences minus the ATT equals the
differential trend in untreated outcomes plus the anticipation gap. -/
theorem did_sub_att {μ : Measure Ω} [IsFiniteMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hT : μ (treated G) ≠ 0) (hCpos : μ (control G) ≠ 0) (hcons : Consistency G Y Yobs)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    did μ G Yobs - att μ G Y = trendGap μ G Y + anticipationGap μ G Y :=
  did_sub_att_of_integrable_cond hG hT hCpos hcons (fun _ => DiD.integrable_cond (hY _ _) _)
    (fun _ => DiD.integrable_cond (hY _ _) _) fun _ => DiD.integrable_cond (hY _ _) _

/-- **Bias under no anticipation.** For a finite measure under which both groups have positive
mass, under consistency, no anticipation, and integrability, without parallel trends,
`DiD - ATT` equals the differential trend in untreated outcomes. -/
theorem did_sub_att_of_noAnticipation {μ : Measure Ω} [IsFiniteMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hT : μ (treated G) ≠ 0) (hCpos : μ (control G) ≠ 0)
    (hcons : Consistency G Y Yobs) (hNA : NoAnticipation μ G Y)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    did μ G Yobs - att μ G Y = trendGap μ G Y := by
  rw [did_sub_att hG hT hCpos hcons hY, noAnticipation_iff_anticipationGap_eq_zero.mp hNA, add_zero]

/-- Under a probability measure, overlap `P(G = 1) < 1` makes the comparison group non-null. -/
theorem control_ne_zero {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → Bool}
    (hG : MeasurableSet (treated G)) (hlt : μ (treated G) < 1) : μ (control G) ≠ 0 := by
  rw [control_eq_compl, prob_compl_eq_one_sub hG]
  exact (tsub_pos_of_lt hlt).ne'

/-- **Identification of the ATT in the two by two design, local moments.** On a probability
space, under consistency, no anticipation, parallel trends in untreated potential outcomes, and
overlap `0 < P(G = 1) < 1`, the ATT equals the observed difference in differences, assuming
only that the treated-path outcomes are integrable given `G = 1` and the untreated outcomes are
integrable given `G = 1` and given `G = 0`. -/
theorem att_eq_did_of_integrable_cond {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hcons : Consistency G Y Yobs) (hNA : NoAnticipation μ G Y) (hPT : ParallelTrends μ G Y)
    (hpos : 0 < μ (treated G)) (hlt : μ (treated G) < 1)
    (hT1 : ∀ t, Integrable (Y t true) μ[|treated G])
    (hT0 : ∀ t, Integrable (Y t false) μ[|treated G])
    (hC0 : ∀ t, Integrable (Y t false) μ[|control G]) :
    att μ G Y = did μ G Yobs := by
  have h := did_sub_att_of_integrable_cond hG hpos.ne' (control_ne_zero hG hlt) hcons hT1 hT0 hC0
  rw [parallelTrends_iff_trendGap_eq_zero.mp hPT,
    noAnticipation_iff_anticipationGap_eq_zero.mp hNA] at h
  linarith

/-- **Identification of the ATT in the two by two design.** On a probability space, under
consistency, no anticipation, parallel trends in untreated potential outcomes, and
integrability of every potential outcome, with overlap `0 < P(G = 1) < 1`, the ATT
`E[Y post 1 - Y post 0 | G = 1]` equals the observed difference in differences. Overlap
guarantees that neither conditional measure `μ[|G = 1]`, `μ[|G = 0]` is the zero measure. -/
theorem att_eq_did {μ : Measure Ω} [IsProbabilityMeasure μ] {G : Ω → Bool}
    {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ} (hG : MeasurableSet (treated G))
    (hcons : Consistency G Y Yobs) (hNA : NoAnticipation μ G Y) (hPT : ParallelTrends μ G Y)
    (hpos : 0 < μ (treated G)) (hlt : μ (treated G) < 1)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ G Y = did μ G Yobs :=
  att_eq_did_of_integrable_cond hG hcons hNA hPT hpos hlt
    (fun _ => DiD.integrable_cond (hY _ _) _) (fun _ => DiD.integrable_cond (hY _ _) _)
    fun _ => DiD.integrable_cond (hY _ _) _

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

theorem cex_treated_measure : cexMeasure (treated cexGroup) = 1 / 2 := by
  rw [cex_treated, cexMeasure, uniformOn_univ]
  simp

/-- **Counterexample.** A concrete two-unit model, with each unit of probability `1 / 2`,
satisfies consistency, no anticipation, and overlap `0 < P(G = 1) < 1`, but not parallel
trends; its difference in differences equals `1` while its ATT equals `0`. -/
theorem cex_did_ne_att :
    Consistency cexGroup cexY cexYobs ∧ NoAnticipation cexMeasure cexGroup cexY ∧
      0 < cexMeasure (treated cexGroup) ∧ cexMeasure (treated cexGroup) < 1 ∧
      ¬ ParallelTrends cexMeasure cexGroup cexY ∧
      did cexMeasure cexGroup cexYobs = 1 ∧ att cexMeasure cexGroup cexY = 0 := by
  have hT : MeasurableSet (treated cexGroup) := by
    rw [cex_treated]; exact MeasurableSet.singleton _
  have hlt : cexMeasure (treated cexGroup) < 1 := by
    rw [cex_treated_measure]; exact ENNReal.half_lt_self one_ne_zero ENNReal.one_ne_top
  have hpos : 0 < cexMeasure (treated cexGroup) := by
    rw [cex_treated_measure]; simp
  have h := did_sub_att_of_noAnticipation (μ := cexMeasure) (Yobs := cexYobs) hT hpos.ne'
    (control_ne_zero hT hlt) cex_consistency cex_noAnticipation
    (fun _ _ => Integrable.of_finite)
  rw [cex_trendGap, cex_att] at h
  exact ⟨cex_consistency, cex_noAnticipation, hpos, hlt, cex_not_parallelTrends,
    by linarith, cex_att⟩

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
a measurable covariate and Mathlib conditional expectation is
`att_eq_integral_sub_integral_comp`. -/
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
    have key := DiD.did_sub_effect_eq (μ := μ) (s := treated G ∩ X ⁻¹' {x})
      (c := control G ∩ X ⁻¹' {x}) (opre := Yobs pre) (opost := Yobs post)
      (y1pre := Y pre true) (y1post := Y post true) (y0pre := Y pre false)
      (y0post := Y post false) hx (hov x hx)
      (ae_cond_of_forall_mem hT fun ω hω => by rw [hcons, show G ω = true from hω.1])
      (ae_cond_of_forall_mem hT fun ω hω => by rw [hcons, show G ω = true from hω.1])
      (ae_cond_of_forall_mem hCx fun ω hω => by rw [hcons, show G ω = false from hω.1])
      (ae_cond_of_forall_mem hCx fun ω hω => by rw [hcons, show G ω = false from hω.1])
      (DiD.integrable_cond (hY _ _) _) (DiD.integrable_cond (hY _ _) _)
      (DiD.integrable_cond (hY _ _) _) (DiD.integrable_cond (hY _ _) _)
      (DiD.integrable_cond (hY _ _) _) (DiD.integrable_cond (hY _ _) _)
    have hpt := hPT x hx (hov x hx)
    have hna := hNA x
    simp only [treatedCell, controlCell] at hpt hna
    rw [hpt, hna, sub_self, sub_self, add_zero, sub_eq_zero] at key
    rw [didCell, treatedCell, controlCell, key]

end Conditional

/-! ### Conditional parallel trends given a general covariate -/

section GeneralCovariate

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **Identification under conditional parallel trends (general covariate).** Let `X : Ω → 𝒳`
be a measurable covariate on a finite measure space, `mT = μ[|G = 1]` and `mC = μ[|G = 0]` the
group conditional measures, and `σ(X)` the σ-algebra generated by `X`. Assume consistency, no
anticipation, a treated group of positive mass, integrable potential outcomes, and:

* overlap: the treated covariate law is absolutely continuous with respect to the comparison
  covariate law, `mT.map X ≪ mC.map X`;
* conditional parallel trends: one measurable function `τ` of the covariate is a version of
  `E[Y post 0 - Y pre 0 | σ(X)]` under both `mT` and `mC`;
* `φ` is a measurable version of the observed comparison-group conditional change
  `E[Yobs post - Yobs pre | σ(X)]` under `mC`.

Then `ATT = E[Yobs post - Yobs pre | G = 1] - E[φ(X) | G = 1]`: the observed treated change
minus the comparison-group conditional change, averaged over the treated covariate law. On the
comparison group the observed change is the untreated change, so `τ = φ` almost everywhere for
`mC.map X`, hence (by overlap) for `mT.map X`. Overlap also forces the comparison group to have
positive mass. -/
theorem att_eq_integral_sub_integral_comp {μ : Measure Ω} [IsFiniteMeasure μ]
    {G : Ω → Bool} {X : Ω → 𝒳} {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ}
    {τ φ : 𝒳 → ℝ} (hG : MeasurableSet (treated G)) (hpos : μ (treated G) ≠ 0)
    (hX : Measurable X) (hτ : Measurable τ) (hφ : Measurable φ)
    (hcons : Consistency G Y Yobs) (hNA : NoAnticipation μ G Y)
    (hov : (μ[|treated G]).map X ≪ (μ[|control G]).map X)
    (hPTt : (μ[|treated G])[fun ω => Y post false ω - Y pre false ω |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ[|treated G]] τ ∘ X)
    (hPTc : (μ[|control G])[fun ω => Y post false ω - Y pre false ω |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ[|control G]] τ ∘ X)
    (hφc : (μ[|control G])[fun ω => Yobs post ω - Yobs pre ω |
        MeasurableSpace.comap X inferInstance] =ᵐ[μ[|control G]] φ ∘ X)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ G Y = ∫ ω, (Yobs post ω - Yobs pre ω) ∂μ[|treated G] - ∫ ω, φ (X ω) ∂μ[|treated G] := by
  have hC : MeasurableSet (control G) := control_eq_compl G ▸ hG.compl
  have hΔ : (fun ω => Yobs post ω - Yobs pre ω)
      =ᵐ[μ[|control G]] fun ω => Y post false ω - Y pre false ω :=
    ae_cond_of_forall_mem hC fun ω hω => by
      change Yobs post ω - Yobs pre ω = _
      rw [hcons, hcons, show G ω = false from hω]
  have h1 : τ ∘ X =ᵐ[μ[|control G]] φ ∘ X :=
    hPTc.symm.trans ((condExp_congr_ae hΔ).symm.trans hφc)
  have hmeas : MeasurableSet {x | τ x = φ x} := measurableSet_eq_fun hτ hφ
  have h4 : τ ∘ X =ᵐ[μ[|treated G]] φ ∘ X :=
    (ae_map_iff hX.aemeasurable hmeas).mp
      (hov.ae_le ((ae_map_iff hX.aemeasurable hmeas).mpr h1))
  have := cond_isProbabilityMeasure (μ := μ) hpos
  have h5 : ∫ ω, (Y post false ω - Y pre false ω) ∂μ[|treated G]
      = ∫ ω, φ (X ω) ∂μ[|treated G] := by
    rw [← integral_condExp (Measurable.comap_le hX)]
    exact integral_congr_ae (hPTt.trans h4)
  have h6 : ∫ ω, (Yobs post ω - Yobs pre ω) ∂μ[|treated G]
      = ∫ ω, (Y post true ω - Y pre true ω) ∂μ[|treated G] :=
    DiD.integral_cond_congr hG fun ω hω => by
      rw [hcons, hcons, show G ω = true from hω]
  have hi : ∀ t d, Integrable (Y t d) μ[|treated G] := fun t d => DiD.integrable_cond (hY t d) _
  rw [h6, ← h5, att, integral_sub (hi _ _) (hi _ _), integral_sub (hi _ _) (hi _ _),
    integral_sub (hi _ _) (hi _ _)]
  have hna : ∫ ω, Y pre true ω ∂μ[|treated G] = ∫ ω, Y pre false ω ∂μ[|treated G] := hNA
  linarith

end GeneralCovariate

end TwoPeriod

end CausalInference
