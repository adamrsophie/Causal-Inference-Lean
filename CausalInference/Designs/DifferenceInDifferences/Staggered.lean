/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Designs.DifferenceInDifferences.TwoPeriod
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Order.WithBot

/-!
# Staggered adoption difference in differences

Group-time average treatment effects with staggered, absorbing treatment adoption, following
Callaway and Sant'Anna (2021), *Difference-in-differences with multiple time periods*.

Periods are natural numbers. The cohort `Gc ω : WithTop ℕ` of a unit is the first period in
which it is treated, with `⊤` meaning never treated. Potential outcomes `Y t g` are indexed by
the period `t` and the adoption date `g`; `Y t ⊤` is the never-treated potential outcome.

## Main definitions

* `Staggered.Consistency`, `Staggered.NoAnticipation`: observed outcomes follow the unit's own
  adoption date; before adoption, potential outcomes coincide almost surely with the
  never-treated ones.
* `Staggered.MeanNoAnticipation`, `Staggered.MeanNoAnticipationNotYetTreated`: no anticipation
  in conditional means, with exactly the equalities the identification theorems use.
* `Staggered.ParallelTrendsNeverTreated`, `Staggered.ParallelTrendsNotYetTreated`: one-period
  parallel trends in never-treated potential outcomes, against the never-treated group or the
  not-yet-treated group.
* `Staggered.att g t = E[Y t g - Y t ⊤ | Gc = g]`, the group-time average treatment effect.
* `Staggered.eventTimeAggregate`: the cohort-size-weighted average of `ATT(g, g + e)`.

## Main results

* `Staggered.att_eq_did_neverTreated`: identification of `ATT(g, t)` by the difference in
  differences between cohort `g` and the never-treated group, relative to a base period `b`,
  under no anticipation in means; `att_eq_did_neverTreated_of_noAnticipation` is the almost
  sure version.
* `Staggered.att_eq_did_notYetTreated`: the same with the not-yet-treated group `{Gc > t}`.
* `Staggered.att_eq_zero_of_lt`, `Staggered.did_eq_zero_of_lt_neverTreated`: pre-period effects
  vanish, and the pre-trend difference in differences is `0`.
* `Staggered.measurableSet_notYetTreated`: measurability from the cohort events.
* `Staggered.eventTimeAggregate_mem_convexHull`: the aggregate is a convex combination of the
  group-time effects; `eventTimeAggregate_eq_sum_did` identifies it.
* `Staggered.att_eq_did_of_twoPeriod`: the two by two theorem recovered from the
  staggered one through the embedding `toCohort`, `toY`, `toYobs`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace CausalInference

namespace Staggered

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cohort first treated in period `g` (`g = ⊤`: the never-treated group). -/
def cohort (Gc : Ω → WithTop ℕ) (g : WithTop ℕ) : Set Ω := {ω | Gc ω = g}

/-- The units not yet treated in period `t`, `{Gc > t}`; it contains the never-treated. -/
def notYetTreated (Gc : Ω → WithTop ℕ) (t : ℕ) : Set Ω := {ω | (t : WithTop ℕ) < Gc ω}

/-- **Consistency.** The observed outcome in period `t` is the potential outcome under the
unit's own adoption date. -/
def Consistency (Gc : Ω → WithTop ℕ) (Y : ℕ → WithTop ℕ → Ω → ℝ) (Yobs : ℕ → Ω → ℝ) :
    Prop :=
  ∀ t ω, Yobs t ω = Y t (Gc ω) ω

/-- **No anticipation** (almost surely). In every period strictly before a unit's adoption
date, its potential outcome under that adoption date equals its never-treated potential
outcome. -/
def NoAnticipation (μ : Measure Ω) (Gc : Ω → WithTop ℕ) (Y : ℕ → WithTop ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ t : ℕ, (t : WithTop ℕ) < Gc ω → Y t (Gc ω) ω = Y t ⊤ ω

/-- **Parallel trends against the never-treated group**, for cohort `g` between periods `s`
and `s + 1`: `E[Y (s+1) ⊤ - Y s ⊤ | Gc = g] = E[Y (s+1) ⊤ - Y s ⊤ | Gc = ⊤]`. -/
def ParallelTrendsNeverTreated (μ : Measure Ω) (Gc : Ω → WithTop ℕ)
    (Y : ℕ → WithTop ℕ → Ω → ℝ) (g s : ℕ) : Prop :=
  ∫ ω, (Y (s + 1) ⊤ ω - Y s ⊤ ω) ∂μ[|cohort Gc g]
    = ∫ ω, (Y (s + 1) ⊤ ω - Y s ⊤ ω) ∂μ[|cohort Gc ⊤]

/-- **Parallel trends against the not-yet-treated group** `{Gc > t}`, for cohort `g` between
periods `s` and `s + 1`:
`E[Y (s+1) ⊤ - Y s ⊤ | Gc = g] = E[Y (s+1) ⊤ - Y s ⊤ | Gc > t]`. -/
def ParallelTrendsNotYetTreated (μ : Measure Ω) (Gc : Ω → WithTop ℕ)
    (Y : ℕ → WithTop ℕ → Ω → ℝ) (g t s : ℕ) : Prop :=
  ∫ ω, (Y (s + 1) ⊤ ω - Y s ⊤ ω) ∂μ[|cohort Gc g]
    = ∫ ω, (Y (s + 1) ⊤ ω - Y s ⊤ ω) ∂μ[|notYetTreated Gc t]

/-- The **group-time average treatment effect** `ATT(g, t) = E[Y t g - Y t ⊤ | Gc = g]`. -/
noncomputable def att (μ : Measure Ω) (Gc : Ω → WithTop ℕ) (Y : ℕ → WithTop ℕ → Ω → ℝ)
    (g t : ℕ) : ℝ :=
  ∫ ω, (Y t g ω - Y t ⊤ ω) ∂μ[|cohort Gc g]

/-- The observed long difference in differences between the events `s` and `c`, from base
period `b` to period `t`. -/
noncomputable def did (μ : Measure Ω) (Yobs : ℕ → Ω → ℝ) (s c : Set Ω) (b t : ℕ) : ℝ :=
  (∫ ω, Yobs t ω ∂μ[|s] - ∫ ω, Yobs b ω ∂μ[|s]) - (∫ ω, Yobs t ω ∂μ[|c] - ∫ ω, Yobs b ω ∂μ[|c])

/-- **No anticipation in means** for cohort `g` at base period `b`:
`E[Y b g | Gc = g] = E[Y b ⊤ | Gc = g]`. This is the only no-anticipation restriction on the
treated cohort that the identification theorems use; it follows from the almost sure
`NoAnticipation` when `b < g` (`meanNoAnticipation_of_noAnticipation`). -/
def MeanNoAnticipation (μ : Measure Ω) (Gc : Ω → WithTop ℕ) (Y : ℕ → WithTop ℕ → Ω → ℝ)
    (g b : ℕ) : Prop :=
  ∫ ω, Y b g ω ∂μ[|cohort Gc g] = ∫ ω, Y b ⊤ ω ∂μ[|cohort Gc g]

/-- **No anticipation in means for the not-yet-treated group** `{Gc > t}` at periods `b` and
`t`: the observed mean equals the never-treated mean,
`E[Yobs b | Gc > t] = E[Y b ⊤ | Gc > t]` and `E[Yobs t | Gc > t] = E[Y t ⊤ | Gc > t]`. Under
consistency it follows from the almost sure `NoAnticipation` when `b ≤ t`
(`meanNoAnticipationNotYetTreated_of_noAnticipation`). -/
def MeanNoAnticipationNotYetTreated (μ : Measure Ω) (Gc : Ω → WithTop ℕ)
    (Y : ℕ → WithTop ℕ → Ω → ℝ) (Yobs : ℕ → Ω → ℝ) (b t : ℕ) : Prop :=
  ∫ ω, Yobs b ω ∂μ[|notYetTreated Gc t] = ∫ ω, Y b ⊤ ω ∂μ[|notYetTreated Gc t] ∧
    ∫ ω, Yobs t ω ∂μ[|notYetTreated Gc t] = ∫ ω, Y t ⊤ ω ∂μ[|notYetTreated Gc t]

omit [MeasurableSpace Ω] in
/-- The not-yet-treated group in period `t` is the complement of the cohorts `0, …, t`. -/
theorem notYetTreated_eq_compl (Gc : Ω → WithTop ℕ) (t : ℕ) :
    notYetTreated Gc t = (⋃ k ∈ Finset.range (t + 1), cohort Gc k)ᶜ := by
  ext ω
  simp only [notYetTreated, cohort, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion,
    Finset.mem_range, not_exists]
  generalize Gc ω = x
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    constructor
    · intro h k hk heq
      have h1 : n = k := WithTop.coe_eq_coe.mp heq
      have h2 : t < n := WithTop.coe_lt_coe.mp h
      omega
    · intro h
      by_contra hn
      have h1 : n ≤ t := WithTop.coe_le_coe.mp (not_lt.mp hn)
      exact h n (by omega) rfl

/-- **Measurability of the not-yet-treated group** from the measurability of the cohort events
`{Gc = k}`, `k ∈ ℕ`. -/
theorem measurableSet_notYetTreated {Gc : Ω → WithTop ℕ}
    (h : ∀ k : ℕ, MeasurableSet (cohort Gc k)) (t : ℕ) :
    MeasurableSet (notYetTreated Gc t) := by
  rw [notYetTreated_eq_compl]
  exact (Finset.measurableSet_biUnion _ fun k _ => h k).compl

/-- One-period parallel trends between two events, for every period from `b` to `t`, imply
parallel long differences from `b` to `t`, when `m r` is integrable for `b ≤ r ≤ t`. -/
theorem long_parallel_trends {μ : Measure Ω} {m : ℕ → Ω → ℝ} {s c : Set Ω} {b t : ℕ}
    (hbt : b ≤ t) (hm : ∀ r, b ≤ r → r ≤ t → Integrable (m r) μ)
    (hstep : ∀ r, b ≤ r → r < t →
      ∫ ω, (m (r + 1) ω - m r ω) ∂μ[|s] = ∫ ω, (m (r + 1) ω - m r ω) ∂μ[|c]) :
    ∫ ω, (m t ω - m b ω) ∂μ[|s] = ∫ ω, (m t ω - m b ω) ∂μ[|c] := by
  induction t, hbt using Nat.le_induction with
  | base => simp
  | succ n hbn ih =>
    have h1 := ih (fun r hr hrn => hm r hr (by omega)) fun r hr hrn => hstep r hr (by omega)
    have h2 := hstep n hbn (by omega)
    have hi : ∀ r, b ≤ r → r ≤ n + 1 → ∀ u : Set Ω, Integrable (m r) μ[|u] :=
      fun r h h' u => DiD.integrable_cond (hm r h h') u
    have e : ∀ u : Set Ω, ∫ ω, (m (n + 1) ω - m b ω) ∂μ[|u]
        = ∫ ω, (m (n + 1) ω - m n ω) ∂μ[|u] + ∫ ω, (m n ω - m b ω) ∂μ[|u] := by
      intro u
      rw [← integral_add (f := fun ω => m (n + 1) ω - m n ω) (g := fun ω => m n ω - m b ω)
        ((hi _ (by omega) le_rfl u).sub (hi n hbn (by omega) u))
        ((hi n hbn (by omega) u).sub (hi b le_rfl (by omega) u))]
      congr 1
      ext ω
      ring
    rw [e s, e c, h1, h2]

/-- On cohort `g`, consistency makes the observed outcome the potential outcome under adoption
at `g`. -/
theorem ae_cond_cohort_obs {μ : Measure Ω} {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ}
    {Yobs : ℕ → Ω → ℝ} {g : WithTop ℕ} (hg : MeasurableSet (cohort Gc g))
    (hcons : Consistency Gc Y Yobs) (r : ℕ) :
    ∀ᵐ ω ∂μ[|cohort Gc g], Yobs r ω = Y r g ω :=
  ae_cond_of_forall_mem hg fun ω hω => by rw [hcons, show Gc ω = g from hω]

/-- Under no anticipation, the mean of the potential outcome under adoption at `g` in a base
period `b < g` equals the mean never-treated outcome, given cohort `g`. -/
theorem integral_cond_cohort_base {μ : Measure Ω} {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {g b : ℕ} (hg : MeasurableSet (cohort Gc g))
    (hNA : NoAnticipation μ Gc Y) (hbg : b < g) :
    ∫ ω, Y b ⊤ ω ∂μ[|cohort Gc g] = ∫ ω, Y b g ω ∂μ[|cohort Gc g] := by
  refine integral_congr_ae ?_
  filter_upwards [ae_cond_mem hg, cond_absolutelyContinuous.ae_le hNA] with ω hω hna
  have hω' : Gc ω = g := hω
  have := hna b (by rw [hω']; exact_mod_cast hbg)
  rw [hω'] at this
  exact this.symm

/-- Under consistency and almost sure no anticipation, on the not-yet-treated group `{Gc > t}`
the observed outcome in any period `r ≤ t` is the never-treated potential outcome. -/
theorem ae_cond_notYetTreated_obs {μ : Measure Ω} {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {r t : ℕ}
    (hnyt : MeasurableSet (notYetTreated Gc t)) (hcons : Consistency Gc Y Yobs)
    (hNA : NoAnticipation μ Gc Y) (hrt : r ≤ t) :
    ∀ᵐ ω ∂μ[|notYetTreated Gc t], Yobs r ω = Y r ⊤ ω := by
  filter_upwards [ae_cond_mem hnyt, cond_absolutelyContinuous.ae_le hNA] with ω hω hna
  have hω' : (t : WithTop ℕ) < Gc ω := hω
  rw [hcons]
  exact hna r (lt_of_le_of_lt (by exact_mod_cast hrt) hω')

/-- The almost sure `NoAnticipation` implies no anticipation in means for cohort `g` at any
base period `b < g`. -/
theorem meanNoAnticipation_of_noAnticipation {μ : Measure Ω} {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {g b : ℕ} (hg : MeasurableSet (cohort Gc g))
    (hNA : NoAnticipation μ Gc Y) (hbg : b < g) : MeanNoAnticipation μ Gc Y g b :=
  (integral_cond_cohort_base hg hNA hbg).symm

/-- Under consistency, the almost sure `NoAnticipation` implies no anticipation in means for the
not-yet-treated group `{Gc > t}` at periods `b ≤ t` and `t`. -/
theorem meanNoAnticipationNotYetTreated_of_noAnticipation {μ : Measure Ω}
    {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {b t : ℕ}
    (hnyt : MeasurableSet (notYetTreated Gc t)) (hcons : Consistency Gc Y Yobs)
    (hNA : NoAnticipation μ Gc Y) (hbt : b ≤ t) :
    MeanNoAnticipationNotYetTreated μ Gc Y Yobs b t := by
  have hc := fun r (hrt : r ≤ t) => ae_cond_notYetTreated_obs (μ := μ) hnyt hcons hNA hrt
  exact ⟨integral_congr_ae (hc b hbt), integral_congr_ae (hc t le_rfl)⟩

/-- **Identification of `ATT(g, t)` with never-treated controls** (Callaway and Sant'Anna).
Let `μ` be a finite measure under which cohort `g` and the never-treated group have positive
mass, and `b ≤ t` (the usual choice is the base period `b = g - 1` for `g ≥ 1`). Under
consistency, no anticipation in means for cohort `g` at the base period `b`, one-period
parallel trends between cohort `g` and the never-treated group in every period from `b` to `t`,
and integrability of `Y b g`, `Y t g`, and of the never-treated outcomes `Y r ⊤` for
`b ≤ r ≤ t`, `ATT(g, t) = (E[Yobs t | Gc = g] - E[Yobs b | Gc = g]) -
(E[Yobs t | Gc = ⊤] - E[Yobs b | Gc = ⊤])`. -/
theorem att_eq_did_neverTreated {μ : Measure Ω} [IsFiniteMeasure μ] {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {g b t : ℕ}
    (hg : MeasurableSet (cohort Gc g)) (hnev : MeasurableSet (cohort Gc ⊤))
    (hgpos : μ (cohort Gc g) ≠ 0) (hnevpos : μ (cohort Gc ⊤) ≠ 0)
    (hcons : Consistency Gc Y Yobs) (hNA : MeanNoAnticipation μ Gc Y g b) (hbt : b ≤ t)
    (hPT : ∀ r, b ≤ r → r < t → ParallelTrendsNeverTreated μ Gc Y g r)
    (hYgb : Integrable (Y b g) μ) (hYgt : Integrable (Y t g) μ)
    (hY0 : ∀ r, b ≤ r → r ≤ t → Integrable (Y r ⊤) μ) :
    att μ Gc Y g t = did μ Yobs (cohort Gc g) (cohort Gc ⊤) b t := by
  have key := DiD.did_sub_effect_eq (μ := μ) (opre := Yobs b) (opost := Yobs t)
    (y1pre := Y b g) (y1post := Y t g) (y0pre := Y b ⊤) (y0post := Y t ⊤) hgpos hnevpos
    (ae_cond_cohort_obs hg hcons b) (ae_cond_cohort_obs hg hcons t)
    (ae_cond_cohort_obs hnev hcons b) (ae_cond_cohort_obs hnev hcons t)
    (DiD.integrable_cond hYgb _) (DiD.integrable_cond hYgt _)
    (DiD.integrable_cond (hY0 b le_rfl hbt) _) (DiD.integrable_cond (hY0 t hbt le_rfl) _)
    (DiD.integrable_cond (hY0 b le_rfl hbt) _) (DiD.integrable_cond (hY0 t hbt le_rfl) _)
  rw [long_parallel_trends (m := fun r => Y r ⊤) hbt hY0 hPT, hNA, sub_self, sub_self,
    add_zero, sub_eq_zero] at key
  rw [att, did, key]

/-- **Identification of `ATT(g, t)` with not-yet-treated controls** (Callaway and Sant'Anna).
Let `μ` be a finite measure under which cohort `g` and the not-yet-treated group `{Gc > t}`
(which contains the never-treated) have positive mass, and `b ≤ t`. Under consistency, no
anticipation in means for cohort `g` at `b` and for `{Gc > t}` at `b` and `t`, one-period
parallel trends between cohort `g` and `{Gc > t}` in every period from `b` to `t`, and
integrability of `Y b g`, `Y t g`, and of `Y r ⊤` for `b ≤ r ≤ t`, and of `Yobs b`, `Yobs t`
given `{Gc > t}`,
`ATT(g, t)` equals
`(E[Yobs t | Gc = g] - E[Yobs b | Gc = g]) - (E[Yobs t | Gc > t] - E[Yobs b | Gc > t])`. The
hypothesis `g ≤ t` (post-adoption periods) keeps cohort `g` out of the comparison group; the
linear argument does not use it. -/
theorem att_eq_did_notYetTreated {μ : Measure Ω} [IsFiniteMeasure μ] {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {g b t : ℕ}
    (hg : MeasurableSet (cohort Gc g))
    (hgpos : μ (cohort Gc g) ≠ 0) (hnytpos : μ (notYetTreated Gc t) ≠ 0)
    (hcons : Consistency Gc Y Yobs) (hNA : MeanNoAnticipation μ Gc Y g b)
    (hNAc : MeanNoAnticipationNotYetTreated μ Gc Y Yobs b t) (hbt : b ≤ t) (_hgt : g ≤ t)
    (hPT : ∀ r, b ≤ r → r < t → ParallelTrendsNotYetTreated μ Gc Y g t r)
    (hYgb : Integrable (Y b g) μ) (hYgt : Integrable (Y t g) μ)
    (hYobsb : Integrable (Yobs b) μ[|notYetTreated Gc t])
    (hYobst : Integrable (Yobs t) μ[|notYetTreated Gc t])
    (hY0 : ∀ r, b ≤ r → r ≤ t → Integrable (Y r ⊤) μ) :
    att μ Gc Y g t = did μ Yobs (cohort Gc g) (notYetTreated Gc t) b t := by
  have key := DiD.did_sub_effect_eq_of_integral (μ := μ) (opre := Yobs b) (opost := Yobs t)
    (y1pre := Y b g) (y1post := Y t g) (y0pre := Y b ⊤) (y0post := Y t ⊤) hgpos hnytpos
    (integral_congr_ae (ae_cond_cohort_obs hg hcons b))
    (integral_congr_ae (ae_cond_cohort_obs hg hcons t)) hNAc.1 hNAc.2
    ((DiD.integrable_cond hYgb _).congr (Filter.EventuallyEq.symm (ae_cond_cohort_obs hg hcons b)))
    ((DiD.integrable_cond hYgt _).congr (Filter.EventuallyEq.symm (ae_cond_cohort_obs hg hcons t)))
    hYobsb hYobst (DiD.integrable_cond hYgb _) (DiD.integrable_cond hYgt _)
    (DiD.integrable_cond (hY0 b le_rfl hbt) _) (DiD.integrable_cond (hY0 t hbt le_rfl) _)
    (DiD.integrable_cond (hY0 b le_rfl hbt) _) (DiD.integrable_cond (hY0 t hbt le_rfl) _)
  rw [long_parallel_trends (m := fun r => Y r ⊤) hbt hY0 hPT, hNA, sub_self, sub_self,
    add_zero, sub_eq_zero] at key
  rw [att, did, key]

/-- **Identification with never-treated controls under almost sure no anticipation.** The
version of `att_eq_did_neverTreated` with the unit-level `NoAnticipation`, a base period
`b < g`, and integrability of every potential outcome. -/
theorem att_eq_did_neverTreated_of_noAnticipation {μ : Measure Ω} [IsFiniteMeasure μ]
    {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {g b t : ℕ}
    (hg : MeasurableSet (cohort Gc g)) (hnev : MeasurableSet (cohort Gc ⊤))
    (hgpos : μ (cohort Gc g) ≠ 0) (hnevpos : μ (cohort Gc ⊤) ≠ 0)
    (hcons : Consistency Gc Y Yobs) (hNA : NoAnticipation μ Gc Y) (hbg : b < g) (hbt : b ≤ t)
    (hPT : ∀ r, b ≤ r → r < t → ParallelTrendsNeverTreated μ Gc Y g r)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ Gc Y g t = did μ Yobs (cohort Gc g) (cohort Gc ⊤) b t :=
  att_eq_did_neverTreated hg hnev hgpos hnevpos hcons
    (meanNoAnticipation_of_noAnticipation hg hNA hbg) hbt hPT (hY _ _) (hY _ _)
    fun r _ _ => hY r ⊤

/-- **Identification with not-yet-treated controls under almost sure no anticipation.** The
version of `att_eq_did_notYetTreated` with the unit-level `NoAnticipation`, a base period
`b < g ≤ t`, and integrability of every potential outcome. -/
theorem att_eq_did_notYetTreated_of_noAnticipation {μ : Measure Ω} [IsFiniteMeasure μ]
    {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {g b t : ℕ}
    (hg : MeasurableSet (cohort Gc g)) (hnyt : MeasurableSet (notYetTreated Gc t))
    (hgpos : μ (cohort Gc g) ≠ 0) (hnytpos : μ (notYetTreated Gc t) ≠ 0)
    (hcons : Consistency Gc Y Yobs) (hNA : NoAnticipation μ Gc Y) (hbg : b < g) (hgt : g ≤ t)
    (hPT : ∀ r, b ≤ r → r < t → ParallelTrendsNotYetTreated μ Gc Y g t r)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ Gc Y g t = did μ Yobs (cohort Gc g) (notYetTreated Gc t) b t := by
  have hbt : b ≤ t := (hbg.trans_le hgt).le
  have hc := fun r (hrt : r ≤ t) => ae_cond_notYetTreated_obs (μ := μ) hnyt hcons hNA hrt
  exact att_eq_did_notYetTreated hg hgpos hnytpos hcons
    (meanNoAnticipation_of_noAnticipation hg hNA hbg)
    (meanNoAnticipationNotYetTreated_of_noAnticipation hnyt hcons hNA hbt) hbt hgt hPT
    (hY _ _) (hY _ _) ((DiD.integrable_cond (hY b ⊤) _).congr (Filter.EventuallyEq.symm (hc b hbt)))
    ((DiD.integrable_cond (hY t ⊤) _).congr (Filter.EventuallyEq.symm (hc t le_rfl)))
    fun r _ _ => hY r ⊤

/-- **Pre-period effects vanish.** Under almost sure no anticipation, `ATT(g, t) = 0` for every
period `t < g` before cohort `g` adopts. -/
theorem att_eq_zero_of_lt {μ : Measure Ω} {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ}
    {g t : ℕ} (hg : MeasurableSet (cohort Gc g)) (hNA : NoAnticipation μ Gc Y) (htg : t < g) :
    att μ Gc Y g t = 0 := by
  have h : ∀ᵐ ω ∂μ[|cohort Gc g], Y t g ω - Y t ⊤ ω = 0 := by
    filter_upwards [ae_cond_mem hg, cond_absolutelyContinuous.ae_le hNA] with ω hω hna
    have hω' : Gc ω = g := hω
    have := hna t (by rw [hω']; exact_mod_cast htg)
    rw [hω'] at this
    rw [this, sub_self]
  rw [att, integral_congr_ae h]
  simp

/-- **Pre-trend test.** Under the hypotheses of `att_eq_did_neverTreated_of_noAnticipation`,
the observed difference in differences between cohort `g` and the never-treated group from a
base period `b` to a period `t` with `b ≤ t < g` is `0`. -/
theorem did_eq_zero_of_lt_neverTreated {μ : Measure Ω} [IsFiniteMeasure μ]
    {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {g b t : ℕ}
    (hg : MeasurableSet (cohort Gc g)) (hnev : MeasurableSet (cohort Gc ⊤))
    (hgpos : μ (cohort Gc g) ≠ 0) (hnevpos : μ (cohort Gc ⊤) ≠ 0)
    (hcons : Consistency Gc Y Yobs) (hNA : NoAnticipation μ Gc Y) (hbt : b ≤ t) (htg : t < g)
    (hPT : ∀ r, b ≤ r → r < t → ParallelTrendsNeverTreated μ Gc Y g r)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    did μ Yobs (cohort Gc g) (cohort Gc ⊤) b t = 0 := by
  rw [← att_eq_did_neverTreated_of_noAnticipation hg hnev hgpos hnevpos hcons hNA
    (lt_of_le_of_lt hbt htg) hbt hPT hY, att_eq_zero_of_lt hg hNA htg]

/-! ### Aggregation at a fixed event time -/

/-- The cohort-size weight of cohort `g` within a finite set `S` of cohorts,
`P(Gc = g) / ∑_{h ∈ S} P(Gc = h)` for `g ∈ S`, and `0` for `g ∉ S`. -/
noncomputable def cohortWeight (μ : Measure Ω) (Gc : Ω → WithTop ℕ) (S : Finset ℕ) (g : ℕ) :
    ℝ :=
  if g ∈ S then μ.real (cohort Gc g) / ∑ h ∈ S, μ.real (cohort Gc h) else 0

/-- The **event-time aggregate** at event time `e`: the cohort-size-weighted average over the
cohorts `g ∈ S` of `ATT(g, g + e)`. -/
noncomputable def eventTimeAggregate (μ : Measure Ω) (Gc : Ω → WithTop ℕ)
    (Y : ℕ → WithTop ℕ → Ω → ℝ) (S : Finset ℕ) (e : ℕ) : ℝ :=
  ∑ g ∈ S, cohortWeight μ Gc S g * att μ Gc Y g (g + e)

theorem cohortWeight_nonneg (μ : Measure Ω) (Gc : Ω → WithTop ℕ) (S : Finset ℕ) (g : ℕ) :
    0 ≤ cohortWeight μ Gc S g := by
  unfold cohortWeight
  split_ifs
  · exact div_nonneg measureReal_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
  · exact le_rfl

/-- Cohorts outside `S` get weight `0`. -/
theorem cohortWeight_of_notMem {μ : Measure Ω} {Gc : Ω → WithTop ℕ} {S : Finset ℕ} {g : ℕ}
    (hg : g ∉ S) : cohortWeight μ Gc S g = 0 := by
  simp [cohortWeight, hg]

/-- The cohort weights sum to one when the cohorts in `S` have positive total probability. -/
theorem sum_cohortWeight {μ : Measure Ω} {Gc : Ω → WithTop ℕ} {S : Finset ℕ}
    (hpos : 0 < ∑ h ∈ S, μ.real (cohort Gc h)) : ∑ g ∈ S, cohortWeight μ Gc S g = 1 := by
  have h : ∀ g ∈ S, cohortWeight μ Gc S g
      = μ.real (cohort Gc g) / ∑ h ∈ S, μ.real (cohort Gc h) := fun g hg => by
    simp [cohortWeight, hg]
  rw [Finset.sum_congr rfl h, ← Finset.sum_div, div_self hpos.ne']

/-- **The event-time aggregate is a convex combination of group-time effects.** Let `μ` be a
finite measure and `S` a nonempty finite set of cohorts, each of positive mass, whose effects
`Y (g + e) g - Y (g + e) ⊤` are integrable given `Gc = g` (so that each `ATT(g, g + e)` is a
genuine mean; the convexity argument itself does not use this). Then the aggregate lies in the
convex hull of `{ATT(g, g + e) : g ∈ S}`. -/
theorem eventTimeAggregate_mem_convexHull {μ : Measure Ω} [IsFiniteMeasure μ]
    {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ} {S : Finset ℕ} (e : ℕ)
    (hne : S.Nonempty) (hS : ∀ g ∈ S, μ (cohort Gc g) ≠ 0)
    (_hint : ∀ g ∈ S, Integrable (fun ω => Y (g + e) g ω - Y (g + e) ⊤ ω) μ[|cohort Gc g]) :
    eventTimeAggregate μ Gc Y S e
      ∈ convexHull ℝ ((fun g => att μ Gc Y g (g + e)) '' (S : Set ℕ)) := by
  have hpos : 0 < ∑ h ∈ S, μ.real (cohort Gc h) :=
    Finset.sum_pos (fun g hg => ENNReal.toReal_pos (hS g hg) (measure_ne_top _ _)) hne
  exact (convex_convexHull ℝ _).sum_mem (fun g _ => cohortWeight_nonneg μ Gc S g)
    (sum_cohortWeight hpos) fun g hg => subset_convexHull ℝ _ ⟨g, hg, rfl⟩

/-- **Identification of the event-time aggregate.** If, for every cohort `g ∈ S` with base
period `base g ≤ g + e`, the hypotheses of `att_eq_did_neverTreated` hold (finite measure,
positive mass of cohort `g` and of the never-treated group, consistency, no anticipation in
means at `base g`, parallel trends from `base g` to `g + e`, integrable potential outcomes),
then the event-time aggregate equals the cohort-size-weighted sum of the observed differences in
differences `∑_{g ∈ S} w_g DiD(g, ⊤; base g, g + e)`. -/
theorem eventTimeAggregate_eq_sum_did {μ : Measure Ω} [IsFiniteMeasure μ]
    {Gc : Ω → WithTop ℕ} {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {S : Finset ℕ}
    {e : ℕ} {base : ℕ → ℕ} (hnev : MeasurableSet (cohort Gc ⊤))
    (hnevpos : μ (cohort Gc ⊤) ≠ 0) (hcons : Consistency Gc Y Yobs)
    (hS : ∀ g ∈ S, MeasurableSet (cohort Gc g) ∧ μ (cohort Gc g) ≠ 0)
    (hNA : ∀ g ∈ S, MeanNoAnticipation μ Gc Y g (base g)) (hbt : ∀ g ∈ S, base g ≤ g + e)
    (hPT : ∀ g ∈ S, ∀ r, base g ≤ r → r < g + e → ParallelTrendsNeverTreated μ Gc Y g r)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    eventTimeAggregate μ Gc Y S e
      = ∑ g ∈ S, cohortWeight μ Gc S g * did μ Yobs (cohort Gc g) (cohort Gc ⊤) (base g) (g + e) :=
  Finset.sum_congr rfl fun g hg => by
    rw [att_eq_did_neverTreated (hS g hg).1 hnev (hS g hg).2 hnevpos hcons (hNA g hg) (hbt g hg)
      (hPT g hg) (hY _ _) (hY _ _) fun r _ _ => hY r ⊤]

/-! ### From the two by two design to staggered adoption

A two-period model embeds in the staggered framework with periods `0` (pre) and `1` (post),
treated units in cohort `1` and comparison units never treated. Under this map the two by two
identification theorem is the case `g = t = 1`, `b = 0` of `att_eq_did_neverTreated`. -/

section Bridge

open TwoPeriod

/-- The period of the two by two design corresponding to a staggered period: `0 ↦ pre`, and
every later period `↦ post`. -/
def toPeriod (t : ℕ) : Period := if t = 0 then .pre else .post

/-- The adoption date of a two-period unit: `1` if treated, `⊤` (never) otherwise. -/
def toCohort (G : Ω → Bool) (ω : Ω) : WithTop ℕ := if G ω then 1 else ⊤

/-- Potential outcomes of the embedded model: adoption at any finite date is the treated path,
`⊤` the untreated path. -/
def toY (Y : Period → Bool → Ω → ℝ) (t : ℕ) (g : WithTop ℕ) (ω : Ω) : ℝ :=
  Y (toPeriod t) (decide (g ≠ ⊤)) ω

/-- Observed outcomes of the embedded model. -/
def toYobs (Yobs : Period → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := Yobs (toPeriod t) ω

omit [MeasurableSpace Ω] in
theorem cohort_toCohort_one (G : Ω → Bool) : cohort (toCohort G) 1 = treated G := by
  ext ω
  cases h : G ω <;> simp [cohort, toCohort, treated, h]

omit [MeasurableSpace Ω] in
theorem cohort_toCohort_top (G : Ω → Bool) : cohort (toCohort G) ⊤ = control G := by
  ext ω
  cases h : G ω <;> simp [cohort, toCohort, TwoPeriod.control, h]

omit [MeasurableSpace Ω] in
/-- Consistency transfers to the embedded model. -/
theorem consistency_toCohort {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ}
    {Yobs : Period → Ω → ℝ} (hcons : TwoPeriod.Consistency G Y Yobs) :
    Staggered.Consistency (toCohort G) (toY Y) (toYobs Yobs) := by
  intro t ω
  cases h : G ω <;> simp [toY, toYobs, toCohort, hcons (toPeriod t) ω, h]

/-- **The two by two theorem from the staggered one.** Under the hypotheses of
`TwoPeriod.att_eq_did`, the ATT equals the observed difference in differences; the proof maps
the model to staggered adoption and applies `att_eq_did_neverTreated` with `g = t = 1`, `b = 0`. -/
theorem att_eq_did_of_twoPeriod {μ : Measure Ω} [IsProbabilityMeasure μ]
    {G : Ω → Bool} {Y : Period → Bool → Ω → ℝ} {Yobs : Period → Ω → ℝ}
    (hG : MeasurableSet (treated G)) (hcons : TwoPeriod.Consistency G Y Yobs)
    (hNA : TwoPeriod.NoAnticipation μ G Y) (hPT : TwoPeriod.ParallelTrends μ G Y)
    (hpos : 0 < μ (treated G)) (hlt : μ (treated G) < 1)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    TwoPeriod.att μ G Y = TwoPeriod.did μ G Yobs := by
  have hC : MeasurableSet (TwoPeriod.control G) := control_eq_compl G ▸ hG.compl
  have key := att_eq_did_neverTreated (μ := μ) (Gc := toCohort G) (Y := toY Y)
    (Yobs := toYobs Yobs) (g := 1) (b := 0) (t := 1)
    (by simpa [cohort_toCohort_one] using hG) (by simpa [cohort_toCohort_top] using hC)
    (by simpa [cohort_toCohort_one] using hpos.ne')
    (by simpa [cohort_toCohort_top] using control_ne_zero hG hlt) (consistency_toCohort hcons)
    (by simpa [MeanNoAnticipation, cohort_toCohort_one, toY, toPeriod, TwoPeriod.NoAnticipation]
      using hNA) zero_le_one
    (fun r _ hr => by
      obtain rfl : r = 0 := by omega
      simpa [ParallelTrendsNeverTreated, cohort_toCohort_one, cohort_toCohort_top, toY,
        toPeriod, TwoPeriod.ParallelTrends] using hPT)
    (hY _ _) (hY _ _) fun r _ _ => hY _ _
  simpa [Staggered.att, Staggered.did, TwoPeriod.att, TwoPeriod.did, cohort_toCohort_one,
    cohort_toCohort_top, toY, toYobs, toPeriod] using key

end Bridge

end Staggered

end CausalInference
