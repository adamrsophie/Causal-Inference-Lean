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
  adoption date; before adoption, potential outcomes coincide with the never-treated ones.
* `Staggered.ParallelTrendsNeverTreated`, `Staggered.ParallelTrendsNotYetTreated`: one-period
  parallel trends in never-treated potential outcomes, against the never-treated group or the
  not-yet-treated group.
* `Staggered.att g t = E[Y t g - Y t ⊤ | Gc = g]`, the group-time average treatment effect.
* `Staggered.eventTimeAggregate`: the cohort-size-weighted average of `ATT(g, g + e)`.

## Main results

* `Staggered.att_eq_did_neverTreated`: identification of `ATT(g, t)` by the difference in
  differences between cohort `g` and the never-treated group, relative to a base period `b < g`.
* `Staggered.att_eq_did_notYetTreated`: the same with the not-yet-treated group `{Gc > t}`.
* `Staggered.eventTimeAggregate_mem_convexHull`: the aggregate is a convex combination of the
  group-time effects.
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

/-- One-period parallel trends between two events, for every period from `b` to `t`, imply
parallel long differences from `b` to `t`. -/
theorem long_parallel_trends {μ : Measure Ω} {m : ℕ → Ω → ℝ} (hm : ∀ t, Integrable (m t) μ)
    {s c : Set Ω} {b t : ℕ} (hbt : b ≤ t)
    (hstep : ∀ r, b ≤ r → r < t →
      ∫ ω, (m (r + 1) ω - m r ω) ∂μ[|s] = ∫ ω, (m (r + 1) ω - m r ω) ∂μ[|c]) :
    ∫ ω, (m t ω - m b ω) ∂μ[|s] = ∫ ω, (m t ω - m b ω) ∂μ[|c] := by
  have hi : ∀ r (u : Set Ω), Integrable (m r) μ[|u] := fun r u => DiD.integrable_cond (hm r) u
  simp_rw [integral_sub (hi _ _) (hi _ _)] at hstep ⊢
  induction t, hbt using Nat.le_induction with
  | base => ring
  | succ n hbn ih =>
    have h1 := ih fun r hr hrn => hstep r hr (by omega)
    have h2 := hstep n hbn (by omega)
    linarith

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

/-- **Identification of `ATT(g, t)` with never-treated controls** (Callaway and Sant'Anna).
Let `b < g` be a base period before adoption of cohort `g`, and `b ≤ t`. Under consistency, no
anticipation, one-period parallel trends between cohort `g` and the never-treated group in
every period from `b` to `t`, and integrability of every potential outcome,
`ATT(g, t) = (E[Yobs t - Yobs b | Gc = g]) - (E[Yobs t - Yobs b | Gc = ⊤])`, written as the
difference of conditional means. The usual choice is `b = g - 1` for `g ≥ 1`. The positivity
hypotheses on the two groups exclude zero conditional measures; the linear argument does not
use them. -/
theorem att_eq_did_neverTreated {μ : Measure Ω} {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {g b t : ℕ}
    (hg : MeasurableSet (cohort Gc g)) (hnev : MeasurableSet (cohort Gc ⊤))
    (_hgpos : μ (cohort Gc g) ≠ 0) (_hnevpos : μ (cohort Gc ⊤) ≠ 0)
    (hcons : Consistency Gc Y Yobs) (hNA : NoAnticipation μ Gc Y) (hbg : b < g) (hbt : b ≤ t)
    (hPT : ∀ r, b ≤ r → r < t → ParallelTrendsNeverTreated μ Gc Y g r)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ Gc Y g t = did μ Yobs (cohort Gc g) (cohort Gc ⊤) b t := by
  have key := DiD.did_sub_effect_eq (μ := μ) (opre := Yobs b) (opost := Yobs t)
    (y1pre := Y b g) (y1post := Y t g) (y0pre := Y b ⊤) (y0post := Y t ⊤)
    (ae_cond_cohort_obs hg hcons b) (ae_cond_cohort_obs hg hcons t)
    (ae_cond_cohort_obs hnev hcons b) (ae_cond_cohort_obs hnev hcons t)
    (hY _ _) (hY _ _) (hY _ _)
  rw [long_parallel_trends (m := fun r => Y r ⊤) (fun r => hY r ⊤) hbt hPT,
    integral_cond_cohort_base hg hNA hbg, sub_self, sub_self, add_zero, sub_eq_zero] at key
  rw [att, did, key]

/-- **Identification of `ATT(g, t)` with not-yet-treated controls** (Callaway and Sant'Anna).
Let `b < g` and `b ≤ t`. The comparison group is `{Gc > t}`, the units not yet treated in
period `t` (including the never-treated). Under consistency, no anticipation (which now also
matters for the comparison units), one-period parallel trends between cohort `g` and `{Gc > t}`
in every period from `b` to `t`, positive probability of both groups (excluding zero
conditional measures; not used by the linear argument), and integrability,
`ATT(g, t)` equals
`(E[Yobs t | Gc = g] - E[Yobs b | Gc = g]) - (E[Yobs t | Gc > t] - E[Yobs b | Gc > t])`. -/
theorem att_eq_did_notYetTreated {μ : Measure Ω} {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {Yobs : ℕ → Ω → ℝ} {g b t : ℕ}
    (hg : MeasurableSet (cohort Gc g)) (hnyt : MeasurableSet (notYetTreated Gc t))
    (_hgpos : μ (cohort Gc g) ≠ 0) (_hnytpos : μ (notYetTreated Gc t) ≠ 0)
    (hcons : Consistency Gc Y Yobs) (hNA : NoAnticipation μ Gc Y) (hbg : b < g) (hbt : b ≤ t)
    (hPT : ∀ r, b ≤ r → r < t → ParallelTrendsNotYetTreated μ Gc Y g t r)
    (hY : ∀ t d, Integrable (Y t d) μ) :
    att μ Gc Y g t = did μ Yobs (cohort Gc g) (notYetTreated Gc t) b t := by
  have hc : ∀ r, r ≤ t → ∀ᵐ ω ∂μ[|notYetTreated Gc t], Yobs r ω = Y r ⊤ ω := by
    intro r hrt
    filter_upwards [ae_cond_mem hnyt, cond_absolutelyContinuous.ae_le hNA] with ω hω hna
    have hω' : (t : WithTop ℕ) < Gc ω := hω
    rw [hcons]
    exact hna r (lt_of_le_of_lt (by exact_mod_cast hrt) hω')
  have key := DiD.did_sub_effect_eq (μ := μ) (opre := Yobs b) (opost := Yobs t)
    (y1pre := Y b g) (y1post := Y t g) (y0pre := Y b ⊤) (y0post := Y t ⊤)
    (ae_cond_cohort_obs hg hcons b) (ae_cond_cohort_obs hg hcons t)
    (hc b hbt) (hc t le_rfl) (hY _ _) (hY _ _) (hY _ _)
  rw [long_parallel_trends (m := fun r => Y r ⊤) (fun r => hY r ⊤) hbt hPT,
    integral_cond_cohort_base hg hNA hbg, sub_self, sub_self, add_zero, sub_eq_zero] at key
  rw [att, did, key]

/-! ### Aggregation at a fixed event time -/

/-- The cohort-size weight of cohort `g` within a finite set `S` of cohorts,
`P(Gc = g) / ∑_{h ∈ S} P(Gc = h)`. -/
noncomputable def cohortWeight (μ : Measure Ω) (Gc : Ω → WithTop ℕ) (S : Finset ℕ) (g : ℕ) :
    ℝ :=
  μ.real (cohort Gc g) / ∑ h ∈ S, μ.real (cohort Gc h)

/-- The **event-time aggregate** at event time `e`: the cohort-size-weighted average over the
cohorts `g ∈ S` of `ATT(g, g + e)`. -/
noncomputable def eventTimeAggregate (μ : Measure Ω) (Gc : Ω → WithTop ℕ)
    (Y : ℕ → WithTop ℕ → Ω → ℝ) (S : Finset ℕ) (e : ℕ) : ℝ :=
  ∑ g ∈ S, cohortWeight μ Gc S g * att μ Gc Y g (g + e)

theorem cohortWeight_nonneg (μ : Measure Ω) (Gc : Ω → WithTop ℕ) (S : Finset ℕ) (g : ℕ) :
    0 ≤ cohortWeight μ Gc S g :=
  div_nonneg measureReal_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg)

/-- The cohort weights sum to one when the cohorts in `S` have positive total probability. -/
theorem sum_cohortWeight {μ : Measure Ω} {Gc : Ω → WithTop ℕ} {S : Finset ℕ}
    (hpos : 0 < ∑ h ∈ S, μ.real (cohort Gc h)) : ∑ g ∈ S, cohortWeight μ Gc S g = 1 := by
  simp only [cohortWeight]
  rw [← Finset.sum_div, div_self hpos.ne']

/-- **The event-time aggregate is a convex combination of group-time effects:** when the cohorts
in `S` have positive total probability, it lies in the convex hull of
`{ATT(g, g + e) : g ∈ S}`. -/
theorem eventTimeAggregate_mem_convexHull {μ : Measure Ω} {Gc : Ω → WithTop ℕ}
    {Y : ℕ → WithTop ℕ → Ω → ℝ} {S : Finset ℕ} (e : ℕ)
    (hpos : 0 < ∑ h ∈ S, μ.real (cohort Gc h)) :
    eventTimeAggregate μ Gc Y S e
      ∈ convexHull ℝ ((fun g => att μ Gc Y g (g + e)) '' (S : Set ℕ)) := by
  refine (convex_convexHull ℝ _).sum_mem (fun g _ => cohortWeight_nonneg μ Gc S g)
    (sum_cohortWeight hpos) fun g hg => subset_convexHull ℝ _ ⟨g, hg, rfl⟩

end Staggered

end CausalInference
