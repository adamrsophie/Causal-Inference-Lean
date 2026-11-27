/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageCensoring
public import CausalInference.Survival.IPCW

/-!
# Two-stage estimation: from real times to the clock of `Survival.IPCW`

On a finite law the adjusted times and the transformed censoring times of a `TwoStageTrial`
take finitely many real values. Ordering them and replacing each time by its rank puts the
trial on the natural-number clock of `Survival.IPCW`, where weights with time-varying
covariates are available.

## Main results

* `rank`, `rank_le_rank_iff`, `rank_eq_rank_iff`: the rank of a time among the support points
  `timeSupport A D` (the values of `A` and `D`), strictly monotone on the support.
* `clockTime`, `clockCensor`: the times on the rank clock. At every support point `s`:
  observed events correspond (`mem_eventSet_iff`: `A = s ≤ D`), risk sets correspond
  (`mem_riskSet_iff`: `A ≥ s`, `D ≥ s`), remaining uncensored at the end of the interval
  corresponds (`mem_uncensored_succ_iff`: `D > s`), and so does survival
  (`rank_lt_clockTime_iff`: `A > s`).
* `TwoStageTrial.weighted_adjTime`: under the structural model, with the sequential no
  unmeasured confounding and positivity of `Survival.IPCW` on the rank clock, the weighted
  hazard at the rank of a support point `s` is the hazard `P(U - S = s) / P(U - S ≥ s)` of the
  untreated time after the secondary baseline, and the weighted product limit is its survival
  `P(U - S > s)`, by `Survival.IPCW.weightedHazard_ipcWeight` and
  `Survival.IPCW.weightedProductLimit_ipcWeight`.

* `exists_rank_eq`, `point`, `point_rank`: the ranks of the support points are exactly
  `0, …, #support - 1`, and `point j` is the support point of rank `j`.
* Real-time covariates: for a covariate process `Lt : ℝ → Ω → 𝓛` indexed by real time,
  `clockCov` reads it at the support points. The history events correspond
  (`covHist_clockCov`: the clock history at the rank of `s` is the real-time history
  `realHist` at the support points up to `s`), so do the risk cells (`riskCell_clock`), and
  the real-time assumptions `RealNUC`, `RealPositive` give those of `Survival.IPCW` on the
  clock (`switchNUC_of_real`, `switchPositive_of_real`).
* `TwoStageTrial.weighted_adjTime_real`: the weighted identification with the covariate
  process and the assumptions in real time.

Ties are not an obstruction: both layers count an event at the censoring time as observed
(`A ≤ D`, `T ≤ C` on the clock). The limit of the transport is the covariate history: the
weights of `Survival.IPCW` condition on the covariate at the support points, so the real-time
assumption `RealNUC` is stated given the history at the support points up to `s` (`realHist`),
not given the values of `Lt` at times between support points.
-/

@[expose] public section

open Finset CausalInference.Longitudinal CausalInference.Survival CausalInference.Survival.IPCW

namespace CausalInference

namespace StructuralNested

section Rank

variable {Ω : Type*} [Fintype Ω]

/-- The finite support of the times `A` and `D`. -/
noncomputable def timeSupport (A D : Ω → ℝ) : Finset ℝ := univ.image A ∪ univ.image D

/-- **The rank of a real time** in the support: the number of support points strictly below
it. On the support it is the index of the time in increasing order. -/
noncomputable def rank (A D : Ω → ℝ) (x : ℝ) : ℕ := #{y ∈ timeSupport A D | y < x}

/-- The rank is monotone. -/
theorem rank_mono (A D : Ω → ℝ) {x y : ℝ} (h : x ≤ y) : rank A D x ≤ rank A D y :=
  card_le_card fun z hz => by
    simp only [mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans_le h⟩

/-- **The rank is strictly monotone on the support.** -/
theorem rank_lt_rank (A D : Ω → ℝ) {x y : ℝ} (hx : x ∈ timeSupport A D) (h : x < y) :
    rank A D x < rank A D y := by
  apply card_lt_card
  refine ⟨fun z hz => ?_, fun hsub => ?_⟩
  · simp only [mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans h⟩
  · have : x ∈ ({y ∈ timeSupport A D | y < x} : Finset ℝ) := hsub (mem_filter.2 ⟨hx, h⟩)
    exact lt_irrefl x (mem_filter.1 this).2

/-- On the support, comparisons of ranks are comparisons of times. -/
theorem rank_le_rank_iff (A D : Ω → ℝ) {x y : ℝ} (hy : y ∈ timeSupport A D) :
    rank A D x ≤ rank A D y ↔ x ≤ y := by
  refine ⟨fun h => ?_, rank_mono A D⟩
  by_contra hxy
  exact absurd h (not_le.2 (rank_lt_rank A D hy (lt_of_not_ge hxy)))

/-- On the support, ranks are equal exactly when the times are. -/
theorem rank_eq_rank_iff (A D : Ω → ℝ) {x y : ℝ} (hx : x ∈ timeSupport A D)
    (hy : y ∈ timeSupport A D) : rank A D x = rank A D y ↔ x = y := by
  refine ⟨fun h => le_antisymm ((rank_le_rank_iff A D hy).1 h.le)
    ((rank_le_rank_iff A D hx).1 h.ge), fun h => h ▸ rfl⟩

theorem mem_support_left (A D : Ω → ℝ) (ω : Ω) : A ω ∈ timeSupport A D :=
  mem_union_left _ (mem_image_of_mem A (mem_univ ω))

theorem mem_support_right (A D : Ω → ℝ) (ω : Ω) : D ω ∈ timeSupport A D :=
  mem_union_right _ (mem_image_of_mem D (mem_univ ω))

/-- The event time on the natural-number clock. -/
noncomputable def clockTime (A D : Ω → ℝ) (ω : Ω) : ℕ := rank A D (A ω)

/-- The censoring time on the natural-number clock. -/
noncomputable def clockCensor (A D : Ω → ℝ) (ω : Ω) : ℕ := rank A D (D ω)

/-! ### The correspondence at each support point -/

variable (A D : Ω → ℝ) {s : ℝ} (hs : s ∈ timeSupport A D) (ω : Ω)
include hs

/-- An observed event at the support point `s` (`A = s ≤ D`; an event at the censoring time
is observed, the convention of both layers) is an observed event at its rank. -/
theorem mem_eventSet_iff :
    ω ∈ eventSet (clockTime A D) (clockCensor A D) (rank A D s) ↔ A ω = s ∧ s ≤ D ω := by
  simp only [eventSet, mem_filter, mem_univ, true_and]
  unfold clockTime clockCensor
  rw [rank_eq_rank_iff A D (mem_support_left A D ω) hs, rank_le_rank_iff A D
    (mem_support_right A D ω)]

omit hs in
/-- The risk set at the support point `s` (`A ≥ s`, `D ≥ s`) is the risk set at its rank. -/
theorem mem_riskSet_iff :
    ω ∈ riskSet (clockTime A D) (clockCensor A D) (rank A D s) ↔ s ≤ A ω ∧ s ≤ D ω := by
  simp only [riskSet, mem_filter, mem_univ, true_and]
  unfold clockTime clockCensor
  rw [rank_le_rank_iff A D (mem_support_left A D ω), rank_le_rank_iff A D
    (mem_support_right A D ω)]

/-- Remaining uncensored after the support point `s` (`D > s`) is remaining uncensored at the
end of the interval of its rank. -/
theorem mem_uncensored_succ_iff :
    ω ∈ uncensored (clockCensor A D) (rank A D s + 1) ↔ s < D ω := by
  simp only [uncensored, mem_filter, mem_univ, true_and, Nat.succ_le_iff]
  unfold clockCensor
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (rank_mono A D (not_lt.1 h')))
  · exact rank_lt_rank A D hs

/-- Survival past the support point `s` is survival past its rank. -/
theorem rank_lt_clockTime_iff : rank A D s < clockTime A D ω ↔ s < A ω := by
  constructor
  · intro h
    by_contra h'
    exact absurd h (not_lt.2 (rank_mono A D (not_lt.1 h')))
  · exact rank_lt_rank A D hs

omit hs in
/-- The rank of any time is at most the size of the support. -/
theorem rank_le_card (x : ℝ) : rank A D x ≤ #(timeSupport A D) := card_filter_le _ _

end Rank

/-! ### Covariates and assumptions in real time -/

section RealTime

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝓥 𝓛 : Type*} [DecidableEq 𝓥]
  [DecidableEq 𝓛] (A D : Ω → ℝ)

omit [DecidableEq Ω] in
/-- The rank of a support point is below the size of the support. -/
theorem rank_lt_card {y : ℝ} (hy : y ∈ timeSupport A D) : rank A D y < #(timeSupport A D) :=
  card_lt_card ⟨filter_subset _ _, fun h => lt_irrefl y (mem_filter.1 (h hy)).2⟩

omit [DecidableEq Ω] in
/-- **The ranks of the support points are exactly `0, …, #support - 1`.** -/
theorem exists_rank_eq {i : ℕ} (hi : i < #(timeSupport A D)) :
    ∃ y ∈ timeSupport A D, rank A D y = i := by
  have hsub : (timeSupport A D).image (rank A D) ⊆ range #(timeSupport A D) := fun j hj => by
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hj
    exact mem_range.2 (rank_lt_card A D hy)
  have hcard : #(range #(timeSupport A D)) ≤ #((timeSupport A D).image (rank A D)) := by
    rw [card_range, card_image_of_injOn fun x hx y hy h => (rank_eq_rank_iff A D hx hy).1 h]
  have := eq_of_subset_of_card_le hsub hcard
  obtain ⟨y, hy, h⟩ := mem_image.1 (this ▸ mem_range.2 hi)
  exact ⟨y, hy, h⟩

open Classical in
/-- The support point of rank `j` (`0` when there is none). -/
noncomputable def point (j : ℕ) : ℝ :=
  if h : ∃ y ∈ timeSupport A D, rank A D y = j then h.choose else 0

omit [DecidableEq Ω] in
/-- The support point of the rank of `s` is `s`. -/
theorem point_rank {s : ℝ} (hs : s ∈ timeSupport A D) : point A D (rank A D s) = s := by
  unfold point
  split_ifs with h
  · exact (rank_eq_rank_iff A D h.choose_spec.1 hs).1 h.choose_spec.2
  · exact absurd ⟨s, hs, rfl⟩ h

/-- The covariate on the rank clock: at time `j`, the real-time covariate `Lt` at the support
point of rank `j`. -/
noncomputable def clockCov (Lt : ℝ → Ω → 𝓛) (j : ℕ) (ω : Ω) : 𝓛 := Lt (point A D j) ω

/-- The real-time covariate history of `ω` at the support points up to `s`. -/
noncomputable def realHist (Lt : ℝ → Ω → 𝓛) (s : ℝ) (ω : Ω) : Finset Ω :=
  univ.filter fun ω' => ∀ u ∈ timeSupport A D, u ≤ s → Lt u ω' = Lt u ω

/-- The real-time risk cell of `ω` at `s`: uncensored through `s` (`D ≥ s`), alive after `s`
(`A > s`), with the baseline covariates and the covariate history of `ω`. -/
noncomputable def realRiskCell (V : Ω → 𝓥) (Lt : ℝ → Ω → 𝓛) (s : ℝ) (ω : Ω) : Finset Ω :=
  univ.filter (fun ω' => s ≤ D ω' ∧ s < A ω' ∧ V ω' = V ω) ∩ realHist A D Lt s ω

omit [DecidableEq Ω] in
/-- **The covariate histories correspond**: at the rank of a support point `s`, the history
event of the rank clock is the real-time history at the support points up to `s`. -/
theorem covHist_clockCov (Lt : ℝ → Ω → 𝓛) {s : ℝ} (hs : s ∈ timeSupport A D) (ω : Ω) :
    covHist (clockCov A D Lt) (rank A D s) ω = realHist A D Lt s ω := by
  ext ω'
  rw [covHist, realHist, mem_filter, mem_filter]
  simp only [mem_univ, true_and, clockCov]
  constructor
  · intro h u hu hus
    have := h (rank A D u) (rank_mono A D hus)
    rwa [point_rank A D hu] at this
  · intro h i hi
    obtain ⟨y, hy, rfl⟩ := exists_rank_eq A D (hi.trans_lt (rank_lt_card A D hs))
    rw [point_rank A D hy]
    exact h y hy ((rank_le_rank_iff A D hs).1 hi)

/-- **The risk cells correspond** at the rank of a support point. -/
theorem riskCell_clock (V : Ω → 𝓥) (Lt : ℝ → Ω → 𝓛) {s : ℝ} (hs : s ∈ timeSupport A D)
    (ω : Ω) :
    riskCell (clockTime A D) (clockCensor A D) V (clockCov A D Lt) (rank A D s) ω =
      realRiskCell A D V Lt s ω := by
  rw [riskCell, realRiskCell, covHist_clockCov A D Lt hs]
  congr 1
  ext ω'
  simp only [baselineCell, mem_filter, mem_univ, true_and]
  rw [rank_lt_clockTime_iff A D hs]
  unfold clockCensor
  rw [rank_le_rank_iff A D (mem_support_right A D ω')]

omit [DecidableEq Ω] in
/-- The uncensored event at the end of the interval of the rank of `s` is `D > s`. -/
theorem uncensored_clock {s : ℝ} (hs : s ∈ timeSupport A D) :
    uncensored (clockCensor A D) (rank A D s + 1) = univ.filter fun ω => s < D ω := by
  ext ω; rw [mem_uncensored_succ_iff A D hs]; simp

/-- **Sequential no unmeasured confounding in real time** up to `s₀`: at every support point
`s < s₀`, within every real-time risk cell, remaining uncensored after `s` is mean independent
of each event `A = u`. -/
def RealNUC (m : Ω → ℝ) (V : Ω → 𝓥) (Lt : ℝ → Ω → 𝓛) (s₀ : ℝ) : Prop :=
  ∀ s ∈ timeSupport A D, s < s₀ → ∀ (ω : Ω) (u : ℝ),
    MeanIndepOn m (realRiskCell A D V Lt s ω) (univ.filter fun ω' => A ω' = u)
      (fun ω' => if s < D ω' then 1 else 0)

/-- **Positivity in real time** up to `s₀`: at every support point `s < s₀`, every individual
of positive mass at risk after `s` has a positive probability of remaining uncensored given
its real-time risk cell. -/
def RealPositive (m : Ω → ℝ) (V : Ω → 𝓥) (Lt : ℝ → Ω → 𝓛) (s₀ : ℝ) : Prop :=
  ∀ s ∈ timeSupport A D, s < s₀ → ∀ ω, 0 < m ω → s ≤ D ω → s < A ω →
    0 < condProb m (realRiskCell A D V Lt s ω) (univ.filter fun ω' => s < D ω')

omit [DecidableEq Ω] in
/-- Every clock time below the rank of a support point `s₀` is the rank of a support point
below `s₀`. -/
theorem exists_point_lt {s₀ : ℝ} (hs₀ : s₀ ∈ timeSupport A D) {j : ℕ}
    (hj : j < rank A D s₀) : ∃ s ∈ timeSupport A D, s < s₀ ∧ rank A D s = j := by
  obtain ⟨s, hs, rfl⟩ := exists_rank_eq A D (hj.trans (rank_lt_card A D hs₀))
  refine ⟨s, hs, ?_, rfl⟩
  by_contra h
  exact absurd hj (not_lt.2 (rank_mono A D (not_lt.1 h)))

/-- **The real-time assumptions give those of `Survival.IPCW` on the rank clock.** -/
theorem switchNUC_of_real {m : Ω → ℝ} {V : Ω → 𝓥} {Lt : ℝ → Ω → 𝓛} {s₀ : ℝ}
    (hs₀ : s₀ ∈ timeSupport A D) (h : RealNUC A D m V Lt s₀) :
    SwitchNUC m (clockTime A D) (clockCensor A D) V (clockCov A D Lt) (rank A D s₀) := by
  intro j hj ω t
  obtain ⟨s, hs, hss, rfl⟩ := exists_point_lt A D hs₀ hj
  rw [riskCell_clock A D V Lt hs]
  have hf : (fun ω' => if rank A D s + 1 ≤ clockCensor A D ω' then (1 : ℝ) else 0) =
      fun ω' => if s < D ω' then 1 else 0 := funext fun ω' => by
    have := mem_uncensored_succ_iff A D hs ω'
    simp only [uncensored, mem_filter, mem_univ, true_and] at this
    simp only [this]
  rw [hf]
  by_cases ht : ∃ u ∈ timeSupport A D, rank A D u = t
  · obtain ⟨u, hu, rfl⟩ := ht
    have he : ev (clockTime A D) (rank A D u) = univ.filter fun ω' => A ω' = u := by
      ext ω'
      simp only [mem_ev, mem_filter, mem_univ, true_and, clockTime]
      exact rank_eq_rank_iff A D (mem_support_left A D ω') hu
    rw [he]
    exact h s hs hss ω u
  · have he : ev (clockTime A D) t = ∅ := by
      ext ω'
      simp only [mem_ev, clockTime, Finset.notMem_empty, iff_false]
      exact fun h' => ht ⟨A ω', mem_support_left A D ω', h'⟩
    rw [MeanIndepOn, he, inter_empty]
    simp [wsum, wmass]

/-- Positivity in real time gives positivity on the rank clock. -/
theorem switchPositive_of_real {m : Ω → ℝ} {V : Ω → 𝓥} {Lt : ℝ → Ω → 𝓛} {s₀ : ℝ}
    (hs₀ : s₀ ∈ timeSupport A D) (h : RealPositive A D m V Lt s₀) :
    SwitchPositive m (clockTime A D) (clockCensor A D) V (clockCov A D Lt) (rank A D s₀) := by
  intro j hj ω hm hC hT
  obtain ⟨s, hs, hss, rfl⟩ := exists_point_lt A D hs₀ hj
  rw [stayProb, riskCell_clock A D V Lt hs, uncensored_clock A D hs]
  refine h s hs hss ω hm ?_ ((rank_lt_clockTime_iff A D hs ω).1 hT)
  exact (rank_le_rank_iff A D (mem_support_right A D ω)).1 hC

end RealTime

/-! ### The weighted identification for the adjusted time -/

namespace TwoStageTrial

variable {Ω 𝓥 𝓛 : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝓥]
  [DecidableEq 𝓛]

/-- The adjusted time after the secondary baseline on the natural-number clock. -/
noncomputable def clockAdj (B : Ω → ℝ) (ψ : ℝ) : Ω → ℕ :=
  clockTime (M.adjTime B ψ) (M.adjCensor B ψ)

/-- The transformed censoring time on the natural-number clock. -/
noncomputable def clockCens (B : Ω → ℝ) (ψ : ℝ) : Ω → ℕ :=
  clockCensor (M.adjTime B ψ) (M.adjCensor B ψ)

/-- **Weighting with time-varying covariates for the adjusted time.** Transport the adjusted
time and the transformed censoring time of a `TwoStageTrial` to the clock of their ranks. Let
the covariates `V` (baseline) and `L j` (measured at the `j`-th support point) define the
weights of `Survival.IPCW`, and assume its sequential no unmeasured confounding and positivity
on that clock up to the rank of a support point `s`. Under the structural model on all
patients, the weighted hazard at the rank of `s` is the real-time hazard of the untreated time
after the secondary baseline at `s`, `P(U - S = s) / P(U - S ≥ s)`, and the weighted product
limit is its survival `P(U - S > s)`. -/
theorem weighted_adjTime [MeasurableSpace Ω] [MeasurableSingletonClass Ω] {p : FiniteDist Ω}
    {B : Ω → ℝ} {ψ : ℝ} (hmodel : M.ModelOn univ B ψ)
    {V : Ω → 𝓥} {L : ℕ → Ω → 𝓛} {s : ℝ}
    (hs : s ∈ timeSupport (M.adjTime B ψ) (M.adjCensor B ψ))
    (hnuc : SwitchNUC p (M.clockAdj B ψ) (M.clockCens B ψ) V L
      (rank (M.adjTime B ψ) (M.adjCensor B ψ) s))
    (hpos : SwitchPositive p (M.clockAdj B ψ) (M.clockCens B ψ) V L
      (rank (M.adjTime B ψ) (M.adjCensor B ψ) s))
    (hk : 0 < wmass p (univ.filter fun ω => s ≤ M.U ω - M.S ω)) :
    weightedHazard p (M.clockAdj B ψ) (M.clockCens B ψ)
        (ipcWeight p (M.clockAdj B ψ) (M.clockCens B ψ) V L)
        (rank (M.adjTime B ψ) (M.adjCensor B ψ) s) =
      wmass p (univ.filter fun ω => M.U ω - M.S ω = s) /
        wmass p (univ.filter fun ω => s ≤ M.U ω - M.S ω) ∧
    weightedProductLimit p (M.clockAdj B ψ) (M.clockCens B ψ)
        (ipcWeight p (M.clockAdj B ψ) (M.clockCens B ψ) V L)
        (rank (M.adjTime B ψ) (M.adjCensor B ψ) s) =
      wmass p (univ.filter fun ω => s < M.U ω - M.S ω) := by
  have hA : ∀ ω, M.adjTime B ψ ω = M.U ω - M.S ω := fun ω => by
    rw [adjTime, ← hmodel ω (mem_univ ω)]
  have e1 : (univ.filter fun ω => M.clockAdj B ψ ω = rank (M.adjTime B ψ) (M.adjCensor B ψ) s)
      = univ.filter fun ω => M.U ω - M.S ω = s := filter_congr fun ω _ => by
    rw [clockAdj, clockTime, rank_eq_rank_iff _ _ (mem_support_left _ _ ω) hs, hA]
  have e2 : (univ.filter fun ω => rank (M.adjTime B ψ) (M.adjCensor B ψ) s ≤ M.clockAdj B ψ ω)
      = univ.filter fun ω => s ≤ M.U ω - M.S ω := filter_congr fun ω _ => by
    rw [clockAdj, clockTime, rank_le_rank_iff _ _ (mem_support_left _ _ ω), hA]
  have e3 : (univ.filter fun ω => rank (M.adjTime B ψ) (M.adjCensor B ψ) s < M.clockAdj B ψ ω)
      = univ.filter fun ω => s < M.U ω - M.S ω := filter_congr fun ω _ => by
    rw [clockAdj, rank_lt_clockTime_iff _ _ hs, hA]
  have hk' : 0 < atRisk p.toMeasure (M.clockAdj B ψ)
      (rank (M.adjTime B ψ) (M.adjCensor B ψ) s) := by
    rw [atRisk_toMeasure, e2]; exact hk
  refine ⟨?_, ?_⟩
  · rw [(weightedHazard_ipcWeight p _ hnuc hpos hk').2, hazard_toMeasure, e1, e2]
  · rw [(weightedProductLimit_ipcWeight p _ hnuc hpos hk').2, survival, toMeasure_real_setOf, e3]

/-- **Weighting with time-varying covariates in real time for the adjusted time.** As
`weighted_adjTime`, with the covariate process `Lt` indexed by real time and the assumptions
stated in real time (`RealNUC`, `RealPositive`): the weights of `Survival.IPCW` built from the
covariate at the support points identify the hazard and the survival of `U - S` at every
support point `s`. -/
theorem weighted_adjTime_real [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {p : FiniteDist Ω} {B : Ω → ℝ} {ψ : ℝ} (hmodel : M.ModelOn univ B ψ) {V : Ω → 𝓥}
    {Lt : ℝ → Ω → 𝓛} {s : ℝ} (hs : s ∈ timeSupport (M.adjTime B ψ) (M.adjCensor B ψ))
    (hnuc : RealNUC (M.adjTime B ψ) (M.adjCensor B ψ) p V Lt s)
    (hpos : RealPositive (M.adjTime B ψ) (M.adjCensor B ψ) p V Lt s)
    (hk : 0 < wmass p (univ.filter fun ω => s ≤ M.U ω - M.S ω)) :
    weightedHazard p (M.clockAdj B ψ) (M.clockCens B ψ)
        (ipcWeight p (M.clockAdj B ψ) (M.clockCens B ψ) V
          (clockCov (M.adjTime B ψ) (M.adjCensor B ψ) Lt))
        (rank (M.adjTime B ψ) (M.adjCensor B ψ) s) =
      wmass p (univ.filter fun ω => M.U ω - M.S ω = s) /
        wmass p (univ.filter fun ω => s ≤ M.U ω - M.S ω) ∧
    weightedProductLimit p (M.clockAdj B ψ) (M.clockCens B ψ)
        (ipcWeight p (M.clockAdj B ψ) (M.clockCens B ψ) V
          (clockCov (M.adjTime B ψ) (M.adjCensor B ψ) Lt))
        (rank (M.adjTime B ψ) (M.adjCensor B ψ) s) =
      wmass p (univ.filter fun ω => s < M.U ω - M.S ω) :=
  M.weighted_adjTime hmodel hs (switchNUC_of_real _ _ hs hnuc) (switchPositive_of_real _ _ hs hpos)
    hk

end TwoStageTrial

end StructuralNested

end CausalInference
