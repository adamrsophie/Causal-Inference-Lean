/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageAssumptions
public import CausalInference.StructuralNested.TwoStageCounterexamples

/-!
# Two-stage estimation: inverse probability of censoring weights in real time

TSD 24 (Section 4.2.3.1) allows inverse probability of censoring weights instead of
recensoring for the two-stage adjusted data. The transformed times `B + exp ψ (T - B)` are real;
this file states the weighting identity for real times on a finite law, so the risk sets are
not indexed by a clock: the weights are evaluated at each patient's own time.

## Main results

* `weightedCdf`: the inverse probability of censoring weighted distribution function of a time
  `A` censored at `D`, with weights `1 / K (A, V)`, where
  `K (t, v) = P(D ≥ t | P, V = v)` (`censorSurv`).
* `weightedCdf_eq`, `weightedSurvival_eq`: under independent censoring given `V`
  (`CensorNUC`, implied by the distributional form `CensorCondIndep`) and positivity of the
  weights (`CensorPositive`), the weighted distribution and survival functions are those of `A`
  without censoring, at every real time.
* `TwoStageTrial.adjustedCensor`: the transformed censoring time; and
  `TwoStageTrial.weightedCdf_adjTime`, `TwoStageTrial.weightedSurvival_adjTime`: under the
  structural model, the weighted distribution and survival functions of the adjusted control
  time after the secondary baseline are those of the untreated time.
* `TwoStageCounterexample.Weighting.Mw`: the discrete weighting example as a two-stage trial in
  real time; its transformed data are the discrete `Ud` and `Dd` (`adjTime_eq`,
  `adjCensor_eq`), the assumptions hold (`censorNUC`, `censorPositive`), and the weighted
  survival at time `2` is the untreated survival `1/2` (`weightedSurvival_two`).

The weights here depend on covariates `V` fixed at the secondary baseline. Weights updated with
covariates measured after the secondary baseline are the discrete-time layer of
`Survival.IPCW`.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

section Generic

variable {Ω 𝓥 : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝓥]

/-- The event `{t ≤ D}` of remaining uncensored at time `t`. -/
noncomputable def uncensoredAt (D : Ω → ℝ) (t : ℝ) : Finset Ω := univ.filter fun ω => t ≤ D ω

/-- **The probability of remaining uncensored at time `t` given `V = v`** within `P`:
`K (t, v) = P(D ≥ t | P, V = v)`. -/
noncomputable def censorSurv (p : FiniteDist Ω) (P : Finset Ω) (V : Ω → 𝓥) (D : Ω → ℝ) (t : ℝ)
    (v : 𝓥) : ℝ :=
  condProb p (P ∩ ev V v) (uncensoredAt D t)

/-- **The inverse probability of censoring weighted distribution function** of the time `A`
censored at `D`, at `t`: every uncensored event (`A ≤ D`) at or before `t` is weighted by
`1 / K (A, V)`, `∑_{ω ∈ P} p ω 1{A ≤ t, A ≤ D} / K (A, V)`. It uses only the observed data:
the observed time `min (A, D)`, the event indicator and `V`. -/
noncomputable def weightedCdf (p : FiniteDist Ω) (P : Finset Ω) (V : Ω → 𝓥) (A D : Ω → ℝ)
    (t : ℝ) : ℝ :=
  wsum p P fun ω => if A ω ≤ t ∧ A ω ≤ D ω then (censorSurv p P V D (A ω) (V ω))⁻¹ else 0

/-- **Independent censoring given `V`**, in mean form: within `P` and every `V = v`, remaining
uncensored at `a` is mean independent of the event `A = a`. -/
def CensorNUC (p : FiniteDist Ω) (P : Finset Ω) (V : Ω → 𝓥) (A D : Ω → ℝ) : Prop :=
  ∀ v a, MeanIndepOn p (P ∩ ev V v) (ev A a) fun ω => if a ≤ D ω then 1 else 0

/-- **Positivity of the censoring weights**: every patient of `P` with positive mass has a
positive probability of remaining uncensored at its own time given its `V`. -/
def CensorPositive (p : FiniteDist Ω) (P : Finset Ω) (V : Ω → 𝓥) (A D : Ω → ℝ) : Prop :=
  ∀ ω ∈ P, 0 < p ω → 0 < censorSurv p P V D (A ω) (V ω)

/-- **Independent censoring in distributional form**: the censoring time `D` is independent of
`A` given `V` within `P`. It implies the mean form `CensorNUC`. -/
def CensorCondIndep (p : FiniteDist Ω) (P : Finset Ω) (V : Ω → 𝓥) (A D : Ω → ℝ) : Prop :=
  p.CondIndepFun D A fun ω => (decide (ω ∈ P), V ω)

/-- The distributional form of independent censoring implies the mean form. -/
theorem CensorCondIndep.censorNUC {p : FiniteDist Ω} {P : Finset Ω} {V : Ω → 𝓥} {A D : Ω → ℝ}
    (h : CensorCondIndep p P V A D) : CensorNUC p P V A D := fun v a => by
  have e : P ∩ ev V v = ev (fun ω => (decide (ω ∈ P), V ω)) (true, v) := by
    ext ω; simp
  rw [e]
  exact meanIndepOn_of_condIndepFun h (fun d => if a ≤ d then 1 else 0) a (true, v)

/-- One cell `P ∩ {V = v} ∩ {A = a}`: the weighted uncensored mass is the mass of the cell. -/
theorem wsum_cell_weight {p : FiniteDist Ω} {P : Finset Ω} {V : Ω → 𝓥} {A D : Ω → ℝ}
    (hnuc : CensorNUC p P V A D) (hpos : CensorPositive p P V A D) (v : 𝓥) (a : ℝ) :
    wsum p (P ∩ ev V v ∩ ev A a)
        (fun ω => if a ≤ D ω then (censorSurv p P V D a v)⁻¹ else 0) =
      wmass p (P ∩ ev V v ∩ ev A a) := by
  set c := P ∩ ev V v ∩ ev A a
  by_cases hc : wmass p c = 0
  · rw [hc]
    refine (wsum_eq_zero_of_wmass_eq_zero (m := p) p.nonneg hc _)
  have hcpos : 0 < wmass p c := (sum_nonneg fun ω _ => p.nonneg ω).lt_of_ne (Ne.symm hc)
  obtain ⟨ω, hω, hp⟩ : ∃ ω ∈ c, 0 < p ω := by
    by_contra h
    push Not at h
    exact hc (le_antisymm (sum_nonpos h) (sum_nonneg fun ω _ => p.nonneg ω))
  have hmem := mem_inter.1 hω
  have hVω : V ω = v := mem_ev.1 (mem_inter.1 hmem.1).2
  have hAω : A ω = a := mem_ev.1 hmem.2
  have hK := hpos ω (mem_inter.1 hmem.1).1 hp
  rw [hVω, hAω] at hK
  have hs : 0 < wmass p (P ∩ ev V v) := hcpos.trans_le (wmass_mono p.nonneg inter_subset_left)
  have hind := hnuc v a
  unfold MeanIndepOn at hind
  have e1 : wsum p c (fun ω => if a ≤ D ω then (censorSurv p P V D a v)⁻¹ else 0) =
      (censorSurv p P V D a v)⁻¹ * wsum p c (fun ω => if a ≤ D ω then 1 else 0) := by
    rw [wsum, wsum, mul_sum]
    exact sum_congr rfl fun ω _ => by split_ifs <;> ring
  have e2 : ∀ s : Finset Ω, wsum p s (fun ω => if a ≤ D ω then 1 else 0) =
      wmass p (s ∩ uncensoredAt D a) := fun s => by
    simp only [wsum, wmass, mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    congr 1
    ext ω; simp [uncensoredAt]
  rw [e1]
  rw [e2, e2] at hind
  rw [e2]
  rw [censorSurv, condProb] at hK ⊢
  have hu : 0 < wmass p (P ∩ ev V v ∩ uncensoredAt D a) := by
    by_contra h; push Not at h
    have := div_nonpos_of_nonpos_of_nonneg h hs.le
    linarith
  field_simp
  linarith

/-- **Inverse probability of censoring weighting recovers the distribution function.** Under
independent censoring given `V` within `P` (`CensorNUC`) and positivity of the weights
(`CensorPositive`), the weighted distribution function of `A` censored at `D` is the
distribution function of `A` without censoring: `weightedCdf t = P(P, A ≤ t)`, for every real
`t`. -/
theorem weightedCdf_eq {p : FiniteDist Ω} {P : Finset Ω} {V : Ω → 𝓥} {A D : Ω → ℝ}
    (hnuc : CensorNUC p P V A D) (hpos : CensorPositive p P V A D) (t : ℝ) :
    weightedCdf p P V A D t = wmass p (P.filter fun ω => A ω ≤ t) := by
  classical
  set key : Ω → 𝓥 × ℝ := fun ω => (V ω, A ω)
  have hfib : ∀ y : 𝓥 × ℝ, P.filter (fun ω => key ω = y) = P ∩ ev V y.1 ∩ ev A y.2 := fun y => by
    ext ω; simp [key, Prod.ext_iff]
  rw [weightedCdf, wsum, wmass, sum_filter,
    ← sum_fiberwise_of_maps_to (g := key) (t := P.image key) fun ω hω => mem_image_of_mem key hω,
    ← sum_fiberwise_of_maps_to (g := key) (t := P.image key) fun ω hω => mem_image_of_mem key hω]
  refine sum_congr rfl fun y _ => ?_
  rw [hfib]
  by_cases ht : y.2 ≤ t
  · have h1 := wsum_cell_weight hnuc hpos y.1 y.2
    rw [wsum, wmass] at h1
    have hl : (∑ i ∈ P ∩ ev V y.1 ∩ ev A y.2, p i *
          (if A i ≤ t ∧ A i ≤ D i then (censorSurv p P V D (A i) (V i))⁻¹ else 0)) =
        ∑ i ∈ P ∩ ev V y.1 ∩ ev A y.2, p i *
          (if y.2 ≤ D i then (censorSurv p P V D y.2 y.1)⁻¹ else 0) :=
      sum_congr rfl fun ω hω => by
        have hmem := mem_inter.1 hω
        rw [mem_ev.1 (mem_inter.1 hmem.1).2, mem_ev.1 hmem.2]
        simp only [ht, true_and]
    have hr : (∑ i ∈ P ∩ ev V y.1 ∩ ev A y.2, if A i ≤ t then p i else 0) =
        ∑ i ∈ P ∩ ev V y.1 ∩ ev A y.2, p i :=
      sum_congr rfl fun ω hω => by rw [mem_ev.1 (mem_inter.1 hω).2]; simp [ht]
    rw [hl, hr, h1]
  · refine sum_congr rfl fun ω hω => ?_
    have hAω : A ω = y.2 := mem_ev.1 (mem_inter.1 hω).2
    simp [hAω, ht]

/-- **The weighted survival function**: the mass of `P` minus the weighted distribution
function is the survival function of `A` without censoring, `P(P, A > t)`. -/
theorem weightedSurvival_eq {p : FiniteDist Ω} {P : Finset Ω} {V : Ω → 𝓥} {A D : Ω → ℝ}
    (hnuc : CensorNUC p P V A D) (hpos : CensorPositive p P V A D) (t : ℝ) :
    wmass p P - weightedCdf p P V A D t = wmass p (P.filter fun ω => t < A ω) := by
  rw [weightedCdf_eq hnuc hpos, wmass, wmass, wmass,
    ← sum_filter_add_sum_filter_not P fun ω => A ω ≤ t]
  simp only [not_le]
  ring

/-- Mean independence holds trivially when the event `t` contains all of `s` or none of it. -/
theorem meanIndepOn_of_inter {p : FiniteDist Ω} {s t : Finset Ω} (f : Ω → ℝ)
    (h : s ∩ t = s ∨ s ∩ t = ∅) : MeanIndepOn p s t f := by
  rcases h with h | h
  · rw [MeanIndepOn, h]
  · simp [MeanIndepOn, h, wsum, wmass]

end Generic

namespace TwoStageTrial

variable {Ω 𝓥 : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝓥]

/-- **The transformed censoring time**: Equation (1) applied to the administrative censoring
time, `B + exp ψ (C - B)` for adjusted switchers and `C` for the others (TSD 24,
Section 4.2.3.1). -/
noncomputable def adjustedCensor (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) : ℝ :=
  if M.X ω then B ω + Real.exp ψ * (M.C ω - B ω) else M.C ω

/-- The transformed time after the secondary baseline, `adjusted B ψ - S`. -/
noncomputable def adjTime (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) : ℝ := M.adjusted B ψ ω - M.S ω

/-- The transformed censoring time after the secondary baseline, `adjustedCensor B ψ - S`. -/
noncomputable def adjCensor (B : Ω → ℝ) (ψ : ℝ) (ω : Ω) : ℝ := M.adjustedCensor B ψ ω - M.S ω

/-- **Inverse probability of censoring weights for the two-stage adjusted control time.**
Under the structural model on `P` at `ψ`, independent censoring of the transformed time by the
transformed censoring time given `V` within `P`, and positivity of the weights, the weighted
distribution function of the adjusted time after the secondary baseline is the distribution
function of the untreated time after the secondary baseline: for every real `t`,
`weightedCdf t = P(P, U - S ≤ t)`. -/
theorem weightedCdf_adjTime {p : FiniteDist Ω} {P : Finset Ω} {V : Ω → 𝓥} {B : Ω → ℝ}
    {ψ : ℝ} (hmodel : M.ModelOn P B ψ)
    (hnuc : CensorNUC p P V (M.adjTime B ψ) (M.adjCensor B ψ))
    (hpos : CensorPositive p P V (M.adjTime B ψ) (M.adjCensor B ψ)) (t : ℝ) :
    weightedCdf p P V (M.adjTime B ψ) (M.adjCensor B ψ) t =
      wmass p (P.filter fun ω => M.U ω - M.S ω ≤ t) := by
  rw [weightedCdf_eq hnuc hpos t]
  congr 1
  exact filter_congr fun ω hω => by rw [adjTime, ← hmodel ω hω]

/-- **The weighted survival of the adjusted control time is the untreated survival**: under
the assumptions of `weightedCdf_adjTime`, `P(P) - weightedCdf t = P(P, U - S > t)`. -/
theorem weightedSurvival_adjTime {p : FiniteDist Ω} {P : Finset Ω} {V : Ω → 𝓥} {B : Ω → ℝ}
    {ψ : ℝ} (hmodel : M.ModelOn P B ψ)
    (hnuc : CensorNUC p P V (M.adjTime B ψ) (M.adjCensor B ψ))
    (hpos : CensorPositive p P V (M.adjTime B ψ) (M.adjCensor B ψ)) (t : ℝ) :
    wmass p P - weightedCdf p P V (M.adjTime B ψ) (M.adjCensor B ψ) t =
      wmass p (P.filter fun ω => t < M.U ω - M.S ω) := by
  rw [weightedSurvival_eq hnuc hpos t]
  congr 1
  exact filter_congr fun ω hω => by rw [adjTime, ← hmodel ω hω]

end TwoStageTrial

namespace TwoStageCounterexample

namespace Weighting

/-- **The weighting example as a two-stage trial in real time.** Switching at the secondary
baseline (time `0`) halves the time ratio, `exp ψ = 1/2`: a switcher survives `2 Ud`; the
administrative censoring time is `4` or `2` according to `c`. -/
noncomputable def Mw : TwoStageTrial Ω where
  R _ := false
  S _ := 0
  X ω := ω.2.1
  W _ := 0
  T ω := if ω.2.1 then 2 * (Ud ω : ℝ) else Ud ω
  C ω := if ω.2.2 then 4 else 2
  U ω := Ud ω

/-- The true parameter, `exp ψw = 1/2`. -/
noncomputable def ψw : ℝ := Real.log (1 / 2)

/-- The true time ratio is `1/2`. -/
theorem exp_ψw : Real.exp ψw = 1 / 2 := Real.exp_log (by norm_num)

/-- The structural model holds at `ψw`. -/
theorem model : Mw.ModelOn univ Mw.S ψw := by
  rintro ⟨l, x, c⟩ _
  cases x
  · rw [Mw.adjusted_of_not_switch _ _ rfl]; simp [Mw]
  · rw [Mw.adjusted_of_switch _ _ rfl, exp_ψw]; simp [Mw]

/-- **The transformed data of the trial are those of the discrete example**: the adjusted time
after the secondary baseline is `Ud` and the transformed censoring time is `Dd`. -/
theorem adjTime_eq : Mw.adjTime Mw.S ψw = fun ω => (Ud ω : ℝ) := by
  funext ω
  rw [TwoStageTrial.adjTime, ← model ω (mem_univ _)]
  simp [Mw]

/-- The transformed censoring time after the secondary baseline is `Dd`. -/
theorem adjCensor_eq : Mw.adjCensor Mw.S ψw = fun ω => (Dd ω : ℝ) := by
  funext ω
  rcases ω with ⟨l, x, c⟩
  cases x <;> cases c <;>
    simp [TwoStageTrial.adjCensor, TwoStageTrial.adjustedCensor, Mw, Dd, exp_ψw]
  norm_num

/-- Independent censoring given `l`: the adjusted time is constant given `l`. -/
theorem censorNUC : CensorNUC p univ V (Mw.adjTime Mw.S ψw) (Mw.adjCensor Mw.S ψw) := by
  intro v a
  refine meanIndepOn_of_inter _ ?_
  rw [adjTime_eq]
  by_cases h : (Ud (v, true, true) : ℝ) = a
  · left
    exact inter_eq_left.2 fun ω hω => by
      have hV : ω.1 = v := mem_ev.1 (mem_inter.1 hω).2
      rw [mem_ev, ← h]; simp [Ud, hV]
  · right
    ext ω
    simp only [mem_inter, mem_ev, Finset.notMem_empty, iff_false, not_and]
    intro hω hA
    have hV : ω.1 = v := hω.2
    refine h ?_
    rw [← hA]; simp [Ud, hV]

/-- Positivity of the weights: a non-switcher with long follow-up remains uncensored past its
untreated time. -/
theorem censorPositive : CensorPositive p univ V (Mw.adjTime Mw.S ψw) (Mw.adjCensor Mw.S ψw) := by
  intro ω _ _
  have hmem : (ω.1, false, true) ∈ univ ∩ ev V (V ω) ∩
      uncensoredAt (Mw.adjCensor Mw.S ψw) (Mw.adjTime Mw.S ψw ω) := by
    rw [adjTime_eq, adjCensor_eq]
    simp only [mem_inter, mem_univ, mem_ev, true_and, uncensoredAt, mem_filter]
    refine ⟨rfl, ?_⟩
    rcases ω with ⟨l, x, c⟩; cases l <;> norm_num [Ud, Dd]
  have hp : 0 < p (ω.1, false, true) := by
    rcases ω with ⟨l, x, c⟩; cases l <;> norm_num [p]
  have h1 := wmass_pos_of_mem p.nonneg hmem hp
  exact div_pos h1 (h1.trans_le (wmass_mono p.nonneg inter_subset_left))

/-- **The weighted survival at time `2` is the untreated survival `1/2`**, by
`TwoStageTrial.weightedSurvival_adjTime`; the discrete example (`weighted`) gives the hazard
`1/2` at time `2` on the same transformed data. -/
theorem weightedSurvival_two :
    wmass p univ - weightedCdf p univ V (Mw.adjTime Mw.S ψw) (Mw.adjCensor Mw.S ψw) 2 = 1 / 2 := by
  rw [Mw.weightedSurvival_adjTime model censorNUC censorPositive, wmass, sum_filter]
  simp [Fintype.sum_prod_type, p, Mw, Ud]
  norm_num

end Weighting

end TwoStageCounterexample

end StructuralNested

end CausalInference
