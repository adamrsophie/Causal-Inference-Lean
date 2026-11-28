/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageClock

/-!
# The rank clock with a covariate that moves between support points

`CausalInference.StructuralNested.TwoStageClock` transports a `TwoStageTrial` to the clock of
the ranks of its support points. The weights read the real-time covariate process `Lt` only at
the support points, and the real-time assumption `RealNUC` conditions on the history at the
support points (`realHist`). Here the assumption is compared with the one that conditions on the
whole covariate path up to the current time.

## Main definitions

* `contHist`, `contRiskCell`: the covariate history of `ω` at every real time up to `s`, and
  the risk cell built from it.
* `ContNUC`, `ContPositive`: sequential no unmeasured confounding and positivity given the
  continuous history.

## Main results

* `contHist_subset_realHist`: the continuous history is finer than the history at the support
  points.
* `contHist_eq_realHist`, `contNUC_iff_realNUC`, `contPositive_iff_realPositive`: when the
  value of the covariate at every time is determined by its values at the support points up to
  that time (`DeterminedBySupport`, which holds for instance when the covariate changes only at
  support points), the two histories coincide and so do the assumptions; then
  `TwoStageTrial.weighted_adjTime_real` applies under the continuous assumptions
  (`TwoStageTrial.weighted_adjTime_cont`).
* `ClockCounterexample`: without that condition the two assumptions differ and the weights of
  the rank clock are biased. Four equally likely patients `(h, c)`, nobody switches, secondary
  baseline `0`; event time `2` for `h = true` and `3` otherwise; censoring at time `1` for
  `h = c = true` and at `3` otherwise. The covariate is `h` before time `1` and `false` from
  time `1` on, so it is constant at the support points `1, 2, 3`. The continuous assumptions
  hold (`contNUC`, `contPositive`), the support point assumption fails (`not_realNUC`), every
  weight at time `2` is `4/3` (`ipcWeight_eq`), the weighted hazard at time `2` is `1/3` against
  the hazard `1/2` of the untreated time, and the weighted product limit is `2/3` against the
  survival `1/2` (`biased`).

So the weights of `TwoStageTrial.weighted_adjTime_real` are valid under the continuous history
assumption only after the covariate process has been made constant between support points; a
covariate measured between two support points that drives censoring breaks them.
-/

@[expose] public section

open Finset CausalInference.Longitudinal CausalInference.Survival CausalInference.Survival.IPCW

namespace CausalInference

namespace StructuralNested

section Continuous

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝓥 𝓛 : Type*} [DecidableEq 𝓥]
  [DecidableEq 𝓛] (A D : Ω → ℝ)

open Classical in
/-- The continuous covariate history of `ω` up to `s`: the individuals whose covariate agrees
with that of `ω` at every real time `u ≤ s`. -/
noncomputable def contHist (Lt : ℝ → Ω → 𝓛) (s : ℝ) (ω : Ω) : Finset Ω :=
  univ.filter fun ω' => ∀ u ≤ s, Lt u ω' = Lt u ω

/-- The risk cell of `ω` at `s` given the continuous history: uncensored through `s`, alive
after `s`, with the baseline covariates and the continuous covariate history of `ω`. -/
noncomputable def contRiskCell (V : Ω → 𝓥) (Lt : ℝ → Ω → 𝓛) (s : ℝ) (ω : Ω) : Finset Ω :=
  univ.filter (fun ω' => s ≤ D ω' ∧ s < A ω' ∧ V ω' = V ω) ∩ contHist Lt s ω

/-- **Sequential no unmeasured confounding given the continuous history** up to `s₀`: as
`RealNUC`, with the risk cell built from the covariate at every real time up to `s`. -/
def ContNUC (m : Ω → ℝ) (V : Ω → 𝓥) (Lt : ℝ → Ω → 𝓛) (s₀ : ℝ) : Prop :=
  ∀ s ∈ timeSupport A D, s < s₀ → ∀ (ω : Ω) (u : ℝ),
    MeanIndepOn m (contRiskCell A D V Lt s ω) (univ.filter fun ω' => A ω' = u)
      (fun ω' => if s < D ω' then 1 else 0)

/-- **Positivity given the continuous history** up to `s₀`: as `RealPositive`, with the risk
cell built from the covariate at every real time up to `s`. -/
def ContPositive (m : Ω → ℝ) (V : Ω → 𝓥) (Lt : ℝ → Ω → 𝓛) (s₀ : ℝ) : Prop :=
  ∀ s ∈ timeSupport A D, s < s₀ → ∀ ω, 0 < m ω → s ≤ D ω → s < A ω →
    0 < condProb m (contRiskCell A D V Lt s ω) (univ.filter fun ω' => s < D ω')

omit [DecidableEq Ω] in
/-- The continuous history is finer than the history at the support points. -/
theorem contHist_subset_realHist (Lt : ℝ → Ω → 𝓛) (s : ℝ) (ω : Ω) :
    contHist Lt s ω ⊆ realHist A D Lt s ω := fun ω' h => by
  simp only [contHist, realHist, mem_filter, mem_univ, true_and] at h ⊢
  exact fun u _ hu => h u hu

/-- The covariate at every time is determined by its values at the support points up to that
time: two individuals that agree at the support points up to `u` agree at `u`. This holds when
the covariate changes only at support points. -/
def DeterminedBySupport (Lt : ℝ → Ω → 𝓛) : Prop :=
  ∀ (u : ℝ) (ω ω' : Ω), (∀ v ∈ timeSupport A D, v ≤ u → Lt v ω' = Lt v ω) → Lt u ω' = Lt u ω

omit [DecidableEq Ω] in
/-- **The two histories coincide** when the covariate is determined by its values at the
support points. -/
theorem contHist_eq_realHist {Lt : ℝ → Ω → 𝓛} (h : DeterminedBySupport A D Lt) (s : ℝ)
    (ω : Ω) : contHist Lt s ω = realHist A D Lt s ω := by
  refine (contHist_subset_realHist A D Lt s ω).antisymm fun ω' hω' => ?_
  simp only [contHist, realHist, mem_filter, mem_univ, true_and] at hω' ⊢
  exact fun u hu => h u ω ω' fun v hv hvu => hω' v hv (hvu.trans hu)

theorem contRiskCell_eq_realRiskCell {Lt : ℝ → Ω → 𝓛} (h : DeterminedBySupport A D Lt)
    (V : Ω → 𝓥) (s : ℝ) (ω : Ω) : contRiskCell A D V Lt s ω = realRiskCell A D V Lt s ω := by
  rw [contRiskCell, realRiskCell, contHist_eq_realHist A D h]

/-- When the covariate is determined by its values at the support points, the continuous no
unmeasured confounding assumption is the one at the support points. -/
theorem contNUC_iff_realNUC {Lt : ℝ → Ω → 𝓛} (h : DeterminedBySupport A D Lt) (m : Ω → ℝ)
    (V : Ω → 𝓥) (s₀ : ℝ) : ContNUC A D m V Lt s₀ ↔ RealNUC A D m V Lt s₀ := by
  simp only [ContNUC, RealNUC, contRiskCell_eq_realRiskCell A D h]

/-- When the covariate is determined by its values at the support points, continuous
positivity is positivity at the support points. -/
theorem contPositive_iff_realPositive {Lt : ℝ → Ω → 𝓛} (h : DeterminedBySupport A D Lt)
    (m : Ω → ℝ) (V : Ω → 𝓥) (s₀ : ℝ) :
    ContPositive A D m V Lt s₀ ↔ RealPositive A D m V Lt s₀ := by
  simp only [ContPositive, RealPositive, contRiskCell_eq_realRiskCell A D h]

end Continuous

namespace TwoStageTrial

variable {Ω 𝓥 𝓛 : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝓥]
  [DecidableEq 𝓛]

/-- **Weighting under the continuous history assumption.** If the covariate process is
determined by its values at the support points of the adjusted and transformed censoring times,
the continuous assumptions give the conclusion of `weighted_adjTime_real`. -/
theorem weighted_adjTime_cont [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    {p : FiniteDist Ω} {B : Ω → ℝ} {ψ : ℝ} (hmodel : M.ModelOn univ B ψ) {V : Ω → 𝓥}
    {Lt : ℝ → Ω → 𝓛} (hdet : DeterminedBySupport (M.adjTime B ψ) (M.adjCensor B ψ) Lt)
    {s : ℝ} (hs : s ∈ timeSupport (M.adjTime B ψ) (M.adjCensor B ψ))
    (hnuc : ContNUC (M.adjTime B ψ) (M.adjCensor B ψ) p V Lt s)
    (hpos : ContPositive (M.adjTime B ψ) (M.adjCensor B ψ) p V Lt s)
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
  M.weighted_adjTime_real hmodel hs ((contNUC_iff_realNUC _ _ hdet _ _ _).1 hnuc)
    ((contPositive_iff_realPositive _ _ hdet _ _ _).1 hpos) hk

end TwoStageTrial

/-! ### The countermodel -/

namespace ClockCounterexample

/-- A patient `(h, c)`: the prognosis `h` (`true` for poor) and the censoring coin `c`. -/
abbrev Ω := Bool × Bool

/-- The four patients are equally likely. -/
noncomputable def p : FiniteDist Ω := FiniteDist.uniform

theorem p_apply (ω : Ω) : p ω = 1 / 4 := by
  simp [p, FiniteDist.uniform_apply]

/-- The event time: `2` for poor prognosis, `3` otherwise. -/
noncomputable def A (ω : Ω) : ℝ := if ω.1 then 2 else 3

/-- The censoring time: `1` for poor prognosis with `c = true`, `3` otherwise. -/
noncomputable def D (ω : Ω) : ℝ := if ω.1 && ω.2 then 1 else 3

/-- The covariate process: the prognosis before time `1`, `false` from time `1` on. -/
noncomputable def Lt (u : ℝ) (ω : Ω) : Bool := if u < 1 then ω.1 else false

/-- No baseline covariate. -/
def V (_ : Ω) : Unit := ()

/-- The trial: nobody switches, the secondary baseline is `0`, the observed time is `A`, the
censoring time is `D`, and the untreated time is `A`. -/
noncomputable def M : TwoStageTrial Ω where
  R _ := true
  S _ := 0
  X _ := false
  W _ := 0
  T := A
  C := D
  U := A

theorem adjTime_eq (B : Ω → ℝ) (ψ : ℝ) : M.adjTime B ψ = A := funext fun ω => by
  rw [TwoStageTrial.adjTime, M.adjusted_of_not_switch B ψ rfl]
  simp [M]

theorem adjCensor_eq (B : Ω → ℝ) (ψ : ℝ) : M.adjCensor B ψ = D := funext fun ω => by
  simp [TwoStageTrial.adjCensor, TwoStageTrial.adjustedCensor, M]

theorem model (B : Ω → ℝ) (ψ : ℝ) : M.ModelOn univ B ψ := fun ω _ => by
  rw [M.adjusted_of_not_switch B ψ rfl]
  rfl

theorem sum_four (f : Ω → ℝ) :
    ∑ ω, f ω = f (true, true) + f (true, false) + f (false, true) + f (false, false) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

theorem wmass_filter (P : Ω → Prop) [DecidablePred P] :
    wmass p (univ.filter P) = ∑ ω, if P ω then p ω else 0 := by
  rw [wmass, sum_filter]

theorem wsum_filter (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    wsum p (univ.filter P) f = ∑ ω, if P ω then p ω * f ω else 0 := by
  rw [wsum, sum_filter]

theorem mem_support {y : ℝ} : y ∈ timeSupport A D ↔ y = 1 ∨ y = 2 ∨ y = 3 := by
  simp only [timeSupport, mem_union, mem_image, mem_univ, true_and, Prod.exists,
    Bool.exists_bool, A, D]
  norm_num
  constructor
  · rintro ((h | h) | h | h | h) <;> simp_all
  · rintro (h | h | h) <;> simp_all

theorem one_mem : (1 : ℝ) ∈ timeSupport A D := mem_support.2 (Or.inl rfl)

theorem two_mem : (2 : ℝ) ∈ timeSupport A D := mem_support.2 (Or.inr (Or.inl rfl))

theorem one_le_of_mem {y : ℝ} (hy : y ∈ timeSupport A D) : 1 ≤ y := by
  rcases mem_support.1 hy with rfl | rfl | rfl <;> norm_num

theorem rank_one : rank A D 1 = 0 := by
  rw [rank, card_eq_zero, filter_eq_empty_iff]
  exact fun y hy => not_lt.2 (one_le_of_mem hy)

theorem rank_two : rank A D 2 = 1 := by
  rw [rank, card_eq_one]
  refine ⟨1, ?_⟩
  ext y
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hy, h2⟩
    rcases mem_support.1 hy with rfl | rfl | rfl
    · rfl
    · norm_num at h2
    · norm_num at h2
  · rintro rfl
    exact ⟨one_mem, by norm_num⟩

/-- The covariate is `false` at every support point, so the history at the support points
carries no information. -/
theorem realHist_eq_univ (s : ℝ) (ω : Ω) : realHist A D Lt s ω = univ := by
  ext ω'
  simp only [realHist, mem_filter, mem_univ, true_and, iff_true]
  intro u hu _
  simp [Lt, not_lt.2 (one_le_of_mem hu)]

/-- The continuous history up to time `1` reveals the prognosis. -/
theorem contHist_one (ω : Ω) : contHist Lt 1 ω = univ.filter fun ω' => ω'.1 = ω.1 := by
  ext ω'
  simp only [contHist, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    simpa [Lt] using h 0 (by norm_num)
  · intro h u _
    simp [Lt, h]

/-! #### The continuous assumptions hold -/

/-- **No unmeasured confounding given the continuous history.** Given the prognosis the event
time is fixed, so it is independent of censoring. -/
theorem contNUC : ContNUC A D p V Lt 2 := by
  intro s hs hs2 ω u
  have hs1 : s = 1 := by
    rcases mem_support.1 hs with rfl | rfl | rfl
    · rfl
    all_goals norm_num at hs2
  subst hs1
  set cell := contRiskCell A D V Lt 1 ω
  have hA : ∀ ω' ∈ cell, A ω' = A ω := fun ω' h => by
    simp only [cell, contRiskCell, contHist_one, mem_inter, mem_filter, mem_univ,
      true_and] at h
    simp [A, h.2]
  by_cases hu : A ω = u
  · have hi : cell ∩ (univ.filter fun ω' => A ω' = u) = cell :=
      inter_eq_left.2 fun ω' h => by simp [hA ω' h, hu]
    rw [MeanIndepOn, hi]
  · have hi : cell ∩ (univ.filter fun ω' => A ω' = u) = ∅ := by
      ext ω'
      simp only [mem_inter, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
      exact fun h h' => hu (by rw [← hA ω' h, h'])
    rw [MeanIndepOn, hi]
    simp [wsum, wmass]

/-- **Positivity given the continuous history.** Every prognosis has a patient censored at
time `3`. -/
theorem contPositive : ContPositive A D p V Lt 2 := by
  intro s hs hs2 ω _ _ _
  have hs1 : s = 1 := by
    rcases mem_support.1 hs with rfl | rfl | rfl
    · rfl
    all_goals norm_num at hs2
  subst hs1
  have hmem : (ω.1, false) ∈ contRiskCell A D V Lt 1 ω ∩ univ.filter fun ω' => 1 < D ω' := by
    simp only [contRiskCell, contHist_one, mem_inter, mem_filter, mem_univ, true_and, A, D, V]
    cases ω.1 <;> norm_num
  have hpos : ∀ ω', 0 < p ω' := fun ω' => by rw [p_apply]; norm_num
  have hn : ∀ ω', 0 ≤ p ω' := fun ω' => (hpos ω').le
  exact div_pos (wmass_pos_of_mem hn hmem (hpos _))
    (wmass_pos_of_mem hn (mem_inter.1 hmem).1 (hpos _))

/-! #### The support point assumption fails and the weights are biased -/

/-- The risk cell at time `1` given the history at the support points is everybody. -/
theorem realRiskCell_one (ω : Ω) : realRiskCell A D V Lt 1 ω = univ := by
  rw [realRiskCell, realHist_eq_univ, inter_univ, filter_true_of_mem]
  intro ω' _
  simp only [A, D, V, and_true]
  constructor
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

/-- **The support point assumption fails at time `1`**: without the prognosis, remaining
uncensored after time `1` has probability `3/4` overall but `1/2` among the patients with the
event at time `2`. -/
theorem not_realNUC : ¬ RealNUC A D p V Lt 2 := by
  intro h
  have := h 1 one_mem (by norm_num) (true, true) 2
  rw [MeanIndepOn, realRiskCell_one, univ_inter, wsum_filter, wmass_filter] at this
  simp only [wsum, wmass, sum_four, A, D, p_apply] at this
  norm_num at this

theorem stayProb_zero (ω : Ω) :
    stayProb p (clockTime A D) (clockCensor A D) V (clockCov A D Lt) 0 ω = 3 / 4 := by
  rw [stayProb, ← rank_one, riskCell_clock A D V Lt one_mem, uncensored_clock A D one_mem,
    realRiskCell_one, condProb, univ_inter, wmass_filter, wmass, sum_four, sum_four]
  simp only [D, p_apply]
  norm_num

/-- **Every weight at time `2` is `4/3`**: the censoring probability `1/4` after time `1` is
spread over everybody. -/
theorem ipcWeight_eq (ω : Ω) :
    ipcWeight p (clockTime A D) (clockCensor A D) V (clockCov A D Lt) (rank A D 2) ω = 4 / 3 := by
  rw [ipcWeight, rank_two, range_one, prod_singleton, stayProb_zero]
  norm_num

theorem eventSet_two : eventSet (clockTime A D) (clockCensor A D) (rank A D 2) =
    univ.filter fun ω => A ω = 2 ∧ 2 ≤ D ω := by
  ext ω; rw [mem_eventSet_iff A D two_mem]; simp

theorem riskSet_two : riskSet (clockTime A D) (clockCensor A D) (rank A D 2) =
    univ.filter fun ω => 2 ≤ A ω ∧ 2 ≤ D ω := by
  ext ω; rw [mem_riskSet_iff A D]; simp

theorem weightedHazard_two :
    weightedHazard p (clockTime A D) (clockCensor A D)
      (ipcWeight p (clockTime A D) (clockCensor A D) V (clockCov A D Lt)) (rank A D 2) =
      1 / 3 := by
  rw [weightedHazard, eventSet_two, riskSet_two, wsum_filter, wsum_filter, sum_four, sum_four]
  simp only [ipcWeight_eq, A, D, p_apply]
  norm_num

theorem weightedHazard_zero :
    weightedHazard p (clockTime A D) (clockCensor A D)
      (ipcWeight p (clockTime A D) (clockCensor A D) V (clockCov A D Lt)) 0 = 0 := by
  have he : eventSet (clockTime A D) (clockCensor A D) 0 = ∅ := by
    rw [← rank_one]
    ext ω
    rw [mem_eventSet_iff A D one_mem]
    simp only [notMem_empty, iff_false, not_and, A]
    split_ifs <;> norm_num
  rw [weightedHazard, he]
  simp [wsum]

/-- **The weights of the rank clock are biased.** At time `2` the weighted hazard is `1/3`,
the hazard of the untreated time `U - S` is `1/2`; the weighted product limit is `2/3`, the
survival `P(U - S > 2)` is `1/2`. -/
theorem biased (B : Ω → ℝ) (ψ : ℝ) :
    weightedHazard p (M.clockAdj B ψ) (M.clockCens B ψ)
        (ipcWeight p (M.clockAdj B ψ) (M.clockCens B ψ) V
          (clockCov (M.adjTime B ψ) (M.adjCensor B ψ) Lt))
        (rank (M.adjTime B ψ) (M.adjCensor B ψ) 2) = 1 / 3 ∧
    wmass p (univ.filter fun ω => M.U ω - M.S ω = 2) /
        wmass p (univ.filter fun ω => 2 ≤ M.U ω - M.S ω) = 1 / 2 ∧
    weightedProductLimit p (M.clockAdj B ψ) (M.clockCens B ψ)
        (ipcWeight p (M.clockAdj B ψ) (M.clockCens B ψ) V
          (clockCov (M.adjTime B ψ) (M.adjCensor B ψ) Lt))
        (rank (M.adjTime B ψ) (M.adjCensor B ψ) 2) = 2 / 3 ∧
    wmass p (univ.filter fun ω => 2 < M.U ω - M.S ω) = 1 / 2 := by
  simp only [TwoStageTrial.clockAdj, TwoStageTrial.clockCens, adjTime_eq, adjCensor_eq]
  refine ⟨weightedHazard_two, ?_, ?_, ?_⟩
  · rw [wmass_filter, wmass_filter, sum_four, sum_four]
    simp only [M, A, p_apply]
    norm_num
  · have h1 := weightedHazard_two
    rw [rank_two] at h1
    rw [weightedProductLimit, rank_two, prod_range_succ, prod_range_one, weightedHazard_zero, h1]
    norm_num
  · rw [wmass_filter, sum_four]
    simp only [M, A, p_apply]
    norm_num

/-- **Summary of the countermodel.** The structural model holds, the continuous assumptions
hold, the support point assumption fails, and the weighted hazard at time `2` differs from the
hazard of the untreated time. -/
theorem summary (B : Ω → ℝ) (ψ : ℝ) :
    M.ModelOn univ B ψ ∧ ContNUC (M.adjTime B ψ) (M.adjCensor B ψ) p V Lt 2 ∧
      ContPositive (M.adjTime B ψ) (M.adjCensor B ψ) p V Lt 2 ∧
      ¬ RealNUC (M.adjTime B ψ) (M.adjCensor B ψ) p V Lt 2 ∧
      weightedHazard p (M.clockAdj B ψ) (M.clockCens B ψ)
          (ipcWeight p (M.clockAdj B ψ) (M.clockCens B ψ) V
            (clockCov (M.adjTime B ψ) (M.adjCensor B ψ) Lt))
          (rank (M.adjTime B ψ) (M.adjCensor B ψ) 2) ≠
        wmass p (univ.filter fun ω => M.U ω - M.S ω = 2) /
          wmass p (univ.filter fun ω => 2 ≤ M.U ω - M.S ω) := by
  obtain ⟨h1, h2, -, -⟩ := biased B ψ
  refine ⟨model B ψ, ?_, ?_, ?_, ?_⟩
  · rw [adjTime_eq, adjCensor_eq]; exact contNUC
  · rw [adjTime_eq, adjCensor_eq]; exact contPositive
  · rw [adjTime_eq, adjCensor_eq]; exact not_realNUC
  · rw [h1, h2]
    norm_num

end ClockCounterexample

end StructuralNested

end CausalInference
