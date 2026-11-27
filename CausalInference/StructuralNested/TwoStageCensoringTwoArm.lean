/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStageCensoring
public import CausalInference.StructuralNested.TwoStageTwoArm

/-!
# Two-stage estimation: the weighting countermodel as a two-arm trial

The control arm of the randomized trial `TwoStageCounterexample.Weighting.Z` is the real-time
weighting example `Mw` of `TwoStageCensoring`, with its censoring time `C` (`4` or `2`); the
experimental arm survives `4`. The analysis compares the survival of the arms at time `2`.

## Main results

* `censorNUC₂`, `censorPositive₂`: independent censoring of the adjusted time by the
  transformed censoring time given `l`, and positivity of the weights, on the two-arm law.
* `naive₂`: censoring the adjusted control time at the transformed censoring time and taking
  the product limit gives the control survival `7/12`; `recensored₂`: recensoring at
  `min (C - S, exp ψ (C - S))` gives `1/2`; `weighted₂`: inverse probability of censoring
  weights given `l` give `1/2` (by `TwoStageTrial.weightedSurvival_adjTime`); `truth₂`: the
  untreated control survival is `1/2`.
* `contrasts₂`: the survival contrasts at time `2` are `5/12` (naive), `1/2` (recensored),
  `1/2` (weighted), against the true hypothetical contrast `1/2`
  (`experimental₂`, `experimental_q`: the experimental survival on the two-arm law is `1`,
  observed since every censoring time is at least `2`; both arms use the clock from
  randomization, as `S = 0`).
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

namespace TwoStageCounterexample

namespace Weighting

open TwoArm

/-- **The two-arm trial**: the experimental arm survives `4` with no adjusted switch, the
control arm is `Mw`, the arm is a fair coin. Every patient has the censoring time `C` of
`Mw` (`4` or `2`). -/
noncomputable abbrev Z : TwoStageTrial (Bool × Ω) := trial Mw T1

/-- The two-arm law. -/
noncomputable abbrev q : FiniteDist (Bool × Ω) := law p

/-- The control arm. -/
abbrev Ctl : Finset (Bool × Ω) := control univ

/-- The baseline covariate `l` of the weight model. -/
def V₂ (z : Bool × Ω) : Bool := z.2.1

/-- The parameter applied from the secondary baseline. -/
noncomputable abbrev B₂ : Bool × Ω → ℝ := fun z => Mw.S z.2

theorem q_apply (z : Bool × Ω) : q z = p z.2 / 2 := rfl

theorem mem_Ctl (z : Bool × Ω) : z ∈ Ctl ↔ z.1 = false := by simp [TwoArm.control]

/-- A mass in the control arm as a sum over the patients. -/
theorem wmass_ctl_filter (P : Bool × Ω → Prop) [DecidablePred P] :
    wmass q (Ctl.filter P) = ∑ ω, if P (false, ω) then p ω / 2 else 0 := by
  rw [wmass_law p (s := univ.filter fun ω => P (false, ω)) (r := false) fun z => by
    obtain ⟨b, ω⟩ := z; cases b <;> simp [TwoArm.control], wmass, sum_filter, sum_div]
  exact sum_congr rfl fun _ _ => by split_ifs <;> simp

/-- In the control arm the transformed data are those of `Mw`. -/
theorem adjTime_ctl (ω : Ω) : Z.adjTime B₂ ψw (false, ω) = Ud ω := by
  have := congrFun adjTime_eq ω
  exact this

theorem adjCensor_ctl (ω : Ω) : Z.adjCensor B₂ ψw (false, ω) = Dd ω := by
  have := congrFun adjCensor_eq ω
  exact this

/-- The structural model holds in the control arm. -/
theorem model₂ : Z.ModelOn Ctl B₂ ψw := by
  rintro ⟨b, ω⟩ hz
  have hb : b = false := (mem_Ctl _).1 hz
  subst hb
  exact model ω (mem_univ ω)

/-- **Independent censoring given `l` on the two-arm law**, re-proved: in the control arm the
adjusted time is a function of `l`. -/
theorem censorNUC₂ : CensorNUC q Ctl V₂ (Z.adjTime B₂ ψw) (Z.adjCensor B₂ ψw) := by
  intro v a
  refine meanIndepOn_of_inter _ ?_
  by_cases h : (Ud (v, true, true) : ℝ) = a
  · left
    refine inter_eq_left.2 fun z hz => ?_
    obtain ⟨hc, hV⟩ := mem_inter.1 hz
    obtain ⟨b, ω⟩ := z
    have hb : b = false := (mem_Ctl _).1 hc
    subst hb
    have hV' : ω.1 = v := (mem_ev (X := V₂)).1 hV
    refine mem_ev.2 ?_
    rw [adjTime_ctl, ← h]; simp [Ud, hV']
  · right
    ext ⟨b, ω⟩
    simp only [mem_inter, mem_ev, Finset.notMem_empty, iff_false, not_and]
    intro hcV hA
    obtain ⟨hc, hV⟩ := hcV
    have hb : b = false := (mem_Ctl _).1 hc
    subst hb
    refine h ?_
    rw [← hA, adjTime_ctl]; simp [Ud, show ω.1 = v from hV]

/-- **Positivity of the weights on the two-arm law**, re-proved. -/
theorem censorPositive₂ : CensorPositive q Ctl V₂ (Z.adjTime B₂ ψw) (Z.adjCensor B₂ ψw) := by
  rintro ⟨b, ω⟩ hz _
  have hb : b = false := (mem_Ctl _).1 hz
  subst hb
  have hmem : ((false, (ω.1, false, true)) : Bool × Ω) ∈ Ctl ∩ ev V₂ (V₂ (false, ω)) ∩
      uncensoredAt (Z.adjCensor B₂ ψw) (Z.adjTime B₂ ψw (false, ω)) := by
    refine mem_inter.2 ⟨mem_inter.2 ⟨(mem_Ctl _).2 rfl, mem_ev.2 rfl⟩,
      mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    rw [adjTime_ctl, adjCensor_ctl]
    rcases ω with ⟨l, x, c⟩; cases l <;> norm_num [Ud, Dd]
  have hp : 0 < q (false, (ω.1, false, true)) := by
    rw [q_apply]; rcases ω with ⟨l, x, c⟩; cases l <;> norm_num [p]
  have h1 := wmass_pos_of_mem q.nonneg hmem hp
  exact div_pos h1 (h1.trans_le (wmass_mono q.nonneg inter_subset_left))

/-- The mass of the control arm is `1/2`. -/
theorem wmass_Ctl : wmass q Ctl = 1 / 2 := by
  rw [wmass_law p (s := univ) (r := false) fun z => by simp [TwoArm.control], wmass,
    p.sum_eq_one]

/-- **The weighted control survival at time `2`** is `1/2` of the control arm. -/
theorem weighted₂ :
    (wmass q Ctl - weightedCdf q Ctl V₂ (Z.adjTime B₂ ψw) (Z.adjCensor B₂ ψw) 2) /
      wmass q Ctl = 1 / 2 := by
  rw [Z.weightedSurvival_adjTime model₂ censorNUC₂ censorPositive₂, wmass_Ctl,
    wmass_ctl_filter]
  simp [Fintype.sum_prod_type, Z, TwoArm.trial, Mw, Ud, p]
  norm_num

/-- **The true control survival at time `2`**: `P(U > 2 | R = 0) = 1/2`. -/
theorem truth₂ : wmass q (Ctl.filter fun z => 2 < Z.U z - Z.S z) / wmass q Ctl = 1 / 2 := by
  rw [wmass_Ctl, wmass_ctl_filter]
  simp [Fintype.sum_prod_type, Z, TwoArm.trial, Mw, Ud, p]
  norm_num

/-- No transformed event happens before time `2` in the control arm, so the product limit at
`2` has the single factor at `2`. -/
theorem two_le_adjTime (ω : Ω) : 2 ≤ Z.adjTime B₂ ψw (false, ω) := by
  rw [adjTime_ctl]; unfold Ud; split_ifs <;> norm_num

/-- The product-limit survival at `2` of the control arm censored at `D`, when no event
happens before `2`: `1 - P(A = 2, D ≥ 2) / P(A ≥ 2, D ≥ 2)`. -/
noncomputable def productLimitAtTwo (D : Bool × Ω → ℝ) : ℝ :=
  1 - wmass q (Ctl.filter fun z => Z.adjTime B₂ ψw z = 2 ∧ 2 ≤ D z) /
    wmass q (Ctl.filter fun z => 2 ≤ Z.adjTime B₂ ψw z ∧ 2 ≤ D z)

/-- **Naive censoring at the transformed censoring time** gives the control survival `7/12`. -/
theorem naive₂ : productLimitAtTwo (Z.adjCensor B₂ ψw) = 7 / 12 := by
  rw [productLimitAtTwo, wmass_ctl_filter, wmass_ctl_filter]
  simp [Fintype.sum_prod_type, adjTime_ctl, adjCensor_ctl, Ud, Dd, p]
  norm_num

/-- The recensoring time `min (C - S, exp ψ (C - S))`, the same rule in the whole control arm:
`2` or `1`. -/
noncomputable def recens (z : Bool × Ω) : ℝ :=
  min (Z.C z - Z.S z) (Real.exp ψw * (Z.C z - Z.S z))

theorem recens_eq (ω : Ω) : recens (false, ω) = if ω.2.2 then 2 else 1 := by
  rw [recens, exp_ψw]
  rcases ω with ⟨l, x, c⟩
  cases c <;> norm_num [Z, TwoArm.trial, Mw]

/-- **Recensoring** gives the control survival `1/2`. -/
theorem recensored₂ : productLimitAtTwo recens = 1 / 2 := by
  rw [productLimitAtTwo, wmass_ctl_filter, wmass_ctl_filter]
  simp [Fintype.sum_prod_type, adjTime_ctl, recens_eq, Ud, p]
  norm_num

/-- The experimental arm survives past `2`: `P(T1 > 2) = 1`, observed since every censoring
time is at least `2`. -/
theorem experimental₂ : p.expect (fun ω => if (2 : ℝ) < T1 ω then 1 else 0) = 1 ∧
    ∀ ω, (2 : ℝ) ≤ Mw.C ω := by
  refine ⟨?_, fun ω => ?_⟩
  · norm_num [T1, FiniteDist.expect, p.sum_eq_one]
  · simp only [Mw]; split_ifs <;> norm_num

/-- **The experimental arm on the two-arm law**: its survival past `2` is `1`, and no patient
of the two-arm trial is censored before `2`, so the survival is observed. -/
theorem experimental_q :
    wmass q ((univ.filter fun z : Bool × Ω => z.1 = true).filter fun z => 2 < Z.T z - Z.S z) /
        wmass q (univ.filter fun z : Bool × Ω => z.1 = true) = 1 ∧
      ∀ z, (2 : ℝ) ≤ Z.C z := by
  refine ⟨?_, fun z => experimental₂.2 z.2⟩
  have e : (univ.filter fun z : Bool × Ω => z.1 = true).filter (fun z => 2 < Z.T z - Z.S z) =
      univ.filter fun z : Bool × Ω => z.1 = true := by
    ext ⟨b, ω⟩
    cases b <;> norm_num [Z, TwoArm.trial, T1, Mw]
  rw [e, div_self]
  rw [wmass_law p (s := univ) (r := true) fun z => by simp, wmass, p.sum_eq_one]
  norm_num

/-- **The stage-two survival contrasts at time `2`**, experimental survival `1` minus the
control survival estimate: naive censoring gives `5/12`, recensoring `1/2`, weighting `1/2`,
and the true hypothetical contrast is `1/2`. -/
theorem contrasts₂ :
    1 - productLimitAtTwo (Z.adjCensor B₂ ψw) = 5 / 12 ∧
    1 - productLimitAtTwo recens = 1 / 2 ∧
    1 - (wmass q Ctl - weightedCdf q Ctl V₂ (Z.adjTime B₂ ψw) (Z.adjCensor B₂ ψw) 2) /
      wmass q Ctl = 1 / 2 ∧
    1 - wmass q (Ctl.filter fun z => 2 < Z.U z - Z.S z) / wmass q Ctl = 1 / 2 := by
  rw [naive₂, recensored₂, weighted₂, truth₂]
  norm_num

end Weighting

end TwoStageCounterexample

end StructuralNested

end CausalInference
