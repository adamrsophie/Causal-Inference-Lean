/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.StructuralNested.TwoStage
public import CausalInference.StructuralNested.TwoStageGEstimation
public import CausalInference.Basic.FiniteCondIndep

/-!
# Two-stage estimation: no unmeasured confounding as conditional independence

TSD 24, Section 4.2.3 states the no unmeasured confounding assumption of two-stage estimation
as conditional independence: "switching must be independent of potential outcomes, conditional
on patient characteristics measured (and included in the model) at the secondary baseline". The
stage-one and g-estimation results of `CausalInference.StructuralNested.TwoStage` and
`CausalInference.StructuralNested.TwoStageGEstimation` use mean forms of it. This file states
the distributional forms with `FiniteDist.CondIndepFun` and proves that they imply the mean
forms.

## Main results

* `StructuralNested.meanIndepOn_of_condIndepFun`: if `Y ⫫ X | Z` on a finite law, every
  function of `Y` is mean independent of every event `{X = x}` within every event `{Z = c}`.
* `TwoStageTrial.BaselineCondIndep`, `TwoStageTrial.BaselineCondIndep.baselineNUC`: the
  untreated residual survival `U - S` is independent of the switch given membership of the
  stage-one population and the covariates measured at the secondary baseline; this implies
  `TwoStageTrial.BaselineNUC`.
* `SwitchClock.SeqCondIndep`, `SwitchClock.SeqCondIndep.seqNUC`: at every period the untreated
  time `U` is independent of the switch at that period given being at risk and the measured
  history; this implies `SwitchClock.SeqNUC`.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

section Generic

variable {Ω β γ δ : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq β] [DecidableEq γ]
  [DecidableEq δ]

/-- A weighted sum of a function of `Y` split over the values taken by `Y`. -/
theorem wsum_comp_eq_sum_image (p : FiniteDist Ω) (s : Finset Ω) (Y : Ω → γ) (g : γ → ℝ) :
    wsum p s (fun ω => g (Y ω)) = ∑ b ∈ univ.image Y, g b * wmass p (s ∩ ev Y b) := by
  unfold wsum wmass
  rw [← sum_fiberwise_of_maps_to (g := Y) (t := univ.image Y)
    (fun ω _ => mem_image_of_mem Y (mem_univ ω))]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr (by ext ω; simp) fun ω hω => ?_
  dsimp only
  rw [mem_ev.1 (mem_inter.1 hω).2]
  ring

omit [DecidableEq Ω] in
/-- A mass of a finite event is the probability of the predicate describing it. -/
theorem wmass_eq_probOf (p : FiniteDist Ω) (s : Finset Ω) (P : Ω → Prop) [DecidablePred P]
    (h : ∀ ω, ω ∈ s ↔ P ω) : wmass p s = p.probOf P := by
  simp only [wmass, FiniteDist.probOf, FiniteDist.prob]
  congr 1
  ext ω; simp [h ω]

/-- **Conditional independence implies mean independence of every function.** If `Y ⫫ X | Z`
under the finite law `p`, then within every event `{Z = c}` every function `g (Y)` is mean
independent of every event `{X = x}` (`Longitudinal.MeanIndepOn`). -/
theorem meanIndepOn_of_condIndepFun {p : FiniteDist Ω} {Y : Ω → γ} {X : Ω → β} {Z : Ω → δ}
    (h : p.CondIndepFun Y X Z) (g : γ → ℝ) (x : β) (c : δ) :
    MeanIndepOn p (ev Z c) (ev X x) (fun ω => g (Y ω)) := by
  unfold MeanIndepOn
  rw [wsum_comp_eq_sum_image, wsum_comp_eq_sum_image, sum_mul, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  have e1 : wmass p (ev Z c ∩ ev X x ∩ ev Y b) =
      p.probOf (fun ω => Y ω = b ∧ X ω = x ∧ Z ω = c) :=
    wmass_eq_probOf p _ _ fun ω => by simp only [mem_inter, mem_ev]; tauto
  have e2 : wmass p (ev Z c) = p.probOf (fun ω => Z ω = c) :=
    wmass_eq_probOf p _ _ fun ω => by simp only [mem_ev]
  have e3 : wmass p (ev Z c ∩ ev Y b) = p.probOf (fun ω => Y ω = b ∧ Z ω = c) :=
    wmass_eq_probOf p _ _ fun ω => by simp only [mem_inter, mem_ev]; tauto
  have e4 : wmass p (ev Z c ∩ ev X x) = p.probOf (fun ω => X ω = x ∧ Z ω = c) :=
    wmass_eq_probOf p _ _ fun ω => by simp only [mem_inter, mem_ev]; tauto
  rw [e1, e2, e3, e4]
  linear_combination g b * h b x c

end Generic

namespace TwoStageTrial

variable {Ω : Type*} (M : TwoStageTrial Ω) [Fintype Ω] [DecidableEq Ω] {𝓛 : Type*}
  [DecidableEq 𝓛]

/-- **No unmeasured confounding at the secondary baseline, distributional form** (TSD 24,
Section 4.2.3): the untreated residual survival `U - S` is independent of the switch `X` given
membership of the stage-one population `P` and the covariates `L` measured at the secondary
baseline. -/
def BaselineCondIndep (p : FiniteDist Ω) (P : Finset Ω) (L : Ω → 𝓛) : Prop :=
  p.CondIndepFun (fun ω => M.U ω - M.S ω) M.X (fun ω => (decide (ω ∈ P), L ω))

variable {M} in
/-- **The distributional form implies the mean form** `BaselineNUC` used by stage one. -/
theorem BaselineCondIndep.baselineNUC {p : FiniteDist Ω} {P : Finset Ω} {L : Ω → 𝓛}
    (h : M.BaselineCondIndep p P L) : M.BaselineNUC p P L := fun l => by
  have e : P ∩ ev L l = ev (fun ω => (decide (ω ∈ P), L ω)) (true, l) := by
    ext ω; simp
  rw [e]
  exact meanIndepOn_of_condIndepFun h id true (true, l)

end TwoStageTrial

namespace SwitchClock

variable {Ω 𝓗 : Type*} (M : SwitchClock Ω 𝓗) [Fintype Ω] [DecidableEq Ω] [Fintype 𝓗]
  [DecidableEq 𝓗]

/-- **Sequential no unmeasured confounding, distributional form** (TSD 24, Section 4.2.3.1,
"TSE with g-estimation"): at every period `j < K`, the untreated survival `U` is independent of
the switch at `j` given being at risk at `j` and the measured history `H j`. -/
def SeqCondIndep (p : FiniteDist Ω) (K : ℕ) : Prop :=
  ∀ j < K, p.CondIndepFun M.U (fun ω => decide (ω ∈ M.switchAt j))
    (fun ω => (decide (ω ∈ M.riskSet j), M.H j ω))

omit [Fintype 𝓗] in
variable {M} in
/-- **The distributional form implies the mean form** `SeqNUC` used by g-estimation. -/
theorem SeqCondIndep.seqNUC {p : FiniteDist Ω} {K : ℕ} (h : M.SeqCondIndep p K) :
    M.SeqNUC p K := fun j hj hh g => by
  have e1 : M.riskCell j hh = ev (fun ω => (decide (ω ∈ M.riskSet j), M.H j ω)) (true, hh) := by
    ext ω; simp [riskCell]
  have e2 : M.switchAt j = ev (fun ω => decide (ω ∈ M.switchAt j)) true := by
    ext ω; simp
  rw [e1, e2]
  exact meanIndepOn_of_condIndepFun (h j hj) g true (true, hh)

end SwitchClock

end StructuralNested

end CausalInference
