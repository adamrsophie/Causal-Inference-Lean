/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Two-stage estimation with g-estimation

The version of two-stage estimation that replaces the accelerated failure time model of stage
one by a structural nested model and g-estimation (TSD 16, Section 3.2.4, paragraph 1; TSD 24,
Section 4.2.3.1, "TSE with g-estimation", TSEgest). Time runs on a discrete clock of decision
periods after the secondary baseline; at each period a patient at risk may switch, given the
measured history. The candidate untreated time `U(ψ)` is computed from the observed data by
Equation (1) applied from the switch. The true `ψ` is the one at which the switch is
independent of `U(ψ)` given the history: a switching model with `U(ψ)` as covariate has a zero
coefficient.

## Main definitions

* `StructuralNested.SwitchClock`: observed survival `Y` after the secondary baseline, switch
  `X` at period `W`, measured history `H j`, latent untreated survival `U`.
* `SwitchClock.counterfactual ψ`, `SwitchClock.StructuralModel`.
* `SwitchClock.riskSet`, `SwitchClock.riskCell`, `SwitchClock.switchAt`; `SwitchClock.SeqNUC`:
  sequential no unmeasured confounding with respect to `U` (in each risk cell, every function of
  `U` is mean independent of the switch).
* `SwitchClock.gEst`: the covariance form of the g-estimating function,
  `∑_j ∑_{at risk at j} p (A_j - P(A_j | history)) U(ψ)`.

## Main results

* `SwitchClock.cov_eq_zero`: at the true parameter, in every period and risk cell the switch is
  mean independent of every function of `U(ψ)`, and the summed
  covariances vanish; `SwitchClock.gEst_eq_zero`: the true parameter is a root.
* `SwitchClock.gEst_eq`: `G(ψ) = α + exp ψ β`; `SwitchClock.gEst_eq_zero_iff`: the root is
  unique when `β ≠ 0`; `SwitchClock.gSlope_pos`: `β > 0` when in every risk cell the patients
  switching now spend at least the cell mean time on the switch treatment, strictly in one
  cell; `SwitchClock.treatedLonger_last`: this holds automatically in the last period.
* `SwitchClock.gEst_eq_zero_iff_one_period`: one period (switching at the secondary baseline):
  the root is unique as soon as one risk cell has switchers with positive treated time and
  non-switchers. `SwitchClock.gEst_eq_zero_iff_two_period`: two periods: the condition is
  needed at period `0` only, where it can fail, since later switchers have treated time too.
* `GEstimationExample`: a two-period model in which a deterioration measured during the first
  period drives the switch at period `1` and survival. With the time-varying history, no
  unmeasured confounding and positivity hold (`nuc_full`, `positive_full`) and the unique root
  is the true `exp ψ₀ = 1/2` (`root_full`); with the baseline record only, no unmeasured
  confounding fails (`not_nuc_base`) and the root is `exp ψ = 5/6` (`root_base`).

## Setting and scope

Finite sample space and finite distribution (`CausalInference.Basic.FiniteDistribution`) with
the finite conditioning of `CausalInference.Longitudinal.Basic`; real survival times, natural
number decision periods. Censoring is not modeled (recensoring and weighting are treated in
`CausalInference.StructuralNested.TwoStage` and its countermodels). The parametric switching
model (for example logistic) and its coefficient are represented by its population score, the
summed conditional covariance; the variant without a secondary baseline, from randomization,
is the case where the clock starts at randomization.

## Sources

* N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival time
  estimates in the presence of treatment switching* (2014): Section 3.2.4.
* H. Bell Gorrod, N. R. Latimer, K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to TSD 16*
  (2024): Section 4.2.3.1, "TSE with g-estimation".
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace StructuralNested

/-- A variable constant on an event is mean independent of every event within it. -/
theorem meanIndepOn_of_const {Ω : Type*} [DecidableEq Ω] {m : Ω → ℝ} {s t : Finset Ω}
    {f : Ω → ℝ} {c : ℝ} (h : ∀ ω ∈ s, f ω = c) : MeanIndepOn m s t f := by
  rw [MeanIndepOn, wsum_congr (s := s ∩ t) (g := fun _ => c) fun ω hω => h ω (mem_inter.1 hω).1,
    wsum_congr h, wsum_const, wsum_const]
  ring

/-- Switching on a discrete clock after the secondary baseline. Time is measured from the
secondary baseline; the decision to switch can be taken at the start of each period
`j = 0, 1, 2, ...`. `Y` is the observed survival after the secondary baseline, `X` whether the
patient switched, `W` the period of the switch (meaningful when `X ω = true`), `H j` the
measured history available at the decision of period `j` (baseline and time-varying
covariates), and `U` the latent survival after the secondary baseline had the patient not
switched. -/
structure SwitchClock (Ω : Type*) (𝓗 : Type*) where
  /-- The observed survival after the secondary baseline. -/
  Y : Ω → ℝ
  /-- Whether the patient switched. -/
  X : Ω → Bool
  /-- The period of the switch. -/
  W : Ω → ℕ
  /-- The measured history at the decision of each period. -/
  H : ℕ → Ω → 𝓗
  /-- The latent survival after the secondary baseline without the switch. -/
  U : Ω → ℝ

namespace SwitchClock

variable {Ω 𝓗 : Type*} (M : SwitchClock Ω 𝓗)

/-- The time spent on the switch treatment: `Y - W` for switchers, `0` otherwise. -/
noncomputable def treated (ω : Ω) : ℝ := if M.X ω then M.Y ω - M.W ω else 0

/-- **The structural model**, computed from the observed data for a candidate `ψ`: the survival
after the secondary baseline with the effect of the switch undone,
`U(ψ) = (Y - treated) + exp ψ treated` (TSD 24, Equation (1), from the switch). -/
noncomputable def counterfactual (ψ : ℝ) (ω : Ω) : ℝ :=
  (M.Y ω - M.treated ω) + Real.exp ψ * M.treated ω

/-- The structural model holds at `ψ`: `U = U(ψ)` for every patient. -/
def StructuralModel (ψ : ℝ) : Prop := ∀ ω, M.U ω = M.counterfactual ψ ω

/-! ### Risk cells and sequential no unmeasured confounding -/

section Finite

variable [Fintype Ω] [DecidableEq Ω] [Fintype 𝓗] [DecidableEq 𝓗]

/-- The patients who switch at period `j`. -/
def switchAt (j : ℕ) : Finset Ω := univ.filter fun ω => M.X ω = true ∧ M.W ω = j

/-- The risk set of period `j`: not switched before `j` and alive at `j`. -/
noncomputable def riskSet (j : ℕ) : Finset Ω :=
  univ.filter fun ω => (M.X ω = true → j ≤ M.W ω) ∧ (j : ℝ) < M.Y ω

/-- The risk cell of period `j` with measured history `h`. -/
noncomputable def riskCell (j : ℕ) (h : 𝓗) : Finset Ω := M.riskSet j ∩ ev (M.H j) h

/-- **Sequential no unmeasured confounding with respect to the untreated time** (TSD 24,
Section 4.2.3.1, "TSE with g-estimation"): at each period `j < K`, within every risk cell, the
switch at `j` is independent of the untreated survival `U`, stated as: every function of `U` is
mean independent of the switch (`Longitudinal.MeanIndepOn`); on a finite space this is
conditional independence of the switch and `U` given the risk cell. -/
def SeqNUC (p : FiniteDist Ω) (K : ℕ) : Prop :=
  ∀ j < K, ∀ h, ∀ g : ℝ → ℝ, MeanIndepOn p (M.riskCell j h) (M.switchAt j) fun ω => g (M.U ω)

/-- The indicator of switching at `j`. -/
def switchInd (j : ℕ) (ω : Ω) : ℝ := if ω ∈ M.switchAt j then 1 else 0

/-- The probability of switching at `j` given the risk cell of `ω`. -/
noncomputable def switchProb (p : FiniteDist Ω) (j : ℕ) (ω : Ω) : ℝ :=
  condProb p (M.riskCell j (M.H j ω)) (M.switchAt j)

/-- The contribution of period `j` to the estimating function for a variable `f`:
`∑_{ω at risk at j} p ω (A_j ω - P(A_j = 1 | risk cell of ω)) f ω`, the mass times the
conditional covariance of the switch and `f`, summed over the risk cells. -/
noncomputable def periodCov (p : FiniteDist Ω) (j : ℕ) (f : Ω → ℝ) : ℝ :=
  wsum p (M.riskSet j) fun ω => (M.switchInd j ω - M.switchProb p j ω) * f ω

/-- **The g-estimating function** in covariance form: `G(ψ) = ∑_{j < K} periodCov j U(ψ)`. It
is the population version of the score of a switching model with `U(ψ)` as covariate, at a
zero coefficient. -/
noncomputable def gEst (p : FiniteDist Ω) (K : ℕ) (ψ : ℝ) : ℝ :=
  ∑ j ∈ range K, M.periodCov p j (M.counterfactual ψ)

omit [Fintype 𝓗] in
/-- **Within one cell, mean independence makes the covariance term vanish.** -/
theorem wsum_cov_eq_zero (p : FiniteDist Ω) {s t : Finset Ω} {f : Ω → ℝ}
    (h : MeanIndepOn p s t f) :
    wsum p s (fun ω => ((if ω ∈ t then 1 else 0) - condProb p s t) * f ω) = 0 := by
  have e : wsum p s (fun ω => ((if ω ∈ t then 1 else 0) - condProb p s t) * f ω) =
      wsum p (s ∩ t) f - condProb p s t * wsum p s f := by
    simp only [wsum, sub_mul, mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    · rw [← sum_ite_mem]; exact sum_congr rfl fun ω _ => by split_ifs <;> ring
    · exact sum_congr rfl fun ω _ => by ring
  rw [e]
  rcases (wmass_nonneg p.nonneg s).eq_or_lt with h0 | h0
  · have h1 : wmass p (s ∩ t) = 0 :=
      le_antisymm ((wmass_mono p.nonneg inter_subset_left).trans_eq h0.symm)
        (wmass_nonneg p.nonneg _)
    rw [wsum_eq_zero_of_wmass_eq_zero p.nonneg h1, wsum_eq_zero_of_wmass_eq_zero p.nonneg h0.symm]
    ring
  · unfold MeanIndepOn at h
    rw [condProb, div_mul_eq_mul_div, sub_eq_zero, eq_div_iff h0.ne']
    linear_combination h

/-- A period term split over the risk cells. -/
theorem periodCov_eq_sum (p : FiniteDist Ω) (j : ℕ) (f : Ω → ℝ) :
    M.periodCov p j f = ∑ h, wsum p (M.riskCell j h)
      (fun ω => ((if ω ∈ M.switchAt j then 1 else 0) -
        condProb p (M.riskCell j h) (M.switchAt j)) * f ω) := by
  rw [periodCov, wsum_eq_sum_ev _ (M.H j)]
  refine sum_congr rfl fun h _ => wsum_congr fun ω hω => ?_
  have hh : M.H j ω = h := mem_ev.1 (mem_inter.1 hω).2
  rw [switchInd, switchProb, hh]

omit [Fintype 𝓗] in
/-- **At the true parameter, the switch is conditionally independent of `U(ψ)` given the
measured history** (TSD 24, Section 4.2.3.1: the coefficient of the counterfactual survival in
the switching model is zero). Under the structural model at `ψ₀` and sequential no unmeasured
confounding up to `K`, for every function `g`, every period `j < K` and every risk cell, the
switch at `j` and `g (U(ψ₀))` have zero conditional covariance; so the sum over periods of the
covariance terms vanishes for every `g`. -/
theorem cov_eq_zero [Finite 𝓗] {p : FiniteDist Ω} {K : ℕ} {ψ₀ : ℝ} (hmodel : M.StructuralModel ψ₀)
    (hnuc : M.SeqNUC p K) (g : ℝ → ℝ) :
    (∀ j < K, ∀ h, MeanIndepOn p (M.riskCell j h) (M.switchAt j)
        fun ω => g (M.counterfactual ψ₀ ω)) ∧
      ∑ j ∈ range K, M.periodCov p j (fun ω => g (M.counterfactual ψ₀ ω)) = 0 := by
  have := Fintype.ofFinite 𝓗
  have hc : (fun ω => g (M.counterfactual ψ₀ ω)) = fun ω => g (M.U ω) := by
    funext ω; rw [hmodel ω]
  refine ⟨fun j hj h => hc ▸ hnuc j hj h g, sum_eq_zero fun j hj => ?_⟩
  rw [periodCov_eq_sum]
  exact sum_eq_zero fun h _ => wsum_cov_eq_zero p (hc ▸ hnuc j (mem_range.1 hj) h g)

omit [Fintype 𝓗] in
/-- **The true parameter is a root of the g-estimating function.** -/
theorem gEst_eq_zero [Finite 𝓗] {p : FiniteDist Ω} {K : ℕ} {ψ₀ : ℝ} (hmodel : M.StructuralModel ψ₀)
    (hnuc : M.SeqNUC p K) : M.gEst p K ψ₀ = 0 :=
  (M.cov_eq_zero hmodel hnuc id).2

/-- The intercept of the g-estimating function. -/
noncomputable def gIntercept (p : FiniteDist Ω) (K : ℕ) : ℝ :=
  ∑ j ∈ range K, M.periodCov p j fun ω => M.Y ω - M.treated ω

/-- The slope of the g-estimating function in `exp ψ`: the summed covariance between the switch
and the time on the switch treatment. -/
noncomputable def gSlope (p : FiniteDist Ω) (K : ℕ) : ℝ :=
  ∑ j ∈ range K, M.periodCov p j M.treated

omit [Fintype 𝓗] in
theorem periodCov_add_mul (p : FiniteDist Ω) (j : ℕ) (f g : Ω → ℝ) (c : ℝ) :
    M.periodCov p j (fun ω => f ω + c * g ω) = M.periodCov p j f + c * M.periodCov p j g := by
  simp only [periodCov, wsum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

omit [Fintype 𝓗] in
/-- **The g-estimating function is affine in `exp ψ`:** `G(ψ) = α + exp ψ β`. -/
theorem gEst_eq (p : FiniteDist Ω) (K : ℕ) (ψ : ℝ) :
    M.gEst p K ψ = M.gIntercept p K + Real.exp ψ * M.gSlope p K := by
  simp only [gEst, gIntercept, gSlope, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => M.periodCov_add_mul p j _ _ _

omit [Fintype 𝓗] in
/-- **Uniqueness of the root.** If the true parameter is a root and the slope does not vanish,
it is the only root. -/
theorem gEst_eq_zero_iff {p : FiniteDist Ω} {K : ℕ} {ψ₀ : ℝ} (hroot : M.gEst p K ψ₀ = 0)
    (hβ : M.gSlope p K ≠ 0) (ψ : ℝ) : M.gEst p K ψ = 0 ↔ ψ = ψ₀ := by
  refine ⟨fun h => ?_, fun h => h ▸ hroot⟩
  rw [gEst_eq] at h hroot
  exact Real.exp_injective (mul_right_cancel₀ hβ (by linarith))

/-- In a risk cell, the patients who switch now spend at least the cell mean time on the switch
treatment: `E[treated | cell] ≤ E[treated | cell, switch at j]`, stated without division. -/
def TreatedLonger (p : FiniteDist Ω) (j : ℕ) (h : 𝓗) : Prop :=
  wsum p (M.riskCell j h) M.treated * wmass p (M.riskCell j h ∩ M.switchAt j) ≤
    wsum p (M.riskCell j h ∩ M.switchAt j) M.treated * wmass p (M.riskCell j h)

omit [Fintype 𝓗] in
/-- The cell term of the slope, without division. -/
theorem cellSlope_mul (p : FiniteDist Ω) (j : ℕ) (h : 𝓗) :
    wmass p (M.riskCell j h) * wsum p (M.riskCell j h)
      (fun ω => ((if ω ∈ M.switchAt j then 1 else 0) -
        condProb p (M.riskCell j h) (M.switchAt j)) * M.treated ω) =
    wsum p (M.riskCell j h ∩ M.switchAt j) M.treated * wmass p (M.riskCell j h) -
      wsum p (M.riskCell j h) M.treated * wmass p (M.riskCell j h ∩ M.switchAt j) := by
  set s := M.riskCell j h
  set t := M.switchAt j
  have e : wsum p s (fun ω => ((if ω ∈ t then 1 else 0) - condProb p s t) * M.treated ω) =
      wsum p (s ∩ t) M.treated - condProb p s t * wsum p s M.treated := by
    simp only [wsum, sub_mul, mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    · rw [← sum_ite_mem]; exact sum_congr rfl fun ω _ => by split_ifs <;> ring
    · exact sum_congr rfl fun ω _ => by ring
  rw [e]
  linear_combination (-(wsum p s M.treated)) * wmass_mul_condProb p.nonneg s t

omit [Fintype 𝓗] in
/-- **A sufficient condition for uniqueness.** If in every risk cell of every period `j < K` the
patients switching now spend at least the cell mean time on the switch treatment, and in one
cell of positive mass strictly more, the slope is positive, so the true parameter is the unique
root. -/
theorem gSlope_pos [Finite 𝓗] {p : FiniteDist Ω} {K : ℕ}
    (hall : ∀ j < K, ∀ h, M.TreatedLonger p j h)
    {j₀ : ℕ} (hj₀ : j₀ < K) {h₀ : 𝓗} (hm : 0 < wmass p (M.riskCell j₀ h₀))
    (hstrict : wsum p (M.riskCell j₀ h₀) M.treated * wmass p (M.riskCell j₀ h₀ ∩ M.switchAt j₀) <
      wsum p (M.riskCell j₀ h₀ ∩ M.switchAt j₀) M.treated * wmass p (M.riskCell j₀ h₀)) :
    0 < M.gSlope p K := by
  have := Fintype.ofFinite 𝓗
  have hcell : ∀ j < K, ∀ h, 0 ≤ wsum p (M.riskCell j h)
      (fun ω => ((if ω ∈ M.switchAt j then 1 else 0) -
        condProb p (M.riskCell j h) (M.switchAt j)) * M.treated ω) := fun j hj h => by
    rcases (wmass_nonneg p.nonneg (M.riskCell j h)).eq_or_lt with h0 | h0
    · rw [wsum_eq_zero_of_wmass_eq_zero p.nonneg h0.symm]
    · have hA : 0 ≤ wmass p (M.riskCell j h) * wsum p (M.riskCell j h)
          (fun ω => ((if ω ∈ M.switchAt j then 1 else 0) -
            condProb p (M.riskCell j h) (M.switchAt j)) * M.treated ω) := by
        rw [cellSlope_mul]; have := hall j hj h; unfold TreatedLonger at this; linarith
      exact (mul_nonneg_iff_of_pos_left h0).1 hA
  have hpos : 0 < wsum p (M.riskCell j₀ h₀)
      (fun ω => ((if ω ∈ M.switchAt j₀ then 1 else 0) -
        condProb p (M.riskCell j₀ h₀) (M.switchAt j₀)) * M.treated ω) := by
    refine (mul_pos_iff_of_pos_left hm).1 ?_
    rw [cellSlope_mul]; linarith
  unfold gSlope
  rw [← sum_erase_add _ _ (mem_range.2 hj₀), periodCov_eq_sum,
    ← sum_erase_add _ _ (mem_univ h₀)]
  refine add_pos_of_nonneg_of_pos (sum_nonneg fun j hj => ?_)
    (add_pos_of_nonneg_of_pos (sum_nonneg fun h _ => hcell j₀ hj₀ h) hpos)
  rw [periodCov_eq_sum]
  exact sum_nonneg fun h _ => hcell j (mem_range.1 (mem_of_mem_erase hj)) h

omit [Fintype 𝓗] in
/-- **The last period needs no condition.** If every switch happens before period `K` and
switchers survive their switch period (`W ≤ Y`), the cells of period `K - 1` satisfy
`TreatedLonger`: whoever is at risk at `K - 1` and has positive treated time switches at
`K - 1`. -/
theorem treatedLonger_last {p : FiniteDist Ω} {K : ℕ} (hK : ∀ ω, M.X ω = true → M.W ω < K)
    (hWY : ∀ ω, M.X ω = true → (M.W ω : ℝ) ≤ M.Y ω) (h : 𝓗) :
    M.TreatedLonger p (K - 1) h := by
  set s := M.riskCell (K - 1) h
  set t := M.switchAt (K - 1)
  have hD : wsum p s M.treated = wsum p (s ∩ t) M.treated := by
    rw [wsum, wsum, ← sum_ite_mem]
    refine sum_congr rfl fun ω hω => ?_
    split_ifs with hm
    · rfl
    · have hr := (mem_inter.1 hω).1
      simp only [riskSet, mem_filter, mem_univ, true_and] at hr
      cases hX : M.X ω
      · simp [treated, hX]
      · have : M.W ω = K - 1 := by have := hK ω hX; have := hr.1 hX; omega
        exact absurd (by simp [t, switchAt, hX, this]) hm
  have hnn : 0 ≤ wsum p (s ∩ t) M.treated := sum_nonneg fun ω _ => by
    refine mul_nonneg (p.nonneg ω) ?_
    unfold treated; split_ifs with hX
    · linarith [hWY ω hX]
    · exact le_rfl
  unfold TreatedLonger
  rw [hD]
  exact mul_le_mul_of_nonneg_left (wmass_mono p.nonneg inter_subset_left) hnn

omit [Fintype 𝓗] in
/-- **One period** (every switch at the secondary baseline, `W = 0`). Switchers survive their
switch period; if some risk cell has switchers with positive treated time and positive mass of
non-switchers, the true parameter is the unique root of the g-estimating function. -/
theorem gEst_eq_zero_iff_one_period [Finite 𝓗] {p : FiniteDist Ω} {ψ₀ : ℝ}
    (hmodel : M.StructuralModel ψ₀) (hnuc : M.SeqNUC p 1)
    (hK : ∀ ω, M.X ω = true → M.W ω < 1) (hWY : ∀ ω, M.X ω = true → (M.W ω : ℝ) ≤ M.Y ω)
    {h₀ : 𝓗} (hD : 0 < wsum p (M.riskCell 0 h₀ ∩ M.switchAt 0) M.treated)
    (hN : wmass p (M.riskCell 0 h₀ ∩ M.switchAt 0) < wmass p (M.riskCell 0 h₀)) (ψ : ℝ) :
    M.gEst p 1 ψ = 0 ↔ ψ = ψ₀ := by
  have := Fintype.ofFinite 𝓗
  have hall : ∀ j < 1, ∀ h, M.TreatedLonger p j h := fun j hj h => by
    obtain rfl : j = 0 := by omega
    exact M.treatedLonger_last hK hWY h
  have hD' : wsum p (M.riskCell 0 h₀) M.treated =
      wsum p (M.riskCell 0 h₀ ∩ M.switchAt 0) M.treated := by
    rw [wsum, wsum, ← sum_ite_mem]
    refine sum_congr rfl fun ω hω => ?_
    split_ifs with hm
    · rfl
    · have hr := (mem_inter.1 hω).1
      simp only [riskSet, mem_filter, mem_univ, true_and] at hr
      cases hX : M.X ω
      · simp [treated, hX]
      · have : M.W ω = 0 := by have := hK ω hX; omega
        exact absurd (by simp [switchAt, hX, this]) hm
  have hm : 0 < wmass p (M.riskCell 0 h₀) :=
    (wmass_nonneg p.nonneg _).trans_lt hN
  refine M.gEst_eq_zero_iff (M.gEst_eq_zero hmodel hnuc) (M.gSlope_pos hall one_pos hm ?_).ne' ψ
  rw [hD']
  exact mul_lt_mul_of_pos_left hN hD

omit [Fintype 𝓗] in
/-- **Two periods.** Every switch happens at period `0` or `1`, and switchers survive their
switch period. If the period-`0` switchers spend at least the cell mean time on the switch
treatment in every period-`0` risk cell (`TreatedLonger p 0`), and strictly more in one cell of
positive mass of some period, the true parameter is the unique root of the g-estimating
function. The period-`1` cells need no condition (`treatedLonger_last`). The condition at
period `0` can fail: a patient who switches at period `1` has positive treated time but is not
a period-`0` switcher. -/
theorem gEst_eq_zero_iff_two_period [Finite 𝓗] {p : FiniteDist Ω} {ψ₀ : ℝ}
    (hmodel : M.StructuralModel ψ₀) (hnuc : M.SeqNUC p 2)
    (hK : ∀ ω, M.X ω = true → M.W ω < 2) (hWY : ∀ ω, M.X ω = true → (M.W ω : ℝ) ≤ M.Y ω)
    (h0 : ∀ h, M.TreatedLonger p 0 h) {j₀ : ℕ} (hj₀ : j₀ < 2) {h₀ : 𝓗}
    (hm : 0 < wmass p (M.riskCell j₀ h₀))
    (hstrict : wsum p (M.riskCell j₀ h₀) M.treated * wmass p (M.riskCell j₀ h₀ ∩ M.switchAt j₀) <
      wsum p (M.riskCell j₀ h₀ ∩ M.switchAt j₀) M.treated * wmass p (M.riskCell j₀ h₀))
    (ψ : ℝ) : M.gEst p 2 ψ = 0 ↔ ψ = ψ₀ := by
  have := Fintype.ofFinite 𝓗
  have hall : ∀ j < 2, ∀ h, M.TreatedLonger p j h := fun j hj h => by
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact h0 h
    · exact M.treatedLonger_last hK hWY h
  exact M.gEst_eq_zero_iff (M.gEst_eq_zero hmodel hnuc) (M.gSlope_pos hall hj₀ hm hstrict).ne' ψ

end Finite

end SwitchClock

/-! ### A countermodel: time-varying confounders are needed -/

namespace GEstimationExample

/-- A point `(l, a)`: `l` is a deterioration measured during the first period after the
secondary baseline, `a` the switch at the start of the second period. -/
abbrev Ω := Bool × Bool

/-- A deteriorated patient switches with probability `3/4`, another with probability `1/4`;
deterioration has probability `1/2`. -/
noncomputable def p : FiniteDist Ω where
  mass ω := if ω.2 = ω.1 then 3 / 8 else 1 / 8
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]; norm_num

/-- The untreated survival after the secondary baseline: `2` if deteriorated, `4` otherwise. -/
noncomputable def u (ω : Ω) : ℝ := if ω.1 then 2 else 4

/-- The trial with the full measured history: nothing at period `0`, the deterioration at
period `1`. Switches happen at period `1`, and the switch doubles the remaining survival
(`exp ψ₀ = 1/2`). -/
noncomputable def full : SwitchClock Ω (Option Bool) where
  Y ω := if ω.2 then 1 + 2 * (u ω - 1) else u ω
  X ω := ω.2
  W _ := 1
  H j ω := if j = 0 then none else some ω.1
  U := u

/-- The same trial with the baseline record only: the history is empty at every period. -/
noncomputable def base : SwitchClock Ω (Option Bool) :=
  { full with H := fun _ _ => none }

/-- The true parameter. -/
noncomputable def ψ₀ : ℝ := Real.log (1 / 2)

theorem exp_ψ₀ : Real.exp ψ₀ = 1 / 2 := Real.exp_log (by norm_num)

theorem model_full : full.StructuralModel ψ₀ := by
  rintro ⟨l, a⟩
  cases l <;> cases a <;>
    simp [full, SwitchClock.counterfactual, SwitchClock.treated, u, exp_ψ₀]

theorem model_base : base.StructuralModel ψ₀ := model_full

theorem riskSet_full (j : ℕ) (hj : j < 2) : full.riskSet j = univ := by
  ext ⟨l, a⟩
  simp only [SwitchClock.riskSet, mem_filter, mem_univ, true_and, iff_true]
  refine ⟨fun _ => by simp [full]; omega, ?_⟩
  have : (j : ℝ) < 2 := by exact_mod_cast hj
  cases l <;> cases a <;> simp [full, u] <;> linarith

theorem riskSet_base (j : ℕ) (hj : j < 2) : base.riskSet j = univ := riskSet_full j hj

theorem switchAt_zero : full.switchAt 0 = ∅ := by
  ext ω; simp [SwitchClock.switchAt, full]

theorem switchAt_one : full.switchAt 1 = univ.filter fun ω => ω.2 = true := by
  ext ω; simp [SwitchClock.switchAt, full]

/-- Period `0` contributes nothing: nobody switches at the secondary baseline. -/
theorem periodCov_zero (M : SwitchClock Ω (Option Bool)) (hM : M.switchAt 0 = ∅)
    (f : Ω → ℝ) : M.periodCov p 0 f = 0 := by
  simp [SwitchClock.periodCov, SwitchClock.switchInd, SwitchClock.switchProb, condProb, hM,
    wsum, wmass]

theorem riskCell_full_one (l : Bool) :
    full.riskCell 1 (some l) = univ.filter fun ω => ω.1 = l := by
  rw [SwitchClock.riskCell, riskSet_full 1 (by norm_num)]
  ext ω; simp [ev, full]

theorem riskCell_full_none : full.riskCell 1 none = ∅ := by
  ext ω; simp [SwitchClock.riskCell, ev, full]

theorem switchProb_full (ω : Ω) :
    full.switchProb p 1 ω = if ω.1 then 3 / 4 else 1 / 4 := by
  have h : full.H 1 ω = some ω.1 := rfl
  rw [SwitchClock.switchProb, h, riskCell_full_one, switchAt_one, condProb, wmass, wmass,
    ← filter_and, sum_filter, sum_filter]
  rcases ω with ⟨l, a⟩
  cases l <;> simp [Fintype.sum_prod_type, p] <;> norm_num

theorem switchProb_base (ω : Ω) : base.switchProb p 1 ω = 1 / 2 := by
  have hc : base.riskCell 1 (base.H 1 ω) = univ := by
    rw [SwitchClock.riskCell, riskSet_base 1 (by norm_num)]; ext; simp [ev, base]
  have hs : base.switchAt 1 = univ.filter fun ω => ω.2 = true := switchAt_one
  rw [SwitchClock.switchProb, hc, hs, condProb, univ_inter, wmass, wmass, sum_filter]
  simp [Fintype.sum_prod_type, p]; norm_num

theorem periodCov_one_full (f : Ω → ℝ) : full.periodCov p 1 f =
    ∑ ω, p ω * (((if ω.2 then 1 else 0) - if ω.1 then 3 / 4 else 1 / 4) * f ω) := by
  rw [SwitchClock.periodCov, riskSet_full 1 (by norm_num), wsum]
  refine sum_congr rfl fun ω _ => ?_
  rw [SwitchClock.switchInd, switchProb_full, switchAt_one]
  simp

theorem periodCov_one_base (f : Ω → ℝ) : base.periodCov p 1 f =
    ∑ ω, p ω * (((if ω.2 then 1 else 0) - 1 / 2) * f ω) := by
  rw [SwitchClock.periodCov, riskSet_base 1 (by norm_num), wsum]
  refine sum_congr rfl fun ω _ => ?_
  rw [SwitchClock.switchInd, switchProb_base]
  have hs : base.switchAt 1 = univ.filter fun ω => ω.2 = true := switchAt_one
  rw [hs]; simp

theorem gEst_full (ψ : ℝ) : full.gEst p 2 ψ = 3 / 4 * Real.exp ψ - 3 / 8 := by
  rw [SwitchClock.gEst, sum_range_succ, sum_range_one, periodCov_zero full switchAt_zero,
    periodCov_one_full]
  simp [Fintype.sum_prod_type, p, full, SwitchClock.counterfactual, SwitchClock.treated, u]
  ring

theorem gEst_base (ψ : ℝ) : base.gEst p 2 ψ = 3 / 4 * Real.exp ψ - 5 / 8 := by
  rw [SwitchClock.gEst, sum_range_succ, sum_range_one, periodCov_zero base switchAt_zero,
    periodCov_one_base]
  simp [Fintype.sum_prod_type, p, base, full, SwitchClock.counterfactual, SwitchClock.treated,
    u]
  ring

/-- **No unmeasured confounding holds given the full history**: within every risk cell the
untreated time is constant (period `1`) or nobody switches (period `0`). -/
theorem nuc_full : full.SeqNUC p 2 := by
  intro j hj h g
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · simp [MeanIndepOn, switchAt_zero, wsum, wmass]
  · cases h with
    | none => simp [MeanIndepOn, riskCell_full_none, wsum, wmass]
    | some l =>
      rw [riskCell_full_one]
      exact meanIndepOn_of_const (c := g (if l then 2 else 4)) fun ω hω => by
        have : ω.1 = l := (mem_filter.1 hω).2
        simp [full, u, this]

/-- **Positivity given the full history**: in each risk cell of period `1` the probability of
switching is strictly between `0` and `1`. -/
theorem positive_full (ω : Ω) :
    0 < full.switchProb p 1 ω ∧ full.switchProb p 1 ω < 1 := by
  rw [switchProb_full]; split_ifs <;> norm_num

/-- **No unmeasured confounding fails given the baseline record**: the switch at period `1` is
not mean independent of the untreated time. -/
theorem not_nuc_base : ¬ base.SeqNUC p 2 := by
  intro h
  have := h 1 (by norm_num) none id
  have hc : base.riskCell 1 none = univ := by
    rw [SwitchClock.riskCell, riskSet_base 1 (by norm_num)]; ext; simp [ev, base]
  have hs : base.switchAt 1 = univ.filter fun ω => ω.2 = true := switchAt_one
  rw [hc, hs, MeanIndepOn, univ_inter, wsum, wsum, wmass, wmass, sum_filter, sum_filter] at this
  simp [Fintype.sum_prod_type, p, base, full, u] at this
  norm_num at this

/-- **With the time-varying history, g-estimation recovers the true parameter**, as its unique
root (`G(ψ) = 3/4 exp ψ - 3/8`). -/
theorem root_full (ψ : ℝ) : full.gEst p 2 ψ = 0 ↔ ψ = ψ₀ := by
  rw [gEst_full]
  constructor
  · intro h
    exact Real.exp_injective ((show Real.exp ψ = 1 / 2 by linarith).trans exp_ψ₀.symm)
  · rintro rfl; rw [exp_ψ₀]; norm_num

/-- The root at `ψ₀` is also an instance of `SwitchClock.gEst_eq_zero`. -/
theorem gEst_full_eq_zero : full.gEst p 2 ψ₀ = 0 := full.gEst_eq_zero model_full nuc_full

/-- **With the baseline record only, the g-estimating function has a wrong root**:
`G(ψ) = 3/4 exp ψ - 5/8` vanishes exactly at `exp ψ = 5/6`, while the true time ratio is
`exp ψ₀ = 1/2`. The structural model holds and the switch probabilities are the same as above;
only the conditioning history differs. -/
theorem root_base (ψ : ℝ) : base.gEst p 2 ψ = 0 ↔ Real.exp ψ = 5 / 6 := by
  rw [gEst_base]
  constructor <;> intro h <;> linarith

theorem root_base_ne : base.gEst p 2 ψ₀ ≠ 0 := by
  rw [Ne, root_base, exp_ψ₀]; norm_num

end GEstimationExample

end StructuralNested

end CausalInference
