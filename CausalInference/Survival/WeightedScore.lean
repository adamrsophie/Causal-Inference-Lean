/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.IPCW
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The weighted Cox score for two arms in discrete time

The partial likelihood score of the proportional hazards model with a binary covariate (the
arm), in discrete time with tied events handled by the Breslow approximation, computed from
event and risk masses `D_a(t)` and `Y_a(t)` of the two arms `a = 0, 1` over the periods
`t < n`:
`U(β) = ∑_{t < n} [D_1(t) - e^β Y_1(t) / (Y_0(t) + e^β Y_1(t)) (D_0(t) + D_1(t))]`.
It is the derivative in `β` of the Breslow log partial likelihood
`∑_t [β D_1(t) - (D_0(t) + D_1(t)) log(Y_0(t) + e^β Y_1(t))]`. The exact discrete (conditional
logistic) partial likelihood of Cox treats ties differently and has a different score; the
Breslow form is the one used here. The null score `U(0)` is the log-rank numerator: observed
minus expected events in arm `1`.

With the masses weighted by the inverse probability of censoring weights of
`Survival.IPCW`, this is the population score of the IPCW-adjusted Cox model of TSD 16,
Appendix A ("a time-dependent Cox model ... uses the time-varying stabilised weights").

## Main definitions

* `coxScore D₀ D₁ Y₀ Y₁ n β`: the Breslow score; `logRankNumerator`: its value at `β = 0`.
* `ScoreMasses`: the masses are those of events within risk sets (`0 ≤ D_a ≤ Y_a`).
* `CommonHazardRatio D₀ D₁ Y₀ Y₁ n r`: `D_1(t) / Y_1(t) = r D_0(t) / Y_0(t)` at every period
  with positive risk masses in both arms.
* `armEventMass`, `armRiskMass`: the weighted event and risk masses of an arm computed from the
  observed record and time-indexed weights; `cfEventMass`, `cfRiskMass`: the masses
  `P(T = t, arm = a)` and `P(T ≥ t, arm = a)` of the survival time without switching.

## Main results

* `coxScore_log_eq_zero`: under a common hazard ratio `r > 0`, every summand of `U(log r)`
  vanishes, so `U(log r) = 0`.
* `coxScore_strictAnti`, `coxScore_eq_zero_iff`: if some period has positive risk mass in both
  arms and positive event mass, `U` is strictly decreasing, and `log r` is its only root.
* `logRankNumerator_eq_zero`: the null score vanishes when the hazards agree in every period.
* `armMass_obsIpcWeight`, `coxScore_obsIpcWeight`: under consistency up to the switch,
  no unmeasured confounding of the switch and positivity, the masses weighted by
  `obsIpcWeight` and computed from the observed records are the counterfactual arm-specific
  masses, so the weighted score is the counterfactual score; `coxScore_obsIpcWeight_eq_zero_iff`:
  its only root is the logarithm of the counterfactual common hazard ratio.
* `Example.unweighted_root_ne`: censoring at the switch without weights gives the root
  `log (3/4)`, while the weighted score has the root `log (1/2)` of the counterfactual ratio.

## Sources

* D. R. Cox, *Regression models and life-tables*, J. R. Stat. Soc. B 34 (1972); N. Breslow,
  *Covariance analysis of censored survival data*, Biometrics 30 (1974).
* N. R. Latimer and K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival
  time estimates in the presence of treatment switching* (2014): Sec 3.2.1 and Appendix A.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace Survival

namespace WeightedScore

open IPCW

section Score

/-- The Breslow partial likelihood score of the proportional hazards model with a binary
covariate in discrete time, over the periods `t < n`, from the event masses `D₀ D₁` and the
risk masses `Y₀ Y₁` of arms `0` and `1`:
`U(β) = ∑_{t < n} [D₁ t - e^β Y₁ t / (Y₀ t + e^β Y₁ t) (D₀ t + D₁ t)]`. -/
noncomputable def coxScore (D₀ D₁ Y₀ Y₁ : ℕ → ℝ) (n : ℕ) (β : ℝ) : ℝ :=
  ∑ t ∈ range n, (D₁ t - Real.exp β * Y₁ t / (Y₀ t + Real.exp β * Y₁ t) * (D₀ t + D₁ t))

/-- The log-rank numerator: observed minus expected events in arm `1`,
`∑_{t < n} [D₁ t - Y₁ t / (Y₀ t + Y₁ t) (D₀ t + D₁ t)]`. -/
noncomputable def logRankNumerator (D₀ D₁ Y₀ Y₁ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, (D₁ t - Y₁ t / (Y₀ t + Y₁ t) * (D₀ t + D₁ t))

/-- The masses are event masses within risk masses: `0 ≤ D_a t ≤ Y_a t` for `t < n`. -/
def ScoreMasses (D₀ D₁ Y₀ Y₁ : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ t < n, 0 ≤ D₀ t ∧ 0 ≤ D₁ t ∧ D₀ t ≤ Y₀ t ∧ D₁ t ≤ Y₁ t

/-- A common discrete hazard ratio `r`: at every period `t < n` with positive risk masses in
both arms, the hazard of arm `1` is `r` times the hazard of arm `0`,
`D₁ t / Y₁ t = r (D₀ t / Y₀ t)`. -/
def CommonHazardRatio (D₀ D₁ Y₀ Y₁ : ℕ → ℝ) (n : ℕ) (r : ℝ) : Prop :=
  ∀ t < n, 0 < Y₀ t → 0 < Y₁ t → D₁ t / Y₁ t = r * (D₀ t / Y₀ t)

variable {D₀ D₁ Y₀ Y₁ : ℕ → ℝ} {n : ℕ}

/-- The null score is the log-rank numerator. -/
theorem coxScore_zero : coxScore D₀ D₁ Y₀ Y₁ n 0 = logRankNumerator D₀ D₁ Y₀ Y₁ n := by
  simp [coxScore, logRankNumerator]

/-- **The score vanishes at the logarithm of a common hazard ratio.** If the masses are event
masses within risk masses and the two arms have the common discrete hazard ratio `r > 0`, every
summand of `U(log r)` is zero: at a period with positive risk masses in both arms the expected
share `r Y₁ / (Y₀ + r Y₁)` of the events is exactly arm `1`'s share, and at a period with an
empty risk set in one arm that arm has no events. -/
theorem coxScore_log_eq_zero {r : ℝ} (hr : 0 < r) (hm : ScoreMasses D₀ D₁ Y₀ Y₁ n)
    (hc : CommonHazardRatio D₀ D₁ Y₀ Y₁ n r) : coxScore D₀ D₁ Y₀ Y₁ n (Real.log r) = 0 := by
  refine sum_eq_zero fun t ht => ?_
  have htn := mem_range.1 ht
  obtain ⟨h0, h1, h0Y, h1Y⟩ := hm t htn
  rw [Real.exp_log hr]
  rcases (h1.trans h1Y).eq_or_lt with hY1 | hY1
  · have : D₁ t = 0 := le_antisymm (hY1 ▸ h1Y) h1
    rw [← hY1, this]; simp
  rcases (h0.trans h0Y).eq_or_lt with hY0 | hY0
  · have : D₀ t = 0 := le_antisymm (hY0 ▸ h0Y) h0
    rw [← hY0, this]
    field_simp
    ring
  have hD := hc t htn hY0 hY1
  have hD1 : D₁ t = r * D₀ t * Y₁ t / Y₀ t := by
    field_simp at hD ⊢; linarith
  have hden : 0 < Y₀ t + r * Y₁ t := by positivity
  rw [hD1]
  field_simp
  ring

/-- The expected share `x Y₁ / (Y₀ + x Y₁)` is nondecreasing in `x > 0` for nonnegative risk
masses. -/
theorem share_le {y₀ y₁ x x' : ℝ} (h0 : 0 ≤ y₀) (h1 : 0 ≤ y₁) (hx : 0 < x) (hxx : x ≤ x') :
    x * y₁ / (y₀ + x * y₁) ≤ x' * y₁ / (y₀ + x' * y₁) := by
  rcases (add_nonneg h0 (mul_nonneg hx.le h1)).eq_or_lt with hd | hd
  · have hy0 : y₀ = 0 := by nlinarith [mul_nonneg hx.le h1]
    have hy1 : y₁ = 0 := by
      rw [hy0, zero_add] at hd
      rcases mul_eq_zero.1 hd.symm with h | h
      · exact absurd h hx.ne'
      · exact h
    simp [hy1]
  have hd' : 0 < y₀ + x' * y₁ := by nlinarith
  rw [div_le_div_iff₀ hd hd']
  nlinarith [mul_nonneg (sub_nonneg.2 hxx) (mul_nonneg h1 h0)]

/-- The expected share is strictly increasing when both risk masses are positive. -/
theorem share_lt {y₀ y₁ x x' : ℝ} (h0 : 0 < y₀) (h1 : 0 < y₁) (hx : 0 < x) (hxx : x < x') :
    x * y₁ / (y₀ + x * y₁) < x' * y₁ / (y₀ + x' * y₁) := by
  have hd : 0 < y₀ + x * y₁ := by positivity
  have hd' : 0 < y₀ + x' * y₁ := by nlinarith
  rw [div_lt_div_iff₀ hd hd']
  nlinarith [mul_pos (sub_pos.2 hxx) (mul_pos h1 h0)]

/-- **The score is strictly decreasing.** If the masses are event masses within risk masses
and some period `t < n` has positive risk masses in both arms and positive event mass, then
`β ↦ U(β)` is strictly decreasing. -/
theorem coxScore_strictAnti (hm : ScoreMasses D₀ D₁ Y₀ Y₁ n)
    (ht : ∃ t < n, 0 < Y₀ t ∧ 0 < Y₁ t ∧ 0 < D₀ t + D₁ t) :
    StrictAnti (coxScore D₀ D₁ Y₀ Y₁ n) := by
  intro β β' hββ
  obtain ⟨t₀, ht₀, hy0, hy1, hd⟩ := ht
  refine sum_lt_sum (fun t htr => ?_) ⟨t₀, mem_range.2 ht₀, ?_⟩
  · obtain ⟨h0, h1, h0Y, h1Y⟩ := hm t (mem_range.1 htr)
    have := share_le (h0.trans h0Y) (h1.trans h1Y) (Real.exp_pos β)
      (Real.exp_le_exp.2 hββ.le)
    nlinarith [mul_le_mul_of_nonneg_right this (add_nonneg h0 h1)]
  · have := share_lt hy0 hy1 (Real.exp_pos β) (Real.exp_lt_exp.2 hββ)
    nlinarith [mul_lt_mul_of_pos_right this hd]

/-- **The root is unique.** Under a common hazard ratio `r > 0`, with event masses within risk
masses and some period with positive risk masses in both arms and positive event mass, the
score vanishes exactly at `β = log r`. -/
theorem coxScore_eq_zero_iff {r : ℝ} (hr : 0 < r) (hm : ScoreMasses D₀ D₁ Y₀ Y₁ n)
    (hc : CommonHazardRatio D₀ D₁ Y₀ Y₁ n r)
    (ht : ∃ t < n, 0 < Y₀ t ∧ 0 < Y₁ t ∧ 0 < D₀ t + D₁ t) (β : ℝ) :
    coxScore D₀ D₁ Y₀ Y₁ n β = 0 ↔ β = Real.log r := by
  rw [← coxScore_log_eq_zero hr hm hc]
  exact (coxScore_strictAnti hm ht).injective.eq_iff

/-- **The log-rank numerator vanishes when the hazards agree.** If the two arms have the same
hazard at every period with positive risk masses in both arms, the null score is zero. -/
theorem logRankNumerator_eq_zero (hm : ScoreMasses D₀ D₁ Y₀ Y₁ n)
    (hc : CommonHazardRatio D₀ D₁ Y₀ Y₁ n 1) : logRankNumerator D₀ D₁ Y₀ Y₁ n = 0 := by
  have h := coxScore_log_eq_zero one_pos hm hc
  rwa [Real.log_one, coxScore_zero] at h

end Score

section Masses

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The weighted event mass of arm `a` at period `t`, computed from the observed record `O` and
the time-indexed weights `w`: `∑_{arm = a, X = t, Δ} m w_t`. -/
noncomputable def armEventMass (m : Ω → ℝ) (O : Ω → ℕ × Bool) (arm : Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : Bool) (t : ℕ) : ℝ :=
  wsum m (ev arm a ∩ obsEventSet O t) (w t)

/-- The weighted risk mass of arm `a` at period `t`, computed from the observed record `O` and
the time-indexed weights `w`: `∑_{arm = a, X ≥ t} m w_t`. -/
noncomputable def armRiskMass (m : Ω → ℝ) (O : Ω → ℕ × Bool) (arm : Ω → Bool)
    (w : ℕ → Ω → ℝ) (a : Bool) (t : ℕ) : ℝ :=
  wsum m (ev arm a ∩ obsRiskSet O t) (w t)

/-- The counterfactual event mass of arm `a` at `t`: `P(T = t, arm = a)` for the survival time
without switching `T`. -/
noncomputable def cfEventMass (m : Ω → ℝ) (T : Ω → ℕ) (arm : Ω → Bool) (a : Bool) (t : ℕ) : ℝ :=
  wmass m (univ.filter fun ω => T ω = t ∧ arm ω = a)

/-- The counterfactual risk mass of arm `a` at `t`: `P(T ≥ t, arm = a)`. -/
noncomputable def cfRiskMass (m : Ω → ℝ) (T : Ω → ℕ) (arm : Ω → Bool) (a : Bool) (t : ℕ) : ℝ :=
  wmass m (univ.filter fun ω => t ≤ T ω ∧ arm ω = a)

omit [DecidableEq Ω] in
/-- The counterfactual masses are event masses within risk masses. -/
theorem scoreMasses_cf {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (T : Ω → ℕ) (arm : Ω → Bool) (n : ℕ) :
    ScoreMasses (cfEventMass m T arm false) (cfEventMass m T arm true)
      (cfRiskMass m T arm false) (cfRiskMass m T arm true) n := fun t _ => by
  have hsub : ∀ a : Bool, (univ.filter fun ω => T ω = t ∧ arm ω = a) ⊆
      univ.filter fun ω => t ≤ T ω ∧ arm ω = a := fun a ω hω => by
    simp only [mem_filter, mem_univ, true_and] at hω ⊢; exact ⟨hω.1.ge, hω.2⟩
  exact ⟨wmass_nonneg hm _, wmass_nonneg hm _, wmass_mono hm (hsub false),
    wmass_mono hm (hsub true)⟩

variable {𝒲 𝓛 : Type*} [DecidableEq 𝒲]
  [DecidableEq 𝓛] {T C : Ω → ℕ}

/-- **The weighted arm masses of the observed records are the counterfactual arm masses.** Put
the arm and further baseline adjustment variables `W` in the baseline covariates, as in
`IPCW.weightedHazard_policy_arm` (the censoring time may be the first switch that a policy
forbids, `IPCW.firstForbidden`). Under consistency up to the switch of the observed death time
`Tobs`, no unmeasured confounding of the switch and positivity up to `k`, the event and risk
masses of arm `a` at `k`, weighted by `obsIpcWeight` and computed from the observed records,
are `P(T = k, arm = a)` and `P(T ≥ k, arm = a)`. -/
theorem armMass_obsIpcWeight (p : FiniteDist Ω) (arm : Ω → Bool) (W : Ω → 𝒲)
    (L : ℕ → Ω → 𝓛) {Tobs : Ω → ℕ} (hcons : ConsistentUntilSwitch Tobs T C) (k : ℕ)
    (hnuc : SwitchNUC p T C (fun ω => (arm ω, W ω)) L k)
    (hpos : SwitchPositive p T C (fun ω => (arm ω, W ω)) L k) (a : Bool) :
    armEventMass p (observed Tobs C) arm
        (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) a k =
      cfEventMass p T arm a k ∧
    armRiskMass p (observed Tobs C) arm
        (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) a k =
      cfRiskMass p T arm a k := by
  rw [armEventMass, armRiskMass, observed_eq_of_consistentUntilSwitch hcons,
    obsIpcWeight_observed, obsEventSet_observed, obsRiskSet_observed]
  have hg : ∀ ω ω' : Ω, T ω' = T ω → (arm ω', W ω') = (arm ω, W ω) →
      (fun ω => if arm ω = a then (1 : ℝ) else 0) ω' =
        (fun ω => if arm ω = a then 1 else 0) ω :=
    fun _ _ _ hV => by simp only [(Prod.mk.inj hV).1]
  have hR := wsum_riskSet_ipcWeight p.nonneg k hnuc hpos _ hg
  have hE := wsum_eventSet_ipcWeight p.nonneg k hnuc hpos _ hg
  rw [wsum_filter_indicator (V := arm)] at hR hE
  rw [← wsum_ev_inter (V := arm)] at hR hE
  exact ⟨hE, hR⟩

/-- **The weighted score of the observed records is the counterfactual score.** Under the
hypotheses of `armMass_obsIpcWeight` for the periods before `n - 1`, the Breslow score over the
periods `t < n` of the masses weighted by `obsIpcWeight` and computed from the observed records
equals, at every `β`, the score of the counterfactual arm masses of the survival time without
switching. -/
theorem coxScore_obsIpcWeight (p : FiniteDist Ω) (arm : Ω → Bool) (W : Ω → 𝒲)
    (L : ℕ → Ω → 𝓛) {Tobs : Ω → ℕ} (hcons : ConsistentUntilSwitch Tobs T C) (n : ℕ)
    (hnuc : SwitchNUC p T C (fun ω => (arm ω, W ω)) L (n - 1))
    (hpos : SwitchPositive p T C (fun ω => (arm ω, W ω)) L (n - 1)) (β : ℝ) :
    coxScore
        (armEventMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) false)
        (armEventMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) true)
        (armRiskMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) false)
        (armRiskMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) true) n β =
      coxScore (cfEventMass p T arm false) (cfEventMass p T arm true)
        (cfRiskMass p T arm false) (cfRiskMass p T arm true) n β := by
  refine sum_congr rfl fun t ht => ?_
  have htn : t ≤ n - 1 := by have := mem_range.1 ht; omega
  obtain ⟨e0, r0⟩ := armMass_obsIpcWeight p arm W L hcons t (switchNUC_mono htn hnuc)
    (switchPositive_mono htn hpos) false
  obtain ⟨e1, r1⟩ := armMass_obsIpcWeight p arm W L hcons t (switchNUC_mono htn hnuc)
    (switchPositive_mono htn hpos) true
  rw [e0, r0, e1, r1]

/-- **The weighted score identifies the counterfactual common hazard ratio.** Under the
hypotheses of `coxScore_obsIpcWeight`, if the survival times without switching of the two arms
have a common discrete hazard ratio `r > 0` over the periods `t < n`, and some period has
positive counterfactual risk masses in both arms and positive event mass, the weighted score of
the observed records vanishes exactly at `β = log r`. -/
theorem coxScore_obsIpcWeight_eq_zero_iff (p : FiniteDist Ω) (arm : Ω → Bool) (W : Ω → 𝒲)
    (L : ℕ → Ω → 𝓛) {Tobs : Ω → ℕ} (hcons : ConsistentUntilSwitch Tobs T C) (n : ℕ)
    (hnuc : SwitchNUC p T C (fun ω => (arm ω, W ω)) L (n - 1))
    (hpos : SwitchPositive p T C (fun ω => (arm ω, W ω)) L (n - 1)) {r : ℝ} (hr : 0 < r)
    (hc : CommonHazardRatio (cfEventMass p T arm false) (cfEventMass p T arm true)
      (cfRiskMass p T arm false) (cfRiskMass p T arm true) n r)
    (ht : ∃ t < n, 0 < cfRiskMass p T arm false t ∧ 0 < cfRiskMass p T arm true t ∧
      0 < cfEventMass p T arm false t + cfEventMass p T arm true t) (β : ℝ) :
    coxScore
        (armEventMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) false)
        (armEventMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) true)
        (armRiskMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) false)
        (armRiskMass p (observed Tobs C) arm
          (obsIpcWeight p (observed Tobs C) (fun ω => (arm ω, W ω)) L) true) n β = 0 ↔
      β = Real.log r := by
  rw [coxScore_obsIpcWeight p arm W L hcons n hnuc hpos]
  exact coxScore_eq_zero_iff hr (scoreMasses_cf p.nonneg T arm n) hc ht β

end Masses

namespace Example

/-! ### Censoring at the switch biases the score; weighting corrects it

Eight equally likely individuals `ω = (arm, l, s)`. The covariate `l` is prognostic. In the
control arm (`arm = false`) the survival time without switching is `1` if `l` and `2`
otherwise, and the poor-prognosis individuals with `s` switch at the end of interval `0`. In the
experimental arm nobody switches and the survival time is `1` if `l` and `s`, `2` otherwise.
The counterfactual hazards at time `1` are `1/2` (control) and `1/4` (experimental): common
hazard ratio `1/2`. Censoring the switchers without weights gives the control hazard `1/3` and
the ratio `3/4`. -/

/-- The uniform distribution on the eight individuals. -/
noncomputable def p : FiniteDist (Bool × Bool × Bool) := FiniteDist.uniform

/-- The arm: `true` is experimental, `false` is control. -/
def arm (ω : Bool × Bool × Bool) : Bool := ω.1

/-- No further baseline covariates. -/
def W (_ : Bool × Bool × Bool) : Unit := ()

/-- The survival time without switching. -/
def T (ω : Bool × Bool × Bool) : ℕ :=
  if ω.1 then (if ω.2.1 && ω.2.2 then 1 else 2) else (if ω.2.1 then 1 else 2)

/-- The switching time: `0` for the poor-prognosis control individuals with `s`. -/
def C (ω : Bool × Bool × Bool) : ℕ := if !ω.1 && ω.2.1 && ω.2.2 then 0 else 2

/-- The prognostic covariate, measured at every time. -/
def L (_ : ℕ) (ω : Bool × Bool × Bool) : Bool := ω.2.1

theorem p_pos (ω : Bool × Bool × Bool) : 0 < p ω := by simp [p]

theorem wmass_p (s : Finset (Bool × Bool × Bool)) :
    wmass p s = ∑ ω, if ω ∈ s then (1 / 8 : ℝ) else 0 := by
  rw [wmass, ← sum_filter, filter_mem_eq_inter, univ_inter]
  simp [p]

theorem riskCell_zero (ω : Bool × Bool × Bool) :
    riskCell T C (fun ω => (arm ω, W ω)) L 0 ω =
      univ.filter fun x => x.1 = ω.1 ∧ x.2.1 = ω.2.1 := by
  revert ω; decide

theorem switchNUC : SwitchNUC p T C (fun ω => (arm ω, W ω)) L 1 := by
  intro j hj ω t
  obtain rfl : j = 0 := by omega
  rw [riskCell_zero]
  cases h : ω.1
  · refine meanIndepOn_ev_of_const (fun x hx y hy => ?_) t _
    simp only [mem_filter, mem_univ, true_and] at hx hy
    simp [T, hx.1, hy.1, hx.2, hy.2]
  · refine meanIndepOn_of_const _ (c := 1) fun x hx => ?_
    simp only [mem_filter, mem_univ, true_and] at hx
    simp [C, hx.1]

theorem switchPositive : SwitchPositive p T C (fun ω => (arm ω, W ω)) L 1 := by
  intro j hj ω _ _ _
  obtain rfl : j = 0 := by omega
  rw [stayProb, condProb]
  have hmem : (ω.1, ω.2.1, false) ∈ riskCell T C (fun ω => (arm ω, W ω)) L 0 ω ∩
      uncensored C 1 := by
    rw [riskCell_zero]; simp [uncensored, C]
  have h1 := wmass_pos_of_mem p.nonneg hmem (p_pos _)
  exact div_pos h1 (h1.trans_le (wmass_mono p.nonneg inter_subset_left))

theorem consistent : ConsistentUntilSwitch T T C := fun _ => ⟨fun _ => rfl, id⟩

/-- The counterfactual hazards have the common ratio `1/2` over the periods `0` and `1`. -/
theorem commonHazardRatio_cf :
    CommonHazardRatio (cfEventMass p T arm false) (cfEventMass p T arm true)
      (cfRiskMass p T arm false) (cfRiskMass p T arm true) 2 (1 / 2) := by
  intro t ht _ _
  interval_cases t <;>
    simp only [cfEventMass, cfRiskMass, wmass_p,
      Fintype.sum_prod_type, Fintype.sum_bool, T, arm] <;> norm_num

theorem informative_cf : ∃ t < 2, 0 < cfRiskMass p T arm false t ∧
    0 < cfRiskMass p T arm true t ∧ 0 < cfEventMass p T arm false t + cfEventMass p T arm true t :=
  ⟨1, by norm_num, by
    simp only [cfEventMass, cfRiskMass, wmass_p,
      Fintype.sum_prod_type, Fintype.sum_bool, T, arm]
    norm_num⟩

theorem unweighted_mass (a : Bool) (t : ℕ) :
    armEventMass p (observed T C) arm (fun _ _ => 1) a t = wmass p (ev arm a ∩ eventSet T C t) ∧
      armRiskMass p (observed T C) arm (fun _ _ => 1) a t =
        wmass p (ev arm a ∩ riskSet T C t) := by
  simp only [armEventMass, armRiskMass, obsEventSet_observed, obsRiskSet_observed, wsum_const,
    mul_one, and_self]

/-- The unweighted masses of the censored data are event masses within risk masses. -/
theorem scoreMasses_unweighted (n : ℕ) :
    ScoreMasses (armEventMass p (observed T C) arm (fun _ _ => 1) false)
      (armEventMass p (observed T C) arm (fun _ _ => 1) true)
      (armRiskMass p (observed T C) arm (fun _ _ => 1) false)
      (armRiskMass p (observed T C) arm (fun _ _ => 1) true) n := fun t _ => by
  have hsub : eventSet T C t ⊆ riskSet T C t := fun ω hω => by
    simp only [eventSet, riskSet, mem_filter, mem_univ, true_and] at hω ⊢; omega
  rw [(unweighted_mass false t).1, (unweighted_mass false t).2, (unweighted_mass true t).1,
    (unweighted_mass true t).2]
  exact ⟨wmass_nonneg p.nonneg _, wmass_nonneg p.nonneg _,
    wmass_mono p.nonneg (inter_subset_inter_left hsub),
    wmass_mono p.nonneg (inter_subset_inter_left hsub)⟩

/-- **Censoring at the switch without weights biases the score, weighting corrects it.** In the
example, no unmeasured confounding of the switch and positivity hold given `l`. The score of
the masses weighted by `obsIpcWeight` has the single root `log (1/2)`, the logarithm of the
counterfactual common hazard ratio; the score of the unweighted masses of the data censored at
the switch has the single root `log (3/4)`, a different value. -/
theorem unweighted_root_ne :
    SwitchNUC p T C (fun ω => (arm ω, W ω)) L 1 ∧
      SwitchPositive p T C (fun ω => (arm ω, W ω)) L 1 ∧
      (∀ β, coxScore
        (armEventMass p (observed T C) arm
          (obsIpcWeight p (observed T C) (fun ω => (arm ω, W ω)) L) false)
        (armEventMass p (observed T C) arm
          (obsIpcWeight p (observed T C) (fun ω => (arm ω, W ω)) L) true)
        (armRiskMass p (observed T C) arm
          (obsIpcWeight p (observed T C) (fun ω => (arm ω, W ω)) L) false)
        (armRiskMass p (observed T C) arm
          (obsIpcWeight p (observed T C) (fun ω => (arm ω, W ω)) L) true) 2 β = 0 ↔
        β = Real.log (1 / 2)) ∧
      (∀ β, coxScore (armEventMass p (observed T C) arm (fun _ _ => 1) false)
        (armEventMass p (observed T C) arm (fun _ _ => 1) true)
        (armRiskMass p (observed T C) arm (fun _ _ => 1) false)
        (armRiskMass p (observed T C) arm (fun _ _ => 1) true) 2 β = 0 ↔
        β = Real.log (3 / 4)) ∧
      Real.log (3 / 4) ≠ Real.log (1 / 2) := by
  refine ⟨switchNUC, switchPositive,
    coxScore_obsIpcWeight_eq_zero_iff p arm W L consistent 2 switchNUC switchPositive
      (by norm_num) commonHazardRatio_cf informative_cf, fun β => ?_,
    (Real.log_lt_log (by norm_num) (by norm_num)).ne'⟩
  refine coxScore_eq_zero_iff (by norm_num) (scoreMasses_unweighted 2) (fun t ht _ _ => ?_)
    ⟨1, by norm_num, ?_⟩ β
  · rw [(unweighted_mass false t).1, (unweighted_mass false t).2, (unweighted_mass true t).1,
      (unweighted_mass true t).2]
    interval_cases t <;>
      simp only [wmass_p, mem_inter, mem_ev, eventSet, riskSet, true_and,
        Fintype.sum_prod_type, Fintype.sum_bool, T, C, arm] <;> norm_num
  · rw [(unweighted_mass false 1).1, (unweighted_mass false 1).2, (unweighted_mass true 1).1,
      (unweighted_mass true 1).2]
    simp only [wmass_p, mem_inter, mem_ev, eventSet, riskSet, true_and,
      Fintype.sum_prod_type, Fintype.sum_bool, T, C, arm]
    norm_num

end Example

end WeightedScore

end Survival

end CausalInference
