/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.MultiState
public import CausalInference.Survival.Censoring
public import CausalInference.Survival.Comparison
public import CausalInference.Bias.HazardRatio

/-!
# Treatment effects on progression and post-progression survival

Three causal points of TSD 19 about treatments that act on progression in an illness-death
model.

## The overall survival hazard ratio drifts when treatment acts on progression only

In the discrete-time illness-death model of `Survival/MultiState.lean`, arm `j` has
progression probability `aⱼ` per period, and both arms have the same death probabilities `b`
(progression free) and `c` (progressed): treatment acts on progression only, with an effect
constant in time on that transition.

* `idHazard_lt_of_progression_lt`: if `a₁ < a₀` and `b < c`, the overall survival hazard of
  arm `1` is strictly below that of arm `0` in every period `t ≥ 1`; both equal `b` at
  `t = 0` (`idHazard_zero`).
* `hazardRatio_drift`: the overall survival hazard ratio is `1` at `t = 0`, below `1` at every
  `t ≥ 1`, and converges to `min c (a₁ + b) / min c (a₀ + b)`, which is `1` if and only if
  `c ≤ a₁ + b`. `not_constant_hazardRatio`: no constant hazard ratio describes the two arms.
  `hazardRatio_deathLaw`: these ratios are the library's `hazardRatio` of the laws of the
  death periods (as quotients); `hazardRatio_deathLaw_of_pos`: with `0 < b ≤ c` and
  `a₀ + b < 1` both hazards are conditional probabilities and the reference hazard is
  positive, so the ratio is a genuine hazard ratio.
* `hazardRatio_limit_ne_one`, `hazardRatio_limit_eq_one`: numerical instances on both sides of
  the condition.

## Selection on progression

Patients have a binary prognostic factor `U` (`true`: good prognosis), independent of the
randomized treatment `A`. `F a u` is the probability of progressing within trial follow-up and
`d a u` the probability of death within a fixed time after progression. The naive comparison
of post-progression survival conditions on having progressed, an event affected by treatment.
It is the built-in selection of `Bias/HazardRatio.lean` with the time 1 risk `1 - F` (not
progressed) and the time 2 risk `d`; this file reuses those definitions.

* `ppsDeath_lt_iff`: if each arm has a positive mass of progressors, treatment has no effect
  after progression within either stratum (`d 1 u = d 0 u`) and good prognosis lowers
  post-progression death, the naive comparison shows harm from treatment
  (`ppsDeath 0 < ppsDeath 1`) if and only if `F 1 1 * F 0 0 < F 1 0 * F 0 1`. A stratum may
  have probability zero of progressing.
* `ppsDeath_eq_of_proportional`: if the follow-up probabilities of progression are
  proportional between the arms (`F 1 u = θ * F 0 u`), the progressors of the two arms have
  the same prognosis composition, so under no effect after progression the naive contrast
  between the arms is zero. Each arm can still select on prognosis:
  `example_proportional_selection` has progressor death probability `5/12` in both arms against
  `3/8` among all patients.
* `twoPeriod_cross_lt`, `twoPeriod_ppsDeath_lt`: with two periods of follow-up and per-period
  progression probabilities proportional between the arms, the cross-product condition holds,
  and the naive comparison shows harm.
* `example_ppsDeath`: a numerical instance (post-progression death within the window `31/76`
  untreated, `71/172` treated, and `3/8` in both arms among all eventual progressors, so that
  the naive analysis also underestimates post-progression survival in both arms).
* `example_reversed`: a model in which treatment and good prognosis both lower the
  probability of progression and the naive comparison shows a benefit instead.

## Dependent censoring of post-progression survival

A progressor with progression period `TP ≤ τ` and post-progression survival `V` is followed
after progression until the administrative end of follow-up at calendar period `τ`, so the
post-progression time is censored at `τ - TP` (`ppsObserved`). When `TP` is associated with
`V`, censoring is dependent.

* `ppsRecord`: the full observed record `(TP, min V (τ - TP), 1{V ≤ τ - TP})` of a
  progressor.
* `pps_not_identified`: two laws of `(TP, V)` (`ppsShiftModel` and `ppsIndepModel`), both
  supported on `TP ≤ 3`, with the same law of the full observed record and different
  post-progression survival `81/200` and `81/100`.
* `pps_ppsObserved_law_eq`: the relabelings `ppsDepModel` and `ppsIndepModel` of the models of
  `CensoringExample.survival_not_identified_without_independence` agree on the observed
  post-progression data once `TP` is discarded, but not on the law of `TP`.
* `not_indepFun_ppsDepModel`: in `ppsDepModel`, `V` is not independent of `TP`.
* `pps_support`: every model of this part gives probability zero to `TP > 3`, so the
  administrative censoring time `3 - TP` is exact.
* `lateGood_productLimit_lt_survival`: a model in the direction described by TSD 19 (late
  progressors survive longer after progression, so early progressors are over-represented in
  the tail): the product-limit functional `1/2` underestimates the post-progression survival
  `3/4`, because the observed death rate `1/2` at time `2` exceeds the true hazard `1/4`.
  `not_indepFun_lateGoodModel`: there too `V` is not independent of `TP`.

## Source

NICE Decision Support Unit, Technical Support Document 19, B. Woods, E. Sideris, S. Palmer,
N. Latimer and M. Soares, *Partitioned survival analysis for decision modelling in health care:
a critical review* (2017): Section 4.1.2, Figure 5 (treatment acting by reducing the hazard of
progression `h₁₂`; "the hazard ratio for OS will converge to 1.0"), and Section 4.2.1, issue
(ii) (the selection issue for post-progression survival with "early progressors", and the
dependent administrative censoring of post-progression survival). The document works in
continuous time; this file uses discrete periods.

Corrections. The convergence of the hazard ratio to `1` holds only if `c ≤ a₁ + b` (the
document's sentence is conditional on all patients coming to reside in the progressed state,
which fails otherwise). The selection effect described in Section 4.2.1 does not follow from
"treatment delays progression" and "good prognosis delays progression" alone: it needs the
cross-product condition. It holds with two periods of follow-up and a proportional effect on
the per-period progression probability (`twoPeriod_cross_lt`), fails to be strict with one
period (`ppsDeath_eq_of_proportional`, which gives equal progressor composition in the two
arms, not absence of selection within each arm), and is reversed in `example_reversed`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace CausalInference

namespace Survival

namespace PostProgression

open MultiState

/-! ### Drift of the overall survival hazard ratio -/

section Drift

variable {a₀ a₁ b c : ℝ}

/-- At the start everybody is progression free, so the overall survival hazard is the
progression-free death probability `b`. -/
theorem idHazard_zero (a b c : ℝ) : idHazard a b c 0 = b := by
  rw [illnessDeath_hazard_eq, progFree_zero, progressed_zero]; ring

/-- A larger progression probability gives a larger ratio of progressed to progression-free
patients: `R₁ t ≤ R₀ t` at every `t` when `a₁ ≤ a₀`. -/
theorem progRatio_le_of_le (h1 : 0 ≤ a₁) (h10 : a₁ ≤ a₀) (hab : a₀ + b < 1) (hc : c ≤ 1)
    (t : ℕ) : progRatio a₁ b c t ≤ progRatio a₀ b c t := by
  have hx0 : 0 < 1 - a₀ - b := by linarith
  have hab1 : a₁ + b < 1 := by linarith
  induction t with
  | zero => simp [progRatio, progressed_zero]
  | succ t ih =>
    rw [progRatio_succ hab1, progRatio_succ hab]
    have hR := progRatio_nonneg h1 hab1 hc t
    calc (a₁ + (1 - c) * progRatio a₁ b c t) / (1 - a₁ - b)
        ≤ (a₁ + (1 - c) * progRatio a₁ b c t) / (1 - a₀ - b) :=
          div_le_div_of_nonneg_left (by nlinarith) hx0 (by linarith)
      _ ≤ (a₀ + (1 - c) * progRatio a₀ b c t) / (1 - a₀ - b) :=
          div_le_div_of_nonneg_right (by nlinarith) hx0.le

/-- A strictly larger progression probability gives a strictly larger ratio of progressed to
progression-free patients from period `1` on. -/
theorem progRatio_lt_of_lt (h1 : 0 ≤ a₁) (h10 : a₁ < a₀) (hab : a₀ + b < 1) (hc : c ≤ 1)
    (t : ℕ) : progRatio a₁ b c (t + 1) < progRatio a₀ b c (t + 1) := by
  have hx0 : 0 < 1 - a₀ - b := by linarith
  have hab1 : a₁ + b < 1 := by linarith
  rw [progRatio_succ hab1, progRatio_succ hab]
  have hR := progRatio_nonneg h1 hab1 hc t
  have hle := progRatio_le_of_le h1 h10.le hab hc t
  calc (a₁ + (1 - c) * progRatio a₁ b c t) / (1 - a₁ - b)
      ≤ (a₁ + (1 - c) * progRatio a₁ b c t) / (1 - a₀ - b) :=
        div_le_div_of_nonneg_left (by nlinarith) hx0 (by linarith)
    _ < (a₀ + (1 - c) * progRatio a₀ b c t) / (1 - a₀ - b) := by
        apply div_lt_div_of_pos_right _ hx0
        nlinarith

/-- Treatment acting on progression only (TSD 19, Section 4.1.2): if arm `1` has a smaller
progression probability than arm `0` (`a₁ < a₀`) and death is more likely after progression
(`b < c`), the overall survival hazard of arm `1` is strictly smaller in every period `t ≥ 1`,
although treatment has no effect on either death probability. -/
theorem idHazard_lt_of_progression_lt (h1 : 0 ≤ a₁) (h10 : a₁ < a₀) (hab : a₀ + b < 1)
    (hc : c ≤ 1) (hbc : b < c) (t : ℕ) :
    idHazard a₁ b c (t + 1) < idHazard a₀ b c (t + 1) := by
  have hab1 : a₁ + b < 1 := by linarith
  have h0 : 0 ≤ a₀ := by linarith
  rw [illnessDeath_hazard_eq_ratio h1 hab1 hc, illnessDeath_hazard_eq_ratio h0 hab hc]
  have hR := progRatio_nonneg h1 hab1 hc (t + 1)
  have hlt := progRatio_lt_of_lt h1 h10 hab hc t
  have : (c - b) / (1 + progRatio a₀ b c (t + 1)) < (c - b) / (1 + progRatio a₁ b c (t + 1)) :=
    div_lt_div_of_pos_left (by linarith) (by linarith) (by linarith)
  linarith

/-- The overall survival hazard is at least the progression-free death probability `b` when
`b ≤ c`. -/
theorem le_idHazard (ha : 0 ≤ a₀) (hab : a₀ + b < 1) (hc : c ≤ 1) (hbc : b ≤ c) (t : ℕ) :
    b ≤ idHazard a₀ b c t := by
  rw [illnessDeath_hazard_eq_ratio ha hab hc]
  have hR := progRatio_nonneg ha hab hc t
  have : (c - b) / (1 + progRatio a₀ b c t) ≤ c - b :=
    div_le_self (by linarith) (by linarith)
  linarith

/-- The limit of the overall survival hazard ratio is `1` if and only if `c ≤ a₁ + b`. -/
theorem limit_eq_one_iff (h1 : 0 ≤ a₁) (h10 : a₁ < a₀) (hb : 0 ≤ b) (hbc : b < c) :
    min c (a₁ + b) / min c (a₀ + b) = 1 ↔ c ≤ a₁ + b := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    rw [min_eq_right hlt.le] at h
    have hpos : 0 < min c (a₀ + b) := lt_min (by linarith) (by linarith)
    rw [div_eq_one_iff_eq hpos.ne'] at h
    have : a₁ + b < min c (a₀ + b) := lt_min hlt (by linarith)
    linarith
  · intro h
    rw [min_eq_left h, min_eq_left (by linarith), div_self (by linarith)]

/-- The drift of the overall survival hazard ratio (TSD 19, Section 4.1.2, Figure 5,
discrete-time version, with the condition for the return to `1` added). Treatment lowers the
progression probability (`0 < a₁ < a₀`) and has no effect on the death probabilities `b`
(progression free) and `c` (progressed), with `0 < b < c ≤ 1` and `a₀ + b < 1`. Then the
overall survival hazard ratio `h₁ t / h₀ t` equals `1` at `t = 0`, is strictly below `1` at
every `t ≥ 1`, and converges to `min c (a₁ + b) / min c (a₀ + b)`; this limit is `1` if and
only if `c ≤ a₁ + b`. -/
theorem hazardRatio_drift (h1 : 0 < a₁) (h10 : a₁ < a₀) (hab : a₀ + b < 1) (hc : c ≤ 1)
    (hb : 0 < b) (hbc : b < c) :
    idHazard a₁ b c 0 / idHazard a₀ b c 0 = 1 ∧
      (∀ t, 1 ≤ t → idHazard a₁ b c t / idHazard a₀ b c t < 1) ∧
      Tendsto (fun t => idHazard a₁ b c t / idHazard a₀ b c t) atTop
        (𝓝 (min c (a₁ + b) / min c (a₀ + b))) ∧
      (min c (a₁ + b) / min c (a₀ + b) = 1 ↔ c ≤ a₁ + b) := by
  have hab1 : a₁ + b < 1 := by linarith
  have h0 : 0 < a₀ := by linarith
  refine ⟨by rw [idHazard_zero, idHazard_zero, div_self hb.ne'], fun t ht => ?_, ?_,
    limit_eq_one_iff h1.le h10 hb.le hbc⟩
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
    have hpos : 0 < idHazard a₀ b c (s + 1) :=
      lt_of_lt_of_le hb (le_idHazard h0.le hab hc hbc.le _)
    rw [div_lt_one hpos]
    exact idHazard_lt_of_progression_lt h1.le h10 hab hc hbc s
  · exact (illnessDeath_tendsto_hazard h1 hab1 hc).div (illnessDeath_tendsto_hazard h0 hab hc)
      (lt_min (by linarith) (by linarith)).ne'

/-- No constant hazard ratio: under the hypotheses of `hazardRatio_drift` there is no `θ` with
`h₁ t = θ * h₀ t` for every `t`, so extrapolating a constant overall survival hazard ratio is
not justified by a constant effect on progression. -/
theorem not_constant_hazardRatio (h1 : 0 < a₁) (h10 : a₁ < a₀) (hab : a₀ + b < 1)
    (hc : c ≤ 1) (hb : 0 < b) (hbc : b < c) :
    ¬ ∃ θ : ℝ, ∀ t, idHazard a₁ b c t = θ * idHazard a₀ b c t := by
  rintro ⟨θ, hθ⟩
  have e0 := hθ 0
  rw [idHazard_zero, idHazard_zero] at e0
  have hθ1 : θ = 1 := by
    have := mul_right_cancel₀ hb.ne' (e0.symm.trans (one_mul b).symm)
    exact this
  have := idHazard_lt_of_progression_lt h1.le h10 hab hc hbc 0
  rw [hθ 1, hθ1, one_mul] at this
  exact lt_irrefl _ this

/-- The ratios of `hazardRatio_drift` are the library's `hazardRatio` of the laws of the death
periods of the two arms (truncated at any horizon `N > t`). This is an identity of quotients,
valid also when a hazard is zero; the reading as a ratio of two conditional probabilities with
positive reference hazard is `hazardRatio_deathLaw_of_pos`. -/
theorem hazardRatio_deathLaw (h1 : 0 ≤ a₁) (h10 : a₁ ≤ a₀) (hb : 0 ≤ b) (hab : a₀ + b ≤ 1)
    (hc0 : 0 ≤ c) (hc : c ≤ 1) {N t : ℕ} (ht : t < N) :
    hazardRatio (deathLaw idInit (idTrans a₁ b c) N) id (deathLaw idInit (idTrans a₀ b c) N) id t
      = idHazard a₁ b c t / idHazard a₀ b c t := by
  rw [hazardRatio, (illnessDeath_hazard_deathLaw h1 hb (by linarith) hc0 hc ht).2,
    (illnessDeath_hazard_deathLaw (h1.trans h10) hb hab hc0 hc ht).2]

/-- The ratio reading of `hazardRatio_deathLaw`. With `0 ≤ a₁ ≤ a₀`, `0 < b ≤ c ≤ 1` and
`a₀ + b < 1`, both arms are at risk at every period `t < N` with positive probability, both
hazards of the death period are conditional probabilities equal to `idHazard`, the reference
hazard is positive, and the library's `hazardRatio` is `idHazard a₁ b c t / idHazard a₀ b c t`. -/
theorem hazardRatio_deathLaw_of_pos (h1 : 0 ≤ a₁) (h10 : a₁ ≤ a₀) (hb : 0 < b)
    (hab : a₀ + b < 1) (hbc : b ≤ c) (hc : c ≤ 1) {N t : ℕ} (ht : t < N) :
    0 < atRisk (deathLaw idInit (idTrans a₁ b c) N) id t ∧
      0 < atRisk (deathLaw idInit (idTrans a₀ b c) N) id t ∧
      0 < hazard (deathLaw idInit (idTrans a₀ b c) N) id t ∧
      hazardRatio (deathLaw idInit (idTrans a₁ b c) N) id (deathLaw idInit (idTrans a₀ b c) N)
        id t = idHazard a₁ b c t / idHazard a₀ b c t := by
  have hab1 : a₁ + b < 1 := by linarith
  have h0 : 0 ≤ a₀ := h1.trans h10
  have hc0 : 0 ≤ c := hb.le.trans hbc
  obtain ⟨-, hr1, -, -, -⟩ := illnessDeath_hazard_deathLaw_of_pos h1 hb.le hab1.le hc0 hc ht
    (aliveMass_idTrans_pos h1 hab1 hc t)
  obtain ⟨-, hr0, hH0, -, -⟩ := illnessDeath_hazard_deathLaw_of_pos h0 hb.le hab.le hc0 hc ht
    (aliveMass_idTrans_pos h0 hab hc t)
  refine ⟨hr1, hr0, ?_, hazardRatio_deathLaw h1 h10 hb.le hab.le hc0 hc ht⟩
  rw [hH0]
  exact lt_of_lt_of_le hb (le_idHazard h0 hab hc hbc t)

/-- A model in which the overall survival hazard ratio does not return to `1`: with
`a₁ = 1/10`, `a₀ = 1/5`, `b = 1/10` and `c = 1/2` (so `a₁ + b < c`), the hazard ratio
converges to `2/3`. -/
theorem hazardRatio_limit_ne_one :
    Tendsto (fun t => idHazard (1 / 10) (1 / 10) (1 / 2) t / idHazard (1 / 5) (1 / 10) (1 / 2) t)
      atTop (𝓝 (2 / 3)) := by
  have h := (hazardRatio_drift (a₁ := 1 / 10) (a₀ := 1 / 5) (b := 1 / 10) (c := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2.1
  rwa [show min (1 / 2 : ℝ) (1 / 10 + 1 / 10) / min (1 / 2) (1 / 5 + 1 / 10) = 2 / 3 by
    norm_num] at h

/-- A model in which the overall survival hazard ratio returns to `1`: with `a₁ = 1/5`,
`a₀ = 2/5`, `b = 1/10` and `c = 1/4` (so `c ≤ a₁ + b`), the hazard ratio converges to `1`. -/
theorem hazardRatio_limit_eq_one :
    Tendsto (fun t => idHazard (1 / 5) (1 / 10) (1 / 4) t / idHazard (2 / 5) (1 / 10) (1 / 4) t)
      atTop (𝓝 1) := by
  have h := hazardRatio_drift (a₁ := 1 / 5) (a₀ := 2 / 5) (b := 1 / 10) (c := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hl := h.2.2.1
  rwa [h.2.2.2.2 (by norm_num)] at hl

end Drift

/-! ### Selection on progression -/

section Selection

open Bias.HazardRatio

variable (pA pU : Bool → ℝ) (F d : Bool → Bool → ℝ)

/-- The share of prognosis level `u` among the patients of arm `a` who progressed within
follow-up: `P(U = u | A = a, progressed) = pA a pU u F a u / ∑ u', pA a pU u' F a u'`
(`progressorShare_eq`). It is `frailtyWeight` of `Bias/HazardRatio.lean` with time 1 risk
`1 - F` (not progressed). -/
noncomputable def progressorShare (a u : Bool) : ℝ :=
  frailtyWeight pA pU (fun a u => 1 - F a u) a u

/-- The naive post-progression death probability of arm `a`: the probability of death within
the fixed time after progression among the patients of arm `a` who progressed within
follow-up, `P(death after progression | A = a, progressed)`. It is `hazard2` of
`Bias/HazardRatio.lean` with time 1 risk `1 - F` and time 2 risk `d`. -/
noncomputable def ppsDeath (a : Bool) : ℝ := hazard2 pA pU (fun a u => 1 - F a u) d a

theorem progressorShare_eq (a u : Bool) :
    progressorShare pA pU F a u = pA a * pU u * F a u / ∑ u', pA a * pU u' * F a u' := by
  simp [progressorShare, frailtyWeight, surv1Mass]

/-- The naive post-progression death probability averages the stratum death probabilities
over the prognosis distribution of the progressors, which depends on the arm. -/
theorem ppsDeath_eq_weighted (a : Bool) :
    ppsDeath pA pU F d a = ∑ u, progressorShare pA pU F a u * d a u :=
  hazard2_eq_weighted _ _ _ _ a

variable {pA pU F d}

/-- Selection on progression (TSD 19, Section 4.2.1, issue (ii), first point). Treatment is
randomized (`U` independent of `A`, positive laws), each arm has a positive probability of
progressing within follow-up (`0 < ∑ u, pU u * F a u`; a single stratum may have probability
zero, for example complete prevention of progression in one prognosis group), treatment has no
effect after progression within either prognosis stratum (`d 1 u = d 0 u`) and good prognosis
lowers post-progression death (`d 0 1 < d 0 0`). Then the naive comparison of post-progression
survival shows harm from treatment, `ppsDeath 0 < ppsDeath 1`, if and only if
`F 1 1 * F 0 0 < F 1 0 * F 0 1`: treatment lowers the probability of progressing within
follow-up relatively more for good-prognosis patients, so that the treated progressors
have a worse prognosis mix. -/
theorem ppsDeath_lt_iff (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hF : ∀ a, 0 < ∑ u, pU u * F a u)
    (hnull : ∀ u, d true u = d false u) (hprot : d false true < d false false) :
    ppsDeath pA pU F d false < ppsDeath pA pU F d true ↔
      F true true * F false false < F true false * F false true := by
  have hS : ∀ a, 0 < surv1Mass pA pU (fun a u => 1 - F a u) a := fun a => by
    have h : surv1Mass pA pU (fun a u => 1 - F a u) a = pA a * ∑ u, pU u * F a u := by
      simp only [surv1Mass, sub_sub_cancel, Finset.mul_sum, mul_assoc]
    rw [h]
    exact mul_pos (hA a) (hF a)
  have hd := hazard2_sub_of_noEffect pA pU (fun a u => 1 - F a u) d hnull (hS true).ne'
    (hS false).ne'
  have hw := frailtyWeight_lt_iff pA pU (fun a u => 1 - F a u) hA hU hS
  simp only [sub_sub_cancel] at hw
  rw [← hw]
  unfold ppsDeath
  constructor
  · intro h
    by_contra hge
    push Not at hge
    nlinarith
  · intro h
    nlinarith

/-- Equal progressor composition with proportional follow-up progression probabilities: if
`F 1 u = θ * F 0 u` in both prognosis strata, the progressors of the two arms have the same
prognosis mix, and under no effect after progression the naive contrast between the arms is
zero. With one period of follow-up and a treatment effect that multiplies the per-period
progression probability, this is the case; so "treatment delays progression" does not by
itself produce a biased contrast. It does not say that there is no selection: within each arm
the progressors can still have a different prognosis mix from the whole arm, so that the
post-progression death probability of each arm is biased for that of all patients
(`example_proportional_selection`). -/
theorem ppsDeath_eq_of_proportional (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (hF : ∀ a u, 0 < F a u) (θ : ℝ) (hθ : ∀ u, F true u = θ * F false u)
    (hnull : ∀ u, d true u = d false u) :
    ppsDeath pA pU F d true = ppsDeath pA pU F d false := by
  have hS : ∀ a, 0 < surv1Mass pA pU (fun a u => 1 - F a u) a :=
    surv1Mass_pos pA pU _ hA hU (fun a u => by simpa using hF a u)
  have hd := hazard2_sub_of_noEffect pA pU (fun a u => 1 - F a u) d hnull (hS true).ne'
    (hS false).ne'
  have hθ0 : 0 < θ := by
    have h1 := hF true true
    rw [hθ] at h1
    exact pos_of_mul_pos_left h1 (hF false true).le
  have hw : frailtyWeight pA pU (fun a u => 1 - F a u) true true =
      frailtyWeight pA pU (fun a u => 1 - F a u) false true := by
    have := hA true; have := hA false; have := hU true; have := hU false
    have := hF false true; have := hF false false
    simp only [frailtyWeight, surv1Mass, Fintype.sum_bool, sub_sub_cancel, hθ]
    field_simp
  unfold ppsDeath
  rw [← sub_eq_zero, hd, hw, sub_self, mul_zero]

/-- Two periods of follow-up with proportional per-period progression probabilities give the
selection condition. With per-period progression probabilities `q a u` (no death before
progression), the probability of progressing within two periods is `1 - (1 - q a u) ^ 2`. If
`q 1 u = θ * q 0 u` with `0 < θ < 1` and good prognosis lowers progression
(`0 < q 0 1 < q 0 0 ≤ 1`), then `F 1 1 * F 0 0 < F 1 0 * F 0 1` for
`F a u = 1 - (1 - q a u) ^ 2`. -/
theorem twoPeriod_cross_lt (q : Bool → Bool → ℝ) (θ : ℝ) (hθ : ∀ u, q true u = θ * q false u)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hq0 : 0 < q false true) (hq1 : q false true < q false false) :
    (1 - (1 - q true true) ^ 2) * (1 - (1 - q false false) ^ 2) <
      (1 - (1 - q true false) ^ 2) * (1 - (1 - q false true) ^ 2) := by
  rw [hθ, hθ]
  have key : (1 - (1 - θ * q false true) ^ 2) * (1 - (1 - q false false) ^ 2) -
      (1 - (1 - θ * q false false) ^ 2) * (1 - (1 - q false true) ^ 2) =
      2 * θ * q false true * q false false * (1 - θ) * (q false true - q false false) := by ring
  have : 2 * θ * q false true * q false false * (1 - θ) * (q false true - q false false) < 0 :=
    mul_neg_of_pos_of_neg (by have := hq0.trans hq1; positivity) (by linarith)
  linarith

/-- With two periods of follow-up and per-period progression probabilities proportional between
the arms, the naive comparison of post-progression survival shows harm from a treatment that has
no effect after progression (TSD 19, Section 4.2.1). -/
theorem twoPeriod_ppsDeath_lt (hA : ∀ a, 0 < pA a) (hU : ∀ u, 0 < pU u)
    (q : Bool → Bool → ℝ) (θ : ℝ) (hθ : ∀ u, q true u = θ * q false u) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (hq0 : 0 < q false true) (hq1 : q false true < q false false)
    (hq2 : q false false ≤ 1) (hnull : ∀ u, d true u = d false u)
    (hprot : d false true < d false false) :
    ppsDeath pA pU (fun a u => 1 - (1 - q a u) ^ 2) d false <
      ppsDeath pA pU (fun a u => 1 - (1 - q a u) ^ 2) d true := by
  have hpos : ∀ a u, 0 < 1 - (1 - q a u) ^ 2 := by
    have hq : ∀ u, 0 < q false u ∧ q false u ≤ 1 := fun u => by
      cases u
      · exact ⟨hq0.trans hq1, hq2⟩
      · exact ⟨hq0, hq1.le.trans hq2⟩
    intro a u
    have e : 1 - (1 - q a u) ^ 2 = q a u * (2 - q a u) := by ring
    rw [e]
    obtain ⟨h0, h1⟩ := hq u
    cases a
    · exact mul_pos h0 (by linarith)
    · rw [hθ u]
      exact mul_pos (mul_pos hθ0 h0) (by nlinarith)
  exact (ppsDeath_lt_iff hA hU
    (fun a => Finset.sum_pos (fun u _ => mul_pos (hU u) (hpos a u)) Finset.univ_nonempty)
    hnull hprot).2 (twoPeriod_cross_lt q θ hθ hθ0 hθ1 hq0 hq1)

/-- Per-period progression probabilities of the example: `1/2` untreated with poor prognosis,
`1/4` untreated with good prognosis, and half of these (`θ = 1/2`) under treatment. -/
noncomputable def exQ (a u : Bool) : ℝ :=
  if a then (if u then 1 / 8 else 1 / 4) else (if u then 1 / 4 else 1 / 2)

/-- The probability of progressing within two periods of follow-up in the example. -/
noncomputable def exF (a u : Bool) : ℝ := 1 - (1 - exQ a u) ^ 2

/-- A numerical instance of the selection effect of TSD 19, Section 4.2.1. Fair laws for
treatment and prognosis, the per-period progression probabilities `exQ` (treatment halves
them), two periods of follow-up, and post-progression death probabilities `exR2` (`1/4` with
good prognosis, `1/2` with poor prognosis, in both arms). Among the progressors within
follow-up, the post-progression death probability is `31/76` untreated and `71/172 > 31/76`
treated: the naive comparison shows harm. Since there is no death before progression and every
per-period progression probability is positive, every patient progresses eventually; among all
eventual progressors (`F = 1`) the post-progression death probability is `3/8` in both arms.
So the naive analysis also overstates post-progression death, that is, underestimates
post-progression survival, in both arms ("early progressors"). -/
theorem example_ppsDeath :
    ppsDeath exHalf exHalf exF exR2 false = 31 / 76 ∧
      ppsDeath exHalf exHalf exF exR2 true = 71 / 172 ∧
      (∀ a, ppsDeath exHalf exHalf (fun _ _ => 1) exR2 a = 3 / 8) ∧
      (3 / 8 : ℝ) < 31 / 76 ∧ (31 / 76 : ℝ) < 71 / 172 := by
  refine ⟨?_, ?_, fun a => ?_, by norm_num, by norm_num⟩
  · norm_num [ppsDeath, hazard2, dead2Mass, surv1Mass, exHalf, exF, exQ, exR2, Fintype.sum_bool]
  · norm_num [ppsDeath, hazard2, dead2Mass, surv1Mass, exHalf, exF, exQ, exR2, Fintype.sum_bool]
  · cases a <;>
      norm_num [ppsDeath, hazard2, dead2Mass, surv1Mass, exHalf, exR2, Fintype.sum_bool]

/-- Proportional progression probabilities with selection in both arms. Take fair laws for
treatment and prognosis, follow-up progression probabilities `exQ` (`1/4` with good and `1/2`
with poor prognosis untreated, halved under treatment, so `F 1 u = (1/2) * F 0 u`), and the
post-progression death probabilities `exR2` (`1/4` with good, `1/2` with poor prognosis, in
both arms). The share of good prognosis among the progressors is `1/3` in both arms, against
`1/2` in the whole arm, and the post-progression death probability among progressors is `5/12`
in both arms, against `3/8` among all patients. The naive contrast is zero, but each arm
selects on prognosis. -/
theorem example_proportional_selection :
    (∀ u, exQ true u = 1 / 2 * exQ false u) ∧
      (∀ a, progressorShare exHalf exHalf exQ a true = 1 / 3) ∧
      (∀ a, ppsDeath exHalf exHalf exQ exR2 a = 5 / 12) ∧
      (∀ a, ppsDeath exHalf exHalf (fun _ _ => 1) exR2 a = 3 / 8) ∧ (3 / 8 : ℝ) ≠ 5 / 12 := by
  refine ⟨fun u => ?_, fun a => ?_, fun a => ?_, (example_ppsDeath).2.2.1, by norm_num⟩
  · cases u <;> norm_num [exQ]
  · cases a <;> norm_num [progressorShare_eq, exHalf, exQ, Fintype.sum_bool]
  · cases a <;>
      norm_num [ppsDeath, hazard2, dead2Mass, surv1Mass, exHalf, exQ, exR2, Fintype.sum_bool]

/-- Follow-up progression probabilities of the reversed example: `4/5` untreated with poor
prognosis, `2/5` untreated with good prognosis, `3/10` treated with poor prognosis and `1/4`
treated with good prognosis. -/
noncomputable def exFrev (a u : Bool) : ℝ :=
  if a then (if u then 1 / 4 else 3 / 10) else (if u then 2 / 5 else 4 / 5)

/-- The selection effect can be reversed. In `exFrev` treatment lowers the probability of
progressing within follow-up in both prognosis strata and good prognosis lowers it in both
arms, but treatment lowers it relatively more for poor-prognosis patients. With the
post-progression death probabilities `exR2` (no effect of treatment), the naive
post-progression death probability is `5/12` untreated and `17/44 < 5/12` treated: the naive
comparison now shows a benefit of treatment after progression. -/
theorem example_reversed :
    (∀ u, exFrev true u < exFrev false u) ∧ (∀ a, exFrev a true < exFrev a false) ∧
      ppsDeath exHalf exHalf exFrev exR2 false = 5 / 12 ∧
      ppsDeath exHalf exHalf exFrev exR2 true = 17 / 44 ∧ (17 / 44 : ℝ) < 5 / 12 := by
  refine ⟨fun u => ?_, fun a => ?_, ?_, ?_, by norm_num⟩
  · cases u <;> norm_num [exFrev]
  · cases a <;> norm_num [exFrev]
  · norm_num [ppsDeath, hazard2, dead2Mass, surv1Mass, exHalf, exFrev, exR2, Fintype.sum_bool]
  · norm_num [ppsDeath, hazard2, dead2Mass, surv1Mass, exHalf, exFrev, exR2, Fintype.sum_bool]

end Selection

/-! ### Dependent censoring of post-progression survival -/

section Censoring

open CensoringExample
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The observed post-progression data under administrative end of follow-up at calendar
period `τ`, for a progressor with progression period `TP ≤ τ` and post-progression survival
`V`: the post-progression time is censored at `τ - TP`, so the observed data are
`observed V (τ - TP)` of `Survival/Censoring.lean`. The function is meant only on the event
`TP ≤ τ` of progression within follow-up: there natural-number subtraction is exact. For
`TP > τ` it returns the meaningless record `(0, V = 0)`, so it should be applied only to laws
supported on `TP ≤ τ`. Every model of this section gives probability zero to `TP > 3`
(`pps_support`). -/
def ppsObserved (τ : ℕ) (TP V : Ω → ℕ) : Ω → ℕ × Bool := observed V fun ω => τ - TP ω

/-- The full observed record of a progressor under administrative end of follow-up at
calendar period `τ`: the progression period `TP` together with the observed post-progression
data `(min V (τ - TP), 1{V ≤ τ - TP})`. As for `ppsObserved`, it is meant on `TP ≤ τ`. -/
def ppsRecord (τ : ℕ) (TP V : Ω → ℕ) : Ω → ℕ × (ℕ × Bool) :=
  fun ω => (TP ω, ppsObserved τ TP V ω)

/-- The relabeling from `(TP, V)` to `(T, C) = (V, 3 - TP)`: post-progression survival and its
censoring time under administrative end of follow-up at period `3`. -/
def relabel (q : ℕ × ℕ) : ℕ × ℕ := (q.2, 3 - q.1)

theorem measurable_relabel : Measurable relabel := Measurable.of_discrete

/-- A law of `(TP, V)` with `TP ∈ {1, 2}`, in units of `1/200`: `(2, 1)` with weight `20`,
`(2, 2)` with weight `90`, `(1, 2)` with weight `9` and `(1, 3)` with weight `81`. Its
relabeling is `CensoringExample.depModel`. -/
noncomputable def ppsDepModel : Measure (ℕ × ℕ) :=
  (2 : ℝ≥0∞)⁻¹ • (100 : ℝ≥0∞)⁻¹ • ((20 : ℝ≥0∞) • Measure.dirac (2, 1) +
    (90 : ℝ≥0∞) • Measure.dirac (2, 2) + (9 : ℝ≥0∞) • Measure.dirac (1, 2) +
    (81 : ℝ≥0∞) • Measure.dirac (1, 3))

/-- A law of `(TP, V)` with `TP ∈ {1, 2}` whose relabeling is `CensoringExample.indepModel`:
progression period and post-progression survival are independent. -/
noncomputable def ppsIndepModel : Measure (ℕ × ℕ) :=
  (2 : ℝ≥0∞)⁻¹ • (100 : ℝ≥0∞)⁻¹ • ((10 : ℝ≥0∞) • Measure.dirac (2, 1) +
    (10 : ℝ≥0∞) • Measure.dirac (1, 1) + (9 : ℝ≥0∞) • Measure.dirac (2, 2) +
    (9 : ℝ≥0∞) • Measure.dirac (1, 2) + (81 : ℝ≥0∞) • Measure.dirac (2, 3) +
    (81 : ℝ≥0∞) • Measure.dirac (1, 3))

theorem aemeasurable_relabel (μ : Measure (ℕ × ℕ)) : AEMeasurable relabel μ :=
  measurable_relabel.aemeasurable

theorem map_relabel_ppsDepModel : ppsDepModel.map relabel = depModel := by
  simp [ppsDepModel, depModel, Measure.map_smul, Measure.map_add, Measure.map_dirac',
    measurable_relabel, aemeasurable_relabel, relabel]

theorem map_relabel_ppsIndepModel : ppsIndepModel.map relabel = indepModel := by
  rw [indepModel_eq]
  simp [ppsIndepModel, Measure.map_smul, Measure.map_add, Measure.map_dirac',
    measurable_relabel, aemeasurable_relabel, relabel]

/-- Observed post-progression data and survival transport along the relabeling. -/
theorem map_ppsObserved (ν : Measure (ℕ × ℕ)) :
    ν.map (ppsObserved 3 Prod.fst Prod.snd) =
      (ν.map relabel).map (observed Prod.fst Prod.snd) := by
  rw [Measure.map_map measurable_observed_fst_snd measurable_relabel]
  rfl

theorem real_relabel (ν : Measure (ℕ × ℕ)) (A : Set (ℕ × ℕ)) :
    ν.real (relabel ⁻¹' A) = (ν.map relabel).real A :=
  (map_measureReal_apply measurable_relabel MeasurableSet.of_discrete).symm

/-- A law whose relabeling is a probability measure is a probability measure. -/
theorem isProbabilityMeasure_of_map_relabel (ν : Measure (ℕ × ℕ))
    [IsProbabilityMeasure (ν.map relabel)] :
    IsProbabilityMeasure ν := by
  refine ⟨?_⟩
  have h := Measure.map_apply measurable_relabel (μ := ν) MeasurableSet.univ
  rw [Set.preimage_univ, measure_univ] at h
  exact h.symm

instance : IsProbabilityMeasure ppsDepModel := by
  have : IsProbabilityMeasure (ppsDepModel.map relabel) := by
    rw [map_relabel_ppsDepModel]; infer_instance
  exact isProbabilityMeasure_of_map_relabel _

instance : IsProbabilityMeasure ppsIndepModel := by
  have : IsProbabilityMeasure (ppsIndepModel.map relabel) := by
    rw [map_relabel_ppsIndepModel]; infer_instance
  exact isProbabilityMeasure_of_map_relabel _

/-- The relabelings `ppsDepModel` and `ppsIndepModel` of the models of
`CensoringExample.survival_not_identified_without_independence` give the same law of the
observed post-progression data `(min V (3 - TP), 1{V ≤ 3 - TP})` and different
post-progression survival `P(V > 2) = 81/200` and `81/100`. This is not a non-identification
result for the trial: the recorded progression period distinguishes them, since
`P(TP = 2)` is `11/20` in `ppsDepModel` and `1/2` in `ppsIndepModel`. The non-identification
result on the full record is `pps_not_identified`. -/
theorem pps_ppsObserved_law_eq :
    ppsDepModel.map (ppsObserved 3 Prod.fst Prod.snd) =
        ppsIndepModel.map (ppsObserved 3 Prod.fst Prod.snd) ∧
      survival ppsDepModel Prod.snd 2 = 81 / 200 ∧
      survival ppsIndepModel Prod.snd 2 = 81 / 100 ∧
      ppsDepModel.real {q | q.1 = 2} = 11 / 20 ∧ ppsIndepModel.real {q | q.1 = 2} = 1 / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [map_ppsObserved, map_ppsObserved, map_relabel_ppsDepModel, map_relabel_ppsIndepModel,
      map_observed_depModel]
  · rw [survival, ← depModel_survival_two, survival, ← map_relabel_ppsDepModel, ← real_relabel]
    rfl
  · rw [survival, ← indepModel_survival_two, survival, ← map_relabel_ppsIndepModel,
      ← real_relabel]
    rfl
  all_goals
    simp only [ppsDepModel, ppsIndepModel, measureReal_def]
    simp only [smul_add, add_apply, smul_apply, Set.mem_ofPred_eq, Measure.dirac_apply_of_mem,
      smul_eq_mul, mul_one, Measure.dirac_apply, OfNat.one_ne_ofNat, not_false_eq_true,
      Set.indicator_of_notMem, mul_zero, add_zero, one_div]
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp [ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num

/-- A law of `(TP, V)` obtained from `ppsIndepModel` by moving its mass `81/200` at
`(TP, V) = (2, 3)` to `(2, 2)`. In units of `1/200`: `(2, 1)` and `(1, 1)` with weight `10`,
`(2, 2)` with weight `90`, `(1, 2)` with weight `9` and `(1, 3)` with weight `81`. A late
progressor (`TP = 2`) is censored after one period of post-progression follow-up, so the moved
mass has the same observed record. -/
noncomputable def ppsShiftModel : Measure (ℕ × ℕ) :=
  (2 : ℝ≥0∞)⁻¹ • (100 : ℝ≥0∞)⁻¹ • ((10 : ℝ≥0∞) • Measure.dirac (2, 1) +
    (10 : ℝ≥0∞) • Measure.dirac (1, 1) + (90 : ℝ≥0∞) • Measure.dirac (2, 2) +
    (9 : ℝ≥0∞) • Measure.dirac (1, 2) + (81 : ℝ≥0∞) • Measure.dirac (1, 3))

instance : IsProbabilityMeasure ppsShiftModel := ⟨by
  simp only [ppsShiftModel, smul_apply, add_apply, measure_univ, smul_eq_mul, mul_one]
  norm_num
  rw [← mul_assoc, ← ENNReal.mul_inv (by simp) (by simp)]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

theorem measurable_ppsRecord : Measurable (ppsRecord 3 (Prod.fst : ℕ × ℕ → ℕ) Prod.snd) :=
  Measurable.of_discrete

/-- Post-progression survival is not identified under administrative censoring (TSD 19,
Section 4.2.1, issue (ii), second point). The two laws `ppsShiftModel` and `ppsIndepModel` of
`(TP, V)` give probability zero to progression after the horizon `3`, give the same law of the
full observed record `(TP, min V (3 - TP), 1{V ≤ 3 - TP})` (`ppsRecord`), and have different
post-progression survival `P(V > 2) = 81/200` and `81/100`. -/
theorem pps_not_identified :
    ppsShiftModel.real {q | 3 < q.1} = 0 ∧ ppsIndepModel.real {q | 3 < q.1} = 0 ∧
      ppsShiftModel.map (ppsRecord 3 Prod.fst Prod.snd) =
        ppsIndepModel.map (ppsRecord 3 Prod.fst Prod.snd) ∧
      survival ppsShiftModel Prod.snd 2 = 81 / 200 ∧
      survival ppsIndepModel Prod.snd 2 = 81 / 100 := by
  refine ⟨?_, ?_, ?_, ?_, pps_ppsObserved_law_eq.2.2.1⟩
  · simp [ppsShiftModel, measureReal_def, Measure.dirac_apply, Set.indicator]
  · simp [ppsIndepModel, measureReal_def, Measure.dirac_apply, Set.indicator]
  · simp only [ppsShiftModel, ppsIndepModel,
      Measure.map_smul _ measurable_ppsRecord.aemeasurable,
      Measure.map_add _ _ measurable_ppsRecord, Measure.map_dirac' measurable_ppsRecord]
    have e : ∀ q : ℕ × ℕ, ppsRecord 3 Prod.fst Prod.snd q =
        (q.1, (min q.2 (3 - q.1), decide (q.2 ≤ 3 - q.1))) := fun _ => rfl
    rw [show (90 : ℝ≥0∞) = 9 + 81 by norm_num, add_smul]
    simp only [e, smul_add]
    norm_num
    abel
  · simp [ppsShiftModel, survival, measureReal_def, Measure.dirac_apply, Set.indicator]
    norm_num

/-- In `ppsDepModel` post-progression survival `V` is not independent of the progression
period `TP`: otherwise it would be independent of the censoring time `3 - TP`, and the
product-limit functional of the observed data would equal the post-progression survival
(`productLimit_map_observed_eq_survival`), which fails. So the censoring of post-progression
survival is dependent exactly because time to progression is prognostic. -/
theorem not_indepFun_ppsDepModel : ¬ ProbabilityTheory.IndepFun Prod.snd Prod.fst ppsDepModel := by
  intro h
  have hC : ProbabilityTheory.IndepFun Prod.snd (fun q : ℕ × ℕ => 3 - q.1) ppsDepModel :=
    h.comp (φ := id) (ψ := fun n => 3 - n) measurable_id Measurable.of_discrete
  have hpos : 0 < ppsDepModel.real {q | 2 ≤ q.2 ∧ 2 ≤ 3 - q.1} := by
    rw [show {q : ℕ × ℕ | 2 ≤ q.2 ∧ 2 ≤ 3 - q.1} = relabel ⁻¹' {p | 2 ≤ p.1 ∧ 2 ≤ p.2} from rfl,
      real_relabel, map_relabel_ppsDepModel]
    exact depModel_atRisk_two_pos
  have hkm := productLimit_map_observed_eq_survival measurable_snd Measurable.of_discrete hC 2 hpos
  apply depModel_productLimit_ne_survival
  rw [← map_relabel_ppsDepModel, ← map_ppsObserved]
  refine hkm.trans ?_
  rw [survival, survival, ← real_relabel]
  rfl

/-- A law of `(TP, V)` in the direction described by TSD 19: early progressors (`TP = 1`,
followed for `2` periods after progression) die at post-progression time `2` or `3` with
probability `1/4` each, and late progressors (`TP = 2`, followed for `1` period) have
post-progression survival `3`, with probability `1/2`. Late progressors survive longer after
progression. -/
noncomputable def lateGoodModel : Measure (ℕ × ℕ) :=
  (4 : ℝ≥0∞)⁻¹ • (Measure.dirac (1, 2) + Measure.dirac (1, 3) + (2 : ℝ≥0∞) • Measure.dirac (2, 3))

/-- Dependent censoring in the direction of TSD 19, Section 4.2.1: when late progressors
survive longer after progression, they are censored earlier, early progressors are
over-represented among those still followed in the tail, and the observed death rate
overstates the true one. In `lateGoodModel` the observed death rate at post-progression time
`2` among those at risk and uncensored is `1/2`, the true hazard `P(V = 2 | V ≥ 2)` is `1/4`,
and the product-limit functional of the observed data at time `2` is `1/2`, below the
post-progression survival `P(V > 2) = 3/4`. -/
theorem lateGood_productLimit_lt_survival :
    lateGoodModel.real {q | q.2 = 2 ∧ 2 ≤ 3 - q.1} / lateGoodModel.real {q | 2 ≤ q.2 ∧ 2 ≤ 3 - q.1}
        = 1 / 2 ∧
      hazard lateGoodModel Prod.snd 2 = 1 / 4 ∧
      productLimit (lateGoodModel.map (ppsObserved 3 Prod.fst Prod.snd)) 2 = 1 / 2 ∧
      survival lateGoodModel Prod.snd 2 = 3 / 4 := by
  have hobs : ∀ m, observedHazard (lateGoodModel.map (ppsObserved 3 Prod.fst Prod.snd)) m =
      lateGoodModel.real {q | q.2 = m ∧ m ≤ 3 - q.1} /
        lateGoodModel.real {q | m ≤ q.2 ∧ m ≤ 3 - q.1} :=
    observedHazard_map_observed measurable_snd Measurable.of_discrete
  have h2 : lateGoodModel.real {q | q.2 = 2 ∧ 2 ≤ 3 - q.1} /
      lateGoodModel.real {q | 2 ≤ q.2 ∧ 2 ≤ 3 - q.1} = 1 / 2 := by
    simp [lateGoodModel, measureReal_def, Measure.dirac_apply, Set.indicator,
      ENNReal.toReal_add, ENNReal.toReal_inv]
    norm_num
  refine ⟨h2, ?_, ?_, ?_⟩
  · simp [lateGoodModel, hazard, atRisk, measureReal_def, Measure.dirac_apply, Set.indicator,
      ENNReal.toReal_add, ENNReal.mul_eq_top, ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num
  · simp only [productLimit, Finset.prod_range_succ, Finset.prod_range_zero, hobs, h2]
    simp [lateGoodModel, measureReal_def, Measure.dirac_apply, Set.indicator]
    norm_num
  · simp [lateGoodModel, survival, measureReal_def, Measure.dirac_apply, Set.indicator,
      ENNReal.toReal_add, ENNReal.mul_eq_top, ENNReal.toReal_mul, ENNReal.toReal_inv]
    norm_num

instance : IsProbabilityMeasure lateGoodModel := ⟨by
  simp only [lateGoodModel, smul_apply, add_apply, measure_univ, smul_eq_mul,
    mul_one]
  norm_num
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- In `lateGoodModel` post-progression survival `V` is not independent of the progression
period `TP`: otherwise the product-limit functional would equal the post-progression survival
(`productLimit_map_observed_eq_survival`), while it is `1/2` against `3/4`. -/
theorem not_indepFun_lateGoodModel :
    ¬ ProbabilityTheory.IndepFun Prod.snd Prod.fst lateGoodModel := by
  intro h
  have hC : ProbabilityTheory.IndepFun Prod.snd (fun q : ℕ × ℕ => 3 - q.1) lateGoodModel :=
    h.comp (φ := id) (ψ := fun n => 3 - n) measurable_id Measurable.of_discrete
  have hpos : 0 < lateGoodModel.real {q | 2 ≤ q.2 ∧ 2 ≤ 3 - q.1} := by
    simp [lateGoodModel, measureReal_def, Measure.dirac_apply, Set.indicator,
      ENNReal.toReal_add, ENNReal.toReal_inv]
  have hkm := productLimit_map_observed_eq_survival measurable_snd Measurable.of_discrete hC 2 hpos
  obtain ⟨-, -, h3, h4⟩ := lateGood_productLimit_lt_survival
  have : productLimit (lateGoodModel.map (ppsObserved 3 Prod.fst Prod.snd)) 2 =
      survival lateGoodModel Prod.snd 2 := hkm
  rw [h3, h4] at this
  norm_num at this

/-- Every law of `(TP, V)` of this section gives probability zero to progression after the
horizon `3`, where `ppsObserved` and `ppsRecord` are not meaningful. -/
theorem pps_support :
    ppsDepModel.real {q | 3 < q.1} = 0 ∧ ppsIndepModel.real {q | 3 < q.1} = 0 ∧
      ppsShiftModel.real {q | 3 < q.1} = 0 ∧ lateGoodModel.real {q | 3 < q.1} = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [ppsDepModel, ppsIndepModel, ppsShiftModel, lateGoodModel, measureReal_def,
      Measure.dirac_apply, Set.indicator]

end Censoring

end PostProgression

end Survival

end CausalInference
