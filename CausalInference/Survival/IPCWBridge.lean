/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.IPCW
public import CausalInference.Longitudinal.WeightingGeneral
public import CausalInference.MissingData.Weighting
public import CausalInference.Basic.FiniteCondIndep

/-!
# IPCW for switching, the missing data weighting identity and the longitudinal g-formula

Two compatibility results for the inverse probability of censoring weights of
`Survival.IPCW`.

## One period and inverse probability weighting under MAR

For the first switching decision, switching is missingness of the later outcome, and the
one-period weighting identity of `Survival.IPCW` is an instance of the inverse probability
weighting identity `MissingData.ipw_identity` (a measure-theoretic statement with conditional
expectations). The correspondence: covariates `X = (V, L 0, 1{T > 0})` (`baseCov`), response
`R = 1{T = 0 or C ≥ 1}` (`stayResp`; death before switch: an individual who dies in interval
`0` makes no switching decision and its outcome is known), outcome `Y = 1{T > 0} g`
(`laterOutcome`) for `g` a function of `T` and `V`, propensity `P(R | X)` (`stayPropensity`),
which is `stayProb 0` on the survivors of interval `0`.

* `integral_ipw_eq_wsum_riskSet`, `integral_laterOutcome`: `E[1{R} Y / π(X)]` is the IPCW sum
  over the risk set at `1`, and `E[Y]` is the sum over `T ≥ 1`; no assumption is used.
* `ipw_hypotheses`: no unmeasured confounding of the switch and positivity give the hypotheses
  of `MissingData.ipw_identity`: the propensity is a version of `E[1{R} | X]`, `MARMean`, and
  `π(X) > 0` almost surely.
* `wsum_riskSet_one_of_ipw_identity`: the one-period identity
  `∑_{T ≥ 1, C ≥ 1} p W_1 g = ∑_{T ≥ 1} p g` derived from `MissingData.ipw_identity`.

## Any number of periods and the g-formula

Switching is the treatment process of `Longitudinal.WeightingGeneral` (`switchTreat`: not
switched at the end of interval `t`, or dead by then), the covariate at time point `t` is
survival of interval `t` with the baseline and time-varying covariates (`switchCov`), and the
regime is "never switch".

* `histL_switch`, `obsProp_switch`: on the risk set the longitudinal history events and
  treatment probabilities are the risk cells and stay probabilities of `Survival.IPCW`.
* `ipw_switch`: the longitudinal weighted sum `Longitudinal.ipw` is the IPCW sum over the risk
  set, for an outcome that vanishes for those who die before the horizon; no assumption is used.
* `weightedProductLimit_eq_gFormula`: under no unmeasured confounding of the switch and
  positivity up to `k`, and `P(T ≥ k) > 0`, the IPCW product limit at `k` is the g-formula
  `Longitudinal.gFormula` with `k` time points, regime "never switch" and outcome `1{T > k}`;
  `weightedProductLimit_one_eq_gFormula` and `weightedProductLimit_two_eq_gFormula` are one
  and two periods.

## Sources

* J. M. Robins, *A new approach to causal inference in mortality studies with a sustained
  exposure period*, Mathematical Modelling 7 (1986).
* J. M. Robins and D. M. Finkelstein, *Correcting for noncompliance and dependent censoring in
  an AIDS clinical trial with inverse probability of censoring weighted (IPCW) log-rank tests*,
  Biometrics 56 (2000).
* N. R. Latimer and K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival
  time estimates in the presence of treatment switching* (2014): Sec 3.2.1 and Appendix A.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace Survival

namespace IPCWBridge

open IPCW

section GFormula

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒱 𝓛 : Type*} [DecidableEq 𝒱] [DecidableEq 𝓛]

/-- Switching as a treatment process over `K` time points: `switchTreat T C K t ω = true` when
`ω` has not switched at the end of interval `t` (`C ≥ t + 1`) or has died by then (`T ≤ t`;
the dead make no switching decision). The regime "never switch" is the constant path `true`. -/
def switchTreat (T C : Ω → ℕ) (K : ℕ) : Fin K → Ω → Bool :=
  fun t ω => decide ((t : ℕ) + 1 ≤ C ω ∨ T ω ≤ t)

/-- The covariate at time point `t`, measured before the switching decision at the end of
interval `t`: alive after the deaths of interval `t` (`T > t`), the baseline covariates and the
time-varying covariates of interval `t`. -/
def switchCov (T : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛) (K : ℕ) : Fin K → Ω → Bool × 𝒱 × 𝓛 :=
  fun t ω => (decide ((t : ℕ) < T ω), V ω, L t ω)

variable {T C : Ω → ℕ} {V : Ω → 𝒱} {L : ℕ → Ω → 𝓛}

/-- For an individual of the risk set at `K`, the history event at time point `t` of the
longitudinal layer (its own covariate path through `t` and treatment path before `t`) is its
risk cell at `t`. -/
theorem histL_switch {K : ℕ} {ω : Ω} (hω : ω ∈ riskSet T C K) (t : Fin K) :
    histL (switchTreat T C K) (switchCov T V L K) (fun s => switchTreat T C K s ω)
      (fun s => switchCov T V L K s ω) t = riskCell T C V L t ω := by
  obtain ⟨hT, hC⟩ := (mem_filter.1 hω).2
  have hTω : ∀ s : Fin K, (s : ℕ) < T ω := fun s => by have := s.isLt; omega
  have hAω : ∀ s : Fin K, (s : ℕ) + 1 ≤ C ω := fun s => by have := s.isLt; omega
  have ht := t.isLt
  ext x
  simp only [histL, hist, mem_inter, mem_filter, mem_univ, true_and, mem_ev, switchTreat,
    switchCov, Prod.mk.injEq, hTω, hAω, true_or, decide_true, decide_eq_true_eq, mem_riskCell]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨?_, h2, h3⟩, fun i hi => ?_⟩
    · rcases Nat.eq_zero_or_pos (t : ℕ) with h0 | h0
      · omega
      · have hs : ((⟨t - 1, by omega⟩ : Fin K) : ℕ) = t - 1 := rfl
        have := (h1 ⟨t - 1, by omega⟩ (by simp; omega)).2
        omega
    · rcases hi.lt_or_eq with hi | hi
      · exact (h1 ⟨i, by omega⟩ (by simp; omega)).1.2.2
      · subst hi; exact h4
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨fun s hs => ⟨⟨by omega, h3, h4 s (by omega)⟩, Or.inl (by omega)⟩, h2, h3,
      h4 t le_rfl⟩

/-- For an individual of the risk set at `K`, the observed treatment probability at time point
`t` of the longitudinal layer is the stay probability `stayProb t` of `Survival.IPCW`. -/
theorem obsProp_switch (m : Ω → ℝ) {K : ℕ} {ω : Ω} (hω : ω ∈ riskSet T C K) (t : Fin K) :
    obsProp m (switchTreat T C K) (switchCov T V L K) ω t = stayProb m T C V L t ω := by
  have hAω : switchTreat T C K t ω = true := by
    obtain ⟨_, hC⟩ := (mem_filter.1 hω).2
    have := t.isLt
    simp [switchTreat]; omega
  have h : riskCell T C V L t ω ∩ ev (switchTreat T C K t) true =
      riskCell T C V L t ω ∩ uncensored C (t + 1) := by
    ext x
    simp only [mem_inter, mem_ev, switchTreat, decide_eq_true_eq, uncensored, mem_filter,
      mem_univ, true_and]
    constructor
    · rintro ⟨hx, h | h⟩
      · exact ⟨hx, h⟩
      · have := ((mem_riskCell.1 hx).1.2.1); omega
    · rintro ⟨hx, h⟩; exact ⟨hx, Or.inl h⟩
  rw [obsProp, histL_switch hω, hAω, stayProb, condProb, condProb, h]

/-- **The IPCW sum is the longitudinal inverse probability weighted sum.** For an outcome `Y`
that vanishes for those who die before `K` (`T < K`), the longitudinal weighted sum
`ipw m A L (never switch) Y` of `Longitudinal.WeightingGeneral`, with switching as the
treatment process (`switchTreat`) and the histories of `switchCov`, is the weighted sum
`∑_{T ≥ K, C ≥ K} m W_K Y` over the risk set at `K` with the unstabilized weight of
`Survival.IPCW`. This is an identity of finite sums; no assumption is used. -/
theorem ipw_switch (m : Ω → ℝ) (K : ℕ) (Y : Ω → ℝ) (hY : ∀ ω, T ω < K → Y ω = 0) :
    ipw m (switchTreat T C K) (switchCov T V L K) (fun _ => true) Y =
      wsum m (riskSet T C K) fun ω => ipcWeight m T C V L K ω * Y ω := by
  rw [ipw, wsum, wsum, riskSet, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hR : K ≤ T ω ∧ K ≤ C ω
  · have hω : ω ∈ riskSet T C K := by simp [riskSet, hR]
    have hfol : ∀ t : Fin K, switchTreat T C K t ω = true := fun t => by
      have := t.isLt; simp [switchTreat]; omega
    rw [ite_eq_left hR, ite_eq_left hfol, one_mul, Fintype.prod_congr _ _ (obsProp_switch m hω),
      Fin.prod_univ_eq_prod_range (fun t => stayProb m T C V L t ω), ipcWeight, prod_inv_distrib,
      div_eq_mul_inv, mul_comm (Y ω)]
  · rw [ite_eq_right hR]
    by_cases hT : T ω < K
    · rw [hY ω hT]; simp
    · have hC : C ω < K := by omega
      have : ¬ ∀ t : Fin K, switchTreat T C K t ω = true := fun h => by
        have := h ⟨C ω, hC⟩
        simp [switchTreat] at this; omega
      rw [ite_eq_right this]; simp

variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Fintype 𝒱] [Fintype 𝓛]

/-- **The IPCW product limit is the g-formula survival under "never switch".** Under sequential
no unmeasured confounding of the switch and positivity up to time `k`, and `P(T ≥ k) > 0`, the
weighted product limit of `Survival.IPCW` at `k` equals the g-formula `gFormula` of
`Longitudinal.GFormula` with `k` time points, switching as the treatment process
(`switchTreat`), the covariate histories `switchCov` (survival through each interval, the
baseline and the time-varying covariates), the regime "never switch", and the outcome
`1{T > k}`. Both are then the survival `P(T > k)` without switching. The proof goes through
the longitudinal weighted sum (`ipw_switch`) and `Longitudinal.ipw_eq_gFormula`. -/
theorem weightedProductLimit_eq_gFormula (p : FiniteDist Ω) (k : ℕ)
    (hnuc : SwitchNUC p T C V L k) (hpos : SwitchPositive p T C V L k)
    (hk : 0 < atRisk p.toMeasure T k) :
    weightedProductLimit p T C (ipcWeight p T C V L) k =
      gFormula p (switchTreat T C k) (switchCov T V L k) (fun _ => true)
        (fun ω => if k < T ω then 1 else 0) := by
  rw [(weightedProductLimit_ipcWeight p k hnuc hpos hk).2, ← ipw_eq_gFormula,
    ipw_switch p k _ fun ω h => ite_eq_right (by omega),
    wsum_riskSet_ipcWeight p.nonneg k hnuc hpos _ fun ω ω' h _ => by simp only [h],
    survival, toMeasure_real_setOf, wsum, wmass, sum_filter, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs <;> first | omega | simp

/-- The one-period case of `weightedProductLimit_eq_gFormula`: one switching decision (at the
end of interval `0`), and the survival `P(T > 1)`. -/
theorem weightedProductLimit_one_eq_gFormula (p : FiniteDist Ω)
    (hnuc : SwitchNUC p T C V L 1) (hpos : SwitchPositive p T C V L 1)
    (hk : 0 < atRisk p.toMeasure T 1) :
    weightedProductLimit p T C (ipcWeight p T C V L) 1 =
      gFormula p (switchTreat T C 1) (switchCov T V L 1) (fun _ => true)
        (fun ω => if 1 < T ω then 1 else 0) :=
  weightedProductLimit_eq_gFormula p 1 hnuc hpos hk

/-- The two-period case of `weightedProductLimit_eq_gFormula`: two switching decisions, and the
survival `P(T > 2)`. -/
theorem weightedProductLimit_two_eq_gFormula (p : FiniteDist Ω)
    (hnuc : SwitchNUC p T C V L 2) (hpos : SwitchPositive p T C V L 2)
    (hk : 0 < atRisk p.toMeasure T 2) :
    weightedProductLimit p T C (ipcWeight p T C V L) 2 =
      gFormula p (switchTreat T C 2) (switchCov T V L 2) (fun _ => true)
        (fun ω => if 2 < T ω then 1 else 0) :=
  weightedProductLimit_eq_gFormula p 2 hnuc hpos hk

end GFormula

section MissingData

/-! ### One period as an instance of inverse probability weighting under MAR

The correspondence with `MissingData.Weighting`, for the first switching decision (end of
interval `0`):

* covariates `X = (V, L 0, 1{T > 0})` (`baseCov`): the baseline covariates, the covariates of
  interval `0`, and survival of interval `0`, all recorded before the decision;
* response `R = 1{T = 0 or C ≥ 1}` (`stayResp`): the later outcome is known when the individual
  died in interval `0` (death before switch: no decision is made) or did not switch at the end
  of interval `0`;
* outcome `Y = 1{T > 0} g` (`laterOutcome`), for any `g` that depends on `T` and `V`;
* propensity `π(x) = P(R | X = x)` (`stayPropensity`): on survivors of interval `0` it is the
  stay probability `stayProb 0` of `Survival.IPCW`, on those who died it is `1`.

The inverse probability weighted mean `E[1{R} Y / π(X)]` is the IPCW sum over the risk set at
`1` (`integral_ipw_eq_wsum_riskSet`), `E[Y]` is the sum over `T ≥ 1`
(`integral_laterOutcome`), no unmeasured confounding of the switch and positivity give the
hypotheses of `MissingData.ipw_identity` (`ipw_hypotheses`), and the one-period weighting
identity of `Survival.IPCW` follows from `MissingData.ipw_identity`
(`wsum_riskSet_one_of_ipw_identity`). -/

open MeasureTheory MissingData

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {𝒱 𝓛 : Type*} [DecidableEq 𝒱] [DecidableEq 𝓛]

/-- The response indicator: the outcome after interval `0` is known when the individual died in
interval `0` or did not switch at its end. -/
def stayResp (T C : Ω → ℕ) (ω : Ω) : Bool := decide (T ω = 0 ∨ 1 ≤ C ω)

/-- The covariates of the first switching decision: baseline covariates, covariates of interval
`0`, and survival of interval `0`. -/
def baseCov (T : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛) (ω : Ω) : 𝒱 × 𝓛 × Bool :=
  (V ω, L 0 ω, decide (0 < T ω))

/-- The outcome made missing by a switch at the end of interval `0`: `g` for survivors of
interval `0`, and `0` for those who died in it. -/
def laterOutcome (T : Ω → ℕ) (g : Ω → ℝ) (ω : Ω) : ℝ := if 0 < T ω then g ω else 0

/-- The response propensity `P(R | X = x)`. -/
noncomputable def stayPropensity (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛)
    (x : 𝒱 × 𝓛 × Bool) : ℝ :=
  condProb m (univ.filter fun ω => baseCov T V L ω = x) (univ.filter fun ω => stayResp T C ω)

variable {T C : Ω → ℕ} {V : Ω → 𝒱} {L : ℕ → Ω → 𝓛}

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem baseCov_cell {ω : Ω} (hT : 0 < T ω) :
    (univ.filter fun x => baseCov T V L x = baseCov T V L ω) = riskCell T C V L 0 ω := by
  ext x
  simp [baseCov, hT, and_comm, and_left_comm]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- On a survivor of interval `0` the propensity is the stay probability of `Survival.IPCW`. -/
theorem stayPropensity_of_pos (m : Ω → ℝ) {ω : Ω} (hT : 0 < T ω) :
    stayPropensity m T C V L (baseCov T V L ω) = stayProb m T C V L 0 ω := by
  have h : riskCell T C V L 0 ω ∩ (univ.filter fun ω => stayResp T C ω) =
      riskCell T C V L 0 ω ∩ uncensored C 1 := by
    ext x
    simp only [mem_inter, mem_filter, mem_univ, true_and, stayResp, decide_eq_true_eq,
      uncensored]
    exact and_congr_right fun hx => by have := (mem_riskCell.1 hx).1.2.1; omega
  rw [stayPropensity, stayProb, condProb, condProb, baseCov_cell hT, h]

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- On an individual of positive mass who died in interval `0` the propensity is `1`. -/
theorem stayPropensity_of_zero {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) {ω : Ω} (h0 : 0 < m ω)
    (hT : T ω = 0) : stayPropensity m T C V L (baseCov T V L ω) = 1 := by
  have h : (univ.filter fun x => baseCov T V L x = baseCov T V L ω) ∩
      (univ.filter fun ω => stayResp T C ω) =
        univ.filter fun x => baseCov T V L x = baseCov T V L ω := by
    refine inter_eq_left.2 fun x hx => ?_
    simp only [mem_filter, mem_univ, true_and, baseCov, Prod.mk.injEq, hT, lt_self_iff_false,
      decide_false, decide_eq_false_iff_not, not_lt, nonpos_iff_eq_zero] at hx
    simp [stayResp, hx.2.2]
  rw [stayPropensity, condProb, h]
  exact div_self (wmass_pos_of_mem hm (by simp) h0).ne'

omit [DecidableEq Ω] in
/-- An almost sure property under `p.toMeasure` is one that holds at every point of positive
mass. -/
theorem ae_of_forall_pos (p : FiniteDist Ω) {P : Ω → Prop} (h : ∀ ω, 0 < p ω → P ω) :
    ∀ᵐ ω ∂p.toMeasure, P ω := by
  classical
  rw [ae_iff]
  have hs : {ω | ¬ P ω} = ((univ.filter fun ω => ¬ P ω : Finset Ω) : Set Ω) := by ext; simp
  rw [hs, FiniteDist.toMeasure_apply_finset, ENNReal.ofReal_eq_zero, FiniteDist.prob]
  refine sum_nonpos fun ω hω => ?_
  by_contra hpos
  exact (mem_filter.1 hω).2 (h ω (lt_of_not_ge hpos))

omit [DecidableEq Ω] in
theorem integral_toMeasure_eq_sum (p : FiniteDist Ω) (f : Ω → ℝ) :
    ∫ ω, f ω ∂p.toMeasure = ∑ ω, p ω * f ω := by
  rw [FiniteDist.integral_toMeasure]; rfl

/-- **The two weighted functionals coincide.** With the correspondence of this section, the
inverse probability weighted mean `E[1{R} Y / π(X)]` of `MissingData.Weighting` is the IPCW
weighted sum `∑_{T ≥ 1, C ≥ 1} p W_1 g` over the risk set at `1`. No assumption is used. -/
theorem integral_ipw_eq_wsum_riskSet (p : FiniteDist Ω) (g : Ω → ℝ) :
    ∫ ω, respInd (stayResp T C) ω * laterOutcome T g ω /
        stayPropensity p T C V L (baseCov T V L ω) ∂p.toMeasure =
      wsum p (riskSet T C 1) fun ω => ipcWeight p T C V L 1 ω * g ω := by
  rw [integral_toMeasure_eq_sum, wsum, riskSet, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hT : 0 < T ω
  · rw [stayPropensity_of_pos _ hT, respInd_apply, ipcWeight, prod_range_one]
    by_cases hC : 1 ≤ C ω
    · simp [stayResp, laterOutcome, hT, hC, show 1 ≤ T ω by omega, div_eq_inv_mul]
    · simp [stayResp, laterOutcome, hC, show T ω ≠ 0 by omega]
  · simp [laterOutcome, hT, show ¬ 1 ≤ T ω by omega]

omit [DecidableEq Ω] in
/-- The full-data mean of the outcome: `E[Y] = ∑_{T ≥ 1} p g`. -/
theorem integral_laterOutcome (p : FiniteDist Ω) (g : Ω → ℝ) :
    ∫ ω, laterOutcome T g ω ∂p.toMeasure = wsum p (univ.filter fun ω => 1 ≤ T ω) g := by
  rw [integral_toMeasure_eq_sum, wsum, sum_filter]
  exact sum_congr rfl fun ω _ => by simp [laterOutcome, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

/-- The finite conditional probability function of `FiniteCondIndep` for a response event is
the conditional probability of the finite layer. -/
theorem condProbFun_resp {δ : Type*} [DecidableEq δ] [MeasurableSpace δ]
    [DiscreteMeasurableSpace δ] (p : FiniteDist Ω) (Z : Ω → δ) (R : Ω → Bool) (ω : Ω) :
    p.condProbFun Z (R ⁻¹' {true}) ω =
      condProb p (univ.filter fun x => Z x = Z ω) (univ.filter fun x => R x = true) := by
  classical
  simp only [FiniteDist.condProbFun, Function.comp_apply]
  have h1 : R ⁻¹' {true} ∩ Z ⁻¹' {Z ω} = {x | Z x = Z ω ∧ R x = true} := by
    ext; simp [and_comm]
  have h2 : Z ⁻¹' {Z ω} = {x | Z x = Z ω} := rfl
  rw [h1, h2, toMeasure_real_setOf, toMeasure_real_setOf, condProb, filter_and]

omit [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
/-- A function constant on the fibers of a variable `G` with discrete codomain generates a
smaller σ-algebra than `G`. -/
theorem comap_le_comap_of_factor {β δ : Type*} [MeasurableSpace β] [MeasurableSpace δ]
    [DiscreteMeasurableSpace δ] (F : Ω → β) (G : Ω → δ)
    (h : ∀ ω ω', G ω' = G ω → F ω' = F ω) :
    MeasurableSpace.comap F inferInstance ≤ MeasurableSpace.comap G inferInstance := by
  rintro s ⟨S, -, rfl⟩
  refine ⟨{d | ∃ ω, G ω = d ∧ F ω ∈ S}, MeasurableSet.of_discrete, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  exact ⟨fun ⟨ω', h1, h2⟩ => h ω' ω h1.symm ▸ h2, fun hs => ⟨ω, rfl, hs⟩⟩

variable [MeasurableSpace 𝒱] [MeasurableSingletonClass 𝒱] [Countable 𝒱] [MeasurableSpace 𝓛]
  [MeasurableSingletonClass 𝓛] [Countable 𝓛]

/-- **No unmeasured confounding of the switch and positivity give the hypotheses of the IPW
identity.** With the correspondence of this section and `g` depending only on `T` and `V`:
`π(X)` is a version of `E[1{R} | X]`, the outcome is missing at random in the mean-independence
form `MARMean`, and `π(X) > 0` almost surely. -/
theorem ipw_hypotheses (p : FiniteDist Ω) (hnuc : SwitchNUC p T C V L 1)
    (hpos : SwitchPositive p T C V L 1) (g : Ω → ℝ)
    (hg : ∀ ω ω', T ω' = T ω → V ω' = V ω → g ω' = g ω) :
    condExp (MeasurableSpace.comap (baseCov T V L) inferInstance) p.toMeasure
        (respInd (stayResp T C)) =ᵐ[p.toMeasure]
        (fun ω => stayPropensity p T C V L (baseCov T V L ω)) ∧
      MARMean p.toMeasure (baseCov T V L) (laterOutcome T g) (stayResp T C) ∧
      ∀ᵐ ω ∂p.toMeasure, 0 < stayPropensity p T C V L (baseCov T V L ω) := by
  set X := baseCov T V L with hX
  set R := stayResp T C with hR
  set Y := laterOutcome T g with hY
  set π := stayPropensity p T C V L with hπ
  have hprop : condExp (MeasurableSpace.comap X inferInstance) p.toMeasure (respInd R)
      =ᵐ[p.toMeasure] fun ω => π (X ω) := by
    refine (FiniteDist.condExp_indicator_ae_eq p X (R ⁻¹' {true})).trans
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [condProbFun_resp]
    rfl
  have hXT : condExp (MeasurableSpace.comap (fun ω => (X ω, T ω)) inferInstance) p.toMeasure
      (respInd R) =ᵐ[p.toMeasure] fun ω => π (X ω) := by
    refine (FiniteDist.condExp_indicator_ae_eq p (fun ω => (X ω, T ω)) (R ⁻¹' {true})).trans
      (ae_of_forall_pos p fun ω h0 => ?_)
    rw [condProbFun_resp]
    by_cases hT : 0 < T ω
    · change _ = stayPropensity p T C V L (baseCov T V L ω)
      rw [stayPropensity_of_pos _ hT]
      have hcell : (univ.filter fun x => (X x, T x) = (X ω, T ω)) =
          riskCell T C V L 0 ω ∩ ev T (T ω) := by
        rw [← baseCov_cell (C := C) hT]
        ext x; simp [hX, Prod.mk.injEq, and_comm]
      have hstay : riskCell T C V L 0 ω ∩ ev T (T ω) ∩ (univ.filter fun x => R x = true) =
          riskCell T C V L 0 ω ∩ ev T (T ω) ∩ uncensored C 1 := by
        ext x
        simp only [mem_inter, mem_filter, mem_univ, true_and, hR, stayResp, decide_eq_true_eq,
          uncensored]
        exact and_congr_right fun hx => by have := (mem_riskCell.1 hx.1).1.2.1; omega
      have hmass : 0 < wmass p (riskCell T C V L 0 ω ∩ ev T (T ω)) :=
        wmass_pos_of_mem p.nonneg (mem_inter.2 ⟨mem_riskCell_self (Nat.zero_le _) hT,
          mem_ev.2 rfl⟩) h0
      have heq := (meanIndepOn_iff_condMean_eq p.nonneg hmass).1 (hnuc 0 one_pos ω (T ω))
      rw [condMean, condMean, wsum_indicator_uncensored, wsum_indicator_uncensored] at heq
      rw [hcell, condProb, hstay]
      exact heq
    · have hT0 : T ω = 0 := by omega
      change _ = stayPropensity p T C V L (baseCov T V L ω)
      rw [stayPropensity_of_zero p.nonneg h0 hT0]
      have hsub : (univ.filter fun x => (X x, T x) = (X ω, T ω)) ⊆
          univ.filter fun x => R x = true := fun x hx => by
        simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq] at hx
        simp [hR, stayResp, hx.2, hT0]
      rw [condProb, inter_eq_left.2 hsub]
      exact div_self (wmass_pos_of_mem p.nonneg (by simp) h0).ne'
  have hle : MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance ≤
      MeasurableSpace.comap (fun ω => (X ω, T ω)) inferInstance :=
    comap_le_comap_of_factor _ _ fun ω ω' h => by
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      have hV : V ω' = V ω := (Prod.mk.inj h1).1
      simp only [hY, laterOutcome, h1, h2, hg ω ω' h2 hV]
  have hXTm : MeasurableSpace.comap (fun ω => (X ω, T ω)) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) := Measurable.of_discrete.comap_le
  have hmeas : StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (fun ω => π (X ω)) :=
    (measurable_comap_prod (X := X) (Y := Y) (h := fun q => π q.1)
      ((Measurable.of_discrete : Measurable π).comp measurable_fst)).stronglyMeasurable
  refine ⟨hprop, ?_, ae_of_forall_pos p fun ω h0 => ?_⟩
  · refine (condExp_condExp_of_le hle hXTm).symm.trans ?_
    refine (condExp_congr_ae hXT).trans ?_
    rw [condExp_of_stronglyMeasurable (hle.trans hXTm) hmeas Integrable.of_finite]
    exact hprop.symm
  · by_cases hT : 0 < T ω
    · rw [hπ, stayPropensity_of_pos _ hT]
      exact hpos 0 one_pos ω h0 (Nat.zero_le _) hT
    · rw [hπ, stayPropensity_of_zero p.nonneg h0 (by omega)]
      exact one_pos

/-- **The one-period IPCW identity is an instance of the IPW identity under MAR.** Under no
unmeasured confounding of the switch and positivity for the first switching decision, for every
`g` that depends only on `T` and `V`, `MissingData.ipw_identity` applied with the
correspondence of this section gives the one-period weighting identity of `Survival.IPCW`:
`∑_{T ≥ 1, C ≥ 1} p W_1 g = ∑_{T ≥ 1} p g` (the case `k = 1` of
`IPCW.wsum_riskSet_ipcWeight`). -/
theorem wsum_riskSet_one_of_ipw_identity (p : FiniteDist Ω) (hnuc : SwitchNUC p T C V L 1)
    (hpos : SwitchPositive p T C V L 1) (g : Ω → ℝ)
    (hg : ∀ ω ω', T ω' = T ω → V ω' = V ω → g ω' = g ω) :
    wsum p (riskSet T C 1) (fun ω => ipcWeight p T C V L 1 ω * g ω) =
      wsum p (univ.filter fun ω => 1 ≤ T ω) g := by
  obtain ⟨hprop, hmar, hπ⟩ := ipw_hypotheses p hnuc hpos g hg
  rw [← integral_ipw_eq_wsum_riskSet, ← integral_laterOutcome]
  exact ipw_identity Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete hprop hmar hπ Integrable.of_finite

end MissingData

end IPCWBridge

end Survival

end CausalInference
