/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Survival.Censoring
public import CausalInference.Longitudinal.Basic

/-!
# Inverse probability of censoring weights for survival under treatment switching

In a randomized trial with treatment switching, the switchers are censored at their switching
time and the remaining individuals are weighted by the inverse of their probability of not
having switched, given their baseline and time-varying covariates (inverse probability of
censoring weights, IPCW). This file formalizes the population identities behind the method in
discrete time, over any number of periods: the weighted hazard and the weighted product limit
identify the hazard and the survival function of the survival time without switching.

## Setting

A finite sample space `Ω` with a nonnegative mass function `m` (a `FiniteDist` for the
identification statements), the survival time without switching `T : Ω → ℕ` (an explicit
counterfactual variable), the switching time `C : Ω → ℕ` used as the censoring time, baseline
covariates `V : Ω → 𝒱` and time-varying covariates `L i : Ω → 𝓛` measured at the start of each
interval `i`. The conventions are those of `Survival.Censoring`: an individual is at risk and
uncensored at `k` when `T ≥ k` and `C ≥ k`, and an event at `k` is observed when `T = k ≤ C`.
Every conditional probability is conditioning on an event of the finite space, with the
primitives `wmass`, `wsum`, `condProb` and `MeanIndepOn` of `Longitudinal.Basic`; every theorem
that uses one as a probability carries the positivity hypothesis that makes it genuine.
The marginal conclusions are stated against the measure-theoretic `Survival.hazard`,
`Survival.survival`, `Survival.observedHazard` and `Survival.productLimit` of
`FiniteDist.toMeasure`, through `toMeasure_real_setOf`; the stratum results are stated as
ratios of masses. The conditional expectation lemmas of `MissingData.Weighting` (one and
two periods, a static outcome) are not used: on a concrete countermodel their hypotheses are
conditional expectation identities, which are hard to check, while here they are finite sums.

## Time indexing and Eq A1

`stayProb m T C V L j ω` is `P(C ≥ j + 1 | C ≥ j, T > j, V, L̄_j)` at the history of `ω`: the
probability of not switching at the end of interval `j` among those unswitched through `j` and
alive after `j`. In the notation of Eq A1 of TSD 16 it is the denominator factor
`P[C(j) = 0 | C̄(j - 1) = 0, V, L̄(j), T > j]`, with `C(j) = 0` read as `C ≥ j + 1`. The
weight at time `k` multiplies the factors `j < k`, so Eq A1's `Ŵ(t)` is the weight at
`k = t + 1`, the one that applies to the risk set of interval `t + 1`. The treatment history
`Ā(j - 1)` of Eq A1 is absent: before the switch it is the randomized treatment, as the
document notes ("past treatment history is removed from the model"); the arm can be one of the
baseline covariates `V`.

## Main definitions

* `riskSet`, `eventSet`, `riskCell`, `baselineCell`, `covHist`: the risk set and observed
  events at `k`, and the conditioning events of the denominator and numerator of Eq A1.
* `stayProb`, `stayProbBaseline`: the denominator and numerator factors of Eq A1.
* `ipcWeight`: the unstabilized weight `∏_{j < k} 1 / stayProb j`;
  `stabilizedWeight`: the stabilized weight `∏_{j < k} stayProbBaseline j / stayProb j` of
  Eq A1, with a numerator conditional on the baseline covariates.
* `weightedHazard`, `weightedProductLimit`: the weighted hazard and product limit for any
  time-indexed weights.
* `SwitchNUC`: sequential no unmeasured confounding of the switch (given the observed history,
  not switching is mean independent of the survival time without switching);
  `SwitchPositive`: positivity of not switching;
  `NoInformativeSwitchGivenBaseline`: the time-varying covariates do not affect the hazard of
  switching given the baseline covariates.
* `ConsistentUntilSwitch`: the observed death time agrees with `T` until the switch.
* `truncate c w`: weights truncated at `c`; `finVar`: the variance under a finite distribution.

## Main results

* `wsum_riskSet_ipcWeight`: the weighting identity over `k` periods,
  `∑_{T ≥ k, C ≥ k} m W_k g = ∑_{T ≥ k} m g` for every `g` of `(T, V)`, by induction on `k`
  (`wsum_riskSet_succ` is one period).
* `weightedHazard_ipcWeight`, `weightedProductLimit_ipcWeight`: the weighted hazard at `k` is
  the hazard of `T`, and the weighted product limit is the survival `P(T > k)`
  (TSD 16, Sec 3.2.1: valid IPCW versions of the Kaplan-Meier estimator).
* `weightedHazard_ipcWeight_restrict`: within a stratum of `V` (for instance a randomized arm,
  TSD 24, Sec 4.2.2.1, separate weighting models per arm) the weighted hazard is the stratum
  hazard.
* `weightedHazard_stabilized_restrict`: stabilized weights identify the hazard within strata
  of the baseline covariates of their numerator (TSD 24, Sec 4.2.2).
* `stabilizedWeight_eq_one`: without informative switching given the baseline covariates the
  stabilized weight is `1` (TSD 16, Appendix A).
* `weightedHazard_ipcWeight_eq_observedHazard`, `weightedProductLimit_ipcWeight_eq_productLimit`:
  with no covariates in the weight models IPCW is simple censoring, the product-limit functional
  of the artificially censored data (TSD 16, Sec 4).
* `wsum_truncate_ipcWeight_eq_iff`, `weightedHazard_truncate_of_le`, `finVar_min_le`:
  truncation keeps the weighting identity exactly when no weight of positive mass exceeds the
  cap, leaves the hazard unchanged when no weight is capped, and does not increase the variance
  of the weights (TSD 24, Sec 4.2.2.1).
* `observed_eq_of_consistentUntilSwitch`: censoring switchers gives the artificially censored
  data of `T`.

Several types of switching are covered by taking `C` as the first switching time (one
censoring process), and arm-specific weighting models by taking the arm in `V`.

## Countermodels (namespace `Example`)

Four equally likely individuals; a prognostic covariate drives both death and switching.

* `censoring_switchers_biased`: the product limit of the censored data is `2/3`, the IPCW
  product limit and the survival are `1/2`.
* `ipcw_without_confounder`: without the covariate in the weight model, positivity holds, no
  unmeasured confounding fails, and the IPCW hazard is the naive `1/3` instead of `1/2`.
* `pooled_stabilized_ne`: all assumptions hold, but the stabilized weighted hazard of the pooled
  population, with the prognostic variable in the numerator, is `1/3`, not the marginal `1/2`.
* `truncation_biased`: truncating the weights at `1` loses mass and gives `1/3`.
* `not_identified_without_positivity`: if a covariate level always switches, two survival times
  with the same observed data and different hazards both satisfy no unmeasured confounding.

A two-period version (namespace `Example₂`), where the confounder is revealed at time `1` and
the weight at time `2` has two factors:

* `two_period_ipcw`: the naive hazard at time `2` is `1/3`, the IPCW hazard is `1/2`.
* `numerator_with_time_varying_confounder`: a numerator conditional on the time-varying
  confounder makes the stabilized weights `1`, and the weighted hazard is the naive `1/3`.

The efficiency of stabilized weights (TSD 16, Appendix A, citing Robins and Finkelstein) and the
effect of truncation on the standard errors of estimated effects are sampling statements and
are not formalized.

## Sources

* N. R. Latimer and K. R. Abrams, *NICE DSU Technical Support Document 16: Adjusting survival
  time estimates in the presence of treatment switching* (2014): Sec 3.2.1, Sec 4, Appendix A
  (IPCW, Eq A1).
* H. Bell Gorrod, N. R. Latimer and K. R. Abrams, *NICE DSU Technical Support Document 24:
  Adjusting survival time estimates in the presence of treatment switching: an update to
  TSD 16* (2024): Sec 4.2.2 and Sec 4.2.2.1.
-/

@[expose] public section

open Finset CausalInference.Longitudinal

namespace CausalInference

namespace Survival

namespace IPCW

section Consistency

variable {Ω : Type*}

/-- Consistency up to the switch: the observed death time `Tobs` agrees with the survival time
without switching `T` for individuals who die before or at their switching time `C`, and
individuals who switch before their death under no switching are still alive at the switch.
Only the outcome after the switch is affected by switching. -/
def ConsistentUntilSwitch (Tobs T C : Ω → ℕ) : Prop :=
  ∀ ω, (T ω ≤ C ω → Tobs ω = T ω) ∧ (C ω < T ω → C ω < Tobs ω)

/-- Under consistency up to the switch, censoring the switchers at their switching time turns
the observed data into the artificially censored data `(min T C, 1{T ≤ C})` of the survival
time without switching: `observed Tobs C = observed T C`. This is why the counterfactual
survival time `T` is the target of every result below. -/
theorem observed_eq_of_consistentUntilSwitch {Tobs T C : Ω → ℕ}
    (h : ConsistentUntilSwitch Tobs T C) : observed Tobs C = observed T C := by
  funext ω
  obtain ⟨h1, h2⟩ := h ω
  by_cases hTC : T ω ≤ C ω
  · rw [observed, observed, h1 hTC]
  · have := h2 (by omega)
    simp only [observed, Prod.mk.injEq]
    exact ⟨by omega, decide_eq_decide.2 ⟨fun _ => by omega, fun _ => by omega⟩⟩

end Consistency

section Defs

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒱 𝓛 : Type*} [DecidableEq 𝒱] [DecidableEq 𝓛]

/-- The event of being uncensored (not yet switched) through interval `j`: `C ≥ j`. -/
def uncensored (C : Ω → ℕ) (j : ℕ) : Finset Ω := univ.filter fun ω => j ≤ C ω

/-- The risk set at time `k`: alive at the start of interval `k` and uncensored through it,
`T ≥ k` and `C ≥ k`. -/
def riskSet (T C : Ω → ℕ) (k : ℕ) : Finset Ω := univ.filter fun ω => k ≤ T ω ∧ k ≤ C ω

/-- The observed events at time `k`: `T = k ≤ C`. -/
def eventSet (T C : Ω → ℕ) (k : ℕ) : Finset Ω := univ.filter fun ω => T ω = k ∧ k ≤ C ω

/-- The baseline cell of `ω` at time `j`: the individuals uncensored through interval `j`
(`C ≥ j`), alive at the end of interval `j` (`T > j`), with the baseline covariates of `ω`. -/
def baselineCell (T C : Ω → ℕ) (V : Ω → 𝒱) (j : ℕ) (ω : Ω) : Finset Ω :=
  univ.filter fun ω' => j ≤ C ω' ∧ j < T ω' ∧ V ω' = V ω

/-- The covariate history event of `ω` through time `j`: `L i = L i ω` for every `i ≤ j`. -/
def covHist (L : ℕ → Ω → 𝓛) (j : ℕ) (ω : Ω) : Finset Ω :=
  univ.filter fun ω' => ∀ i ≤ j, L i ω' = L i ω

/-- The risk cell of `ω` at time `j`: its baseline cell intersected with its covariate history
event through `j`. This is the conditioning event of the denominator of Eq A1. -/
def riskCell (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛) (j : ℕ) (ω : Ω) : Finset Ω :=
  baselineCell T C V j ω ∩ covHist L j ω

/-- The probability of remaining uncensored at the end of interval `j` given the risk cell of
`ω`: `P(C ≥ j + 1 | C ≥ j, T > j, V = V ω, L̄_j = L̄_j ω)`, a factor of the denominator of
Eq A1. It is a conditional probability when the risk cell has positive mass. -/
noncomputable def stayProb (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛) (j : ℕ)
    (ω : Ω) : ℝ :=
  condProb m (riskCell T C V L j ω) (uncensored C (j + 1))

/-- The probability of remaining uncensored at the end of interval `j` given the baseline cell
of `ω`: `P(C ≥ j + 1 | C ≥ j, T > j, V = V ω)`, a factor of the numerator of Eq A1. -/
noncomputable def stayProbBaseline (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (j : ℕ) (ω : Ω) : ℝ :=
  condProb m (baselineCell T C V j ω) (uncensored C (j + 1))

/-- The unstabilized inverse probability of censoring weight at time `k`:
`∏_{j < k} 1 / P(C ≥ j + 1 | C ≥ j, T > j, V, L̄_j)`, evaluated at the history of `ω`. -/
noncomputable def ipcWeight (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛) (k : ℕ)
    (ω : Ω) : ℝ :=
  ∏ j ∈ range k, (stayProb m T C V L j ω)⁻¹

/-- The stabilized inverse probability of censoring weight at time `k` (Eq A1):
`∏_{j < k} P(C ≥ j + 1 | C ≥ j, T > j, V) / P(C ≥ j + 1 | C ≥ j, T > j, V, L̄_j)`. -/
noncomputable def stabilizedWeight (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛)
    (k : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ range k, stayProbBaseline m T C V j ω / stayProb m T C V L j ω

/-- The weighted hazard at time `k` with the time-indexed weights `w`: the weighted mass of the
observed events at `k` over the weighted mass of the risk set at `k`,
`∑_{T = k ≤ C} m w_k / ∑_{T ≥ k, C ≥ k} m w_k`. -/
noncomputable def weightedHazard (m : Ω → ℝ) (T C : Ω → ℕ) (w : ℕ → Ω → ℝ) (k : ℕ) : ℝ :=
  wsum m (eventSet T C k) (w k) / wsum m (riskSet T C k) (w k)

/-- The weighted product limit at time `k`: `∏_{i ≤ k} (1 - weightedHazard i)`. -/
noncomputable def weightedProductLimit (m : Ω → ℝ) (T C : Ω → ℕ) (w : ℕ → Ω → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ range (k + 1), (1 - weightedHazard m T C w i)

/-- Sequential no unmeasured confounding of the switch up to time `k`: for every `j < k`, within
every risk cell at `j`, remaining uncensored at the end of interval `j` is mean independent of
each event `T = t` of the potential survival time without switching. In words: given the
observed history, the hazard of switching does not depend on prognosis. (For `t ≤ j` the
condition is empty, since `T > j` on the risk cell.) -/
def SwitchNUC (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛) (k : ℕ) : Prop :=
  ∀ j < k, ∀ (ω : Ω) (t : ℕ), MeanIndepOn m (riskCell T C V L j ω) (ev T t)
    (fun ω' => if j + 1 ≤ C ω' then 1 else 0)

/-- Positivity of remaining unswitched up to time `k`: for every `j < k` and every individual of
positive mass in the risk population at `j` (`C ≥ j`, `T > j`), the probability of remaining
uncensored given its risk cell is positive. No covariate history makes switching certain. -/
def SwitchPositive (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛) (k : ℕ) : Prop :=
  ∀ j < k, ∀ ω, 0 < m ω → j ≤ C ω → j < T ω → 0 < stayProb m T C V L j ω

end Defs

section Lemmas

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒱 𝓛 : Type*} [DecidableEq 𝒱] [DecidableEq 𝓛]
  {m : Ω → ℝ} {T C : Ω → ℕ} {V : Ω → 𝒱} {L : ℕ → Ω → 𝓛}

@[simp] theorem mem_riskCell {j : ℕ} {ω ω' : Ω} :
    ω' ∈ riskCell T C V L j ω ↔
      (j ≤ C ω' ∧ j < T ω' ∧ V ω' = V ω) ∧ ∀ i ≤ j, L i ω' = L i ω := by
  simp [riskCell, baselineCell, covHist]

theorem mem_riskCell_self {j : ℕ} {ω : Ω} (hC : j ≤ C ω) (hT : j < T ω) :
    ω ∈ riskCell T C V L j ω := by
  simp [hC, hT]

/-- A weighted sum of an indicator is the mass of the intersection. -/
theorem wsum_indicator_uncensored (s : Finset Ω) (j : ℕ) :
    wsum m s (fun ω => if j ≤ C ω then 1 else 0) = wmass m (s ∩ uncensored C j) := by
  simp [wsum, wmass, uncensored, Finset.sum_filter, ← Finset.filter_mem_eq_inter]

omit [Fintype Ω] [DecidableEq Ω] in
/-- The tower property for a finite partition: if `u` is constant on the classes of `κ` within
`R`, then `∑_{R} m f u = ∑_{R} m E[f | class] u`. -/
theorem wsum_mul_eq_wsum_condMean_mul {β : Type*} [DecidableEq β] (hm : ∀ ω, 0 ≤ m ω)
    (R : Finset Ω) (κ : Ω → β) (f u : Ω → ℝ)
    (hu : ∀ ω ∈ R, ∀ ω' ∈ R, κ ω' = κ ω → u ω' = u ω) :
    wsum m R (fun ω => f ω * u ω) =
      wsum m R (fun ω => condMean m (R.filter fun ω' => κ ω' = κ ω) f * u ω) := by
  unfold wsum
  rw [← sum_fiberwise_of_maps_to (g := κ) (t := R.image κ) (fun ω hω => mem_image_of_mem κ hω),
    ← sum_fiberwise_of_maps_to (g := κ) (t := R.image κ) (fun ω hω => mem_image_of_mem κ hω)]
  refine sum_congr rfl fun b _ => ?_
  set F := R.filter fun ω => κ ω = b with hF
  rcases F.eq_empty_or_nonempty with hE | ⟨ω₀, hω₀⟩
  · rw [hE]; simp
  have hω₀' := mem_filter.1 hω₀
  have hconst : ∀ ω ∈ F, u ω = u ω₀ := fun ω hω => by
    have h := mem_filter.1 hω
    exact hu ω₀ hω₀'.1 ω h.1 (h.2.trans hω₀'.2.symm)
  have hcls : ∀ ω ∈ F, (R.filter fun ω' => κ ω' = κ ω) = F := fun ω hω => by
    rw [hF, (mem_filter.1 hω).2]
  calc ∑ ω ∈ F, m ω * (f ω * u ω) = (∑ ω ∈ F, m ω * f ω) * u ω₀ := by
        rw [sum_mul]; exact sum_congr rfl fun ω hω => by rw [hconst ω hω]; ring
    _ = (wmass m F * condMean m F f) * u ω₀ := by
        congr 1
        by_cases h0 : wmass m F = 0
        · rw [h0, zero_mul]; exact wsum_eq_zero_of_wmass_eq_zero hm h0 f
        · exact (wmass_mul_condMean h0 f).symm
    _ = ∑ ω ∈ F, m ω * (condMean m (R.filter fun ω' => κ ω' = κ ω) f * u ω) := by
        rw [wmass, sum_mul, sum_mul]
        exact sum_congr rfl fun ω hω => by rw [hcls ω hω, hconst ω hω]; ring

theorem riskCell_congr {j : ℕ} {ω ω' : Ω} (hV : V ω' = V ω) (hL : ∀ i ≤ j, L i ω' = L i ω) :
    riskCell T C V L j ω' = riskCell T C V L j ω := by
  ext x; simp only [mem_riskCell, hV]
  exact and_congr_right fun _ => forall₂_congr fun i hi => by rw [hL i hi]

theorem stayProb_congr {j : ℕ} {ω ω' : Ω} (hV : V ω' = V ω) (hL : ∀ i ≤ j, L i ω' = L i ω) :
    stayProb m T C V L j ω' = stayProb m T C V L j ω := by
  rw [stayProb, stayProb, riskCell_congr hV hL]

/-- One period of the weighting argument. Let `u` depend only on `T`, `V` and `L̄_k`. Under no
unmeasured confounding of the switch and positivity at time `k`, weighting the individuals
still uncensored at the end of interval `k` by `1 / P(C ≥ k + 1 | risk cell)` restores the
individuals alive after `k` and uncensored through `k`:
`∑_{T ≥ k + 1, C ≥ k + 1} m u / π_k = ∑_{T > k, C ≥ k} m u`. -/
theorem wsum_riskSet_succ (hm : ∀ ω, 0 ≤ m ω) (k : ℕ)
    (hnuc : ∀ (ω : Ω) (t : ℕ), MeanIndepOn m (riskCell T C V L k ω) (ev T t)
      (fun ω' => if k + 1 ≤ C ω' then 1 else 0))
    (hpos : ∀ ω, 0 < m ω → k ≤ C ω → k < T ω → 0 < stayProb m T C V L k ω)
    (u : Ω → ℝ) (hu : ∀ ω ω', T ω' = T ω → V ω' = V ω → (∀ i ≤ k, L i ω' = L i ω) →
      u ω' = u ω) :
    wsum m (riskSet T C (k + 1)) (fun ω => (stayProb m T C V L k ω)⁻¹ * u ω) =
      wsum m (univ.filter fun ω => k < T ω ∧ k ≤ C ω) u := by
  set R := univ.filter fun ω => k < T ω ∧ k ≤ C ω with hR
  set f : Ω → ℝ := fun ω' => if k + 1 ≤ C ω' then 1 else 0 with hf
  have hL : wsum m (riskSet T C (k + 1)) (fun ω => (stayProb m T C V L k ω)⁻¹ * u ω) =
      wsum m R (fun ω => f ω * ((stayProb m T C V L k ω)⁻¹ * u ω)) := by
    simp only [wsum, riskSet, hR, hf, sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    split_ifs <;> first | omega | simp
  rw [hL, wsum_mul_eq_wsum_condMean_mul hm R (fun ω => (T ω, V ω, fun i : Fin (k + 1) => L i ω))]
  · refine sum_congr rfl fun ω hω => ?_
    obtain ⟨hTω, hCω⟩ := (mem_filter.1 hω).2
    rcases (hm ω).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, zero_mul]
    have hcls : (R.filter fun ω' => (T ω', V ω', fun i : Fin (k + 1) => L i ω') =
        (T ω, V ω, fun i : Fin (k + 1) => L i ω)) = riskCell T C V L k ω ∩ ev T (T ω) := by
      ext x
      simp only [hR, mem_filter, mem_univ, true_and, Prod.mk.injEq, funext_iff, Fin.forall_iff,
        mem_inter, mem_riskCell, mem_ev, Nat.lt_succ_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩; exact ⟨⟨⟨h2, h1, h4⟩, h5⟩, h3⟩
      · rintro ⟨⟨⟨h2, h1, h4⟩, h5⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3, h4, h5⟩
    have hmem : ω ∈ riskCell T C V L k ω ∩ ev T (T ω) :=
      mem_inter.2 ⟨mem_riskCell_self hCω hTω, mem_ev.2 rfl⟩
    have hmass : 0 < wmass m (riskCell T C V L k ω ∩ ev T (T ω)) :=
      h0.trans_le (single_le_sum (fun x _ => hm x) hmem)
    have hcell : 0 < wmass m (riskCell T C V L k ω) :=
      hmass.trans_le (wmass_mono hm inter_subset_left)
    have hπ : condMean m (riskCell T C V L k ω ∩ ev T (T ω)) f = stayProb m T C V L k ω := by
      rw [(meanIndepOn_iff_condMean_eq hm hmass).1 (hnuc ω (T ω)), condMean,
        wsum_indicator_uncensored, stayProb, condProb]
    have hne := (hpos ω h0 hCω hTω).ne'
    dsimp only
    rw [hcls, hπ]
    field_simp
  · intro ω hω ω' hω' hκ
    simp only [Prod.mk.injEq, funext_iff, Fin.forall_iff, Nat.lt_succ_iff] at hκ
    obtain ⟨hT, hV, hLk⟩ := hκ
    rw [stayProb_congr hV hLk, hu ω ω' hT hV hLk]

theorem ipcWeight_congr {k : ℕ} {ω ω' : Ω} (hV : V ω' = V ω) (hL : ∀ i ≤ k, L i ω' = L i ω) :
    ipcWeight m T C V L k ω' = ipcWeight m T C V L k ω :=
  prod_congr rfl fun j hj => by
    rw [stayProb_congr hV fun i hi => hL i (hi.trans (mem_range.1 hj).le)]

theorem switchNUC_mono {k k' : ℕ} (h : k' ≤ k) (hnuc : SwitchNUC m T C V L k) :
    SwitchNUC m T C V L k' := fun j hj => hnuc j (hj.trans_le h)

theorem switchPositive_mono {k k' : ℕ} (h : k' ≤ k) (hpos : SwitchPositive m T C V L k) :
    SwitchPositive m T C V L k' := fun j hj => hpos j (hj.trans_le h)

/-- **The inverse probability of censoring weighting identity over `k` periods.** Under
sequential no unmeasured confounding of the switch and positivity up to time `k`, for every
`g` that depends only on the potential survival time `T` and the baseline covariates `V`, the
weighted sum of `g` over the risk set at `k` (alive and unswitched at the start of interval
`k`) equals the sum of `g` over everyone alive at the start of interval `k`:
`∑_{T ≥ k, C ≥ k} m W_k g = ∑_{T ≥ k} m g`, with `W_k` the unstabilized weight. The proof is
by induction on `k`, one period at a time (`wsum_riskSet_succ`). -/
theorem wsum_riskSet_ipcWeight (hm : ∀ ω, 0 ≤ m ω) : ∀ (k : ℕ),
    SwitchNUC m T C V L k → SwitchPositive m T C V L k →
    ∀ g : Ω → ℝ, (∀ ω ω', T ω' = T ω → V ω' = V ω → g ω' = g ω) →
    wsum m (riskSet T C k) (fun ω => ipcWeight m T C V L k ω * g ω) =
      wsum m (univ.filter fun ω => k ≤ T ω) g
  | 0, _, _, g, _ => by simp [riskSet, ipcWeight, wsum]
  | k + 1, hnuc, hpos, g, hg => by
    have hstep := wsum_riskSet_succ (m := m) (T := T) (C := C) (V := V) (L := L) hm k
      (hnuc k (Nat.lt_succ_self k)) (hpos k (Nat.lt_succ_self k))
      (fun ω => ipcWeight m T C V L k ω * g ω)
      (fun ω ω' hT hV hL => by rw [ipcWeight_congr hV hL, hg ω ω' hT hV])
    have ih := wsum_riskSet_ipcWeight hm k (switchNUC_mono k.le_succ hnuc)
      (switchPositive_mono k.le_succ hpos) (fun ω => if k + 1 ≤ T ω then g ω else 0)
      (fun ω ω' hT hV => by rw [hT, hg ω ω' hT hV])
    have e1 : wsum m (riskSet T C (k + 1)) (fun ω => ipcWeight m T C V L (k + 1) ω * g ω) =
        wsum m (riskSet T C (k + 1))
          (fun ω => (stayProb m T C V L k ω)⁻¹ * (ipcWeight m T C V L k ω * g ω)) :=
      sum_congr rfl fun ω _ => by simp only [ipcWeight, prod_range_succ]; ring
    have e2 : wsum m (univ.filter fun ω => k < T ω ∧ k ≤ C ω)
        (fun ω => ipcWeight m T C V L k ω * g ω) = wsum m (riskSet T C k)
          (fun ω => ipcWeight m T C V L k ω * if k + 1 ≤ T ω then g ω else 0) := by
      simp only [wsum, riskSet, sum_filter]
      refine sum_congr rfl fun ω _ => ?_
      split_ifs <;> first | omega | simp
    have e3 : wsum m (univ.filter fun ω => k ≤ T ω) (fun ω => if k + 1 ≤ T ω then g ω else 0) =
        wsum m (univ.filter fun ω => k + 1 ≤ T ω) g := by
      simp only [wsum, sum_filter]
      refine sum_congr rfl fun ω _ => ?_
      split_ifs <;> first | omega | simp
    rw [e1, hstep, e2, ih, e3]

/-- The weighted sum of the observed events at `k`: under the hypotheses of
`wsum_riskSet_ipcWeight`, `∑_{T = k ≤ C} m W_k g = ∑_{T = k} m g`. -/
theorem wsum_eventSet_ipcWeight (hm : ∀ ω, 0 ≤ m ω) (k : ℕ) (hnuc : SwitchNUC m T C V L k)
    (hpos : SwitchPositive m T C V L k) (g : Ω → ℝ)
    (hg : ∀ ω ω', T ω' = T ω → V ω' = V ω → g ω' = g ω) :
    wsum m (eventSet T C k) (fun ω => ipcWeight m T C V L k ω * g ω) =
      wsum m (univ.filter fun ω => T ω = k) g := by
  have h := wsum_riskSet_ipcWeight hm k hnuc hpos (fun ω => if T ω = k then g ω else 0)
    (fun ω ω' hT hV => by rw [hT, hg ω ω' hT hV])
  have e1 : wsum m (eventSet T C k) (fun ω => ipcWeight m T C V L k ω * g ω) =
      wsum m (riskSet T C k) (fun ω => ipcWeight m T C V L k ω *
        if T ω = k then g ω else 0) := by
    simp only [wsum, eventSet, riskSet, sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    split_ifs <;> first | omega | simp
  have e2 : wsum m (univ.filter fun ω => k ≤ T ω) (fun ω => if T ω = k then g ω else 0) =
      wsum m (univ.filter fun ω => T ω = k) g := by
    simp only [wsum, sum_filter]
    refine sum_congr rfl fun ω _ => ?_
    split_ifs <;> first | omega | simp
  rw [e1, h, e2]

omit [DecidableEq Ω] in
/-- A weighted hazard does not change when the weights on the risk set are multiplied by a
nonzero constant (individuals of zero mass are irrelevant). -/
theorem weightedHazard_congr_mul (w w' : ℕ → Ω → ℝ) (k : ℕ) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ ω ∈ riskSet T C k, m ω ≠ 0 → w' k ω = c * w k ω) :
    weightedHazard m T C w' k = weightedHazard m T C w k := by
  have key : ∀ E ⊆ riskSet T C k, wsum m E (w' k) = c * wsum m E (w k) := fun E hE => by
    rw [wsum, wsum, mul_sum]
    refine sum_congr rfl fun ω hω => ?_
    by_cases h0 : m ω = 0
    · simp [h0]
    · rw [h ω (hE hω) h0]; ring
  have hsub : eventSet T C k ⊆ riskSet T C k := fun ω hω => by
    simp only [eventSet, riskSet, mem_filter, mem_univ, true_and] at hω ⊢; omega
  rw [weightedHazard, weightedHazard, key _ hsub, key _ subset_rfl, mul_div_mul_left _ _ hc]

omit [DecidableEq Ω] in
/-- With all weights equal to one, the weighted hazard is the naive hazard among the
individuals at risk and uncensored: `m(T = k ≤ C) / m(T ≥ k, C ≥ k)`. -/
theorem weightedHazard_one (k : ℕ) :
    weightedHazard m T C (fun _ _ => 1) k = wmass m (eventSet T C k) / wmass m (riskSet T C k) := by
  rw [weightedHazard, wsum_const, wsum_const, mul_one, mul_one]

theorem stayProbBaseline_congr {j : ℕ} {ω ω' : Ω} (hV : V ω' = V ω) :
    stayProbBaseline m T C V j ω' = stayProbBaseline m T C V j ω := by
  have h : baselineCell T C V j ω' = baselineCell T C V j ω := by
    ext x; simp [baselineCell, hV]
  rw [stayProbBaseline, stayProbBaseline, h]

/-- The numerator factor is positive at an individual of positive mass still uncensored at the
end of interval `j` and alive after `j`; no positivity assumption is needed for this. -/
theorem stayProbBaseline_pos (hm : ∀ ω, 0 ≤ m ω) {j : ℕ} {ω : Ω} (h0 : 0 < m ω)
    (hC : j + 1 ≤ C ω) (hT : j < T ω) : 0 < stayProbBaseline m T C V j ω := by
  have hmem : ω ∈ baselineCell T C V j ω ∩ uncensored C (j + 1) := by
    simp [baselineCell, uncensored, hT, show j ≤ C ω by omega, show j < C ω by omega]
  have h1 : 0 < wmass m (baselineCell T C V j ω ∩ uncensored C (j + 1)) :=
    h0.trans_le (single_le_sum (fun x _ => hm x) hmem)
  exact div_pos h1 (h1.trans_le (wmass_mono hm inter_subset_left))

/-- The stabilized weight is the unstabilized weight times the product of the numerator
factors, which depends on the baseline covariates only. -/
theorem stabilizedWeight_eq_mul (k : ℕ) (ω : Ω) :
    stabilizedWeight m T C V L k ω =
      (∏ j ∈ range k, stayProbBaseline m T C V j ω) * ipcWeight m T C V L k ω := by
  simp only [stabilizedWeight, ipcWeight, div_eq_mul_inv, prod_mul_distrib]

/-- Restricting a weighted sum to a stratum of `V` is multiplying by its indicator. -/
theorem wsum_ev_inter (v : 𝒱) (E : Finset Ω) (f : Ω → ℝ) :
    wsum m (ev V v ∩ E) f = wsum m E (fun ω => f ω * if V ω = v then 1 else 0) := by
  have h : ev V v ∩ E = E.filter fun ω => V ω = v := by ext; simp [ev, and_comm]
  rw [h, wsum, wsum, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp

omit [DecidableEq Ω] in
theorem wsum_filter_indicator (P : Ω → Prop) [DecidablePred P] (v : 𝒱) :
    wsum m (univ.filter P) (fun ω => if V ω = v then 1 else 0) =
      wmass m (univ.filter fun ω => P ω ∧ V ω = v) := by
  simp only [wsum, wmass, sum_filter]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs <;> simp_all

/-- **Arm-specific or stratum-specific weighting (Sec 4.2.2.1 of TSD 24).** Under the hypotheses
of `wsum_riskSet_ipcWeight`, the unstabilized weighted hazard computed within the stratum
`V = v` of the baseline covariates equals the hazard of `T` in that stratum,
`P(T = k | T ≥ k, V = v)`, provided `P(T ≥ k, V = v) > 0`. With the randomized arm among the
baseline covariates, this is the separate weighting model in each arm. -/
theorem weightedHazard_ipcWeight_restrict (hm : ∀ ω, 0 ≤ m ω) (k : ℕ) (v : 𝒱)
    (hnuc : SwitchNUC m T C V L k) (hpos : SwitchPositive m T C V L k)
    (hk : 0 < wmass m (univ.filter fun ω => k ≤ T ω ∧ V ω = v)) :
    0 < wsum m (ev V v ∩ riskSet T C k) (ipcWeight m T C V L k) ∧
      weightedHazard (restrict m (ev V v)) T C (ipcWeight m T C V L) k =
        wmass m (univ.filter fun ω => T ω = k ∧ V ω = v) /
          wmass m (univ.filter fun ω => k ≤ T ω ∧ V ω = v) := by
  have hg : ∀ ω ω' : Ω, T ω' = T ω → V ω' = V ω →
      (fun ω => if V ω = v then (1 : ℝ) else 0) ω' = (fun ω => if V ω = v then 1 else 0) ω :=
    fun ω ω' _ hV => by simp only [hV]
  have hR := wsum_riskSet_ipcWeight hm k hnuc hpos _ hg
  have hE := wsum_eventSet_ipcWeight hm k hnuc hpos _ hg
  rw [wsum_filter_indicator] at hR hE
  rw [← wsum_ev_inter] at hR hE
  refine ⟨hR ▸ hk, ?_⟩
  rw [weightedHazard, wsum_restrict, wsum_restrict]
  exact congrArg₂ (· / ·) hE hR

/-- **Stabilized weights identify the hazard within strata of the baseline covariates
(Eq A1 of TSD 16; Sec 4.2.2 of TSD 24).** With the numerator of Eq A1 conditional on the
baseline covariates `V`, under the hypotheses of `wsum_riskSet_ipcWeight` and
`P(T ≥ k, V = v) > 0`, the stabilized weighted hazard computed within the stratum `V = v`
equals the hazard of `T` in that stratum. On the stratum the numerator is a positive constant,
so it cancels; it does not cancel across strata, and the stabilized weighted hazard of the
pooled population is in general not the marginal hazard (`Example.pooled_stabilized_ne`). This is
why baseline variables in the numerator must also enter the weighted outcome model. -/
theorem weightedHazard_stabilized_restrict (hm : ∀ ω, 0 ≤ m ω) (k : ℕ) (v : 𝒱)
    (hnuc : SwitchNUC m T C V L k) (hpos : SwitchPositive m T C V L k)
    (hk : 0 < wmass m (univ.filter fun ω => k ≤ T ω ∧ V ω = v)) :
    weightedHazard (restrict m (ev V v)) T C (stabilizedWeight m T C V L) k =
      wmass m (univ.filter fun ω => T ω = k ∧ V ω = v) /
        wmass m (univ.filter fun ω => k ≤ T ω ∧ V ω = v) := by
  obtain ⟨hR, h⟩ := weightedHazard_ipcWeight_restrict hm k v hnuc hpos hk
  obtain ⟨ω₁, hω₁, hne⟩ := exists_ne_zero_of_sum_ne_zero hR.ne'
  have hp₁ : 0 < m ω₁ := (hm ω₁).lt_of_ne fun h0 => hne (by rw [← h0, zero_mul])
  obtain ⟨hv₁, hr₁⟩ := mem_inter.1 hω₁
  have hr₁' := (mem_filter.1 hr₁).2
  have hc : 0 < ∏ j ∈ range k, stayProbBaseline m T C V j ω₁ :=
    prod_pos fun j hj => stayProbBaseline_pos hm hp₁ (by have := mem_range.1 hj; omega)
      (by have := mem_range.1 hj; omega)
  rw [← h]
  refine weightedHazard_congr_mul _ _ k hc.ne' fun ω _ hω => ?_
  have hV : V ω = V ω₁ := by
    rw [mem_ev.1 hv₁]
    by_contra hv
    exact hω (by simp [Longitudinal.restrict, hv])
  rw [stabilizedWeight_eq_mul]
  congr 1
  exact prod_congr rfl fun j _ => stayProbBaseline_congr hV

/-- No informative switching given the baseline covariates up to time `k`: for every `j < k`,
within every baseline cell at `j`, remaining uncensored at the end of interval `j` is mean
independent of the covariate history event `L̄_j = L̄_j ω`. In words: the history of the
time-varying prognostic factors does not affect the hazard of switching once the baseline
covariates are accounted for. -/
def NoInformativeSwitchGivenBaseline (m : Ω → ℝ) (T C : Ω → ℕ) (V : Ω → 𝒱) (L : ℕ → Ω → 𝓛)
    (k : ℕ) : Prop :=
  ∀ j < k, ∀ ω : Ω, MeanIndepOn m (baselineCell T C V j ω) (covHist L j ω)
    (fun ω' => if j + 1 ≤ C ω' then 1 else 0)

/-- **The stabilized weight equals one without informative switching (Appendix A of TSD 16).**
If the history of the time-varying covariates does not affect the hazard of switching given the
baseline covariates, then under positivity every individual of positive mass in the risk set
at `k` has stabilized weight `1`: each factor of Eq A1 is a ratio of two equal, positive
conditional probabilities. -/
theorem stabilizedWeight_eq_one (hm : ∀ ω, 0 ≤ m ω) (k : ℕ)
    (hni : NoInformativeSwitchGivenBaseline m T C V L k) (hpos : SwitchPositive m T C V L k)
    {ω : Ω} (h0 : 0 < m ω) (hω : ω ∈ riskSet T C k) :
    stabilizedWeight m T C V L k ω = 1 := by
  obtain ⟨hT, hC⟩ := (mem_filter.1 hω).2
  refine prod_eq_one fun j hj => ?_
  have hjk := mem_range.1 hj
  have hπ := hpos j hjk ω h0 (by omega) (by omega)
  have hmass : 0 < wmass m (baselineCell T C V j ω ∩ covHist L j ω) :=
    h0.trans_le (single_le_sum (fun x _ => hm x) (mem_riskCell_self (V := V) (L := L)
      (show j ≤ C ω by omega) (show j < T ω by omega)))
  have heq := (meanIndepOn_iff_condMean_eq hm hmass).1 (hni j hjk ω)
  rw [condMean, condMean, wsum_indicator_uncensored, wsum_indicator_uncensored] at heq
  have hsp : stayProb m T C V L j ω = stayProbBaseline m T C V j ω := heq
  rw [← hsp]
  exact div_self hπ.ne'

/-- Truncation of the weights at the level `c`: `min (w k ω) c`. -/
noncomputable def truncate (c : ℝ) (w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun k ω => min (w k ω) c

omit [Fintype Ω] [DecidableEq Ω] in
/-- Truncation loses mass exactly when a weight of positive mass exceeds the cap:
`∑_s m min(f, c) = ∑_s m f` if and only if `f ≤ c` at every point of `s` of positive mass. -/
theorem wsum_min_eq_iff (hm : ∀ ω, 0 ≤ m ω) (s : Finset Ω) (f : Ω → ℝ) (c : ℝ) :
    wsum m s (fun ω => min (f ω) c) = wsum m s f ↔ ∀ ω ∈ s, 0 < m ω → f ω ≤ c := by
  rw [wsum, wsum, sum_eq_sum_iff_of_le fun ω _ => mul_le_mul_of_nonneg_left (min_le_left _ _)
    (hm ω)]
  refine forall₂_congr fun ω _ => ?_
  rcases (hm ω).eq_or_lt with h0 | h0
  · simp [← h0]
  · rw [mul_right_inj' h0.ne', min_eq_left_iff]
    exact ⟨fun h _ => h, fun h => h h0⟩

omit [DecidableEq Ω] in
/-- Truncation that caps no weight of positive mass on the risk set leaves the weighted hazard
unchanged. -/
theorem weightedHazard_truncate_of_le (w : ℕ → Ω → ℝ) (k : ℕ) (c : ℝ)
    (h : ∀ ω ∈ riskSet T C k, m ω ≠ 0 → w k ω ≤ c) :
    weightedHazard m T C (truncate c w) k = weightedHazard m T C w k :=
  weightedHazard_congr_mul w (truncate c w) k one_ne_zero fun ω hω h0 => by
    rw [truncate, one_mul, min_eq_left (h ω hω h0)]

/-- **Truncation of the weights (Sec 4.2.2.1 of TSD 24): when the weighting identity survives.**
Under the hypotheses of `wsum_riskSet_ipcWeight`, the truncated weights still restore the
population alive at `k`, `∑_{T ≥ k, C ≥ k} m min(W_k, c) = m(T ≥ k)`, if and only if no
individual of positive mass in the risk set has weight above `c`. -/
theorem wsum_truncate_ipcWeight_eq_iff (hm : ∀ ω, 0 ≤ m ω) (k : ℕ)
    (hnuc : SwitchNUC m T C V L k) (hpos : SwitchPositive m T C V L k) (c : ℝ) :
    wsum m (riskSet T C k) (truncate c (ipcWeight m T C V L) k) =
        wmass m (univ.filter fun ω => k ≤ T ω) ↔
      ∀ ω ∈ riskSet T C k, 0 < m ω → ipcWeight m T C V L k ω ≤ c := by
  have hR := wsum_riskSet_ipcWeight hm k hnuc hpos (fun _ => 1) (fun _ _ _ _ => rfl)
  simp only [mul_one, wsum_const] at hR
  rw [← hR]
  exact wsum_min_eq_iff hm _ _ c

/-- The variance of a real function under a finite distribution:
`E[(f - E f)²]`. -/
noncomputable def finVar (p : FiniteDist Ω) (f : Ω → ℝ) : ℝ :=
  p.expect fun ω => (f ω - p.expect f) ^ 2

omit [DecidableEq Ω] in
/-- `E[(f - a)²] = Var f + (E f - a)²` for every constant `a`. -/
theorem expect_sq_sub (p : FiniteDist Ω) (f : Ω → ℝ) (a : ℝ) :
    p.expect (fun ω => (f ω - a) ^ 2) = finVar p f + (p.expect f - a) ^ 2 := by
  set E := p.expect f with hE
  have hs : ∑ ω, p ω = 1 := p.sum_eq_one
  have hf : ∑ ω, p ω * f ω = E := rfl
  calc p.expect (fun ω => (f ω - a) ^ 2)
      = ∑ ω, (p ω * (f ω - E) ^ 2 + (2 * (E - a)) * (p ω * f ω) - (2 * (E - a) * E) * p ω +
          (E - a) ^ 2 * p ω) := sum_congr rfl fun ω _ => by ring
    _ = finVar p f + 2 * (E - a) * (∑ ω, p ω * f ω) - 2 * (E - a) * E * (∑ ω, p ω) +
          (E - a) ^ 2 * (∑ ω, p ω) := by
        rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
        rfl
    _ = finVar p f + (E - a) ^ 2 := by rw [hf, hs]; ring

omit [DecidableEq Ω] in
/-- **Truncation does not increase the variance of the weights (Sec 4.2.2.1 of TSD 24).** For
every function `f` and cap `c`, `Var(min(f, c)) ≤ Var(f)` under a finite distribution. This is
the population counterpart of the smaller standard errors of truncated weights; the document's
statement about the standard errors of estimated treatment effects is a sampling statement and
is not formalized. -/
theorem finVar_min_le (p : FiniteDist Ω) (f : Ω → ℝ) (c : ℝ) :
    finVar p (fun ω => min (f ω) c) ≤ finVar p f := by
  have h1 := expect_sq_sub p (fun ω => min (f ω) c) (min (p.expect f) c)
  have h2 : p.expect (fun ω => (min (f ω) c - min (p.expect f) c) ^ 2) ≤
      p.expect (fun ω => (f ω - p.expect f) ^ 2) := by
    refine p.expect_mono fun ω => sq_le_sq.2 ?_
    have := abs_min_sub_min_le_max (f ω) c (p.expect f) c
    simpa using this
  have h3 := sq_nonneg (p.expect (fun ω => min (f ω) c) - min (p.expect f) c)
  have h4 : p.expect (fun ω => (f ω - p.expect f) ^ 2) = finVar p f := rfl
  linarith

omit [Fintype Ω] in
/-- If the survival time is constant on `s`, then within `s` every variable is mean independent
of each event `T = t`. Used to check no unmeasured confounding in the examples. -/
theorem meanIndepOn_ev_of_const {s : Finset Ω} (hs : ∀ x ∈ s, ∀ y ∈ s, T x = T y) (t : ℕ)
    (f : Ω → ℝ) [Fintype Ω] : MeanIndepOn m s (ev T t) f := by
  by_cases h : ∃ x ∈ s, T x = t
  · obtain ⟨x, hx, hxt⟩ := h
    have : s ∩ ev T t = s := inter_eq_left.2 fun y hy => mem_ev.2 ((hs y hy x hx).trans hxt)
    rw [MeanIndepOn, this]
  · push Not at h
    have : s ∩ ev T t = ∅ := by
      ext y; simp only [mem_inter, mem_ev, notMem_empty, iff_false, not_and]; exact h y
    rw [MeanIndepOn, this]
    simp [wsum, wmass]

omit [Fintype Ω] in
/-- A variable constant on `s` is mean independent of every event within `s`. -/
theorem meanIndepOn_of_const {s : Finset Ω} (t : Finset Ω) {f : Ω → ℝ} {c : ℝ}
    (hf : ∀ x ∈ s, f x = c) : MeanIndepOn m s t f := by
  have h1 : wsum m (s ∩ t) f = wmass m (s ∩ t) * c :=
    (wsum_congr fun x hx => hf x (mem_inter.1 hx).1).trans (wsum_const _ c)
  have h2 : wsum m s f = wmass m s * c := (wsum_congr hf).trans (wsum_const _ c)
  rw [MeanIndepOn, h1, h2]
  ring

omit [Fintype Ω] in
/-- Within `s`, every variable is mean independent of an event containing `s`. -/
theorem meanIndepOn_of_subset {s t : Finset Ω} (h : s ⊆ t) (f : Ω → ℝ) :
    MeanIndepOn m s t f := by
  rw [MeanIndepOn, inter_eq_left.2 h]

end Lemmas

section Measure

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {𝒱 𝓛 : Type*} [DecidableEq 𝒱] [DecidableEq 𝓛]
  {T C : Ω → ℕ} {V : Ω → 𝒱} {L : ℕ → Ω → 𝓛}

omit [DecidableEq Ω] in
/-- The bridge to measure theory: the probability, under the measure of a finite distribution,
of the event defined by a predicate is the mass of the corresponding finset. -/
theorem toMeasure_real_setOf (p : FiniteDist Ω) (P : Ω → Prop) [DecidablePred P] :
    p.toMeasure.real {ω | P ω} = wmass p (univ.filter P) := by
  have hs : {ω | P ω} = ((univ.filter P : Finset Ω) : Set Ω) := by ext; simp
  rw [MeasureTheory.measureReal_def, hs, FiniteDist.toMeasure_apply_finset,
    ENNReal.toReal_ofReal (p.prob_nonneg _)]
  rfl

omit [DecidableEq Ω] in
theorem hazard_toMeasure (p : FiniteDist Ω) (k : ℕ) :
    hazard p.toMeasure T k =
      wmass p (univ.filter fun ω => T ω = k) / wmass p (univ.filter fun ω => k ≤ T ω) := by
  rw [hazard, atRisk, toMeasure_real_setOf, toMeasure_real_setOf]

omit [DecidableEq Ω] in
theorem atRisk_toMeasure (p : FiniteDist Ω) (k : ℕ) :
    atRisk p.toMeasure T k = wmass p (univ.filter fun ω => k ≤ T ω) :=
  toMeasure_real_setOf p _

/-- **The weighted hazard identifies the hazard (Sec 3.2.1 of TSD 16).** Under sequential no
unmeasured confounding of the switch and positivity up to time `k`, and if `P(T ≥ k) > 0`,
the inverse probability of censoring weighted risk set at `k` has positive weighted mass and
the weighted hazard at `k` equals the hazard `P(T = k | T ≥ k)` of the survival time without
switching. -/
theorem weightedHazard_ipcWeight (p : FiniteDist Ω) (k : ℕ) (hnuc : SwitchNUC p T C V L k)
    (hpos : SwitchPositive p T C V L k) (hk : 0 < atRisk p.toMeasure T k) :
    0 < wsum p (riskSet T C k) (ipcWeight p T C V L k) ∧
      weightedHazard p T C (ipcWeight p T C V L) k = hazard p.toMeasure T k := by
  have hR := wsum_riskSet_ipcWeight p.nonneg k hnuc hpos (fun _ => 1) (fun _ _ _ _ => rfl)
  have hE := wsum_eventSet_ipcWeight p.nonneg k hnuc hpos (fun _ => 1) (fun _ _ _ _ => rfl)
  simp only [mul_one, wsum_const] at hR hE
  rw [atRisk_toMeasure] at hk
  refine ⟨?_, ?_⟩
  · change 0 < wsum p (riskSet T C k) (fun ω => ipcWeight p T C V L k ω)
    rw [hR]; exact hk
  · rw [weightedHazard, hazard_toMeasure]
    change wsum p (eventSet T C k) (fun ω => ipcWeight p T C V L k ω) /
      wsum p (riskSet T C k) (fun ω => ipcWeight p T C V L k ω) = _
    rw [hR, hE]

/-- **The weighted product limit identifies survival (Sec 3.2.1 of TSD 16).** Under sequential no
unmeasured confounding of the switch and positivity up to time `k`, and `P(T ≥ k) > 0`, the
inverse probability of censoring weighted product limit at `k` equals the survival
`P(T > k)` of the survival time without switching; every factor is one minus a genuine
weighted conditional probability (first conjunct). -/
theorem weightedProductLimit_ipcWeight (p : FiniteDist Ω) (k : ℕ) (hnuc : SwitchNUC p T C V L k)
    (hpos : SwitchPositive p T C V L k) (hk : 0 < atRisk p.toMeasure T k) :
    (∀ i ≤ k, 0 < wsum p (riskSet T C i) (ipcWeight p T C V L i)) ∧
      weightedProductLimit p T C (ipcWeight p T C V L) k = survival p.toMeasure T k := by
  have hi : ∀ i ≤ k, 0 < wsum p (riskSet T C i) (ipcWeight p T C V L i) ∧
      weightedHazard p T C (ipcWeight p T C V L) i = hazard p.toMeasure T i := fun i hik =>
    weightedHazard_ipcWeight p i (switchNUC_mono hik hnuc) (switchPositive_mono hik hpos)
      (hk.trans_le (atRisk_antitone hik))
  refine ⟨fun i hik => (hi i hik).1, ?_⟩
  rw [survival_eq_prod_one_sub_hazard' Measurable.of_discrete, weightedProductLimit]
  exact prod_congr rfl fun i hi' => by rw [(hi i (Nat.lt_succ_iff.1 (mem_range.1 hi'))).2]

omit [DecidableEq Ω] in
/-- The naive hazard among those at risk and uncensored is the observed hazard of the law of
the artificially censored data `(min T C, 1{T ≤ C})` (`Survival.observedHazard`). -/
theorem observedHazard_toMeasure (p : FiniteDist Ω) (k : ℕ) :
    observedHazard (p.toMeasure.map (observed T C)) k =
      wmass p (eventSet T C k) / wmass p (riskSet T C k) := by
  rw [observedHazard_map_observed Measurable.of_discrete Measurable.of_discrete,
    toMeasure_real_setOf, toMeasure_real_setOf]
  rfl

/-- **IPCW reduces to simple censoring when all confounders are unmeasured (Sec 4 of TSD 16).**
If the weight models contain no covariates (`V` and every `L i` constant), then under
positivity, and if the risk set at `k` has positive mass, the inverse probability of censoring
weighted hazard at `k` is the naive observed hazard of the artificially censored data. No
assumption on the switching mechanism is used: the weights are constant over the risk set. -/
theorem weightedHazard_ipcWeight_eq_observedHazard (p : FiniteDist Ω) (k : ℕ)
    (hV : ∀ ω ω', V ω' = V ω) (hL : ∀ i ω ω', L i ω' = L i ω)
    (hpos : SwitchPositive p T C V L k) (hk : 0 < wmass p (riskSet T C k)) :
    weightedHazard p T C (ipcWeight p T C V L) k =
      observedHazard (p.toMeasure.map (observed T C)) k := by
  obtain ⟨ω₀, hω₀, hne⟩ := exists_ne_zero_of_sum_ne_zero hk.ne'
  have hp₀ : 0 < p ω₀ := (p.nonneg ω₀).lt_of_ne (Ne.symm hne)
  obtain ⟨hT, hC⟩ := (mem_filter.1 hω₀).2
  have hc : ipcWeight p T C V L k ω₀ ≠ 0 :=
    prod_ne_zero_iff.2 fun j hj => inv_ne_zero (hpos j (mem_range.1 hj) ω₀ hp₀
      (by have := mem_range.1 hj; omega) (by have := mem_range.1 hj; omega)).ne'
  rw [observedHazard_toMeasure, ← weightedHazard_one]
  refine weightedHazard_congr_mul _ _ k hc fun ω _ _ => ?_
  rw [mul_one, ipcWeight_congr (hV ω₀ ω) fun i _ => hL i ω₀ ω]

/-- The product-limit form of `weightedHazard_ipcWeight_eq_observedHazard`: without covariates
in the weight models, the inverse probability of censoring weighted product limit is the
product-limit (Kaplan-Meier) functional of the artificially censored data
(`Survival.productLimit`). -/
theorem weightedProductLimit_ipcWeight_eq_productLimit (p : FiniteDist Ω) (k : ℕ)
    (hV : ∀ ω ω', V ω' = V ω) (hL : ∀ i ω ω', L i ω' = L i ω)
    (hpos : SwitchPositive p T C V L k) (hk : 0 < wmass p (riskSet T C k)) :
    weightedProductLimit p T C (ipcWeight p T C V L) k =
      productLimit (p.toMeasure.map (observed T C)) k := by
  refine prod_congr rfl fun i hi => ?_
  have hik := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have hsub : riskSet T C k ⊆ riskSet T C i := fun ω hω => by
    simp only [riskSet, mem_filter, mem_univ, true_and] at hω ⊢; omega
  rw [weightedHazard_ipcWeight_eq_observedHazard p i hV hL (switchPositive_mono hik hpos)
    (hk.trans_le (wmass_mono p.nonneg hsub))]

end Measure

namespace Example

/-! ### A switching trial with a prognostic covariate

Four equally likely individuals `ω = (l, s) : Bool × Bool`. The covariate `l` is prognostic:
individuals with `l = true` die in interval `1` (`T = 1`), the others survive follow-up
(`T = 2`). Among the poor-prognosis individuals, those with `s = true` switch at the end of
interval `0` (`C = 0`); nobody else switches (`C = 2`). -/

/-- The uniform distribution on the four individuals. -/
noncomputable def p : FiniteDist (Bool × Bool) := FiniteDist.uniform

/-- The survival time without switching: `1` for poor prognosis, `2` otherwise. -/
def T (ω : Bool × Bool) : ℕ := if ω.1 then 1 else 2

/-- The switching (censoring) time: `0` for poor-prognosis switchers, `2` otherwise. -/
def C (ω : Bool × Bool) : ℕ := if ω.1 && ω.2 then 0 else 2

/-- The prognostic covariate, measured at every time. -/
def L (_ : ℕ) (ω : Bool × Bool) : Bool := ω.1

/-- No baseline covariates. -/
def V (_ : Bool × Bool) : Unit := ()

theorem riskCell_zero (ω : Bool × Bool) :
    riskCell T C V L 0 ω = univ.filter fun x => x.1 = ω.1 := by
  revert ω; decide

theorem wmass_p (s : Finset (Bool × Bool)) :
    wmass p s = ∑ ω, if ω ∈ s then (1 / 4 : ℝ) else 0 := by
  rw [wmass, ← sum_filter, filter_mem_eq_inter, univ_inter]
  simp [p]

theorem wmass_filter_p (P : Bool × Bool → Prop) [DecidablePred P] :
    wmass p (univ.filter P) = ∑ a : Bool, ∑ b : Bool, if P (a, b) then (1 / 4 : ℝ) else 0 := by
  rw [wmass_p]
  simp only [mem_filter, mem_univ, true_and, Fintype.sum_prod_type]

theorem p_pos (ω : Bool × Bool) : 0 < p ω := by simp [p]

/-- No unmeasured confounding of the switch holds: within each risk cell at time `0` the
survival time is constant. -/
theorem switchNUC : SwitchNUC p T C V L 1 := by
  intro j hj ω t
  obtain rfl : j = 0 := by omega
  refine meanIndepOn_ev_of_const (fun x hx y hy => ?_) t _
  rw [riskCell_zero] at hx hy
  simp only [mem_filter, mem_univ, true_and] at hx hy
  simp [T, hx, hy]

theorem stayProb_zero (ω : Bool × Bool) :
    stayProb p T C V L 0 ω = if ω.1 then 1 / 2 else 1 := by
  rcases ω with ⟨_ | _, _ | _⟩ <;>
    simp [stayProb, condProb, wmass_p, Fintype.sum_prod_type, riskCell_zero, uncensored, C] <;>
    norm_num

theorem switchPositive : SwitchPositive p T C V L 1 := by
  intro j hj ω _ _ _
  obtain rfl : j = 0 := by omega
  rw [stayProb_zero]
  split_ifs <;> norm_num

theorem hazard_one : hazard p.toMeasure T 1 = 1 / 2 := by
  rw [hazard_toMeasure, wmass_filter_p, wmass_filter_p]
  simp only [Fintype.sum_bool]
  norm_num [T]

theorem survival_one : survival p.toMeasure T 1 = 1 / 2 := by
  rw [survival, toMeasure_real_setOf, wmass_filter_p]
  simp only [Fintype.sum_bool]
  norm_num [T]

theorem atRisk_one_pos : 0 < atRisk p.toMeasure T 1 := by
  rw [atRisk_toMeasure, wmass_filter_p]
  simp only [Fintype.sum_bool]
  norm_num [T]

/-- The naive hazard at time `1` among those at risk and unswitched is `1/3`. -/
theorem naive_hazard_one : wmass p (eventSet T C 1) / wmass p (riskSet T C 1) = 1 / 3 := by
  rw [eventSet, riskSet, wmass_filter_p, wmass_filter_p]
  simp only [Fintype.sum_bool]
  norm_num [T, C]

theorem riskSet_one_pos : 0 < wmass p (riskSet T C 1) := by
  rw [riskSet, wmass_filter_p]
  simp only [Fintype.sum_bool]
  norm_num [T, C]

/-- **Censoring switchers is biased; IPCW corrects it (Sec 3.1.2 and Sec 3.2.1 of TSD 16).** In
the example the product limit of the artificially censored data at time `1` is `2/3`, while the
survival without switching is `1/2`; the inverse probability of censoring weighted product limit
recovers `1/2`, since no unmeasured confounding of the switch and positivity hold given `L`. -/
theorem censoring_switchers_biased :
    productLimit (p.toMeasure.map (observed T C)) 1 = 2 / 3 ∧
      weightedProductLimit p T C (ipcWeight p T C V L) 1 = 1 / 2 ∧
      survival p.toMeasure T 1 = 1 / 2 := by
  refine ⟨?_, ?_, survival_one⟩
  · rw [productLimit, prod_range_succ, prod_range_one, observedHazard_toMeasure,
      observedHazard_toMeasure, naive_hazard_one, eventSet, riskSet, wmass_filter_p,
      wmass_filter_p]
    simp only [Fintype.sum_bool]
    norm_num [T, C]
  · rw [(weightedProductLimit_ipcWeight p 1 switchNUC switchPositive atRisk_one_pos).2,
      survival_one]

/-- No covariates in the weight models. -/
def L₀ (_ : ℕ) (_ : Bool × Bool) : Unit := ()

theorem stayProb_zero_L₀ (ω : Bool × Bool) : stayProb p T C V L₀ 0 ω = 3 / 4 := by
  have h : riskCell T C V L₀ 0 ω = univ := by revert ω; decide
  rw [stayProb, condProb, h, wmass_p, wmass_p]
  simp [Fintype.sum_prod_type, uncensored, C]
  norm_num

theorem switchPositive_L₀ : SwitchPositive p T C V L₀ 1 := by
  intro j hj ω _ _ _
  obtain rfl : j = 0 := by omega
  rw [stayProb_zero_L₀]
  norm_num

/-- **Without the confounder in the weight model, IPCW is simple censoring and is biased
(Sec 4 of TSD 16, Sec 3.2.1).** With no covariates in the weight models, positivity holds but
no unmeasured confounding of the switch fails (switching depends on prognosis through the
unmeasured `l`); the inverse probability of censoring weighted hazard at time `1` is the naive
`1/3`, not the hazard `1/2`. -/
theorem ipcw_without_confounder :
    SwitchPositive p T C V L₀ 1 ∧ ¬ SwitchNUC p T C V L₀ 1 ∧
      weightedHazard p T C (ipcWeight p T C V L₀) 1 = 1 / 3 ∧ hazard p.toMeasure T 1 = 1 / 2 := by
  have hw : weightedHazard p T C (ipcWeight p T C V L₀) 1 = 1 / 3 := by
    rw [weightedHazard_ipcWeight_eq_observedHazard p 1 (fun _ _ => rfl) (fun _ _ _ => rfl)
      switchPositive_L₀ riskSet_one_pos, observedHazard_toMeasure, naive_hazard_one]
  refine ⟨switchPositive_L₀, fun h => ?_, hw, hazard_one⟩
  have := (weightedHazard_ipcWeight p 1 h switchPositive_L₀ atRisk_one_pos).2
  rw [hw, hazard_one] at this
  norm_num at this

/-- The prognostic covariate recorded as a baseline covariate. -/
def Vp (ω : Bool × Bool) : Bool := ω.1

theorem riskCell_zero_Vp (ω : Bool × Bool) :
    riskCell T C Vp L₀ 0 ω = univ.filter fun x => x.1 = ω.1 := by
  revert ω; decide

theorem stayProb_zero_Vp (ω : Bool × Bool) :
    stayProb p T C Vp L₀ 0 ω = if ω.1 then 1 / 2 else 1 := by
  rcases ω with ⟨_ | _, _ | _⟩ <;>
    simp [stayProb, condProb, wmass_p, Fintype.sum_prod_type, riskCell_zero_Vp, uncensored,
      C] <;>
    norm_num

/-- **Stabilized weights with a prognostic numerator do not identify the marginal hazard
(Sec 4.2.2 of TSD 24).** With the prognostic variable as baseline covariate `V` and no
time-varying covariates, no unmeasured confounding of the switch and positivity hold, so the
stabilized weighted hazard within each stratum of `V` is the stratum hazard
(`weightedHazard_stabilized_restrict`). But the stabilized weights are all `1` here
(`stabilizedWeight_eq_one`), and the stabilized weighted hazard of the pooled population is the
naive `1/3`, not the marginal hazard `1/2`. -/
theorem pooled_stabilized_ne :
    SwitchNUC p T C Vp L₀ 1 ∧ SwitchPositive p T C Vp L₀ 1 ∧
      weightedHazard p T C (stabilizedWeight p T C Vp L₀) 1 = 1 / 3 ∧
      hazard p.toMeasure T 1 = 1 / 2 := by
  have hnuc : SwitchNUC p T C Vp L₀ 1 := by
    intro j hj ω t
    obtain rfl : j = 0 := by omega
    refine meanIndepOn_ev_of_const (fun x hx y hy => ?_) t _
    rw [riskCell_zero_Vp] at hx hy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    simp [T, hx, hy]
  have hpos : SwitchPositive p T C Vp L₀ 1 := by
    intro j hj ω _ _ _
    obtain rfl : j = 0 := by omega
    rw [stayProb_zero_Vp]
    split_ifs <;> norm_num
  have hni : NoInformativeSwitchGivenBaseline p T C Vp L₀ 1 := by
    intro j _ ω
    have h : covHist L₀ j ω = univ := by ext; simp [covHist, L₀]
    rw [MeanIndepOn, h, inter_univ]
  refine ⟨hnuc, hpos, ?_, hazard_one⟩
  rw [← naive_hazard_one, ← weightedHazard_one]
  refine weightedHazard_congr_mul _ _ 1 one_ne_zero fun ω hω _ => ?_
  rw [stabilizedWeight_eq_one p.nonneg 1 hni hpos (p_pos ω) hω, one_mul]

theorem ipcWeight_one (ω : Bool × Bool) : ipcWeight p T C V L 1 ω = if ω.1 then 2 else 1 := by
  rw [ipcWeight, prod_range_one, stayProb_zero]
  split_ifs <;> norm_num

/-- **Truncation can bias the weighted hazard (Sec 4.2.2.1 of TSD 24).** Truncating the
weights of the example at `1` caps the weight `2` of the poor-prognosis individual who did not
switch: the truncated weights no longer restore the population at risk, and the truncated
weighted hazard at time `1` is the naive `1/3` instead of `1/2`. -/
theorem truncation_biased :
    wsum p (riskSet T C 1) (truncate 1 (ipcWeight p T C V L) 1) ≠
        wmass p (univ.filter fun ω => 1 ≤ T ω) ∧
      weightedHazard p T C (truncate 1 (ipcWeight p T C V L)) 1 = 1 / 3 ∧
      weightedHazard p T C (ipcWeight p T C V L) 1 = 1 / 2 := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have := ((wsum_truncate_ipcWeight_eq_iff p.nonneg 1 switchNUC switchPositive 1).1 h)
      (true, false) (by simp [riskSet, T, C]) (p_pos _)
    rw [ipcWeight_one] at this
    norm_num at this
  · rw [← naive_hazard_one, ← weightedHazard_one]
    refine weightedHazard_congr_mul _ _ 1 one_ne_zero fun ω _ _ => ?_
    rw [truncate, ipcWeight_one, one_mul]
    split_ifs <;> norm_num
  · rw [(weightedHazard_ipcWeight p 1 switchNUC switchPositive atRisk_one_pos).2, hazard_one]

/-- A switching time under which every poor-prognosis individual switches at the end of
interval `0`: positivity fails. -/
def Cp (ω : Bool × Bool) : ℕ := if ω.1 then 0 else 2

/-- A second survival time: everybody survives follow-up. -/
def T' (_ : Bool × Bool) : ℕ := 2

/-- **Positivity cannot be dropped (Sec 3.2.1 of TSD 16; Sec 4.2.2 of TSD 24).** If every
individual with poor prognosis switches, the two survival times `T` and `T'` give the same
artificially censored data and the same covariates, no unmeasured confounding of the switch
holds for both, positivity fails, and the hazards at time `1` differ (`1/2` and `0`). So the
hazard is not identified from the observed data. -/
theorem not_identified_without_positivity :
    observed T Cp = observed T' Cp ∧ SwitchNUC p T Cp V L 1 ∧ SwitchNUC p T' Cp V L 1 ∧
      ¬ SwitchPositive p T Cp V L 1 ∧ hazard p.toMeasure T 1 = 1 / 2 ∧
      hazard p.toMeasure T' 1 = 0 := by
  have hcell : ∀ ω, riskCell T Cp V L 0 ω = univ.filter fun x => x.1 = ω.1 := by
    decide
  refine ⟨by funext ω; revert ω; decide, ?_, ?_, fun h => ?_, hazard_one, ?_⟩
  · intro j hj ω t
    obtain rfl : j = 0 := by omega
    refine meanIndepOn_ev_of_const (fun x hx y hy => ?_) t _
    rw [hcell] at hx hy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    simp [T, hx, hy]
  · intro j _ ω t
    exact meanIndepOn_ev_of_const (fun _ _ _ _ => rfl) t _
  · have := h 0 one_pos (true, false) (p_pos _) (Nat.zero_le _) (by decide)
    rw [stayProb, condProb,
      show riskCell T Cp V L 0 (true, false) ∩ uncensored Cp 1 = ∅ by decide] at this
    simp [wmass] at this
  · rw [hazard_toMeasure, wmass_filter_p]
    simp [T']

end Example

namespace Example₂

open Example (p wmass_filter_p p_pos)

/-! ### Two periods with a time-varying confounder

The same four individuals. The covariate is uninformative at time `0` and reveals the
prognosis `l` at time `1`. Poor-prognosis individuals die in interval `2` (`T = 2`), the others
survive follow-up (`T = 3`); poor-prognosis individuals with `s = true` switch at the end of
interval `1` (`C = 1`), nobody else switches (`C = 3`). The weight at time `2` has two
factors. -/

/-- The survival time without switching. -/
def T (ω : Bool × Bool) : ℕ := if ω.1 then 2 else 3

/-- The switching time. -/
def C (ω : Bool × Bool) : ℕ := if ω.1 && ω.2 then 1 else 3

/-- The time-varying covariate: uninformative at time `0`, the prognosis from time `1` on. -/
def L (i : ℕ) (ω : Bool × Bool) : Bool := if i = 0 then false else ω.1

/-- No baseline covariates. -/
def V (_ : Bool × Bool) : Unit := ()

/-- The time-varying confounder `L 1` used as if it were a baseline covariate. -/
def Vt (ω : Bool × Bool) : Bool := ω.1

theorem stayProb_zero (ω : Bool × Bool) : stayProb p T C V L 0 ω = 1 := by
  have h : riskCell T C V L 0 ω = univ := by revert ω; decide
  rw [stayProb, condProb, h, show (univ : Finset (Bool × Bool)) ∩ uncensored C 1 = univ by
    decide]
  exact div_self (by rw [← univ_inter (univ : Finset (Bool × Bool)), ← h]; exact
    ((p_pos ω).trans_le (single_le_sum (fun x _ => p.nonneg x)
      (by rw [h]; exact mem_univ ω))).ne')

theorem riskCell_one (ω : Bool × Bool) :
    riskCell T C V L 1 ω = univ.filter fun x => x.1 = ω.1 := by
  revert ω; decide

theorem stayProb_one (ω : Bool × Bool) :
    stayProb p T C V L 1 ω = if ω.1 then 1 / 2 else 1 := by
  rw [stayProb, condProb, riskCell_one]
  rcases ω with ⟨_ | _, _ | _⟩ <;>
    simp only [show ∀ b : Bool, (univ.filter fun x : Bool × Bool => x.1 = b) ∩ uncensored C 2 =
      univ.filter fun x => x.1 = b ∧ 2 ≤ C x from fun b => by ext; simp [uncensored]] <;>
    rw [wmass_filter_p, wmass_filter_p] <;> simp only [Fintype.sum_bool] <;> norm_num [C]

theorem switchNUC : SwitchNUC p T C V L 2 := by
  intro j hj ω t
  interval_cases j
  · refine meanIndepOn_of_const _ (c := 1) fun x _ => ?_
    have : 1 ≤ C x := by unfold C; split_ifs <;> omega
    simp [this]
  · refine meanIndepOn_ev_of_const (fun x hx y hy => ?_) t _
    rw [riskCell_one] at hx hy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    simp [T, hx, hy]

theorem switchPositive : SwitchPositive p T C V L 2 := by
  intro j hj ω _ _ _
  interval_cases j
  · rw [stayProb_zero]; norm_num
  · rw [stayProb_one]; split_ifs <;> norm_num

theorem hazard_two : hazard p.toMeasure T 2 = 1 / 2 := by
  rw [hazard_toMeasure, wmass_filter_p, wmass_filter_p]
  simp only [Fintype.sum_bool]
  norm_num [T]

/-- **Two periods: IPCW corrects the bias of censoring switchers (Sec 3.2.1 of TSD 16).** The
naive hazard at time `2` among those at risk and unswitched is `1/3`; the inverse probability
of censoring weighted hazard, whose weight at time `2` has two factors, is the hazard `1/2`. -/
theorem two_period_ipcw :
    wmass p (eventSet T C 2) / wmass p (riskSet T C 2) = 1 / 3 ∧
      weightedHazard p T C (ipcWeight p T C V L) 2 = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · rw [eventSet, riskSet, wmass_filter_p, wmass_filter_p]
    simp only [Fintype.sum_bool]
    norm_num [T, C]
  · rw [(weightedHazard_ipcWeight p 2 switchNUC switchPositive (by
      rw [atRisk_toMeasure, wmass_filter_p]; simp only [Fintype.sum_bool]; norm_num [T])).2,
      hazard_two]

theorem riskCell_Vt (j : ℕ) (hj : j < 2) (ω : Bool × Bool) :
    riskCell T C Vt L j ω = univ.filter fun x => x.1 = ω.1 := by
  interval_cases j <;> revert ω <;> decide

/-- **The numerator must not contain a time-varying confounder (Sec 4.2.2 of TSD 24).** If the
numerator of the stabilized weights conditions on the time-varying confounder `L 1`, no
unmeasured confounding of the switch and positivity still hold, but the stabilized weights are
all `1` (`stabilizedWeight_eq_one`) and the stabilized weighted hazard of the trial population
at time `2` is the naive `1/3`, not the hazard `1/2`. -/
theorem numerator_with_time_varying_confounder :
    SwitchNUC p T C Vt L 2 ∧ SwitchPositive p T C Vt L 2 ∧
      weightedHazard p T C (stabilizedWeight p T C Vt L) 2 = 1 / 3 ∧
      hazard p.toMeasure T 2 = 1 / 2 := by
  have hnuc : SwitchNUC p T C Vt L 2 := by
    intro j hj ω t
    refine meanIndepOn_ev_of_const (fun x hx y hy => ?_) t _
    rw [riskCell_Vt j hj] at hx hy
    simp only [mem_filter, mem_univ, true_and] at hx hy
    simp [T, hx, hy]
  have hpos : SwitchPositive p T C Vt L 2 := by
    intro j hj ω _ _ _
    rw [stayProb, condProb, riskCell_Vt j hj]
    have hm : 0 < wmass p ((univ.filter fun x : Bool × Bool => x.1 = ω.1) ∩
        uncensored C (j + 1)) := by
      refine (p_pos (ω.1, false)).trans_le (single_le_sum (fun x _ => p.nonneg x) ?_)
      simp [uncensored, C]; omega
    exact div_pos hm (hm.trans_le (wmass_mono p.nonneg inter_subset_left))
  have hni : NoInformativeSwitchGivenBaseline p T C Vt L 2 := by
    intro j _ ω
    refine meanIndepOn_of_subset (fun x (hx : x ∈ baselineCell T C Vt j ω) => ?_) _
    have hx' : x.1 = ω.1 := (mem_filter.1 hx).2.2.2
    exact mem_filter.2 ⟨mem_univ _, fun i _ => by rw [L, L, hx']⟩
  refine ⟨hnuc, hpos, ?_, hazard_two⟩
  rw [← (two_period_ipcw).1, ← weightedHazard_one]
  refine weightedHazard_congr_mul _ _ 2 one_ne_zero fun ω hω _ => ?_
  rw [stabilizedWeight_eq_one p.nonneg 2 hni hpos (p_pos ω) hω, one_mul]

end Example₂

end IPCW

end Survival

end CausalInference
