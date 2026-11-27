/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Bridge

/-!
# Inverse probability of treatment weighting at a general finite horizon

The inverse probability of treatment weighting identity of Robins, Hernán and Brumback (2000)
for a static regime at any finite number `K` of time points, in the finite setting of
`CausalInference.Longitudinal.Basic`.

`Weighting.lean` already has, at two time points only: the identity `ipw2_static`
(`E[Y(a0, a1)] = ipw2`), the fact `ipw2_one` that unstabilized weights restricted to the regime
have mean one, and the fact `expect_stabilizedWeight2` that stabilized weights have mean one.
This file adds the general-horizon versions of the first two; stabilized weights at a general
horizon are not treated.

## Main definitions

* `Longitudinal.obsProp m A L ω t`: `f(A_t | L̄_t, Ā_{t-1})` evaluated at the observed history
  of `ω`, as a conditional probability given a history event.
* `Longitudinal.ipw m A L a Y`: the weighted sum `E[1{Ā = ā} · Y · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})]`.

## Main results

* `Longitudinal.ipw_eq_wmass_mul_iceGFormula`, `Longitudinal.ipw_eq_wmass_mul_gFormula`,
  `Longitudinal.ipw_eq_gFormula`: the weighted mean equals the g-formula, as an identity with no
  causal hypothesis and no positivity hypothesis (on a block whose history event has zero mass
  both sides vanish), proved by induction on `K`.
* `Longitudinal.Model.expect_Ypo_eq_ipw`: under outcome consistency, sequential exchangeability
  and sequential positivity for `ā`, `E[Y(ā)] = ipw p A L ā Y`.
* `Longitudinal.ipw_one`: under sequential positivity the unstabilized weights restricted to the
  regime have mean one.
* `Longitudinal.ipw_two_eq_ipw2`: at two time points `ipw` is the `ipw2` of `Weighting.lean`.

## References

* J. M. Robins, M. A. Hernán and B. Brumback, *Marginal structural models and causal inference
  in epidemiology*, Epidemiology 11 (2000).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), section 21.2.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [Fintype 𝓛]
  [DecidableEq 𝓛]

omit [Fintype 𝓛] in
/-- The probability of the observed treatment at time `t` given the observed past,
`P(A_t = A_t(ω) | L̄_t = L̄_t(ω), Ā_{t-1} = Ā_{t-1}(ω))`: the conditional probability, given the
history event of the observed covariate and treatment paths of `ω` up to and including the
covariate at `t`, of the event that the treatment at `t` takes its observed value. -/
noncomputable def obsProp {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (ω : Ω)
    (t : Fin K) : ℝ :=
  condProb m (histL A L (fun s => A s ω) (fun s => L s ω) t) (ev (A t) (A t ω))

omit [Fintype 𝓛] in
/-- The inverse probability of treatment weighted sum for the static regime `a`:
`E[1{Ā = ā} · Y · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})]` under the mass function `m` (unnormalized:
for a probability mass function it is the weighted mean). -/
noncomputable def ipw {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) (Y : Ω → ℝ) : ℝ :=
  wsum m univ fun ω => (if ∀ t, A t ω = a t then 1 else 0) * (Y ω / ∏ t, obsProp m A L ω t)

/-- The recursive g-formula under a mass function of total mass zero is zero. -/
theorem iceGFormula_eq_zero_of_wmass_univ_eq_zero {m : Ω → ℝ} (h : wmass m univ = 0) :
    ∀ (K : ℕ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (Y : Ω → ℝ),
      iceGFormula K m A L a Y = 0
  | 0, _, _, _, _ => by rw [iceGFormula, condMean, h, div_zero]
  | K + 1, _, _, _, _ => by
    rw [iceGFormula]
    exact sum_eq_zero fun l _ => by rw [condProb, h, div_zero, zero_mul]

/-- **Inverse probability weighting equals the recursive g-formula**, as an identity with no
causal hypothesis and no positivity hypothesis: for every nonnegative mass function `m`, the
weighted sum `ipw m A L a Y` is the total mass times `iceGFormula K m A L a Y`. On a block whose
history event has zero mass both sides vanish. The proof is by induction on `K`, generalizing
over the mass function: conditioning on the first time point is restriction of `m`. -/
theorem ipw_eq_wmass_mul_iceGFormula : ∀ (K : ℕ) {m : Ω → ℝ} (_hm : ∀ ω, 0 ≤ m ω)
    (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (Y : Ω → ℝ),
    ipw m A L a Y = wmass m univ * iceGFormula K m A L a Y
  | 0, m, hm, A, L, a, Y => by
    simp only [ipw, iceGFormula, IsEmpty.forall_iff, ite_true, univ_eq_empty, prod_empty,
      div_one, one_mul]
    rcases (wmass_nonneg hm univ).eq_or_lt with h | h
    · rw [condMean, ← h, zero_mul]
      exact wsum_eq_zero_of_wmass_eq_zero hm h.symm Y
    · exact (wmass_mul_condMean h.ne' Y).symm
  | K + 1, m, hm, A, L, a, Y => by
    rw [iceGFormula, mul_sum, ipw, wsum_eq_sum_ev univ (L 0)]
    refine sum_congr rfl fun l0 _ => ?_
    rw [univ_inter]
    set E := ev (L 0) l0 ∩ ev (A 0) (a 0) with hE
    set c0 := condProb m (ev (L 0) l0) (ev (A 0) (a 0)) with hc0
    have h1 : wsum m (ev (L 0) l0) (fun ω => (if ∀ t, A t ω = a t then 1 else 0) *
        (Y ω / ∏ t, obsProp m A L ω t)) = wsum m E (fun ω => (if ∀ t, A t ω = a t then 1 else 0) *
        (Y ω / ∏ t, obsProp m A L ω t)) := by
      rw [hE, wsum, wsum, ← sum_ite_mem]
      refine sum_congr rfl fun ω _ => ?_
      by_cases h : ω ∈ ev (A 0) (a 0)
      · simp only [h, ite_true]
      · have ht : ¬ ∀ t, A t ω = a t := fun ht => h (by simpa using ht 0)
        simp only [h, ht, ite_false, zero_mul, mul_zero]
    have h2 : wsum m E (fun ω => (if ∀ t, A t ω = a t then 1 else 0) *
        (Y ω / ∏ t, obsProp m A L ω t)) =
        c0⁻¹ * ipw (restrict m E) (Fin.tail A) (Fin.tail L) (Fin.tail a) Y := by
      rw [ipw, wsum_restrict, inter_univ, wsum, wsum, mul_sum]
      refine sum_congr rfl fun ω hω => ?_
      have hω' := hω
      simp only [hE, mem_inter, mem_ev] at hω'
      obtain ⟨hL0, hA0⟩ := hω'
      have hind : (∀ t, A t ω = a t) ↔ ∀ t, Fin.tail A t ω = Fin.tail a t := by
        rw [Fin.forall_fin_succ]
        exact ⟨fun h => h.2, fun h => ⟨hA0, h⟩⟩
      have hp0 : obsProp m A L ω 0 = c0 := by
        simp [obsProp, histL, hL0, hA0, hc0]
      have hps : ∀ t : Fin K, obsProp m A L ω t.succ =
          obsProp (restrict m E) (Fin.tail A) (Fin.tail L) ω t := by
        intro t
        have hc : (fun s => L s ω) = Fin.cons (L 0 ω) (fun s : Fin K => L s.succ ω) :=
          (Fin.cons_self_tail _).symm
        rw [obsProp, hc, histL_cons_succ, hL0, hA0, ← condProb_restrict]
        rfl
      simp only [hind, Fin.prod_univ_succ, hp0, hps]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [h1, h2, ipw_eq_wmass_mul_iceGFormula K (restrict_nonneg hm E), wmass_restrict,
      inter_univ]
    rcases (wmass_nonneg hm E).eq_or_lt with h0 | h0
    · rw [iceGFormula_eq_zero_of_wmass_univ_eq_zero (by rw [wmass_restrict, inter_univ, h0])]
      simp
    have hL : 0 < wmass m (ev (L 0) l0) := h0.trans_le (wmass_mono hm inter_subset_left)
    have hU : 0 < wmass m univ := hL.trans_le (wmass_mono hm (subset_univ _))
    rw [hc0, condProb, condProb, univ_inter, ← hE]
    field_simp

/-- Inverse probability weighting equals the total mass times the sum-product g-formula, with no
causal hypothesis and no positivity hypothesis. -/
theorem ipw_eq_wmass_mul_gFormula {K : ℕ} {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (Y : Ω → ℝ) :
    ipw m A L a Y = wmass m univ * gFormula m A L a Y := by
  rw [ipw_eq_wmass_mul_iceGFormula K hm, gFormula_eq_iceGFormula]

/-- For a finite probability distribution, the weighted mean `ipw p A L a Y` equals the
g-formula `gFormula p A L a Y`, whether or not any causal assumption holds. -/
theorem ipw_eq_gFormula {K : ℕ} (p : FiniteDist Ω) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) (Y : Ω → ℝ) :
    ipw p A L a Y = gFormula p A L a Y := by
  have h1 : wmass p univ = 1 := p.sum_eq_one
  rw [ipw_eq_wmass_mul_gFormula p.nonneg, h1, one_mul]

omit [Fintype 𝓛] in
/-- At two time points the general weighted mean is the two time point weighted mean `ipw2`
of `Weighting.lean`, for every nonnegative mass function. -/
theorem ipw_two_eq_ipw2 [Finite 𝓛] {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (A : Fin 2 → Ω → 𝒜)
    (L : Fin 2 → Ω → 𝓛) (a : Fin 2 → 𝒜) (Y : Ω → ℝ) :
    ipw m A L a Y = ipw2 m (L 0) (A 0) (L 1) (A 1) (a 0) (a 1) Y := by
  have : Fintype 𝓛 := Fintype.ofFinite 𝓛
  rw [ipw_eq_wmass_mul_gFormula hm, ipw2_eq_gFormula2_static, gFormula2_eq_wmass_mul_gFormula hm]

omit [Fintype 𝓛] in
/-- **Unstabilized weights have mean one** on the regime, at any finite horizon: if each history
event `L̄_t = l̄_t, Ā_{t-1} = ā_{t-1}` of positive probability keeps positive probability after
adding `A_t = a_t` (sequential positivity for `ā`), then
`E[1{Ā = ā} · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})] = 1`. -/
theorem ipw_one [Finite 𝓛] {K : ℕ} (p : FiniteDist Ω) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜)
    (hpos : ∀ (l : Fin K → 𝓛) (t : Fin K), 0 < wmass p (histL A L a l t) →
      0 < wmass p (histL A L a l t ∩ ev (A t) (a t))) :
    ipw p A L a (fun _ => 1) = 1 := by
  have : Fintype 𝓛 := Fintype.ofFinite 𝓛
  have h1 : wmass p univ = 1 := p.sum_eq_one
  rw [ipw_eq_wmass_mul_iceGFormula K p.nonneg, h1, one_mul,
    ← condMean_eq_iceGFormula K p.nonneg (by rw [h1]; exact one_pos) A L a _
      (fun _ _ => meanIndepOn_const _ _ _ 1) hpos, condMean, wsum_const, h1, one_mul, div_one]

namespace Model

variable {K : ℕ} (M : Model Ω K 𝒜 𝓛)

omit [Fintype 𝓛] in
/-- **The inverse probability of treatment weighting identity at a general finite horizon.** In
a longitudinal model with `K` time points, under outcome consistency, sequential exchangeability
(mean independence form) and sequential positivity for the static regime `ā`,
`E[Y(ā)] = E[1{Ā = ā} · Y · Π_{t < K} 1 / f(A_t | L̄_t, Ā_{t-1})]`. -/
theorem expect_Ypo_eq_ipw [Finite 𝓛] (a : Fin K → 𝒜) (hcons : M.OutcomeConsistent a)
    (hex : M.SeqExchangeable a) (hpos : M.SeqPositive a) :
    M.p.expect (M.Ypo a) = ipw M.p M.A M.L a M.Y := by
  have : Fintype 𝓛 := Fintype.ofFinite 𝓛
  rw [ipw_eq_gFormula, (M.expect_Ypo_eq_gFormula a hcons hex hpos).1]

end Model

end Longitudinal

end CausalInference
