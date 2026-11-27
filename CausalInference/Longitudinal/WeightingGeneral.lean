/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.Dynamic

/-!
# Inverse probability of treatment weighting at a general finite horizon

The inverse probability of treatment weighting identity of Robins, Hernán and Brumback (2000)
for a static regime at any finite number `K` of time points, in the finite setting of
`CausalInference.Longitudinal.Basic`.

`Weighting.lean` already has, at two time points only: the identity `ipw2_static`
(`E[Y(a0, a1)] = ipw2`), the fact `ipw2_one` that unstabilized weights restricted to the regime
have mean one, and the fact `expect_stabilizedWeight2` that stabilized weights have mean one.
This file adds the general-horizon versions of all three, the identification identity for
stabilized weights whose numerator is the probability of the observed treatment path, the chain
rule writing that numerator as the textbook product `Π_t f(A_t | Ā_{t-1})`, and weighting for
dynamic regimes.

## Main definitions

* `Longitudinal.obsProp m A L ω t`: `f(A_t | L̄_t, Ā_{t-1})` evaluated at the observed history
  of `ω`, as a conditional probability given a history event.
* `Longitudinal.ipw m A L a Y`: the weighted sum `E[1{Ā = ā} · Y · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})]`.
* `Longitudinal.stabilizedWeight m A L ω`: `P(Ā = Ā(ω)) / Π_t f(A_t | L̄_t, Ā_{t-1})`, with the
  numerator a conditional probability given the sure event.
* `Longitudinal.pathPrefix A a t`: the event `A_s = a_s` for all `s < t`.
* `Longitudinal.ipwDyn m A L g Y`: the weighted sum
  `E[1{ω follows g} · Y · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})]` for a dynamic regime `g`.

## Main results

* `Longitudinal.ipw_eq_wmass_mul_iceGFormula`, `Longitudinal.ipw_eq_wmass_mul_gFormula`,
  `Longitudinal.ipw_eq_gFormula`: the weighted mean equals the g-formula, as an identity of the
  totalized expressions (each ratio read as `0` when its denominator vanishes) with no causal
  and no positivity hypothesis, proved by induction on `K`. Their probabilistic reading is
  `Model.expect_Ypo_eq_ipw`, under sequential positivity.
* `Longitudinal.Model.expect_Ypo_eq_ipw`: under outcome consistency, sequential exchangeability
  and sequential positivity for `ā`, `E[Y(ā)] = ipw p A L ā Y`.
* `Longitudinal.ipw_one`: under sequential positivity the unstabilized weights restricted to the
  regime have mean one.
* `Longitudinal.ipw_two_eq_ipw2`: at two time points `ipw` is the `ipw2` of `Weighting.lean`.
* `Longitudinal.Model.expect_stabilized_eq`: identification with stabilized weights,
  `E[1{Ā = ā} · SW · Y] = P(Ā = ā) · E[Y(ā)]`, for `SW = P(Ā = Ā(ω)) / Π_t f(A_t | L̄_t, Ā_{t-1})`.
* `Longitudinal.expect_stabilizedWeight`: under sequential positivity for every treatment path of
  positive probability, stabilized weights have mean one.
* `Longitudinal.condProb_path_eq_prod`: the chain rule
  `P(Ā = ā) = Π_t P(A_t = a_t | Ā_{t-1} = ā_{t-1})` for a path of positive mass.
* `Longitudinal.stabilizedWeight_two`: at two time points `stabilizedWeight` is the
  `stabilizedWeight2` of `Weighting.lean`, for every nonnegative mass function.
* `Longitudinal.obsProp_pos`: the observed treatment probabilities are positive at every point
  of positive mass.
* `Longitudinal.ipwDyn_eq_wmass_mul_iceGFormulaDyn`, `Longitudinal.ipwDyn_eq_gFormulaDyn`:
  weighting for a dynamic regime `g` with the indicator of following `g` equals the dynamic
  g-formula, as an identity of the totalized expressions (Hernán and Robins, Technical Point
  21.2); `Longitudinal.expect_eq_ipwDyn` and `Longitudinal.Model.expect_YpoDyn_eq_ipwDyn` are its
  identification readings and `Longitudinal.ipwDyn_one` the mean-one property.
* `Longitudinal.StabilizedDynamicExample.stabilized_ne_dynamic`: with one time point the
  nonstabilized weighted mean gives the true `E[Y^g] = 1/2` while the normalized stabilized mean
  among the followers of `g` gives `3/4`, so stabilized weights cannot be used with dynamic
  regimes (Technical Point 21.2).

## References

* J. M. Robins, M. A. Hernán and B. Brumback, *Marginal structural models and causal inference
  in epidemiology*, Epidemiology 11 (2000).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), section 21.2 and Technical
  Point 21.2.
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
covariate at `t`, of the event that the treatment at `t` takes its observed value. It is defined
at every sample point as the totalized ratio `condProb` (read as `0` when the history event has
zero mass, as can happen at a point of zero mass); at a point of positive mass it is positive
(`obsProp_pos`). -/
noncomputable def obsProp {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (ω : Ω)
    (t : Fin K) : ℝ :=
  condProb m (histL A L (fun s => A s ω) (fun s => L s ω) t) (ev (A t) (A t ω))

omit [Fintype 𝓛] in
/-- At a point of positive mass, under a nonnegative mass function, the observed treatment
probability is positive: the point lies in its own history event and in the intersection of that
event with its observed treatment. -/
theorem obsProp_pos {K : ℕ} {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) {ω : Ω} (hω : 0 < m ω) (t : Fin K) : 0 < obsProp m A L ω t := by
  have hmem : ω ∈ histL A L (fun s => A s ω) (fun s => L s ω) t := by
    simp [histL, hist]
  exact div_pos (wmass_pos_of_mem hm (mem_inter.2 ⟨hmem, by simp⟩) hω)
    (wmass_pos_of_mem hm hmem hω)

/-- The event that the first `t` treatments follow the path `a`: `A_s = a_s` for every time
point `s < t` (a natural number; the sure event at `t = 0`, the event `Ā = ā` at `t = K`). -/
def pathPrefix {K : ℕ} (A : Fin K → Ω → 𝒜) (a : Fin K → 𝒜) (t : ℕ) : Finset Ω :=
  univ.filter fun ω => ∀ s : Fin K, (s : ℕ) < t → A s ω = a s

omit [DecidableEq Ω] in
/-- No treatment is constrained before time `0`. -/
theorem pathPrefix_zero {K : ℕ} (A : Fin K → Ω → 𝒜) (a : Fin K → 𝒜) :
    pathPrefix A a 0 = univ := by
  ext ω; simp [pathPrefix]

/-- One more time point adds the constraint `A_t = a_t`. -/
theorem pathPrefix_succ {K : ℕ} (A : Fin K → Ω → 𝒜) (a : Fin K → 𝒜) (t : Fin K) :
    pathPrefix A a (t + 1) = pathPrefix A a t ∩ ev (A t) (a t) := by
  ext ω
  simp only [pathPrefix, mem_filter, mem_univ, true_and, mem_inter, mem_ev]
  constructor
  · intro h
    exact ⟨fun s hs => h s (by omega), h t (by omega)⟩
  · rintro ⟨h, ht⟩ s hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | hs
    · exact h s hs
    · rw [Fin.ext hs]; exact ht

omit [DecidableEq Ω] in
/-- At time `K` the prefix event is the event `Ā = ā`. -/
theorem pathPrefix_K {K : ℕ} (A : Fin K → Ω → 𝒜) (a : Fin K → 𝒜) :
    pathPrefix A a K = univ.filter fun ω => ∀ t, A t ω = a t := by
  ext ω; simp [pathPrefix]

/-- The chain rule for the treatment path, unnormalized: for a nonnegative mass function, the
total mass times `Π_{t < n} P(A_t = a_t | Ā_{t-1} = ā_{t-1})` is the mass of the event that the
first `n` treatments follow `a`, for every `n ≤ K`. No positivity is needed and no `0/0`
convention carries it: each step multiplies the mass of `Ā_{t-1} = ā_{t-1}` by the conditional
probability given that event, which is the mass of the next prefix event also when the first
mass is `0` (`wmass_mul_condProb`). -/
theorem wmass_univ_mul_prod_condProb {K : ℕ} {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω)
    (A : Fin K → Ω → 𝒜) (a : Fin K → 𝒜) :
    ∀ n, n ≤ K → wmass m univ * ∏ i ∈ range n, (if h : i < K then
      condProb m (pathPrefix A a i) (ev (A ⟨i, h⟩) (a ⟨i, h⟩)) else 1) =
        wmass m (pathPrefix A a n)
  | 0, _ => by rw [prod_range_zero, mul_one, pathPrefix_zero]
  | n + 1, hn => by
    have hn' : n < K := by omega
    rw [prod_range_succ, ← mul_assoc, wmass_univ_mul_prod_condProb hm A a n (by omega)]
    simp only [hn', ↓reduceDIte]
    rw [wmass_mul_condProb hm]
    exact congrArg (wmass m) (pathPrefix_succ A a ⟨n, hn'⟩).symm

/-- **The chain rule for the probability of a treatment path.** For a nonnegative mass function
and a treatment path `a` of positive mass,
`P(Ā = ā) = Π_{t < K} P(A_t = a_t | Ā_{t-1} = ā_{t-1})`, where `P(Ā = ā)` is the conditional
probability given the sure event (the numerator of `stabilizedWeight`). Every factor conditions
on an event `Ā_{t-1} = ā_{t-1}` that contains `Ā = ā` and so has positive mass. -/
theorem condProb_path_eq_prod {K : ℕ} {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (A : Fin K → Ω → 𝒜)
    (a : Fin K → 𝒜) (hpos : 0 < wmass m (univ.filter fun ω => ∀ t, A t ω = a t)) :
    condProb m univ (univ.filter fun ω => ∀ t, A t ω = a t) =
      ∏ t : Fin K, condProb m (pathPrefix A a t) (ev (A t) (a t)) := by
  have hU : 0 < wmass m univ := hpos.trans_le (wmass_mono hm (subset_univ _))
  have h := wmass_univ_mul_prod_condProb hm A a K le_rfl
  rw [pathPrefix_K, ← Fin.prod_univ_eq_prod_range] at h
  simp only [Fin.is_lt, ↓reduceDIte, Fin.eta] at h
  rw [condProb, univ_inter, ← h]
  field_simp

omit [Fintype 𝓛] in
/-- The inverse probability of treatment weighted sum for the static regime `a`:
`E[1{Ā = ā} · Y · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})]` under the mass function `m` (unnormalized:
for a probability mass function it is the weighted mean). -/
noncomputable def ipw {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) (Y : Ω → ℝ) : ℝ :=
  wsum m univ fun ω => (if ∀ t, A t ω = a t then 1 else 0) * (Y ω / ∏ t, obsProp m A L ω t)

omit [Fintype 𝓛] in
/-- The stabilized weight at a general horizon: the probability `P(Ā = Ā(ω))` of the observed
treatment path of `ω` (the conditional probability of that path given the sure event, so that
the weight does not change when the mass function is rescaled), divided by the product
`Π_t f(A_t | L̄_t, Ā_{t-1})` of the observed treatment probabilities (`obsProp`). By the chain rule
(`condProb_path_eq_prod`) the numerator is the textbook product `Π_t f(A_t | Ā_{t-1})` on every
path of positive mass. At two time points it is `stabilizedWeight2` (`stabilizedWeight_two`). The
ratios are totalized: they are meaningful for a mass function of positive total mass at a point
of positive mass (`obsProp_pos`). -/
noncomputable def stabilizedWeight {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (ω : Ω) : ℝ :=
  condProb m univ (univ.filter fun ω' => ∀ t, A t ω' = A t ω) / ∏ t, obsProp m A L ω t

omit [Fintype 𝓛] in
/-- **At two time points the stabilized weight is `stabilizedWeight2`**, for every nonnegative
mass function (normalized or not): the numerator `P(A0 = a0, A1 = a1)` is
`P(A0 = a0) · P(A1 = a1 | A0 = a0)`, also when `P(A0 = a0) = 0` (then both sides are `0` by
nonnegativity, so no `0/0` convention carries the identity), and the denominators are the same
conditional probabilities `prop0 · prop1`. -/
theorem stabilizedWeight_two {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (A : Fin 2 → Ω → 𝒜)
    (L : Fin 2 → Ω → 𝓛) (ω : Ω) :
    stabilizedWeight m A L ω = stabilizedWeight2 m (L 0) (A 0) (L 1) (A 1) ω := by
  have hf : (univ.filter fun ω' => ∀ t, A t ω' = A t ω) = ev (A 0) (A 0 ω) ∩ ev (A 1) (A 1 ω) := by
    ext ω'; simp [Fin.forall_fin_two]
  have hnum : condProb m univ (ev (A 0) (A 0 ω)) * condProb m (ev (A 0) (A 0 ω)) (ev (A 1) (A 1 ω))
      = condProb m univ (ev (A 0) (A 0 ω) ∩ ev (A 1) (A 1 ω)) := by
    rw [condProb, univ_inter, div_mul_eq_mul_div, wmass_mul_condProb hm, condProb, univ_inter]
  rw [stabilizedWeight, stabilizedWeight2, hf, hnum, Fin.prod_univ_two, obsProp, obsProp,
    histL_two_zero, histL_two_one, prop0, prop1]

omit [Fintype 𝓛] in
/-- At a point with first covariate `l0` and first treatment `a0`, the observed treatment
probability at time `0` is `P(A_0 = a0 | L_0 = l0)`. -/
theorem obsProp_zero_eq {K : ℕ} {m : Ω → ℝ} (A : Fin (K + 1) → Ω → 𝒜) (L : Fin (K + 1) → Ω → 𝓛)
    {ω : Ω} {l0 : 𝓛} {a0 : 𝒜} (hL0 : L 0 ω = l0) (hA0 : A 0 ω = a0) :
    obsProp m A L ω 0 = condProb m (ev (L 0) l0) (ev (A 0) a0) := by
  simp [obsProp, histL, hL0, hA0]

omit [Fintype 𝓛] in
/-- At a point with first covariate `l0` and first treatment `a0`, the observed treatment
probability at time `t + 1` is the observed treatment probability at time `t` of the shifted
model under the mass function restricted to `L_0 = l0, A_0 = a0`. -/
theorem obsProp_succ_eq {K : ℕ} {m : Ω → ℝ} (A : Fin (K + 1) → Ω → 𝒜) (L : Fin (K + 1) → Ω → 𝓛)
    {ω : Ω} {l0 : 𝓛} {a0 : 𝒜} (hL0 : L 0 ω = l0) (hA0 : A 0 ω = a0) (t : Fin K) :
    obsProp m A L ω t.succ =
      obsProp (restrict m (ev (L 0) l0 ∩ ev (A 0) a0)) (Fin.tail A) (Fin.tail L) ω t := by
  have hc : (fun s => L s ω) = Fin.cons (L 0 ω) (fun s : Fin K => L s.succ ω) :=
    (Fin.cons_self_tail _).symm
  rw [obsProp, hc, histL_cons_succ, hL0, hA0, ← condProb_restrict]
  rfl

/-- Under a mass function of total mass zero the totalized recursive g-formula expression is
`0`: with no time points it is a conditional mean given the sure event, and otherwise every term
of the outer sum carries the factor `P(L_0 = l) = wmass m (ev (L 0) l) / wmass m univ`, whose
denominator is the vanishing total mass. The inner ratios need not have zero denominators (a
signed mass function can give masses `1` and `-1` to two baseline strata). A proof device only:
it carries no probabilistic meaning. -/
private theorem iceGFormula_eq_zero_of_wmass_univ_eq_zero {m : Ω → ℝ} (h : wmass m univ = 0) :
    ∀ (K : ℕ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (Y : Ω → ℝ),
      iceGFormula K m A L a Y = 0
  | 0, _, _, _, _ => by rw [iceGFormula, condMean, h, div_zero]
  | K + 1, _, _, _, _ => by
    rw [iceGFormula]
    exact sum_eq_zero fun l _ => by rw [condProb, h, div_zero, zero_mul]

/-- **Inverse probability weighting equals the recursive g-formula**, as an identity of the
totalized expressions with no causal hypothesis and no positivity hypothesis: for every
nonnegative mass function `m`, the weighted sum `ipw m A L a Y` is the total mass times
`iceGFormula K m A L a Y`, every ratio on either side being read as `0` when its denominator
vanishes. On a block whose history event has zero mass both sides vanish. This is an algebraic
identity only; its probabilistic reading is `Model.expect_Ypo_eq_ipw`. The proof is by induction
on `K`, generalizing over the mass function: conditioning on the first time point is restriction
of `m`. -/
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
      have hp0 : obsProp m A L ω 0 = c0 := obsProp_zero_eq A L hL0 hA0
      have hps : ∀ t : Fin K, obsProp m A L ω t.succ =
          obsProp (restrict m E) (Fin.tail A) (Fin.tail L) ω t := obsProp_succ_eq A L hL0 hA0
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
causal hypothesis and no positivity hypothesis, as an identity of the totalized expressions. -/
theorem ipw_eq_wmass_mul_gFormula {K : ℕ} {m : Ω → ℝ} (hm : ∀ ω, 0 ≤ m ω) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (a : Fin K → 𝒜) (Y : Ω → ℝ) :
    ipw m A L a Y = wmass m univ * gFormula m A L a Y := by
  rw [ipw_eq_wmass_mul_iceGFormula K hm, gFormula_eq_iceGFormula]

/-- For a finite probability distribution, the weighted mean `ipw p A L a Y` equals the
g-formula `gFormula p A L a Y`, whether or not any causal assumption holds, as an identity of the
totalized expressions (each ratio read as `0` when its denominator vanishes). Without sequential
positivity neither side need be a meaningful conditional quantity; `Model.expect_Ypo_eq_ipw` is
the identification statement. -/
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

omit [DecidableEq Ω] in
/-- A weighted sum of an indicator times a function is the weighted sum over the event. -/
theorem wsum_ite_one_mul {m : Ω → ℝ} (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    wsum m univ (fun ω => (if P ω then 1 else 0) * f ω) = wsum m (univ.filter P) f := by
  rw [wsum, wsum, sum_filter]
  exact sum_congr rfl fun ω _ => by split_ifs <;> simp

omit [Fintype 𝓛] in
/-- **Stabilized weights have mean one at a general horizon.** If sequential positivity holds
for every static regime `ā` that occurs with positive probability, then `E[SW] = 1` for the
stabilized weight `SW = P(Ā = Ā(ω)) / Π_t f(A_t | L̄_t, Ā_{t-1})` (`stabilizedWeight`). -/
theorem expect_stabilizedWeight [Finite 𝒜] [Finite 𝓛] {K : ℕ} (p : FiniteDist Ω)
    (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (hpos : ∀ a : Fin K → 𝒜, 0 < p.prob (univ.filter fun ω => ∀ t, A t ω = a t) →
      ∀ (l : Fin K → 𝓛) (t : Fin K), 0 < wmass p (histL A L a l t) →
        0 < wmass p (histL A L a l t ∩ ev (A t) (a t))) :
    p.expect (stabilizedWeight p A L) = 1 := by
  have : Fintype 𝒜 := Fintype.ofFinite 𝒜
  have h1 : wmass p univ = 1 := p.sum_eq_one
  have hexp : p.expect (stabilizedWeight p A L) = wsum p univ (stabilizedWeight p A L) := rfl
  have hev : ∀ a : Fin K → 𝒜, ev (fun ω t => A t ω) a = univ.filter fun ω => ∀ t, A t ω = a t :=
    fun a => by ext ω; simp [funext_iff]
  rw [hexp, ← h1, wsum_eq_sum_ev _ (fun ω t => A t ω), wmass_eq_sum_ev _ (fun ω t => A t ω)]
  refine sum_congr rfl fun a _ => ?_
  rw [univ_inter, hev]
  rcases (wmass_nonneg p.nonneg (univ.filter fun ω => ∀ t, A t ω = a t)).eq_or_lt with h0 | h0
  · rw [wsum_eq_zero_of_wmass_eq_zero p.nonneg h0.symm, ← h0]
  have hone := ipw_one p A L a (hpos a h0)
  rw [ipw, wsum_ite_one_mul] at hone
  have hsw : wsum p (univ.filter fun ω => ∀ t, A t ω = a t) (stabilizedWeight p A L) =
      wmass p (univ.filter fun ω => ∀ t, A t ω = a t) *
        wsum p (univ.filter fun ω => ∀ t, A t ω = a t)
          (fun ω => 1 / ∏ t, obsProp p A L ω t) := by
    rw [wsum, wsum, mul_sum]
    refine sum_congr rfl fun ω hω => ?_
    have hω' : ∀ t, A t ω = a t := (mem_filter.1 hω).2
    have hf : (univ.filter fun ω' => ∀ t, A t ω' = A t ω) =
        univ.filter fun ω' => ∀ t, A t ω' = a t := by
      simp only [hω']
    rw [stabilizedWeight, hf, condProb, univ_inter, h1]
    ring
  rw [hsw, hone, mul_one]


section DynamicWeighting

/-! ### Weighting for dynamic regimes -/

omit [Fintype Ω] [DecidableEq Ω] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Following a dynamic regime is decidable. -/
instance DynamicRegime.decidableFollows {K : ℕ} (g : DynamicRegime K 𝒜 𝓛) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (ω : Ω) : Decidable (g.Follows A L ω) :=
  decidable_of_iff _ (g.follows_iff A L ω).symm

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq 𝒜] [Fintype 𝓛] [DecidableEq 𝓛] in
/-- Following a regime with `K + 1` time points is following its first rule and then the regime
`g.tailRegime l0` of the remaining time points, for the observed first covariate `l0`. -/
theorem follows_succ_iff {K : ℕ} (g : DynamicRegime (K + 1) 𝒜 𝓛) (A : Fin (K + 1) → Ω → 𝒜)
    (L : Fin (K + 1) → Ω → 𝓛) (ω : Ω) :
    g.Follows A L ω ↔ A 0 ω = g.headRule (L 0 ω) ∧
      (g.tailRegime (L 0 ω)).Follows (Fin.tail A) (Fin.tail L) ω := by
  rw [DynamicRegime.follows_iff, DynamicRegime.follows_iff, Fin.forall_fin_succ]
  have hc : (fun s => L s ω) = Fin.cons (L 0 ω) (fun s : Fin K => L s.succ ω) :=
    (Fin.cons_self_tail _).symm
  rw [hc, DynamicRegime.path_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

omit [Fintype 𝓛] in
/-- The inverse probability weighted sum for the dynamic regime `g` (Hernán and Robins,
Technical Point 21.2): `E[1{ω follows g} · Y · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})]` under the mass
function `m` (unnormalized), with the nonstabilized weights of the observed treatments. -/
noncomputable def ipwDyn {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) (Y : Ω → ℝ) : ℝ :=
  wsum m univ fun ω => (if g.Follows A L ω then 1 else 0) * (Y ω / ∏ t, obsProp m A L ω t)

omit [Fintype 𝓛] in
/-- For a static regime seen as a dynamic regime, the dynamic weighted sum is `ipw`. -/
theorem ipwDyn_ofStatic {K : ℕ} (m : Ω → ℝ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (a : Fin K → 𝒜) (Y : Ω → ℝ) :
    ipwDyn m A L (DynamicRegime.ofStatic a) Y = ipw m A L a Y := by
  simp only [ipwDyn, ipw, DynamicRegime.follows_iff, DynamicRegime.path_ofStatic]

/-- Under a mass function of total mass zero the totalized recursive dynamic g-formula expression
is `0`, for the reason given at `iceGFormula_eq_zero_of_wmass_univ_eq_zero`. A proof device
only. -/
private theorem iceGFormulaDyn_eq_zero_of_wmass_univ_eq_zero {m : Ω → ℝ}
    (h : wmass m univ = 0) :
    ∀ (K : ℕ) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (g : DynamicRegime K 𝒜 𝓛) (Y : Ω → ℝ),
      iceGFormulaDyn K m A L g Y = 0
  | 0, _, _, _, _ => by rw [iceGFormulaDyn, condMean, h, div_zero]
  | K + 1, _, _, _, _ => by
    rw [iceGFormulaDyn]
    exact sum_eq_zero fun l _ => by rw [condProb, h, div_zero, zero_mul]

/-- **Inverse probability weighting for a dynamic regime equals the recursive dynamic
g-formula**, as an identity of the totalized expressions with no causal and no positivity
hypothesis: for every nonnegative mass function `m`, `ipwDyn m A L g Y` is the total mass times
`iceGFormulaDyn K m A L g Y`. Its probabilistic reading is `expect_eq_ipwDyn`. The proof is the
induction of `ipw_eq_wmass_mul_iceGFormula`, with `g.tailRegime` for the remaining time
points. -/
theorem ipwDyn_eq_wmass_mul_iceGFormulaDyn : ∀ (K : ℕ) {m : Ω → ℝ} (_hm : ∀ ω, 0 ≤ m ω)
    (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛) (g : DynamicRegime K 𝒜 𝓛) (Y : Ω → ℝ),
    ipwDyn m A L g Y = wmass m univ * iceGFormulaDyn K m A L g Y
  | 0, m, hm, A, L, g, Y => by
    have hf : ∀ ω, g.Follows A L ω := fun _ t => t.elim0
    simp only [ipwDyn, iceGFormulaDyn, hf, ite_true, univ_eq_empty, prod_empty, div_one,
      one_mul]
    rcases (wmass_nonneg hm univ).eq_or_lt with h | h
    · rw [condMean, ← h, zero_mul]
      exact wsum_eq_zero_of_wmass_eq_zero hm h.symm Y
    · exact (wmass_mul_condMean h.ne' Y).symm
  | K + 1, m, hm, A, L, g, Y => by
    rw [iceGFormulaDyn, mul_sum, ipwDyn, wsum_eq_sum_ev univ (L 0)]
    refine sum_congr rfl fun l0 _ => ?_
    rw [univ_inter]
    set E := ev (L 0) l0 ∩ ev (A 0) (g.headRule l0) with hE
    set c0 := condProb m (ev (L 0) l0) (ev (A 0) (g.headRule l0)) with hc0
    have h1 : wsum m (ev (L 0) l0) (fun ω => (if g.Follows A L ω then 1 else 0) *
        (Y ω / ∏ t, obsProp m A L ω t)) = wsum m E (fun ω => (if g.Follows A L ω then 1 else 0) *
        (Y ω / ∏ t, obsProp m A L ω t)) := by
      rw [hE, wsum, wsum, ← sum_ite_mem]
      refine sum_congr rfl fun ω hω => ?_
      by_cases h : ω ∈ ev (A 0) (g.headRule l0)
      · simp only [h, ite_true]
      · have hL0 : L 0 ω = l0 := mem_ev.1 hω
        have ht : ¬ g.Follows A L ω := fun ht =>
          h (mem_ev.2 (by rw [← hL0]; exact ((follows_succ_iff g A L ω).1 ht).1))
        simp only [h, ht, ite_false, zero_mul, mul_zero]
    have h2 : wsum m E (fun ω => (if g.Follows A L ω then 1 else 0) *
        (Y ω / ∏ t, obsProp m A L ω t)) =
        c0⁻¹ * ipwDyn (restrict m E) (Fin.tail A) (Fin.tail L) (g.tailRegime l0) Y := by
      rw [ipwDyn, wsum_restrict, inter_univ, wsum, wsum, mul_sum]
      refine sum_congr rfl fun ω hω => ?_
      have hω' := hω
      simp only [hE, mem_inter, mem_ev] at hω'
      obtain ⟨hL0, hA0⟩ := hω'
      have hind : g.Follows A L ω ↔ (g.tailRegime l0).Follows (Fin.tail A) (Fin.tail L) ω := by
        rw [follows_succ_iff, hL0]
        exact ⟨fun h => h.2, fun h => ⟨hA0, h⟩⟩
      have hp0 : obsProp m A L ω 0 = c0 := obsProp_zero_eq A L hL0 hA0
      have hps : ∀ t : Fin K, obsProp m A L ω t.succ =
          obsProp (restrict m E) (Fin.tail A) (Fin.tail L) ω t := obsProp_succ_eq A L hL0 hA0
      simp only [hind, Fin.prod_univ_succ, hp0, hps]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [h1, h2, ipwDyn_eq_wmass_mul_iceGFormulaDyn K (restrict_nonneg hm E), wmass_restrict,
      inter_univ]
    rcases (wmass_nonneg hm E).eq_or_lt with h0 | h0
    · rw [iceGFormulaDyn_eq_zero_of_wmass_univ_eq_zero (by rw [wmass_restrict, inter_univ, h0])]
      simp
    have hL : 0 < wmass m (ev (L 0) l0) := h0.trans_le (wmass_mono hm inter_subset_left)
    have hU : 0 < wmass m univ := hL.trans_le (wmass_mono hm (subset_univ _))
    rw [hc0, condProb, condProb, univ_inter, ← hE]
    field_simp

/-- For a finite probability distribution, the dynamic weighted mean equals the dynamic
g-formula, as an identity of the totalized expressions with no causal hypothesis. -/
theorem ipwDyn_eq_gFormulaDyn {K : ℕ} (p : FiniteDist Ω) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (g : DynamicRegime K 𝒜 𝓛) (Y : Ω → ℝ) :
    ipwDyn p A L g Y = gFormulaDyn p A L g Y := by
  have h1 : wmass p univ = 1 := p.sum_eq_one
  rw [ipwDyn_eq_wmass_mul_iceGFormulaDyn K p.nonneg, h1, one_mul, gFormulaDyn_eq_iceGFormulaDyn]

omit [Fintype 𝓛] in
/-- **Inverse probability weighting for a dynamic regime** (Hernán and Robins, Technical Point
21.2). Under consistency along `g` (an individual who follows `g` has `Y = Y^g`), sequential
exchangeability for `Y^g` along `g` and sequential positivity for `g`,
`E[Y^g] = E[1{ω follows g} · Y · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})]`. -/
theorem expect_eq_ipwDyn [Finite 𝓛] {K : ℕ} (p : FiniteDist Ω) (A : Fin K → Ω → 𝒜)
    (L : Fin K → Ω → 𝓛) (Y : Ω → ℝ) (g : DynamicRegime K 𝒜 𝓛) (Yg : Ω → ℝ)
    (hcons : ∀ ω, g.Follows A L ω → Y ω = Yg ω) (hex : SeqExchangeableDyn p A L g Yg)
    (hpos : SeqPositiveDyn p A L g) :
    p.expect Yg = ipwDyn p A L g Y := by
  have : Fintype 𝓛 := Fintype.ofFinite 𝓛
  rw [ipwDyn_eq_gFormulaDyn]
  exact (expect_eq_gFormulaDyn p A L Y g Yg hcons hex hpos).1

omit [Fintype 𝓛] in
/-- **Nonstabilized weights for a dynamic regime have mean one** among its followers: under
sequential positivity for `g`, `E[1{ω follows g} · Π_t 1 / f(A_t | L̄_t, Ā_{t-1})] = 1`. -/
theorem ipwDyn_one [Finite 𝓛] {K : ℕ} (p : FiniteDist Ω) (A : Fin K → Ω → 𝒜) (L : Fin K → Ω → 𝓛)
    (g : DynamicRegime K 𝒜 𝓛) (hpos : SeqPositiveDyn p A L g) :
    ipwDyn p A L g (fun _ => 1) = 1 := by
  rw [← expect_eq_ipwDyn p A L _ g (fun _ => 1) (fun _ _ => rfl)
    (fun _ _ => meanIndepOn_const _ _ _ 1) hpos]
  exact p.expect_const 1

omit [Fintype 𝓛] in
/-- **Inverse probability weighting for a dynamic regime in a model.** Under nonanticipation,
consistency, sequential exchangeability for the model-level potential outcome `Y^g` along `g`
and sequential positivity for `g`, `E[Y^g] = ipwDyn p A L g Y`. -/
theorem Model.expect_YpoDyn_eq_ipwDyn [Inhabited 𝒜] [Finite 𝓛] {K : ℕ} (M : Model Ω K 𝒜 𝓛)
    (hna : M.Nonanticipating) (hcons : M.Consistent) (g : DynamicRegime K 𝒜 𝓛)
    (hex : SeqExchangeableDyn M.p M.A M.L g (M.YpoDyn g)) (hpos : SeqPositiveDyn M.p M.A M.L g) :
    M.p.expect (M.YpoDyn g) = ipwDyn M.p M.A M.L g M.Y := by
  have : Fintype 𝓛 := Fintype.ofFinite 𝓛
  rw [ipwDyn_eq_gFormulaDyn]
  exact Model.expect_YpoDyn_eq_gFormulaDyn hna hcons g hex hpos

end DynamicWeighting

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

omit [Fintype 𝓛] in
/-- **Identification with stabilized weights at a general finite horizon.** In a longitudinal
model, under outcome consistency, sequential exchangeability (mean independence form) and
sequential positivity for the static regime `ā`,
`E[1{Ā = ā} · SW · Y] = P(Ā = ā) · E[Y(ā)]` for the stabilized weight
`SW = P(Ā = Ā(ω)) / Π_{t < K} f(A_t | L̄_t, Ā_{t-1})` (`stabilizedWeight`). On the regime the
numerator is the constant `P(Ā = ā)`, so this is `expect_Ypo_eq_ipw` scaled by that constant. -/
theorem expect_stabilized_eq [Finite 𝓛] (a : Fin K → 𝒜) (hcons : M.OutcomeConsistent a)
    (hex : M.SeqExchangeable a) (hpos : M.SeqPositive a) :
    M.p.expect (fun ω => (if ∀ t, M.A t ω = a t then 1 else 0) *
      (stabilizedWeight M.p M.A M.L ω * M.Y ω)) =
      M.p.prob (univ.filter fun ω => ∀ t, M.A t ω = a t) * M.p.expect (M.Ypo a) := by
  rw [M.expect_Ypo_eq_ipw a hcons hex hpos, ipw, wsum, FiniteDist.expect, FiniteDist.prob,
    mul_sum]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : ∀ t, M.A t ω = a t
  · have hf : (univ.filter fun ω' => ∀ t, M.A t ω' = M.A t ω) =
        univ.filter fun ω' => ∀ t, M.A t ω' = a t := by
      simp only [h]
    have h1 : wmass M.p univ = 1 := M.p.sum_eq_one
    rw [stabilizedWeight, hf, condProb, univ_inter, h1, div_one]
    simp only [h, implies_true, ↓reduceIte, wmass, div_eq_mul_inv]
    ring
  · simp [h]

end Model

namespace StabilizedDynamicExample

/-! ### Stabilized weights fail for dynamic regimes -/

/-- The sample space: a point is `(l, a)`, the covariate and the treatment. -/
abbrev Sample := Bool × Bool

/-- The covariate is fair and the treatment is independent of it with `P(A = true) = 3/4`. -/
noncomputable def p : FiniteDist Sample where
  mass ω := if ω.2 then 3 / 8 else 1 / 8
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp [Fintype.sum_prod_type]; norm_num

/-- The covariate at the single time point. -/
def L : Fin 1 → Sample → Bool := fun _ ω => ω.1

/-- The treatment at the single time point. -/
def A : Fin 1 → Sample → Bool := fun _ ω => ω.2

/-- The regime "treat if and only if the covariate is `true`". -/
def g : DynamicRegime 1 Bool Bool := fun t l _ => l (Fin.last t)

/-- The outcome `Y = L`. It does not depend on the treatment, so `Y^g = Y` under every regime. -/
noncomputable def Y (ω : Sample) : ℝ := if ω.1 then 1 else 0

/-- Following `g` is receiving the treatment equal to the covariate. -/
theorem follows_iff (ω : Sample) : g.Follows A L ω ↔ ω.2 = ω.1 := by
  simp [DynamicRegime.Follows, g, A, L]

/-- The observed treatment probabilities are `3/4` for the treated and `1/4` for the
untreated. -/
theorem obsProp_eq (ω : Sample) : obsProp p A L ω 0 = if ω.2 then 3 / 4 else 1 / 4 := by
  obtain ⟨l, a⟩ := ω
  cases l <;> cases a <;>
  simp only [obsProp, condProb, histL, hist, wmass, ev, filter_inter, inter_filter, univ_inter,
    filter_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool] <;>
  norm_num [p, A, L]

/-- The treatment is independent of the covariate, so every stabilized weight is `1`. -/
theorem stabilizedWeight_eq_one (ω : Sample) : stabilizedWeight p A L ω = 1 := by
  rw [stabilizedWeight, Fin.prod_univ_one, obsProp_eq]
  obtain ⟨l, a⟩ := ω
  cases l <;> cases a <;>
  norm_num [condProb, wmass, sum_filter, Fintype.sum_prod_type, Fin.forall_fin_one, p, A]

/-- **Stabilized weights cannot be used with dynamic regimes** (Hernán and Robins, Technical
Point 21.2). With one time point, a fair covariate `L`, a treatment independent of `L` with
`P(A = true) = 3/4`, the outcome `Y = L` and the regime `g(L) = L`: the true value is
`E[Y^g] = E[Y] = 1/2`, which the nonstabilized weighted mean `ipwDyn` reproduces, while the
normalized stabilized mean among the followers of `g`,
`E[1{follows g} · SW · Y] / E[1{follows g} · SW]`, is `3/4`. -/
theorem stabilized_ne_dynamic :
    p.expect Y = 1 / 2 ∧ ipwDyn p A L g Y = 1 / 2 ∧
      wsum p univ (fun ω => (if g.Follows A L ω then 1 else 0) *
          (stabilizedWeight p A L ω * Y ω)) /
        wsum p univ (fun ω => (if g.Follows A L ω then 1 else 0) * stabilizedWeight p A L ω) =
        3 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [FiniteDist.expect, Fintype.sum_prod_type, p, Y]
  · simp only [ipwDyn, wsum, Fin.prod_univ_one, obsProp_eq, follows_iff,
      Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num [p, Y]
  · simp only [wsum, stabilizedWeight_eq_one, follows_iff, Fintype.sum_prod_type,
      Fintype.sum_bool]
    norm_num [p, Y]

end StabilizedDynamicExample

end Longitudinal

end CausalInference
