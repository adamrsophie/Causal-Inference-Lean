/-
Copyright (c) 2026 Adam R Sophie. All rights reserved.
Released under the GNU General Public License v3.0 as described in the file LICENSE.
Authors: Adam R Sophie
-/
module

public import CausalInference.Longitudinal.TwoTime

/-!
# Inverse probability of treatment weighting at two time points

The inverse probability of treatment weighting identity of Robins, Hernán and Brumback (2000)
for a static regime at two time points, in the finite setting of
`CausalInference.Longitudinal.Basic`, and the fact that stabilized weights have mean one.

## Main definitions

* `Longitudinal.prop0`, `Longitudinal.prop1`: the treatment probabilities of the observed
  treatments, `P(A0 = A0(ω) | L0 = L0(ω))` and
  `P(A1 = A1(ω) | L0 = L0(ω), A0 = A0(ω), L1 = L1(ω))`.
* `Longitudinal.ipw2`: the weighted mean `E[1{A0 = a0, A1 = a1} Y / (prop0 · prop1)]`.
* `Longitudinal.stabilizedWeight2`: the stabilized weight
  `P(A0 = A0(ω)) P(A1 = A1(ω) | A0 = A0(ω)) / (prop0(ω) · prop1(ω))`.

## Main results

* `Longitudinal.ipw2_static`: under consistency, sequential exchangeability and sequential
  positivity, `E[Y(a0, a1)] = E[1{A0 = a0, A1 = a1} Y / (prop0 · prop1)]`.
* `Longitudinal.ipw2_one`: under sequential positivity the unstabilized weights restricted to
  the regime have mean one.
* `Longitudinal.expect_stabilizedWeight2`: if sequential positivity holds for every regime that
  occurs with positive probability, the stabilized weights have mean one.
* `Longitudinal.ipw2_stabilized_static`: identification with stabilized weights, under the
  hypotheses of `ipw2_static`, `E[1{A0 = a0, A1 = a1} · SW · Y] = P(A0 = a0, A1 = a1) E[Y(a0, a1)]`.
* `Longitudinal.ipw2_eq_gFormula2_static`: `ipw2` equals `gFormula2` as an identity of the
  totalized finite sums, with no hypothesis; `ipw2_static` is its probabilistic reading.

The weighting theorems are derived from the g-formula; their proofs do not use positivity of
the denominators `prop0(ω) · prop1(ω)` beyond the sequential positivity hypothesis.

## References

* J. M. Robins, M. A. Hernán and B. Brumback, *Marginal structural models and causal inference
  in epidemiology*, Epidemiology 11 (2000).
* M. A. Hernán and J. M. Robins, *Causal Inference: What If* (2020), chapter 21.
-/

@[expose] public section

namespace CausalInference

namespace Longitudinal

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {𝒜 𝓛 : Type*} [DecidableEq 𝒜] [DecidableEq 𝓛]

/-- The probability of the observed first treatment given the first covariate,
`P(A0 = A0(ω) | L0 = L0(ω))`. -/
noncomputable def prop0 (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (ω : Ω) : ℝ :=
  condProb m (ev L0 (L0 ω)) (ev A0 (A0 ω))

/-- The probability of the observed second treatment given the past,
`P(A1 = A1(ω) | L0 = L0(ω), A0 = A0(ω), L1 = L1(ω))`. -/
noncomputable def prop1 (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛) (A1 : Ω → 𝒜)
    (ω : Ω) : ℝ :=
  condProb m (ev L0 (L0 ω) ∩ ev A0 (A0 ω) ∩ ev L1 (L1 ω)) (ev A1 (A1 ω))

/-- The inverse probability of treatment weighted mean for the static regime `(a0, a1)`:
`E[1{A0 = a0, A1 = a1} · Y / (P(A0 | L0) · P(A1 | L0, A0, L1))]`. -/
noncomputable def ipw2 (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛) (A1 : Ω → 𝒜)
    (a0 a1 : 𝒜) (Y : Ω → ℝ) : ℝ :=
  wsum m univ fun ω => (if A0 ω = a0 ∧ A1 ω = a1 then 1 else 0) *
    (Y ω / (prop0 m L0 A0 ω * prop1 m L0 A0 L1 A1 ω))

omit [DecidableEq 𝓛] in
/-- A weighted sum of an indicator times a function is the weighted sum over the event. -/
theorem wsum_ite_and {m : Ω → ℝ} (A0 A1 : Ω → 𝒜) (a0 a1 : 𝒜) (g : Ω → ℝ) :
    wsum m univ (fun ω => (if A0 ω = a0 ∧ A1 ω = a1 then 1 else 0) * g ω) =
      wsum m (ev A0 a0 ∩ ev A1 a1) g := by
  unfold wsum
  rw [← univ_inter (ev A0 a0 ∩ ev A1 a1), ← sum_ite_mem]
  refine sum_congr rfl fun ω _ => ?_
  by_cases h : A0 ω = a0 ∧ A1 ω = a1 <;> simp [h]

/-- **The two time point weighted mean equals the two time point g-formula**, for every mass
function and with no causal and no positivity hypothesis, as an identity of the totalized
expressions: every ratio on either side, conditional means, conditional probabilities and
inverse weights, is read as `0` when its denominator vanishes. On a null conditioning event
neither side is a conditional quantity, so this is an algebraic identity only. Its probabilistic
reading is `ipw2_static`, under sequential positivity and a probability mass function. -/
theorem ipw2_eq_gFormula2_static [Fintype 𝓛] (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛)
    (A1 : Ω → 𝒜) (a0 a1 : 𝒜) (Y : Ω → ℝ) :
    ipw2 m L0 A0 L1 A1 a0 a1 Y = gFormula2 m L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) Y := by
  rw [ipw2, wsum_ite_and, wsum_eq_sum_ev _ L0, gFormula2]
  refine sum_congr rfl fun l0 _ => ?_
  rw [wsum_eq_sum_ev _ L1]
  refine sum_congr rfl fun l1 _ => ?_
  have hset : ev A0 a0 ∩ ev A1 a1 ∩ ev L0 l0 ∩ ev L1 l1 =
      ev L0 l0 ∩ ev A0 a0 ∩ ev L1 l1 ∩ ev A1 a1 := by
    ext ω; simp only [mem_inter, mem_ev]; tauto
  rw [hset]
  have hc : wsum m (ev L0 l0 ∩ ev A0 a0 ∩ ev L1 l1 ∩ ev A1 a1)
      (fun ω => Y ω / (prop0 m L0 A0 ω * prop1 m L0 A0 L1 A1 ω)) =
      wsum m (ev L0 l0 ∩ ev A0 a0 ∩ ev L1 l1 ∩ ev A1 a1) Y /
        (condProb m (ev L0 l0) (ev A0 a0) *
          condProb m (ev L0 l0 ∩ ev A0 a0 ∩ ev L1 l1) (ev A1 a1)) := by
    rw [wsum, wsum, sum_div]
    refine sum_congr rfl fun ω hω => ?_
    simp only [mem_inter, mem_ev] at hω
    obtain ⟨⟨⟨hL0, hA0⟩, hL1⟩, hA1⟩ := hω
    rw [prop0, prop1, hL0, hA0, hL1, hA1, mul_div_assoc]
  rw [hc, condMean, condProb, condProb, condProb]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- **The inverse probability of treatment weighting identity at two time points.** Under
consistency, sequential exchangeability for `Y(a0, a1)` and sequential positivity for the static
regime `(a0, a1)`,
`E[Y(a0, a1)] = E[1{A0 = a0, A1 = a1} · Y / (P(A0 = a0 | L0) · P(A1 = a1 | L0, A0, L1))]`. -/
theorem ipw2_static [Finite 𝓛] (p : FiniteDist Ω) {L0 : Ω → 𝓛} {A0 : Ω → 𝒜} {L1 : Ω → 𝓛}
    {A1 : Ω → 𝒜} {Y : Ω → ℝ} {Ypo : 𝒜 → 𝒜 → Ω → ℝ} {a0 a1 : 𝒜}
    (hcons : ∀ ω, A0 ω = a0 → A1 ω = a1 → Y ω = Ypo a0 a1 ω)
    (hex : SeqExchangeable2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) (Ypo a0 a1))
    (hpos : SeqPositive2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1)) :
    p.expect (Ypo a0 a1) = ipw2 p L0 A0 L1 A1 a0 a1 Y := by
  have : Fintype 𝓛 := Fintype.ofFinite 𝓛
  rw [ipw2_eq_gFormula2_static]
  exact gFormula2_eq p.nonneg hcons hex hpos

omit [Fintype Ω] in
/-- A constant is mean independent of every event. -/
theorem meanIndepOn_const (m : Ω → ℝ) (s t : Finset Ω) (c : ℝ) :
    MeanIndepOn m s t (fun _ => c) := by
  rw [MeanIndepOn, wsum_const, wsum_const]; ring

/-- **Unstabilized weights have mean one** on the regime: under sequential positivity for
`(a0, a1)`, `E[1{A0 = a0, A1 = a1} / (P(A0 = a0 | L0) · P(A1 = a1 | L0, A0, L1))] = 1`. -/
theorem ipw2_one [Finite 𝓛] (p : FiniteDist Ω) {L0 : Ω → 𝓛} {A0 : Ω → 𝒜} {L1 : Ω → 𝓛} {A1 : Ω → 𝒜}
    {a0 a1 : 𝒜} (hpos : SeqPositive2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1)) :
    ipw2 p L0 A0 L1 A1 a0 a1 (fun _ => 1) = 1 := by
  rw [← ipw2_static p (Ypo := fun _ _ _ => 1) (fun _ _ _ => rfl)
    ⟨fun _ => meanIndepOn_const _ _ _ 1, fun _ _ => meanIndepOn_const _ _ _ 1⟩ hpos]
  exact p.expect_const 1

/-- The stabilized weight at two time points:
`P(A0 = A0(ω)) · P(A1 = A1(ω) | A0 = A0(ω)) / (prop0(ω) · prop1(ω))`. -/
noncomputable def stabilizedWeight2 (m : Ω → ℝ) (L0 : Ω → 𝓛) (A0 : Ω → 𝒜) (L1 : Ω → 𝓛)
    (A1 : Ω → 𝒜) (ω : Ω) : ℝ :=
  condProb m univ (ev A0 (A0 ω)) * condProb m (ev A0 (A0 ω)) (ev A1 (A1 ω)) /
    (prop0 m L0 A0 ω * prop1 m L0 A0 L1 A1 ω)

/-- **Stabilized weights have mean one.** If sequential positivity holds for every static
regime `(a0, a1)` that occurs with positive probability, then `E[SW] = 1` for the stabilized
weight `SW = P(A0) P(A1 | A0) / (P(A0 | L0) P(A1 | L0, A0, L1))`. -/
theorem expect_stabilizedWeight2 [Finite 𝒜] [Finite 𝓛] (p : FiniteDist Ω) {L0 : Ω → 𝓛} {A0 : Ω → 𝒜}
    {L1 : Ω → 𝓛} {A1 : Ω → 𝒜}
    (hpos : ∀ a0 a1, 0 < p.prob (ev A0 a0 ∩ ev A1 a1) →
      SeqPositive2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1)) :
    p.expect (stabilizedWeight2 p L0 A0 L1 A1) = 1 := by
  have : Fintype 𝒜 := Fintype.ofFinite 𝒜
  have h1 : wmass p univ = 1 := p.sum_eq_one
  have hexp : p.expect (stabilizedWeight2 p L0 A0 L1 A1) =
      wsum p univ (stabilizedWeight2 p L0 A0 L1 A1) := rfl
  rw [hexp, ← h1, wsum_eq_sum_ev _ A0, wmass_eq_sum_ev _ A0]
  refine sum_congr rfl fun a0 _ => ?_
  rw [wsum_eq_sum_ev _ A1, wmass_eq_sum_ev _ A1]
  refine sum_congr rfl fun a1 _ => ?_
  rw [univ_inter]
  rcases (wmass_nonneg p.nonneg (ev A0 a0 ∩ ev A1 a1)).eq_or_lt with h0 | h0
  · rw [wsum_eq_zero_of_wmass_eq_zero p.nonneg h0.symm, ← h0]
  have hA0 : 0 < wmass p (ev A0 a0) := h0.trans_le (wmass_mono p.nonneg inter_subset_left)
  have hone := ipw2_one p (hpos a0 a1 h0)
  rw [ipw2, wsum_ite_and] at hone
  have hsw : wsum p (ev A0 a0 ∩ ev A1 a1) (stabilizedWeight2 p L0 A0 L1 A1) =
      wmass p (ev A0 a0 ∩ ev A1 a1) *
        wsum p (ev A0 a0 ∩ ev A1 a1)
          (fun ω => 1 / (prop0 p L0 A0 ω * prop1 p L0 A0 L1 A1 ω)) := by
    rw [wsum, wsum, mul_sum]
    refine sum_congr rfl fun ω hω => ?_
    simp only [mem_inter, mem_ev] at hω
    rw [stabilizedWeight2, hω.1, hω.2, condProb, condProb, univ_inter, h1]
    field_simp
  rw [hsw, hone, mul_one]


/-- **Identification with stabilized weights at two time points.** Under consistency, sequential
exchangeability for `Y(a0, a1)` and sequential positivity for the static regime `(a0, a1)`,
`E[1{A0 = a0, A1 = a1} · SW · Y] = P(A0 = a0, A1 = a1) · E[Y(a0, a1)]` for the stabilized weight
`SW = P(A0) P(A1 | A0) / (P(A0 | L0) P(A1 | L0, A0, L1))`. On the regime the numerator of `SW` is
the constant `P(A0 = a0, A1 = a1)`, so this is `ipw2_static` scaled by that constant; when the
regime has probability zero both sides are `0` because the indicator vanishes almost surely. -/
theorem ipw2_stabilized_static [Finite 𝓛] (p : FiniteDist Ω) {L0 : Ω → 𝓛} {A0 : Ω → 𝒜}
    {L1 : Ω → 𝓛} {A1 : Ω → 𝒜} {Y : Ω → ℝ} {Ypo : 𝒜 → 𝒜 → Ω → ℝ} {a0 a1 : 𝒜}
    (hcons : ∀ ω, A0 ω = a0 → A1 ω = a1 → Y ω = Ypo a0 a1 ω)
    (hex : SeqExchangeable2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1) (Ypo a0 a1))
    (hpos : SeqPositive2 p L0 A0 L1 A1 (fun _ => a0) (fun _ _ => a1)) :
    p.expect (fun ω => (if A0 ω = a0 ∧ A1 ω = a1 then 1 else 0) *
      (stabilizedWeight2 p L0 A0 L1 A1 ω * Y ω)) =
      p.prob (ev A0 a0 ∩ ev A1 a1) * p.expect (Ypo a0 a1) := by
  have h1 : wmass p univ = 1 := p.sum_eq_one
  have hexp : p.expect (fun ω => (if A0 ω = a0 ∧ A1 ω = a1 then 1 else 0) *
      (stabilizedWeight2 p L0 A0 L1 A1 ω * Y ω)) = wsum p univ (fun ω =>
        (if A0 ω = a0 ∧ A1 ω = a1 then 1 else 0) * (stabilizedWeight2 p L0 A0 L1 A1 ω * Y ω)) :=
    rfl
  have hprob : p.prob (ev A0 a0 ∩ ev A1 a1) = wmass p (ev A0 a0 ∩ ev A1 a1) := rfl
  rw [hexp, wsum_ite_and, ipw2_static p hcons hex hpos, ipw2, wsum_ite_and, hprob]
  rcases (wmass_nonneg p.nonneg (ev A0 a0 ∩ ev A1 a1)).eq_or_lt with h0 | h0
  · rw [wsum_eq_zero_of_wmass_eq_zero p.nonneg h0.symm, ← h0, zero_mul]
  have hA0 : 0 < wmass p (ev A0 a0) := h0.trans_le (wmass_mono p.nonneg inter_subset_left)
  rw [wsum, wsum, mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  simp only [mem_inter, mem_ev] at hω
  rw [stabilizedWeight2, hω.1, hω.2, condProb, condProb, univ_inter, h1]
  field_simp

end Longitudinal

end CausalInference
